"""LeanDojo-v2 を使う子機用エージェント（Colab など GPU のある Linux 環境向け）。

オーケストレータ（子機では core/remote.py）からほかの AI CLI と同じように起動される。
  - 標準入力: プロンプト（末尾の ```json``` にタスク JSON がある）
  - 環境変数: RESEARCH_LEASE_TOKEN / RESEARCH_CONFIG / RESEARCH_PYTHON（オーケストレータが設定）
  - 標準出力の最後: claude -p 互換の JSON（{"type": "result", "total_cost_usd": 0, ...}）

扱うのは prove タスクだけ。それ以外は即座に release する。
証明の候補は必ず desk check（親機と同じ静的フィルタ＋lake build）を通し、通ったものだけを
desk submit する。提出物は CI と親機でもう一度検証されるので、この AI の出力は信用しない。

バックエンド（環境変数 LEANDOJO_BACKEND）:
  whole    : 証明全体を生成（既定）。LeanDojo-v2 の HFProver（LEANDOJO_CKPT のモデル）を使う。
             LeanDojo-v2 が読み込めないときは transformers で同じモデルを直接使う。
  external : LeanDojo-v2 の ExternalProver（Hugging Face 推論 API。HF_TOKEN が必要）。
  search   : LeanDojo-v2 の HFProver.search（Pantograph でタクティクを1手ずつ探索）。
             Pantograph がこのプロジェクトの Lean 版で動く場合のみ。

その他の環境変数:
  LEANDOJO_CKPT      モデル（既定 deepseek-ai/DeepSeek-Prover-V2-7B）
  LEANDOJO_SAMPLES   1タスクあたりの候補数（既定 8）
  LEANDOJO_4BIT      1 なら 4bit 量子化で読み込む（T4 など VRAM 16GB 向け。bitsandbytes が必要）
  LEANDOJO_MAX_NEW   生成トークン数の上限（既定 1024）
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
from core.config import load_config, resolve  # noqa: E402

CFG = load_config()  # RESEARCH_CONFIG（オーケストレータが設定）
ROOT = resolve(CFG, CFG["project"].get("lean_root", "."))  # Lean プロジェクトの場所（子機・テストでも正しく解決）
DESK = REPO / "core" / "desk.py"
PY = os.environ.get("RESEARCH_PYTHON", sys.executable)
_opens = (CFG.get("lean") or {}).get("spec_opens") or []
OPENS = ("open " + " ".join(_opens)) if _opens else ""


def log(msg: str) -> None:
    print(f"[leandojo] {msg}", file=sys.stderr, flush=True)


def desk(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([PY, str(DESK), *args], cwd=str(ROOT), capture_output=True, text=True,
                          encoding="utf-8", errors="replace")


def finish(summary: str) -> None:
    print(json.dumps({"type": "result", "result": summary, "total_cost_usd": 0}, ensure_ascii=False))


# ---- 証明ファイルの組み立て -------------------------------------------------
def defs_imports(stmt: str) -> list[str]:
    return sorted(set(re.findall(r"\bDefs\.D_\d{4}\b", stmt)))


def theorem_text(stmt: str) -> str:
    """モデルに渡す定理文（Lean 4 / Mathlib 形式）。"""
    return f"{OPENS}\n\ntheorem main : {stmt} := by"


def clean_proof(text: str) -> str:
    """生成結果からタクティク列だけを取り出す。"""
    m = re.findall(r"```(?:lean4?|)\n(.*?)```", text, re.S)
    if m:
        text = m[-1]
    if ":= by" in text:
        text = text.split(":= by", 1)[1]
    lines = [ln for ln in text.splitlines() if ln.strip()]
    if not lines:
        return ""
    ind = min(len(ln) - len(ln.lstrip()) for ln in lines)
    body = [ln[ind:] for ln in lines]
    bad = ("sorry", "admit", "axiom", "native_decide", "implemented_by", "extern")
    if any(b in ln for ln in body for b in bad):
        return ""
    return "\n".join("  " + ln for ln in body)


def proof_file(node: str, stmt: str, tactics: str) -> str:
    imports = [f"import Specs.{node}"] + [f"import {d}" for d in defs_imports(stmt)]
    return ("\n".join(imports) + f"\n\nnamespace Proofs.{node}\n\n{OPENS}\n\n"
            f"theorem main : Specs.{node}.stmt := by\n  unfold Specs.{node}.stmt\n{tactics}\n\n"
            f"end Proofs.{node}\n")


# ---- バックエンド -----------------------------------------------------------
class Generator:
    def __init__(self, backend: str):
        self.backend = backend
        self.ckpt = os.environ.get("LEANDOJO_CKPT", "deepseek-ai/DeepSeek-Prover-V2-7B")
        self.max_new = int(os.environ.get("LEANDOJO_MAX_NEW", "1024"))
        self.impl = None
        self.tok = self.model = None
        if backend == "fixed":  # テスト用: LEANDOJO_FIXED の文字列をそのまま返す
            self.ckpt = "fixed"
        elif backend == "external":
            from lean_dojo_v2.prover import ExternalProver  # type: ignore
            self.impl = ExternalProver()
        elif backend in ("whole", "search"):
            if os.environ.get("LEANDOJO_4BIT") != "1":
                try:
                    from lean_dojo_v2.prover.hf_prover import HFProver  # type: ignore
                    self.impl = HFProver(ckpt_path=self.ckpt)
                except Exception as e:  # LeanDojo-v2 が無い・Pantograph が入らない等
                    log(f"LeanDojo-v2 の HFProver を読み込めません（{e!r}）。transformers を直接使います")
            if self.impl is None:
                self._load_transformers()
        else:
            raise ValueError(f"未知のバックエンド: {backend}")

    def _load_transformers(self) -> None:
        import torch  # type: ignore
        from transformers import AutoModelForCausalLM, AutoTokenizer  # type: ignore
        kw: dict = {"device_map": "auto", "torch_dtype": torch.bfloat16}
        if os.environ.get("LEANDOJO_4BIT") == "1":
            from transformers import BitsAndBytesConfig  # type: ignore
            kw["quantization_config"] = BitsAndBytesConfig(load_in_4bit=True,
                                                           bnb_4bit_compute_dtype=torch.float16)
            kw.pop("torch_dtype")
        self.tok = AutoTokenizer.from_pretrained(self.ckpt)
        self.model = AutoModelForCausalLM.from_pretrained(self.ckpt, **kw)

    def whole(self, theorem: str) -> str:
        if self.backend == "fixed":
            return os.environ.get("LEANDOJO_FIXED", "")
        if self.impl is not None and hasattr(self.impl, "generate_whole_proof"):
            return self.impl.generate_whole_proof(theorem)
        import torch  # type: ignore
        prompt = ("Complete the following Lean 4 code (Mathlib). Output only the proof.\n\n"
                  f"```lean4\n{theorem}\n```")
        msgs = [{"role": "user", "content": prompt}]
        ids = self.tok.apply_chat_template(msgs, add_generation_prompt=True, return_tensors="pt")
        ids = ids.to(self.model.device)
        with torch.no_grad():
            out = self.model.generate(ids, max_new_tokens=self.max_new, do_sample=True,
                                      temperature=0.8, top_p=0.95)
        return self.tok.decode(out[0][ids.shape[1]:], skip_special_tokens=True)

    def search(self, node: str, stmt: str) -> str:
        from pantograph.server import Server  # type: ignore
        imports = ["Init", f"Specs.{node}"] + defs_imports(stmt)
        server = Server(imports=imports, project_path=str(ROOT))
        result, tactics = self.impl.search(server=server, goal=f"Specs.{node}.stmt")
        if not getattr(result, "success", False) or not tactics:
            return ""
        return "\n".join(tactics)


# ---- メイン -----------------------------------------------------------------
def main() -> int:
    prompt = sys.stdin.buffer.read().decode("utf-8")
    blocks = re.findall(r"```json\n(.*?)\n```", prompt, re.S)
    if not blocks:
        finish("タスク JSON が見つからない")
        return 1
    task = json.loads(blocks[-1])
    ctx = task.get("context", {})
    node, stmt = ctx.get("node"), ctx.get("stmt")
    if task.get("task") != "prove" or not node or not stmt:
        desk("release", "--reason", "LeanDojo エージェントは prove タスクのみ扱う")
        finish("prove 以外のタスクなので解放")
        return 0
    out = ROOT / task.get("file", f"work/{os.environ.get('RESEARCH_AGENT', 'leandojo')}/{node}.lean")
    out.parent.mkdir(parents=True, exist_ok=True)

    backend = os.environ.get("LEANDOJO_BACKEND", "whole")
    samples = int(os.environ.get("LEANDOJO_SAMPLES", "8"))
    t0 = time.time()
    try:
        gen = Generator(backend)
    except Exception as e:
        desk("release", "--reason", f"LeanDojo バックエンドを起動できない: {e!r}"[:300])
        finish(f"バックエンド起動失敗: {e!r}")
        return 1

    last_err = ""
    for i in range(samples if backend != "search" else 1):
        desk("beat")
        try:
            if backend == "search":
                tactics = clean_proof(gen.search(node, stmt))
            else:
                tactics = clean_proof(gen.whole(theorem_text(stmt)))
        except Exception as e:
            last_err = f"生成で例外: {e!r}"
            log(last_err)
            continue
        if not tactics:
            log(f"候補 {i + 1}: 空か禁止語を含むので捨てる")
            continue
        out.write_text(proof_file(node, stmt, tactics), encoding="utf-8")
        r = desk("check", str(out))
        log(f"候補 {i + 1}: check rc={r.returncode}")
        try:
            ok = r.returncode == 0 and json.loads(r.stdout).get("ok") is True
        except ValueError:
            ok = False
        if ok:
            s = desk("submit", str(out), "--note", f"LeanDojo-v2 ({backend}, {gen.ckpt}) の候補 {i + 1}")
            finish(f"提出: {s.stdout.strip()[:500]}")
            return 0
        last_err = (r.stdout + r.stderr).strip()[-800:]

    note = (f"LeanDojo-v2（{backend}, {getattr(gen, 'ckpt', '')}）で {samples} 候補を試し、"
            f"{int(time.time() - t0)} 秒で全て不合格。最後のエラー: {last_err}")
    desk("release", "--reason", "LeanDojo-v2 の候補がすべて検証に失敗", "--note", note[:1500])
    finish("候補がすべて不合格")
    return 0


if __name__ == "__main__":
    sys.exit(main())
