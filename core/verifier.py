"""決定論的 Lean 4 チェッカー（唯一の審判）。

受理条件（すべて満たすこと）:
 1. Targets/ のハッシュが人間の承認時と一致している
 2. 静的フィルタを通過
 3. `lake build Proofs.<ID>` が成功（Lean カーネルによる型検査）
 4. 独立に生成した検査ファイルで、ロック済み命題 `Specs.<...>.stmt` から組み立てた
    「期待される型」を `Proofs.<ID>.main` が持つことを型検査
 5. `#print axioms` の結果が許可公理（既定: propext, Classical.choice, Quot.sound）に含まれる

検証器は Lean ソースのみを読み、PR 本文・コメント・エージェントの自己申告は一切読まない。
"""
from __future__ import annotations

import glob
import hashlib
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from core import static_filter
from core.config import load_config, resolve
from core.db import DB


class InfraError(RuntimeError):
    """検証器・環境側の異常（証明の良し悪しとは無関係）。"""


@dataclass
class Verdict:
    ok: bool
    reason: str = ""
    log: str = ""
    axioms: list[str] = field(default_factory=list)


def sha256_bytes(b: bytes) -> str:
    """内容ハッシュ（改行コード CRLF/LF の違いは無視する）。"""
    return hashlib.sha256(b.replace(b"\r\n", b"\n")).hexdigest()


def write_lf(path: Path, text: str) -> None:
    path.write_bytes(text.replace("\r\n", "\n").encode("utf-8"))


def tree_hash(root: Path, rel_dirs: list[str]) -> str:
    """ロック領域のハッシュ（相対パスと内容。改行コードの差は正規化）。"""
    h = hashlib.sha256()
    for d in rel_dirs:
        base = root / d
        files = [base] if base.is_file() else sorted(
            (p for p in base.rglob("*") if p.is_file()),
            key=lambda p: p.relative_to(root).as_posix().lower(),
        )
        for p in files:
            rel = p.relative_to(root).as_posix()
            data = p.read_bytes().replace(b"\r\n", b"\n")
            h.update(rel.encode() + b"\0" + sha256_bytes(data).encode() + b"\n")
    return h.hexdigest()


LOCKED_PATHS = ["Targets", "Targets.lean"]


def run(cmd: list[str], cwd: Path, timeout: float, env: dict | None = None) -> tuple[int, str]:
    """タイムアウト付き実行。タイムアウト時はプロセスツリーごと終了させる。"""
    kw: dict = {}
    if os.name == "nt":
        kw["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        kw["start_new_session"] = True
    try:
        p = subprocess.Popen(cmd, cwd=str(cwd), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             stdin=subprocess.DEVNULL, env=env, **kw)
    except FileNotFoundError as e:
        raise InfraError(f"コマンドが見つからない: {cmd[0]} ({e})")
    try:
        out, _ = p.communicate(timeout=timeout)
        return p.returncode, out.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        if os.name == "nt":
            subprocess.run(["taskkill", "/T", "/F", "/PID", str(p.pid)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        else:
            os.killpg(p.pid, signal.SIGKILL)
        out, _ = p.communicate()
        return -999, out.decode("utf-8", "replace") + f"\n[timeout after {timeout}s]"


_AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.S)
_NOAXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def parse_axioms(output: str) -> dict[str, list[str] | None]:
    """名前 → 公理一覧。同じ名前が複数回現れたら None（曖昧なので不合格扱い）。"""
    found: list[tuple[str, list[str]]] = []
    for m in _AXIOMS_RE.finditer(output):
        found.append((m.group(1), [a.strip() for a in m.group(2).replace("\n", " ").split(",")
                                   if a.strip()]))
    for m in _NOAXIOMS_RE.finditer(output):
        found.append((m.group(1), []))
    res: dict[str, list[str] | None] = {}
    for name, axs in found:
        res[name] = None if name in res else axs
    return res


def has_error(output: str) -> bool:
    return (bool(re.search(r":\d+:\d+: error|(^|\n)\s*error:", output))
            or "[timeout after" in output)


class Verifier:
    def __init__(self, cfg: dict, db: DB, holder: str = "verifier"):
        self.cfg = cfg
        self.db = db
        self.holder = f"{holder}:{os.getpid()}"
        self.root = resolve(cfg, cfg["project"].get("lean_root", "."))
        lc = cfg["lean"]
        self.lake = lc.get("lake", "lake")
        self.allowed_axioms = set(lc.get("allowed_axioms", []))
        self.build_timeout = float(lc.get("build_timeout_sec", 900))
        self.check_timeout = float(lc.get("check_timeout_sec", 600))
        self.slots = int(lc.get("build_slots", 1))
        self.max_hb = int(lc.get("max_heartbeats_cap", 1_000_000))

    # ---- 共通 ----------------------------------------------------------------
    def targets_hash(self) -> str:
        return tree_hash(self.root, LOCKED_PATHS)

    def assert_targets_locked(self) -> None:
        approved = self.db.get_meta("targets_hash")
        if not approved:
            raise InfraError("Targets が未承認です（人間が `desk.py approve-targets` を実行すること）")
        if approved != self.targets_hash():
            raise InfraError("Targets/ が承認後に変更されています。検証を停止します")

    def _slot(self):
        verifier = self

        class _Ctx:
            def __enter__(self):
                ttl = max(verifier.build_timeout, verifier.check_timeout) + 120
                self.slot = verifier.db.acquire_slot(verifier.holder, verifier.slots, ttl)
                return self

            def __exit__(self, *a):
                verifier.db.release_slot(self.slot, verifier.holder)

        return _Ctx()

    def lake_build(self, modules: list[str]) -> tuple[bool, str]:
        rc, out = run([self.lake, "build", *modules], self.root, self.build_timeout)
        return rc == 0 and not has_error(out), out

    def lean_file(self, path: Path) -> tuple[bool, str]:
        rel = os.path.relpath(path, self.root)
        rc, out = run([self.lake, "env", "lean", rel], self.root, self.check_timeout)
        return rc == 0 and not has_error(out), out

    def module_path(self, module: str) -> Path:
        return self.root / (module.replace(".", "/") + ".lean")

    def purge_module(self, module: str) -> None:
        """不合格モジュールのソースとビルド成果物を削除（後続の import を防ぐ）。"""
        p = self.module_path(module)
        if p.exists():
            p.unlink()
        rel = module.replace(".", "/")
        for pat in (f".lake/build/**/{rel}.*", f".lake/build/**/{rel}"):
            for f in glob.glob(str(self.root / pat), recursive=True):
                try:
                    if os.path.isdir(f):
                        shutil.rmtree(f)
                    else:
                        os.unlink(f)
                except OSError:
                    pass

    def axioms_check(self, imports: list[str], decls: list[tuple[str, str]],
                     tag: str) -> Verdict:
        """decls = [(name, "型 := 値")] を独立ファイルで型検査し、公理を調べる。"""
        chk_dir = self.root / "Check"
        chk_dir.mkdir(exist_ok=True)
        path = chk_dir / f"C_{tag}_{os.getpid()}_{int(time.time() * 1000)}.lean"
        lines = [f"import {m}" for m in imports] + [""]
        for name, body in decls:
            lines.append(f"theorem {name} : {body}")
        lines.append("")
        for name, _ in decls:
            lines.append(f"#print axioms {name}")
        write_lf(path, "\n".join(lines) + "\n")
        try:
            ok, out = self.lean_file(path)
        finally:
            try:
                path.unlink()
            except OSError:
                pass
        if not ok:
            return Verdict(False, "期待される型との一致検査に失敗（命題のすり替え・型不一致）", out)
        ax = parse_axioms(out)
        used: set[str] = set()
        for name, _ in decls:
            if ax.get(name) is None:
                return Verdict(False, f"#print axioms の出力に {name} が無いか曖昧", out)
            used |= set(ax[name])
        bad = sorted(used - self.allowed_axioms)
        if bad:
            return Verdict(False, f"許可されていない公理に依存: {', '.join(bad)}", out, sorted(used))
        return Verdict(True, "ok", out, sorted(used))

    # ---- Spec（補題の命題） --------------------------------------------------
    def spec_source(self, node_id: str, stmt: str) -> str:
        lc = self.cfg["lean"]
        imps = "\n".join(f"import {m}" for m in lc.get("spec_imports", []))
        opens = lc.get("spec_opens") or []
        open_line = f"open {' '.join(opens)}\n" if opens else ""
        return (f"{imps}\n\n-- 機械生成ファイル（desk が DB から生成）。手で編集しないこと。\n"
                f"namespace Specs.{node_id}\n{open_line}\n"
                f"def stmt : Prop :=\n  {stmt.strip()}\n\nend Specs.{node_id}\n")

    def verify_spec(self, node_id: str, stmt: str, *, trusted: bool = False) -> Verdict:
        """命題テキストを Specs/<node_id>.lean に書き出してビルドする。
        trusted=True は Targets 由来の根ノード用（静的フィルタは同じく通す）。"""
        self.assert_targets_locked()
        fr = static_filter.check_spec_text(stmt)
        if not fr.ok:
            return Verdict(False, "命題の静的検査に失敗: " + "; ".join(fr.violations))
        module = f"Specs.{node_id}"
        path = self.module_path(module)
        if self.db.artifact(module):
            raise InfraError(f"{module} は既に登録済み")
        path.parent.mkdir(parents=True, exist_ok=True)
        src = self.spec_source(node_id, stmt)
        write_lf(path, src)
        with self._slot():
            ok, out = self.lake_build([module])
            if not ok:
                self.purge_module(module)
                return Verdict(False, "命題がコンパイルできない", out)
            v = self.axioms_check([module], [(f"Check.{node_id}.spec_refl",
                                              f"Specs.{node_id}.stmt = Specs.{node_id}.stmt := rfl")],
                                  f"spec_{node_id}")
        if not v.ok:
            self.purge_module(module)
            return v
        self.db.add_artifact(module=module, kind="spec", node=node_id,
                             path=path.relative_to(self.root).as_posix(),
                             sha256=sha256_bytes(src.encode()), axioms=[], agent="desk")
        return Verdict(True, "ok", out)

    # ---- 証明・帰着・反証 ----------------------------------------------------
    def expected_type(self, kind: str, node_id: str, children: list[str] | None = None) -> tuple[str, list[str]]:
        if kind in ("proof", "composed"):
            return f"Specs.{node_id}.stmt", [f"Specs.{node_id}"]
        if kind == "refutation":
            return f"¬ Specs.{node_id}.stmt", [f"Specs.{node_id}"]
        if kind == "reduction":
            assert children is not None
            hyps = " → ".join(f"Specs.{c}.stmt" for c in children)
            return f"{hyps} → Specs.{node_id}.stmt", [f"Specs.{c}" for c in children] + [f"Specs.{node_id}"]
        raise ValueError(kind)

    def verify_module(self, *, module_id: str, kind: str, node_id: str, src: str,
                      agent: str | None, children: list[str] | None = None) -> Verdict:
        """Proofs/<module_id>.lean として src を検証し、合格なら登録する。"""
        self.assert_targets_locked()
        module = f"Proofs.{module_id}"
        if self.db.artifact(module):
            return Verdict(False, f"{module} は既に受理済み（新規ファイルのみ提出可）")
        allowed_mods = self.db.checked_proof_modules() | {
            r["module"] for r in self.db.artifacts() if r["kind"] == "spec"}
        fr = static_filter.check_proof(
            src, module_id,
            allowed_prefixes=list(self.cfg["lean"].get("allowed_import_prefixes", [])),
            allowed_modules=allowed_mods, forbidden_imports=list(self.cfg["lean"].get("forbidden_imports") or []),
            max_heartbeats=self.max_hb)
        if not fr.ok:
            return Verdict(False, "静的フィルタで拒否: " + "; ".join(fr.violations))
        exp, spec_mods = self.expected_type(kind, node_id, children)
        for sm in spec_mods:
            if not self.db.artifact(sm):
                raise InfraError(f"{sm} が未登録")
        path = self.module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        write_lf(path, src)
        accepted = False
        try:
            with self._slot():
                ok, out = self.lake_build([module])
                if not ok:
                    return Verdict(False, "Lean のビルドに失敗", out)
                v = self.axioms_check(spec_mods + [module],
                                      [(f"Check.{module_id}.ok", f"{exp} := Proofs.{module_id}.main")],
                                      module_id)
            if not v.ok:
                return v
            self.db.add_artifact(module=module, kind=kind, node=node_id,
                                 path=path.relative_to(self.root).as_posix(),
                                 sha256=sha256_bytes(src.encode()), axioms=v.axioms, agent=agent)
            accepted = True
            return Verdict(True, "受理", out, v.axioms)
        finally:
            if not accepted:
                self.purge_module(module)

    # ---- 整合性監査 ----------------------------------------------------------
    def audit_artifacts(self) -> list[str]:
        """受理済みファイルが改竄・削除されていないか検査する。"""
        bad = []
        for r in self.db.artifacts():
            p = self.root / r["path"]
            if not p.exists():
                bad.append(f"{r['module']}: ファイルが存在しない")
            elif sha256_bytes(p.read_bytes()) != r["sha256"]:
                bad.append(f"{r['module']}: 受理後に内容が変更されている")
        return bad


def main(argv: list[str] | None = None) -> int:
    """CI / 手動用: python core/verifier.py audit | targets-hash"""
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["audit", "targets-hash"])
    a = ap.parse_args(argv)
    cfg = load_config()
    db = DB(resolve(cfg, cfg["project"]["db_path"]))
    v = Verifier(cfg, db)
    if a.cmd == "targets-hash":
        print(v.targets_hash())
        return 0
    bad = v.audit_artifacts()
    for b in bad:
        print("NG", b)
    print("OK" if not bad else f"{len(bad)} 件の不整合")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
