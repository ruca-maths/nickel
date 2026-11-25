"""GitHub 連携モード用: PR で追加された Proofs/*.lean を、ベースブランチの
status/graph.json（機械生成・保護パス）を正として検証する。

  python core/ci_verify.py Proofs/L_0007.lean Proofs/N_0003.lean ...

DB はベースの graph.json から一時的に再構成するので、ローカルの state/ は不要。
PR 本文・コメントは一切読まない。
"""
from __future__ import annotations

import json
import re
import sys
import tempfile
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from core.config import load_config
from core.db import DB
from core.verifier import Verifier

NAME_RE = re.compile(r"^Proofs/((L|N|R)_\d{4})\.lean$")


def main(paths: list[str]) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]
    except Exception:
        pass
    cfg = load_config()
    root = Path(cfg["_root"])
    graph = json.loads((root / "status" / "graph.json").read_text(encoding="utf-8"))
    tmp = tempfile.mkdtemp(prefix="ci-verify-")
    db = DB(Path(tmp) / "ci.db")
    v = Verifier(cfg, db, holder="ci")
    if graph.get("targets_hash") != v.targets_hash():
        print("NG: Targets/ のハッシュが承認済みの値と一致しません")
        return 1
    db.set_meta("targets_hash", graph["targets_hash"])
    for a in graph["artifacts"]:
        db.add_artifact(module=a["module"], kind=a["kind"], node=a["node"], path=a["path"],
                        sha256=a["sha256"], axioms=a["axioms"], agent="base")
    status = {n["id"]: n["status"] for n in graph["nodes"]}
    reductions = {r["id"]: r for r in graph["reductions"]}
    failed = 0
    for p in paths:
        m = NAME_RE.match(p.replace("\\", "/"))
        if not m:
            print(f"NG {p}: ファイル名が規約外")
            failed += 1
            continue
        mid, kind_ch = m.group(1), m.group(2)
        src = (root / p).read_text(encoding="utf-8")
        (root / p).unlink()  # verify_module が書き直す
        children = None
        if kind_ch == "L":
            kind, node = "proof", mid
        elif kind_ch == "N":
            kind, node = "refutation", "L_" + mid.split("_")[1]
        else:
            r = reductions.get(mid)
            if not r or r["status"] != "proposed":
                print(f"NG {p}: ベースに提案済みの帰着 {mid} がありません")
                (root / p).write_text(src, encoding="utf-8")
                failed += 1
                continue
            kind, node, children = "reduction", r["parent"], r["children"]
        if status.get(node) != "open":
            print(f"NG {p}: ノード {node} は open ではありません（{status.get(node)}）")
            (root / p).write_text(src, encoding="utf-8")
            failed += 1
            continue
        verdict = v.verify_module(module_id=mid, kind=kind, node_id=node, src=src, agent="ci",
                                  children=children)
        if verdict.ok:
            print(f"OK {p}: 公理 {verdict.axioms}")
        else:
            print(f"NG {p}: {verdict.reason}\n{verdict.log[-3000:]}")
            (root / p).write_text(src, encoding="utf-8")
            failed += 1
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
