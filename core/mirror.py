"""親機が公開する status/graph.json から、子機・CI 用のミラー DB を作る。

ミラーは「親機が受理済みのもの」の写しにすぎず、ここで受理されたものも PR → CI →
親機の再検証を経るまで成果にはならない。予算（spend）とローカルの試行記録は保持する。
"""
from __future__ import annotations

import json
from pathlib import Path

from core.db import DB


def load_graph(root: Path, text: str | None = None) -> dict:
    if text is None:
        text = (root / "status" / "graph.json").read_text(encoding="utf-8")
    return json.loads(text)


def refresh(db: DB, graph: dict, *, keep_leases: bool = False) -> None:
    with db.tx() as c:
        for t in ("nodes", "reductions", "artifacts"):
            c.execute(f"DELETE FROM {t}")
        if not keep_leases:
            c.execute("DELETE FROM leases")
        c.execute("INSERT OR REPLACE INTO meta(key,value) VALUES('targets_hash', ?)",
                  (graph.get("targets_hash") or "",))
        for n in graph["nodes"]:
            c.execute(
                "INSERT INTO nodes(id,origin,goal_key,tier,stmt,informal,status,depth,both_sides,"
                "created_by,created_at) VALUES(?,?,?,?,?,?,?,?,?,?,0)",
                (n["id"], "goal" if n.get("goal") else "lemma", n.get("goal"), n["tier"], n["stmt"],
                 n.get("informal") or "", n["status"], n.get("depth", 0), int(bool(n.get("both_sides"))),
                 "mirror"))
        for r in graph["reductions"]:
            c.execute("INSERT INTO reductions(id,parent,children,status,created_by,created_at,negate)"
                      " VALUES(?,?,?,?,?,0,?)", (r["id"], r["parent"], json.dumps(r["children"]),
                                                 r["status"], "mirror", int(bool(r.get("negate")))))
        for a in graph["artifacts"]:
            c.execute("INSERT INTO artifacts(module,kind,node,path,sha256,axioms,agent,accepted_at)"
                      " VALUES(?,?,?,?,?,?,?,0)", (a["module"], a["kind"], a["node"], a["path"],
                                                   a["sha256"], json.dumps(a.get("axioms") or []), "base"))
