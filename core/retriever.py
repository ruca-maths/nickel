"""証明済み補題の検索（RAG）と失敗記憶の抽出。

既定は依存ライブラリ無しの語彙重なり検索。config の `retriever.backend: command` と
`retriever.command` を設定すると外部コマンド（LeanDojo-v2 などの前提検索器）に
クエリを JSON で渡し、JSON の前提リストを受け取る差し込み口になる。

注意: 失敗メモや他エージェントの文章は「信頼できないデータ」としてプロンプトに入れる
（指示として扱わないよう、呼び出し側で明示的に区切る）。
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

from core.db import DB

_TOK = re.compile(r"[A-Za-z_][\w.']*|[^\s\w()\[\]{},:]")


def tokens(s: str) -> set[str]:
    out = set()
    for t in _TOK.findall(s or ""):
        out.add(t)
        out.update(p for p in t.split(".") if len(p) > 1)
    return out


def read_failures(path: Path, node: str | None = None, limit: int = 8) -> list[dict]:
    if not path.exists():
        return []
    rows = []
    with path.open(encoding="utf-8") as f:
        for line in f:
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if node is None or r.get("node") == node:
                rows.append(r)
    return rows[-limit:]


class Retriever:
    def __init__(self, cfg: dict, db: DB, failures_path: Path):
        self.cfg = cfg
        self.db = db
        self.failures_path = failures_path
        rc = cfg.get("retriever") or {}
        self.backend = rc.get("backend", "simple")
        self.command = rc.get("command")

    def checked_lemmas(self) -> list[dict]:
        out = []
        for n in self.db.nodes("checked"):
            out.append({"node": n["id"], "spec": f"Specs.{n['id']}.stmt",
                        "proof": f"Proofs.{n['id']}.main", "stmt": n["stmt"],
                        "informal": n["informal"] or ""})
        return out

    def premises(self, query: str, k: int = 8) -> list[dict]:
        if self.backend == "command" and self.command:
            try:
                p = subprocess.run(self.command, input=json.dumps({"query": query, "k": k}),
                                   capture_output=True, text=True, timeout=120, shell=False)
                return json.loads(p.stdout)[:k]
            except Exception as e:  # 外部検索器の障害で本体を止めない
                return [{"error": f"外部検索器エラー: {e}"}]
        q = tokens(query)
        scored = []
        for lem in self.checked_lemmas():
            t = tokens(lem["stmt"] + " " + lem["informal"])
            if not t:
                continue
            score = len(q & t) / len(q | t)
            scored.append((score, lem))
        scored.sort(key=lambda x: -x[0])
        return [lem for s, lem in scored[:k] if s > 0]

    def context(self, node_id: str) -> dict:
        n = self.db.node(node_id)
        if n is None:
            return {"error": f"{node_id} は存在しない"}
        reds = []
        for r in self.db.reductions_of(node_id):
            reds.append({"id": r["id"], "status": r["status"], "children": json.loads(r["children"])})
        parents = [r["parent"] for r in self.db.q("SELECT * FROM reductions WHERE status IN ('live','done')")
                   if node_id in json.loads(r["children"])]
        hint_file = self.failures_path.parent / "hints" / f"{node_id}.md"
        hints = hint_file.read_text(encoding="utf-8") if hint_file.exists() else ""
        return {
            "node": node_id,
            "human_hints": hints,
            "tier": n["tier"],
            "status": n["status"],
            "stmt": n["stmt"],
            "spec": f"Specs.{node_id}.stmt",
            "informal": n["informal"] or "",
            "reductions": reds,
            "used_by": parents,
            "related_checked_lemmas": self.premises(n["stmt"] + " " + (n["informal"] or "")),
            "past_failures_UNTRUSTED": [
                {k: r.get(k) for k in ("task", "agent", "reason", "note", "error_excerpt")}
                for r in read_failures(self.failures_path, node_id)
            ],
        }
