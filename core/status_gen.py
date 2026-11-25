"""STATUS.md と status/graph.json の機械生成（AI の手書き禁止）。"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

ICON = {"open": "⬜", "checked": "✅", "refuted": "❌", "proposed": "…", "void": "·"}


def build_graph(desk) -> dict:
    db = desk.db
    mx = int(desk.lim("max_attempts_per_task", 5))
    nodes = []
    for n in db.nodes():
        if n["status"] == "void":
            continue
        att = {t: db.count_attempts(n["id"], t) for t in ("prove", "decompose", "refute")}
        exhausted = n["status"] == "open" and all(v >= mx for v in att.values())
        nodes.append({"id": n["id"], "goal": n["goal_key"], "tier": n["tier"], "status": n["status"],
                      "exhausted": exhausted, "depth": n["depth"], "both_sides": bool(n["both_sides"]), "stmt": n["stmt"],
                      "informal": n["informal"], "attempts": att, "closed_by": n["closed_by"]})
    reductions = [{"id": r["id"], "parent": r["parent"], "children": json.loads(r["children"]),
                   "status": r["status"]}
                  for r in db.q("SELECT * FROM reductions WHERE status!='void' ORDER BY id")]
    artifacts = [{"module": r["module"], "kind": r["kind"], "node": r["node"], "path": r["path"],
                  "sha256": r["sha256"], "axioms": json.loads(r["axioms"] or "[]")}
                 for r in db.artifacts()]
    return {"generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
            "targets_hash": db.get_meta("targets_hash"),
            "nodes": nodes, "reductions": reductions, "artifacts": artifacts}


def render_md(desk, g: dict) -> str:
    db = desk.db
    L = []
    L.append("<!-- このファイルは core/status_gen.py が自動生成します。手で編集しないこと。 -->")
    L.append("# 研究状況: 任意の M3 空間は M1 空間か？\n")
    L.append(f"- 生成時刻: {g['generated_at']}")
    L.append(f"- Targets 承認ハッシュ: `{(g['targets_hash'] or '未承認')[:16]}…`"
             f"（承認者: {db.get_meta('targets_approved_by', '-')}）")
    L.append(f"- 本日の支出: ${db.spent_today():.2f} / ${float((desk.cfg.get('budget') or {}).get('daily_usd', 0)):.2f}")
    stop = desk.root / "STOP"
    if stop.exists():
        L.append(f"- **停止中**: {stop.read_text(encoding='utf-8').strip()}")
    bad = desk.v.audit_artifacts()
    L.append(f"- 受理済みファイルの整合性: {'OK' if not bad else '**NG** ' + '; '.join(bad)}")
    L.append("")
    L.append("## 目標")
    L.append("| 段階 | 目標 | ノード | 状態 | 試行 (証明/分解/反証) |")
    L.append("|---|---|---|---|---|")
    for n in g["nodes"]:
        if n["goal"]:
            a = n["attempts"]
            st = ICON.get(n["status"], n["status"]) + (" 試行上限" if n["exhausted"] else "")
            L.append(f"| {n['tier']} | {n['goal']}: {n['informal']} | {n['id']} | {st} | "
                     f"{a['prove']}/{a['decompose']}/{a['refute']} |")
    L.append("")
    lemmas = [n for n in g["nodes"] if not n["goal"]]
    if lemmas:
        L.append("## 補題")
        L.append("| ノード | 深さ | 状態 | 説明 |")
        L.append("|---|---|---|---|")
        for n in lemmas:
            L.append(f"| {n['id']} | {n['depth']} | {ICON.get(n['status'], n['status'])} | "
                     f"{(n['informal'] or '').replace('|', '/')[:80]} |")
        L.append("")
    if g["reductions"]:
        L.append("## 依存グラフ")
        L.append("```mermaid\ngraph TD")
        for n in g["nodes"]:
            label = n["goal"] or n["id"]
            L.append(f'  {n["id"]}["{label} {ICON.get(n["status"], "")}"]')
        for r in g["reductions"]:
            for c in r["children"]:
                style = "-.->" if r["status"] == "dead" else "-->"
                L.append(f"  {r['parent']} {style}|{r['id']}| {c}")
        L.append("```\n")
    leases = db.active_leases()
    if leases:
        L.append("## 実行中のリース")
        for ls in leases:
            L.append(f"- {ls['agent']}: {ls['task']} {ls['node']}（残り {int(ls['expires_at'] - time.time())} 秒）")
        L.append("")
    audits = sorted(desk.audits_dir.glob("*.md")) if desk.audits_dir.exists() else []
    if audits:
        L.append("## Red Team 監査報告（未レビュー。人間が確認すること）")
        for a in audits[-5:]:
            L.append(f"- `{a.relative_to(desk.root).as_posix()}`")
        L.append("")
    return "\n".join(L) + "\n"


def build_site(desk, g: dict) -> dict:
    """公開用の進捗ページ（index.html）が読むデータ。AI の文章は短く切って載せる。"""
    import re

    db = desk.db
    uses = {}
    for f in sorted((desk.root / "Proofs").glob("*.lean")):
        src = f.read_text(encoding="utf-8")
        uses[f.stem] = {"imports": re.findall(r"^import (Proofs\.\w+)", src, re.M), "lines": src.count("\n")}
    nodes = [{k: n[k] for k in ("id", "goal", "tier", "status", "depth", "informal", "attempts", "closed_by",
                                "exhausted")} | {"stmt": n["stmt"][:400]} for n in g["nodes"]]
    accepted = [dict(r) for r in db.q("SELECT module,kind,node,agent,accepted_at,axioms FROM artifacts "
                                      "WHERE kind!='spec' ORDER BY accepted_at")]
    fails = []
    if desk.failures_path.exists():
        for line in desk.failures_path.read_text(encoding="utf-8").splitlines():
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            fails.append({k: (str(r.get(k) or "")[:500]) for k in ("ts", "node", "task", "agent", "outcome", "reason")})
    events = [dict(r) for r in db.q("SELECT kind,agent,detail,created_at FROM events WHERE kind IN "
                                    "('checked','refuted','goal_closed','targets_approved') ORDER BY id")]
    spend = [dict(r) for r in db.q("SELECT agent, ROUND(SUM(usd),3) usd, COUNT(*) n FROM spend GROUP BY agent")]
    attempts = [dict(r) for r in db.q("SELECT agent,task,outcome,COUNT(*) n FROM attempts GROUP BY agent,task,outcome")]
    running = [{"agent": r["agent"], "task": r["task"], "node": r["node"]} for r in db.active_leases()]
    return {"generated_at": g["generated_at"], "targets_hash": g["targets_hash"], "nodes": nodes,
            "reductions": g["reductions"], "uses": uses, "accepted": accepted, "failures": fails[-200:],
            "events": events, "spend": spend, "sessions": sum(s["n"] for s in spend), "attempts": attempts,
            "running": running, "spent_today": round(db.spent_today(), 2)}


def generate(desk) -> None:
    g = build_graph(desk)
    out = desk.root / "status"
    out.mkdir(exist_ok=True)
    (out / "graph.json").write_text(json.dumps(g, ensure_ascii=False, indent=2), encoding="utf-8")
    (out / "site.json").write_text(json.dumps(build_site(desk, g), ensure_ascii=False), encoding="utf-8")
    (desk.root / "STATUS.md").write_text(render_md(desk, g), encoding="utf-8")


if __name__ == "__main__":
    from core.desk import Desk

    generate(Desk())
    print("STATUS.md を再生成しました")
