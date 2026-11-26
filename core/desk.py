"""リース制タスク配分デスク（CLI / ライブラリ）。

エージェント向けコマンド（tools/research.sh 経由）:
  task / next / beat / check / propose / submit / release / audit / context / lemmas / status
人間向け管理コマンド（エージェントには公開しない）:
  approve-targets / init / sweep / regen

リーストークンは --token か環境変数 RESEARCH_LEASE_TOKEN で渡す。
エージェントは自分の作業領域 work/<agent_id>/ の新規ファイルだけを提出できる。
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from core import static_filter
from core.config import load_config, resolve
from core.db import DB, TIER_ORDER
from core.retriever import Retriever
from core.verifier import InfraError, Verifier

ROLES = {"architect": {"decompose"}, "prover": {"prove"}, "redteam": {"refute", "audit"}}


class DeskError(Exception):
    pass


def _excerpt(log: str, limit: int = 6000) -> str:
    """Lean ログからエラー周辺を優先して抜き出す。"""
    if not log:
        return ""
    lines = log.splitlines()
    keep = [i for i, l in enumerate(lines) if re.search(r"error|warning: declaration uses|timeout", l)]
    if keep:
        picked: list[str] = []
        for i in keep:
            picked.extend(lines[max(0, i - 1): i + 12])
        text = "\n".join(picked)
    else:
        text = log
    return text[-limit:]


class Desk:
    def __init__(self, cfg: dict | None = None):
        self.cfg = cfg or load_config()
        p = self.cfg["project"]
        self.root = resolve(self.cfg, p.get("lean_root", "."))
        self.db = DB(resolve(self.cfg, p["db_path"]))
        self.v = Verifier(self.cfg, self.db, holder="desk")
        self.failures_path = resolve(self.cfg, p.get("failures_log", "memory/failures.jsonl"))
        self.audits_dir = resolve(self.cfg, p.get("audits_dir", "memory/audits"))
        self.work_dir = resolve(self.cfg, p.get("work_dir", "work"))
        self.L = self.cfg.get("limits", {})
        self.retriever = Retriever(self.cfg, self.db, self.failures_path)

    def lim(self, key: str, default):
        return self.L.get(key, default)

    # ======================================================================
    # 人間用: Targets 承認と根ノード登録
    # ======================================================================
    def approve_targets(self, by: str) -> dict:
        with self.v._slot():
            ok, out = self.v.lake_build(["Targets"])
        if not ok:
            raise DeskError("Targets がビルドできません:\n" + _excerpt(out))
        h = self.v.targets_hash()
        self.db.set_meta("targets_hash", h)
        self.db.set_meta("targets_approved_by", by)
        self.db.set_meta("targets_approved_at", time.strftime("%Y-%m-%d %H:%M:%S"))
        self.db.event("targets_approved", by, {"hash": h})
        return {"targets_hash": h, "approved_by": by}

    def init(self) -> dict:
        goals_file = self.root / "Targets" / "goals.json"
        goals = json.loads(goals_file.read_text(encoding="utf-8"))["goals"]
        added = []
        for g in goals:
            if self.db.q1("SELECT 1 FROM nodes WHERE goal_key=?", (g["key"],)):
                continue
            nid = self.db.next_id("L")
            verdict = self.v.verify_spec(nid, g["lean"], trusted=True)
            if not verdict.ok:
                raise DeskError(f"目標 {g['key']} の Spec が作れません: {verdict.reason}\n"
                                + _excerpt(verdict.log))
            self.db.add_node(node_id=nid, origin="goal", goal_key=g["key"], tier=g["tier"],
                             stmt=g["lean"], informal=g.get("title", ""),
                             both_sides=bool(g.get("both_sides")), created_by="human")
            added.append({"node": nid, "goal": g["key"]})
        self.regen()
        return {"added": added}

    # ======================================================================
    # スケジューリング
    # ======================================================================
    def tier_open(self, tier: str) -> bool:
        caps = (self.cfg.get("budget") or {}).get("tier_daily_usd") or {}
        cap = caps.get(tier)
        return cap is None or self.db.spent_today(tier) < float(cap)

    def candidates(self, role: str) -> list[tuple[tuple, str, str | None]]:
        mx = int(self.lim("max_attempts_per_task", 5))
        out: list[tuple[tuple, str, str | None]] = []
        n_nodes = self.db.count_nodes()
        # 補題は「まだ open の親を持つ帰着」の子であるときだけ意味がある（親が別経路で証明済みなら不要）
        needed: set[str] = set()
        for r in self.db.q("SELECT parent, children FROM reductions WHERE status='live'"):
            p = self.db.node(r["parent"])
            if p is not None and p["status"] == "open":
                needed.update(json.loads(r["children"]))
        for n in self.db.nodes("open"):
            nid = n["id"]
            if not self.tier_open(n["tier"]):
                continue
            if n["origin"] == "lemma" and nid not in needed:
                continue
            tr = TIER_ORDER.get(n["tier"], 5)
            live = self.db.reductions_of(nid, ("live",))
            pf = self.db.count_attempts(nid, "prove")
            if role == "prover":
                # 本題など「直接証明させても無駄な段階」は Prover に配らない（分解役・反証役が担当）
                # 除外は目標ノードそのものだけ（その分解でできた子補題は普通に配る）
                skip = n["origin"] == "goal" and n["tier"] in (self.lim("prover_skip_tiers", None) or [])
                if pf < mx and not live and not skip:
                    out.append(((tr, -n["depth"], pf, nid), "prove", nid))
            elif role == "architect":
                df = self.db.count_attempts(nid, "decompose")
                n_red = len(self.db.reductions_of(nid, ("live", "done", "dead")))
                hard = n["tier"] in ("T3", "T4", "Tinf") and n["origin"] == "goal"
                ready = pf >= int(self.lim("decompose_after_failures", 2)) or hard
                if (ready and not live and df < mx
                        and n_red < int(self.lim("max_reductions_per_node", 3))
                        and n["depth"] < int(self.lim("max_depth", 6))
                        and n_nodes < int(self.lim("max_nodes", 200))):
                    out.append(((tr, df, nid), "decompose", nid))
            elif role == "redteam":
                rf = self.db.count_attempts(nid, "refute")
                ready = n["both_sides"] or pf >= int(self.lim("refute_after_failures", 2))
                # 反証側の帰着が進行中なら、直接の反証は配らない（子補題の側で進める）
                neg_live = any(r["negate"] for r in live)
                if ready and rf < mx and not neg_live:
                    out.append(((tr, rf, nid), "refute", nid))
        if role == "redteam":
            last = self.db.q1("SELECT MAX(created_at) t FROM attempts WHERE task='audit'")["t"]
            if last is None or time.time() - last > 24 * 3600:
                out.append(((-1,), "audit", None))
        out.sort(key=lambda x: x[0])
        return out

    def lease_next(self, agent: str, role: str, exclude_tasks: tuple[str, ...] = (),
                   claim=None) -> dict | None:
        """次のタスクのリースを取る。claim(task, node) が与えられれば、ローカルのリースを
        取った後にそれ（例: 別 PC 間の確保）も成功したものだけを返す。"""
        if role not in ROLES:
            raise DeskError(f"未知のロール {role}")
        self.sweep()
        held = self.db.leases_of_agent(agent)
        if held:
            return self.task_info(held[0]["token"])
        ttl = float(self.lim("lease_ttl_sec", 1800))
        for _, task, nid in self.candidates(role):
            if task in exclude_tasks:
                continue
            key = f"{task}:{nid or 'targets'}"
            token = self.db.acquire_lease(task_key=key, node=nid or "-", task=task,
                                          agent=agent, role=role, ttl=ttl)
            if token and claim is not None and not claim(task, nid):
                self.db.drop_lease(token)
                continue
            if token:
                self.db.event("lease", agent, {"task": key})
                return self.task_info(token)
        return None

    def _lease(self, token: str | None):
        token = token or os.environ.get("RESEARCH_LEASE_TOKEN")
        if not token:
            raise DeskError("リーストークンがありません（RESEARCH_LEASE_TOKEN）")
        ls = self.db.lease(token)
        if ls is None:
            raise DeskError("リースが無効か期限切れです")
        return ls

    def module_for(self, task: str, node: str) -> str:
        if task == "prove":
            return node
        if task == "refute":
            return "N_" + node.split("_", 1)[1]
        raise DeskError(task)

    def agent_dir(self, agent: str) -> Path:
        d = self.work_dir / agent
        d.mkdir(parents=True, exist_ok=True)
        return d

    def task_info(self, token: str) -> dict:
        ls = self._lease(token)
        agent, task, nid = ls["agent"], ls["task"], ls["node"]
        wd = self.agent_dir(agent).relative_to(self.root).as_posix()
        info: dict = {"lease_token": token, "agent": agent, "task": task,
                      "expires_in_sec": int(ls["expires_at"] - time.time())}
        if task == "audit":
            info.update({"instructions": "Targets/Defs.lean と Targets/Goals.lean を原典の定義と照合し、"
                         "監査報告（Markdown）を書いて `research.sh audit <file>` で提出する。",
                         "report_file": f"{wd}/audit.md"})
            return info
        info["context"] = self.retriever.context(nid)
        if task in ("prove", "refute"):
            mod = self.module_for(task, nid)
            exp, _ = self.v.expected_type("proof" if task == "prove" else "refutation", nid)
            info.update({
                "module": f"Proofs.{mod}", "file": f"{wd}/{mod}.lean",
                "required_shape": (f"import Specs.{nid}\n(必要な Mathlib の部分モジュール、例 import Mathlib.Topology.LocallyFinite / Checked の import Proofs.L_xxxx。import Mathlib 全体は禁止)\n"
                                   f"namespace Proofs.{mod}\n...\ntheorem main : {exp} := ...\n"
                                   f"end Proofs.{mod}"),
            })
        elif task == "decompose":
            info["instructions"] = ("子補題を JSON で `research.sh propose <file>` に提出し、"
                                    "返ってきた帰着モジュールを書いて `research.sh submit` する。")
            info["proposal_format"] = {
                "negate": False,
                "children": [{"stmt": "<Lean の命題項>", "informal": "<日本語の説明>",
                              "imports": ["Defs.D_0001 など（任意）"]},
                             {"existing": "L_0002"}]}
            info["proposal_notes"] = (
                "negate: true にすると「子すべて ⇒ ¬親」（反証側の分解）になる。新しい対象（反例の空間など）が"
                "必要なら、先に `research.sh define <file>` で定義モジュールを登録し、子の imports に書く。")
        return info

    # ======================================================================
    # エージェント操作
    # ======================================================================
    def beat(self, token: str | None = None) -> dict:
        ls = self._lease(token)
        ok = self.db.beat(ls["token"], float(self.lim("lease_ttl_sec", 1800)))
        return {"ok": ok}

    def _own_file(self, ls, file: str) -> Path:
        p = Path(file)
        if not p.is_absolute():
            p = self.root / p
        p = p.resolve()
        base = self.agent_dir(ls["agent"]).resolve()
        if base not in p.parents:
            raise DeskError(f"提出できるのは {base.relative_to(self.root.resolve()).as_posix()}/ 内のファイルだけです")
        if not p.is_file() or p.is_symlink():
            raise DeskError(f"ファイルがありません: {file}")
        if p.stat().st_size > 512 * 1024:
            raise DeskError("ファイルが大きすぎます（512KB 上限）")
        return p

    def _module_of_lease(self, ls) -> tuple[str, str, list[str] | None]:
        """(module_id, kind, children)"""
        if ls["task"] in ("prove", "refute"):
            kind = "proof" if ls["task"] == "prove" else "refutation"
            return self.module_for(ls["task"], ls["node"]), kind, None
        if ls["task"] == "decompose":
            r = self.db.q1("SELECT * FROM reductions WHERE lease_token=? AND status='proposed'",
                           (ls["token"],))
            if not r:
                raise DeskError("先に `propose` で子補題を登録してください")
            return r["id"], ("reduction_neg" if r["negate"] else "reduction"), json.loads(r["children"])
        raise DeskError(f"{ls['task']} では Lean ファイルを提出しません")

    def check(self, file: str, token: str | None = None) -> dict:
        ls = self._lease(token)
        n = self.db.bump_checks(ls["token"])
        if n > int(self.lim("max_checks_per_lease", 30)):
            raise DeskError("このリースでの check 回数上限に達しました。submit か release してください")
        p = self._own_file(ls, file)
        mod, _, _ = self._module_of_lease(ls)
        src = p.read_text(encoding="utf-8")
        allowed = self.db.checked_proof_modules() | {r["module"] for r in self.db.artifacts()
                                                     if r["kind"] == "spec"}
        fr = static_filter.check_proof(src, mod,
                                       allowed_prefixes=list(self.cfg["lean"].get("allowed_import_prefixes", [])),
                                       allowed_modules=allowed, forbidden_imports=list(self.cfg["lean"].get("forbidden_imports") or []),
            max_heartbeats=self.v.max_hb)
        if not fr.ok:
            return {"ok": False, "stage": "static_filter", "violations": fr.violations}
        with self.v._slot():
            ok, out = self.v.lean_file(p)
        self.db.beat(ls["token"], float(self.lim("lease_ttl_sec", 1800)))
        return {"ok": ok, "stage": "lean", "log": _excerpt(out), "checks_used": n,
                "note": "ok=true でも命題一致・公理検査は submit 時に行われます"}

    def define(self, file: str, token: str | None = None) -> dict:
        """（Architect の分解タスク中）定義モジュール Defs.D_xxxx を登録する。
        ファイルでは名前空間を `Defs.NEW` と書く（受理時に Defs.D_xxxx へ置換する）。"""
        ls = self._lease(token)
        if ls["task"] != "decompose":
            raise DeskError("define は decompose タスク専用です")
        p = self._own_file(ls, file)
        src = p.read_text(encoding="utf-8")
        if "Defs.NEW" not in src:
            raise DeskError("名前空間は `namespace Defs.NEW` / `end Defs.NEW` と書いてください")
        did = self.db.next_id("D")
        src = src.replace("Defs.NEW", f"Defs.{did}")
        verdict = self.v.verify_defs(module_id=did, src=src, agent=ls["agent"])
        if not verdict.ok:
            return {"ok": False, "reason": verdict.reason, "log": _excerpt(verdict.log)}
        self.db.event("defs", ls["agent"], {"module": f"Defs.{did}"})
        self.regen(commit_msg=f"{ls['agent']}: 定義 Defs.{did} を登録")
        return {"ok": True, "module": f"Defs.{did}",
                "note": f"命題では Defs.{did}.<名前> と書き、子の imports に \"Defs.{did}\" を入れる"}

    def propose(self, file: str, token: str | None = None) -> dict:
        ls = self._lease(token)
        if ls["task"] != "decompose":
            raise DeskError("propose は decompose タスク専用です")
        parent = self.db.node(ls["node"])
        p = self._own_file(ls, file)
        try:
            data = json.loads(p.read_text(encoding="utf-8"))
            children = data["children"]
            negate = bool(data.get("negate", False))
            assert isinstance(children, list) and children
        except Exception as e:
            raise DeskError(f"提案 JSON が不正です: {e}")
        if len(children) > int(self.lim("max_children_per_reduction", 6)):
            raise DeskError("子補題が多すぎます")
        if self.db.count_nodes() + len(children) > int(self.lim("max_nodes", 200)):
            raise DeskError("補題グラフのノード数上限に達します")
        self._void_proposals(ls["token"])
        child_ids: list[str] = []
        created: list[str] = []
        try:
            for ch in children:
                if "existing" in ch:
                    ex = self.db.node(ch["existing"])
                    if not ex or ex["status"] in ("void", "refuted", "proposed"):
                        raise DeskError(f"既存ノード {ch['existing']} は使えません")
                    if ex["id"] == parent["id"]:
                        raise DeskError("親自身を子にはできません")
                    child_ids.append(ex["id"])
                    continue
                stmt = str(ch.get("stmt", ""))
                fr = static_filter.check_spec_text(stmt)
                if not fr.ok:
                    raise DeskError("命題の静的検査に失敗: " + "; ".join(fr.violations))
                imps = [str(m) for m in (ch.get("imports") or [])]
                dup = None if imps else self.db.q1(
                    "SELECT id FROM nodes WHERE stmt=? AND status IN ('open','checked')", (stmt.strip(),))
                if dup:
                    child_ids.append(dup["id"])
                    continue
                nid = self.db.next_id("L")
                verdict = self.v.verify_spec(nid, stmt, imports=imps)
                if not verdict.ok:
                    raise DeskError(f"子補題の命題が不正: {verdict.reason}\n{_excerpt(verdict.log)}")
                self.db.add_node(node_id=nid, origin="lemma", tier=parent["tier"], stmt=stmt.strip(),
                                 informal=str(ch.get("informal", ""))[:2000], depth=parent["depth"] + 1,
                                 status="proposed", created_by=ls["agent"], lease_token=ls["token"])
                created.append(nid)
                child_ids.append(nid)
        except Exception:
            for nid in created:
                self.db.set_node_status(nid, "void", ls["agent"])
            raise
        rid = self.db.next_id("R")
        self.db.add_reduction(rid, parent["id"], child_ids, ls["agent"], ls["token"], negate=negate)
        exp, _ = self.v.expected_type("reduction_neg" if negate else "reduction", parent["id"], child_ids)
        wd = self.agent_dir(ls["agent"]).relative_to(self.root).as_posix()
        imports = "\n".join(f"import Specs.{c}" for c in child_ids + [parent["id"]])
        return {"reduction": rid, "children": child_ids, "file": f"{wd}/{rid}.lean",
                "required_shape": f"{imports}\nnamespace Proofs.{rid}\ntheorem main : {exp} := ...\nend Proofs.{rid}"}

    def _void_proposals(self, token: str) -> None:
        for r in self.db.q("SELECT * FROM reductions WHERE lease_token=? AND status='proposed'", (token,)):
            self.db.set_reduction_status(r["id"], "void")
        for n in self.db.q("SELECT * FROM nodes WHERE lease_token=? AND status='proposed'", (token,)):
            self.db.set_node_status(n["id"], "void", "desk")

    def _log_failure(self, ls, outcome: str, reason: str, note: str = "", log: str = "") -> None:
        self.db.add_attempt(ls["node"], ls["task"], ls["agent"], ls["token"], outcome, reason)
        rec = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S"), "node": ls["node"], "task": ls["task"],
               "agent": ls["agent"], "outcome": outcome, "reason": reason[:1000],
               "note": (note or "")[:2000], "error_excerpt": _excerpt(log, 1500)}
        self.failures_path.parent.mkdir(parents=True, exist_ok=True)
        with self.failures_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    def _end_lease(self, ls) -> None:
        self._void_proposals(ls["token"])
        self.db.drop_lease(ls["token"])

    def submit(self, file: str, note: str = "", token: str | None = None) -> dict:
        ls = self._lease(token)
        p = self._own_file(ls, file)
        mod, kind, children = self._module_of_lease(ls)
        src = p.read_text(encoding="utf-8")
        node = self.db.node(ls["node"])
        if node["status"] != "open":
            self._end_lease(ls)
            return {"ok": False, "reason": f"{ls['node']} は既に {node['status']} です"}
        verdict = self.v.verify_module(module_id=mod, kind=kind, node_id=ls["node"], src=src,
                                       agent=ls["agent"], children=children)
        if not verdict.ok:
            self._log_failure(ls, "rejected", verdict.reason, note, verdict.log)
            self._end_lease(ls)
            self.regen()
            return {"ok": False, "reason": verdict.reason, "log": _excerpt(verdict.log)}
        self.db.add_attempt(ls["node"], ls["task"], ls["agent"], ls["token"], "accepted", note[:2000])
        if kind in ("reduction", "reduction_neg"):
            rid = mod
            self.db.set_reduction_status(rid, "live")
            for c in children or []:
                if self.db.node(c)["status"] == "proposed":
                    self.db.conn.execute("UPDATE nodes SET status='open', lease_token=NULL WHERE id=?", (c,))
            self.db.drop_lease(ls["token"])
            self._try_compose(self.db.reduction(rid))
        else:
            self.db.drop_lease(ls["token"])
            if kind == "proof":
                self._mark_checked(ls["node"], ls["agent"])
            else:
                self._mark_refuted(ls["node"], ls["agent"])
        self.regen(commit_msg=f"{ls['agent']}: Proofs.{mod} を受理")
        return {"ok": True, "module": f"Proofs.{mod}", "axioms": verdict.axioms}

    # ======================================================================
    # 別 PC 連携（親機）: マージ済み証明の取り込み
    # ======================================================================
    def git(self):
        from core.gitops import Git

        g = self.cfg.get("git") or {}
        return Git(self.root, g.get("remote", "origin"), g.get("base_branch", "main"))

    def ingest(self, rel: str) -> dict:
        """リポジトリに入った Proofs/<L|N>_xxxx.lean を（DB に無ければ）再検証して受理する。"""
        p = self.root / rel
        mid = p.stem
        if self.db.artifact(f"Proofs.{mid}"):
            return {"ok": True, "skipped": "登録済み"}
        m = re.fullmatch(r"(L|N)_(\d{4})", mid)
        src = p.read_text(encoding="utf-8")
        p.unlink()  # verify_module が書き直す（不合格なら消えたままになる）
        if not m:
            self.db.event("alarm", "sync", f"{rel}: 別 PC からは L_/N_ 以外を受け付けない")
            return {"ok": False, "reason": "ファイル名が規約外"}
        kind = "proof" if m.group(1) == "L" else "refutation"
        node = mid if kind == "proof" else f"L_{m.group(2)}"
        n = self.db.node(node)
        if not n or n["status"] != "open":
            return {"ok": False, "reason": f"{node} は open ではない"}
        verdict = self.v.verify_module(module_id=mid, kind=kind, node_id=node, src=src, agent="remote")
        if not verdict.ok:
            self.db.event("alarm", "sync", f"{rel}: CI を通ったはずの証明が再検証で不合格: {verdict.reason}")
            return {"ok": False, "reason": verdict.reason}
        self.db.add_attempt(node, "prove" if kind == "proof" else "refute", "remote", None, "accepted", rel)
        (self._mark_checked if kind == "proof" else self._mark_refuted)(node, "remote")
        return {"ok": True, "module": f"Proofs.{mid}"}

    def sync(self, push: bool = True) -> dict:
        """origin の基準ブランチを取り込み、新しい証明を受理し、状態を commit して push する。"""
        gcfg = self.cfg.get("git") or {}
        g = self.git()
        paths = ["Defs", "Specs", "Proofs", "STATUS.md", "status", "memory"]

        def commit_state(msg: str) -> None:
            present = [p for p in paths if (self.root / p).exists()]
            if present:
                g.run("add", "-A", "--", *present)
            if not g.ok("diff", "--cached", "--quiet"):
                g.run("commit", "-q", "-m", msg)

        def integrate() -> None:
            g.fetch()
            if g.ok("merge", "--ff-only", g.base_ref()):
                return
            # 状態ファイルが衝突したら親機（この DB）の内容を優先して統合する。rebase は途中で
            # 止まるとリポジトリが中途半端な状態で残るので使わない
            if not g.ok("merge", "--autostash", "--no-edit", "-X", "ours", g.base_ref()):
                g.ok("merge", "--abort")
                raise RuntimeError("origin の取り込みに失敗しました（手動で確認が必要）")

        commit_state("sync: 研究メモと状態を保存")  # 未コミットの変更があると rebase できないため先に保存
        integrate()
        results = {}
        known = {r["path"] for r in self.db.artifacts()}
        for f in sorted((self.root / "Proofs").glob("*.lean")):
            rel = f.relative_to(self.root).as_posix()
            if rel not in known:
                results[rel] = self.ingest(rel)
        from core.status_gen import remote_activity

        activity = remote_activity(g, float(gcfg.get("claim_ttl_sec", 7200)))
        self.regen(activity=activity)
        commit_state(f"sync: 状態更新（取り込み {sum(1 for r in results.values() if r.get('ok') and 'module' in r)} 件）")
        pushed = False
        if push:
            for _ in range(3):
                if g.ok("push", g.remote, f"HEAD:refs/heads/{g.base}"):
                    pushed = True
                    break
                integrate()
        # 確保の掃除: ノードが open でなくなったもの・期限切れのもの
        ttl = float(gcfg.get("claim_ttl_sec", 7200))
        removed = []
        for name, sha in g.claims().items():
            node = name.split("-", 1)[-1]
            n = self.db.node(node)
            stale = False
            if n is None or n["status"] != "open":
                stale = True
            else:
                g.run("fetch", g.remote, f"refs/heads/claim/{name}", check=False)
                try:
                    stale = time.time() - g.commit_time(sha) > ttl
                except Exception:
                    stale = False
            if stale and g.delete_branch(f"claim/{name}"):
                removed.append(name)
        return {"ingested": results, "pushed": pushed, "claims_removed": removed}

    def release(self, reason: str, note: str = "", token: str | None = None) -> dict:
        ls = self._lease(token)
        self._log_failure(ls, "gave_up", reason or "release", note)
        self._end_lease(ls)
        self.regen()
        return {"ok": True}

    def audit(self, file: str, token: str | None = None) -> dict:
        ls = self._lease(token)
        if ls["task"] != "audit":
            raise DeskError("audit タスクのリースではありません")
        p = self._own_file(ls, file)
        self.audits_dir.mkdir(parents=True, exist_ok=True)
        dest = self.audits_dir / f"{time.strftime('%Y%m%d-%H%M%S')}-{ls['agent']}.md"
        dest.write_text("<!-- AI による監査報告。人間がレビューするまで効力なし -->\n"
                        + p.read_text(encoding="utf-8")[:100_000], encoding="utf-8")
        self.db.add_attempt("-", "audit", ls["agent"], ls["token"], "reported", dest.name)
        self.db.drop_lease(ls["token"])
        self.regen()
        return {"ok": True, "saved": dest.relative_to(self.root).as_posix()}

    # ======================================================================
    # グラフ伝播
    # ======================================================================
    def _mark_checked(self, nid: str, by: str) -> None:
        n = self.db.node(nid)
        if n["status"] == "refuted":
            self._alarm(f"矛盾: {nid} が証明と反証の両方を持つ")
        self.db.set_node_status(nid, "checked", by)
        self.db.event("checked", by, {"node": nid})
        if n["origin"] == "goal":
            self._goal_closed(n, "checked")
        for r in self.db.reductions_with_child(nid):
            self._try_compose(r)

    def _mark_refuted(self, nid: str, by: str) -> None:
        n = self.db.node(nid)
        if n["status"] == "checked":
            self._alarm(f"矛盾: {nid} が証明と反証の両方を持つ")
        self.db.set_node_status(nid, "refuted", by)
        self.db.event("refuted", by, {"node": nid})
        if n["origin"] == "goal":
            self._goal_closed(n, "refuted")
        for r in self.db.reductions_with_child(nid):
            self.db.set_reduction_status(r["id"], "dead")

    def _try_compose(self, r) -> None:
        if r is None or r["status"] != "live":
            return
        children = json.loads(r["children"])
        if not all(self.db.node(c)["status"] == "checked" for c in children):
            return
        parent = self.db.node(r["parent"])
        if parent["status"] != "open":
            self.db.set_reduction_status(r["id"], "done")
            return
        pid = parent["id"]
        negate = bool(r["negate"])
        mid = ("N_" + pid.split("_", 1)[1]) if negate else pid
        goal = f"¬ Specs.{pid}.stmt" if negate else f"Specs.{pid}.stmt"
        args = " ".join(f"Proofs.{c}.main" for c in children)
        imports = [f"Specs.{pid}", f"Proofs.{r['id']}"] + [f"Proofs.{c}" for c in children]
        src = ("\n".join(f"import {m}" for m in imports)
               + f"\n\n-- 機械生成: 帰着 {r['id']} と子補題の証明の合成\n"
               f"namespace Proofs.{mid}\n\ntheorem main : {goal} :=\n  Proofs.{r['id']}.main {args}\n\n"
               f"end Proofs.{mid}\n")
        verdict = self.v.verify_module(module_id=mid, kind="refutation" if negate else "composed",
                                       node_id=pid, src=src, agent="desk")
        if not verdict.ok:
            self.db.event("infra_error", "desk", {"compose": r["id"], "reason": verdict.reason})
            raise InfraError(f"合成に失敗 ({r['id']}): {verdict.reason}\n{_excerpt(verdict.log)}")
        self.db.set_reduction_status(r["id"], "done")
        (self._mark_refuted if negate else self._mark_checked)(pid, "desk")

    def _goal_closed(self, n, how: str) -> None:
        self.db.event("goal_closed", None, {"node": n["id"], "goal": n["goal_key"], "how": how})
        if n["tier"] == "Tinf":
            self._alarm(f"本題 {n['goal_key']} が {how} になりました。人間による精査まで停止します",
                        level="RESULT")

    def _alarm(self, msg: str, level: str = "ALARM") -> None:
        self.db.event(level.lower(), "desk", msg)
        (self.root / "STOP").write_text(f"[{level}] {msg}\n", encoding="utf-8")

    # ======================================================================
    # 保守
    # ======================================================================
    def sweep(self) -> dict:
        expired = self.db.expired_leases()
        for ls in expired:
            self._log_failure(ls, "expired", "リース期限切れ")
            self._end_lease(ls)
        return {"expired": len(expired)}

    def regen(self, commit_msg: str | None = None, *, activity: dict | None = None) -> None:
        from core import status_gen

        if not self.cfg.get("status_enabled", True):
            return  # 子機: 追跡ファイル（STATUS.md 等）は書かない
        status_gen.generate(self, activity)
        if commit_msg and (self.cfg.get("git") or {}).get("autocommit"):
            paths = ["Defs", "Specs", "Proofs", "STATUS.md", "status", "memory"]
            subprocess.run(["git", "add", "--", *paths], cwd=self.root, capture_output=True)
            subprocess.run(["git", "commit", "-q", "-m", commit_msg, "--", *paths],
                           cwd=self.root, capture_output=True)


# ==========================================================================
# CLI
# ==========================================================================
def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]
    except Exception:
        pass
    ap = argparse.ArgumentParser(prog="desk")
    ap.add_argument("--token")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("approve-targets"); s.add_argument("--by", required=True)
    sub.add_parser("init")
    sub.add_parser("sweep")
    sub.add_parser("regen")
    s = sub.add_parser("sync"); s.add_argument("--no-push", action="store_true")
    s = sub.add_parser("next"); s.add_argument("--agent", required=True); s.add_argument("--role", required=True)
    sub.add_parser("task")
    sub.add_parser("beat")
    s = sub.add_parser("check"); s.add_argument("file")
    s = sub.add_parser("propose"); s.add_argument("file")
    s = sub.add_parser("define"); s.add_argument("file")
    s = sub.add_parser("submit"); s.add_argument("file"); s.add_argument("--note", default="")
    s = sub.add_parser("release"); s.add_argument("--reason", required=True); s.add_argument("--note", default="")
    s = sub.add_parser("audit"); s.add_argument("file")
    s = sub.add_parser("context"); s.add_argument("node")
    s = sub.add_parser("lemmas"); s.add_argument("--query", default="")
    sub.add_parser("status")
    a = ap.parse_args(argv)
    d = Desk()
    try:
        if a.cmd == "approve-targets":
            res = d.approve_targets(a.by)
        elif a.cmd == "init":
            res = d.init()
        elif a.cmd == "sweep":
            res = d.sweep()
        elif a.cmd == "sync":
            res = d.sync(push=not a.no_push)
        elif a.cmd == "regen":
            d.regen(); res = {"ok": True}
        elif a.cmd == "next":
            res = d.lease_next(a.agent, a.role) or {"task": None, "message": "割り当て可能なタスクはありません"}
        elif a.cmd == "task":
            res = d.task_info(a.token or os.environ.get("RESEARCH_LEASE_TOKEN", ""))
        elif a.cmd == "beat":
            res = d.beat(a.token)
        elif a.cmd == "check":
            res = d.check(a.file, a.token)
        elif a.cmd == "define":
            res = d.define(a.file, a.token)
        elif a.cmd == "propose":
            res = d.propose(a.file, a.token)
        elif a.cmd == "submit":
            res = d.submit(a.file, a.note, a.token)
        elif a.cmd == "release":
            res = d.release(a.reason, a.note, a.token)
        elif a.cmd == "audit":
            res = d.audit(a.file, a.token)
        elif a.cmd == "context":
            res = d.retriever.context(a.node)
        elif a.cmd == "lemmas":
            res = d.retriever.premises(a.query, 30) if a.query else d.retriever.checked_lemmas()
        elif a.cmd == "status":
            res = {"nodes": [dict(n) for n in d.db.nodes() if n["status"] != "void"],
                   "leases": [dict(x) for x in d.db.active_leases()],
                   "spent_today_usd": d.db.spent_today()}
        else:
            raise DeskError(a.cmd)
    except (DeskError, InfraError) as e:
        print(json.dumps({"ok": False, "error": str(e)}, ensure_ascii=False, indent=2))
        return 1
    print(json.dumps(res, ensure_ascii=False, indent=2, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
