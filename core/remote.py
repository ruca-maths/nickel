"""子機（別 PC）ランナー。

  python core/remote.py --agents prover-3 [--max-sessions N] [--loop]

1 セッションの流れ:
  1. origin の基準ブランチを取得して作業ツリーを合わせ、status/graph.json からミラー DB を作る
  2. 他の PC の確保（claim/*）と提出待ち（proof/*）を除いてタスクを選び、claim ブランチを push して確保
  3. エージェントを実行（research.sh check / submit はミラー DB 上で、親機と同じ検証器を使う）
  4. ローカルで受理されたら「基準ブランチ＋証明ファイル1つ」のブランチを push して PR を作る
     （CI と親機の再検証を通るまで成果ではない）。受理されなければ確保を解除する

子機で扱うのは prove / refute のみ（分解 decompose と監査 audit は親機の担当）。
"""
from __future__ import annotations

import argparse
import copy
import json
import subprocess
import sys
import time
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from core import mirror
from core.config import load_config, resolve
from core.desk import Desk
from core.gitops import Git, GitError
from core.orchestrator import Orchestrator

CHILD_ROLES = {"prover", "redteam"}


def child_config(cfg: dict) -> dict:
    """子機用設定（ミラー DB を使い、STATUS.md などの追跡ファイルは書かない）。"""
    c = copy.deepcopy(cfg)
    g = c.get("git") or {}
    c["project"]["db_path"] = g.get("child_db_path", "state/remote.db")
    # 設定ファイルは state/ に置くので、パスはすべて元の config.yaml 基準の絶対パスにする
    for key in ("lean_root", "db_path", "failures_log", "audits_dir", "work_dir"):
        if key in c["project"]:
            c["project"][key] = str(resolve(cfg, c["project"][key]))
    c["project"].setdefault("lean_root", str(resolve(cfg, ".")))
    c["status_enabled"] = False
    c.setdefault("git", {})["autocommit"] = False
    out = resolve(cfg, "state/remote_config.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    dump = {k: v for k, v in c.items() if not k.startswith("_")}
    out.write_text(json.dumps(dump, ensure_ascii=False, indent=2), encoding="utf-8")
    return load_config(out)


class Remote:
    def __init__(self, cfg: dict | None = None, log=print):
        base_cfg = cfg or load_config()
        self.cfg = child_config(base_cfg)
        self.log = log
        g = self.cfg.get("git") or {}
        self.desk = Desk(self.cfg)
        self.git = Git(self.desk.root, g.get("remote", "origin"), g.get("base_branch", "main"))
        self.claim_ttl = float(g.get("claim_ttl_sec", 7200))
        self.pr_cmd = g.get("pr_command", ["gh", "pr", "create", "--base", "{base}", "--head", "{branch}",
                                           "--title", "{title}", "--body", "{body}"])
        self.orch = Orchestrator(self.cfg, log=log)

    # ---- 同期 -----------------------------------------------------------------
    def refresh(self) -> None:
        g = self.git
        g.fetch()
        if g.run("status", "--porcelain", "--untracked-files=no"):
            raise GitError("子機の作業ツリーに未コミットの変更があります（追跡ファイルは編集しないこと）")
        g.run("checkout", "-q", "--detach", g.base_ref())
        mirror.refresh(self.desk.db, mirror.load_graph(self.desk.root))
        busy = set()
        for name in g.claims():
            busy.add(tuple(name.split("-", 1)))
        for ref in g.ls_remote("refs/heads/proof/*"):
            mod = ref.removeprefix("refs/heads/proof/").split("-", 1)[0]
            if mod.startswith("L_"):
                busy.add(("prove", mod))
            elif mod.startswith("N_"):
                busy.add(("refute", "L_" + mod.split("_", 1)[1]))
        far = time.time() + 10 * 365 * 86400
        for task, node in busy:
            self.desk.db.conn.execute(
                "INSERT OR REPLACE INTO leases(token,task_key,node,task,agent,role,acquired_at,expires_at)"
                " VALUES(?,?,?,?,?,?,?,?)",
                (f"busy:{task}:{node}", f"{task}:{node}", node, task, "other-pc", "-", time.time(), far))

    # ---- 1セッション ----------------------------------------------------------
    def session(self, agent: dict) -> str:
        if agent["role"] not in CHILD_ROLES:
            raise ValueError(f"子機では {agent['role']} は動かせません（prover / redteam のみ）")
        self.refresh()
        if not self.orch.can_launch():
            return "budget"
        claimed: list[str] = []

        def claim(task: str, node: str) -> bool:
            name = f"{task}-{node}"
            if self.git.claim(name, agent["id"], self.claim_ttl):
                claimed.append(name)
                return True
            return False

        task = self.desk.lease_next(agent["id"], agent["role"], exclude_tasks=("audit", "decompose"),
                                    claim=claim)
        if not task:
            return "idle"
        node = task["context"]["node"]
        self.log(f"[{agent['id']}] 確保 {claimed[-1]}")
        self.orch.session(agent, task)
        mod = self.desk.module_for(task["task"], node)
        art = self.desk.db.artifact(f"Proofs.{mod}")
        if art and art["agent"] == agent["id"]:
            path = self.desk.root / art["path"]
            data = path.read_bytes()
            branch = f"proof/{mod}-{agent['id']}"
            self.git.push_files_branch(branch, {art["path"]: data},
                                       f"{agent['id']}: Proofs.{mod} を提出（子機で受理済み）")
            self.desk.v.purge_module(f"Proofs.{mod}")
            self.open_pr(branch, mod, agent["id"])
            self.log(f"[{agent['id']}] {branch} を push しました")
            return "submitted"
        self.git.delete_branch(f"claim/{claimed[-1]}")
        return "no_result"

    def open_pr(self, branch: str, mod: str, agent: str) -> None:
        if not self.pr_cmd:
            return
        sub = {"base": self.git.base, "branch": branch, "title": f"Proofs.{mod} ({agent})",
               "body": "子機ランナーが自動作成。検証は CI と親機が Lean ソースのみで行う。"}
        cmd = [str(x).format(**sub) for x in self.pr_cmd]
        p = subprocess.run(cmd, cwd=self.desk.root, capture_output=True, text=True)
        if p.returncode != 0:
            self.log(f"[{agent}] PR 作成に失敗: {p.stderr.strip()}（ブランチ {branch} は push 済み）")

    def run(self, agents: list[dict], max_sessions: int | None = None, loop: bool = False) -> str:
        n = 0
        while True:
            if (self.desk.root / "STOP").exists():
                return "STOP"
            progressed = False
            for a in agents:
                if max_sessions is not None and n >= max_sessions:
                    return "完了"
                r = self.session(a)
                if r == "budget":
                    return "本日の予算上限に到達"
                if r != "idle":
                    n += 1
                    progressed = True
            if not progressed:
                if not loop:
                    return "割り当て可能なタスクなし"
                time.sleep(float(self.cfg["runner"].get("idle_sleep_sec", 60)))


def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]
    except Exception:
        pass
    ap = argparse.ArgumentParser()
    ap.add_argument("--agents", required=True, help="子機で動かすエージェント ID（カンマ区切り）")
    ap.add_argument("--max-sessions", type=int)
    ap.add_argument("--loop", action="store_true", help="タスクが無くても待機して続ける")
    a = ap.parse_args(argv)
    r = Remote()
    want = a.agents.split(",")
    agents = [x for x in r.cfg["agents"] if x["id"] in want]
    if len(agents) != len(want):
        print("config.yaml の agents に無い ID があります")
        return 2
    print(r.run(agents, a.max_sessions, a.loop))
    return 0


if __name__ == "__main__":
    sys.exit(main())
