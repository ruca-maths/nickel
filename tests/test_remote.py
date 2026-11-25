"""別 PC 連携（GitHub モード）の結合テスト。GitHub の代わりにローカルの bare リポジトリを使う。

親機1台・子機2台を作り、確保の競合、子機での証明と PR ブランチ push、マージ後の親機 sync
による再検証と取り込み、確保の掃除と期限切れの引き継ぎ、CI を素通りした不正証明の
再検証での拒否を確かめる。
"""
import json
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from core.config import load_config  # noqa: E402
from core.desk import Desk  # noqa: E402
from core.gitops import Git  # noqa: E402
from core.remote import Remote  # noqa: E402
from tests.test_system import make_env  # noqa: E402

HAVE = shutil.which("lake") is not None and shutil.which("git") is not None


def git(cwd, *args):
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()


@unittest.skipUnless(HAVE, "lake / git が見つからない")
class TestRemote(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        top = Path(tempfile.mkdtemp(prefix="mresearch-remote-"))
        cls.bare = top / "origin.git"
        git(top, "init", "-q", "--bare", "-b", "main", str(cls.bare))
        parent = make_env()
        shutil.copy(REPO / ".gitignore", parent / ".gitignore")
        cfg = json.loads((parent / "config.yaml").read_text(encoding="utf-8"))
        cfg["git"] = {"mode": "github", "autocommit": True, "remote": "origin", "base_branch": "main",
                      "claim_ttl_sec": 7200, "pr_command": []}
        cfg["agents"].append({"id": "prover-c", "role": "prover", "model": "x", "max_turns": 1})
        (parent / "config.yaml").write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        git(parent, "init", "-q", "-b", "main")
        git(parent, "remote", "add", "origin", cls.bare.as_posix())
        cls.parent = parent
        cls.pd = Desk(load_config(parent / "config.yaml"))
        cls.pd.approve_targets("tester")
        cls.pd.init()
        git(parent, "add", "-A")
        git(parent, "commit", "-q", "-m", "init")
        git(parent, "push", "-q", "origin", "HEAD:refs/heads/main")
        cls.child = top / "child"
        cls.child2 = top / "child2"
        for c in (cls.child, cls.child2):
            git(top, "clone", "-q", cls.bare.as_posix(), str(c))

    def remote(self, root) -> Remote:
        return Remote(load_config(root / "config.yaml"), log=lambda *a: None)

    def test_1_claim_conflict_and_child_submission(self):
        g2 = Git(self.child2)
        g2.fetch()
        self.assertTrue(g2.claim("prove-L_0001", "other", 7200))
        self.assertFalse(Git(self.child).claim("prove-L_0001", "me", 7200))  # 確保済み
        r = self.remote(self.child)
        agent = next(a for a in r.cfg["agents"] if a["id"] == "prover-c")
        self.assertEqual(r.session(agent), "submitted")  # L_0001 は他 PC が確保中なので L_0002
        refs = Git(self.child).ls_remote("refs/heads/*")
        self.assertIn("refs/heads/proof/L_0002-prover-c", refs)
        self.assertIn("refs/heads/claim/prove-L_0002", refs)
        self.assertFalse((self.child / "Proofs" / "L_0002.lean").exists())  # 作業ツリーは汚さない
        self.assertEqual(git(self.child, "status", "--porcelain", "--untracked-files=no"), "")
        # 提出ブランチは「main + 証明ファイル1つ」
        git(self.child, "fetch", "-q", "origin")
        files = git(self.child, "diff", "--name-only", "origin/main", "origin/proof/L_0002-prover-c")
        self.assertEqual(files, "Proofs/L_0002.lean")

    def test_2_merge_then_parent_sync(self):
        # PR のマージを模擬（main への fast-forward）
        git(self.child, "push", "-q", "origin", "origin/proof/L_0002-prover-c:refs/heads/main")
        res = self.pd.sync()
        self.assertTrue(res["ingested"]["Proofs/L_0002.lean"]["ok"], res)
        self.assertTrue(res["pushed"])
        self.assertEqual(self.pd.db.node("L_0002")["status"], "checked")
        self.assertIn("prove-L_0002", res["claims_removed"])
        self.assertNotIn("prove-L_0001", res["claims_removed"])
        # 子機から見ても Checked になっている
        r = self.remote(self.child)
        r.refresh()
        self.assertEqual(r.desk.db.node("L_0002")["status"], "checked")
        graph = json.loads(git(self.child, "show", "origin/main:status/graph.json"))
        self.assertIn("Proofs.L_0002", [a["module"] for a in graph["artifacts"]])

    def test_3_stale_claim_takeover(self):
        g = Git(self.child)
        g.fetch()
        self.assertFalse(g.claim("prove-L_0001", "me", 7200))
        time.sleep(1.2)
        self.assertTrue(g.claim("prove-L_0001", "me", 0))  # 期限切れなら引き継げる
        g.delete_branch("claim/prove-L_0001")

    def test_4_bad_proof_on_main_rejected_by_parent(self):
        # CI を素通りして main に sorry 入りの証明が入った場合
        bad = b"import Specs.L_0001\nnamespace Proofs.L_0001\ntheorem main : Specs.L_0001.stmt := by sorry\nend Proofs.L_0001\n"
        g = Git(self.child)
        g.fetch()
        sha = g.push_files_branch("evil", {"Proofs/L_0001.lean": bad}, "evil")
        git(self.child, "push", "-q", "origin", f"{sha}:refs/heads/main")
        res = self.pd.sync()
        self.assertFalse(res["ingested"]["Proofs/L_0001.lean"]["ok"])
        self.assertEqual(self.pd.db.node("L_0001")["status"], "open")
        self.assertFalse((self.parent / "Proofs" / "L_0001.lean").exists())
        g.fetch()
        tree = git(self.child, "ls-tree", "-r", "--name-only", "origin/main", "Proofs")
        self.assertNotIn("Proofs/L_0001.lean", tree)  # 親機が削除をコミットして push 済み


if __name__ == "__main__":
    unittest.main(verbosity=2)
