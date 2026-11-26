"""親機が fetch した子機の確保と提出の集計。Lean は不要。"""
import subprocess
import tempfile
import unittest
from pathlib import Path

from core.gitops import Git
from core.live_status import LiveStatus
from core.status_gen import remote_activity


class TestRemoteActivity(unittest.TestCase):
    def test_claims_submissions_and_expiry_from_fetched_refs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            bare = root / "origin.git"
            subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
            git = Git(root)
            git.run("init", "-q", "-b", "main")
            git.run("remote", "add", "origin", str(bare))
            (root / "status").mkdir()
            (root / "status" / "site.json").write_text('{"generated_at":"published"}', encoding="utf-8")
            git.run("add", "status/site.json")
            git.run("commit", "-qm", "init", env=git._ident_env())
            git.run("push", "origin", "HEAD:refs/heads/main")
            git.fetch()
            self.assertTrue(git.claim("prove-L_0001", "prover-pc2", 7200))
            self.assertTrue(git.claim("refute-L_0002", "redteam-pc3", 7200))
            git.push_files_branch("proof/N_0002-redteam-pc3", {}, "submit")
            git.fetch()
            live = LiveStatus({"_root": root, "project": {"db_path": "missing.db"},
                               "git": {"mode": "github"}}, 5)
            live.refresh_remote()
            activity, _, connection = live.remote
            self.assertEqual(connection, "接続中")
            (root / "status" / "site.json").write_text('{"generated_at":"local"}', encoding="utf-8")
            self.assertEqual(live.snapshot()["generated_at"], "published")
            self.assertEqual(activity["claims"][0]["agent"], "prover-pc2")
            self.assertEqual(activity["submitted"][0]["agent"], "redteam-pc3")

            observed = remote_activity(git, 7200)
            self.assertEqual([(r["agent"], r["task"], r["node"]) for r in observed["claims"]],
                             [("prover-pc2", "prove", "L_0001")])
            self.assertEqual(observed["submitted"], [
                {"agent": "redteam-pc3", "task": "refute", "node": "L_0002",
                 "branch": "proof/N_0002-redteam-pc3"},
            ])
            self.assertGreater(observed["claims"][0]["expires_at"], observed["observed_at"])
            self.assertEqual(remote_activity(git, 0)["claims"], [])
            self.assertTrue(git.delete_branch("claim/prove-L_0001"))
            git.fetch()
            self.assertEqual(remote_activity(git, 7200)["claims"], [])
            live.refresh_remote()
            self.assertEqual(live.remote[0]["claims"], [])
