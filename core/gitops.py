"""別 PC 連携のための git 操作。

* 確保（claim）: `refs/heads/claim/<task>-<node>` ブランチの新規作成をリースの代わりにする。
  毎回固有のコミット（基準ブランチの木＋確保情報のメッセージ）を作るので、同じ名前の
  ブランチを2台目が push しようとすると non-fast-forward で拒否される（原子的）。
  期限（claim_ttl_sec）を過ぎた確保は --force-with-lease で引き継げる。
* 提出: 作業ツリーを汚さずに「基準ブランチ＋1ファイル」のコミットを作って push する。
"""
from __future__ import annotations

import os
import subprocess
import tempfile
import time
from pathlib import Path


class GitError(RuntimeError):
    pass


class Git:
    def __init__(self, root: str | Path, remote: str = "origin", base: str = "main"):
        self.root = Path(root)
        self.remote = remote
        self.base = base

    def run(self, *args: str, check: bool = True, env: dict | None = None,
            input: bytes | None = None, timeout: float | None = None) -> str:
        e = dict(os.environ)
        if env:
            e.update(env)
        p = subprocess.run(["git", *args], cwd=self.root, env=e, input=input,
                           capture_output=True, timeout=timeout)
        out = p.stdout.decode("utf-8", "replace").strip()
        if check and p.returncode != 0:
            raise GitError(f"git {' '.join(args)} に失敗: {p.stderr.decode('utf-8', 'replace').strip()}")
        return out

    def ok(self, *args: str) -> bool:
        return subprocess.run(["git", *args], cwd=self.root, capture_output=True).returncode == 0

    def _ident_env(self) -> dict:
        if self.run("config", "user.name", check=False) and self.run("config", "user.email", check=False):
            return {}
        return {"GIT_AUTHOR_NAME": "research-bot", "GIT_AUTHOR_EMAIL": "research-bot@invalid",
                "GIT_COMMITTER_NAME": "research-bot", "GIT_COMMITTER_EMAIL": "research-bot@invalid"}

    # ---- 参照 -----------------------------------------------------------------
    def fetch(self) -> None:
        self.run("fetch", "--prune", self.remote)

    def base_ref(self) -> str:
        return f"{self.remote}/{self.base}"

    def ls_remote(self, pattern: str) -> dict[str, str]:
        out = self.run("ls-remote", self.remote, pattern, check=False)
        res = {}
        for line in out.splitlines():
            if "\t" in line:
                sha, ref = line.split("\t", 1)
                res[ref] = sha
        return res

    def show_base_file(self, rel: str) -> str:
        return self.run("show", f"{self.base_ref()}:{rel}")

    # ---- 確保 -----------------------------------------------------------------
    def claims(self) -> dict[str, str]:
        """{確保名: sha}"""
        return {ref.removeprefix("refs/heads/claim/"): sha
                for ref, sha in self.ls_remote("refs/heads/claim/*").items()}

    def _claim_commit(self, name: str, agent: str) -> str:
        base = self.run("rev-parse", self.base_ref())
        msg = f"claim {name} by {agent} at {int(time.time())}"
        return self.run("commit-tree", f"{base}^{{tree}}", "-p", base, "-m", msg, env=self._ident_env())

    def commit_time(self, sha: str) -> int:
        return int(self.run("log", "-1", "--format=%ct", sha))

    def claim(self, name: str, agent: str, ttl: float) -> bool:
        ref = f"refs/heads/claim/{name}"
        commit = self._claim_commit(name, agent)
        if self.ok("push", self.remote, f"{commit}:{ref}"):
            return True
        # 既存の確保がある: 期限切れなら引き継ぐ
        old = self.ls_remote(ref).get(ref)
        if not old:
            return False
        self.run("fetch", self.remote, ref, check=False)
        try:
            age = time.time() - self.commit_time(old)
        except GitError:
            return False
        if age <= ttl:
            return False
        return self.ok("push", f"--force-with-lease={ref}:{old}", self.remote, f"{commit}:{ref}")

    def delete_branch(self, name: str) -> bool:
        return self.ok("push", self.remote, "--delete", name)

    # ---- 提出 -----------------------------------------------------------------
    def push_files_branch(self, branch: str, files: dict[str, bytes], message: str) -> str:
        """基準ブランチに files を足した単一コミットを作り、branch として push する。"""
        base = self.run("rev-parse", self.base_ref())
        fd, index = tempfile.mkstemp(prefix="gitidx-")
        os.close(fd)
        os.unlink(index)
        env = {"GIT_INDEX_FILE": index, **self._ident_env()}
        try:
            self.run("read-tree", base, env=env)
            for rel, data in files.items():
                blob = self.run("hash-object", "-w", "--stdin", input=data)
                self.run("update-index", "--add", "--cacheinfo", f"100644,{blob},{rel}", env=env)
            tree = self.run("write-tree", env=env)
        finally:
            if os.path.exists(index):
                os.unlink(index)
        commit = self.run("commit-tree", tree, "-p", base, "-m", message, env=self._ident_env())
        self.run("push", "--force", self.remote, f"{commit}:refs/heads/{branch}")
        return commit
