#!/usr/bin/env python3
"""Ensure hook subprocesses inspect dependency repos without changing the staged index."""

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


WRAPPER = Path(__file__).resolve().parents[1] / ".githooks/with-clean-git-env"


def run(*args, cwd, env):
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()


class HookEnvironmentTest(unittest.TestCase):
    def test_foreign_repository_from_linked_worktree_preserves_staged_index(self):
        clean = os.environ.copy()
        local_vars = run("git", "rev-parse", "--local-env-vars", cwd=WRAPPER.parent, env=clean)
        for variable in local_vars.splitlines():
            clean.pop(variable, None)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            parent, worktree, dependency = (root / name for name in ("parent", "worktree", "dependency"))
            for repository in (parent, dependency):
                repository.mkdir()
                run("git", "init", "--quiet", cwd=repository, env=clean)
                run("git", "config", "user.name", "Hook test", cwd=repository, env=clean)
                run("git", "config", "user.email", "hook-test@example.invalid", cwd=repository, env=clean)
                (repository / "tracked.txt").write_text(repository.name + "\n")
                run("git", "add", "tracked.txt", cwd=repository, env=clean)
                run("git", "-c", "core.hooksPath=/dev/null", "commit", "--quiet", "-m", "fixture", cwd=repository, env=clean)
            run("git", "worktree", "add", "--quiet", "--detach", str(worktree), cwd=parent, env=clean)
            git_dir = run("git", "rev-parse", "--absolute-git-dir", cwd=worktree, env=clean)
            staged_index = root / "staged.index"
            inherited = dict(clean, GIT_DIR=git_dir, GIT_INDEX_FILE=str(staged_index),
                             HOOK_ENV_REGRESSION="preserved")
            run("git", "read-tree", "HEAD", cwd=worktree, env=inherited)
            before = hashlib.sha256(staged_index.read_bytes()).hexdigest()
            # The inherited hook context reproduces the actual wrong-repo lookup.
            self.assertEqual(run("git", "rev-parse", "HEAD", cwd=dependency, env=inherited),
                             run("git", "rev-parse", "HEAD", cwd=parent, env=clean))
            expected = run("git", "rev-parse", "HEAD", cwd=dependency, env=clean)
            self.assertEqual(run(str(WRAPPER), "git", "rev-parse", "HEAD", cwd=dependency, env=inherited), expected)
            (dependency / "new.txt").write_text("dependency-only staged change\n")
            run(str(WRAPPER), "git", "add", "new.txt", cwd=dependency, env=inherited)
            self.assertEqual(hashlib.sha256(staged_index.read_bytes()).hexdigest(), before)
            self.assertEqual(run(str(WRAPPER), "python3", "-c",
                                 "import os; print(os.environ['HOOK_ENV_REGRESSION'])",
                                 cwd=dependency, env=inherited), "preserved")


if __name__ == "__main__":
    unittest.main()
