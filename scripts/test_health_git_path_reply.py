#!/usr/bin/env python3
"""Use isolated real repositories to test the Git GC-log health lookup."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import system_health_check as health


class GitCommonDirectoryReply(unittest.TestCase):
    def test_external_git_directory_suffixes(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        for suffix in ("", " ", "\t", "\u00a0", "\u0085", "\u2028", "\u2029"):
            with self.subTest(suffix=repr(suffix)):
                with tempfile.TemporaryDirectory(prefix="health-git-reply-", dir=scratch) as td:
                    root = Path(td).resolve()
                    repo = root / "repo"
                    common = root / ("git-data" + suffix)
                    env = {"PATH": os.defpath, "GIT_CONFIG_NOSYSTEM": "1",
                           "GIT_CONFIG_GLOBAL": os.devnull}
                    with mock.patch.dict(os.environ, env, clear=True):
                        subprocess.run(["git", "init", "-q", "--separate-git-dir", str(common), str(repo)],
                                       check=True, capture_output=True)
                        # A neighboring directory must not hide this failure record.
                        (root / "git-data").mkdir(exist_ok=True)
                        (common / "gc.log").write_text("owned test failure record\n")
                        ok, message = health.check_worktree_gc_logs(repo)
                        self.assertFalse(ok, message)
                        self.assertIn("stale git gc.log", message)
                        resolved, error = health._resolve_git_common_dir(repo)
                        self.assertIsNone(error)
                        self.assertEqual(resolved, common)
                        (common / "gc.log").unlink()
                        self.assertTrue(health.check_worktree_gc_logs(repo)[0])

    def test_foreign_git_location_cannot_hide_local_gc_log(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        for name in ("GIT_DIR", "GIT_COMMON_DIR"):
            with self.subTest(variable=name):
                with tempfile.TemporaryDirectory(prefix="health-git-context-", dir=scratch) as td:
                    root = Path(td).resolve()
                    repo, foreign = root / "repo", root / "foreign"
                    env = {"PATH": os.defpath, "GIT_CONFIG_NOSYSTEM": "1",
                           "GIT_CONFIG_GLOBAL": os.devnull}
                    with mock.patch.dict(os.environ, env, clear=True):
                        for path in (repo, foreign):
                            subprocess.run(["git", "init", "-q", str(path)],
                                           check=True, capture_output=True)
                        (repo / ".git/gc.log").write_text("owned test failure record\n")
                        with mock.patch.dict(os.environ, {name: str(foreign / ".git")}):
                            ok, message = health.check_worktree_gc_logs(repo)
                            self.assertFalse(ok, message)
                            resolved, error = health._resolve_git_common_dir(repo)
                            self.assertIsNone(error)
                            self.assertEqual(resolved, repo / ".git")
                            self.assertEqual(os.environ[name], str(foreign / ".git"))

    def test_git_launch_errors_are_reported_without_escaping(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        for failure in ("missing-directory", "not-directory", "missing-git", "non-executable-git"):
            with self.subTest(failure=failure):
                with tempfile.TemporaryDirectory(prefix="health-git-launch-", dir=scratch) as td:
                    root = Path(td).resolve()
                    repo, tools = root / "repo", root / "tools"
                    tools.mkdir()
                    if failure == "not-directory":
                        repo.write_text("not a directory\n")
                    elif failure != "missing-directory":
                        repo.mkdir()
                    if failure == "non-executable-git":
                        (tools / "git").write_text("#!/bin/sh\nexit 0\n")
                        (tools / "git").chmod(0o600)
                    env = {"PATH": str(tools) if failure in {"missing-git", "non-executable-git"}
                           else os.defpath}
                    with mock.patch.dict(os.environ, env, clear=True):
                        ok, message = health.check_worktree_gc_logs(repo)
                        self.assertFalse(ok)
                        self.assertIn("could not launch git", message)
                        self.assertIn(str(repo), message)

    def test_report_metadata_falls_back_on_launch_failures(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        for failure in ("missing-directory", "not-directory", "missing-git", "non-executable-git"):
            for getter, expected in ((health._get_git_commit, "unknown"),
                                     (health._get_project_name, "repo")):
                with self.subTest(failure=failure, getter=getter.__name__):
                    with tempfile.TemporaryDirectory(prefix="health-metadata-", dir=scratch) as td:
                        root = Path(td).resolve()
                        repo, tools = root / "repo", root / "tools"
                        tools.mkdir()
                        if failure == "not-directory":
                            repo.write_text("not a directory\n")
                        elif failure != "missing-directory":
                            repo.mkdir()
                        if failure == "non-executable-git":
                            (tools / "git").write_text("#!/bin/sh\nexit 0\n")
                            (tools / "git").chmod(0o600)
                        env = {"PATH": str(tools) if failure in {"missing-git", "non-executable-git"}
                               else os.defpath}
                        with mock.patch.dict(os.environ, env, clear=True):
                            self.assertEqual(getter(repo), expected)

    def test_report_metadata_reads_a_real_repository(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="health-metadata-valid-", dir=scratch) as td:
            repo = Path(td).resolve()
            env = {"PATH": os.defpath, "GIT_CONFIG_NOSYSTEM": "1",
                   "GIT_CONFIG_GLOBAL": os.devnull}
            with mock.patch.dict(os.environ, env, clear=True):
                def git(*args):
                    return subprocess.check_output(["git", "-C", str(repo), *args],
                                                   stderr=subprocess.DEVNULL).decode().strip()
                git("init", "-q")
                git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                    "commit", "--allow-empty", "-qm", "fixture")
                git("remote", "add", "origin", "/fixtures/health-origin.git")
                self.assertEqual(health._get_git_commit(repo), git("rev-parse", "HEAD"))
                self.assertEqual(health._get_project_name(repo), "health-origin")

    def test_metadata_ignores_inherited_git_repository_locations(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="health-metadata-context-", dir=scratch) as td:
            root = Path(td).resolve()
            repo, foreign = root / "requested", root / "foreign"
            env = {"PATH": os.defpath, "GIT_CONFIG_NOSYSTEM": "1",
                   "GIT_CONFIG_GLOBAL": os.devnull}
            with mock.patch.dict(os.environ, env, clear=True):
                def git(path, *args):
                    return subprocess.check_output(["git", "-C", str(path), *args],
                                                   stderr=subprocess.DEVNULL).decode().strip()
                for path in (repo, foreign):
                    path.mkdir()
                    git(path, "init", "-q")
                    git(path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                        "commit", "--allow-empty", "-qm", path.name)
                    git(path, "remote", "add", "origin", f"/fixtures/{path.name}.git")
                expected_commit = git(repo, "rev-parse", "HEAD")
                self.assertNotEqual(expected_commit, git(foreign, "rev-parse", "HEAD"))
                locations = {
                    "GIT_DIR": str(foreign / ".git"),
                    "GIT_COMMON_DIR": str(foreign / ".git"),
                    "GIT_WORK_TREE": str(foreign),
                    "GIT_INDEX_FILE": str(foreign / ".git/index"),
                    "GIT_OBJECT_DIRECTORY": str(foreign / ".git/objects"),
                    "GIT_ALTERNATE_OBJECT_DIRECTORIES": str(foreign / ".git/objects"),
                    "GIT_PREFIX": "foreign/",
                }
                contexts = [(name, {name: value}) for name, value in locations.items()]
                contexts.append(("all-location-variables", locations))
                for name, context in contexts:
                    for getter, expected in ((health._get_git_commit, expected_commit),
                                             (health._get_project_name, "requested")):
                        with self.subTest(context=name, getter=getter.__name__):
                            with mock.patch.dict(os.environ, context):
                                self.assertEqual(getter(repo), expected)
                                for key, value in context.items():
                                    self.assertEqual(os.environ[key], value)
                                self.assertEqual(os.environ["PATH"], os.defpath)
                                self.assertEqual(os.environ["GIT_CONFIG_GLOBAL"], os.devnull)

    def test_command_launcher_reports_errors_and_preserves_results(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="health-command-", dir=scratch) as td:
            root = Path(td).resolve()
            blocked, regular = root / "blocked", root / "regular"
            blocked.write_text("#!/bin/sh\nexit 0\n")
            blocked.chmod(0o600)
            regular.write_text("not a directory\n")
            for executable in (root / "missing", blocked, regular / "child"):
                with self.subTest(executable=str(executable)):
                    ok, message = health.run_cmd([str(executable)])
                    self.assertFalse(ok)
                    self.assertIn("could not launch command", message)
                    self.assertIn(str(executable), message)
            self.assertEqual(health.run_cmd(["/bin/sh", "-c", "printf out; printf err >&2"]),
                             (True, "outerr"))
            self.assertEqual(health.run_cmd(["/bin/sh", "-c", "exit 7"]), (False, "exit 7"))

    def test_non_repository_refuses(self):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="health-git-not-repo-", dir=scratch) as td:
            env = {"PATH": os.defpath, "GIT_CONFIG_NOSYSTEM": "1",
                   "GIT_CONFIG_GLOBAL": os.devnull}
            with mock.patch.dict(os.environ, env, clear=True):
                common, error = health._resolve_git_common_dir(Path(td))
                self.assertIsNone(common)
                self.assertTrue(error)
                self.assertFalse(health.check_worktree_gc_logs(Path(td))[0])


if __name__ == "__main__":
    unittest.main()
