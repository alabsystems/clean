#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Native authority protocol controls; no network, compiling or cached verdicts."""
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest
import zlib
from unittest.mock import patch

import compiler_pin_authority as authority

REV = "a" * 40


def oid(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


class Peer:
    def __init__(self):
        self.data = b'[workspace.dependencies]\r\ntrust-ir = {rev="' + REV.encode() + b'"}\r\n'
        self.tree = b"100644 blob " + oid(self.data).encode() + b"\tCargo.toml\0"
        self.alternate = b""
        self.bad = None
        self.calls = []

    def __call__(self, args, **kwargs):
        self.calls.append(args)
        assert kwargs["env"]["GIT_NO_LAZY_FETCH"] == "1"
        assert kwargs["env"]["GIT_NO_REPLACE_OBJECTS"] == "1"
        assert kwargs["stdout"] == subprocess.PIPE
        assert "text" not in kwargs
        if args[1:3] == ["repo", "fetch-main"]:
            assert args[-1] == "--blobless"
            value = b""
        elif args[1] == "cat":
            assert args[2] == f"alabsystems/trust-cg@{REV}:Cargo.toml"
            value = self.data
        elif args[1] == "init":
            value = b""
        elif args[1] == "rev-parse":
            assert args[-1] == REV + "^{commit}"
            value = ("b" * 40 if self.bad == "commit" else REV).encode()
        elif args[1] == "merge-base":
            assert args[2:] == ["--is-ancestor", REV, authority.MAIN]
            value = b""
        elif args[1] == "ls-tree":
            assert args[2:5] == ["-z", REV, "--"]
            value = self.alternate if args[-1] == "Targo.toml" else self.tree
        else:
            raise AssertionError(f"unexpected operation, including direct Git fallback: {args}")
        bad = ((self.bad == "fetch" and args[1:3] == ["repo", "fetch-main"])
               or (self.bad == "ancestor" and args[1] == "merge-base"))
        return subprocess.CompletedProcess(args, 1 if bad else 0, stdout=value)


class AuthorityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.peer = Peer()
        self.which = patch.object(authority.shutil, "which", side_effect=lambda name: "/native/" + name)
        self.which.start()
        self.addCleanup(self.which.stop)

    def make(self):
        return authority.Authority(self.root / "objects", authority.REPOSITORIES[1], REV,
                                   execute=self.peer)

    def test_exact_fresh_main_and_raw_bytes(self):
        self.assertEqual(self.make().manifest(), self.peer.data)
        self.assertEqual(len([a for a in self.peer.calls if a[1] == "cat"]), 1)
        self.assertFalse(any(a[1] in {"fetch", "show"} for a in self.peer.calls))

    def test_wrong_selected_commit_refuses(self):
        self.peer.bad = "commit"
        with self.assertRaisesRegex(authority.Refusal, "different selected"):
            self.make()

    def test_off_main_and_refused_fetch_have_no_fallback(self):
        for cause in ["fetch", "ancestor"]:
            self.peer.bad = cause
            with self.subTest(cause=cause), self.assertRaises(authority.Refusal):
                authority.Authority(self.root / cause, authority.REPOSITORIES[1], REV,
                                    execute=self.peer)
        self.assertFalse(any(a[1] == "cat" for a in self.peer.calls))

    def test_missing_native_agh_refuses_before_creating_store(self):
        with patch.object(authority.shutil, "which", return_value=None):
            with self.assertRaises(authority.Refusal):
                self.make()
        self.assertFalse((self.root / "objects").exists())
        self.assertEqual(self.peer.calls, [])

    def test_noncanonical_repository_and_revision_refuse_before_transport(self):
        for repository, revision in [("other/trust-cg", REV), (authority.REPOSITORIES[1], REV[:12]),
                                     (authority.REPOSITORIES[1], REV.upper())]:
            with self.subTest(repository=repository, revision=revision), self.assertRaises(authority.Refusal):
                authority.Authority(self.root / "objects", repository, revision, execute=self.peer)
        self.assertEqual(self.peer.calls, [])

    def test_regular_exact_manifest_is_required_before_cat(self):
        a = self.make()
        for entry in [b"", b"120000 blob " + b"a" * 40 + b"\tCargo.toml\0",
                      b"160000 commit " + b"a" * 40 + b"\tCargo.toml\0",
                      self.peer.tree.replace(b"Cargo.toml", b"other.toml"),
                      self.peer.tree * 2, self.peer.tree.replace(b"blob ", b"blob x")]:
            self.peer.tree = entry
            with self.subTest(entry=entry), self.assertRaises(authority.Refusal):
                a.manifest()
        self.assertFalse(any(args[1] == "cat" for args in self.peer.calls))

    def test_targo_precedence_refuses_before_cat(self):
        a = self.make()
        self.peer.alternate = b"100644 blob " + b"a" * 40 + b"\tTargo.toml\0"
        with self.assertRaisesRegex(authority.Refusal, "precedence"):
            a.manifest()
        self.assertFalse(any(args[1] == "cat" for args in self.peer.calls))

    def test_tampered_truncated_or_newline_normalized_bytes_refuse(self):
        a = self.make()
        original = self.peer.data
        for data in [original[:-1], original + b"x", original.replace(b"\r\n", b"\n")]:
            self.peer.data = data
            with self.subTest(data=data), self.assertRaisesRegex(authority.Refusal, "authenticated Git blob"):
                a.manifest()

    def test_nonbyte_transport_is_refused(self):
        a = self.make()
        self.peer.data = self.peer.data.decode()
        with self.assertRaisesRegex(authority.Refusal, "raw bytes"):
            a.manifest()

    def test_unknown_manifest_path_refuses_before_transport(self):
        a = self.make()
        before = len(self.peer.calls)
        for path in ["../Cargo.toml", "crates/x/Cargo.toml", ""]:
            with self.subTest(path=path), self.assertRaises(authority.Refusal):
                a.entry(path)
        self.assertEqual(len(self.peer.calls), before)

    def test_ambient_git_indirection_is_removed(self):
        injected = {key: "wrong" for key in ["GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL", "GIT_DIR",
                                             "GIT_WORK_TREE", "GIT_OBJECT_DIRECTORY",
                                             "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_REPLACE_REF_BASE"]}
        with patch.dict(authority.os.environ, injected):
            env = authority.git_environment()
        self.assertFalse((set(injected) - {"GIT_CONFIG_GLOBAL"}) & set(env))
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], authority.os.devnull)
        self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(env["GIT_TERMINAL_PROMPT"], "0")

    def test_oversized_transport_refuses_before_hashing(self):
        a = self.make()
        self.peer.data = b"x" * (32 * 1024 * 1024 + 1)
        with self.assertRaisesRegex(authority.Refusal, "byte limit"):
            a.manifest()

    def test_success_writes_exact_bytes_only_after_both_authorities(self):
        manifest = self.root / "manifest"
        with patch.object(authority, "Authority") as fetch:
            fetch.return_value.manifest.return_value = self.peer.data
            authority.prepare(self.root / "stores", manifest, REV, "b" * 40)
            self.assertEqual([c.args[1:] for c in fetch.call_args_list],
                             [(authority.REPOSITORIES[0], REV),
                              (authority.REPOSITORIES[1], "b" * 40)])
        self.assertEqual(manifest.read_bytes(), self.peer.data)
        with patch.object(authority, "Authority") as fetch:
            with self.assertRaises(authority.Refusal):
                authority.prepare(self.root / "another", manifest, REV, REV)
            fetch.assert_not_called()

    def test_both_revisions_validate_before_first_fetch_or_write(self):
        output = self.root / "manifest"
        with patch.object(authority, "Authority") as fetch:
            with self.assertRaises(authority.Refusal):
                authority.prepare(self.root / "stores", output, REV, "bad")
            fetch.assert_not_called()
        self.assertFalse(output.exists())
        self.assertFalse((self.root / "stores").exists())


class HostileGitTests(unittest.TestCase):
    def test_actual_graft_template_and_namespace_do_not_forge_main_ancestry(self):
        git = authority.shutil.which("git")
        self.assertIsNotNone(git, "the authority protocol requires actual Git")
        base = Path(tempfile.gettempdir()) / ".ubd"
        base.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base, prefix="clean-authority-graft-") as temporary:
            root = Path(temporary)
            objects = []
            def obj(kind, data):
                raw = kind.encode() + b" " + str(len(data)).encode() + b"\0" + data
                identity = hashlib.sha1(raw).hexdigest()
                objects.append((identity, zlib.compress(raw)))
                return identity
            tree = obj("tree", b"")
            def commit(message):
                return obj("commit", (f"tree {tree}\nauthor Fixture <fixture@example.invalid> 1 +0000\n"
                    f"committer Fixture <fixture@example.invalid> 1 +0000\n\n{message}\n").encode())
            main, unrelated = commit("main"), commit("unrelated")
            template = root / "template"
            (template / "info").mkdir(parents=True)
            graft = template / "info/grafts"
            graft.write_text(f"{main} {unrelated}\n")
            config = root / "global-config"
            config.write_text(f"[init]\n templateDir = {template}\n")
            def execute(args, **kwargs):
                if args[0] == "/simulated/agh":
                    self.assertEqual(args[1:3], ["repo", "fetch-main"])
                    for identity, data in objects:
                        target = kwargs["cwd"] / "objects" / identity[:2] / identity[2:]
                        target.parent.mkdir(exist_ok=True)
                        target.write_bytes(data)
                    for ref, value in [(authority.MAIN, main),
                            ("refs/namespaces/evil/refs/agh/fetched-main", unrelated)]:
                        subprocess.run([git, "update-ref", ref, value], cwd=kwargs["cwd"],
                                       env=kwargs["env"], check=True)
                    return subprocess.CompletedProcess(args, 0, stdout=b"")
                return subprocess.run(args, **kwargs)
            poison = {"GIT_GRAFT_FILE": str(graft), "GIT_TEMPLATE_DIR": str(template),
                      "GIT_CONFIG_GLOBAL": str(config), "GIT_NAMESPACE": "evil",
                      "GIT_NO_REPLACE_OBJECTS": "1"}
            with patch.dict(authority.os.environ, poison), \
                    patch.object(authority.shutil, "which", side_effect=lambda name:
                                 git if name == "git" else "/simulated/agh"):
                with self.assertRaisesRegex(authority.Refusal, "merge-base"):
                    authority.Authority(root / "objects", authority.REPOSITORIES[1], unrelated,
                                        execute=execute)
            self.assertFalse((root / "objects/info/grafts").exists())
            control = subprocess.run([git, "merge-base", "--is-ancestor", unrelated, authority.MAIN],
                                     cwd=root / "objects", stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     env={**authority.os.environ, "GIT_GRAFT_FILE": str(graft),
                                          "GIT_NO_REPLACE_OBJECTS": "1"})
            self.assertEqual(control.returncode, 0, control.stderr)

    def test_every_ambient_graft_template_shallow_and_format_input_is_removed(self):
        names = {"GIT_GRAFT_FILE", "GIT_SHALLOW_FILE", "GIT_TEMPLATE_DIR", "GIT_NAMESPACE",
                 "GIT_DEFAULT_HASH", "GIT_DEFAULT_REF_FORMAT", "GIT_CONFIG_SYSTEM"}
        with patch.dict(authority.os.environ, {name: "poison" for name in names}):
            env = authority.git_environment()
        self.assertFalse(names.intersection(env))
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], authority.os.devnull)
        self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")


if __name__ == "__main__":
    unittest.main()
