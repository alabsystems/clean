#!/usr/bin/env python3
# Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
"""Transport-only production-launch controls; no lock/compiler/proof verdict.

Run with a maintained native GNU owner. Expected identities come from the
caller's actual descriptors; no fake scheduler, token or SDK/CPU claim is made.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shlex
import sys
import tempfile
import unittest
from unittest.mock import patch

import bump_ay_pin as ay
import check_workspace_dependency_boundary as boundary
import dev_ir_aliases as aliases

SINGLE = ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1", "TRUST_CPU_IMPLICIT_FD")
SETS = ("ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS")
GNU = ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS")


def identity(fd):
    value = os.fstat(fd)
    return [value.st_dev, value.st_ino, value.st_mode, value.st_rdev]


def actual_descriptors():
    fds = set()
    for name in SINGLE:
        if name in os.environ:
            fds.add(int(os.environ[name]))
    for name in SETS:
        if name in os.environ:
            fds.update(map(int, os.environ[name].split(",")))
    for name in GNU:
        for pair in re.finditer(r"(?:^|\s)--jobserver-(?:auth|fds)=([0-9]+),([0-9]+)(?=\s|$)", os.environ.get(name, "")):
            fds.update(map(int, pair.groups()))
    if not any("--jobserver-auth=" in os.environ.get(n, "") for n in GNU):
        raise RuntimeError("transport regression requires a real maintained native GNU owner")
    return sorted(fds)


class ProductionLaunchTransport(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = {str(fd): identity(fd) for fd in actual_descriptors()}
        print("ACTUAL_TRANSPORT=" + json.dumps({
            "identities": cls.expected,
            "present": [name for name in (*SINGLE, *SETS, *GNU) if name in os.environ],
            "absent_not_tested": [name for name in (*SINGLE, *SETS) if name not in os.environ],
        }), flush=True)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="clean-transport-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.log = self.root / "calls"
        child = self.root / "transport_child.py"
        child.write_text(r"""import json,os,sys
from pathlib import Path
for fd,wanted in json.loads(os.environ["CLEAN_TRANSPORT_EXPECTED"]).items():
    try:
        s=os.fstat(int(fd)); got=[s.st_dev,s.st_ino,s.st_mode,s.st_rdev]
    except OSError as error:
        raise SystemExit("transport descriptor closed: "+fd)
    if got!=wanted:
        raise SystemExit("transport descriptor replaced: "+fd)
unrelated=os.environ.get("CLEAN_TRANSPORT_UNRELATED")
if unrelated:
    fd,wanted=json.loads(unrelated)
    try:
        s=os.fstat(fd);got=[s.st_dev,s.st_ino,s.st_mode,s.st_rdev]
    except OSError:
        got=None
    if got==wanted:
        raise SystemExit("unadvertised descriptor inherited")
with open(os.environ["CLEAN_TRANSPORT_LOG"],"a") as log:
    log.write(json.dumps(sys.argv[1:])+"\n")
if "--select" in sys.argv:
    print(os.environ["CLEAN_TRANSPORT_FRONTEND"]);sys.exit(0)
if "--offline" in sys.argv and os.environ.get("CLEAN_TRANSPORT_OFFLINE")=="fail":
    print("fixture-offline-cache-refusal",file=sys.stderr);sys.exit(19)
if "--offline" not in sys.argv and os.environ.get("CLEAN_TRANSPORT_ONLINE")=="fail":
    print("fixture-terminal-online-refusal",file=sys.stderr);sys.exit(20)
metadata=os.environ.get("CLEAN_TRANSPORT_METADATA")
print(Path(metadata).read_text() if metadata else "{}")
""")
        self.probe = self.root / "transport-probe"
        self.probe.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + " " + shlex.quote(str(child)) + ' "$@"\n')
        self.probe.chmod(0o700)
        frontend = self.root / "scripts/rust_frontend.sh"
        frontend.parent.mkdir()
        frontend.write_text("#!/bin/sh\nexec " + shlex.quote(str(self.probe)) + ' --select "$@"\n')
        environment = {
            "CLEAN_TRANSPORT_EXPECTED": json.dumps(self.expected),
            "CLEAN_TRANSPORT_LOG": str(self.log),
            "CLEAN_TRANSPORT_FRONTEND": str(self.probe),
        }
        for item in [patch.dict(os.environ, environment), patch.object(boundary, "ROOT", self.root),
                     patch.object(boundary, "FRONTEND", frontend)]:
            item.start()
            self.addCleanup(item.stop)
        self.locks = {"Cargo.lock": '[[package]]\nname="probe"\nversion="0.0.0"\nsource="git+https://example.invalid/transport?rev=' + "a"*40 + "#" + "a"*40 + '"\n'}

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def test_boundary_frontend_selector(self):
        self.assertEqual(boundary.resolve_targo(), str(self.probe))
        self.assertEqual(len(self.calls()), 1)

    def test_offline_lock_launch(self):
        boundary.check_git_pinned_locks_resolve(self.locks, str(self.probe))
        self.assertIn("--offline", self.calls()[0])

    def test_online_retry_keeps_transport_and_terminal_stderr(self):
        with patch.dict(os.environ, {"CLEAN_TRANSPORT_OFFLINE": "fail", "CLEAN_TRANSPORT_ONLINE": "fail"}):
            with self.assertRaisesRegex(boundary.BoundaryViolation, "fixture-terminal-online-refusal"):
                boundary.check_git_pinned_locks_resolve(self.locks, str(self.probe))
        calls = self.calls()
        self.assertEqual(len(calls), 2)
        self.assertIn("--offline", calls[0])
        self.assertNotIn("--offline", calls[1])

    def test_alias_selector_and_metadata(self):
        # Minimal graph DATA exercises the unchanged projection; it is no lock
        # qualification and no assertion about any real IR revision.
        rev, other = "a"*40, "b"*40
        source = lambda r: "git+" + aliases.IR_URL + "?rev=" + r + "#" + r
        manifest = ('[workspace.metadata.clean]\ndev-only-ir-aliases=["probe-dev"]\n'
                    '[workspace.dependencies.probe-dev]\npackage="trust-ir"\ngit="' + aliases.IR_URL + '"\nrev="' + other + '"\n')
        member = '[dev-dependencies.probe-dev]\nworkspace=true\n'
        manifests = {"Cargo.toml": manifest, "member/Cargo.toml": member}
        metadata = {
            "workspace_root": str(self.root), "workspace_members": ["member"],
            "packages": [{"id":"member","name":"member","manifest_path":str(self.root/"member/Cargo.toml")},
                         {"id":"production","name":"trust-ir","version":"0.0.0","source":source(rev)},
                         {"id":"development","name":"trust-ir","version":"0.0.0","source":source(other)}],
            "resolve":{"nodes":[{"id":"member","deps":[
                {"name":"production","pkg":"production","dep_kinds":[{"kind":None}]},
                {"name":"probe_dev","pkg":"development","dep_kinds":[{"kind":"dev"}]}]},
                {"id":"production","deps":[]},{"id":"development","deps":[]}]},
        }
        data = self.root/"metadata.json"
        data.write_text(json.dumps(metadata))
        lock = '[[package]]\nname="trust-ir"\nversion="0.0.0"\nsource="' + source(other) + '"\n'
        with patch.dict(os.environ, {"CLEAN_TRANSPORT_METADATA": str(data)}):
            result = aliases.production_locks(self.root, manifests, {"Cargo.lock":lock})
        self.assertEqual(result["Cargo.lock"], "")
        self.assertEqual(len(self.calls()), 2)

    def test_ay_commands_after_environment_overlays(self):
        commands = ay.Commands(self.root, self.probe)
        commands.frontend(["metadata"])
        commands.run([str(self.probe), "git-overlay-probe"], cwd=self.root, git=True)
        self.assertEqual(len(self.calls()), 2)

    def test_root_metadata_launch(self):
        result = boundary.workspace_metadata(str(self.probe))
        self.assertEqual(result.returncode, 0)
        self.assertIn("--no-deps", self.calls()[0])

    def test_unadvertised_descriptor_is_not_forwarded(self):
        r, w = os.pipe()
        try:
            with patch.dict(os.environ, {"CLEAN_TRANSPORT_UNRELATED": json.dumps([r, identity(r)])}):
                self.assertEqual(boundary.workspace_metadata(str(self.probe)).returncode, 0)
            self.assertEqual(len(self.calls()), 1)
        finally:
            os.close(r)
            os.close(w)

    def test_malformed_or_closed_locator_refuses_before_child(self):
        # Negative locator corruption only: these bytes grant no resource.
        read_fd, write_fd = os.pipe()
        os.close(read_fd)
        os.close(write_fd)
        alias_manifests = {
            "Cargo.toml": '[workspace.metadata.clean]\ndev-only-ir-aliases=["probe-dev"]\n'
                '[workspace.dependencies.probe-dev]\npackage="trust-ir"\ngit="' + aliases.IR_URL + '"\nrev="' + "b"*40 + '"\n',
            "member/Cargo.toml": '[dev-dependencies.probe-dev]\nworkspace=true\n',
        }
        launchers = [lambda: boundary.resolve_targo(),
                     lambda: boundary.check_git_pinned_locks_resolve(self.locks, str(self.probe)),
                     lambda: ay.Commands(self.root, self.probe).frontend(["metadata"]),
                     lambda: aliases.production_locks(self.root, alias_manifests, {"Cargo.lock": ""}),
                     lambda: aliases.production_locks(self.root, alias_manifests, {"Cargo.lock": ""}, str(self.probe)),
                     lambda: boundary.workspace_metadata(str(self.probe))]
        corruptions = [{"ATERM_SDK_LEASE_V3": "malformed"},
                       {"ATERM_SDK_LEASE_V3": str(read_fd)},
                       {"CARGO_MAKEFLAGS": f"--jobserver-auth={read_fd},{write_fd}"}]
        for corruption in corruptions:
            for launch in launchers:
                with self.subTest(corruption=corruption, launch=launch):
                    with patch.dict(os.environ, corruption):
                        with self.assertRaises((RuntimeError, boundary.BoundaryViolation)):
                            launch()
                    self.assertEqual(self.calls(), [])


class LocatorSyntax(unittest.TestCase):
    def test_recognized_fd_field_syntax_is_non_authority(self):
        # Pure OS unit data, never passed to Targo/native owners as SDK or CPU
        # authority. Actual absent SDK/CPU contexts remain NOT_TESTED above.
        from resource_transport import resource_fds
        r, w = os.pipe()
        try:
            self.assertEqual(resource_fds({}), ())
            for name in SINGLE:
                self.assertEqual(resource_fds({name: str(r)}), (r,))
            for name in SETS:
                self.assertEqual(resource_fds({name: f"{r},{w}"}), tuple(sorted([r,w])))
                for value in ["", f"{r},{r}", f"{r},x"]:
                    with self.assertRaises(RuntimeError):
                        resource_fds({name:value})
            for name in SINGLE:
                for value in ["", "0", "2", "-1", "x", "01"]:
                    with self.assertRaises(RuntimeError):
                        resource_fds({name:value})
            for name in GNU:
                self.assertEqual(resource_fds({name:f"-j --jobserver-auth={r},{w}"}), tuple(sorted([r,w])))
            # Named paths/native handoffs are preserved for the native importer;
            # this numeric transport helper neither opens nor authenticates them.
            self.assertEqual(resource_fds({"CARGO_MAKEFLAGS":"--jobserver-auth=fifo:/not-opened"}), ())
        finally:
            os.close(r)
            os.close(w)


if __name__ == "__main__":
    unittest.main(verbosity=2)
