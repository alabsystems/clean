#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Self-test of scripts/rederive_chain.py: the derived-artifact walk.

Run by scripts/check_script_selftests.sh (the scripts/test_* glob). Every arm is a
synthetic tree on disk with small generator scripts of the shape the real chain has --
a `--check` that re-derives and compares, a no-argument mint, one generator that reads
another's output, one that guards a ratchet -- and the gate-registry node is run with
the REAL check_gate_registry R7 reading of a derived input set over a synthetic
registry. Nothing here builds or replays anything; the re-pin is a stand-in that
records its argv and moves the pin.

  * FRESH            nothing stale: no mint runs, the check is green.
  * ORDER            an upstream input moves: the upstream node is re-minted, and only
                     then is the downstream node judged stale and re-minted.
  * RATCHET          a mint that refuses (the shape of verdict_set's line ratchet) stops
                     the walk with exit 1; the node below it is not judged or touched.
  * STILL STALE      a mint that exits 0 and leaves its node stale is a refusal.
  * READ-ONLY        `--check` names the stale node and writes nothing.
  * REGISTRY         a row whose pinned DERIVED inputs moved is stale, by the registry's
                     own R7 reading; it is re-pinned through the re-pin command, one call
                     per drifted row, and a row whose inputs did not move is not; a re-pin
                     that refuses stops the walk.
  * VENDOR           the manifest is staged then minted from a directory under the tree's
                     `target/` that is gone afterwards; `--offline` drops `--download`.
  * TABLE            every script the live node table names exists in this tree.
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import rederive_chain as chain  # noqa: E402

# data/a.json = {"from": <inputs/a.txt>}; --check re-derives and compares.
GEN_A = r'''import json, sys
from pathlib import Path
want = json.dumps({"from": Path("inputs/a.txt").read_text()}) + "\n"
if "--check" in sys.argv:
    sys.exit(0 if Path("data/a.json").read_text() == want else 1)
Path("data/a.json").write_text(want)
'''
# data/b.json pins data/a.json's digest, as the IO contracts pin the verdict set's.
GEN_B = r'''import hashlib, json, sys
from pathlib import Path
want = json.dumps({"a": hashlib.sha256(Path("data/a.json").read_bytes()).hexdigest()}) + "\n"
if "--check" in sys.argv:
    sys.exit(0 if Path("data/b.json").read_text() == want else 1)
Path("data/b.json").write_text(want)
'''
# A generator that refuses to mint a value above its committed ratchet.
GEN_RATCHET = r'''import json, sys
from pathlib import Path
value = len(Path("inputs/a.txt").read_text())
committed = json.loads(Path("data/r.json").read_text())
if "--check" in sys.argv:
    sys.exit(0 if committed["value"] == value else 1)
if value > committed["baseline"]:
    print(f"ratchet EXCEEDED: {value} > {committed['baseline']}", file=sys.stderr)
    sys.exit(1)
Path("data/r.json").write_text(json.dumps({"value": value, "baseline": committed["baseline"]}) + "\n")
'''
# A mint that exits 0 and writes nothing.
GEN_LAZY = 'import sys\nsys.exit(0 if "--check" not in sys.argv else 1)\n'
# Records every call; used to see what a node ran.
RECORDER = r'''import sys
from pathlib import Path
with open("calls.log", "a") as fh:
    fh.write(" ".join([Path(sys.argv[0]).name, *sys.argv[1:]]) + "\n")
'''
# A gate that derives its inputs, as check_lint_coverage does.
SUBJECT = r'''import sys
ANSWERS_PINNED_INPUTS = True
if "--pinned-inputs" in sys.argv:
    print("inputs/x.txt")
'''
# The re-pin stand-in: records its argv, then moves the row's input pin (a green replay).
REPIN = RECORDER + r'''
import hashlib, json
if "--fail" in Path("repin.mode").read_text():
    print("refusing to re-pin -- its recorded demonstration does NOT replay", file=sys.stderr)
    sys.exit(1)
doc = json.loads(Path("data/gate_registry.json").read_text())
for row in doc["rows"]:
    if row["id"] == sys.argv[-1]:
        row["demonstrated"]["inputs"] = {
            "inputs/x.txt": hashlib.sha256(Path("inputs/x.txt").read_bytes()).hexdigest()}
Path("data/gate_registry.json").write_text(json.dumps(doc, indent=2) + "\n")
'''


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Tree:
    def __init__(self, base: Path) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="rederive-", dir=base))
        for rel, text in (("scripts/gen_a.py", GEN_A), ("scripts/gen_b.py", GEN_B),
                          ("scripts/gen_ratchet.py", GEN_RATCHET), ("scripts/gen_lazy.py", GEN_LAZY),
                          ("scripts/recorder.py", RECORDER), ("scripts/check_alpha.py", SUBJECT),
                          ("scripts/repin.py", REPIN), ("inputs/a.txt", "one"),
                          ("inputs/x.txt", "x1"), ("repin.mode", "ok\n")):
            self.write(rel, text)
        self.write("data/r.json", json.dumps({"value": 3, "baseline": 3}) + "\n")
        for script in ("gen_a.py", "gen_b.py"):
            self.py(f"scripts/{script}")
        row = {"id": "check_alpha", "path": "scripts/check_alpha.py",
               "demonstrated": {"inputs": {"inputs/x.txt": sha(self.root / "inputs/x.txt")}}}
        quiet = {"id": "check_quiet", "path": "scripts/recorder.py", "demonstrated": {}}
        self.write("data/gate_registry.json", json.dumps({"rows": [row, quiet]}, indent=2) + "\n")

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def py(self, *argv: str) -> None:
        subprocess.run([sys.executable, *argv], cwd=self.root, check=True)

    def ctx(self, offline: bool = False) -> chain.Context:
        return chain.Context(self.root, offline=offline)

    def calls(self) -> list[str]:
        log = self.root / "calls.log"
        return log.read_text().splitlines() if log.is_file() else []

    def snapshot(self) -> dict[str, bytes]:
        return {p.relative_to(self.root).as_posix(): p.read_bytes()
                for p in sorted(self.root.rglob("*")) if p.is_file()}


A = chain.Node("a", ("data/a.json",), ("scripts/gen_a.py", "--check"), (("scripts/gen_a.py",),))
B = chain.Node("b", ("data/b.json",), ("scripts/gen_b.py", "--check"), (("scripts/gen_b.py",),))
RATCHET = chain.Node("r", ("data/r.json",), ("scripts/gen_ratchet.py", "--check"),
                     (("scripts/gen_ratchet.py",),))
LAZY = chain.Node("lazy", (), ("scripts/gen_lazy.py", "--check"), (("scripts/gen_lazy.py",),))
REGISTRY = chain.GateRegistry("registry", ("data/gate_registry.json",), ("scripts/recorder.py",),
                              repin=("scripts/repin.py", "--repin"))


class Walk(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.base = Path(tempfile.mkdtemp(prefix="test-rederive-chain-"))

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.base, ignore_errors=True)

    def test_fresh_tree_mints_nothing(self) -> None:
        tree = Tree(self.base)
        ctx = tree.ctx()
        self.assertEqual(chain.rederive(ctx, (A, B)), 0)
        self.assertEqual(ctx.log, [])
        self.assertEqual(chain.check(tree.ctx(), (A, B)), 0)

    def test_upstream_move_re_mints_in_dependency_order(self) -> None:
        tree = Tree(self.base)
        tree.write("inputs/a.txt", "two")
        ctx = tree.ctx()
        self.assertEqual(chain.rederive(ctx, (A, B)), 0)
        self.assertEqual(ctx.log, ["a: scripts/gen_a.py -> 0", "b: scripts/gen_b.py -> 0"])
        self.assertIn('"two"', (tree.root / "data/a.json").read_text())
        self.assertEqual(chain.check(tree.ctx(), (A, B)), 0)

    def test_check_is_read_only_and_names_the_stale_node(self) -> None:
        tree = Tree(self.base)
        tree.write("inputs/a.txt", "two")
        before = tree.snapshot()
        self.assertEqual(chain.check(tree.ctx(), (A, B)), 1)
        self.assertEqual(tree.snapshot(), before)

    def test_a_ratchet_refusal_stops_the_walk(self) -> None:
        tree = Tree(self.base)
        tree.write("inputs/a.txt", "longer")  # 6 > baseline 3, and a.json is stale too
        before_b = (tree.root / "data/b.json").read_bytes()
        ctx = tree.ctx()
        self.assertEqual(chain.rederive(ctx, (RATCHET, A, B)), 1)
        self.assertEqual(ctx.log, ["r: scripts/gen_ratchet.py -> 1"])
        self.assertEqual((tree.root / "data/b.json").read_bytes(), before_b)

    def test_a_mint_that_leaves_its_node_stale_is_refused(self) -> None:
        """Refused where it happens: the stale node below it (a.json, its input moved) is
        not minted over an upstream that is still stale."""
        tree = Tree(self.base)
        tree.write("inputs/a.txt", "two")
        ctx = tree.ctx()
        self.assertEqual(chain.rederive(ctx, (LAZY, A)), 1)
        self.assertEqual(ctx.log, ["lazy: scripts/gen_lazy.py -> 0"])


class GateRegistryNode(unittest.TestCase):
    """The real check_gate_registry R7 reading of a derived input set, on a synthetic
    registry; the re-pin is the stand-in."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.base = Path(tempfile.mkdtemp(prefix="test-rederive-registry-"))

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.base, ignore_errors=True)

    def test_unmoved_inputs_are_fresh(self) -> None:
        tree = Tree(self.base)
        self.assertEqual(REGISTRY.stale(tree.ctx()), "")
        self.assertEqual(chain.rederive(tree.ctx(), (REGISTRY,)), 0)
        self.assertNotIn("repin.py", " ".join(tree.calls()))

    def test_a_moved_derived_input_is_re_pinned_by_its_row_alone(self) -> None:
        tree = Tree(self.base)
        tree.write("inputs/x.txt", "x2")
        self.assertIn("check_alpha (changed: inputs/x.txt)", REGISTRY.stale(tree.ctx()))
        self.assertEqual(chain.rederive(tree.ctx(), (REGISTRY,)), 0)
        repins = [c for c in tree.calls() if c.startswith("repin.py")]
        self.assertEqual(repins, ["repin.py --repin check_alpha"])
        self.assertEqual(REGISTRY.stale(tree.ctx()), "")

    def test_a_refused_re_pin_stops_the_walk(self) -> None:
        tree = Tree(self.base)
        tree.write("inputs/x.txt", "x2")
        tree.write("repin.mode", "--fail\n")
        before_b = (tree.root / "data/b.json").read_bytes()
        ctx = tree.ctx()
        self.assertEqual(chain.rederive(ctx, (REGISTRY, B)), 1)
        self.assertEqual(ctx.log, ["registry: scripts/repin.py --repin check_alpha -> 1"])
        self.assertEqual((tree.root / "data/b.json").read_bytes(), before_b)

    def test_an_underivable_input_set_is_a_refusal(self) -> None:
        tree = Tree(self.base)
        tree.write("scripts/check_alpha.py", SUBJECT.replace("inputs/x.txt", "inputs/gone.txt"))
        self.assertEqual(chain.rederive(tree.ctx(), (REGISTRY,)), 1)


class VendorNode(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.base = Path(tempfile.mkdtemp(prefix="test-rederive-vendor-"))

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.base, ignore_errors=True)

    def run_vendor(self, offline: bool) -> tuple[int, list[str], Path]:
        tree = Tree(self.base)
        # --check fails once (stale), then passes after the two mint calls.
        tree.write("scripts/vendor.py", RECORDER + r'''
calls = Path("calls.log").read_text().splitlines()
if "--check" in sys.argv:
    sys.exit(0 if len(calls) > 1 else 1)
if "--stage-third-party" in sys.argv:
    Path(sys.argv[2]).mkdir(parents=True)
''')
        node = chain.VendorManifest("vendor", ("data/vendor_manifest.json",),
                                    ("scripts/vendor.py", "--check"))
        rc = chain.rederive(tree.ctx(offline=offline), (node,))
        return rc, tree.calls(), tree.root

    def test_staged_under_target_then_minted_and_cleaned(self) -> None:
        rc, calls, root = self.run_vendor(offline=False)
        self.assertEqual(rc, 0)
        stage = f"target/rederive-vendor-{os.getpid()}"
        self.assertEqual(calls[1:3], [f"vendor.py --stage-third-party {stage} --download",
                                      f"vendor.py {stage}"])
        self.assertFalse((root / stage).exists())

    def test_offline_stages_from_the_cache_only(self) -> None:
        rc, calls, _ = self.run_vendor(offline=True)
        self.assertEqual(rc, 0)
        self.assertNotIn("--download", " ".join(calls))


class LiveTable(unittest.TestCase):
    def test_every_script_the_chain_names_exists(self) -> None:
        for node in chain.NODES:
            argvs = (node.check, *node.mint, *((node.repin,) if hasattr(node, "repin") else ()))
            for argv in argvs:
                self.assertTrue((ROOT / argv[0]).is_file(), f"{node.name}: {argv[0]}")
            for out in node.outputs:
                self.assertTrue((ROOT / out).is_file(), f"{node.name}: {out}")

    def test_outputs_and_usage(self) -> None:
        out = subprocess.run([sys.executable, str(SCRIPTS / "rederive_chain.py"), "--outputs"],
                             capture_output=True, text=True, check=True).stdout.split()
        self.assertEqual(out, [o for node in chain.NODES for o in node.outputs])
        bad = subprocess.run([sys.executable, str(SCRIPTS / "rederive_chain.py"), "--nope"],
                             capture_output=True, text=True)
        self.assertEqual(bad.returncode, 2)


if __name__ == "__main__":
    unittest.main()
