#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Self-test of the WS6.5 trust-ir pin transaction: leg table, coherence, driver.

Run by scripts/check_script_selftests.sh (the scripts/test_* glob). Every arm
is a fixture on disk: a synthetic Git repository with the exact leg shape of
this tree (nine trust-ir declarations in six manifests, three trust-cg
declarations, two lockfiles), mutated one leg at a time. Nothing here
resolves, fetches or compiles.

The arms are the increment's Tests field:

  * POSITIVE          the coherent fixture passes `check`, and the live tree's
                      leg census matches the table (the shape this test pins).
  * NEGATIVE TWIN     the 2026-09-17 tree (`3e87b95ba`): every manifest and the
                      root lock at the new revision, the crystal lock still at
                      the old one. Refused with the SPECIFIC reason, on the
                      lock's name. Closed upstream by `48ce23658`; ported here
                      as the PASS row with its twin (roadmap Section 2.4 rule 4).
  * MUTATION CONTROL  hand-edit ONE manifest leg. The census reports the split,
                      `check` refuses naming the leg, the driver REFUSES before
                      staging anything (only an explicit `--repair` rewrites
                      every leg), and the same fixture with the edit reverted
                      passes -- so the rule caused the refusal and does not
                      over-refuse.
  * HISTORICAL TWIN   the coherence test on the REAL `3e87b95ba` tree, read from
                      this repository's objects: refused naming the crystal
                      lock; the same test on `48ce23658` (the repair) passes.
  * trust-cg authority: a trust-cg manifest pinning another trust-ir is
                      refused; one pinning the coordinated rev passes; a
                      `[patch]` of the trust-ir URL is refused.
  * clean-kernel      a root lock with a second, Git-sourced clean-kernel row
                      (the dropped `[patch]`) is refused.
  * driver            `bump-trust-ir-pin.sh` on the fixture: a malformed sha
                      is a usage refusal, a trust-cg whose manifest pins
                      another trust-ir is refused before staging, `--dry-run`
                      stages every leg and touches nothing, and a split fixture
                      is REPAIR mode. All offline, against a local fake
                      trust-cg object repo.
  * ADVERSARIAL       review arms (2026-09-20). The census refuses every
                      spelling of the repository that is not the exact URL
                      (Cargo canonicalises `trust-ir` == `trust-ir.git`, so
                      such a leg resolves but was invisible to the rewrite --
                      a real hole, closed), a root `[patch]` of trust-ir.git,
                      a root lock carrying two trust-ir graphs, a floating
                      lock selector, and a renamed dependency key.
  * TRANSACTION       the driver WITHOUT --dry-run against a fake Targo: a
                      refresh that fails and one that leaves the crystal lock
                      behind each roll the tree back byte-identically
                      (uncommitted work included); a coherent refresh lands
                      every leg and both locks and is idempotent; --repair
                      moves the hand-edited leg to the TARGET, adopting nothing.
  * PHASE G           (2026-10-15) the move ends by re-deriving what it left
                      stale (scripts/rederive_chain.py, a stand-in here whose
                      derived file pins the crystal manifest and lock as R7
                      does): it runs after phase F, over the moved tree, with
                      --offline passed on; a re-derivation that fails rolls
                      back the legs AND the derived artifacts (one it created
                      is removed); a tree with coherent legs whose derived
                      artifacts are red BEFORE the move is refused before
                      anything is staged. The real chain has its own
                      self-test, scripts/test_rederive_chain.py.
  * SPLIT LEGS        (review, 2026-10-16) a split crystal leg reddens the
                      derived file by itself: --repair reports that red and
                      repairs the split; a lock left behind at the target is a
                      split too (refused, then refreshed by --repair); the tree
                      an incomplete rollback leaves is one the same bump moves
                      on from; a transaction directory a killed bump left is
                      named. Each arm fails on the lane's pre-review driver.
"""
from __future__ import annotations

import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import trust_ir_pin_legs as legs  # noqa: E402

OLD = "6a7fe3525a" + "0" * 30
NEW = "b094459bbe" + "1" * 30
CG_OLD = "919d4131" + "2" * 32
CG_NEW = "bbdf39be" + "3" * 32
TIR = legs.TRUST_IR_URL
TCG = legs.TRUST_CG_URL


def ir_source(rev: str) -> str:
    return f"git+{TIR}?rev={rev}#{rev}"


def cg_source(rev: str) -> str:
    return f"git+{TCG}?rev={rev}#{rev}"


def declaration(key: str, url: str, rev: str, extra: str = "") -> str:
    return f'{key} = {{ git = "{url}", rev = "{rev}"{extra} }}\n'


def package(name: str, version: str = "0.14.0", source: str | None = None) -> str:
    row = f'[[package]]\nname = "{name}"\nversion = "{version}"\n'
    if source is not None:
        row += f'source = "{source}"\n'
    return row + "\n"


def fixture(ir: str = NEW, cg: str = CG_NEW, *, crystal_lock: str | None = None,
            root_lock_ir: str | None = None) -> dict[str, str]:
    """Every tracked manifest and lock of a tree at (ir, cg), leg-for-leg."""
    crystal_lock = crystal_lock or ir
    root_lock_ir = root_lock_ir or ir
    files: dict[str, str] = {}
    files["Cargo.toml"] = (
        '[workspace]\nmembers = ["crates/*"]\n\n[workspace.dependencies]\n'
        + declaration("trust-ir-contract", TIR, ir)
        + declaration("trust-ir-semr", TIR, ir, ', package = "trust-ir", default-features = false, features = ["binary"]')
        + f'\n[patch."https://github.com/alabsystems/clean.git"]\n'
        'clean-kernel = { path = "crates/clean-kernel" }\n'
    )
    files["crates/clean-auto/Cargo.toml"] = (
        '[package]\nname = "clean-auto"\nversion = "0.9.0"\n\n[dev-dependencies]\n'
        f'# the trust-cg commit that co-owns {TIR} -- a comment, not a leg\n'
        + declaration("trust-cg-lower", TCG, cg)
        + declaration("trust-cg-ir", TCG, cg)
        + declaration("trust-cg-opt", TCG, cg)
        + declaration("trust-ir", TIR, ir, ', features = ["serde"]')
    )
    files["crates/clean-compiler/Cargo.toml"] = (
        '[package]\nname = "clean-compiler"\nversion = "0.9.0"\n\n[dependencies]\n'
        + declaration("trust-ir", TIR, ir, ', optional = true, features = ["binary"]')
        + declaration("trust-ir-build", TIR, ir, ", optional = true")
        + declaration("trust-ir-conformance", TIR, ir, ", optional = true, default-features = false")
    )
    files["crates/clean-reflect/Cargo.toml"] = (
        '[package]\nname = "clean-reflect"\nversion = "0.9.0"\n\n[dependencies]\n'
        + declaration("trust-ir", TIR, ir, ', default-features = false, features = ["serde"]')
    )
    files["crates/clean-verify/Cargo.toml"] = (
        '[package]\nname = "clean-verify"\nversion = "0.9.0"\n\n[dependencies]\n'
        + declaration("trust-ir", TIR, ir, ', default-features = false, features = ["parser", "fmt"]')
    )
    files["crates/clean-kernel/Cargo.toml"] = '[package]\nname = "clean-kernel"\nversion = "0.9.0"\n'
    files["scripts/crystal_a2_project/Cargo.toml"] = (
        '[workspace]\n\n[package]\nname = "a2mint-project"\nversion = "0.1.0"\npublish = false\n\n'
        '[dependencies]\n'
        + declaration("trust-ir", TIR, ir, ', default-features = false, features = ["binary", "fmt"]')
        + 'sha2 = { version = "0.10", default-features = false }\n'
    )
    files["Cargo.lock"] = (
        "version = 4\n\n"
        + package("clean-auto", "0.9.0") + package("clean-kernel", "0.9.0")
        + package("clean-mathverse", "0.9.0") + package("clean-olean", "0.9.0")
        + package("trust-ir", source=ir_source(root_lock_ir))
        + package("trust-ir-build", source=ir_source(root_lock_ir))
        + package("trust-ir-contract", source=ir_source(root_lock_ir))
        + package("trust-cg-ir", "0.6.0", cg_source(cg))
        + package("trust-cg-lower", "0.6.0", cg_source(cg))
        + package("trust-cg-opt", "0.6.0", cg_source(cg))
    )
    files["scripts/crystal_a2_project/Cargo.lock"] = (
        "version = 4\n\n" + package("a2mint-project", "0.1.0")
        + package("trust-ir", source=ir_source(crystal_lock))
        + package("trust-ir-contract", source=ir_source(crystal_lock))
    )
    return files


def manifests(files: dict[str, str]) -> dict[str, str]:
    return {k: v for k, v in files.items() if k.endswith("Cargo.toml")}


def locks(files: dict[str, str]) -> dict[str, str]:
    return {k: v for k, v in files.items() if k.endswith("Cargo.lock")}


def trust_cg_manifest(ir: str) -> str:
    return (
        '[workspace]\nmembers = ["crates/*"]\n\n[workspace.dependencies]\n'
        + declaration("trust-ir", TIR, ir, ', features = ["serde", "binary"]')
        + declaration("trust-ir-build", TIR, ir)
    )


class LegTable(unittest.TestCase):
    def test_live_tree_matches_the_leg_table(self) -> None:
        """The shape this test pins IS the shape of the tree (no `!!` row)."""
        live = legs.read_tracked(ROOT, "*Cargo.toml")
        ir = legs.census(live, "trust-ir")
        cg = legs.census(live, "trust-cg")
        self.assertEqual(
            {k: tuple(key for _, key, _ in v) for k, v in ir.items()}, legs.TRUST_IR_LEGS)
        self.assertEqual(
            {k: tuple(key for _, key, _ in v) for k, v in cg.items()}, legs.TRUST_CG_LEGS)
        self.assertEqual(len(legs.revisions(ir)), 9, "nine trust-ir declarations")
        self.assertEqual(len(legs.revisions(cg)), 3, "three trust-cg declarations")

    def test_live_tree_is_coherent(self) -> None:
        """POSITIVE on the real tree: what the hook leg asserts on every push."""
        live = legs.read_tracked(ROOT, "*Cargo.toml")
        locks = legs.dev_ir_aliases.production_locks(
            ROOT, live, legs.read_tracked(ROOT, "*Cargo.lock"))
        result = legs.check_pin_coherence(live, locks)
        self.assertEqual(set(result), {"trust-ir", "trust-cg"})

    def test_live_tree_restates_no_pin(self) -> None:
        """No tracked manifest comment quotes a trust-ir/trust-cg commit id."""
        self.assertEqual(legs.restated_pins(legs.read_tracked(ROOT, "*Cargo.toml")), [])

    def test_declared_dev_alias_does_not_hide_an_extra_git_declaration(self) -> None:
        files = manifests(fixture())
        files["Cargo.toml"] = files["Cargo.toml"].replace(
            '[workspace.dependencies]\n',
            '[workspace.dependencies]\n'
            + declaration("witness", TIR, NEW, ', package = "trust-ir"'))
        files["Cargo.toml"] += (
            '\n[workspace.metadata.clean]\ndev-only-ir-aliases = ["witness"]\n'
        )
        files["crates/clean-kernel/Cargo.toml"] += (
            '\n[dev-dependencies]\nwitness = { workspace = true }\n'
        )
        legs.census(files, "trust-ir")
        files["Cargo.toml"] += (
            '\n[patch."https://example.invalid/extra"]\n'
            + declaration("witness", TIR, NEW, ', package = "trust-ir"'))
        with self.assertRaisesRegex(legs.PinShapeError, "exactly one Git declaration"):
            legs.census(files, "trust-ir")

    def test_maintained_semr_alias_cannot_stay_on_another_revision(self) -> None:
        files = fixture()
        files["Cargo.toml"] += (
            '\n[workspace.metadata.clean]\ndev-only-ir-aliases = ["trust-ir-semr"]\n'
        )
        files["crates/clean-kernel/Cargo.toml"] += (
            '\n[dev-dependencies]\ntrust-ir-semr = { workspace = true }\n'
        )
        legs.check_pin_coherence(manifests(files), locks(files))
        files["Cargo.toml"] = files["Cargo.toml"].replace(
            declaration("trust-ir-semr", TIR, NEW, ', package = "trust-ir", default-features = false, features = ["binary"]'),
            declaration("trust-ir-semr", TIR, OLD, ', package = "trust-ir", default-features = false, features = ["binary"]'),
        )
        with self.assertRaisesRegex(legs.PinCoherenceError, "split across manifest legs"):
            legs.check_pin_coherence(manifests(files), locks(files))
        with tempfile.TemporaryDirectory() as tmp:
            stage = Path(tmp)
            legs.stage(manifests(files), {"trust-ir": NEW, "trust-cg": CG_NEW}, stage)
            self.assertIn(
                declaration("trust-ir-semr", TIR, NEW, ', package = "trust-ir", default-features = false, features = ["binary"]'),
                (stage / "Cargo.toml").read_text(),
            )

    def test_a_comment_restating_a_pin_is_refused(self) -> None:
        """The clean-auto note that went stale twice, a trailing comment, and
        the comments the rule must NOT catch."""
        files = manifests(fixture())
        files["crates/clean-auto/Cargo.toml"] += (
            f"# every TrustIR edge in this workspace sits at {NEW[:8]} with it.\n"
        )
        files["crates/clean-reflect/Cargo.toml"] += (
            declaration("trust-ir", TIR, NEW).rstrip("\n") + f"  # trust-ir {CG_NEW[:10]}\n"
        )
        found = legs.restated_pins(files)
        self.assertEqual(len(found), 2, found)
        self.assertTrue(found[0].startswith("crates/clean-auto/Cargo.toml:"), found)
        self.assertTrue(found[1].startswith("crates/clean-reflect/Cargo.toml:"), found)
        controls = manifests(fixture())
        controls["Cargo.toml"] += (
            "# the redirect was removed on 2026-08-12 (93550c617)\n"
            "\n"
            "# keep the TrustIR edge at the revision this TrustCG pin selects\n"
            "# trust-ir 0.14.0, published 20260923; deadbeef is a word\n"
        )
        self.assertEqual(legs.restated_pins(controls), [])

    def test_a_wrapped_or_capitalised_restatement_is_refused(self) -> None:
        """The two spellings a per-line, lowercase rule passed: the name and
        the id on adjacent comment lines, and the id in capitals."""
        for note in (
            f"# every TrustIR edge in this workspace sits at\n# {NEW[:8]} with it.\n",
            f"# trust-ir is pinned at {NEW[:8].upper()} today\n",
        ):
            files = manifests(fixture())
            files["crates/clean-auto/Cargo.toml"] += note
            found = legs.restated_pins(files)
            self.assertEqual(len(found), 1, (note, found))
            self.assertTrue(found[0].startswith("crates/clean-auto/Cargo.toml:"), found)

    def test_positive_fixture(self) -> None:
        files = fixture()
        self.assertEqual(legs.check_pin_coherence(manifests(files), locks(files)),
                         {"trust-ir": NEW, "trust-cg": CG_NEW})

    def test_negative_twin_crystal_lock_left_behind(self) -> None:
        """The 3e87b95ba tree: crystal lock at 6a7fe352 while every other leg moved."""
        files = fixture(crystal_lock=OLD)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        message = str(caught.exception)
        self.assertIn("scripts/crystal_a2_project/Cargo.lock resolves trust-ir " + OLD, message)
        self.assertIn(f"every manifest leg declares {NEW}", message)
        # Ratchet direction: the SAME fixture with the lock regenerated passes.
        legs.check_pin_coherence(manifests(files), locks(fixture()))

    def test_root_lock_left_behind_is_named(self) -> None:
        files = fixture(root_lock_ir=OLD)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("Cargo.lock resolves trust-ir " + OLD, str(caught.exception))

    def test_mutation_control_one_manifest_leg(self) -> None:
        """Hand-edit one leg: split reported, refusal names the leg, revert passes."""
        for relative, key in (("crates/clean-compiler/Cargo.toml", "trust-ir-build"),
                              ("scripts/crystal_a2_project/Cargo.toml", "trust-ir"),
                              ("Cargo.toml", "trust-ir-contract"),
                              ("Cargo.toml", "trust-ir-semr")):
            with self.subTest(leg=f"{relative}:{key}"):
                files = fixture()
                edited = files[relative].replace(
                    f'{key} = {{ git = "{TIR}", rev = "{NEW}"',
                    f'{key} = {{ git = "{TIR}", rev = "{OLD}"', 1)
                self.assertNotEqual(edited, files[relative])
                files[relative] = edited
                with self.assertRaises(legs.PinCoherenceError) as caught:
                    legs.manifest_revision(manifests(files), "trust-ir")
                self.assertIn("trust-ir pin is split across manifest legs", str(caught.exception))
                self.assertIn(f"{relative}:{key}={OLD[:12]}", str(caught.exception))
                with self.assertRaises(legs.PinCoherenceError):
                    legs.check_pin_coherence(manifests(files), locks(files))
        legs.check_pin_coherence(manifests(fixture()), locks(fixture()))

    def test_mutation_control_trust_cg_leg(self) -> None:
        files = fixture()
        files["crates/clean-auto/Cargo.toml"] = files["crates/clean-auto/Cargo.toml"].replace(
            declaration("trust-cg-opt", TCG, CG_NEW), declaration("trust-cg-opt", TCG, CG_OLD))
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("trust-cg pin is split across manifest legs", str(caught.exception))
        self.assertIn("crates/clean-auto/Cargo.toml:trust-cg-opt=" + CG_OLD[:12], str(caught.exception))

    def test_shape_change_is_a_refusal_not_a_miss(self) -> None:
        """A ninth declaration, a missing one, and a multi-line table are all `!!`."""
        files = fixture()
        files["crates/clean-lsp/Cargo.toml"] = '[dependencies]\n' + declaration("trust-ir", TIR, NEW)
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.census(manifests(files), "trust-ir")
        self.assertIn("!! crates/clean-lsp/Cargo.toml", str(caught.exception))
        self.assertIn("differ from the leg table", str(caught.exception))

        files = fixture()
        files["crates/clean-reflect/Cargo.toml"] = '[package]\nname = "clean-reflect"\n'
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.census(manifests(files), "trust-ir")
        self.assertIn("!! crates/clean-reflect/Cargo.toml", str(caught.exception))

        files = fixture()
        files["crates/clean-verify/Cargo.toml"] = (
            '[dependencies.trust-ir]\ngit = "' + TIR + '"\nrev = "' + NEW + '"\n')
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.census(manifests(files), "trust-ir")
        self.assertIn("outside an inline dependency declaration", str(caught.exception))

        files = fixture()
        del files["scripts/crystal_a2_project/Cargo.lock"]
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("scripts/crystal_a2_project/Cargo.lock: lock is not tracked", str(caught.exception))

    def test_second_clean_kernel_is_refused(self) -> None:
        """A dropped root [patch] pulls a Git-sourced clean-kernel beside the workspace one."""
        files = fixture()
        files["Cargo.lock"] += package(
            "clean-kernel", "0.9.0",
            "git+https://github.com/alabsystems/clean.git?rev=" + "5" * 40 + "#" + "5" * 40)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("Cargo.lock carries 2 clean-kernel row(s)", str(caught.exception))
        self.assertIn("root [patch]", str(caught.exception))

    def test_lock_source_shapes(self) -> None:
        files = fixture()
        files["Cargo.lock"] = files["Cargo.lock"].replace(ir_source(NEW), f"git+{TIR}?rev={NEW}#{OLD}", 1)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn(f"requests {NEW} but resolves {OLD}", str(caught.exception))
        files = fixture()
        files["Cargo.lock"] = files["Cargo.lock"].replace(f'source = "{ir_source(NEW)}"\n', "", 1)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("does not use the exact trust-ir Git source", str(caught.exception))

    def test_trust_cg_authority(self) -> None:
        legs.check_trust_cg_authority(trust_cg_manifest(NEW), "trust-cg", NEW)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_trust_cg_authority(trust_cg_manifest(OLD), "trust-cg", NEW)
        self.assertIn(f"pins trust-ir ['{OLD}'], not the coordinated {NEW}", str(caught.exception))
        # Two declarations disagreeing inside trust-cg itself is a refusal too.
        split = trust_cg_manifest(NEW).replace(declaration("trust-ir-build", TIR, NEW),
                                               declaration("trust-ir-build", TIR, OLD))
        with self.assertRaises(legs.PinCoherenceError):
            legs.check_trust_cg_authority(split, "trust-cg", NEW)
        patched = trust_cg_manifest(NEW) + f'\n[patch."{TIR}"]\ntrust-ir = {{ path = "../trust-ir/crates/trust-ir" }}\n'
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.check_trust_cg_authority(patched, "trust-cg", NEW)
        self.assertIn("[patch] redirects", str(caught.exception))
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.check_trust_cg_authority('[package]\nname = "x"\n', "not-trust-cg", NEW)
        self.assertIn("no trust-ir.git declaration found", str(caught.exception))
        floating = trust_cg_manifest(NEW).replace(f'rev = "{NEW}" }}', 'branch = "main" }', 1)
        with self.assertRaises(legs.PinShapeError):
            legs.check_trust_cg_authority(floating, "trust-cg", NEW)

    def test_stage_rewrites_every_leg_and_only_the_rev(self) -> None:
        files = fixture(OLD, CG_OLD)
        with tempfile.TemporaryDirectory(prefix="clean-pin-stage-") as temp:
            staged = legs.stage(manifests(files), {"trust-ir": NEW, "trust-cg": CG_NEW}, Path(temp))
            self.assertEqual(staged, sorted(set(legs.TRUST_IR_LEGS) | set(legs.TRUST_CG_LEGS)))
            after = dict(manifests(files))
            for relative in staged:
                after[relative] = (Path(temp) / relative).read_text()
            self.assertEqual(legs.manifest_revision(after, "trust-ir"), NEW)
            self.assertEqual(legs.manifest_revision(after, "trust-cg"), CG_NEW)
            expected = manifests(fixture(NEW, CG_NEW))
            self.assertEqual(after, expected, "only the rev fields moved")
            # Idempotent: staging at the target changes nothing.
            self.assertEqual(legs.stage(after, {"trust-ir": NEW, "trust-cg": CG_NEW}, Path(temp)), [])


class HistoricalTree(unittest.TestCase):
    """The coherence test against the REAL trees, read from this repository's objects.

    `3e87b95ba` (2026-09-17) moved every manifest leg and the root lock to
    trust-ir b094459b and left `scripts/crystal_a2_project/Cargo.lock` at
    6a7fe352 -- the split the roadmap's negative twin names. `48ce23658` is the
    upstream repair (roadmap Section 2.4 rule 4: closed upstream, ported as a
    PASS row with its twin). Both are ancestors of every tree this test runs
    on; a shallow or grafted clone that lacks them is a FAILURE, not a skip.
    """

    SPLIT = "3e87b95ba9d6e5b991b1b897d4278d492bd2ce95"
    REPAIRED = "48ce2365896c367aa2611ab584ffa8db4f15decb"
    CRYSTAL_OLD = "6a7fe3525a93467542a10dfd4bf336499fa121dc"
    MOVED_TO = "b094459bbe4decfa424e257e7bb9e288114f6990"

    def setUp(self) -> None:
        # These exact historical trees predate the SemR alias. Judge their
        # retained crystal-lock regression with their original eight-leg shape;
        # current-tree and transaction controls always require all nine legs.
        patch = mock.patch.dict(legs.TRUST_IR_LEGS, {"Cargo.toml": ("trust-ir-contract",)})
        patch.start()
        self.addCleanup(patch.stop)

    @staticmethod
    def tree_at(commit: str, pattern: str) -> dict[str, str]:
        listed = subprocess.run(
            ["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", commit],
            capture_output=True, text=True, check=True).stdout.split("\n")
        suffix = pattern.lstrip("*")
        out = {}
        for relative in sorted(path for path in listed if path.endswith(suffix)):
            out[relative] = subprocess.run(
                ["git", "-C", str(ROOT), "show", f"{commit}:{relative}"],
                capture_output=True, text=True, check=True).stdout
        return out

    def test_split_tree_3e87b95ba_is_refused_naming_the_crystal_lock(self) -> None:
        manifests = self.tree_at(self.SPLIT, "*Cargo.toml")
        locks = self.tree_at(self.SPLIT, "*Cargo.lock")
        self.assertEqual(legs.manifest_revision(manifests, "trust-ir"), self.MOVED_TO,
                         "every manifest leg had moved")
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests, locks)
        self.assertIn(
            "scripts/crystal_a2_project/Cargo.lock resolves trust-ir " + self.CRYSTAL_OLD,
            str(caught.exception))
        self.assertIn(f"every manifest leg declares {self.MOVED_TO}", str(caught.exception))

    def test_repaired_tree_48ce23658_passes(self) -> None:
        manifests = self.tree_at(self.REPAIRED, "*Cargo.toml")
        locks = self.tree_at(self.REPAIRED, "*Cargo.lock")
        result = legs.check_pin_coherence(manifests, locks)
        self.assertEqual(result["trust-ir"], self.MOVED_TO)


class Driver(unittest.TestCase):
    """The bash driver on a synthetic repository, fully offline."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.temp = Path(tempfile.mkdtemp(prefix="clean-pin-driver-"))
        cls.trust_cg = cls.temp / "trust-cg"
        cls.trust_cg.mkdir()
        cls.git(cls.trust_cg, "init", "-q", "-b", "main")
        cls.git(cls.trust_cg, "config", "user.email", "t@example.invalid")
        cls.git(cls.trust_cg, "config", "user.name", "t")
        cls.cg_commits = {}
        for label, ir in (("old", OLD), ("new", NEW)):
            (cls.trust_cg / "Cargo.toml").write_text(trust_cg_manifest(ir))
            cls.git(cls.trust_cg, "add", "Cargo.toml")
            cls.git(cls.trust_cg, "commit", "-q", "-m", label)
            cls.cg_commits[label] = cls.git(cls.trust_cg, "rev-parse", "HEAD").strip()

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.temp, ignore_errors=True)

    @staticmethod
    def git(cwd: Path, *args: str) -> str:
        return subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, text=True,
                              check=True).stdout

    def repo(self, files: dict[str, str]) -> Path:
        root = Path(tempfile.mkdtemp(prefix="clean-pin-repo-", dir=self.temp))
        for relative, text in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        (root / "scripts").mkdir(exist_ok=True)
        # Match the real repository's generated-Python-cache exclusion now
        # that the pin CLI imports its dependency-graph policy helper.
        (root / ".gitignore").write_text("__pycache__/\n")
        (root / "scripts/rederive_chain.py").write_text(FAKE_REDERIVE)
        (root / "data").mkdir(exist_ok=True)
        (root / "data/derived.json").write_text(derived_json(files))
        shutil.copy(SCRIPTS / "bump-trust-ir-pin.sh", root / "scripts")
        shutil.copy(SCRIPTS / "trust_ir_pin_legs.py", root / "scripts")
        shutil.copy(SCRIPTS / "dev_ir_aliases.py", root / "scripts")
        shutil.copy(SCRIPTS / "check_workspace_dependency_boundary.py", root / "scripts")
        # Both copied helpers import it (fe3d50943).
        shutil.copy(SCRIPTS / "resource_transport.py", root / "scripts")
        self.git(root, "init", "-q", "-b", "main")
        self.git(root, "config", "user.email", "t@example.invalid")
        self.git(root, "config", "user.name", "t")
        self.git(root, "add", "-A")
        self.git(root, "commit", "-q", "-m", "fixture")
        return root

    def run_driver(self, root: Path, *args: str) -> subprocess.CompletedProcess:
        env = dict(os.environ, CLEAN_TRUST_CG_REPO=str(self.trust_cg), FAKE_REDERIVE_MODE="ok")
        return subprocess.run(["bash", str(root / "scripts/bump-trust-ir-pin.sh"), *args],
                              cwd=root, env=env, capture_output=True, text=True, check=False)

    def test_malformed_sha_is_a_refusal(self) -> None:
        root = self.repo(fixture(OLD, self.cg_commits["old"]))
        result = self.run_driver(root, NEW[:12], self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("is not a full 40-hex lowercase commit sha", result.stderr)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_trust_cg_that_pins_another_trust_ir_is_refused_before_staging(self) -> None:
        root = self.repo(fixture(OLD, self.cg_commits["old"]))
        result = self.run_driver(root, NEW, self.cg_commits["old"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(f"pins trust-ir ['{OLD}'], not the coordinated {NEW}", result.stdout + result.stderr)
        self.assertIn("does not co-own trust-ir", result.stderr)
        self.assertNotIn("PHASE B", result.stdout)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_dry_run_stages_every_leg_and_touches_nothing(self) -> None:
        root = self.repo(fixture(OLD, self.cg_commits["old"]))
        result = self.run_driver(root, NEW, self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(f"moving trust-ir: {OLD} -> {NEW}", result.stdout)
        for relative in sorted(set(legs.TRUST_IR_LEGS) | set(legs.TRUST_CG_LEGS)):
            self.assertIn(f"--- a/{relative}", result.stdout)
        self.assertIn("DRY RUN -- nothing installed", result.stdout)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_hand_edited_leg_is_refused_by_driver_and_check(self) -> None:
        """MUTATION CONTROL, driver half: a split tree is REFUSED, naming the leg.

        Both refuse (the increment's Tests field): the driver before staging a
        byte, and the coherence gate. Only an explicit `--repair` turns the
        split into a rewrite of EVERY leg, and even then nothing is adopted from
        the hand-edited leg -- every leg moves to the requested target.
        """
        files = fixture(NEW, self.cg_commits["new"])
        files["crates/clean-reflect/Cargo.toml"] = files["crates/clean-reflect/Cargo.toml"].replace(NEW, OLD)
        root = self.repo(files)
        result = self.run_driver(root, NEW, self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("<> trust-ir " + OLD + "  crates/clean-reflect/Cargo.toml:trust-ir", result.stdout)
        self.assertIn("a pin is SPLIT across revisions", result.stderr)
        self.assertIn("A hand-edited leg is refused, never adopted", result.stderr)
        self.assertNotIn("PHASE B", result.stdout)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")
        # And the coherence gate on that tree refuses, naming the leg.
        check = subprocess.run([sys.executable, str(root / "scripts/trust_ir_pin_legs.py"), "check",
                                "--root", str(root)], capture_output=True, text=True, check=False)
        self.assertEqual(check.returncode, 3)
        self.assertIn("crates/clean-reflect/Cargo.toml:trust-ir=" + OLD[:12], check.stderr)
        # --repair: the split becomes a rewrite of every leg to the target.
        result = self.run_driver(root, NEW, self.cg_commits["new"], "--dry-run", "--offline", "--repair")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("REPAIR MODE (--repair): a pin is currently SPLIT", result.stdout)
        self.assertIn("--- a/crates/clean-reflect/Cargo.toml", result.stdout)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")
        # Control: the same fixture with the edit reverted is not refused.
        result = self.run_driver(self.repo(fixture(NEW, self.cg_commits["new"])),
                                 NEW, self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_shape_drift_refuses_before_repair(self) -> None:
        files = fixture(OLD, CG_OLD)
        files["crates/clean-lsp/Cargo.toml"] = "[dependencies]\n" + declaration("trust-ir", TIR, OLD)
        root = self.repo(files)
        result = self.run_driver(root, NEW, self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("!! crates/clean-lsp/Cargo.toml", result.stdout)
        self.assertIn("no longer matches its declared shape", result.stderr)

    def test_already_at_target_still_checks_the_locks(self) -> None:
        """No-op is DEFERRED: manifests at the target but a stale crystal lock is a refusal."""
        root = self.repo(fixture(NEW, self.cg_commits["new"]))
        result = self.run_driver(root, NEW, self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("nothing to do", result.stdout)
        self.assertNotIn("PHASE B", result.stdout)
        root = self.repo(fixture(NEW, self.cg_commits["new"], crystal_lock=OLD))
        result = self.run_driver(root, NEW, self.cg_commits["new"], "--dry-run", "--offline")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("scripts/crystal_a2_project/Cargo.lock resolves trust-ir " + OLD, result.stderr)
        self.assertIn("a lockfile does not", result.stderr)


class Adversarial(unittest.TestCase):
    """Review arms (2026-09-20): inputs the implementer did not write.

    Each is a claim the coherence test could have accepted, or a legitimate
    tree it could have refused, before the review. The first was a real hole:
    Cargo canonicalises a GitHub URL (it strips `.git`), so a ninth declaration
    spelled `https://github.com/alabsystems/trust-ir` IS a trust-ir
    dependency, yet the census keyed on the exact URL neither counted nor
    rewrote it. The lock check would have refused the tree only after a
    refresh, naming the lock rather than the leg.
    """

    def test_non_canonical_url_spelling_is_a_named_refusal(self) -> None:
        for spelling in ("https://github.com/alabsystems/trust-ir",
                         "https://github.com/alabsystems/trust-ir.git",
                         "ssh://git@github.com/alabsystems/trust-ir.git",
                         "https://github.com/alabsystems/trust-ir.git/"):
            with self.subTest(spelling=spelling):
                files = fixture()
                files["crates/clean-lsp/Cargo.toml"] = (
                    "[dependencies]\n" + declaration("trust-ir", spelling, OLD))
                with self.assertRaises(legs.PinShapeError) as caught:
                    legs.census(manifests(files), "trust-ir")
                message = str(caught.exception)
                self.assertIn("!! crates/clean-lsp/Cargo.toml:2: trust-ir declares trust-ir through", message)
                self.assertIn(f"not the exact {TIR}", message)
                # And the lock that spelling produces is refused on its own.
                files = fixture()
                files["Cargo.lock"] = files["Cargo.lock"].replace(
                    ir_source(NEW), f"git+{spelling}?rev={NEW}#{NEW}", 1)
                with self.assertRaises(legs.PinCoherenceError):
                    legs.check_pin_coherence(manifests(fixture()), locks(files))
        # A comment may spell the repository however it likes.
        files = fixture()
        files["crates/clean-lsp/Cargo.toml"] = (
            "[dependencies]\n# pinned like alabsystems/trust-ir, see git@github.com:alabsystems/trust-ir.git\n")
        self.assertNotIn("crates/clean-lsp/Cargo.toml", legs.census(manifests(files), "trust-ir"))
        # `trust-ir-contract` is a KEY that starts with the needle, not a mention.
        legs.census(manifests(fixture()), "trust-ir")

    def test_root_patch_of_trust_ir_is_refused_by_census_and_lock(self) -> None:
        """A `[patch."<trust-ir.git>"]` redirect makes the rev decorative."""
        files = fixture()
        files["Cargo.toml"] += (
            f'\n[patch."{TIR}"]\ntrust-ir = {{ path = "../trust-ir/crates/trust-ir" }}\n')
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.census(manifests(files), "trust-ir")
        self.assertIn("!! Cargo.toml:", str(caught.exception))
        self.assertIn("outside an inline dependency declaration", str(caught.exception))
        # The lock such a patch produces (a sourceless trust-ir row) is refused too.
        files = fixture()
        files["Cargo.lock"] = files["Cargo.lock"].replace(f'source = "{ir_source(NEW)}"\n', "", 1)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(fixture()), locks(files))
        self.assertIn("does not use the exact trust-ir Git source: None", str(caught.exception))

    def test_root_lock_carrying_two_trust_ir_graphs_is_refused(self) -> None:
        """What a trust-cg that co-owns ANOTHER trust-ir leaves in the root lock."""
        files = fixture()
        files["Cargo.lock"] += package("trust-ir-build", source=ir_source(OLD))
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("Cargo.lock resolves multiple trust-ir Git revisions", str(caught.exception))
        self.assertIn(OLD, str(caught.exception))
        self.assertIn(NEW, str(caught.exception))

    def test_floating_lock_selector_is_refused(self) -> None:
        files = fixture()
        files["Cargo.lock"] = files["Cargo.lock"].replace(
            ir_source(NEW), f"git+{TIR}?branch=main#{NEW}", 1)
        with self.assertRaises(legs.PinCoherenceError) as caught:
            legs.check_pin_coherence(manifests(files), locks(files))
        self.assertIn("does not use the exact trust-ir Git source", str(caught.exception))

    def test_key_reorder_and_rename_are_shape_refusals(self) -> None:
        """A renamed dependency key is a `!!` row, never a silently-adopted leg."""
        files = fixture()
        files["crates/clean-reflect/Cargo.toml"] = files["crates/clean-reflect/Cargo.toml"].replace(
            "trust-ir = {", 'tir = { package = "trust-ir",', 1)
        with self.assertRaises(legs.PinShapeError) as caught:
            legs.census(manifests(files), "trust-ir")
        self.assertIn("['tir'] differ from the leg table ['trust-ir']", str(caught.exception))


class CheckDiagnosis(unittest.TestCase):
    """Only a caught coherence error supplies the driver's split diagnosis."""

    def test_check_status_distinguishes_split_from_other_refusals(self) -> None:
        files = fixture()
        for error, expected in (
            (legs.PinCoherenceError("fixture split"), 3),
            (legs.PinShapeError("fixture shape"), 2),
            (legs.dev_ir_aliases.DevAliasError("fixture resolver"), 2),
            (subprocess.CalledProcessError(1, "git"), 2),
            (OSError("fixture I/O"), 2),
        ):
            with self.subTest(error=type(error).__name__), \
                    mock.patch.object(legs, "read_tracked", side_effect=error), \
                    redirect_stderr(io.StringIO()) as output:
                self.assertEqual(legs.cmd_check(Path("/unused")), expected)
                self.assertIn("REFUSED:", output.getvalue())
        with mock.patch.object(legs, "read_tracked", side_effect=lambda root, pattern:
                               locks(files) if pattern == "*Cargo.lock" else manifests(files)), \
                mock.patch.object(legs.dev_ir_aliases, "production_locks", return_value=locks(files)):
            self.assertEqual(legs.cmd_check(Path("/unused")), 0)


# A stand-in for scripts/rederive_chain.py (phase A.5's `--check`, phase C's `--outputs`,
# phase G's re-derivation), modelling the one node that reads a leg the way the real one
# does: data/derived.json pins the sha256 of the crystal manifest and lock (R7's derived
# inputs of check_lint_coverage), `--check` is RED when either moved since, and the
# re-derivation refuses a crystal manifest and lock that disagree, as the replay's
# `targo metadata --locked` does in every arm's baseline. A fresh tree is re-derived to
# nothing. FAKE_REDERIVE_MODE: ok; fail (a stale tree's writes, then exit 1 -- a replay
# that refused after a partial mint); eat-backup (the same, deleting one backup file
# first); red-before (`--check` exits 1 whatever the legs, a red the move did not cause).
# Every call is appended to $FAKE_REDERIVE_LOG.
FAKE_REDERIVE = r'''#!/usr/bin/env python3
import hashlib, json, os, re, sys
from pathlib import Path
root = Path(__file__).resolve().parent.parent
mode = os.environ.get("FAKE_REDERIVE_MODE", "ok")
args = sys.argv[1:]
if os.environ.get("FAKE_REDERIVE_LOG"):
    with open(os.environ["FAKE_REDERIVE_LOG"], "a") as fh:
        fh.write(" ".join(["rederive", *args]) + "\n")
if "--outputs" in args:
    print("data/derived.json\ndata/minted.json")
    sys.exit(0)
MANIFEST, LOCK = "scripts/crystal_a2_project/Cargo.toml", "scripts/crystal_a2_project/Cargo.lock"
def live():
    return {rel: hashlib.sha256((root / rel).read_bytes()).hexdigest() for rel in (MANIFEST, LOCK)}
pinned = json.loads((root / "data/derived.json").read_text())["inputs"]
moved = [rel for rel, sha in live().items() if pinned.get(rel) != sha]
if "--check" in args:
    if mode == "red-before":
        print("  [RED] verdict-set: stale before the move")
        sys.exit(1)
    if moved:
        print("  [RED] gate-registry: R7 FRESH: check_lint_coverage was demonstrated against a "
              f"derived input set that has moved since (changed: {', '.join(moved)})")
        sys.exit(1)
    print("  [ok] gate-registry\nREDERIVE_CHECK=ok")
    sys.exit(0)
manifest_rev = re.search(r'trust-ir\.git", rev = "([0-9a-f]{40})"', (root / MANIFEST).read_text()).group(1)
lock_rev = re.search(r"trust-ir\.git\?rev=([0-9a-f]{40})", (root / LOCK).read_text()).group(1)
if manifest_rev != lock_rev:
    print(f"error: cannot update the lock file {LOCK} because --locked was passed", file=sys.stderr)
    print("REDERIVE=fail every baseline of check_lint_coverage's replay is red", file=sys.stderr)
    sys.exit(1)
if not moved:
    print("  [fresh] gate-registry\nREDERIVE=ok re-derived=none")
    sys.exit(0)
(root / "data/derived.json").write_text(json.dumps({"inputs": live()}) + "\n")
(root / "data/minted.json").write_text("minted\n")
if mode == "eat-backup":
    # What macOS's $TMPDIR cleaner did to old-dated files: one backup vanishes
    # while the transaction is open. It must be found in the checkout's git directory.
    eaten = list(root.glob(".git/bump-trust-ir-pin.*/backup/scripts/crystal_a2_project/Cargo.lock"))
    for path in eaten:
        path.unlink()
    print(f"ate {len(eaten)} backup(s)", file=sys.stderr)
    sys.exit(1)
if mode == "fail":
    print("REDERIVE=fail check_lint_coverage did not replay", file=sys.stderr)
    sys.exit(1)
print("REDERIVE=ok re-derived=gate-registry")
'''


def derived_json(files: dict[str, str]) -> str:
    """data/derived.json pinning `files`' crystal manifest and lock, as the stand-in mints it."""
    inputs = {rel: hashlib.sha256(files[rel].encode()).hexdigest()
              for rel in ("scripts/crystal_a2_project/Cargo.toml",
                          "scripts/crystal_a2_project/Cargo.lock")}
    return json.dumps({"inputs": inputs}) + "\n"


FAKE_TARGO = r'''#!/usr/bin/env bash
# A stand-in for `targo metadata [--locked] --format-version 1 --manifest-path P`.
# FAKE_TARGO_MODE: ok (rewrite the lock beside P from every Cargo.toml under P's
# directory), fail (exit 101, write nothing), leave-crystal (refresh the root
# lock only -- the 3e87b95ba omission, replayed by the resolver).
set -u
mode="${FAKE_TARGO_MODE:-ok}"
manifest=""; locked=0
while [ $# -gt 0 ]; do
    case "$1" in
        --manifest-path) manifest="$2"; shift ;;
        --locked) locked=1 ;;
    esac
    shift
done
[ -n "$manifest" ] || { echo "fake targo: no --manifest-path" >&2; exit 2; }
printf '%s\n' "metadata locked=$locked mode=$mode $manifest" >>"${FAKE_TARGO_LOG:-/dev/null}"
if [ "$locked" -eq 1 ]; then echo '{}'; exit 0; fi
case "$mode" in
    fail) echo "fake targo: resolver refused" >&2; exit 101 ;;
    leave-crystal) case "$manifest" in */crystal_a2_project/*) echo '{}'; exit 0 ;; esac ;;
esac
python3 - "$manifest" <<'PY'
import re, sys
from pathlib import Path
manifest = Path(sys.argv[1]); root = manifest.parent; lock = root / "Cargo.lock"
text = lock.read_text()
for url in ("https://github.com/alabsystems/trust-ir.git", "https://github.com/alabsystems/trust-cg.git"):
    revs = set()
    for m in root.rglob("Cargo.toml"):
        if {".git", "target"} & set(m.relative_to(root).parts):
            continue  # cargo reads neither a git directory nor a build directory
        revs |= set(re.findall(r'git = "' + re.escape(url) + r'", rev = "([0-9a-f]{40})"', m.read_text()))
    if len(revs) == 1:
        rev = next(iter(revs))
        text = re.sub(r"git\+" + re.escape(url) + r"\?rev=[0-9a-f]{40}#[0-9a-f]{40}", f"git+{url}?rev={rev}#{rev}", text)
lock.write_text(text)
PY
echo '{}'
'''


class Transaction(unittest.TestCase):
    """The driver's REAL install/refresh/verify/rollback path (never `--dry-run`).

    Every driver arm above stops at phase B. These run phases C-F against a
    fake Targo whose `metadata` is the only thing it models: a refresh that
    fails, one that leaves the crystal lock behind (the resolver replaying the
    3e87b95ba omission), and one that refreshes both. The tree must come back
    byte-identical -- uncommitted work included -- on either failure, and
    the success path must end where `check` and the hook leg would pass.
    """

    @classmethod
    def setUpClass(cls) -> None:
        cls.temp = Path(tempfile.mkdtemp(prefix="clean-pin-txn-"))
        cls.trust_cg = cls.temp / "trust-cg"
        cls.trust_cg.mkdir()
        Driver.git(cls.trust_cg, "init", "-q", "-b", "main")
        Driver.git(cls.trust_cg, "config", "user.email", "t@example.invalid")
        Driver.git(cls.trust_cg, "config", "user.name", "t")
        (cls.trust_cg / "Cargo.toml").write_text(trust_cg_manifest(NEW))
        Driver.git(cls.trust_cg, "add", "Cargo.toml")
        Driver.git(cls.trust_cg, "commit", "-q", "-m", "new")
        cls.cg_new = Driver.git(cls.trust_cg, "rev-parse", "HEAD").strip()
        cls.fake_targo = cls.temp / "targo"
        cls.fake_targo.write_text(FAKE_TARGO)
        cls.fake_targo.chmod(0o755)

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.temp, ignore_errors=True)

    git = staticmethod(Driver.git)

    def repo(self, files: dict[str, str]) -> Path:
        root = Driver.repo(self, files)  # type: ignore[arg-type]
        boundary = root / "scripts/check_workspace_dependency_boundary.py"
        boundary.write_text("import os, sys\nprint('BOUNDARY_FIXTURE_CHECKED')\nsys.exit(int(os.environ.get('FAKE_BOUNDARY_EXIT', '0')))\n")
        self.git(root, "add", str(boundary.relative_to(root)))
        self.git(root, "commit", "-q", "-m", "explicit boundary test double")
        return root

    def snapshot(self, root: Path) -> dict[str, bytes]:
        out = subprocess.run(["git", "-C", str(root), "ls-files", "-z"], capture_output=True, check=True).stdout
        return {name: (root / name).read_bytes() for name in out.decode().split("\0") if name}

    def run_txn(self, root: Path, mode: str, *args: str,
                rederive: str = "ok", boundary_exit: int = 0) -> subprocess.CompletedProcess:
        env = dict(os.environ, CLEAN_TRUST_CG_REPO=str(self.trust_cg), FAKE_TARGO_MODE=mode,
                   FAKE_TARGO_LOG=str(root.with_suffix(".targo.log")),
                   FAKE_REDERIVE_MODE=rederive, FAKE_BOUNDARY_EXIT=str(boundary_exit),
                   FAKE_REDERIVE_LOG=str(root.with_suffix(".rederive.log")))
        return subprocess.run(
            ["bash", str(root / "scripts/bump-trust-ir-pin.sh"), NEW, self.cg_new,
             "--offline", *([] if "--source-only" in args else ["--no-boundary-check"]), "--targo", str(self.fake_targo), *args],
            cwd=root, env=env, capture_output=True, text=True, check=False)

    def test_failed_refresh_rolls_back_exactly_as_found(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        # Uncommitted work in a controlled leg must survive the rollback verbatim.
        verify = root / "crates/clean-verify/Cargo.toml"
        verify.write_text(verify.read_text() + "# an uncommitted note\n")
        before = self.snapshot(root)
        result = self.run_txn(root, "fail")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("PHASE D", result.stdout)
        self.assertIn("root lock refresh failed", result.stderr)
        self.assertIn("ROLLED BACK -- working tree unchanged.", result.stderr)
        self.assertEqual(self.snapshot(root), before)
        self.assertEqual(Driver.git(root, "status", "--porcelain"), " M crates/clean-verify/Cargo.toml\n")

    def test_refresh_that_leaves_the_crystal_lock_behind_is_refused_and_rolled_back(self) -> None:
        """The 3e87b95ba omission replayed by the resolver itself: phase F refuses."""
        root = self.repo(fixture(OLD, CG_OLD))
        before = self.snapshot(root)
        result = self.run_txn(root, "leave-crystal")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("PHASE F", result.stdout)
        self.assertIn("scripts/crystal_a2_project/Cargo.lock resolves trust-ir " + OLD, result.stderr)
        self.assertIn("post-bump pin coherence FAILED", result.stderr)
        self.assertIn("ROLLED BACK -- working tree unchanged.", result.stderr)
        self.assertEqual(self.snapshot(root), before)
        self.assertEqual(Driver.git(root, "status", "--porcelain"), "")

    def test_coherent_refresh_lands_every_leg_and_both_locks(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("both lockfiles accepted under --locked", result.stdout)
        self.assertIn(f"DONE -- trust-ir pinned at {NEW} and trust-cg at {self.cg_new}", result.stdout)
        self.assertNotIn("ROLLED BACK", result.stderr)
        log = root.with_suffix(".targo.log").read_text()
        self.assertEqual(log.count("locked=0"), 2, log)
        self.assertEqual(log.count("locked=1"), 2, log)
        self.assertIn("crystal_a2_project/Cargo.toml", log)
        after = self.snapshot(root)
        expected = fixture(NEW, self.cg_new)
        for relative in sorted(set(legs.TRUST_IR_LEGS) | set(legs.TRUST_CG_LEGS) | set(legs.TRUST_IR_LOCKS)):
            self.assertEqual(after[relative].decode(), expected[relative], relative)
        self.assertEqual(
            legs.check_pin_coherence(legs.read_tracked(root, "*Cargo.toml"), legs.read_tracked(root, "*Cargo.lock")),
            {"trust-ir": NEW, "trust-cg": self.cg_new})
        # Idempotent: a second run is the deferred no-op, and it re-runs `--locked` on both.
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("nothing to do", result.stdout)
        self.assertEqual(after, self.snapshot(root))

    def test_source_transaction_updates_both_locks_without_minting_diagnostic_evidence(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", "--source-only", rederive="red-before")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("both lockfiles accepted under --locked", result.stdout)
        self.assertIn("SOURCE TRANSACTION COMPLETE", result.stdout)
        self.assertIn("Full diagnostic and its derived artifacts: NOT JUDGED", result.stdout)
        self.assertNotIn("PHASE G", result.stdout)
        self.assertEqual(root.with_suffix(".rederive.log").read_text().splitlines(),
                         ["rederive --outputs"])
        after = self.snapshot(root)
        expected = fixture(NEW, self.cg_new)
        controlled = set(legs.TRUST_IR_LEGS) | set(legs.TRUST_CG_LEGS) | set(legs.TRUST_IR_LOCKS)
        for relative in controlled:
            self.assertEqual(after[relative].decode(), expected[relative], relative)
        for relative in before.keys() - controlled:
            self.assertEqual(after[relative], before[relative], relative)
        log = root.with_suffix(".targo.log").read_text()
        self.assertEqual(log.count("locked=0"), 2, log)
        self.assertEqual(log.count("locked=1"), 2, log)

    def test_source_transaction_refuses_boundary_override_before_mutation(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", "--source-only", "--no-boundary-check")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("requires the dependency-boundary check", result.stderr)
        self.assertNotIn("PHASE A", result.stdout)
        self.assertEqual(self.snapshot(root), before)

    def test_source_transaction_boundary_failure_rolls_back_and_checks_noop(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", "--source-only", boundary_exit=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("BOUNDARY_FIXTURE_CHECKED", result.stdout)
        self.assertIn("ROLLED BACK", result.stderr)
        self.assertEqual(self.snapshot(root), before)
        result = self.run_txn(root, "ok", "--source-only")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        after = self.snapshot(root)
        result = self.run_txn(root, "ok", "--source-only", boundary_exit=1)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("both lockfiles accepted under --locked", result.stdout)
        self.assertIn("BOUNDARY_FIXTURE_CHECKED", result.stdout)
        self.assertEqual(self.snapshot(root), after)

    def test_source_transaction_preserves_refresh_and_split_lock_refusals(self) -> None:
        for mode in ("fail", "leave-crystal"):
            with self.subTest(mode=mode):
                root = self.repo(fixture(OLD, CG_OLD))
                before = self.snapshot(root)
                result = self.run_txn(root, mode, "--source-only")
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("ROLLED BACK -- working tree unchanged.", result.stderr)
                self.assertNotIn("SOURCE TRANSACTION COMPLETE", result.stdout)
                self.assertEqual(self.snapshot(root), before)

    def test_source_transaction_still_refuses_a_split_without_repair(self) -> None:
        files = fixture(OLD, CG_OLD)
        files["crates/clean-reflect/Cargo.toml"] = files["crates/clean-reflect/Cargo.toml"].replace(OLD, "9" * 40)
        root = self.repo(files)
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", "--source-only")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertNotIn("PHASE D", result.stdout)
        self.assertEqual(self.snapshot(root), before)

    def test_repair_rewrites_the_hand_edited_leg_to_the_target(self) -> None:
        """--repair adopts nothing from the edit: the split leg lands at the TARGET."""
        files = fixture(OLD, CG_OLD)
        files["crates/clean-reflect/Cargo.toml"] = files["crates/clean-reflect/Cargo.toml"].replace(OLD, "9" * 40)
        root = self.repo(files)
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertNotIn("PHASE C", result.stdout)
        result = self.run_txn(root, "ok", "--repair")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        after = self.snapshot(root)
        self.assertEqual(after["crates/clean-reflect/Cargo.toml"].decode(),
                         fixture(NEW, self.cg_new)["crates/clean-reflect/Cargo.toml"])
        self.assertNotIn(b"9" * 40, after["crates/clean-reflect/Cargo.toml"])

    def test_phase_g_rederives_over_the_moved_tree_after_phase_f(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        out = result.stdout
        self.assertLess(out.index("PHASE F"), out.index("PHASE G"))
        self.assertLess(out.index("PHASE G"), out.index("REDERIVE=ok"))
        self.assertLess(out.index("REDERIVE=ok"), out.index("DONE --"))
        # --outputs and the read-only --check in phase A, then one re-derivation,
        # --offline passed on.
        self.assertEqual(root.with_suffix(".rederive.log").read_text().splitlines(),
                         ["rederive --outputs", "rederive --check", "rederive --offline"])
        self.assertEqual((root / "data/derived.json").read_text(),
                         derived_json(fixture(NEW, self.cg_new)))
        self.assertEqual(Driver.git(root, "status", "--porcelain", "--", "data"),
                         " M data/derived.json\n?? data/minted.json\n")

    def test_failed_rederivation_rolls_back_the_legs_and_the_derived_artifacts(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", rederive="fail")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("PHASE G", result.stdout)
        self.assertIn("REDERIVE=fail", result.stderr)
        self.assertIn("the bump is not done", result.stderr)
        self.assertIn("ROLLED BACK -- working tree unchanged.", result.stderr)
        self.assertEqual(self.snapshot(root), before)
        self.assertFalse((root / "data/minted.json").exists())
        self.assertEqual(Driver.git(root, "status", "--porcelain"), "")

    def test_a_vanished_backup_is_a_failed_rollback_never_an_unchanged_claim(self) -> None:
        """Phase G holds the backup for an hour. It lives in the checkout's git directory,
        and a rollback restores from phase C's list, so a backup file gone missing is
        reported."""
        root = self.repo(fixture(OLD, CG_OLD))
        result = self.run_txn(root, "ok", rederive="eat-backup")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("ate 1 backup(s)", result.stderr)
        self.assertIn("ROLLBACK FAILED to restore scripts/crystal_a2_project/Cargo.lock",
                      result.stderr)
        self.assertIn("ROLLBACK INCOMPLETE", result.stderr)
        self.assertNotIn("working tree unchanged", result.stderr)
        # Everything else was restored, and the scratch directory is gone.
        self.assertEqual(Driver.git(root, "status", "--porcelain"),
                         " M scripts/crystal_a2_project/Cargo.lock\n")
        self.assertEqual(list(root.glob(".git/bump-trust-ir-pin.*")), [])
        # The tree it leaves -- a crystal lock at the target under manifests that are not,
        # which reddens the registry's pin of it -- is one the same bump moves on from:
        # its red is the lock's, reported and re-derived by phase G, never refused.
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("[RED] gate-registry", result.stdout)
        self.assertIn("reported, NOT refused", result.stderr)
        self.assertIn("REDERIVE=ok re-derived=gate-registry", result.stdout)
        self.assertEqual(
            legs.check_pin_coherence(legs.read_tracked(root, "*Cargo.toml"), legs.read_tracked(root, "*Cargo.lock")),
            {"trust-ir": NEW, "trust-cg": self.cg_new})
        self.assertEqual((root / "data/derived.json").read_text(),
                         derived_json(fixture(NEW, self.cg_new)))

    def split_at_target(self, leg: str) -> Path:
        """A tree committed at the target with its derived artifacts fresh, then `leg`
        hand-moved back to OLD in the working tree -- the shape of the 2026-10-16 review's
        reproducer (the crystal manifest) or of an incomplete rollback (the crystal lock)."""
        root = self.repo(fixture(NEW, self.cg_new))
        path = root / leg
        path.write_text(path.read_text().replace(NEW, OLD))
        check = subprocess.run([sys.executable, str(root / "scripts/rederive_chain.py"), "--check"],
                               cwd=root, capture_output=True, text=True, check=False)
        self.assertEqual(check.returncode, 1, check.stdout)
        self.assertIn("[RED] gate-registry: R7 FRESH", check.stdout)
        self.assertIn(f"changed: {leg}", check.stdout)
        return root

    def test_repair_moves_a_split_crystal_leg_its_derived_artifacts_read(self) -> None:
        """--repair exists to fix a split. A split crystal leg reddens the registry's pin of
        it by itself, so phase A reports that red and the repair proceeds: refused, the
        split could only be restored by hand (the stand-in's replay, like the real one's
        `targo metadata --locked`, refuses a crystal manifest its lock disagrees with)."""
        root = self.split_at_target("scripts/crystal_a2_project/Cargo.toml")
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("a pin is SPLIT across revisions", result.stderr)
        self.assertNotIn("PHASE B", result.stdout)
        result = self.run_txn(root, "ok", "--repair")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("REPAIR MODE (--repair): a pin is currently SPLIT", result.stdout)
        self.assertIn("[RED] gate-registry", result.stdout)
        self.assertIn("reported, NOT refused", result.stderr)
        self.assertLess(result.stdout.index("PHASE F"), result.stdout.index("PHASE G"))
        self.assertIn("REDERIVE=ok", result.stdout)
        # The repaired legs are the committed ones, so nothing was left to re-derive.
        self.assertEqual(Driver.git(root, "status", "--porcelain"), "")

    def test_repair_refreshes_a_lock_left_behind_at_the_target(self) -> None:
        """Manifests at the target and a lock that is not: a split the census cannot see.
        Refused like one, naming --repair; --repair refreshes both locks."""
        root = self.split_at_target("scripts/crystal_a2_project/Cargo.lock")
        result = self.run_txn(root, "ok")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("a lockfile does not", result.stderr)
        self.assertIn("re-run with --repair", result.stderr)
        self.assertNotIn("PHASE B", result.stdout)
        self.assertEqual(Driver.git(root, "status", "--porcelain"),
                         " M scripts/crystal_a2_project/Cargo.lock\n")
        result = self.run_txn(root, "ok", "--repair")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("REPAIR MODE (--repair): the manifests read the target and a lockfile does not",
                      result.stdout)
        self.assertIn("reported, NOT refused", result.stderr)
        self.assertIn("REDERIVE=ok", result.stdout)
        self.assertEqual(Driver.git(root, "status", "--porcelain"), "")

    def test_a_surviving_transaction_directory_is_named(self) -> None:
        """A bump killed outright leaves its backup in the git directory; the next run says so."""
        root = self.repo(fixture(OLD, CG_OLD))
        left = root / ".git/bump-trust-ir-pin.KILLED/backup/scripts/crystal_a2_project"
        left.mkdir(parents=True)
        (left / "Cargo.lock").write_text("the lock a killed bump found\n")
        result = self.run_txn(root, "ok", "--dry-run")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stderr.count("a bump's transaction directory survives at"), 1,
                         result.stderr)
        self.assertIn(str(root / ".git/bump-trust-ir-pin.KILLED"), result.stderr)
        self.assertTrue(left.is_dir())

    def test_derived_artifacts_red_before_the_move_are_refused_before_staging(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", rederive="red-before")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("[RED] verdict-set", result.stdout)
        self.assertIn("already red before the bump", result.stderr)
        self.assertNotIn("PHASE B", result.stdout)
        self.assertEqual(root.with_suffix(".rederive.log").read_text().splitlines(),
                         ["rederive --outputs", "rederive --check"])
        self.assertEqual(self.snapshot(root), before)
        self.assertEqual(Driver.git(root, "status", "--porcelain"), "")

    def alias_repo(self, ir: str, cg: str) -> tuple[Path, dict]:
        """A real declared dev alias, resolved only by a fixture Targo's graph."""
        witness = "c" * 40
        files = fixture(ir, cg)
        files["Cargo.toml"] = files["Cargo.toml"].replace(
            "[workspace.dependencies]\n",
            '[workspace.metadata.clean]\ndev-only-ir-aliases = ["witness"]\n\n'
            "[workspace.dependencies]\n"
            + declaration("witness", TIR, witness, ', package = "trust-ir"'))
        files["crates/clean-kernel/Cargo.toml"] += (
            '\n[dev-dependencies]\nwitness = { workspace = true }\n')
        files["Cargo.lock"] += package("trust-ir", source=ir_source(witness))
        files["scripts/rust_frontend.sh"] = '''#!/usr/bin/env bash
set -eu
[ "$1" = --targo ]
[ -n "${TARGO:-}" ] || { echo "fixture: TARGO was not exported" >&2; exit 127; }
printf '%s' "$TARGO"
'''
        files["scripts/alias-targo"] = '''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
with Path(os.environ["FAKE_ALIAS_TARGO_LOG"]).open("a") as log:
    log.write(json.dumps(sys.argv[1:]) + "\\n")
if os.environ["FAKE_ALIAS_MODE"] == "fail":
    print("fixture metadata resolver refused", file=sys.stderr)
    sys.exit(61)
print(os.environ["FAKE_ALIAS_METADATA"])
'''
        root = self.repo(files)
        (root / "scripts/alias-targo").chmod(0o755)
        self.git(root, "add", "scripts/alias-targo")
        self.git(root, "commit", "-q", "-m", "fixture executable")
        members, packages, nodes = [], [], []
        for relative, text in manifests(files).items():
            if not relative.startswith("crates/"):
                continue
            name = legs.tomllib.loads(text)["package"]["name"]
            members.append(name)
            packages.append({"id": name, "name": name, "version": "0.9.0",
                             "source": None, "manifest_path": str(root / relative)})
            edge = ({"name": "witness", "pkg": "dev", "dep_kinds": [{"kind": "dev"}]}
                    if name == "clean-kernel" else
                    {"name": "trust_ir", "pkg": "prod", "dep_kinds": [{"kind": None}]})
            nodes.append({"id": name, "deps": [edge]})
        for name, rev in (("prod", ir), ("dev", witness)):
            packages.append({"id": name, "name": "trust-ir", "version": "0.14.0",
                             "source": ir_source(rev)})
            nodes.append({"id": name, "deps": []})
        return root, {"workspace_root": str(root), "workspace_members": members,
                      "packages": packages, "resolve": {"nodes": nodes}}

    def alias_preflight(self, root: Path, metadata: dict, selection: str, mode: str,
                        *args: str, rederive: str = "red-before") -> subprocess.CompletedProcess:
        targo = str(root / "scripts/alias-targo")
        env = dict(os.environ, CLEAN_TRUST_CG_REPO=str(self.trust_cg),
                   FAKE_ALIAS_MODE=mode, FAKE_ALIAS_METADATA=json.dumps(metadata),
                   FAKE_ALIAS_TARGO_LOG=str(root.with_suffix(".alias-targo.log")),
                   FAKE_REDERIVE_MODE=rederive,
                   FAKE_REDERIVE_LOG=str(root.with_suffix(".rederive.log")))
        env.pop("TARGO", None)
        env.pop("CLEAN_TARGO", None)
        options = ["--targo", targo] if selection == "argument" else []
        if selection == "environment":
            env["CLEAN_TARGO"] = targo
        return subprocess.run(
            ["bash", str(root / "scripts/bump-trust-ir-pin.sh"), NEW, self.cg_new,
             "--offline", *options, *args], cwd=root, env=env,
            capture_output=True, text=True, check=False)

    def test_resolver_failure_never_excuses_red_baseline_as_a_split(self) -> None:
        for selection in ("argument", "environment"):
            for dry in (True, False):
                for at_target in (True, False):
                    for repair in (True, False):
                        with self.subTest(selection=selection, dry=dry,
                                          at_target=at_target, repair=repair):
                            root, metadata = self.alias_repo(
                                NEW if at_target else OLD, self.cg_new if at_target else CG_OLD)
                            before = self.snapshot(root)
                            options = (["--dry-run"] if dry else []) + (["--repair"] if repair else [])
                            result = self.alias_preflight(root, metadata, selection, "fail", *options)
                            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                            self.assertIn("cannot establish pre-bump pin coherence", result.stderr)
                            self.assertIn("fixture metadata resolver refused", result.stderr)
                            self.assertNotIn("the legs disagree", result.stderr)
                            self.assertNotIn("PHASE B", result.stdout)
                            self.assertEqual(self.snapshot(root), before)
                            self.assertEqual(self.git(root, "status", "--porcelain"), "")
                            calls = root.with_suffix(".alias-targo.log").read_text().splitlines()
                            self.assertEqual([json.loads(call) for call in calls],
                                             [["metadata", "--locked", "--all-features", "--format-version", "1"]])
                            self.assertEqual(root.with_suffix(".rederive.log").read_text().splitlines(),
                                             ["rederive --outputs"])

    def test_selected_frontend_checks_alias_coherence_and_red_baseline_in_dry_and_full_runs(self) -> None:
        for selection in ("argument", "environment"):
            for dry in (True, False):
                with self.subTest(selection=selection, dry=dry):
                    root, metadata = self.alias_repo(OLD, CG_OLD)
                    before = self.snapshot(root)
                    result = self.alias_preflight(root, metadata, selection, "ok",
                                                  *(["--dry-run"] if dry else []))
                    self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                    self.assertIn("[RED] verdict-set", result.stdout)
                    self.assertIn("already red before the bump", result.stderr)
                    self.assertNotIn("PHASE B", result.stdout)
                    self.assertEqual(self.snapshot(root), before)
                    self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_selected_frontend_accepts_coherent_alias_preflight_with_fresh_baseline(self) -> None:
        for selection in ("argument", "environment"):
            for at_target in (True, False):
                for dry in ((True, False) if at_target else (True,)):
                    with self.subTest(selection=selection, at_target=at_target, dry=dry):
                        root, metadata = self.alias_repo(
                            NEW if at_target else OLD, self.cg_new if at_target else CG_OLD)
                        before = self.snapshot(root)
                        result = self.alias_preflight(root, metadata, selection, "ok",
                                                      *(["--dry-run"] if dry else []), rederive="ok")
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertIn("nothing to do" if at_target else "DRY RUN -- nothing installed", result.stdout)
                        self.assertEqual(self.snapshot(root), before)
                        self.assertEqual(self.git(root, "status", "--porcelain"), "")

    def test_alias_checked_split_crystal_repairs_remain_available(self) -> None:
        for selection in ("argument", "environment"):
            for leg in ("scripts/crystal_a2_project/Cargo.toml", "scripts/crystal_a2_project/Cargo.lock"):
                with self.subTest(selection=selection, leg=leg):
                    root, metadata = self.alias_repo(NEW, self.cg_new)
                    path = root / leg
                    path.write_text(path.read_text().replace(NEW, OLD))
                    before = self.snapshot(root)
                    status = self.git(root, "status", "--porcelain")
                    result = self.alias_preflight(root, metadata, selection, "ok",
                                                  "--dry-run", "--repair", rederive="ok")
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn("REPAIR MODE (--repair)", result.stdout)
                    self.assertIn("[RED] gate-registry", result.stdout)
                    self.assertIn("reported, NOT refused", result.stderr)
                    self.assertIn("DRY RUN -- nothing installed", result.stdout)
                    self.assertEqual(self.snapshot(root), before)
                    self.assertEqual(self.git(root, "status", "--porcelain"), status)

    def test_unexpected_check_failure_is_not_a_split(self) -> None:
        root = self.repo(fixture(OLD, CG_OLD))
        script = root / "scripts/trust_ir_pin_legs.py"
        script.write_text(script.read_text().replace(
            'def cmd_check(root: Path) -> int:\n',
            'def cmd_check(root: Path) -> int:\n    raise RuntimeError("fixture unexpected failure")\n'))
        self.git(root, "add", "scripts/trust_ir_pin_legs.py")
        self.git(root, "commit", "-q", "-m", "fixture check crash")
        before = self.snapshot(root)
        result = self.run_txn(root, "ok", "--dry-run", rederive="red-before")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("fixture unexpected failure", result.stderr)
        self.assertIn("cannot establish pre-bump pin coherence", result.stderr)
        self.assertNotIn("the legs disagree", result.stderr)
        self.assertNotIn("PHASE B", result.stdout)
        self.assertEqual(self.snapshot(root), before)
        self.assertEqual(self.git(root, "status", "--porcelain"), "")


if __name__ == "__main__":
    unittest.main()
