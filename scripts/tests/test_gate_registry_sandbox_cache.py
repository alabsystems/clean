#!/usr/bin/env python3
"""Real filesystem regressions for sandbox cache aliases and copy containment.

These tests exercise sandbox assembly, not any gate's mathematical verdict.
Unsafe-copy controls mock cp so the before-fix run cannot recurse into itself.
"""

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "check_gate_registry.py"
SPEC = importlib.util.spec_from_file_location("gate_registry_cache_tested", SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


class SandboxCacheTests(unittest.TestCase):
    def setUp(self):
        self.maxDiff = None
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.root = self.base / "source"
        self.root.mkdir()
        self.refusal_number = 0
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers = []\n')
        (self.root / "src").mkdir()
        (self.root / "src/source.txt").write_text("tracked source\n")
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.track("Cargo.toml", "src/source.txt")

    def track(self, *names):
        subprocess.run(["git", "add", "--", *names], cwd=self.root, check=True)

    def cache_alias(self):
        cache = self.root / "target.noindex"
        cache.mkdir()
        (cache / "artifact").write_text("private generated artifact\n")
        (self.root / "target").symlink_to("target.noindex", target_is_directory=True)
        return cache

    def assert_copy_refused(self, source, destination):
        with mock.patch.object(GATE.subprocess, "run") as run:
            run.return_value = subprocess.CompletedProcess([], 0, "", "")
            with self.assertRaisesRegex(GATE.Red, "itself|descendant"):
                GATE._clone_tree(source, destination)
            run.assert_not_called()

    def assert_alias_refused(self, mutated=()):
        self.refusal_number += 1
        with mock.patch.object(GATE, "_clone_tree") as clone, \
                mock.patch.object(GATE, "_claim_demo_target") as claim:
            with self.assertRaisesRegex(GATE.Red, "cache alias"):
                GATE._build_sandbox(
                    self.root, self.base / f"refused-{self.refusal_number}", False, set(mutated)
                )
            clone.assert_not_called()
            claim.assert_not_called()

    def test_copy_same_directory_refused_before_cp(self):
        self.assert_copy_refused(self.root / "src", self.root / "src")

    def test_copy_into_descendant_refused_before_cp(self):
        self.assert_copy_refused(self.root / "src", self.root / "src/new/copy")

    def test_copy_resolved_destination_parent_alias_refused_before_cp(self):
        alias = self.base / "alias"
        alias.symlink_to(self.root / "src", target_is_directory=True)
        self.assert_copy_refused(self.root / "src", alias / "new/copy")

    def test_copy_resolved_source_alias_refused_before_cp(self):
        alias = self.base / "alias"
        alias.symlink_to(self.root / "src", target_is_directory=True)
        self.assert_copy_refused(alias, self.root / "src/new")

    def test_existing_destination_child_alias_refused_before_cp(self):
        destination = self.base / "destination"
        destination.mkdir()
        (destination / "src").symlink_to(self.root / "src", target_is_directory=True)
        self.assert_copy_refused(self.root / "src", destination)

    def test_existing_parent_destination_refused_before_cp(self):
        self.assert_copy_refused(self.root / "src", self.root)

    def test_fallback_revalidates_effective_destination_before_second_cp(self):
        source = self.root / "src"
        destination = self.base / "partial-copy"

        def failed_copy(*args, **kwargs):
            if not destination.exists():
                destination.mkdir()
                (destination / source.name).symlink_to(source, target_is_directory=True)
            return subprocess.CompletedProcess([], 1, "", "partial first copy")

        with mock.patch.object(GATE.subprocess, "run", side_effect=failed_copy) as run:
            with self.assertRaisesRegex(GATE.Red, "itself|descendant"):
                GATE._clone_tree(source, destination)
            self.assertEqual(run.call_count, 1, "unsafe fallback cp must never run")

    def test_sibling_directory_and_file_copies_still_work(self):
        destination = self.base / "copy"
        GATE._clone_tree(self.root / "src", destination)
        self.assertEqual((destination / "source.txt").read_text(), "tracked source\n")
        GATE._clone_tree(self.root / "src/source.txt", self.base / "copied.txt")
        self.assertEqual((self.base / "copied.txt").read_text(), "tracked source\n")

    def test_backing_cache_alias_is_omitted_and_private_caches_isolated(self):
        cache = self.cache_alias()
        private_caches = []
        for build in (False, True):
            with self.subTest(build=build):
                sandbox = self.base / ("build" if build else "clone")
                GATE._build_sandbox(self.root, sandbox, build, set())
                self.assertTrue((sandbox / "target").is_symlink())
                self.assertFalse((sandbox / "target.noindex").exists())
                self.assertFalse((sandbox / "target.noindex").is_symlink())
                private = GATE._demo_target_dir(self.root, sandbox.name)
                private_caches.append(private.resolve())
                self.assertEqual((sandbox / "target").resolve(), private.resolve())
                self.assertNotEqual(private.resolve(), cache)
                self.assertTrue(private.resolve().is_relative_to(cache))
                self.assertFalse((sandbox / "target/artifact").exists())
                environment = GATE._sandbox_env(sandbox)
                self.assertEqual(environment["CARGO_TARGET_DIR"], str(private))
                self.assertEqual(environment["CARGO_BUILD_BUILD_DIR"], str(private))
                (sandbox / "target/plant").write_text("sandbox unit\n")
                self.assertFalse((cache / "plant").exists())
                self.assertFalse((sandbox / "src").is_symlink())
                self.assertIn(sandbox / "src/source.txt", list(sandbox.rglob("*.txt")))
                (sandbox / "src/source.txt").write_text("sandbox only\n")
                self.assertEqual((self.root / "src/source.txt").read_text(), "tracked source\n")
        self.assertEqual(len(set(private_caches)), 2)
        self.assertEqual((cache / "artifact").read_text(), "private generated artifact\n")

    def test_sandbox_inside_cache_never_copies_its_backing_directory(self):
        cache = self.cache_alias()
        original = GATE._clone_tree
        copied = []

        def checked_copy(source, destination):
            self.assertNotEqual(source.resolve(), cache, "cache would copy into itself")
            copied.append(source)
            original(source, destination)

        sandbox = cache / "evidence/sandbox"
        with mock.patch.object(GATE, "_clone_tree", side_effect=checked_copy):
            GATE._build_sandbox(self.root, sandbox, True, set())
        self.assertTrue(copied)
        self.assertFalse((sandbox / "target.noindex").exists())
        self.assertFalse((sandbox / "target.noindex").is_symlink())
        self.assertEqual((sandbox / "target").resolve(),
                         GATE._demo_target_dir(self.root, sandbox.name).resolve())
        self.assertNotEqual((sandbox / "target").resolve(), cache)

    def test_noindex_directory_is_build_output_unless_git_tracks_it(self):
        # An untracked `*.noindex` directory is the Spotlight-excluded build
        # layout atpkg lays out (`target-quality.noindex`, 119 GiB on this box
        # when measured) and never reaches a sandbox; one git TRACKS is source
        # and is copied whole, whatever its name.
        self.cache_alias()
        extra = self.root / "source.noindex"
        extra.mkdir()
        (extra / "file.txt").write_text("untracked output\n")
        kept = self.root / "kept.noindex"
        kept.mkdir()
        (kept / "file.txt").write_text("tracked source\n")
        self.track("kept.noindex/file.txt")
        (self.root / "other-alias").symlink_to(kept, target_is_directory=True)
        sandbox = self.base / "sandbox"
        GATE._build_sandbox(self.root, sandbox, False, set())
        self.assertFalse((sandbox / "source.noindex").exists())
        self.assertFalse((sandbox / "source.noindex").is_symlink())
        self.assertFalse((sandbox / "kept.noindex").is_symlink())
        self.assertEqual((sandbox / "kept.noindex/file.txt").read_text(), "tracked source\n")
        self.assertTrue((sandbox / "other-alias").is_symlink())
        self.assertEqual((sandbox / "other-alias").readlink(), kept)

    def test_noindex_without_matching_target_alias_is_still_build_output(self):
        source = self.root / "target.noindex"
        source.mkdir()
        (source / "file.txt").write_text("not a cache alias\n")
        sandbox = self.base / "sandbox"
        GATE._build_sandbox(self.root, sandbox, False, set())
        self.assertFalse((sandbox / "target.noindex").exists())
        self.assertFalse((sandbox / "target.noindex").is_symlink())

    def test_target_pointing_at_ordinary_source_keeps_source_walkable(self):
        (self.root / "target").symlink_to("src", target_is_directory=True)
        sandbox = self.base / "sandbox"
        GATE._build_sandbox(self.root, sandbox, False, set())
        self.assertFalse((sandbox / "src").is_symlink())
        self.assertIn(sandbox / "src/source.txt", list(sandbox.rglob("*.txt")))

    def test_tracked_source_under_backing_cache_refuses_before_copy(self):
        cache = self.cache_alias()
        (cache / "proof.rs").write_text("tracked proof\n")
        self.track("target.noindex/proof.rs")
        self.assert_alias_refused()

    def test_tracked_alias_into_backing_cache_refuses_before_copy(self):
        cache = self.cache_alias()
        (self.root / "tracked-link").symlink_to(cache / "artifact")
        self.track("tracked-link")
        self.assert_alias_refused()

    def test_workspace_members_under_cache_refuse_before_copy(self):
        cache = self.cache_alias()
        member = cache / "member"
        member.mkdir()
        (member / "Cargo.toml").write_text('[package]\nname="fixture"\nversion="0.1.0"\n')
        (self.root / "member-alias").symlink_to(member, target_is_directory=True)
        for name in ("target.noindex", "target.noindex/member", "member-alias", "target.noindex/*"):
            with self.subTest(member=name):
                (self.root / "Cargo.toml").write_text(f'[workspace]\nmembers = ["{name}"]\n')
                self.assert_alias_refused()

    def test_declared_mutations_in_cache_refuse_before_copy(self):
        cache = self.cache_alias()
        (self.root / "mutation-alias").symlink_to(cache, target_is_directory=True)
        for name in ("target.noindex/artifact", "target/artifact", "mutation-alias/artifact"):
            with self.subTest(mutation=name):
                self.assert_alias_refused({name})

    def test_git_inventory_failure_refuses_before_copy(self):
        self.cache_alias()
        with mock.patch.object(GATE.subprocess, "run") as run:
            run.return_value = subprocess.CompletedProcess([], 1, "", "unavailable inventory")
            self.assert_alias_refused()

    def test_existing_member_and_mutation_layout_semantics_are_preserved(self):
        self.cache_alias()
        member = self.root / "crates/member"
        member.mkdir(parents=True)
        (member / "Cargo.toml").write_text('[package]\nname="member"\nversion="0.1.0"\n')
        (member / "source.txt").write_text("member source\n")
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers = ["crates/member"]\n')
        for build, mutated in ((False, set()), (True, set()), (True, {"crates/member/source.txt"})):
            with self.subTest(build=build, mutated=mutated):
                sandbox = self.base / f"layout-{build}-{len(mutated)}"
                GATE._build_sandbox(self.root, sandbox, build, mutated)
                self.assertEqual((sandbox / "crates/member").is_symlink(), build and not mutated)
                self.assertEqual((sandbox / "crates/member/source.txt").read_text(), "member source\n")

    def test_declared_cargo_target_sources_in_cache_refuse_before_copy(self):
        cache = self.cache_alias()
        (cache / "payload.rs").write_text("pub fn source() {}\n")
        prefix = '[workspace]\nmembers=[]\n[package]\nname="fixture"\nversion="0.1.0"\n'
        targets = [
            '[lib]\npath="target.noindex/payload.rs"\n',
            *[f'[[{kind}]]\nname="fixture"\npath="target.noindex/payload.rs"\n'
              for kind in ("bin", "example", "test", "bench")],
        ]
        for target in targets:
            with self.subTest(target=target):
                (self.root / "Cargo.toml").write_text(prefix + target)
                self.assert_alias_refused()
        (self.root / "Cargo.toml").write_text(prefix + 'build="target.noindex/payload.rs"\n')
        self.assert_alias_refused()

    def test_default_build_source_alias_into_cache_refuses_before_copy(self):
        cache = self.cache_alias()
        (cache / "build.rs").write_text("fn main() {}\n")
        (self.root / "build.rs").symlink_to(cache / "build.rs")
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers=[]\n[package]\nname="fixture"\nversion="0.1.0"\n')
        self.assert_alias_refused()

    def test_local_cargo_path_dependencies_into_cache_refuse_before_copy(self):
        cache = self.cache_alias()
        dependency = cache / "dependency"
        dependency.mkdir()
        (dependency / "Cargo.toml").write_text('[package]\nname="dependency"\nversion="0.1.0"\n')
        (self.root / "dependency-alias").symlink_to(dependency, target_is_directory=True)
        prefix = '[workspace]\nmembers=[]\n[package]\nname="fixture"\nversion="0.1.0"\n'
        tables = ("dependencies", "dev-dependencies", "build-dependencies",
                  "workspace.dependencies", 'target.\'cfg(unix)\'.dependencies')
        for table in tables:
            with self.subTest(table=table):
                (self.root / "Cargo.toml").write_text(prefix + f'[{table}]\ndependency={{path="dependency-alias"}}\n')
                self.assert_alias_refused()

    def test_indirect_member_dependency_into_cache_refuses_before_copy(self):
        cache = self.cache_alias()
        for name in ("member", "middle"):
            (self.root / name).mkdir()
        (cache / "dependency").mkdir()
        (cache / "dependency/Cargo.toml").write_text('[package]\nname="dependency"\nversion="0.1.0"\n')
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers=["member"]\n')
        (self.root / "member/Cargo.toml").write_text('[package]\nname="member"\nversion="0.1.0"\n[dependencies]\nmiddle={path="../middle"}\n')
        (self.root / "middle/Cargo.toml").write_text('[package]\nname="middle"\nversion="0.1.0"\n[dependencies]\ndependency={path="../target.noindex/dependency"}\n')
        self.assert_alias_refused()

    def test_ordinary_path_dependency_cycle_terminates_without_hiding_source(self):
        self.cache_alias()
        for name, other in (("first", "second"), ("second", "first")):
            member = self.root / name
            member.mkdir()
            (member / "Cargo.toml").write_text(f'[package]\nname="{name}"\nversion="0.1.0"\n[dependencies]\n{other}={{path="../{other}"}}\n')
            (member / "source.txt").write_text(name)
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers=["first"]\n')
        sandbox = self.base / "sandbox"
        GATE._build_sandbox(self.root, sandbox, False, set())
        for name in ("first", "second"):
            self.assertFalse((sandbox / name).is_symlink())
            self.assertEqual((sandbox / name / "source.txt").read_text(), name)

    def test_reachable_missing_or_malformed_manifest_refuses_before_copy(self):
        self.cache_alias()
        member = self.root / "member"
        member.mkdir()
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers=["member"]\n')
        self.assert_alias_refused()
        (member / "Cargo.toml").write_text("[not valid toml\n")
        self.assert_alias_refused()

    def test_cargo_patch_and_replace_paths_into_cache_refuse_before_copy(self):
        cache = self.cache_alias()
        dependency = cache / "dependency"
        dependency.mkdir()
        (dependency / "Cargo.toml").write_text('[package]\nname="dependency"\nversion="0.1.0"\n')
        for table, name in (('patch.crates-io', 'dependency'),
                            ('patch."https://example.invalid/source"', 'dependency'),
                            ('replace', '"dependency:0.1.0"')):
            with self.subTest(table=table):
                (self.root / "Cargo.toml").write_text(f'[workspace]\nmembers=[]\n[{table}]\n{name}={{path="target.noindex/dependency"}}\n')
                self.assert_alias_refused()

    def test_inferred_target_file_aliases_into_cache_refuse_before_copy(self):
        cache = self.cache_alias()
        (cache / "payload.rs").write_text("pub fn source() {}\n")
        (self.root / "Cargo.toml").write_text('[workspace]\nmembers=[]\n[package]\nname="fixture"\nversion="0.1.0"\n')
        for name in ("src/lib.rs", "src/main.rs", "src/bin/extra.rs",
                     "examples/extra.rs", "tests/extra.rs", "benches/extra.rs",
                     "src/bin/extra/main.rs", "examples/named/main.rs",
                     "tests/named/main.rs", "benches/named/main.rs"):
            with self.subTest(source=name):
                source = self.root / name
                source.parent.mkdir(parents=True, exist_ok=True)
                source.symlink_to(cache / "payload.rs")
                try:
                    self.assert_alias_refused()
                finally:
                    source.unlink()


    # -- build output and nested checkouts never reach a sandbox --------------
    #
    # The checker below is deliberately INDEPENDENT of the module's exclusion
    # list: it spells the rule out again by hand, so a regression in the shared
    # predicate cannot make the copier and its check agree on a wrong answer.

    def plant_build_outputs(self):
        """Every shape of build output and nested checkout measured on this box."""
        self.cache_alias()
        for rel in ("target-quality.noindex", "target-self-verify/release",
                    "scripts/tool/target/debug", "lean/.lake/build/lib"):
            (self.root / rel).mkdir(parents=True)
            (self.root / rel / "artifact").write_text("build output\n")
        (self.root / "target-quality").symlink_to("target-quality.noindex",
                                                   target_is_directory=True)
        # Nested checkouts: a lane's worktree (a `.git` FILE), a Lean package
        # clone, and an EARLIER sandbox kept under a replay directory.
        lane = self.root / ".claude/worktrees/lane"
        lane.mkdir(parents=True)
        (lane / ".git").write_text("gitdir: /elsewhere/.git/worktrees/lane\n")
        (lane / "lib.rs").write_text("a lane's copy of the source\n")
        package = self.root / "lean/.lake/packages/dep"
        (package / ".git").mkdir(parents=True)
        (package / "Dep.lean").write_text("a package clone\n")
        earlier = self.root / "scratch/replay/sandboxes/0123456789ab/tree-build"
        (earlier / ".git").mkdir(parents=True)
        (earlier / "README.md").write_text("a kept sandbox\n")
        (earlier / "target").symlink_to(GATE._demo_target_dir(self.root, "tree-build"),
                                        target_is_directory=True)
        # Source that merely LOOKS like build output is still copied.
        (self.root / "bakeoff/target-sets").mkdir(parents=True)
        (self.root / "bakeoff/target-sets/set.tsv").write_text("tracked\n")
        (self.root / "scripts/target_census.sh").write_text("tracked\n")
        (self.root / "lean/lakefile.lean").write_text("tracked\n")
        self.track("bakeoff/target-sets/set.tsv", "scripts/target_census.sh",
                   "lean/lakefile.lean")

    def build_output_in(self, sandbox):
        """Every build dir or nested checkout `sandbox` holds, by an independent walk."""
        allowed = {"target", "bakeoff/target-sets"}
        found = []
        for directory, names, files in os.walk(sandbox):
            here = Path(directory).relative_to(sandbox)
            if here.parts and here.parts[0] == ".git":
                names[:] = []
                continue
            for name in names + files:
                entry = Path(directory) / name
                rel = (here / name).as_posix()
                if not entry.is_dir() or rel in allowed:
                    continue
                if (name.startswith("target") or name.endswith(".noindex")
                        or rel.endswith(".lake/build")):
                    found.append(f"build dir {rel}")
                elif not entry.is_symlink() and os.path.lexists(entry / ".git"):
                    found.append(f"nested checkout {rel}")
        return sorted(found)

    def test_sandbox_never_holds_a_build_dir_or_a_nested_checkout(self):
        self.plant_build_outputs()
        for build in (False, True):
            with self.subTest(build=build):
                sandbox = self.base / ("tree-build" if build else "tree")
                GATE._build_sandbox(self.root, sandbox, build, set())
                self.assertEqual(self.build_output_in(sandbox), [])
                for rel in ("bakeoff/target-sets/set.tsv", "scripts/target_census.sh",
                            "lean/lakefile.lean", "src/source.txt"):
                    self.assertTrue((sandbox / rel).is_file(), f"{rel} was not copied")
                self.assertEqual((sandbox / "target").resolve(),
                                 GATE._demo_target_dir(self.root, sandbox.name).resolve())

    def test_sandbox_inside_the_tree_never_copies_itself_or_a_sibling(self):
        self.cache_alias()
        base = self.root / "scratch/demo/0123456789ab"
        first = base / "tree"
        second = base / "tree-build"
        GATE._build_sandbox(self.root, first, False, set())
        GATE._build_sandbox(self.root, second, True, set())
        for sandbox in (first, second):
            with self.subTest(sandbox=sandbox.name):
                self.assertEqual(self.build_output_in(sandbox), [])
                # The directories around the destination are walked, so they
                # exist -- empty; neither sandbox is inside either sandbox.
                self.assertEqual(list((sandbox / base.relative_to(self.root)).iterdir()), [])
                self.assertTrue((sandbox / "src/source.txt").is_file())

    def test_existing_destination_is_refused_never_merged(self):
        # `cp -R src dst` into an EXISTING dst nests the copy one level down
        # (dst/src/src), so a sandbox a failed cleanup left behind would grow
        # a second copy inside the first.
        dest = self.base / "stale"
        (dest / "src").mkdir(parents=True)
        (dest / "src/old.txt").write_text("stale\n")
        with self.assertRaisesRegex(GATE.Red, "already exists"):
            GATE._build_sandbox(self.root, dest, False, set())
        self.assertFalse((dest / "src/src").exists())

    def test_declared_mutation_inside_build_output_refuses_before_copy(self):
        (self.root / "scripts/tool/target").mkdir(parents=True)
        (self.root / "scripts/tool/target/generated.rs").write_text("generated\n")
        with mock.patch.object(GATE, "_clone_tree") as clone:
            with self.assertRaisesRegex(GATE.Red, "excluded"):
                GATE._build_sandbox(self.root, self.base / "refused", False,
                                    {"scripts/tool/target/generated.rs"})
            clone.assert_not_called()

    def test_a_copier_that_admits_build_output_is_refused_by_the_audit(self):
        # The runtime audit, through the production path: with the exclusion
        # step disabled the copy takes the build dirs, and `_build_sandbox`
        # must refuse the result rather than hand it to an arm.
        self.plant_build_outputs()
        with mock.patch.object(GATE, "_sandbox_exclusions", return_value={}):
            with self.assertRaisesRegex(GATE.Red, "target-quality.noindex"):
                GATE._build_sandbox(self.root, self.base / "leaky", False, set())

    def test_audit_names_a_build_dir_and_a_nested_sandbox(self):
        sandbox = self.base / "sandbox"
        GATE._build_sandbox(self.root, sandbox, False, set())
        self.assertEqual(GATE._sandbox_audit(self.root, sandbox), [])
        (sandbox / "src/target/debug").mkdir(parents=True)
        (sandbox / "evidence/sandboxes/tree/.git").mkdir(parents=True)
        leaks = GATE._sandbox_audit(self.root, sandbox)
        self.assertTrue(any("src/target" in leak for leak in leaks), leaks)
        self.assertTrue(any("evidence/sandboxes/tree" in leak for leak in leaks), leaks)

    def test_a_sandbox_that_survives_removal_is_reported(self):
        sandbox = self.base / "sandbox"
        GATE._build_sandbox(self.root, sandbox, False, set())
        with mock.patch.object(GATE.shutil, "rmtree"):
            self.assertIn(str(sandbox), GATE._remove_sandbox(sandbox) or "")
        self.assertIsNone(GATE._remove_sandbox(sandbox))
        self.assertFalse(sandbox.exists())


if __name__ == "__main__":
    unittest.main()
