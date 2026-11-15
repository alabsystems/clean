# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Source-only transaction controls; fake commands never run Git or a resolver.

Fixtures model the full audited AY inventories. They do not establish actual
dependency resolution, compilation, upstream API compatibility, or a cohort.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
OLD = "0123456789abcdef0123456789abcdef01234567"
NEW = "89abcdef0123456789abcdef0123456789abcdef"
TY = "fedcba9876543210fedcba9876543210fedcba98"
AY_URL = "https://github.com/alabsystems/ay.git"
TY_URL = "https://github.com/alabsystems/ty.git"
MANIFEST_NAMES = (
    "ay", "ay-dpll", "ay-core", "ay-lean-bridge", "ay-proof", "ay-frontend", "ay-translate",
)
ROOT_NAMES = (
    "ay", "ay-allsat", "ay-arrays", "ay-bv", "ay-chc", "ay-core", "ay-count",
    "ay-diff-logic", "ay-dispatch", "ay-dpll", "ay-drat-check", "ay-dt", "ay-euf",
    "ay-fp", "ay-frontend", "ay-intsat", "ay-jit", "ay-lean-bridge", "ay-lia",
    "ay-lra", "ay-map", "ay-milp", "ay-model-check", "ay-multiset", "ay-nia",
    "ay-nonlinear-common", "ay-nra", "ay-pb-core", "ay-prefetch", "ay-proof",
    "ay-proof-common", "ay-sat", "ay-sat-congruence-core", "ay-seq", "ay-set",
    "ay-strings", "ay-sys", "ay-translate",
)
LOCKS = (
    "Cargo.lock", "cli-runner/Cargo.lock", "bench-runner/Cargo.lock",
    "realtelem-harness/Cargo.lock", "telemetry-harness/Cargo.lock",
)
OWNED = ("Cargo.toml", *LOCKS)


def source(revision: str) -> str:
    return f"git+{AY_URL}?rev={revision}#{revision}"


def fixture(revision: str = OLD, *, cdclt=False, version="0.27.0") -> dict[str, bytes]:
    manifest = '[workspace]\nmembers = []\n[workspace.dependencies]\n'
    for name in MANIFEST_NAMES:
        manifest += (f'{name} = {{ package = "{name}", version = "{version}", '
                     f'git = "{AY_URL}", rev = "{revision}", default-features = false }}\n')
    manifest += (f'tla-core = {{ git = "{TY_URL}", rev = "{TY}" }}\n'
                 'unrelated = { version = "1.0.0", features = ["keep"] }\n')
    files = {"Cargo.toml": manifest.encode()}
    for relative in LOCKS:
        names = ROOT_NAMES if relative == "Cargo.lock" else tuple(
            name for name in ROOT_NAMES if name != "ay-lean-bridge")
        if cdclt:
            names = (*names, "ay-cdclt")
        lock = '# immutable fixture metadata\nversion = 4\n\n'
        for name in names:
            lock += (f'[[package]]\nname = "{name}"\nversion = "{version}"\n'
                     f'source = "{source(revision)}"\n')
            if cdclt and name in ("ay-dpll", "ay-cdclt"):
                dependency = "ay-cdclt" if name == "ay-dpll" else "ay-core"
                lock += f'dependencies = ["{dependency}"]\n'
            lock += '\n'
        if relative in ("Cargo.lock", "cli-runner/Cargo.lock"):
            lock += (f'[[package]]\nname = "tla-core"\nversion = "0.99.0"\n'
                     f'source = "git+{TY_URL}?rev={TY}#{TY}"\n\n')
        # Source-qualified AY references may move, but the containing non-AY
        # package's name/version/source/checksum and other references may not.
        lock += ('[[package]]\nname = "unrelated"\nversion = "1.0.0"\n'
                 'source = "registry+https://github.com/rust-lang/crates.io-index"\n'
                 f'checksum = "{"a" * 64}"\n'
                 f'dependencies = ["ay-core {version} ({source(revision).split("#")[0]})"]\n')
        files[relative] = lock.encode()
    return files


def write_fixture(root: Path, files: dict[str, bytes]) -> None:
    for relative, data in files.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(0o644)


def empty_authority(m, revision=NEW, *, cdclt=False, version="0.27.0"):
    names = frozenset(ROOT_NAMES) | ({"ay-cdclt"} if cdclt else set())
    declarations = {name: {} for name in names}
    required = {name: set() for name in names}
    if cdclt:
        for owner, dependency in (("ay-dpll", "ay-cdclt"), ("ay-cdclt", "ay-core")):
            declarations[owner][dependency] = [{"git": AY_URL, "rev": revision, "version": version}]
            required[owner].add(dependency)
    return m.Target(revision, version, declarations, required, names)


class FakeCommands:
    """A simulated resolver, not evidence that Cargo resolves this fixture."""

    def __init__(self, m, root, revision, *, fail_at=0, mutate=None, metadata=None, cdclt=False,
                 version="0.27.0"):
        self.m, self.root, self.revision = m, root, revision
        self.fail_at, self.mutate = fail_at, mutate
        self.metadata = metadata
        self.cdclt = cdclt
        self.version = version
        self.calls, self.git_calls = [], []
        (root / ".fixture-git").mkdir()

    def git_run(self, args, *, cwd=None, allowed=(0,)):
        self.git_calls.append(list(args))
        if args[:2] == ["rev-parse", "--git-path"]:
            return str(self.root / ".fixture-git/transaction.lock") + "\n"
        if args[0] == "status":
            return ""
        if args[0] == "ls-files":
            if "--error-unmatch" in args:
                return "\n".join(OWNED) + "\n"
            paths = sorted({path.relative_to(self.root).as_posix()
                            for path in self.root.rglob("Cargo.*") if path.is_file()}
                           | set(self.m.GUARDS))
            separator = "\0" if "-z" in args else "\n"
            return separator.join(paths) + separator
        raise AssertionError(f"unexpected fake Git operation: {args}")

    def frontend(self, args):
        self.calls.append(list(args))
        if len(self.calls) == self.fail_at:
            raise self.m.Refusal("simulated resolver failure")
        manifest = Path(args[args.index("--manifest-path") + 1])
        lock = manifest.with_name("Cargo.lock")
        relative = lock.relative_to(self.root).as_posix()
        if "--locked" not in args:
            lock.write_bytes(fixture(self.revision, cdclt=self.cdclt, version=self.version)[relative])
        if self.mutate is not None:
            self.mutate(self, lock)
        rows = self.m.packages(lock.read_bytes(), relative)
        if self.metadata is not None:
            rows = self.metadata(self, rows)
        return json.dumps({"packages": rows})


class BumpAyPinTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        spec = importlib.util.spec_from_file_location(
            "clean_bump_ay_pin_tests_writer", ROOT / "scripts/bump_ay_pin.py")
        if spec is None or spec.loader is None:
            raise RuntimeError("cannot load transaction writer")
        cls.writer = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.writer
        with patch.object(sys, "path", [str(ROOT / "scripts"), *sys.path]):
            spec.loader.exec_module(cls.writer)

    def test_unused_vendor_declaration_does_not_admit_foreign_activation(self) -> None:
        m = self.writer

        class Authority:
            def __init__(self):
                self.doc = {"workspace": {}, "package": {"name": "veripb", "version": "3.0.2"}}
                self.alternate = None

            def read(self, path):
                self_path = "vendor/veripb/Cargo.toml"
                if path != self_path:
                    raise AssertionError(path)
                return self.doc

            def read_optional(self, path):
                if path != "vendor/veripb/Targo.toml":
                    raise AssertionError(path)
                return self.alternate

        authority = Authority()
        self.assertEqual(m.unused_vendor_declaration(
            authority, ["vendor/veripb"], "veripb", "vendor/veripb", True), "3.0.2")
        for excluded, path, optional in [([], "vendor/veripb", True),
                                         (["vendor/veripb"], "vendor/veripb/child", True),
                                         (["vendor/veripb"], "../veripb", True),
                                         (["vendor/veripb"], "vendor/veripb", False)]:
            with self.subTest(path=path, optional=optional), self.assertRaises(m.Refusal):
                m.unused_vendor_declaration(authority, excluded, "veripb", path, optional)
        for package in [{"name": "other", "version": "3.0.2"},
                        {"name": "veripb", "version": {"workspace": True}},
                        {"name": "veripb", "version": "3.0.2", "workspace": "../../"}]:
            authority.doc["package"] = package
            with self.assertRaises(m.Refusal):
                m.unused_vendor_declaration(authority, ["vendor/veripb"], "veripb", "vendor/veripb", True)
        authority.doc["package"] = {"name": "veripb", "version": "3.0.2"}
        authority.alternate = {"package": {"name": "veripb"}}
        with self.assertRaises(m.Refusal):
            m.unused_vendor_declaration(authority, ["vendor/veripb"], "veripb", "vendor/veripb", True)
        # A legitimate declaration must NOT allow the vendor to enter Clean's
        # selected graph, even with a valid same-revision AY source identity.
        with self.assertRaisesRegex(m.Refusal, "foreign effective package"):
            m.validate_metadata(json.dumps({"packages": [{"name": "veripb", "source": source(NEW)}]}),
                                fixture(NEW)["Cargo.lock"], "vendor activation", NEW)

    def test_git_edge_disambiguation_resolves_to_the_full_exact_package_identity(self) -> None:
        m = self.writer
        git_base = f"git+{TY_URL}?rev={TY}"
        git_row = {"name": "num-integer", "version": "0.1.46", "source": f"{git_base}#{TY}"}
        registry_row = {**git_row, "source": m.REGISTRY}
        index = m.package_index([git_row, registry_row])
        for qualifier in (git_base, git_row["source"]):
            self.assertIs(m.resolve_edge(f"num-integer 0.1.46 ({qualifier})", index, "fixture"), git_row)
        self.assertIs(m.resolve_edge(f"num-integer 0.1.46 ({m.REGISTRY})", index, "fixture"), registry_row)
        for edge in ("num-integer", "num-integer 0.1.46",
                     f"num-integer 0.1.47 ({git_base})",
                     f"num-integer 0.1.46 ({git_base}#{NEW})",
                     f"num-integer 0.1.46 ({git_base.replace(TY, NEW)})"):
            with self.subTest(edge=edge), self.assertRaises(m.Refusal):
                m.resolve_edge(edge, index, "fixture")
        # A fragment-free query cannot choose between two resolved commits.
        split = m.package_index([git_row, {**git_row, "source": f"{git_base}#{NEW}"}])
        with self.assertRaises(m.Refusal):
            m.resolve_edge(f"num-integer 0.1.46 ({git_base})", split, "fixture")
        for malformed in (f"{git_base}#short", f"{git_base}#", f"{m.REGISTRY}#{TY}"):
            with self.subTest(source=malformed), self.assertRaises(m.Refusal):
                m.resolve_edge(f"num-integer 0.1.46 ({malformed.split('#')[0]})",
                               m.package_index([{**git_row, "source": malformed}]), "fixture")

    def test_every_committed_lock_dependency_resolves_without_changing_its_authority(self) -> None:
        m = self.writer
        count = 0
        for lock in LOCKS:
            rows = m.packages((ROOT / lock).read_bytes(), lock)
            index = m.package_index(rows)
            for package in rows:
                for edge in package.get("dependencies", []):
                    selected = m.resolve_edge(edge, index, lock)
                    self.assertIn(selected, rows)
                    count += 1
        self.assertGreater(count, 0)

    def test_current_reads_all_six_owned_files_and_exact_rosters(self) -> None:
        m = self.writer
        with tempfile.TemporaryDirectory(prefix="clean-ay-current-") as temporary:
            root = Path(temporary).resolve()
            original = fixture()
            write_fixture(root, original)
            files = m.snapshot(root)
            self.assertEqual(set(files), set(OWNED))
            self.assertEqual({name: item.data for name, item in files.items()}, original)
            self.assertEqual({item.mode for item in files.values()}, {0o644})
            state = m.current(root, files)
            self.assertEqual((state.revision, state.version, state.ty_revision), (OLD, "0.27.0", TY))

    def test_current_refuses_split_mutable_missing_alias_and_lock_evidence(self) -> None:
        m, base = self.writer, fixture()
        manifest = base["Cargo.toml"]
        root_lock = base["Cargo.lock"]
        variants = {
            "split revision": {"Cargo.toml": manifest.replace(OLD.encode(), NEW.encode(), 1)},
            "abbreviated revision": {"Cargo.toml": manifest.replace(OLD.encode(), b"abc123")},
            "split version": {"Cargo.toml": manifest.replace(b'"0.27.0"', b'"0.25.0"', 1)},
            "wrong URL": {"Cargo.toml": manifest.replace(AY_URL.encode(), b"https://invalid/ay.git", 1)},
            "AY alias": {"Cargo.toml": manifest + (
                f'fake = {{ package = "ay-core", git = "{AY_URL}", rev = "{OLD}" }}\n').encode()},
            "missing root package": {"Cargo.lock": root_lock.replace(b'name = "ay-core"', b'name = "gone"')},
            "duplicate root package": {"Cargo.lock": root_lock + (
                f'\n[[package]]\nname = "ay-core"\nversion = "0.27.0"\nsource = "{source(OLD)}"\n').encode()},
            "stale standalone": {"bench-runner/Cargo.lock": base["bench-runner/Cargo.lock"].replace(
                OLD.encode(), NEW.encode())},
            "false resolved fragment": {"Cargo.lock": root_lock.replace(
                ("#" + OLD).encode(), ("#" + NEW).encode())},
            "wrong lock version": {"Cargo.lock": root_lock.replace(b'"0.27.0"', b'"0.25.0"', 1)},
            "split TY": {"cli-runner/Cargo.lock": base["cli-runner/Cargo.lock"].replace(
                TY.encode(), NEW.encode())},
        }
        for label, changed in variants.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory(prefix="clean-ay-refusal-") as temporary:
                root = Path(temporary).resolve()
                write_fixture(root, base | changed)
                with self.assertRaises(m.Refusal):
                    m.current(root, m.snapshot(root))

    def test_snapshot_refuses_missing_symlink_and_hardlink_owned_files(self) -> None:
        m = self.writer
        for kind in ("missing", "symlink", "hardlink"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory(prefix="clean-ay-path-") as temporary:
                root = Path(temporary).resolve()
                write_fixture(root, fixture())
                path = root / "Cargo.lock"
                if kind == "missing":
                    path.unlink()
                elif kind == "symlink":
                    real = root / "other.lock"
                    path.rename(real)
                    path.symlink_to(real)
                else:
                    (root / "other.lock").hardlink_to(path)
                with self.assertRaises(m.Refusal):
                    m.snapshot(root)

    def test_manifest_rewrite_changes_only_seven_revision_values_and_is_idempotent(self) -> None:
        m = self.writer
        files = {name: m.Snapshot(data, 0o644) for name, data in fixture().items()}
        state = m.Current(OLD, "0.27.0", TY)
        self.assertEqual(m.rewritten(files, state, NEW), {"Cargo.toml": fixture(NEW)["Cargo.toml"]})
        self.assertEqual(m.rewritten(files, state, OLD), {"Cargo.toml": files["Cargo.toml"].data})
        for revision in ("main", "latest", NEW[:12], NEW.upper(), "", None):
            with self.subTest(revision=revision), self.assertRaises(m.Refusal):
                m.rewritten(files, state, revision)

    def test_target_catalog_is_complete_immutable_and_source_specific(self) -> None:
        m = self.writer
        documents = {"Cargo.toml": {"workspace": {"package": {"version": "0.27.0"},
                     "members": ["crates/" + name for name in ROOT_NAMES]}}}
        documents.update({f"crates/{name}/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}} for name in ROOT_NAMES})
        def observe(changes):
            docs = documents | changes
            reads = []
            class FakeAuthority:
                def __init__(self, commands, directory, revision):
                    self.revision = m.exact_sha(revision)
                def read(self, relative):
                    reads.append(relative)
                    return docs[relative]
                def read_optional(self, relative):
                    return docs.get(relative)
            with patch.object(m, "Authority", FakeAuthority):
                result = m.target(None, Path("/unused"), m.Current(OLD, "0.27.0", TY), NEW)
            self.assertEqual(len(reads), 39)
            return result
        result = observe({})
        self.assertEqual((result.revision, result.version), (NEW, "0.27.0"))
        self.assertEqual(set(result.declarations), set(ROOT_NAMES))
        variants = {
            "target version": {"Cargo.toml": {"workspace": {"package": {"version": "0.28.0"}, "members": []}}},
            "missing member": {"Cargo.toml": {"workspace": {"package": {"version": "0.27.0"},
                                "members": ["crates/" + name for name in ROOT_NAMES[1:]]}}},
            "duplicate package": {"crates/ay/Cargo.toml": {"package": {"name": "ay-core", "version": "0.27.0"}}},
            "package version": {"crates/ay/Cargo.toml": {"package": {"name": "ay", "version": "0.25.0"}}},
            "missing inherited dependency": {"crates/ay/Cargo.toml": {
                "package": {"name": "ay", "version": "0.27.0"}, "dependencies": {"missing": {"workspace": True}}}},
            "foreign AY path": {"crates/ay/Cargo.toml": {
                "package": {"name": "ay", "version": "0.27.0"}, "dependencies": {"ay-core": {"path": "../wrong"}}}},
            "mutable dependency": {"crates/ay/Cargo.toml": {
                "package": {"name": "ay", "version": "0.27.0"},
                "dependencies": {"external": {"git": "https://invalid/dep", "branch": "main"}}}},
        }
        for label, changes in variants.items():
            with self.subTest(label=label), self.assertRaises(m.Refusal):
                observe(changes)

    def test_graph_preserves_non_ay_rows_and_normalizes_only_exact_ay_references(self) -> None:
        m, before, after = self.writer, fixture(), fixture(NEW)
        state, authority = m.Current(OLD, "0.27.0", TY), empty_authority(m)
        for lock in LOCKS:
            m.validate_graph(before[lock], after[lock], lock, state, NEW, authority)
        data = after["Cargo.lock"]
        variants = {
            "registry version": data.replace(b'name = "unrelated"\nversion = "1.0.0"',
                                               b'name = "unrelated"\nversion = "2.0.0"'),
            "checksum": data.replace(("a" * 64).encode(), ("b" * 64).encode()),
            "TY pin": data.replace(TY.encode(), OLD.encode()),
            "AY version": data.replace(b'"0.27.0"', b'"0.25.0"', 1),
            "stale AY": data.replace(NEW.encode(), OLD.encode(), 2),
            "duplicate AY": data + (f'\n[[package]]\nname = "ay"\nversion = "0.27.0"\nsource = "{source(NEW)}"\n').encode(),
            "new AY edge": data.replace(b'name = "ay"\n', b'name = "ay"\ndependencies = ["unrelated"]\n', 1),
            "lock format": data.replace(b'version = 4', b'version = 3', 1),
        }
        for label, candidate in variants.items():
            with self.subTest(label=label), self.assertRaises(m.Refusal):
                m.validate_graph(before["Cargo.lock"], candidate, "Cargo.lock", state, NEW, authority)
        # A source-shaped inert value is not a dependency edge and may not be rewritten.
        original = before["Cargo.lock"] + f'note = "{source(OLD)}"\n'.encode()
        candidate = after["Cargo.lock"] + f'note = "{source(NEW)}"\n'.encode()
        with self.assertRaises(m.Refusal):
            m.validate_graph(original, candidate, "Cargo.lock", state, NEW, authority)

    def test_target_resolves_nested_member_and_inherited_owning_path(self) -> None:
        m = self.writer
        members = {name: "crates/" + name for name in ROOT_NAMES}
        members["ay-nra"] = "crates/ay-theories/nra"
        documents = {"Cargo.toml": {"workspace": {
            "package": {"version": "0.27.0"}, "members": list(members.values()),
            "dependencies": {"ay-core": {"path": "crates/ay-core", "version": "0.27.0"}},
        }}}
        documents.update({path + "/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}
        } for name, path in members.items()})
        documents["crates/ay-theories/nra/Cargo.toml"]["dependencies"] = {
            "ay-core": {"workspace": True}, "unrelated": "1.0",
        }
        class FakeAuthority:
            def __init__(self, commands, directory, revision):
                self.revision = m.exact_sha(revision)
            def read(self, relative):
                return documents[relative]
            def read_optional(self, relative):
                return documents.get(relative)
        with patch.object(m, "Authority", FakeAuthority):
            selected = m.target(None, Path("/unused"), m.Current(OLD, "0.27.0", TY), NEW)
        self.assertEqual(selected.declarations["ay-nra"]["ay-core"], [
            {"git": AY_URL, "rev": NEW, "version": "0.27.0"}])
        self.assertEqual(selected.declarations["ay-nra"]["unrelated"], [{"version": "1.0"}])
        self.assertEqual(selected.required["ay-nra"], {"ay-core", "unrelated"})

    def test_inactive_optional_owning_paths_do_not_expand_the_resolved_roster(self) -> None:
        m = self.writer
        names = (*ROOT_NAMES, "ay-lrat-check")
        documents = {"Cargo.toml": {"workspace": {
            "package": {"version": "0.27.0"},
            "members": ["crates/" + name for name in names],
            "dependencies": {"ay-lrat-check": {"path": "crates/ay-lrat-check", "version": "0.27.0"}},
        }}}
        documents.update({f"crates/{name}/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}} for name in names})
        documents["crates/ay/Cargo.toml"]["dependencies"] = {
            "ay-lrat-check": {"workspace": True, "optional": True},
        }

        def observe(changes=None):
            docs = documents | (changes or {})
            class FakeAuthority:
                def __init__(self, commands, directory, revision):
                    m.exact_sha(revision)
                def read(self, relative):
                    return docs[relative]
                def read_optional(self, relative):
                    return docs.get(relative)
            with patch.object(m, "Authority", FakeAuthority):
                return m.target(None, Path("/unused"), m.Current(OLD, "0.27.0", TY), NEW)

        authority = observe()
        self.assertEqual(authority.package_names, frozenset(ROOT_NAMES))
        self.assertEqual(authority.required["ay"], set())
        self.assertEqual(authority.declarations["ay"]["ay-lrat-check"], [
            {"git": AY_URL, "rev": NEW, "version": "0.27.0"}])
        before, after = fixture(), fixture(NEW)
        state = m.Current(OLD, "0.27.0", TY)
        for lock in LOCKS:
            m.validate_graph(before[lock], after[lock], lock, state, NEW, authority)
            activated = after[lock] + (f'\n[[package]]\nname = "ay-lrat-check"\n'
                f'version = "0.27.0"\nsource = "{source(NEW)}"\n').encode()
            with self.subTest(lock=lock), self.assertRaises(m.Refusal):
                m.validate_graph(before[lock], activated, lock, state, NEW, authority)
        workspace = documents["Cargo.toml"]["workspace"]
        variants = {
            "required unreviewed package": {"crates/ay/Cargo.toml": documents["crates/ay/Cargo.toml"] | {
                "dependencies": {"ay-lrat-check": {"workspace": True}}}},
            "missing owning package": {"Cargo.toml": {"workspace": workspace | {
                "members": ["crates/" + name for name in ROOT_NAMES]}}},
            "wrong owning path": {"Cargo.toml": {"workspace": workspace | {
                "dependencies": {"ay-lrat-check": {"path": "crates/ay-core"}}}}},
            "mixed foreign authority": {"Cargo.toml": {"workspace": workspace | {
                "dependencies": {"ay-lrat-check": {"path": "crates/ay-lrat-check", "git": "https://invalid/ay.git"}}}}},
            "registry substitution": {"Cargo.toml": {"workspace": workspace | {
                "dependencies": {"ay-lrat-check": {"version": "0.27.0"}}}}},
            "wrong package version": {"crates/ay-lrat-check/Cargo.toml": {
                "package": {"name": "ay-lrat-check", "version": "0.28.0"}}},
        }
        for label, changes in variants.items():
            with self.subTest(label=label), self.assertRaises(m.Refusal):
                observe(changes)

    def test_target_refuses_exclusions_workspace_redirects_and_alternate_manifests(self) -> None:
        m = self.writer
        members = {name: "crates/" + name for name in ROOT_NAMES}
        members["ay-nra"] = "crates/ay-theories/nra"
        workspace = {"package": {"version": "0.27.0"}, "members": list(members.values())}
        documents = {"Cargo.toml": {"workspace": workspace}}
        documents.update({path + "/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}
        } for name, path in members.items()})
        member = "crates/ay-theories/nra/Cargo.toml"
        ancestor = "crates/ay-theories/Cargo.toml"

        def observe(*, workspace_changes=None, changes=None):
            docs = json.loads(json.dumps(documents))
            docs["Cargo.toml"]["workspace"].update(workspace_changes or {})
            docs.update(changes or {})
            probes = []
            class FakeAuthority:
                def __init__(self, commands, directory, revision):
                    self.revision = m.exact_sha(revision)
                def read(self, relative):
                    if relative not in docs:
                        raise m.Refusal("missing immutable fixture: " + relative)
                    return docs[relative]
                def read_optional(self, relative):
                    probes.append(relative)
                    return docs.get(relative)
            with patch.object(m, "Authority", FakeAuthority):
                selected = m.target(None, Path("/unused"), m.Current(OLD, "0.27.0", TY), NEW)
            self.assertEqual(set(selected.declarations), set(ROOT_NAMES))
            return probes

        probes = observe(workspace_changes={"exclude": ["examples"]})
        self.assertIn(ancestor, probes)  # A genuinely absent ancestor is admissible.
        self.assertEqual(probes.count("crates/Targo.toml"), 1)
        observe(changes={ancestor: {"package": {"name": "auxiliary", "version": "1.0.0"}}})
        for excluded in ("crates/ay-theories/nra", "crates/ay-theories", "crates"):
            with self.subTest(excluded=excluded), self.assertRaises(m.Refusal):
                observe(workspace_changes={"exclude": [excluded]})
        malformed_lists = (
            {"members": workspace["members"] + [workspace["members"][0]]},
            {"members": "crates/ay"}, {"exclude": "examples"},
            {"exclude": ["examples", "examples"]}, {"exclude": [False]},
        )
        for change in malformed_lists:
            with self.subTest(change=change), self.assertRaises(m.Refusal):
                observe(workspace_changes=change)
        for path in ("../crates/ay", "crates/./ay", "crates//ay", "crates/ay/", "crates/*", "/crates/ay"):
            for field in ("members", "exclude"):
                with self.subTest(path=path, field=field), self.assertRaises(m.Refusal):
                    observe(workspace_changes={field: [path]})
        member_package = documents[member]["package"]
        redirects = {
            "member workspace": {member: {"package": member_package, "workspace": {}}},
            "member explicit root": {member: {"package": member_package | {"workspace": "../../.."}}},
            "member explicit foreign": {member: {"package": member_package | {"workspace": "../foreign"}}},
            "member malformed owner": {member: {"package": member_package | {"workspace": False}}},
            "ancestor workspace": {ancestor: {"workspace": {}}},
            "ancestor package redirect": {ancestor: {"package": {"workspace": "../.."}}},
            "ancestor legacy redirect": {ancestor: {"project": {"workspace": "../.."}}},
            "ancestor malformed package": {ancestor: {"package": []}},
        }
        for label, changes in redirects.items():
            with self.subTest(label=label), self.assertRaises(m.Refusal):
                observe(changes=changes)
        for directory in ("", "crates", "crates/ay-theories", "crates/ay-theories/nra"):
            alternate = (directory + "/" if directory else "") + "Targo.toml"
            with self.subTest(alternate=alternate), self.assertRaises(m.Refusal):
                observe(changes={alternate: {}})

    def test_authority_fetches_exact_commit_and_rejects_rewrites_and_symlink_blobs(self) -> None:
        m = self.writer
        class FakeGit:
            def __init__(self, mutation=""):
                self.mutation, self.calls, self.agh_calls = mutation, [], []
            def git_run(self, args, *, cwd=None, allowed=(0,)):
                self.calls.append(list(args))
                if args[0] == "init":
                    return ""
                if args[0] == "config":
                    return ("url.https://invalid/.insteadof https://github.com/alabsystems/\n"
                            if self.mutation == "rewrite" else "")
                if args == ["remote", "add", "origin", AY_URL]:
                    return ""
                if args[0] == "rev-parse":
                    if args != ["rev-parse", "--verify", "refs/agh/pin-authority^{commit}"]:
                        raise AssertionError(f"unexpected authority ref: {args}")
                    return (OLD if self.mutation == "wrong commit" else NEW) + "\n"
                if args[0] == "ls-tree":
                    mode = "120000" if self.mutation == "symlink" else "100644"
                    return f"{mode} blob {'a' * 40}\tCargo.toml\0"
                if args[0] == "show":
                    return '[workspace.package]\nversion = "0.27.0"\n'
                raise AssertionError(f"unexpected authority Git operation: {args}")
            def agh_run(self, args, *, cwd):
                self.agh_calls.append(list(args))
                if args != ["repo", "fetch", "alabsystems/ay", str(cwd),
                            "--ref", NEW, "--into", "refs/agh/pin-authority"]:
                    raise AssertionError(f"unexpected authority Agh operation: {args}")
                if self.mutation == "Agh refusal":
                    raise m.Refusal("Agh refused source access")
                return ""
        with tempfile.TemporaryDirectory(prefix="clean-ay-objects-") as temporary:
            root = Path(temporary).resolve()
            commands = FakeGit()
            authority = m.Authority(commands, root / "positive", NEW)
            self.assertEqual(authority.read("Cargo.toml")["workspace"]["package"]["version"], "0.27.0")
            self.assertEqual(authority.revision, NEW)
            self.assertFalse(any("main" in args for args in commands.calls))
            self.assertEqual(len(commands.agh_calls), 1)
            self.assertFalse(any("fetch" in args for args in commands.calls))
            for mutation in ("wrong commit", "rewrite", "symlink", "Agh refusal"):
                with self.subTest(mutation=mutation), self.assertRaises(m.Refusal):
                    candidate = m.Authority(FakeGit(mutation), root / mutation.replace(" ", "-"), NEW)
                    candidate.read("Cargo.toml")

    def test_optional_immutable_manifest_distinguishes_absence_from_unusable_objects(self) -> None:
        m = self.writer
        relative = "crates/ay-theories/Cargo.toml"
        class FakeGit:
            def __init__(self, mutation=""):
                self.mutation, self.calls = mutation, []
            def git_run(self, args, *, cwd=None, allowed=(0,)):
                self.calls.append(list(args))
                if args == ["ls-tree", "-z", NEW, "--", relative]:
                    if self.mutation == "absent":
                        return ""
                    if self.mutation == "Git failure":
                        raise m.Refusal("simulated immutable-tree read failure")
                    mode = {"symlink": "120000", "directory": "040000", "gitlink": "160000",
                            "executable": "100755"}.get(self.mutation, "100644")
                    kind = "tree" if self.mutation == "wrong type" else "blob"
                    name = "elsewhere/Cargo.toml" if self.mutation == "wrong path" else relative
                    oid = "a" * (12 if self.mutation == "short object" else 40)
                    entry = f"{mode} {kind} {oid}\t{name}\0"
                    return entry * (2 if self.mutation == "duplicate" else 1)
                if args == ["show", f"{NEW}:{relative}"]:
                    if self.mutation == "show failure":
                        raise m.Refusal("simulated immutable-blob read failure")
                    return "[broken" if self.mutation == "malformed TOML" else '[package]\nname = "auxiliary"\n'
                raise AssertionError(f"unexpected optional-object Git operation: {args}")

        def reader(mutation=""):
            # Isolate the real reader; the preceding test covers real constructor
            # admission with fake Agh/private-ref reads, without executing Git.
            candidate = object.__new__(m.Authority)
            candidate.commands, candidate.directory, candidate.revision = FakeGit(mutation), Path("/unused"), NEW
            candidate._documents = {}
            return candidate

        for mode in ("", "executable"):
            candidate = reader(mode)
            self.assertEqual(candidate.read_optional(relative), {"package": {"name": "auxiliary"}})
            self.assertEqual(candidate.read(relative), candidate.read_optional(relative))
            self.assertEqual(len(candidate.commands.calls), 2)  # One tree and one blob, cached thereafter.
        absent = reader("absent")
        self.assertIsNone(absent.read_optional(relative))
        self.assertIsNone(absent.read_optional(relative))
        with self.assertRaises(m.Refusal):
            absent.read(relative)
        self.assertEqual(len(absent.commands.calls), 1)
        for mutation in ("symlink", "directory", "gitlink", "wrong type", "wrong path", "short object",
                         "duplicate", "Git failure", "show failure", "malformed TOML"):
            with self.subTest(mutation=mutation), self.assertRaises(m.Refusal):
                reader(mutation).read_optional(relative)
        candidate = reader()
        for path in ("", "/Cargo.toml", "../Cargo.toml", "crates/./Cargo.toml", "crates//Cargo.toml", "*", None):
            with self.subTest(path=path), self.assertRaises(m.Refusal):
                candidate.read_optional(path)
        self.assertEqual(candidate.commands.calls, [])

    def test_graph_checks_admitted_and_required_target_dependency_edges(self) -> None:
        m, before, after = self.writer, fixture(), fixture(NEW)
        state, authority = m.Current(OLD, "0.27.0", TY), empty_authority(m)
        authority.declarations["ay"]["unrelated"] = [{"version": "1.0.0"}]
        authority.required["ay"].add("unrelated")
        with_edge = after["Cargo.lock"].replace(
            b'name = "ay"\n', b'name = "ay"\ndependencies = ["unrelated"]\n', 1)
        m.validate_graph(before["Cargo.lock"], with_edge, "Cargo.lock", state, NEW, authority)
        with self.assertRaises(m.Refusal):
            m.validate_graph(before["Cargo.lock"], after["Cargo.lock"], "Cargo.lock", state, NEW, authority)
        authority.declarations["ay"]["unrelated"] = [{"version": "2.0.0"}]
        with self.assertRaises(m.Refusal):
            m.validate_graph(before["Cargo.lock"], with_edge, "Cargo.lock", state, NEW, authority)

    def test_cdclt_inventory_requires_one_canonical_owning_edge_in_every_lock(self) -> None:
        m = self.writer
        good = fixture(cdclt=True)
        with tempfile.TemporaryDirectory(prefix="clean-ay-cdclt-inventory-") as temporary:
            root = Path(temporary).resolve()
            write_fixture(root, good)
            self.assertEqual(m.current(root, m.snapshot(root)).revision, OLD)
            for lock in LOCKS:
                rows = m.packages(good[lock], lock)
                expected = m.ROSTERS[lock] | {"ay-cdclt"}
                self.assertEqual(m.pins.ay_lock_package_names(rows, m.ROSTERS[lock]), expected)
                self.assertEqual(len(rows) - len(m.packages(fixture()[lock], lock)), 1)
                for qualifier in (source(OLD), source(OLD).split("#", 1)[0]):
                    next(row for row in rows if row["name"] == "ay-dpll")["dependencies"] = [
                        f"ay-cdclt 0.27.0 ({qualifier})"]
                    self.assertEqual(m.pins.ay_lock_package_names(rows, m.ROSTERS[lock]), expected)
            block = (f'[[package]]\nname = "ay-cdclt"\nversion = "0.27.0"\n'
                     f'source = "{source(OLD)}"\ndependencies = ["ay-core"]\n\n').encode()
            variants = {
                "missing": good["Cargo.lock"].replace(block, b""),
                "unreferenced": good["Cargo.lock"].replace(b'dependencies = ["ay-cdclt"]', b''),
                "duplicate": good["Cargo.lock"] + block,
                "unknown": good["Cargo.lock"] + block.replace(b'"ay-cdclt"', b'"ay-unreviewed"'),
                "foreign package": good["Cargo.lock"].replace(block, block.replace(
                    source(OLD).encode(), b"registry+https://github.com/rust-lang/crates.io-index")),
                "foreign edge": good["Cargo.lock"].replace(b'dependencies = ["ay-cdclt"]', (
                    f'dependencies = ["ay-cdclt 0.27.0 ({source(NEW)})"]').encode()),
                "wrong edge version": good["Cargo.lock"].replace(
                    b'dependencies = ["ay-cdclt"]', b'dependencies = ["ay-cdclt 0.28.0"]'),
            }
            for label, lock in variants.items():
                with self.subTest(label=label):
                    write_fixture(root, good | {"Cargo.lock": lock})
                    with self.assertRaises(m.Refusal):
                        m.current(root, m.snapshot(root))
            write_fixture(root, good | {"bench-runner/Cargo.lock": fixture()["bench-runner/Cargo.lock"]})
            with self.assertRaisesRegex(m.Refusal, "inventory generations"):
                m.current(root, m.snapshot(root))

    def test_cdclt_target_is_derived_from_exact_immutable_declarations(self) -> None:
        m = self.writer
        names = (*ROOT_NAMES, "ay-cdclt")
        documents = {"Cargo.toml": {"workspace": {
            "package": {"version": "0.27.0"}, "members": ["crates/" + name for name in names]}}}
        documents.update({f"crates/{name}/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}} for name in names})
        documents["crates/ay-dpll/Cargo.toml"]["dependencies"] = {"ay-cdclt": {"path": "../ay-cdclt"}}
        documents["crates/ay-cdclt/Cargo.toml"]["dependencies"] = {"ay-core": {"path": "../ay-core"}}

        def observe(changes):
            docs = documents | changes
            class FakeAuthority:
                def __init__(self, commands, directory, revision):
                    m.exact_sha(revision)
                def read(self, relative):
                    if relative not in docs:
                        raise m.Refusal("missing immutable fixture: " + relative)
                    return docs[relative]
                def read_optional(self, relative):
                    return docs.get(relative)
            with patch.object(m, "Authority", FakeAuthority):
                return m.target(None, Path("/unused"), m.Current(OLD, "0.27.0", TY), NEW)

        target = observe({})
        self.assertEqual(target.package_names, frozenset(names))
        self.assertEqual(target.required["ay-dpll"], {"ay-cdclt"})
        self.assertEqual(target.required["ay-cdclt"], {"ay-core"})
        legacy = observe({"crates/ay-dpll/Cargo.toml": documents["crates/ay-dpll/Cargo.toml"] | {"dependencies": {}}})
        self.assertEqual(legacy.package_names, frozenset(ROOT_NAMES), "mere package presence cannot expand the roster")
        before, after = fixture(), fixture(NEW, cdclt=True)
        state = m.Current(OLD, "0.27.0", TY)
        for lock in LOCKS:
            m.validate_graph(before[lock], after[lock], lock, state, NEW, target)
            with self.assertRaises(m.Refusal):
                m.validate_graph(before[lock], after[lock], lock, state, NEW, legacy)
        changes = {
            "missing target package": {"Cargo.toml": {"workspace": {
                "package": {"version": "0.27.0"}, "members": ["crates/" + name for name in ROOT_NAMES]}}},
            "wrong package version": {"crates/ay-cdclt/Cargo.toml": {"package": {"name": "ay-cdclt", "version": "0.28.0"}}},
            "foreign resolution": {"crates/ay-dpll/Cargo.toml": documents["crates/ay-dpll/Cargo.toml"] | {
                "dependencies": {"ay-cdclt": {"git": "https://invalid/ay.git", "rev": NEW}}}},
            "wrong owning path": {"crates/ay-dpll/Cargo.toml": documents["crates/ay-dpll/Cargo.toml"] | {
                "dependencies": {"ay-cdclt": {"path": "../ay-core"}}}},
            "unreviewed AY dependency": {"crates/ay-cdclt/Cargo.toml": documents["crates/ay-cdclt/Cargo.toml"] | {
                "dependencies": {"ay-unreviewed": {"path": "../ay-unreviewed"}}}},
        }
        for label, changed in changes.items():
            with self.subTest(label=label), self.assertRaises(m.Refusal):
                observe(changed)

    def test_cdclt_migration_cannot_forge_edges_or_change_external_resolution(self) -> None:
        m = self.writer
        before, good = fixture()["Cargo.lock"], fixture(NEW, cdclt=True)["Cargo.lock"]
        authority = empty_authority(m, cdclt=True)
        state = m.Current(OLD, "0.27.0", TY)
        cdclt = (f'name = "ay-cdclt"\nversion = "0.27.0"\nsource = "{source(NEW)}"\n'
                 'dependencies = ["ay-core"]').encode()
        variants = {
            "missing required cdclt edge": good.replace(b'dependencies = ["ay-cdclt"]', b''),
            "forged cdclt dependency": good.replace(cdclt, cdclt.replace(b'["ay-core"]', b'["ay-sat"]')),
            "forged registry dependency": good.replace(cdclt, cdclt.replace(b'["ay-core"]', b'["ay-core", "unrelated"]')),
            "non-AY checksum": good.replace(b'a' * 64, b'b' * 64),
        }
        for label, candidate in variants.items():
            with self.subTest(label=label), self.assertRaises(m.Refusal):
                m.validate_graph(before, candidate, "Cargo.lock", state, NEW, authority)

    def test_cdclt_transaction_migrates_and_preserves_new_same_revision_requests(self) -> None:
        m = self.writer
        for same_revision in (False, True):
            with self.subTest(same_revision=same_revision), tempfile.TemporaryDirectory(prefix="clean-ay-cdclt-success-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                if same_revision:
                    write_fixture(root, fixture(NEW, cdclt=True))
                commands = FakeCommands(m, root, NEW, cdclt=True)
                with patch.object(m, "target", return_value=empty_authority(m, cdclt=True)):
                    m.transaction(root, NEW, commands)
                self.assertEqual({name: (root / name).read_bytes() for name in OWNED}, fixture(NEW, cdclt=True))
                self.assertEqual(len(commands.calls), 10)
                self.assertTrue(all("--locked" in args for args in commands.calls[5:]))
                self.assertEqual(all("--locked" in args for args in commands.calls[:5]), same_revision)

    def test_cdclt_migration_failures_restore_legacy_bytes_and_modes(self) -> None:
        m = self.writer
        for failure in (1, 3, 6, 10, "foreign metadata"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory(prefix="clean-ay-cdclt-rollback-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                (root / "Cargo.toml").chmod(0o640)
                before = m.snapshot(root)
                def metadata(commands, rows):
                    if failure == "foreign metadata" and len(commands.calls) == 6:
                        next(row for row in rows if row["name"] == "ay-cdclt")["source"] = source(OLD)
                    return rows
                commands = FakeCommands(m, root, NEW, cdclt=True,
                                        fail_at=failure if isinstance(failure, int) else 0, metadata=metadata)
                with patch.object(m, "target", return_value=empty_authority(m, cdclt=True)):
                    with self.assertRaises(m.Refusal):
                        m.transaction(root, NEW, commands)
                self.assertEqual(m.snapshot(root), before)

    def transaction_fixture(self, root):
        m = self.writer
        write_fixture(root, fixture())
        for relative in m.GUARDS:
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"# protected helper fixture; never executed\n")
        for lock in LOCKS[1:]:
            (root / Path(lock).with_name("Cargo.toml")).write_bytes(
                b'[package]\nname = "fixture"\nversion = "1.0.0"\n')

    def test_transaction_refreshes_then_rechecks_all_five_graphs_without_git_writes(self) -> None:
        m = self.writer
        with tempfile.TemporaryDirectory(prefix="clean-ay-success-") as temporary:
            root = Path(temporary).resolve()
            self.transaction_fixture(root)
            commands = FakeCommands(m, root, NEW)
            with patch.object(m, "target", return_value=empty_authority(m)) as admitted:
                m.transaction(root, NEW, commands)
            self.assertEqual(admitted.call_count, 1)
            self.assertEqual({name: (root / name).read_bytes() for name in OWNED}, fixture(NEW))
            self.assertEqual(len(commands.calls), 10)
            self.assertTrue(all("--locked" not in args for args in commands.calls[:5]))
            self.assertTrue(all("--locked" in args for args in commands.calls[5:]))
            self.assertTrue(all(args[0] == "metadata" for args in commands.calls))
            self.assertTrue(all(args[0] in ("ls-files", "status", "rev-parse") for args in commands.git_calls))

    def test_same_revision_still_requires_target_and_ten_locked_metadata_calls(self) -> None:
        m = self.writer
        with tempfile.TemporaryDirectory(prefix="clean-ay-noop-") as temporary:
            root = Path(temporary).resolve()
            self.transaction_fixture(root)
            before = m.snapshot(root)
            commands = FakeCommands(m, root, OLD)
            with patch.object(m, "target", return_value=empty_authority(m, OLD)) as admitted:
                m.transaction(root, OLD, commands)
            self.assertEqual(admitted.call_count, 1)
            self.assertEqual(m.snapshot(root), before)
            self.assertEqual(len(commands.calls), 10)
            self.assertTrue(all("--locked" in args for args in commands.calls))

    def test_resolver_failures_restore_all_six_original_bytes_and_modes(self) -> None:
        m = self.writer
        for failing_call in (1, 3, 6, 10):
            with self.subTest(call=failing_call), tempfile.TemporaryDirectory(prefix="clean-ay-rollback-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                (root / "Cargo.toml").chmod(0o640)
                before = m.snapshot(root)
                commands = FakeCommands(m, root, NEW, fail_at=failing_call)
                with patch.object(m, "target", return_value=empty_authority(m)):
                    with self.assertRaisesRegex(m.Refusal, "simulated resolver failure"):
                        m.transaction(root, NEW, commands)
                self.assertEqual(m.snapshot(root), before)

    def test_target_refusal_precedes_any_install_or_resolver(self) -> None:
        m = self.writer
        with tempfile.TemporaryDirectory(prefix="clean-ay-target-") as temporary:
            root = Path(temporary).resolve()
            self.transaction_fixture(root)
            before = m.snapshot(root)
            commands = FakeCommands(m, root, NEW)
            with patch.object(m, "target", side_effect=m.Refusal("target refused")):
                with self.assertRaisesRegex(m.Refusal, "target refused"):
                    m.transaction(root, NEW, commands)
            self.assertEqual(m.snapshot(root), before)
            self.assertEqual(commands.calls, [])

    def test_unreviewed_coherent_versions_refuse_before_target_or_resolver(self) -> None:
        m = self.writer
        for version in ("0.26.0", "0.29.0"):
            with self.subTest(version=version), tempfile.TemporaryDirectory(prefix="clean-ay-version-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                write_fixture(root, {name: data.replace(b"0.27.0", version.encode())
                                     for name, data in fixture().items()})
                before = m.snapshot(root)
                commands = FakeCommands(m, root, NEW)
                with patch.object(m, "target", side_effect=AssertionError("target called")):
                    with self.assertRaisesRegex(m.Refusal, "package-version migration requires separate review"):
                        m.transaction(root, NEW, commands)
                self.assertEqual(m.snapshot(root), before)
                self.assertEqual(commands.calls, [])

    def test_existing_lock_and_unowned_ay_graph_refuse_without_owned_changes(self) -> None:
        m = self.writer
        for kind in ("existing lock", "unowned AY lock"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory(prefix="clean-ay-admission-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                before = m.snapshot(root)
                commands = FakeCommands(m, root, NEW)
                lock = root / ".fixture-git/transaction.lock"
                if kind == "existing lock":
                    lock.mkdir()
                else:
                    extra = root / "unowned/Cargo.lock"
                    extra.parent.mkdir()
                    extra.write_bytes(fixture()["Cargo.lock"])
                with patch.object(m, "target", side_effect=AssertionError("target called")):
                    with self.assertRaises(m.Refusal):
                        m.transaction(root, NEW, commands)
                self.assertEqual(m.snapshot(root), before)
                self.assertEqual(commands.calls, [])
                if kind == "existing lock":
                    self.assertTrue(lock.is_dir())

    def test_effective_metadata_cannot_substitute_a_foreign_source_even_on_noop(self) -> None:
        m = self.writer
        for selected in (OLD, NEW):
            with self.subTest(selected=selected), tempfile.TemporaryDirectory(prefix="clean-ay-effective-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                before = m.snapshot(root)
                def metadata(commands, rows):
                    if len(commands.calls) == 6:
                        rows[0]["source"] = source(NEW if selected == OLD else OLD)
                    return rows
                commands = FakeCommands(m, root, selected, metadata=metadata)
                with patch.object(m, "target", return_value=empty_authority(m, selected)):
                    with self.assertRaises(m.Refusal):
                        m.transaction(root, selected, commands)
                self.assertEqual(m.snapshot(root), before)
                self.assertEqual(len(commands.calls), 6)

    def test_reviewed_version_migration_requires_explicit_forward_selection(self) -> None:
        m = self.writer
        old = m.Current(OLD, "0.27.0", TY)
        new = m.Current(NEW, "0.28.0", TY)
        self.assertEqual(m.selected_version(old, None), "0.27.0")
        self.assertEqual(m.selected_version(old, "0.28.0"), "0.28.0")
        self.assertEqual(m.selected_version(new, None), "0.28.0")
        for state, requested in ((old, "0.29.0"), (old, "0.28"), (old, "^0.28.0"),
                                 (old, "0.28.1"), (new, "0.27.0")):
            with self.subTest(requested=requested), self.assertRaises(m.Refusal):
                m.selected_version(state, requested)

    def test_version_migration_rewrites_only_the_seven_revision_and_version_values(self) -> None:
        m = self.writer
        files = {name: m.Snapshot(data, 0o644) for name, data in fixture().items()}
        expected = fixture(NEW, version="0.28.0")
        rewritten = m.rewritten(files, m.Current(OLD, "0.27.0", TY), NEW, "0.28.0")
        self.assertEqual(rewritten, {"Cargo.toml": expected["Cargo.toml"]})
        self.assertEqual(rewritten["Cargo.toml"].count(b'version = "0.28.0"'), 7)
        self.assertEqual(rewritten["Cargo.toml"].count(NEW.encode()), 7)

    def test_version_migration_preserves_every_non_ay_node_and_resolved_edge(self) -> None:
        m = self.writer
        old, new = fixture(), fixture(NEW, version="0.28.0")
        state, authority = m.Current(OLD, "0.27.0", TY), empty_authority(m, version="0.28.0")
        for lock in LOCKS:
            m.validate_graph(old[lock], new[lock], lock, state, NEW, authority)
        data = new["Cargo.lock"]
        mutations = (
            data.replace(b'version = "0.28.0"', b'version = "0.27.0"', 1),
            data.replace(TY.encode(), NEW.encode()),
            data.replace(("a" * 64).encode(), ("b" * 64).encode()),
            data.replace(b'unrelated"\nversion = "1.0.0"', b'unrelated"\nversion = "2.0.0"'),
            data.replace(b'ay-core 0.28.0', b'ay-core 0.27.0'),
            data.replace(b'name = "ay"\n', b'name = "ay"\ndependencies = ["unrelated"]\n', 1),
        )
        for index, changed in enumerate(mutations):
            with self.subTest(mutation=index), self.assertRaises(m.Refusal):
                m.validate_graph(old["Cargo.lock"], changed, "Cargo.lock", state, NEW, authority)

    def test_explicit_version_migration_refreshes_and_rechecks_all_five_locked_graphs(self) -> None:
        m = self.writer
        with tempfile.TemporaryDirectory(prefix="clean-ay-version-move-") as temporary:
            root = Path(temporary).resolve()
            self.transaction_fixture(root)
            commands = FakeCommands(m, root, NEW, version="0.28.0")
            with patch.object(m, "target", return_value=empty_authority(m, version="0.28.0")):
                m.transaction(root, NEW, commands, "0.28.0")
            self.assertEqual({name: (root / name).read_bytes() for name in OWNED},
                             fixture(NEW, version="0.28.0"))
            self.assertEqual(len(commands.calls), 10)
            self.assertTrue(all("--locked" in args for args in commands.calls[5:]))
            self.assertEqual(m.current(root, m.snapshot(root)), m.Current(NEW, "0.28.0", TY))
            self.assertTrue(all(args[0] in ("ls-files", "status", "rev-parse")
                                for args in commands.git_calls))

    def test_version_migration_wrong_target_and_resolver_failures_restore_exact_old_state(self) -> None:
        m = self.writer
        for fail_at in (0, 1, 3, 6, 10):
            with self.subTest(call=fail_at), tempfile.TemporaryDirectory(prefix="clean-ay-version-red-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                (root / "Cargo.toml").chmod(0o640)
                before = m.snapshot(root)
                commands = FakeCommands(m, root, NEW, version="0.28.0", fail_at=fail_at)
                authority = empty_authority(m, version="0.27.0" if fail_at == 0 else "0.28.0")
                with patch.object(m, "target", return_value=authority), self.assertRaises(m.Refusal):
                    m.transaction(root, NEW, commands, "0.28.0")
                self.assertEqual(m.snapshot(root), before)
                if fail_at == 0:
                    self.assertEqual(commands.calls, [])

    def test_version_migration_checks_actual_target_workspace_and_each_member_version(self) -> None:
        m = self.writer
        docs = {"Cargo.toml": {"workspace": {"package": {"version": "0.28.0"},
                "members": ["crates/" + name for name in ROOT_NAMES]}}}
        docs.update({f"crates/{name}/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}} for name in ROOT_NAMES})

        class FakeAuthority:
            def __init__(self, commands, directory, revision):
                self.revision = revision
            def read(self, relative):
                return docs[relative]
            def read_optional(self, relative):
                return docs.get(relative)

        state = m.Current(OLD, "0.27.0", TY)
        with patch.object(m, "Authority", FakeAuthority):
            with self.assertRaises(m.Refusal):
                m.target(None, Path("/unused"), state, NEW)
            target = m.target(None, Path("/unused"), state, NEW, "0.28.0")
            self.assertEqual(target.version, "0.28.0")
            for name in ROOT_NAMES:
                docs[f"crates/{name}/Cargo.toml"]["package"]["version"] = "0.27.0"
                with self.subTest(package=name), self.assertRaises(m.Refusal):
                    m.target(None, Path("/unused"), state, NEW, "0.28.0")
                docs[f"crates/{name}/Cargo.toml"]["package"]["version"] = {"workspace": True}

    def test_immutable_target_binds_exact_actual_ay_sys_macos_dependency(self) -> None:
        from test_ay_exec_policy_owner import manifest as policy_manifest
        import copy
        m = self.writer
        docs = {"Cargo.toml": {"workspace": {"package": {"version": "0.28.0"},
                "members": ["crates/" + name for name in ROOT_NAMES],
                "exclude": ["vendor/trust-exec-policy"]}}}
        docs.update({f"crates/{name}/Cargo.toml": {
            "package": {"name": name, "version": {"workspace": True}}} for name in ROOT_NAMES})
        docs["vendor/trust-exec-policy/Cargo.toml"] = policy_manifest()
        key = 'cfg(target_os = "macos")'
        route = {key: {"dependencies": {
            "trust-exec-policy": {"path": "../../vendor/trust-exec-policy"}}}}
        docs["crates/ay-sys/Cargo.toml"]["target"] = route

        class FakeAuthority:
            def __init__(self, commands, directory, revision):
                self.revision = revision
            def read(self, relative):
                return docs[relative]
            def read_optional(self, relative):
                return docs.get(relative)

        state = m.Current(OLD, "0.27.0", TY)
        with patch.object(m, "Authority", FakeAuthority):
            target = m.target(None, Path("/unused"), state, NEW, "0.28.0")
            self.assertTrue(target.exec_policy)
            self.assertIn("trust-exec-policy", target.required["ay-sys"])
            for condition in ('cfg(target_os = "linux")', 'cfg(unix)'):
                docs["crates/ay-sys/Cargo.toml"]["target"] = {condition: copy.deepcopy(route[key])}
                with self.subTest(condition=condition), self.assertRaises(m.Refusal):
                    m.target(None, Path("/unused"), state, NEW, "0.28.0")
            docs["crates/ay-sys/Cargo.toml"]["target"] = copy.deepcopy(route)
            docs["crates/ay-sys/Cargo.toml"]["target"][key]["dependencies"]["trust-exec-policy"]["optional"] = True
            with self.assertRaises(m.Refusal):
                m.target(None, Path("/unused"), state, NEW, "0.28.0")
            docs["crates/ay-sys/Cargo.toml"]["target"] = {}
            docs["crates/ay-sys/Cargo.toml"]["dependencies"] = copy.deepcopy(route[key]["dependencies"])
            with self.assertRaises(m.Refusal):
                m.target(None, Path("/unused"), state, NEW, "0.28.0")
            docs["crates/ay-sys/Cargo.toml"].pop("dependencies")
            docs["crates/ay-core/Cargo.toml"]["target"] = copy.deepcopy(route)
            with self.assertRaises(m.Refusal):
                m.target(None, Path("/unused"), state, NEW, "0.28.0")
            docs["crates/ay-core/Cargo.toml"].pop("target")
            docs["crates/ay-sys/Cargo.toml"]["target"] = {
                key: {"dependencies": {"renamed": {"package": "trust-exec-policy",
                         "path": "../../vendor/trust-exec-policy"}}}}
            with self.assertRaises(m.Refusal):
                m.target(None, Path("/unused"), state, NEW, "0.28.0")

    def test_actual_exec_policy_owner_preserves_all_other_nodes_and_effective_metadata(self) -> None:
        from dataclasses import replace
        m = self.writer
        old, new = fixture(), fixture(NEW, version="0.28.0")
        libc = ('\n[[package]]\nname = "libc"\nversion = "0.2.177"\n'
                f'source = "{m.REGISTRY}"\nchecksum = "{"b" * 64}"\n').encode()
        vendor = ('\n[[package]]\nname = "trust-exec-policy"\nversion = "0.13.0"\n'
                  f'source = "{source(NEW)}"\ndependencies = ["libc"]\n').encode()
        for lock in LOCKS:
            old[lock] += libc
            new[lock] = new[lock].replace(b'name = "ay-sys"\n',
                b'name = "ay-sys"\ndependencies = ["trust-exec-policy"]\n') + libc + vendor
        authority = replace(empty_authority(m, version="0.28.0"), exec_policy=True)
        authority.required["ay-sys"].add("trust-exec-policy")
        authority.declarations["ay-sys"]["trust-exec-policy"] = [
            {"git": AY_URL, "rev": NEW, "version": "0.13.0"}]
        state = m.Current(OLD, "0.27.0", TY)
        for lock in LOCKS:
            m.validate_graph(old[lock], new[lock], lock, state, NEW, authority)
            rows = m.packages(new[lock], lock)
            m.validate_metadata(json.dumps({"packages": rows}), new[lock], lock, NEW)
        with tempfile.TemporaryDirectory(prefix="clean-exec-source-owner-") as temporary:
            root = Path(temporary).resolve()
            write_fixture(root, new)
            self.assertEqual(m.current(root, m.snapshot(root)), m.Current(NEW, "0.28.0", TY))
        with self.assertRaises(m.Refusal):
            m.validate_graph(old["Cargo.lock"], new["Cargo.lock"], "Cargo.lock", state, NEW,
                             replace(authority, exec_policy=False))
        with self.assertRaises(m.Refusal):
            m.validate_graph(old["Cargo.lock"], new["Cargo.lock"].replace(
                b'libc"\nversion = "0.2.177"', b'libc"\nversion = "0.2.178"'),
                "Cargo.lock", state, NEW, authority)
        missing = [row for row in m.packages(new["Cargo.lock"], "Cargo.lock")
                   if row["name"] != "trust-exec-policy"]
        with self.assertRaises(m.Refusal):
            m.validate_metadata(json.dumps({"packages": missing}), new["Cargo.lock"], "Cargo.lock", NEW)

    def test_resolver_owned_mode_and_protected_source_drift_refuse_then_restore_owned(self) -> None:
        m = self.writer
        for kind in ("owned mode", "protected source"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory(prefix="clean-ay-drift-") as temporary:
                root = Path(temporary).resolve()
                self.transaction_fixture(root)
                before = m.snapshot(root)
                def mutate(commands, lock):
                    if len(commands.calls) == 3:
                        if kind == "owned mode":
                            lock.chmod(0o755)
                        else:
                            (root / m.GUARDS[0]).write_bytes(b"# external drift\n")
                commands = FakeCommands(m, root, NEW, mutate=mutate)
                with patch.object(m, "target", return_value=empty_authority(m)):
                    with self.assertRaises(m.Refusal):
                        m.transaction(root, NEW, commands)
                self.assertEqual(m.snapshot(root), before)
                if kind == "protected source":
                    # The transaction owns only six files; detection must not
                    # silently claim it restored arbitrary external writers.
                    self.assertEqual((root / m.GUARDS[0]).read_bytes(), b"# external drift\n")


if __name__ == "__main__":
    unittest.main(verbosity=2)
