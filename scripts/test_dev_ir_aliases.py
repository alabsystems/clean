#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
import copy
import unittest

import dev_ir_aliases as policy

A, B, C = "a" * 40, "b" * 40, "c" * 40


def source(rev):
    return f"git+{policy.IR_URL}?rev={rev}#{rev}"


def fixture():
    manifests = {
        "Cargo.toml": f'''[workspace]
members = ["app"]
[workspace.metadata.clean]
dev-only-ir-aliases = ["witness"]
[workspace.dependencies]
witness = {{ package = "trust-ir", git = "{policy.IR_URL}", rev = "{B}" }}
''',
        "app/Cargo.toml": '''[package]
name = "app"
version = "1.0.0"
[dev-dependencies]
witness = { workspace = true }
''',
    }
    metadata = {
        "workspace_root": "/w", "workspace_members": ["app"],
        "packages": [
            {"id": "app", "name": "app", "version": "1.0.0", "source": None, "manifest_path": "/w/app/Cargo.toml"},
            {"id": "prod", "name": "trust-ir", "version": "0.14.0", "source": source(A)},
            {"id": "dev", "name": "trust-ir", "version": "0.14.0", "source": source(B)},
        ],
        "resolve": {"nodes": [
            {"id": "app", "deps": [
                {"name": "trust_ir", "pkg": "prod", "dep_kinds": [{"kind": None}]},
                {"name": "witness", "pkg": "dev", "dep_kinds": [{"kind": "dev"}]},
            ]},
            {"id": "prod", "deps": []}, {"id": "dev", "deps": []},
        ]},
    }
    lock = f'''version = 4

[[package]]
name = "trust-ir"
version = "0.14.0"
source = "{source(A)}"

[[package]]
name = "trust-ir"
version = "0.14.0"
source = "{source(B)}"
'''
    return manifests, metadata, lock


class DevIrAliasTests(unittest.TestCase):
    def test_exact_dev_package_can_be_projected(self):
        manifests, metadata, lock = fixture()
        excluded = policy.excluded_packages(manifests, metadata)
        self.assertEqual(excluded, {("trust-ir", "0.14.0", source(B))})
        projected = policy.project_lock(lock, excluded)
        self.assertIn(source(A), projected)
        self.assertNotIn(source(B), projected)
        self.assertIn(source(B), lock, "the actual lock must remain unchanged")

    def test_promoted_normal_or_build_alias_refuses_even_if_optional(self):
        for kind in ["dependencies", "build-dependencies"]:
            manifests, metadata, _ = fixture()
            manifests["app/Cargo.toml"] = manifests["app/Cargo.toml"].replace("dev-dependencies", kind).replace("workspace = true", "workspace = true, optional = true")
            with self.assertRaisesRegex(policy.DevAliasError, "workspace dev-dependency"):
                policy.excluded_packages(manifests, metadata)

    def test_target_specific_runtime_alias_refuses(self):
        manifests, metadata, _ = fixture()
        manifests["app/Cargo.toml"] += '\n[target.\'cfg(windows)\'.dependencies]\nwitness = { workspace = true }\n'
        with self.assertRaisesRegex(policy.DevAliasError, "workspace dev-dependency"):
            policy.excluded_packages(manifests, metadata)

    def test_unregistered_dev_edge_to_same_package_refuses(self):
        manifests, metadata, _ = fixture()
        metadata["resolve"]["nodes"][0]["deps"].append({"name": "sneaked", "pkg": "dev", "dep_kinds": [{"kind": "dev"}]})
        with self.assertRaisesRegex(policy.DevAliasError, "undeclared dev edge"):
            policy.excluded_packages(manifests, metadata)

    def test_hidden_transitive_production_duplicate_refuses(self):
        manifests, metadata, _ = fixture()
        metadata["resolve"]["nodes"][1]["deps"].append({"name": "hidden_ir", "pkg": "dev", "dep_kinds": [{"kind": "build"}]})
        with self.assertRaisesRegex(policy.DevAliasError, "production dependency graph splits"):
            policy.excluded_packages(manifests, metadata)

    def test_resolved_alias_must_match_declared_revision(self):
        manifests, metadata, _ = fixture()
        metadata["packages"][2]["source"] = source(C)
        with self.assertRaisesRegex(policy.DevAliasError, "different package or revision"):
            policy.excluded_packages(manifests, metadata)

    def test_graph_runtime_promotion_refuses_even_if_manifest_claims_dev(self):
        manifests, metadata, _ = fixture()
        metadata["resolve"]["nodes"][0]["deps"][1]["dep_kinds"].append({"kind": "build"})
        with self.assertRaisesRegex(policy.DevAliasError, "production dependency graph splits"):
            policy.excluded_packages(manifests, metadata)

    def test_missing_declaration_and_incomplete_membership_refuse(self):
        manifests, metadata, _ = fixture()
        manifests["Cargo.toml"] = manifests["Cargo.toml"].replace('["witness"]', '[]')
        with self.assertRaisesRegex(policy.DevAliasError, "undeclared dev edge"):
            policy.excluded_packages(manifests, metadata)
        manifests, metadata, _ = fixture()
        metadata["workspace_members"].append("missing")
        with self.assertRaisesRegex(policy.DevAliasError, "workspace membership is incomplete"):
            policy.excluded_packages(manifests, metadata)

    def test_cargo_alias_collision_refuses(self):
        manifests, _, _ = fixture()
        manifests["Cargo.toml"] = manifests["Cargo.toml"].replace('["witness"]', '["a-b", "a_b"]')
        with self.assertRaisesRegex(policy.DevAliasError, "distinct Cargo crate names"):
            policy.declared_aliases(manifests)

    def test_edge_must_belong_to_declaring_member(self):
        manifests, metadata, _ = fixture()
        metadata["packages"][0]["manifest_path"] = "/w/other/Cargo.toml"
        manifests["other/Cargo.toml"] = '[package]\nname="other"\nversion="1.0.0"\n'
        with self.assertRaisesRegex(policy.DevAliasError, "not declared by"):
            policy.excluded_packages(manifests, metadata)

    def test_orphan_foreign_ir_package_refuses(self):
        manifests, metadata, _ = fixture()
        metadata["packages"].append({"id": "orphan", "name": "trust-ir-contract", "version": "0.14.0", "source": source(C)})
        metadata["resolve"]["nodes"].append({"id": "orphan", "deps": []})
        with self.assertRaisesRegex(policy.DevAliasError, "undeclared or reachable"):
            policy.excluded_packages(manifests, metadata)

    def test_missing_or_spoofed_resolved_edges_refuse(self):
        manifests, metadata, _ = fixture()
        metadata["resolve"]["nodes"][0]["deps"][1]["dep_kinds"] = []
        with self.assertRaisesRegex(policy.DevAliasError, "edge is incomplete"):
            policy.excluded_packages(manifests, metadata)

    def test_manifest_overrides_and_unused_declarations_refuse(self):
        manifests, _, _ = fixture()
        for changed in [
            manifests["app/Cargo.toml"].replace("workspace = true", 'workspace = true, path = "x"'),
            '[package]\nname="app"\nversion="1.0.0"\n',
        ]:
            trial = copy.deepcopy(manifests)
            trial["app/Cargo.toml"] = changed
            with self.assertRaises(policy.DevAliasError):
                policy.declared_aliases(trial)

    def test_no_projection_if_resolved_package_missing_from_lock(self):
        manifests, metadata, lock = fixture()
        excluded = policy.excluded_packages(manifests, metadata)
        with self.assertRaisesRegex(policy.DevAliasError, "disagree with the root lock"):
            policy.project_lock(lock.replace(source(B), source(C)), excluded)


if __name__ == "__main__":
    unittest.main()
