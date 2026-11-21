// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Compare the native Level eliminators with the original pinned Lean artifact.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantInfo, Environment, Reducibility};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{ConstantKind, Declaration, Name, ReferenceKernel};
use clean_olean::meaning_digest::{MeaningDigests, Package};
use clean_olean::{
    load_module_with_deps, pinned_lean_binary, read_artifact, reference_base_closed,
    require_pinned_lean_lib_path, ArtifactDepth, ClosedRecheckOptions,
};

const MODULE: &str = "CICL.Level";
const SOURCE: &str = include_str!("../../../theories/cic_l/CICL/Level.lean");
const PINS: &str = include_str!("cic_l_level/definition_pins.json");

fn compile_original(path: &Path, lib: &Path) {
    let lean = pinned_lean_binary().expect("repository-pinned Lean");
    fs::create_dir(path.join("CICL")).expect("temporary source directory");
    fs::write(path.join("CICL/Level.lean"), SOURCE).expect("original Level source");
    let output = Command::new(lean)
        .current_dir(path)
        .env_remove("LEAN_SRC_PATH")
        .env("LEAN_PATH", lib)
        .args(["-o", "CICL/Level.olean", "CICL/Level.lean"])
        .output()
        .expect("compile original Level source");
    assert!(
        output.status.success(),
        "pinned Lean refused original Level: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn original_family(pinned: &Environment) -> InductiveDecl {
    let family = pinned
        .get_inductive(&Name::from_string(MODULE))
        .expect("original Level family");
    InductiveDecl {
        level_params: family.level_params.clone(),
        num_params: family.num_params,
        types: vec![InductiveType {
            name: family.name.clone(),
            type_: family.type_.clone(),
            constructors: family
                .constructor_names
                .iter()
                .map(|name| Constructor {
                    name: name.clone(),
                    type_: pinned
                        .get_constructor(name)
                        .expect("original Level constructor")
                        .type_
                        .clone(),
                })
                .collect(),
        }],
    }
}

fn fenced_family(native: &Environment, family: InductiveDecl) -> ReferenceKernel {
    let roots = BTreeSet::from([Name::from_string("Nat")]);
    let mut kernel = reference_base_closed(native, &roots, &ClosedRecheckOptions::default())
        .expect("plan the original Nat cone")
        .into_kernel()
        .expect("check the original Nat cone");
    kernel
        .add_inductive_checked(family)
        .expect("regenerate the core Level family in the reference theory");
    kernel
}

fn replay_wrapper(kernel: &mut ReferenceKernel, wrapper: &ConstantInfo, hint: Reducibility) {
    kernel
        .add_checked_with_reducibility(
            Declaration::Definition {
                name: wrapper.name.clone(),
                level_params: wrapper.level_params.clone(),
                type_: wrapper.type_.clone(),
                value: wrapper.value.clone().expect("original native wrapper body"),
                is_reducible: hint == Reducibility::Reducible,
            },
            hint,
        )
        .expect("fenced check of the original native wrapper body");
    assert!(kernel.environment().get_recursor(&wrapper.name).is_none());
}

#[test]
fn level_wrapper_hints_match_the_exact_pinned_closure() {
    let lib = require_pinned_lean_lib_path().expect("repository-pinned Lean library");
    let staging = tempfile::tempdir().expect("isolated Level artifact directory");
    let path = staging.path();
    compile_original(path, &lib);
    let artifact = read_artifact(MODULE, &path.join("CICL/Level.olean"), ArtifactDepth::Names)
        .expect("original stored Level inventory");
    let package = Package::of_module_names([(MODULE.to_owned(), artifact.names)]);
    let pins: serde_json::Value = serde_json::from_str(PINS).expect("committed Level pins");

    let mut pinned = Environment::for_lean_replay();
    load_module_with_deps(&mut pinned, MODULE, &[path.to_path_buf(), lib.clone()])
        .expect("load original Level artifact");
    let mut native = Environment::for_lean_replay();
    load_module_with_deps(&mut native, "Init.Data.Nat.MinMax", &[lib])
        .expect("load the original Level prelude");
    let family = original_family(&pinned);
    native
        .add_inductive(family.clone())
        .expect("generate native Level eliminators from the checked family");
    // The ordinary source world caches wrapper iota rules. The reference
    // world rechecks the actual wrapper values as ordinary definitions.
    let mut checked = fenced_family(&native, family.clone());
    let mut regular = fenced_family(&native, family);
    let pinned_digests = MeaningDigests::new(&pinned, &package);

    for suffix in ["casesOn", "recOn"] {
        let name = Name::from_string(MODULE).str(suffix);
        let expected = pinned.get_const(&name).expect("pinned wrapper");
        let actual = native.get_const(&name).expect("native wrapper");
        assert_eq!(actual.kind, ConstantKind::Definition, "{name}");
        assert_eq!(actual.kind, expected.kind, "{name}");
        assert_eq!(actual.level_params, expected.level_params, "{name}");
        assert_eq!(actual.type_, expected.type_, "{name}");
        assert_eq!(actual.value, expected.value, "{name}");
        assert!(actual.is_reducible && expected.is_reducible, "{name}");
        assert_eq!(actual.reducibility, Reducibility::Reducible, "{name}");
        assert_eq!(actual.reducibility, expected.reducibility, "{name}");
        assert!(native.get_recursor(&name).is_some());

        replay_wrapper(&mut checked, actual, actual.reducibility);
        replay_wrapper(&mut regular, actual, Reducibility::Regular(0));
        let checked_digests = MeaningDigests::new(checked.environment(), &package);
        let expected_digest = pins[name.to_string()]["meaning_sha256"]
            .as_str()
            .expect("committed wrapper digest");
        assert_eq!(
            pinned_digests.closure(&name),
            checked_digests.closure(&name)
        );
        assert_eq!(
            pinned_digests.digest(&name).expect("pinned wrapper digest"),
            expected_digest
        );
        assert_eq!(
            checked_digests
                .digest(&name)
                .expect("checked native wrapper digest"),
            expected_digest
        );

        let changed = regular
            .environment()
            .get_const(&name)
            .expect("mutated wrapper record");
        assert_eq!(changed.type_, expected.type_, "{name}");
        assert_eq!(changed.value, expected.value, "{name}");
        assert_eq!(changed.reducibility, Reducibility::Regular(0), "{name}");
        let changed_digests = MeaningDigests::new(regular.environment(), &package);
        assert_eq!(
            changed_digests.closure(&name),
            pinned_digests.closure(&name)
        );
        let changed_digest = changed_digests
            .digest(&name)
            .expect("changed wrapper digest");
        assert_ne!(changed_digest, expected_digest, "{name}");
        eprintln!(
            "{name} exact pinned closure {expected_digest}; regular hint refused {changed_digest}"
        );
    }
}
