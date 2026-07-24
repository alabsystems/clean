// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-olean `Lean.Meta.instanceExtension` decode + restore
//! (#olean-env-ext-restore, increment 1).
//!
//! Before the typed decoder, every `instanceExtension` entry in a real Lean
//! `.olean` was silently dropped at parse (its `ScopedEnvExtension.Entry
//! InstanceEntry` layout does not match the generic `(Name × DataValue)` pair
//! heuristic), and the instance table was rebuilt by a shape heuristic that
//! fabricates `DEFAULT_INSTANCE_PRIORITY` (100) and drops some genuine
//! `@[instance]`s outright (e.g. the monad-lifting transitivity instances).
//! These tests pin the restored behavior against the pinned v4.30.0-rc2
//! toolchain oleans and skip (with a message) when that toolchain is absent —
//! the decode is layout-validated, so a different toolchain would degrade to
//! counted `undecoded_entries`, not wrong data.
//!
//! Ground truth: `Lean/Meta/Instances.lean:46-97` (`InstanceEntry`,
//! `instanceExtension`), `Lean/ScopedEnvExtension.lean:17-19` (entry wrapper),
//! audited in `docs/plans/OLEAN_ENV_EXT_AUDIT_2026-07-09.md`.

use super::{load_module_with_deps, parse_module};
use crate::module::{
    ParsedAttrKind, ParsedExtensionEntry, ParsedInstanceEntry, LEAN_INSTANCE_EXTENSION,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use std::path::PathBuf;

/// Lean 4's default instance priority (`Lean/Meta/Instances.lean`); Clean's
/// fabricated heuristic priority is `DEFAULT_INSTANCE_PRIORITY = 100`, so any
/// imported instance carrying 1000 (or Lean's explicit 500 on
/// `instBEqOfDecidableEq`) proves the decoded entry — not the heuristic —
/// populated the registry.
const LEAN_DEFAULT_PRIORITY: u32 = 1000;

/// The pinned toolchain whose `InstanceEntry` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

/// Locate the pinned v4.30.0-rc2 stdlib, or `None` to skip.
fn v4_30_lib_path() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let lib = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(PINNED_TOOLCHAIN)
        .join("lib/lean");
    lib.exists().then_some(lib)
}

/// Decoded instance entries of `Init/Prelude.olean`, or `None` to skip.
fn decode_prelude_instance_entries() -> Option<(Vec<ParsedInstanceEntry>, usize)> {
    let lib = v4_30_lib_path()?;
    let bytes = std::fs::read(lib.join("Init/Prelude.olean")).ok()?;
    let module = parse_module(&bytes).expect("Init/Prelude.olean should parse");
    let ext = module
        .entries
        .iter()
        .find(|ext| ext.extension_name == LEAN_INSTANCE_EXTENSION)
        .expect("Init.Prelude should carry a Lean.Meta.instanceExtension entry array");
    let decoded = ext
        .entries
        .iter()
        .map(|entry| match entry {
            ParsedExtensionEntry::Instance(inst) => inst.clone(),
            other => {
                panic!("instanceExtension should decode every entry as Instance, got {other:?}")
            }
        })
        .collect();
    Some((decoded, ext.undecoded_entries))
}

#[test]
fn test_instance_ext_decoder_prelude_entries_fully_decoded() {
    let Some((decoded, undecoded)) = decode_prelude_instance_entries() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    // v4.30.0-rc2 Init.Prelude persists 151 @[instance] registrations; stay
    // tolerant to patch-level drift but insist on full decode (loud contract:
    // an undecodable entry must be counted, and for the pinned layout there
    // must be none).
    assert!(
        decoded.len() >= 100,
        "expected >= 100 decoded instance entries in Init.Prelude, got {}",
        decoded.len()
    );
    assert_eq!(
        undecoded, 0,
        "the pinned v4.30 InstanceEntry layout should decode every entry"
    );

    let inst_hadd = decoded
        .iter()
        .find(|inst| inst.instance_name == "instHAdd")
        .expect("instHAdd should be a persisted @[instance] in Init.Prelude");
    assert_eq!(
        inst_hadd.priority,
        u64::from(LEAN_DEFAULT_PRIORITY),
        "instHAdd carries Lean's default priority"
    );
    assert_eq!(inst_hadd.attr_kind, ParsedAttrKind::Global);
    assert_eq!(inst_hadd.scope_ns, None);

    // `instance (priority := 500) instBEqOfDecidableEq` — a NON-default
    // priority that only the real entry can supply.
    let beq_of_dec = decoded
        .iter()
        .find(|inst| inst.instance_name == "instBEqOfDecidableEq")
        .expect("instBEqOfDecidableEq should be a persisted @[instance]");
    assert_eq!(
        beq_of_dec.priority, 500,
        "instBEqOfDecidableEq's explicit (priority := 500) must be decoded"
    );
}

#[test]
fn test_imported_instances_registered_with_real_priorities() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    let summaries = load_module_with_deps(&mut env, "Init.Prelude", &[lib])
        .expect("Init.Prelude should import");
    for summary in &summaries {
        assert_eq!(
            summary.extension_undecoded_entries, 0,
            "module {:?} should decode all typed extension entries",
            summary.module_name
        );
    }

    // The restored state is what `clean_elab::infer::init_instances_from_env`
    // snapshots into the elaborator's InstanceTable: `get_class_instances`
    // order and priorities directly drive `resolve_instance::candidate_order`.
    let beq = env.get_class_instances(&Name::interned("BEq"));
    let name_inst_beq = beq
        .iter()
        .find(|i| i.name == Name::interned("Lean.Name.instBEq"))
        .expect("Lean.Name.instBEq should be registered for class BEq");
    assert_eq!(
        name_inst_beq.priority, LEAN_DEFAULT_PRIORITY,
        "real entries carry Lean's default priority 1000, not the fabricated 100"
    );
    let beq_of_dec = beq
        .iter()
        .find(|i| i.name == Name::interned("instBEqOfDecidableEq"))
        .expect("instBEqOfDecidableEq should be registered for class BEq");
    assert_eq!(
        beq_of_dec.priority, 500,
        "explicit (priority := 500) must survive into the kernel registry"
    );
    // Priority-first ordering (what resolve_instance consumes): the specific
    // BEq instance outranks the DecidableEq-derived fallback, as in Lean.
    let pos_specific = beq
        .iter()
        .position(|i| i.name == Name::interned("Lean.Name.instBEq"))
        .expect("position exists");
    let pos_fallback = beq
        .iter()
        .position(|i| i.name == Name::interned("instBEqOfDecidableEq"))
        .expect("position exists");
    assert!(
        pos_specific < pos_fallback,
        "priority 1000 instance must rank before the priority 500 fallback"
    );

    let hadd = env.get_class_instances(&Name::interned("HAdd"));
    let inst_hadd = hadd
        .iter()
        .find(|i| i.name == Name::interned("instHAdd"))
        .expect("instHAdd should be registered for class HAdd");
    assert_eq!(inst_hadd.priority, LEAN_DEFAULT_PRIORITY);
}

#[test]
fn test_heuristic_dropped_real_instances_are_restored() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // The monad-lifting transitivity instances are genuine Init.Prelude
    // `@[instance]`s that the shape heuristic
    // (`valid_instance_class`) drops — before the typed decoder they were
    // entirely ABSENT from the table, so `monadLift`-style resolution over the
    // imported environment was structurally broken. The decoded entries must
    // restore them, attached to their real classes.
    for (instance, class) in [
        ("instMonadLiftTOfMonadLift", "MonadLiftT"),
        ("instMonadFunctorTOfMonadFunctor", "MonadFunctorT"),
    ] {
        let instance = Name::interned(instance);
        let class = Name::interned(class);
        assert!(
            env.is_instance(&instance),
            "{instance} is a persisted @[instance] and must be restored"
        );
        assert!(env.is_class(&class), "{class} must be registered");
        assert!(
            env.get_class_instances(&class)
                .iter()
                .any(|i| i.name == instance),
            "{instance} must be attached to class {class}"
        );
    }
}

#[test]
fn test_instance_ext_synth_order_decoded_and_registered() {
    let Some((decoded, undecoded)) = decode_prelude_instance_entries() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    assert_eq!(undecoded, 0, "synthOrder decode must not degrade any entry");

    // Ground truth, verified against the v4.30.0-rc2 Init.Prelude olean
    // (`InstanceEntry.synthOrder`, `Lean/Meta/Instances.lean:46-60`; binder
    // indices into the instance type's Pi telescope):
    // - `instMonadLiftTOfMonadLift : (m n o) → [MonadLift n o] →
    //   [MonadLiftT m n] → MonadLiftT m o` → [3, 4]: the `[MonadLift n o]`
    //   sub-goal (binder 3) is synthesized FIRST because `MonadLift`'s first
    //   param is a `semiOutParam` (`Init/Prelude.lean:3890`), so solving it
    //   pins the middle monad `n` consumed by binder 4;
    // - `instHAdd : {α} → [Add α] → HAdd α α α` → [1];
    // - `instAddNat : Add Nat` (no [inst] binders) → [].
    for (name, expected) in [
        ("instMonadLiftTOfMonadLift", &[3u64, 4][..]),
        ("instMonadEvalTOfMonadEval", &[3, 4][..]),
        ("instHAdd", &[1][..]),
        ("instAddNat", &[][..]),
        ("instDecidableAnd", &[2, 3][..]),
    ] {
        let entry = decoded
            .iter()
            .find(|inst| inst.instance_name == name)
            .unwrap_or_else(|| panic!("{name} should be a persisted @[instance]"));
        assert_eq!(
            entry.synth_order, expected,
            "{name}: decoded synthOrder must match Lean's persisted value"
        );
    }
}

#[test]
fn test_imported_synth_order_registered_in_environment() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // The bridge must register the decoded synthOrder alongside the instance
    // (the elaborator's InstanceTable snapshot reads it via
    // `get_instance_synth_order` and schedules sub-goals with it).
    assert_eq!(
        env.get_instance_synth_order(&Name::interned("instMonadLiftTOfMonadLift")),
        Some(&[3usize, 4][..]),
        "instMonadLiftTOfMonadLift must carry decoded synthOrder [3, 4]"
    );
    assert_eq!(
        env.get_instance_synth_order(&Name::interned("instHAdd")),
        Some(&[1usize][..]),
        "instHAdd must carry decoded synthOrder [1]"
    );
    // Hand-registered instances (no persisted entry) have no stored order —
    // the resolver computes the Lean-style default for those.
    assert_eq!(
        env.get_instance_synth_order(&Name::interned("instAddNat_not_registered_here")),
        None
    );
}
