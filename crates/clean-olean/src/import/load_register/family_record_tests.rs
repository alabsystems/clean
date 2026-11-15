// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Imported inductive-family records through the production loader, on a
//! module the pinned Lean compiled (`tests/fixtures/lean/<pin>/family_records`).
//!
//! The forged arms edit ONE field of the parsed module in memory — exactly what
//! a crafted `.olean` would carry past the byte parser — and then run the real
//! registration (`load_module_direct_with_cache_and_policy`).
use super::super::load_parse::LoadRecursorValData;
use super::*;
use crate::test_support::compiled_fixture_dir;
use std::sync::OnceLock;

fn fixture() -> LoadModule {
    static BYTES: OnceLock<Vec<u8>> = OnceLock::new();
    let bytes = BYTES.get_or_init(|| {
        let olean = compiled_fixture_dir("family_records").join("FamilyRecords.olean");
        std::fs::read(&olean).expect("pinned-Lean compiled FamilyRecords.olean")
    });
    super::super::load_parse::parse_load_module(bytes.clone())
        .expect("pinned-Lean FamilyRecords module")
}

/// Load into a bare environment — the one `clean olean verify-batch` imports
/// Init into — and return it with every family-record refusal.
fn load(module: &LoadModule) -> (Environment, Vec<(String, String)>) {
    let mut env = Environment::new();
    let summary = load_module_direct_with_cache_and_policy(
        &mut env,
        module,
        Some("FamilyRecords".into()),
        &mut ExprInternCache::with_capacity(128),
        OleanImportPolicy::default(),
    )
    .expect("direct load of the pinned-Lean fixture");
    let refused = summary
        .skipped_constants
        .into_iter()
        .filter(|s| s.reason.contains("imported family record"))
        .map(|s| (s.name, s.reason))
        .collect();
    (env, refused)
}

fn recursor<'a>(module: &'a mut LoadModule, name: &str) -> &'a mut LoadRecursorValData {
    module
        .constants
        .iter_mut()
        .find(|c| c.name == name)
        .and_then(|c| c.recursor_val.as_mut())
        .unwrap_or_else(|| panic!("{name} is a recursor of the fixture"))
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_family_records_every_lean_recursor_is_regenerated_and_admitted() {
    let (env, refused) = load(&fixture());
    assert!(
        refused.is_empty(),
        "no Lean-written record may be refused: {refused:?}"
    );
    for rec in [
        "Eq.rec", "HEq.rec", "B.rec", "S.rec", "P.rec", "Pair.rec", "Ev.rec", "Od.rec", "L.rec",
        // The nested family, re-admitted through the kernel's nested pipeline.
        "T.rec", "T.rec_1",
    ] {
        assert!(env.get_recursor(&n(rec)).is_some(), "{rec} must import");
    }
    // Lean's kernel wrote k := true for Eq.rec and k := false for S.rec; both
    // equal the regenerated entries, so both stand.
    assert!(env.get_recursor(&n("Eq.rec")).is_some_and(|r| r.is_k));
    assert!(env.get_recursor(&n("S.rec")).is_some_and(|r| !r.is_k));
    // The quotient primitives are the kernel's; the file's records were dropped.
    for quot in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] {
        assert!(
            env.get_quot(&n(quot)).is_some(),
            "{quot} must be kernel-built"
        );
    }
}

/// A forged record on the NESTED family is refused like any other: its
/// regeneration runs the kernel's own nested pipeline and compares.
#[test]
fn test_family_records_forged_nested_auxiliary_recursor_is_refused() {
    let mut module = fixture();
    recursor(&mut module, "T.rec_1").num_minors += 1;
    let (env, refused) = load(&module);
    assert!(
        refused
            .iter()
            .any(|(name, reason)| name == "T.rec_1" && reason.contains("num_minors")),
        "{refused:?}"
    );
    assert!(env.get_recursor(&n("T.rec_1")).is_none());
}

#[test]
fn test_family_records_forged_k_flag_is_refused() {
    let mut module = fixture();
    recursor(&mut module, "S.rec").k = true;
    let (env, refused) = load(&module);
    assert!(
        refused
            .iter()
            .any(|(name, reason)| name == "S.rec" && reason.contains("K-like flag")),
        "{refused:?}"
    );
    assert!(env.get_recursor(&n("S.rec")).is_none());
    assert!(
        env.get_recursor(&n("B.rec")).is_some(),
        "only the forged record is refused"
    );
}

#[test]
fn test_family_records_forged_iota_rule_is_refused() {
    let mut module = fixture();
    let rules = &mut recursor(&mut module, "B.rec").rules;
    let first = rules[0].rhs_ptr;
    rules[0].rhs_ptr = rules[1].rhs_ptr;
    rules[1].rhs_ptr = first;
    let (env, refused) = load(&module);
    assert!(
        refused
            .iter()
            .any(|(name, reason)| name == "B.rec" && reason.contains("iota right-hand side")),
        "{refused:?}"
    );
    assert!(env.get_recursor(&n("B.rec")).is_none());
}
