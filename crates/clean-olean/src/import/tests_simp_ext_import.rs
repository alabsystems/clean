// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-olean `Lean.Meta.simpExtension` decode + restore (RC-B / T10).
//!
//! Before the typed decoder, every `simpExtension` entry in a real Lean
//! `.olean` was silently dropped at parse: a `ScopedEnvExtension.Entry
//! SimpEntry` element has ONE object field (`Entry.global`), so the generic
//! `(Name × DataValue)` pair heuristic's `header.other < 2` bail rejected it —
//! and bare `simp` under real imports saw only the hand-written builtin rules
//! (~0.4% of upstream's `@[simp]` set). These tests pin the restored behavior
//! against the pinned v4.30.0-rc2 toolchain oleans and skip (with a message)
//! when that toolchain is absent — the decode is layout-validated, so a
//! different toolchain would degrade to counted `undecoded_entries`, not
//! wrong data.
//!
//! Ground truth: `Lean/Meta/Tactic/Simp/SimpTheorems.lean:143-165`
//! (`SimpTheorem`), `:449-453` (`SimpEntry`), `:57-79` (`Origin`),
//! `Lean/ScopedEnvExtension.lean:17-19` (entry wrapper), byte-level verified
//! against the pinned toolchain's `Init/SimpLemmas.olean` / `Init/Prelude.olean`.

use super::{load_module_with_deps, parse_module};
use crate::module::{
    ParsedExtensionEntry, ParsedSimpEntry, ParsedSimpEntryKind, LEAN_SIMP_EXTENSION,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

/// The pinned toolchain whose `SimpTheorem` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

/// Locate the pinned v4.30.0-rc2 stdlib, or `None` to skip.
fn v4_30_lib_path() -> Option<std::path::PathBuf> {
    crate::pinned_lean_lib_path()
}

/// Decoded simp entries of `module` (path relative to the stdlib root), or
/// `None` to skip.
fn decode_simp_entries(module: &str) -> Option<(Vec<ParsedSimpEntry>, usize)> {
    let lib = v4_30_lib_path()?;
    let bytes = std::fs::read(lib.join(module)).ok()?;
    let parsed = parse_module(&bytes).unwrap_or_else(|e| panic!("{module} should parse: {e}"));
    let ext = parsed
        .entries
        .iter()
        .find(|ext| ext.extension_name == LEAN_SIMP_EXTENSION)
        .unwrap_or_else(|| panic!("{module} should carry a Lean.Meta.simpExtension entry array"));
    let decoded = ext
        .entries
        .iter()
        .map(|entry| match entry {
            ParsedExtensionEntry::Simp(simp) => simp.clone(),
            other => {
                panic!("simpExtension should decode every entry as Simp, got {other:?}")
            }
        })
        .collect();
    Some((decoded, ext.undecoded_entries))
}

/// TEETH: the decoded entry count must be NONZERO. If the pre-decoder
/// `header.other < 2` bail is ever re-asserted (the generic pair heuristic
/// rejecting one-field `ScopedEnvExtension.Entry` constructors), every entry
/// is dropped again and this collapses to zero — the regression this brick
/// exists to prevent must fail loudly, not silently.
#[test]
fn test_simp_ext_decoded_count_nonzero_teeth() {
    let Some((decoded, undecoded)) = decode_simp_entries("Init/SimpLemmas.olean") else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    assert!(
        !decoded.is_empty(),
        "the typed simpExtension decoder decoded ZERO entries — the old \
         one-field-constructor bail (extensions.rs `header.other < 2`) is back"
    );
    assert_eq!(
        undecoded, 0,
        "the pinned v4.30 SimpTheorem layout should decode every entry"
    );
}

#[test]
fn test_simp_ext_decoder_simp_lemmas_entries_fully_decoded() {
    let Some((decoded, undecoded)) = decode_simp_entries("Init/SimpLemmas.olean") else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    // v4.30.0-rc2 Init.SimpLemmas persists 81 @[simp] registrations; stay
    // tolerant to patch-level drift but insist on full decode (loud contract:
    // an undecodable entry must be counted, and for the pinned layout there
    // must be none).
    assert!(
        decoded.len() >= 50,
        "expected >= 50 decoded simp entries in Init.SimpLemmas, got {}",
        decoded.len()
    );
    assert_eq!(undecoded, 0, "no entry may be silently degraded");

    let ne_eq = decoded
        .iter()
        .find(|simp| simp.lemma_name == "ne_eq")
        .expect("ne_eq should be a persisted @[simp] theorem in Init.SimpLemmas");
    assert_eq!(ne_eq.kind, ParsedSimpEntryKind::Theorem);
    assert_eq!(
        ne_eq.priority, 1000,
        "ne_eq carries Lean's default simp priority"
    );
    assert!(ne_eq.post, "ne_eq is a post-order (default) simp lemma");
    assert_eq!(ne_eq.scope_ns, None, "ne_eq is a global registration");

    let eq_self = decoded
        .iter()
        .find(|simp| simp.lemma_name == "eq_self")
        .expect("eq_self should be a persisted @[simp] theorem in Init.SimpLemmas");
    assert_eq!(eq_self.kind, ParsedSimpEntryKind::Theorem);
    assert_eq!(eq_self.priority, 1000);
}

#[test]
fn test_simp_ext_decoder_prelude_thm_and_unfold_entries() {
    let Some((decoded, undecoded)) = decode_simp_entries("Init/Prelude.olean") else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    assert_eq!(
        undecoded, 0,
        "Init.Prelude's simpExtension entries should decode fully"
    );

    // `@[simp] theorem id_eq` ⟶ `SimpEntry.thm` with origin `.decl id_eq`.
    let id_eq = decoded
        .iter()
        .find(|simp| simp.lemma_name == "id_eq")
        .expect("id_eq should be a persisted @[simp] theorem in Init.Prelude");
    assert_eq!(id_eq.kind, ParsedSimpEntryKind::Theorem);
    assert_eq!(id_eq.priority, 1000);

    // `@[simp] abbrev Eq.ndrec` — a reducible definition — is persisted as
    // `SimpEntry.toUnfold`, not a theorem.
    let ndrec = decoded
        .iter()
        .find(|simp| simp.lemma_name == "Eq.ndrec")
        .expect("Eq.ndrec should be a persisted @[simp] toUnfold in Init.Prelude");
    assert_eq!(ndrec.kind, ParsedSimpEntryKind::ToUnfold);
}

#[test]
fn test_imported_simp_lemmas_registered_in_kernel_registry() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    let summaries = load_module_with_deps(&mut env, "Init.SimpLemmas", &[lib])
        .expect("Init.SimpLemmas should import");

    // The restore is loud: for Init.SimpLemmas itself, every decoded origin
    // names a theorem of that very module, so nothing may count as
    // undecoded/unresolved.
    let own = summaries
        .iter()
        .find(|s| matches!(&s.module_name, Some(n) if n.ends_with("Init.SimpLemmas")))
        .expect("the root module should produce a summary");
    assert_eq!(
        own.extension_undecoded_entries, 0,
        "every Init.SimpLemmas simp origin should decode AND resolve"
    );

    // The registry the simp tactic reads (`collect_registry_lemmas`) must now
    // contain the imported registrations with their real priorities.
    for lemma in ["ne_eq", "eq_self", "ite_true", "and_true", "id_eq"] {
        let name = Name::interned(lemma);
        assert!(
            env.is_simp_lemma(&name),
            "{lemma} must be registered as a simp lemma after import"
        );
        let info = env.get_simp_lemma(&name).expect("registered above");
        assert_eq!(
            info.priority.value(),
            1000,
            "{lemma} must carry Lean's default priority 1000"
        );
    }

    // Registry floor: Init.SimpLemmas alone persists 81 entries and its
    // import closure (Init.Core, Init.Prelude, …) adds more; a collapse back
    // toward the pre-decoder zero must fail loudly.
    let registered = env.get_simp_lemmas().count();
    assert!(
        registered >= 80,
        "expected >= 80 registered simp lemmas after import Init.SimpLemmas, got {registered}"
    );
}
