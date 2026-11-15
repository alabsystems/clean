// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure-instance SOURCES: `{ src with f := v }` (queue-C brick 12).
//!
//! Fixture-driven from `tests/fixtures/struct_instance/`. Every declaration in
//! every fixture was run through the pinned `lean` v4.30.0-rc2 with
//! `set_option pp.parens true` first; the fixture header records the term Lean
//! printed for each, so these are pins on Lean's answer and not on Clean's.
//!
//! The rule under test (`getStructName`, `src/Lean/Elab/StructInst.lean`):
//!
//! > If the expected type is available and it is a structure, then we use it.
//! > Otherwise, we use the type of the first source.
//!
//! Clean read the source FIRST, so `{ s with d := 7 } : Deriv` with
//! `s : Base` decided it was building a `Base` and reported
//! `Unknown structure field d on Base; nearest fields: b`.
//!
//! `mkDExplicitParent` is the control that separates this from a general
//! structure-instance failure: spelling the parent subobject out
//! (`{ toBase := s, d := 7 }`) always worked, and must keep working.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE_DIR: &str = "../../tests/fixtures/struct_instance";

fn read_fixture(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(file);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// Elaborate every declaration of a fixture against the kernel prelude and
/// return `(declaration name, verdict)` per leaf, in source order. A verdict is
/// `Ok(())` only when the declaration registered — i.e. the kernel accepted the
/// elaborated term; otherwise it is the verbatim error rendering.
fn elab_fixture(file: &str) -> Vec<(String, Result<(), String>)> {
    let src = read_fixture(file);
    let decls = parse_file(&src).unwrap_or_else(|e| panic!("{file} must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        // A structure declaration itself; not a row under test.
                        _ => {}
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), ToString::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    verdicts
}

/// Assert that each named declaration of `file` registered, reporting every
/// failure at once with its verbatim error.
fn assert_all_accepted(file: &str, expected_names: &[&str]) {
    let verdicts = elab_fixture(file);
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    for want in expected_names {
        assert!(
            names.contains(want),
            "{file}: declaration `{want}` produced no verdict; got {names:?}"
        );
    }
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, verdict)| verdict.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "{file}: {} declaration(s) rejected:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Brick 12. `{ src with f := v }` builds the EXPECTED type, taking the parent
/// subobject from `src`. Pinned to the pinned `lean`'s own output:
/// `fun s => { toBase := s, d := 7 }`.
#[test]
fn test_struct_with_source_resolves_against_expected_type() {
    assert_all_accepted(
        "with_source_expected_type.lean",
        &["mkD", "mkDExplicitParent", "bumpD", "downD"],
    );
}

/// The CONVENIENT APPROXIMATION this brick must not be mistaken for: "the
/// source and the expected type name the same structure, so just read the
/// source". `mkD`'s source is a `Base` and its expected type is a `Deriv`, so a
/// fix that keeps reading the source cannot pass — and `mkDExplicitParent`
/// in the same fixture passed all along, which is why the fixture pins both.
#[test]
fn test_struct_with_source_of_a_different_structure_is_the_point() {
    let verdicts = elab_fixture("with_source_expected_type.lean");
    let mk_d = verdicts
        .iter()
        .find(|(name, _)| name == "mkD")
        .map(|(_, verdict)| verdict.clone());
    assert_eq!(
        mk_d,
        Some(Ok(())),
        "`mkD` is `{{ s with d := 7 }}` with `s : Base` and expected type `Deriv`; \
         it is rejected exactly when the fields are resolved against the source"
    );
}

/// Brick 18. `__ := e` is Mathlib's SPREAD: it contributes `e` as an additional
/// `with`-source. Pinned to what the pinned `lean` + the real Mathlib checkout
/// print — `fun s => (have __spread.0 := s; { toBase2 := __spread.0, d := 7 })`
/// — and NOT to bare Lean, which rejects `__` outright ("`__` is not a field of
/// structure `Deriv2`"). See the fixture header for both measurements.
#[test]
fn test_struct_spread_field_is_an_extra_source() {
    assert_all_accepted(
        "spread_source.lean",
        &["mkD2", "mkD2Brace", "bumpP", "mkD2WithBeatsSpread"],
    );
}

/// The CONVENIENT APPROXIMATION for brick 18: "`__ := e` assigns the parent
/// subobject". It is not — a spread is a *source*, so it fills every field it
/// can provide. `bumpP` is the arm that separates the two: `Pair` has no parent
/// at all, so a parent-injection reading gives `q` nothing and the declaration
/// is rejected as missing a field. Lean prints
/// `fun x => (have __spread.0 := x; { p := 1, q := __spread.0.q })`.
#[test]
fn test_struct_spread_fills_a_non_parent_field() {
    let verdicts = elab_fixture("spread_source.lean");
    let bump_p = verdicts
        .iter()
        .find(|(name, _)| name == "bumpP")
        .map(|(_, verdict)| verdict.clone());
    assert_eq!(
        bump_p,
        Some(Ok(())),
        "`bumpP` spreads a whole `Pair` and assigns only `p`; `q` must come \
         from the spread, and `Pair` has no parent for an injection to target"
    );
}

/// THE BOUNDARY, pinned as a negative so nobody reads bricks 12/18 as covering
/// it: `openWith` and `openSpread` assign an INHERITED field alongside a source
/// of a different structure. Lean accepts both (the fixture header carries its
/// output); Clean rejects both, before these bricks and after them, because the
/// inherited assignment has to be routed into the nested `toBase3` slot whose
/// other fields would then have to come from the source.
///
/// This test asserts they are still rejected. If it starts failing, the gap
/// closed — update the fixture header and move these two into
/// `spread_source.lean` / `with_source_expected_type.lean`; do not weaken it.
#[test]
fn test_struct_inherited_field_with_foreign_source_is_still_open() {
    let verdicts = elab_fixture("source_inherited_field_open.lean");
    for want in ["openWith", "openSpread"] {
        let verdict = verdicts
            .iter()
            .find(|(name, _)| name == want)
            .unwrap_or_else(|| panic!("`{want}` produced no verdict"));
        assert!(
            verdict.1.is_err(),
            "`{want}` is the documented open boundary of bricks 12/18 and is \
             expected to be rejected; it was accepted, so the gap closed"
        );
    }
}
