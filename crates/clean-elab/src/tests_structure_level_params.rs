// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A structure's universe parameters are the ones its type, constructor and
//! projections USE — never a level metavariable that field elaboration minted
//! and did not assign.
//!
//! An instance candidate that is tried and rolled back leaves its freshened
//! level names (`?u_N`) in `universe_params`. The structure's self-occurrence
//! `S.{…}` is built from EVERY name in that list, and the "which parameters
//! survive" scan used to count the self-occurrence as a use — so a structure
//! whose field ran an instance search past a universe-polymorphic candidate
//! was registered as `S.{?u_4}`: a phantom parameter no use site can
//! determine. `by exact s` then died on `cannot assign rigid universe
//! parameter ?u_1 := ?u_3`, and a term-mode use left a level metavariable
//! behind.
//!
//! Ground truth (pinned v4.30.0-rc2 `lean`, 2026-09-20): the fixture
//! elaborates as written; `S` has no universe parameter and `C` has exactly
//! `u`.

use crate::test_support::file_verdicts::{assert_all_accepted, run_file, verdict_of};

/// `Foo Nat` is answered by `fooNat`, with a universe-polymorphic candidate
/// whose `[Marker α]` premise fails registered on EITHER side of it, so the
/// search passes a rolled-back polymorphic candidate whatever the order.
const FIXTURE: &str = "universe u\n\
     class Marker (α : Type u) where\n\
     \x20 m : Nat\n\
     class Foo (α : Type u) where\n\
     \x20 x : Nat\n\
     instance fooOfMarker1 {α : Type u} [Marker α] : Foo α := ⟨0⟩\n\
     instance fooNat : Foo Nat := ⟨1⟩\n\
     instance fooOfMarker2 {α : Type u} [Marker α] : Foo α := ⟨0⟩\n\
     structure S where\n\
     \x20 n : Nat\n\
     \x20 h : @Foo.x Nat _ = n\n\
     class C (α : Type u) where\n\
     \x20 a : α\n\
     \x20 h : @Foo.x Nat _ = 1\n";

#[test]
fn test_structure_rolled_back_candidate_levels_are_not_universe_params() {
    let verdicts = run_file(&format!(
        "{FIXTURE}\
         def useS (s : S) : S := by exact s\n\
         def useC {{α : Type u}} [inst : C α] : C α := by exact inst\n\
         def mkS : S := ⟨1, rfl⟩\n"
    ));
    for name in ["useS", "useC", "mkS"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: the structure must carry exactly its used universe parameters: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// The registered parameter lists themselves, read off the environment: `S`
/// is monomorphic and `C` has the one declared parameter.
#[test]
fn test_structure_registered_level_params_match_lean() {
    use crate::{
        elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult,
        FileContext,
    };
    let decls = clean_parser::parse_file(FIXTURE).expect("fixture must parse");
    let mut env = clean_kernel::Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut seen = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .unwrap_or_else(|e| panic!("fixture declaration must elaborate: {e:?}"));
        if let ElabResult::Structure {
            name,
            universe_params,
            ..
        } = result
        {
            let params: Vec<String> = universe_params.iter().map(ToString::to_string).collect();
            seen.push((name.to_string(), params));
        }
    }
    let params_of = |wanted: &str| {
        seen.iter()
            .find(|(n, _)| n == wanted)
            .map(|(_, p)| p.clone())
            .unwrap_or_else(|| panic!("`{wanted}` must be a structure result; got {seen:?}"))
    };
    assert_eq!(params_of("S"), Vec::<String>::new(), "Lean: `S : Type`");
    assert_eq!(params_of("C"), vec!["u".to_string()], "Lean: `C.{{u}}`");
    assert_eq!(params_of("Foo"), vec!["u".to_string()], "Lean: `Foo.{{u}}`");
}
