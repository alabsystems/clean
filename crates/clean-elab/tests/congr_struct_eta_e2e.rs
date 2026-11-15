// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `congr` on a ONE-SIDED constructor equality `S.mk a⃗ = e`.
//!
//! Lean's `MVarId.congr?` (`Lean/Meta/Tactic/Congr.lean:42-51`) reads the head
//! off the LEFT side only and `applyCongrThm?` (:33-38) then `apply`s the
//! generated congruence theorem, so the RIGHT side's arguments are solved by
//! `isDefEq` — and `isDefEqEtaStruct` (`Lean/Meta/ExprDefEq.lean:111`, called at
//! :2176) assigns `?b := e.field`. Lean therefore never requires the right side
//! to be syntactically a constructor application.
//!
//! Clean's port decided by a syntactic head-plus-arity match in `rhs_args`
//! (`crates/clean-elab/src/tactic/congr_n.rs`), so `MyBEq.mk beq1 = inst2` with
//! `inst2` a rigid local made NO progress: the row is `beq_ext`
//! (`Mathlib/Logic/Basic.lean:999`, `have ⟨beq1⟩ := inst1; congr; funext x y;
//! exact h x y`), whose reported face — "Unknown identifier: x" — is the
//! `funext` afterwards finding no function equality to work on.
//!
//! The fallback is structure ETA and it is gated on `is_def_eq`, which is the
//! same question Lean asks: Clean's def-eq already has structure eta
//! (`theorem eta1 (i : MyBEq α) : i = MyBEq.mk i.beq := rfl` passes).
//!
//! ACCEPTANCE BAR: the positive case PROVES its theorem end to end (the kernel
//! re-checks the term), and the controls pin the four class-33 contracts that
//! must not move.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// A one-field structure over a function, exactly `BEq`'s shape.
const BEQ: &str = "
structure MyBEq (a : Type) where
  mk :: (beq : a -> a -> Bool)
";

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

#[test]
fn test_congr_splits_a_constructor_against_a_bare_local() {
    // The exact goal shape `beq_ext` reaches after its `have ⟨beq1⟩ := inst1`:
    // a constructor application on the LEFT and a rigid local on the RIGHT.
    // `congr` must split it into the per-field equation, which `congrPre`'s
    // `assumption` then closes — `MyBEq.beq a i2` and `Proj(MyBEq, 0, i2)` are
    // definitionally the same. Before the eta fallback, `rhs_args` returned
    // `None` here and congr made NO progress at all.
    let src = format!(
        "{BEQ}
theorem mkEqLocal (a : Type) (i2 : MyBEq a) (b1 : a -> a -> Bool)
    (h : b1 = i2.beq) : (⟨b1⟩ : MyBEq a) = i2 := by
  congr
"
    );
    elaborate_module(&src)
        .expect("congr must split `S.mk a = e` through structure eta on the right");
}

/// The same split with the residual field equation discharged POINTWISE — the
/// `congr; funext x y; exact h x y` tail `beq_ext` itself writes.
#[test]
fn test_congr_split_leaves_the_pointwise_field_equation() {
    let src = format!(
        "{BEQ}
theorem mkEqLocalFunext (a : Type) (i2 : MyBEq a) (b1 : a -> a -> Bool)
    (h : forall x y, b1 x y = i2.beq x y) : (⟨b1⟩ : MyBEq a) = i2 := by
  congr
  funext x y
  exact h x y
"
    );
    elaborate_module(&src)
        .expect("the split must leave exactly the pointwise field equation `funext` expects");
}

/// CONTROL (class-33 contract): `congr` NEVER fails — it leaves what it cannot
/// split. A two-constructor inductive has no eta and must be left alone, not
/// eta-expanded into a wrong goal.
#[test]
fn test_congr_leaves_a_multi_constructor_goal_untouched() {
    let src = "
inductive Two where
  | left : Nat -> Two
  | right : Nat -> Two

theorem twoLeft (n : Nat) (t : Two) (h : Two.left n = t) : Two.left n = t := by
  congr
";
    elaborate_module(src)
        .expect("congr must leave a multi-constructor goal for the closing steps, never split it");
}

/// CONTROL (class-33 contract): `congr 0` still closes `a = a`.
#[test]
fn test_congr_zero_still_closes_reflexivity() {
    let src = format!(
        "{BEQ}
theorem congrZero (a : Type) (i : MyBEq a) : i = i := by
  congr 0
"
    );
    elaborate_module(&src).expect("congr 0 must still close a reflexive goal");
}

/// CONTROL (class-33 contract): `congrPre` runs first, so an `assumption`-closable
/// goal never reaches the split at all.
#[test]
fn test_congr_closes_by_assumption_before_splitting() {
    let src = format!(
        "{BEQ}
theorem congrPre (a : Type) (i1 : MyBEq a) (i2 : MyBEq a) (h : i1 = i2) : i1 = i2 := by
  congr
"
    );
    elaborate_module(&src).expect("congrPre's assumption arm must still close the goal");
}

/// CONTROL: structure eta itself, so a failure of the test above can be read as
/// a `congr` defect and not a def-eq one.
#[test]
fn test_structure_eta_holds_in_defeq() {
    let src = format!(
        "{BEQ}
theorem eta1 (a : Type) (i : MyBEq a) : i = (⟨i.beq⟩ : MyBEq a) := rfl
"
    );
    elaborate_module(&src).expect("Clean's def-eq has structure eta; the congr gate relies on it");
}

// ---------------------------------------------------------------------------
// ADVERSARIAL REVIEW ADDITIONS (W3E review pass)
//
// Ground-truthed on the same shapes against
// `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`: the whole file
// below is accepted there (EXIT=0, no diagnostics).
// ---------------------------------------------------------------------------

/// A structure whose two fields have DIFFERENT types, so a projection emitted
/// at the wrong position cannot type-check. This is the named trap of the
/// change — "emitting a projection at a parameter position would mint a
/// well-typed WRONG goal" — read back at the FIELD positions: if
/// `struct_eta_rhs_args` ever paired field `i` with `Proj(S, j, rhs)` for
/// `i ≠ j`, the `infer_type` gate would refuse and `congr` would make no
/// progress, so this theorem would stop being proved.
#[test]
fn test_congr_struct_eta_pairs_each_field_with_its_own_projection() {
    let src = "
structure Mixed where
  mk :: (n : Nat) (b : Bool)

theorem mixedEta (m : Mixed) (h1 : 1 = m.n) (h2 : true = m.b)
    : (⟨1, true⟩ : Mixed) = m := by
  congr
";
    elaborate_module(src)
        .expect("each field position must receive its OWN projection of the right side");
}

/// The structure's PARAMETERS come from the LEFT side, never from a projection.
/// `Tagged 3` has one parameter and one field, so a parameter slot filled with
/// `Proj(Tagged, 0, t)` would be the well-typed wrong goal the change exists to
/// avoid; the value pin is that the theorem still closes.
#[test]
fn test_congr_struct_eta_takes_parameters_from_the_left_side() {
    let src = "
structure Tagged (k : Nat) where
  mk :: (v : Nat)

theorem taggedEta (t : Tagged 3) (h : 1 = t.v) : (⟨1⟩ : Tagged 3) = t := by
  congr
";
    elaborate_module(src).expect("a parameter slot must be filled from the LEFT side");
}

/// ORDERING CONTROL: the pre-existing `whnf` fallback still runs BEFORE the new
/// eta one, so a right side that unfolds to a constructor application keeps
/// taking the old path. A regression here would be silent — both paths can
/// prove this — so it is pinned as a value, not as a mechanism.
#[test]
fn test_congr_unfolding_right_side_still_takes_the_whnf_path() {
    let src = "
structure Mixed2 where
  mk :: (n : Nat) (b : Bool)

def mkIt (n : Nat) : Mixed2 := ⟨n, true⟩

theorem viaDef (n : Nat) : (⟨n, true⟩ : Mixed2) = mkIt n := by
  congr
";
    elaborate_module(src).expect("a definition on the right still unfolds through `whnf` first");
}
