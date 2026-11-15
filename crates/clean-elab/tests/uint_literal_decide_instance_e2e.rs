// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `decide (d < 21)` at a machine carrier must be the SAME TERM as the
//! carrier's own decision — end to end, through the real file pipeline.
//!
//! ## The gap this guards
//!
//! Two spellings of one decision at `UInt32`:
//!
//! ```text
//! def sugar    (d : UInt32) : Bool := decide (d < 21)
//! def explicit (d : UInt32) : Bool :=
//!   @Decidable.decide (LT.lt d (UInt32.ofNat 21))
//!                    (instDecidableUInt32Lt d (UInt32.ofNat 21))
//! ```
//!
//! With two PARAMETERS (`decide (a < b)`) these already coincide. With a
//! LITERAL operand they did not, and `theorem : sugar d = explicit d := Eq.refl`
//! was rejected — *"the two sides are not definitionally equal"*.
//!
//! ## Measured cause (2026-09-20)
//!
//! `decide X` binds `X` to `decide`'s IMPLICIT `{p : Prop}`, and the assignment
//! stores the weak-head-normalised proposition, so the `Decidable` goal is
//! already the `Nat`-level `Nat.le (Nat.succ (BitVec.toNat 32 (UInt32.toBitVec
//! d))) …` rather than `@LT.lt UInt32 instLTUInt32 d …`. Resolving
//! `instDecidableUInt32Lt` against that goal has to INVERT
//! `BitVec.toNat 32 (UInt32.toBitVec ?b)`, which succeeds while `?b`'s partner
//! is a variable and fails once it is `UInt32.ofNat 21` (whnf collapses that
//! operand to a numeral before the congruence step). The search then falls
//! through to `instDecidableNatLt`.
//!
//! That fall-through was only FATAL because the two instances were not
//! convertible: `UInt32.decLt` was a bespoke `dite` over `Nat.ble` while
//! `Nat.decLt` is a `Bool.rec` dispatcher, so `instDecidableNatLt A B` and
//! `instDecidableUInt32Lt a b` never met even with NO literal anywhere
//! (`nat_level_and_carrier_decisions_are_convertible` below pins exactly that,
//! and it failed before this fix).
//!
//! The repair is in `clean-kernel`'s wrapper order stack
//! (`algebra_uint_dec_le_proof.rs`): the BitVec-carrier builder now defines
//! `<T>.decLe`/`<T>.decLt` as `Nat.decLe`/`Nat.decLt` on the `toNat` images —
//! byte-for-byte the shape the Nat-carrier branch of the SAME builder already
//! used — so whichever instance the search picks, the kernel sees one term.
//!
//! ## Why this is not a weakening
//!
//! Every gate here is a real `Eq.refl` re-checked by the kernel, and the
//! NEGATIVE TWINS below (a different constant, the opposite direction, the
//! wrong relation) are still refused. `sugar`'s meaning is unchanged; only the
//! two spellings of it converged.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};
use clean_parser::parse_file;

/// Drive the real file pipeline (`parse_file → preprocess → elaborate+register`)
/// so a pass here matches an observable `clean check` pass on surface syntax.
fn try_elaborate(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(env)
}

/// The source must elaborate, and the named theorem's proof must `infer_type`
/// to its stated proposition with an EMPTY axiom closure — an `Eq.refl` the
/// kernel forced, not a `sorry`.
fn assert_refl_theorem(name: &str, source: &str) {
    let env = try_elaborate(source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` must carry a proof value"));
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition"
    );
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(deps.is_empty(), "`{name}` must be axiom-free; got {deps:?}");
}

/// The source must be REJECTED — the negative-twin shape.
fn assert_rejected(what: &str, source: &str) {
    let outcome = try_elaborate(source);
    assert!(
        outcome.is_err(),
        "{what} must be refused, but it elaborated"
    );
}

/// The three definitions every gate below is stated over, at `UInt32`.
///
/// The explicit spellings pass the instance through `@`: pinned Lean
/// (v4.30.0-rc2) gives `decide : (p : Prop) → [h : Decidable p] → Bool` and
/// refuses a positional instance (`Decidable.decide p inst`, "Function
/// expected"). Clean refuses it too
/// (`positional_instance_argument_is_refused_as_lean_refuses_it`), so without
/// `@` these definitions would not elaborate and the negative twins below
/// would pass without reaching their subject.
const DEFS_U32: &str = r#"
def sugar_lit (d : UInt32) : Bool := decide (d < 21)
def sugar_ofnat (d : UInt32) : Bool := decide (d < UInt32.ofNat 21)
def explicit_lit (d : UInt32) : Bool :=
  @Decidable.decide (LT.lt d (UInt32.ofNat 21))
                   (instDecidableUInt32Lt d (UInt32.ofNat 21))
"#;

// ---------------------------------------------------------------------------
// THE GOAL — the sugar an author actually writes IS the carrier's decision.
// ---------------------------------------------------------------------------

#[test]
fn literal_decide_sugar_is_the_carrier_decision() {
    assert_refl_theorem(
        "t_literal",
        &format!(
            "{DEFS_U32}
theorem t_literal : forall (d : UInt32), sugar_lit d = explicit_lit d :=
  fun d => Eq.refl (sugar_lit d)"
        ),
    );
}

/// The bare NUMERAL spelling and the explicit `UInt32.ofNat` spelling are one
/// term — this held before the fix and must keep holding (the numeral
/// elaboration was never the defect).
#[test]
fn numeral_and_ofnat_spellings_coincide() {
    assert_refl_theorem(
        "t_numeral",
        &format!(
            "{DEFS_U32}
theorem t_numeral : forall (d : UInt32), sugar_lit d = sugar_ofnat d :=
  fun d => Eq.refl (sugar_lit d)"
        ),
    );
}

/// The TWO-PARAMETER case, which already worked: it must not regress.
#[test]
fn two_parameter_sugar_is_the_carrier_decision() {
    assert_refl_theorem(
        "t_two",
        r#"
def sugar_two (a : UInt32) (b : UInt32) : Bool := decide (a < b)
def explicit_two (a : UInt32) (b : UInt32) : Bool :=
  @Decidable.decide (LT.lt a b) (instDecidableUInt32Lt a b)
theorem t_two : forall (a : UInt32) (b : UInt32), sugar_two a b = explicit_two a b :=
  fun a b => Eq.refl (sugar_two a b)"#,
    );
}

/// THE UNDERLYING DEFECT, stated with NO literal anywhere: the `Nat`-level
/// decision on the `toNat` images and the carrier's own decision are one term.
/// This is what the instance fall-through needed and did not have.
#[test]
fn nat_level_and_carrier_decisions_are_convertible() {
    assert_refl_theorem(
        "t_nat_vs_carrier",
        r#"
def nat_inst (a : UInt32) (b : UInt32) : Bool :=
  @Decidable.decide (Nat.lt (UInt32.toNat a) (UInt32.toNat b))
                   (instDecidableNatLt (UInt32.toNat a) (UInt32.toNat b))
def explicit_two (a : UInt32) (b : UInt32) : Bool :=
  @Decidable.decide (LT.lt a b) (instDecidableUInt32Lt a b)
theorem t_nat_vs_carrier :
    forall (a : UInt32) (b : UInt32), nat_inst a b = explicit_two a b :=
  fun a b => Eq.refl (nat_inst a b)"#,
    );
}

/// `<=` at the same carrier — the sibling relation, same route.
#[test]
fn literal_decide_le_sugar_is_the_carrier_decision() {
    assert_refl_theorem(
        "t_le",
        r#"
def sugar_le (d : UInt32) : Bool := decide (d <= 21)
def explicit_le (d : UInt32) : Bool :=
  @Decidable.decide (LE.le d (UInt32.ofNat 21))
                   (instDecidableUInt32Le d (UInt32.ofNat 21))
theorem t_le : forall (d : UInt32), sugar_le d = explicit_le d :=
  fun d => Eq.refl (sugar_le d)"#,
    );
}

/// The other widths the owner's code uses — `UInt64` (a `usize`/`u64` guard)
/// and `UInt8`.
#[test]
fn literal_decide_sugar_holds_at_u64_and_u8() {
    assert_refl_theorem(
        "t_u64",
        r#"
def sugar64 (d : UInt64) : Bool := decide (d < 2097152)
def explicit64 (d : UInt64) : Bool :=
  @Decidable.decide (LT.lt d (UInt64.ofNat 2097152))
                   (instDecidableUInt64Lt d (UInt64.ofNat 2097152))
theorem t_u64 : forall (d : UInt64), sugar64 d = explicit64 d :=
  fun d => Eq.refl (sugar64 d)"#,
    );
    assert_refl_theorem(
        "t_u8",
        r#"
def sugar8 (d : UInt8) : Bool := decide (d < 7)
def explicit8 (d : UInt8) : Bool :=
  @Decidable.decide (LT.lt d (UInt8.ofNat 7)) (instDecidableUInt8Lt d (UInt8.ofNat 7))
theorem t_u8 : forall (d : UInt8), sugar8 d = explicit8 d :=
  fun d => Eq.refl (sugar8 d)"#,
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE TWINS — the convergence must not admit a DIFFERENT decision.
// ---------------------------------------------------------------------------

/// A different constant: `d < 22` is not `d < 21`.
#[test]
fn a_different_literal_is_still_refused() {
    assert_rejected(
        "a comparison against a different constant",
        &format!(
            "{DEFS_U32}
def sugar_22 (d : UInt32) : Bool := decide (d < 22)
theorem t_bad : forall (d : UInt32), sugar_22 d = explicit_lit d :=
  fun d => Eq.refl (sugar_22 d)"
        ),
    );
}

/// The opposite direction: `21 < d` is not `d < 21`.
#[test]
fn the_wrong_direction_is_still_refused() {
    assert_rejected(
        "a wrong-direction comparison",
        &format!(
            "{DEFS_U32}
def sugar_swapped (d : UInt32) : Bool := decide (UInt32.ofNat 21 < d)
theorem t_bad_dir : forall (d : UInt32), sugar_swapped d = explicit_lit d :=
  fun d => Eq.refl (sugar_swapped d)"
        ),
    );
}

/// The wrong relation: `d <= 21` is not `d < 21`.
#[test]
fn the_wrong_relation_is_still_refused() {
    assert_rejected(
        "`<=` standing in for `<`",
        &format!(
            "{DEFS_U32}
def sugar_le21 (d : UInt32) : Bool := decide (d <= 21)
theorem t_bad_rel : forall (d : UInt32), sugar_le21 d = explicit_lit d :=
  fun d => Eq.refl (sugar_le21 d)"
        ),
    );
}

/// A different CARRIER is still a different decision: a `UInt64` island
/// definition does not discharge a `UInt32` one.
#[test]
fn a_different_carrier_is_still_refused() {
    assert_rejected(
        "a UInt64 decision standing in for a UInt32 one",
        &format!(
            "{DEFS_U32}
def sugar64 (d : UInt64) : Bool := decide (d < 21)
theorem t_bad_carrier : forall (d : UInt32), sugar64 d = explicit_lit d :=
  fun d => Eq.refl (sugar64 d)"
        ),
    );
}

/// Lean refuses a positional argument aimed at `decide`'s instance-implicit
/// `[h : Decidable p]` ("Function expected at decide (d < UInt32.ofNat 21) but
/// this term has type Bool", pinned v4.30.0-rc2). Clean must refuse the same
/// spelling instead of letting argument count fill the instance slot.
#[test]
fn positional_instance_argument_is_refused_as_lean_refuses_it() {
    let err = match try_elaborate(
        "def positional (d : UInt32) : Bool :=
  Decidable.decide (LT.lt d (UInt32.ofNat 21)) (instDecidableUInt32Lt d (UInt32.ofNat 21))",
    ) {
        Ok(_) => panic!("a positional argument must not fill `decide`'s `[h : Decidable p]`"),
        Err(err) => err,
    };
    assert!(
        err.contains("Too many arguments"),
        "the refusal must be the surplus-argument refusal; got {err}"
    );
}
