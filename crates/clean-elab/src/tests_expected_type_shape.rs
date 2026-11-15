// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expected-type SHAPE at two kinds of site (trust-ir round 4, lane X).
//!
//! * **G31, ledger (101).** An abbreviated monad type reaches a later branch
//!   FOLDED. Lean's `elabMatch` gives every alternative the first one's
//!   inferred type as is, and an `if` with no expected type elaborates its
//!   else-branch against the then-branch's type. Clean whnf-unfolded both
//!   (`StateT σ m α` is a Pi underneath), so a `pure ()` / `throw err` branch
//!   faced a bare Pi and could not pin its monad.
//! * **G34, ledger (104).** A `Bool` in a TYPE position (an arrow side, a
//!   binder type, a `∀` body, a declaration's result type) is coerced to
//!   `b = true`, Lean's `elabType` → `coerceToSort` through
//!   `CoeSort Bool Prop`.
//!
//! Every widening carries a negative control the pinned Lean 4.8.0 binary
//! rejects (`reports/trust-ir-semantics-probe/repros/G31-*`, `G34-*`).

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_parser::parse_file;

/// Elaborate every declaration of `src`; the first refusal, rendered.
fn elab(env: &mut Environment, src: &str) -> Result<(), String> {
    let decls = parse_file(src).map_err(|e| format!("parse: {e:?}"))?;
    for d in &decls {
        elaborate_decl_and_register_with_warning(env, d).map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

fn accepts(src: &str) {
    let mut env = Environment::with_prelude();
    if let Err(e) = elab(&mut env, src) {
        panic!("pinned Lean 4.8.0 accepts this, Clean must too: {e}\n{src}");
    }
}

/// The refusal text; panics when the source is accepted.
fn refuses(src: &str) -> String {
    let mut env = Environment::with_prelude();
    match elab(&mut env, src) {
        Ok(()) => panic!("pinned Lean 4.8.0 refuses this, Clean must too:\n{src}"),
        Err(e) => e,
    }
}

const G31_IF: &str = "def g31_if (b : Bool) (x : StateT Nat (Except String) Unit) : \
    StateT Nat (Except String) Unit :=\n  if b then x else pure ()\n";

const SEM: &str = "abbrev Sem (α : Type) := StateT Nat (Except String) α\n";

#[test]
fn test_g31_if_else_branch_sees_folded_monad_and_computes() {
    accepts(&format!(
        "{G31_IF}theorem g31_if_false : g31_if false (fun _ => .ok ((), 7)) 3 = .ok ((), 3) := rfl\n\
         theorem g31_if_true : g31_if true (fun _ => .ok ((), 7)) 3 = .ok ((), 7) := rfl\n"
    ));
}

#[test]
fn test_g31_if_unannotated_def_infers_folded_type() {
    // No declared type: the speculative lane is the only lane.
    accepts(
        "def g31_n (b : Bool) (x : StateT Nat (Except String) Unit) :=\n  \
         if b then x else pure ()\n",
    );
}

#[test]
fn test_g31_if_false_value_claim_is_refused() {
    let e = refuses(&format!(
        "{G31_IF}theorem g31_twin : g31_if false (fun _ => .ok ((), 7)) 3 = .ok ((), 7) := rfl\n"
    ));
    assert!(e.contains("g31_twin") || e.contains("mismatch"), "{e}");
}

#[test]
fn test_g31_if_ill_typed_else_branch_is_refused() {
    // The RIGHT reason (Lean: "application type mismatch" at `pure true`):
    // integ/r2 refused this as "failed to synthesize instance `Pure ?0`".
    let e = refuses(
        "def g31_bad (b : Bool) (x : StateT Nat (Except String) Unit) : \
         StateT Nat (Except String) Unit :=\n  if b then x else pure true\n",
    );
    assert!(
        e.contains("Type mismatch") && e.contains("Bool vs PUnit"),
        "the payload mismatch, not an instance failure: {e}"
    );
}

#[test]
fn test_g31_match_motive_keeps_abbrev_under_open_expected_type() {
    accepts(&format!(
        "{SEM}def g31_pnl {{α : Type}} (m : Sem α) : Prop := ∀ s, m s ≠ .error \"boom\"\n\
         theorem g31_match (e : Except String Nat) (onOk : Nat → Sem Nat)\n    \
         (h : ∀ x, g31_pnl (onOk x)) (h2 : ∀ (err : String), g31_pnl (throw err : Sem Nat)) :\n    \
         g31_pnl (match e with\n      | .ok v => onOk v\n      | .error err => throw err) := by\n  \
         cases e with\n  | ok v => exact h v\n  | error err => exact h2 err\n"
    ));
}

#[test]
fn test_g31_match_motive_lift_computes() {
    accepts(&format!(
        "{SEM}def g31_lift (e : Except String Nat) (onOk : Nat → Sem Nat) : Sem Nat :=\n  \
         id (match e with\n    | .ok v => onOk v\n    | .error err => throw err)\n\
         theorem g31_lift_error : g31_lift (.error \"x\") (fun v => pure v) 0 = .error \"x\" := rfl\n\
         theorem g31_lift_ok : g31_lift (.ok 4) (fun v => pure (v+1)) 0 = .ok (5, 0) := rfl\n"
    ));
}

#[test]
fn test_g31_match_ill_typed_later_arm_is_refused() {
    // The RIGHT reason (Lean: "application type mismatch" at `pure true`),
    // never the motive refusal (`Match arm 1 has type …`).
    let e = refuses(&format!(
        "{SEM}def g31_bad_match (e : Except String Nat) (onOk : Nat → Sem Nat) : Sem Nat :=\n  \
         id (match e with\n    | .ok v => onOk v\n    | .error _ => pure true)\n"
    ));
    assert!(
        e.contains("Type mismatch") && e.contains("Bool vs Nat"),
        "the payload mismatch, not a motive refusal: {e}"
    );
}

/// G31's argument face (ledger (101)), CLOSED at the round-3/4 integration
/// (integ/r5, 2026-10-16): with NO expected type, `Option.getD (some x) (pure
/// ())` at `x : StateT …` elaborates, as in pinned Lean 4.8.0. It was pinned
/// as a refusal ("cannot unify an application with a function type": the
/// `pure ()` slot met `StateT …` unfolded to its Pi); lane E's folded
/// bare-metavariable assignment (decision R51, choice 2) now hands the slot
/// `StateT Nat (Except String) Unit` as written. The value computes, and the
/// twin `pure true` is refused at the payload, as Lean refuses it
/// ("application type mismatch").
#[test]
fn test_g31_open_argument_slot_without_expected_type() {
    accepts(
        "def g31_arg (x : StateT Nat (Except String) Unit) := Option.getD (some x) (pure ())\n\
         theorem g31_arg_computes : g31_arg (fun s => .ok ((), s + 1)) 3 = .ok ((), 4) := rfl\n",
    );
    let e = refuses(
        "def g31_arg_bad (x : StateT Nat (Except String) Unit) := \
         Option.getD (some x) (pure true)\n",
    );
    assert!(
        e.contains("Type mismatch") && e.contains("Bool vs PUnit"),
        "the payload mismatch, not the old Pi refusal: {e}"
    );
}

/// G31's `Eq`-operand face (ledger (101)), CLOSED at the round-3/4
/// integration (integ/r5, 2026-10-16): two `match`es as the operands of `=`
/// with no ground expected type elaborate, as in pinned Lean 4.8.0 (pinned as
/// a refusal until then: "but match motive expects" — the left one's type
/// reached the right one's motive unfolded; closed by the same folded
/// assignment, R51 choice 2). Twins that Lean refuses: a false `rfl` ("type
/// mismatch") and an ill-typed right arm `pure true` ("application type
/// mismatch").
#[test]
fn test_g31_match_as_eq_operand() {
    accepts(&format!(
        "{SEM}theorem g31_eq (e : Except String Nat) : (match e with\n    \
         | .ok v => (pure v : Sem Nat)\n    | .error err => throw err) =\n    \
         (match e with | .ok v => pure v | .error err => throw err) := rfl\n"
    ));
    let e = refuses(&format!(
        "{SEM}theorem g31_eq_false (e : Except String Nat) : (match e with\n    \
         | .ok v => (pure v : Sem Nat)\n    | .error err => throw err) =\n    \
         (match e with | .ok v => pure (v + 1) | .error err => throw err) := rfl\n"
    ));
    assert!(e.contains("mismatch"), "a false rfl is a mismatch: {e}");
    let e = refuses(&format!(
        "{SEM}theorem g31_eq_bad (e : Except String Nat) : (match e with\n    \
         | .ok v => (pure v : Sem Nat)\n    | .error err => throw err) =\n    \
         (match e with | .ok v => pure true | .error err => throw err) := rfl\n"
    ));
    assert!(
        e.contains("Type mismatch") && e.contains("Bool vs Nat"),
        "the payload mismatch, not a motive refusal: {e}"
    );
}

fn binder_types(env: &Environment, name: &str) -> Vec<Expr> {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    let mut ty: Expr = Expr::clone(&info.type_);
    let mut out = Vec::new();
    while let ExprKind::Pi(_, dom, body) = ty.kind() {
        let (dom, body) = (dom.as_ref().clone(), body.as_ref().clone());
        out.push(dom);
        ty = body;
    }
    out.push(ty);
    out
}

fn is_eq_true(e: &Expr) -> bool {
    let args = e.get_app_args();
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "Eq")
        && args.len() == 3
        && matches!(args[2].kind(), ExprKind::Const(n, _) if n.to_string() == "Bool.true")
}

#[test]
fn test_g34_bool_arrow_sides_and_binders_coerce_to_eq_true() {
    accepts(
        "structure Alloc where\n  id : Nat\n  alive : Bool\n\
         def g34_wf (xs : List Alloc) : Prop :=\n  \
         ∀ a1 a2 : Alloc, a1 ∈ xs → a2 ∈ xs → a1.alive → a2.alive → a1.id != a2.id → True\n\
         def g34_neq_imp (n : Nat) : Prop := ∀ m : Nat, m != n → m != n\n\
         theorem g34_neq_imp_holds (n : Nat) : g34_neq_imp n := fun _ h => h\n\
         theorem g34_binder (b : Bool) (h : b) : b = true := h\n\
         theorem g34_result (b : Bool) (h : b = true) : b := h\n\
         def g34_pi_binder (b : Bool) : Prop := (h : b) → True\n\
         def g34_pi_body (b : Bool) : Prop := ∀ (_ : True), b\n\
         theorem g34_forall : ∀ b : Bool, b → b = true := fun _ h => h\n\
         theorem g34_fun_binder : ∀ b : Bool, b → b = true := fun b (h : b) => h\n\
         theorem g34_unfolds (b : Bool) : (b → True) = (b = true → True) := rfl\n",
    );
}

#[test]
fn test_g34_signature_binder_type_is_eq_true() {
    let mut env = Environment::with_prelude();
    elab(
        &mut env,
        "theorem g34_sig (o : Option Nat) (h : o != none) : True := True.intro\n",
    )
    .unwrap_or_else(|e| panic!("Lean accepts a Bool signature binder: {e}"));
    let tys = binder_types(&env, "g34_sig");
    assert!(
        is_eq_true(&tys[1]),
        "`h : o != none` binds `(o != none) = true`: {}",
        tys[1]
    );
}

#[test]
fn test_g34_prop_type_positions_are_untouched() {
    let mut env = Environment::with_prelude();
    elab(
        &mut env,
        "theorem g34_prop (P : Prop) (h : P) : P → P := fun _ => h\n",
    )
    .unwrap_or_else(|e| panic!("a Prop binder is unchanged: {e}"));
    for ty in binder_types(&env, "g34_prop") {
        assert!(!is_eq_true(&ty), "no coercion on a Prop: {ty}");
    }
}

#[test]
fn test_g34_coerced_arrow_false_claim_is_refused() {
    refuses("theorem g34_twin (n : Nat) : ∀ m : Nat, m != n → m == n := fun _ h => h\n");
}

#[test]
fn test_g34_coercion_is_eq_true_not_eq_false() {
    refuses("theorem g34_twin_false (b : Bool) (h : b) : b = false := h\n");
}

#[test]
fn test_g34_non_bool_non_type_is_still_refused() {
    // `Nat` has no `CoeSort`: a numeral in a type position stays an error.
    refuses("def g34_nat_type (n : Nat) : Prop := n → True\n");
}
