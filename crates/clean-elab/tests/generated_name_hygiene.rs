// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Names the parser and elaborator write into a desugaring must mean what the
//! desugaring means, whatever the user's program binds under the same
//! spelling. False theorems measured 2026-09-25 against Lean 4.8.0, each
//! accepted by the previous Clean (82a9eeeee), and their fixes:
//!
//! * `_eqn_last`, the as-alias the parser gives a last equation position that
//!   is itself a tuple, was a plain identifier: with `def _eqn_last : Nat ×
//!   Nat := (40, 41)`, the arm `| 0, (a, b) => _eqn_last.1 + a + b` read the
//!   alias, and `e1 0 (1, 2) = 4` held by `rfl` (Lean: 43). It is now
//!   `SurfaceName::unspellable`.
//! * An anonymous `letI : T := v; body` bound `_anon`, a plain identifier, so
//!   a global `_anon` in the body read the instance: `q1 = 6` (Lean: 78). It
//!   now binds `this`, as Lean's `letI` does.
//! * A NOTATION's head (`and` for `&&`, `or` for `||`, `Not` for `¬`, `Eq`
//!   for `=`, `Ne`, `Iff`, `And`, `Or`, `Exists`, `Prod` for `×`, `Sum` for
//!   `⊕`, `toString` for `s!`, …) was resolved like a source identifier, so a
//!   parameter of that spelling captured it: `def k1 (and : Bool → Bool →
//!   Bool) (a b : Bool) := a && b` made `k1 (fun _ _ => true) false false =
//!   true` provable (Lean: `false`), and `def k4 (Eq : Nat → Nat → Prop) :=
//!   (1 : Nat) = 2` made `k4 (fun _ _ => True)` itself provable. Those heads
//!   are now `SurfaceName::global_path` references, which never resolve to a
//!   local.
//!
//! Every expected (`T`) statement below is accepted by Lean 4.8.0 and every
//! `F` statement is refused by it (both measured); each `F` is the value the
//! previous Clean computed, not `truth + 1`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

/// `(holds, decidable, statement)`: a statement that holds must register
/// axiom-free by `rfl`; one that does not must be refused by `rfl` and, when
/// it is a decidable equation of data, by `decide`, leaving nothing behind.
fn check(env: &mut Environment, prefix: &str, cases: &[(bool, bool, &str)]) {
    for (id, (holds, decidable, statement)) in cases.iter().enumerate() {
        if *holds {
            let name = format!("{prefix}_true_{id}");
            register(env, &format!("theorem {name} : {statement} := rfl"))
                .unwrap_or_else(|error| panic!("{statement} must hold: {error}"));
            let deps = env
                .axiom_deps(&Name::from_string(&name))
                .expect("registered theorem");
            assert!(deps.is_empty(), "{statement}: depends on axioms: {deps:?}");
            continue;
        }
        let proofs: &[(&str, &str)] = if *decidable {
            &[("rfl", "rfl"), ("decide", "by decide")]
        } else {
            &[("rfl", "rfl")]
        };
        for (kind, proof) in proofs {
            let name = format!("{prefix}_false_{id}_{kind}");
            let error = register(env, &format!("theorem {name} : {statement} := {proof}"))
                .expect_err(&format!("FALSE theorem accepted: {statement} := {proof}"));
            assert!(
                !error.contains("parse error"),
                "negative must parse: {error}"
            );
            assert!(
                env.get_const(&Name::from_string(&name)).is_none(),
                "false theorem registered: {statement}"
            );
        }
    }
}

#[test]
fn last_tuple_position_alias_does_not_capture_a_global() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def _eqn_last : Nat × Nat := (40, 41)
def e1 : Nat → Nat × Nat → Nat
  | 0, (a, b) => _eqn_last.1 + a + b
  | n+1, (a, _) => _eqn_last.2 + n + a
def e4 : Nat → Nat × Nat → Nat × Nat → Nat
  | 0, (a, b), (c, d) => _eqn_last.1 + a + b + c + d
  | _, _, _ => 0
def e5 (p : Nat × Nat) : Nat := match (0 : Nat), p with
  | 0, (a, b) => _eqn_last.1 + a + b
  | _, _ => 0
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "eqn_last",
        &[
            (true, true, "e1 0 (1, 2) = 43"),
            (false, true, "e1 0 (1, 2) = 4"),
            (true, true, "e1 2 (5, 6) = 47"),
            (true, true, "e4 0 (1, 2) (3, 4) = 50"),
            (false, true, "e4 0 (1, 2) (3, 4) = 13"),
            (true, true, "e5 (1, 2) = 43"),
        ],
    );
    let error = register(
        &mut env,
        "theorem e1_general_false : ∀ a b : Nat, e1 0 (a, b) = a + a + b := fun _ _ => rfl",
    )
    .expect_err("FALSE theorem accepted: ∀ a b, e1 0 (a, b) = a + a + b");
    assert!(!error.contains("parse error"), "{error}");
}

#[test]
fn anonymous_let_instance_binds_this() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def _anon : Nat := 77
def q1 : Nat := letI : Nat := 5; _anon + 1
def q2 (n : Nat) : Nat :=
  letI : Nat := n
  _anon + n
def q3 : Nat := letI : Nat := 5; this + 1
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "anon",
        &[
            (true, true, "q1 = 78"),
            (false, true, "q1 = 6"),
            (true, true, "q2 3 = 80"),
            (false, true, "q2 3 = 6"),
            (true, true, "q3 = 6"),
            (false, true, "(letI : Nat := 5; _anon) = 5"),
        ],
    );
}

#[test]
fn notation_heads_are_not_captured_by_locals() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def k1 (and : Bool → Bool → Bool) (a b : Bool) : Bool := a && b
def k2 (or : Bool → Bool → Bool) (a b : Bool) : Bool := a || b
def k3 (Not : Prop → Prop) : Prop := ¬ True
def k4 (Eq : Nat → Nat → Prop) : Prop := (1 : Nat) = 2
def k5 (Ne : Nat → Nat → Prop) : Prop := (1 : Nat) ≠ 1
def k6 (Iff : Prop → Prop → Prop) : Prop := True ↔ False
def k7 (And : Prop → Prop → Prop) : Prop := True ∧ False
def k8 (Or : Prop → Prop → Prop) : Prop := False ∨ False
def k9 (Exists : (Nat → Prop) → Prop) : Prop := ∃ n : Nat, n = n
def k10 (Prod : Type → Type → Type) : Type := Nat × Nat
def k11 (Sum : Type → Type → Type) : Type := Nat ⊕ Nat
def k12 (toString : Nat → String) (n : Nat) : String := s!"{n}"
def k13 (HAdd : Nat) (a b : Nat) : Nat := a + b + HAdd
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "head",
        &[
            (true, true, "k1 (fun _ _ => true) false false = false"),
            (false, true, "k1 (fun _ _ => true) false false = true"),
            (true, true, "k2 (fun _ _ => false) true true = true"),
            (false, true, "k2 (fun _ _ => false) true true = false"),
            (false, false, "k3 (fun _ => True) = True"),
            (false, false, "k4 (fun _ _ => True) = True"),
            (false, false, "k5 (fun _ _ => True) = True"),
            (false, false, "k6 (fun _ _ => True) = True"),
            (false, false, "k7 (fun _ _ => True) = True"),
            (false, false, "k8 (fun _ _ => True) = True"),
            (false, false, "k9 (fun _ => False) = False"),
            (false, false, "k10 (fun _ _ => Nat) = Nat"),
            (false, false, "k11 (fun _ _ => Nat) = Nat"),
            (true, true, "k12 (fun _ => \"z\") 3 = \"3\""),
            (false, true, "k12 (fun _ => \"z\") 3 = \"z\""),
            (true, true, "k13 10 1 2 = 13"),
        ],
    );
    // `k4 (fun _ _ => True)` unfolds to `1 = 2`: a proof of it is a proof of
    // `False`.
    let error = register(
        &mut env,
        "theorem k4_holds : k4 (fun _ _ => True) := by unfold k4; trivial",
    )
    .expect_err("FALSE theorem accepted: k4 (fun _ _ => True)");
    assert!(!error.contains("parse error"), "{error}");
}
