// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick E2 — term-level `▸` (subst) elaboration, Lean-faithful motive
//! inference (`docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md` §4 Brick 2).
//!
//! The acceptance bar is ORIENTATION FIDELITY: in computational cast positions
//! (`h ▸ (v : F a) : F b`) a wrong-orientation motive yields a well-typed but
//! WRONG value — silent wrongness the kernel re-check cannot catch. Every cast
//! below therefore pins the resulting VALUE in-language with a `rfl` theorem
//! (kernel definitional equality against the ground-truth constructor form),
//! and the whole corpus was oracle-checked against Lean v4.30.0-rc2: every
//! positive decl is accepted by Lean, both negative probes are rejected.
//!
//! Covered arms of `elabSubst` (`Lean/Elab/BuiltinNotation.lean:457`):
//! * expected-type branch, rhs-occurrence (no symm) — `t_id`, `t_motive`, `w2`
//! * expected-type branch, lhs-only → symm + swap    — `t_fwd`, `t_rev`, `w3`
//! * BOTH sides occur → rhs abstracted FIRST         — `bothCast`, `bc`
//! * value's-type pre-cast (the `hTypeAbst` catch)   — `bothCastPre`
//! * no-expected-type branch (lhs first)             — `inferCast`
//! * z-probes: no-occurrence and non-equality LHS are rejected LOUDLY
//! * audit row b01 (`h ▸ rfl`) = `t_fwd`; row b02 (`▸` motive) = `t_motive`

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Indexed carrier for computational casts: the payload `k` rides along the
/// index `n`, so a cast that loses or misroutes the value is caught by the
/// `rfl` value pins below.
const W_PRELUDE: &str = "
inductive W : Nat -> Type where
  | mk : (k : Nat) -> (n : Nat) -> W n
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

/// Every declaration must be axiom-free down to the bedrock — in particular
/// NO sorry axiom may back any `▸` elaboration (the never-silently-wrong bar).
fn assert_bedrock(env: &Environment, short_names: &[&str]) {
    for short in short_names {
        let name = env
            .constants()
            .map(|c| &c.name)
            .find(|n| n.last_component().as_deref() == Some(*short))
            .cloned()
            .unwrap_or_else(|| panic!("`{short}` was not registered"));
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("{name}: axiom_deps returned None"));
        assert!(
            deps.is_empty(),
            "{name} must rest on zero axioms (no sorry, no domain axioms), got: {deps:?}"
        );
    }
}

#[test]
fn test_subst_proof_positions_both_orientations_kernel_check() {
    let src = format!(
        "{W_PRELUDE}
-- audit row b01: `h ▸ rfl` (expected type contains only the LHS → symm path)
theorem t_fwd (a b : Nat) (h : a = b) : b = a := h ▸ rfl
-- rhs-occurrence path, no symm
theorem t_id (a b : Nat) (h : a = b) : a = b := h ▸ rfl
-- audit row b02: `▸` with a real motive (p b from p a)
theorem t_motive (p : Nat -> Prop) (a b : Nat) (h : a = b) (hp : p a) : p b := h ▸ hp
-- reversed orientation in a proof position (expected mentions only lhs)
theorem t_rev (p : Nat -> Prop) (a b : Nat) (h : a = b) (hp : p b) : p a := h ▸ hp
-- nested/chained subst, right-associative `▸`
theorem t_chain (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := h2 ▸ h1 ▸ rfl
"
    );
    let env = elaborate_module(&src).expect("proof-position ▸ corpus must elaborate");
    assert_bedrock(&env, &["t_fwd", "t_id", "t_motive", "t_rev", "t_chain"]);
}

#[test]
fn test_subst_computational_cast_forward_value_preserved() {
    let src = format!(
        "{W_PRELUDE}
def two : Nat := 2
theorem h2 : two = 2 := rfl
def w1 : W two := W.mk 41 two
-- cast along h2 : two = 2 into the rhs-shaped expected type W 2
def w2 : W 2 := h2 ▸ w1
-- VALUE pin: the cast must reduce to the original payload at the new index.
theorem w2_val : w2 = W.mk 41 2 := rfl
"
    );
    let env = elaborate_module(&src).expect("forward computational cast must elaborate");
    assert_bedrock(&env, &["h2", "w2", "w2_val"]);
}

#[test]
fn test_subst_computational_cast_reversed_equation_value_preserved() {
    let src = format!(
        "{W_PRELUDE}
def two : Nat := 2
def w1 : W two := W.mk 41 two
-- REVERSED equation: 2 = two. The expected type `W 2` mentions only the LHS,
-- so the elaborator must symm the equation and swap the sides (Lean
-- elabSubst:481-485). A wrong-orientation motive would demand `v : W 2`
-- instead of accepting w1 : W two, or produce a stuck cast.
theorem h2r : 2 = two := rfl
def w3 : W 2 := h2r ▸ w1
theorem w3_val : w3 = W.mk 41 2 := rfl
-- `h.symm ▸ v`: the reversed equation written via dot notation. Here the
-- expected type `W two` mentions only the RHS of `h2.symm : 2 = two`, so this
-- exercises the rhs-first arm with a symm-ed equation term.
theorem h2 : two = 2 := rfl
def w5 : W two := h2.symm ▸ W.mk 43 2
theorem w5_val : w5 = W.mk 43 two := rfl
"
    );
    let env = elaborate_module(&src).expect("reversed-equation cast (symm path) must elaborate");
    assert_bedrock(&env, &["h2r", "w3", "w3_val", "w5", "w5_val"]);
}

#[test]
fn test_subst_expected_type_contains_both_sides_rhs_abstracted_first() {
    let src = format!(
        "{W_PRELUDE}
def two : Nat := 2
theorem h2 : two = 2 := rfl
-- The expected type `W (a + b)` contains BOTH lhs (a) and rhs (b). Lean
-- abstracts the rhs occurrences FIRST, so the cast source is W (a + a) — a
-- lhs-first orientation would demand W (b + b) and reject this v. This decl
-- is the discriminator that pins the rhs-first search.
def bothCast (a b : Nat) (h : a = b) (v : W (a + a)) : W (a + b) := h ▸ v
-- The pre-cast catch path (elabSubst:490-505): v sits at W (b + b), which the
-- direct check rejects; the value's own type mentions rhs, so the value is
-- pre-cast backwards along symm h and then cast forward. Lean accepts this.
def bothCastPre (a b : Nat) (h : a = b) (v : W (b + b)) : W (a + b) := h ▸ v
-- VALUE pin at a concrete instantiation.
def bc : W (two + 2) := bothCast two 2 h2 (W.mk 7 (two + two))
theorem bc_val : bc = W.mk 7 (two + 2) := rfl
"
    );
    let env = elaborate_module(&src).expect("both-sides ▸ casts must elaborate rhs-first");
    assert_bedrock(&env, &["bothCast", "bothCastPre", "bc", "bc_val"]);
}

#[test]
fn test_subst_no_expected_type_transports_value_type_forward() {
    let src = format!(
        "{W_PRELUDE}
-- No expected type: the result type is inferred by abstracting the VALUE's
-- type at lhs and transporting forward (elabSubst:524-537, lhs first).
def inferCast (a b : Nat) (h : a = b) (v : W a) := h ▸ v
-- Pin the inferred result type: it must be W b (not W a).
def inferCastUse (a b : Nat) (h : a = b) (v : W a) : W b := inferCast a b h v
"
    );
    let env = elaborate_module(&src).expect("no-expected-type ▸ must infer the transported type");
    assert_bedrock(&env, &["inferCast", "inferCastUse"]);
}

#[test]
fn test_subst_no_occurrence_rejected_loudly() {
    let src = format!(
        "{W_PRELUDE}
def zNoOcc (a b c : Nat) (h : a = b) (v : W c) : W c := h ▸ v
"
    );
    let err = elaborate_module(&src)
        .expect_err("▸ with an expected type mentioning neither equality side must be rejected");
    assert!(
        err.contains('\u{25b8}'),
        "rejection must be the loud subst diagnostic, got: {err}"
    );
}

#[test]
fn test_subst_non_equality_equation_rejected_loudly() {
    let src = format!(
        "{W_PRELUDE}
def zNotEq (a b : Nat) (v : W a) : W a := a ▸ v
"
    );
    // A non-equality LHS cannot have subst semantics; the arm yields to the
    // generic application path, which must fail loudly (never a sorry, never
    // a silently wrong term).
    elaborate_module(&src).expect_err("▸ with a non-equality left operand must be rejected loudly");
}
