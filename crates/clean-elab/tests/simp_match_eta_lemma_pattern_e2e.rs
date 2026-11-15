//! End-to-end pins for **simp normalizing a lemma pattern by ETA** before
//! matching it.
//!
//! ## The gap
//!
//! `simp_expr_inner` eta-reduces the goal subterm (`config.eta`) and nothing
//! ever eta-reduced the LEMMA's stored LHS, so the two sides reached the
//! first-order matcher normalized by different steps.
//!
//! The unifier does have an eta arm (`unify/unifier/unify_expr.rs`,
//! `eta_expand_other`), but it reads the non-lambda side's domain out of
//! `tc.infer_type(other)` and simp's matcher builds its unifier over an EMPTY
//! kernel local context — so for ANY goal-local function that call answers
//! `UnknownFVar`, the arm returns `None` and falls through to
//! `try_kernel_def_eq`, which cannot assign a metavariable. The candidate then
//! died as a shape bail:
//!
//! ```text
//! cannot unify a lambda with a free variable: fun (x : ?p) => ?x x vs fvar#3
//! ```
//!
//! This bites every imported lemma whose LHS came from
//! `if h : p then x h else y`, because that notation elaborates the then-branch
//! ETA-EXPANDED. Measured row:
//! `Mathlib/Logic/Basic.lean:dite_ne_right_iff`.
//!
//! ## The fix, and the one that was tried first
//!
//! Reducing the pattern makes the eta arm unnecessary instead of making it
//! work: `fun h => ?x h` contracts to `?x`, which the matcher assigns
//! directly. Handing the unifier the GOAL'S LOCAL CONTEXT — what the diagnosis
//! proposed, and what Lean's `isDefEqEta` effectively does, inferring in the
//! ambient `MetaM` lctx — was implemented, measured, and REVERTED: it
//! regressed nine universe-polymorphic lemma-matching tests (527 passed /
//! 0 failed before, 518 / 9 after), because `propagate_meta_type_levels` and
//! `expr_sort_level` also bail on a failed `infer_type`, so a context that
//! types goal locals silently switches level propagation on for every match.
//! That is a change to LEVEL SOLVING and needs its own measurement.
//!
//! ## The discriminating A/B
//!
//! The two arms below differ ONLY in whether the `dite` then-branch is a goal
//! LOCAL or a global CONSTANT. The constant arm passed all along (an empty
//! context can still type a global), which is why the gap was invisible.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn expect_registers(source: &str) {
    if let Err(e) = try_elaborate(source) {
        panic!("must elaborate and kernel-register, got: {e}\n--- source ---\n{source}");
    }
}

fn expect_fails(source: &str, why: &str) {
    if try_elaborate(source).is_ok() {
        panic!("{why}\n--- source ---\n{source}");
    }
}

/// `diteEqRight` is spelled the way `if h : p then x h else y` really
/// elaborates — an ETA-EXPANDED then-branch. A version written `x` bare
/// matched all along, which is exactly why a matcher tested against
/// hand-built patterns was untested against its one production shape.
const SETUP: &str = concat!(
    "axiom Pp : Prop\n",
    "axiom instPp : Decidable Pp\n",
    "axiom Aq : Pp -> Nat\n",
    "axiom diteEqRight : forall (x : Pp -> Nat) (y : Nat),\n",
    "  (@dite Nat Pp instPp (fun h => x h) (fun _ => y) = y) ↔ (forall (h : Pp), x h = y)\n",
);

/// THE GAP: the `dite` then-branch is the goal LOCAL `A`, so matching the
/// lemma needs `fun h => ?x h =?= A` — the eta arm, which needs `A`'s type.
#[test]
fn test_simp_eta_matches_a_goal_local_function() {
    expect_registers(&format!(
        "{SETUP}theorem t_local (A : Pp -> Nat) (b : Nat) :\n\
         \x20   (@dite Nat Pp instPp A (fun _ => b) = b) ↔ (forall (h : Pp), A h = b) := by\n\
         \x20 simp [diteEqRight]\n"
    ));
}

/// CONTROL (the A/B partner): the same shape with a GLOBAL constant in the
/// then-branch passed before the fix and must keep passing.
#[test]
fn test_simp_eta_matches_a_global_constant_function() {
    expect_registers(&format!(
        "{SETUP}theorem t_const (b : Nat) :\n\
         \x20   (@dite Nat Pp instPp Aq (fun _ => b) = b) ↔ (forall (h : Pp), Aq h = b) := by\n\
         \x20 simp [diteEqRight]\n"
    ));
}

/// SOUNDNESS GATE: handing the matcher the goal's locals widens which
/// candidates are OFFERED; every rewrite is still proof-checked and
/// kernel-rechecked. A goal the lemma does not prove must still fail.
#[test]
fn test_simp_eta_match_does_not_close_a_false_goal() {
    expect_fails(
        &format!(
            "{SETUP}theorem t_false (A : Pp -> Nat) (b : Nat) :\n\
             \x20   (@dite Nat Pp instPp A (fun _ => b) = b) ↔ (forall (h : Pp), A h = Nat.succ b) := by\n\
             \x20 simp [diteEqRight]\n"
        ),
        "the eta match must not close a goal the lemma does not prove",
    );
}
