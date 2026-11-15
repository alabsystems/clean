// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end pins for **`simp` reducing a projection node**
//! (`Proj(S, i, S.mk … v …)` — proj-of-constructor iota).
//!
//! ## The gap
//!
//! `simp [Class.field]` delta-unfolds the field accessor by substituting its
//! VALUE (`simp/lemmas.rs::resolve_unfold_defs` stores `name -> body`,
//! `simp/expr.rs::unfold_named_consts` folds it in). A class field's body is a
//! projection, so `Class.field inst x` becomes the kernel node
//! `Proj(Class, i, inst) x` — and nothing in `tactic/simp/` ever reduced that
//! node. The only `Proj` arm in the traversal re-simplified the structure
//! argument and rebuilt the projection by congruence; there was no iota step
//! anywhere, so the goal stuck even when the structure argument was already a
//! LITERAL constructor application.
//!
//! Measured at Mathlib (`Mathlib/Order/Basic.lean`, `compl_lt`/`compl_le`/
//! `compl_gt`/`compl_ge`): `simp [Compl.compl]` unfolded to
//! `Compl.0.(Pi.instCompl A …) (LT.lt …)` and stopped there. Because the stuck
//! term is FUNCTION-valued there is not even a binder for simp to descend
//! under, so `not_lt`/`not_not` could never fire.
//!
//! ## What Lean does
//!
//! `simpProj` (`Lean/Meta/Tactic/Simp/Main.lean:299`) dispatches a `.proj`
//! node to `reduceProj?` (`Lean/Meta/WHNF.lean:580-583`), which whnf's the
//! structure argument and reads out field `i`. The reduction runs at
//! reducible+instances transparency, never at full transparency — Main.lean's
//! own comment records that `simp [X.x]` legitimately LEAVES `(instX a').1`
//! stuck when the structure argument is not a constructor application there.
//! The refusal controls below pin exactly that ceiling.

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

/// A one-field class whose instance is a named constant — the shape every
/// Mathlib order instance has, minus the imports.
const SETUP: &str = concat!(
    "class Cmpl (A : Type) where\n",
    "  cmpl : A -> A\n",
    "axiom Kk : Nat -> Nat\n",
    "axiom Jj : Nat -> Nat\n",
    "axiom kEq : forall (n : Nat), Kk n = n\n",
    "axiom kJ : forall (n : Nat), Kk n = Jj n\n",
    "instance instCmplNat : Cmpl Nat where\n",
    "  cmpl := fun n => Kk n\n",
);

/// A class whose field is FUNCTION-valued, so the stuck projection has no
/// binder under it — `Mathlib`'s `Compl.compl` exactly.
const SETUP_FN: &str = concat!(
    "class Cop (A : Type) where\n",
    "  cop : (A -> Prop) -> (A -> Prop)\n",
    "axiom Pp : Nat -> Prop\n",
    "axiom Qq : Prop -> Prop\n",
    "axiom qEq : forall (p : Prop), Qq p = p\n",
    "instance instCopNat : Cop Nat where\n",
    "  cop := fun f => fun a => Qq (f a)\n",
);

/// CONTROL, and the reason the Mathlib rows are all FUNCTION-valued: at a
/// SCALAR field the reduction is not needed and was never the gap.
///
/// MEASURED at the parent commit — this arm PASSES there, and
/// `CLEAN_SIMP_REWRITE_TRACE=1` says why: `simp-rewrite: lemma=kJ
/// from=App(Proj(Cmpl, 0, Const(instCmplNat)), FVar(0)) to=App(Const(Jj),
/// FVar(0))`. The matcher's own def-eq sees THROUGH the stuck projection and
/// unifies `Kk ?n` with the whole node, so the rewrite fires with the node
/// still unreduced. That only works because the lemma matches the node
/// ITSELF; when the projected field is a function the lemma has to match a
/// subterm that does not EXIST until the projection reduces, which is the
/// gap pinned below.
///
/// Kept because the reduction must not break this path: a rewrite that fired
/// through def-eq before must still fire.
#[test]
fn test_simp_reduces_projection_of_named_instance() {
    expect_registers(&format!(
        "{SETUP}theorem t_proj (n : Nat) : Cmpl.cmpl n = Jj n := by simp [Cmpl.cmpl, kJ]\n"
    ));
}

/// CONTROL: the same shape under `simp only`, where there is no default simp
/// set to fall back on — only the unfold, the projection reduction and the
/// one named lemma. Also passes at the parent commit, for the reason above;
/// its value is that it pins the `simp only` path separately.
#[test]
fn test_simp_only_reduces_projection_of_named_instance() {
    expect_registers(&format!(
        "{SETUP}theorem t_only (n : Nat) : Cmpl.cmpl n = Jj n := by simp only [Cmpl.cmpl, kJ]\n"
    ));
}

/// THE MATHLIB SHAPE: the projected field is a FUNCTION, so nothing can be
/// rewritten until the projection itself reduces — there is not even a binder
/// for simp to descend under. This is `Compl.compl` exactly.
///
/// MEASURED at the parent commit: leaves
/// `⊢ Cop.0.instCopNat Pp fvar#0 = Pp fvar#0`, the stuck face the diagnosis
/// recorded at `Mathlib/Order/Basic.lean`.
#[test]
fn test_simp_reduces_function_valued_projection() {
    expect_registers(&format!(
        "{SETUP_FN}theorem t_fn (n : Nat) : Cop.cop Pp n = Pp n := by simp [Cop.cop, qEq]\n"
    ));
}

/// CEILING CONTROL: a projection whose structure argument is a goal LOCAL
/// must stay UNREDUCED. That is the `BEq.beq inst a b` shape the simp lemma
/// registry indexes on, and Lean leaves it stuck too.
#[test]
fn test_simp_leaves_projection_on_a_local_instance_unreduced() {
    expect_fails(
        &format!(
            "{SETUP}theorem t_fvar (inst : Cmpl Nat) (n : Nat) : @Cmpl.cmpl Nat inst n = Kk n := by simp [Cmpl.cmpl, kEq]\n"
        ),
        "a projection on a LOCAL instance must not reduce",
    );
}

/// CEILING CONTROL: without the unfold request there is no projection node at
/// all — the head is still the `Cmpl.cmpl` constant — so nothing reduces and
/// the goal is left alone, as in Lean.
#[test]
fn test_simp_without_the_unfold_request_makes_no_progress() {
    expect_fails(
        &format!("{SETUP}theorem t_nounfold (n : Nat) : Cmpl.cmpl n = Jj n := by simp [kJ]\n"),
        "`simp [kJ]` alone must not unfold the class projection",
    );
}

/// SOUNDNESS GATE: the reduction is definitional, so it can only expose more
/// rewrites — never prove something false. With only `kEq : Kk n = n`
/// offered, the reduced goal is `n = Jj n`; `Jj` is opaque and no offered
/// lemma mentions it, so this must not close. Ground-truthed against the
/// pinned `lean` v4.30.0-rc2, which leaves `n = Jj n` unsolved.
///
/// `Kk (Kk n)` was the first candidate here and is the wrong one: `kEq`
/// rewrites it to `n` as well, so the goal is TRUE and both Lean and Clean
/// close it. A soundness gate has to be false to be a gate.
#[test]
fn test_simp_projection_reduction_does_not_close_a_false_goal() {
    expect_fails(
        &format!(
            "{SETUP}theorem t_false (n : Nat) : Cmpl.cmpl n = Jj n := by simp [Cmpl.cmpl, kEq]\n"
        ),
        "projection reduction must not make an underivable goal provable",
    );
}
