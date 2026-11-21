// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end regression coverage for work package PKG4 (the unifier):
//!
//! 1. `Unifier::unify_meta` as a port of Lean's `processAssignment` — the
//!    `ctxApprox` arm of `CheckAssignment.checkMVar`
//!    (`Lean/Meta/ExprDefEq.lean:856-890`) and `checkTypesAndAssign`
//!    (`:457-472`).
//! 2. The App/App arm reducing an application's function part (and a flex
//!    application's partner) before comparing it, where Lean compares the
//!    parts as written first (`isDefEqApp`, `tryHeuristic`,
//!    `processAssignment`).
//! 3. An unannotated `fun x =>` binder minted at `Type` instead of Lean's
//!    `Sort ?u` (`Lean/Elab/Binders.lean` `elabFunBinderViews` → `elabType`,
//!    `Lean/Elab/Term/TermElabM.lean` `elabType`).
//!
//! Every fixture below was ground-truthed on the pinned toolchain
//! (`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`, builtin
//! `Init` only): Lean accepts every declaration this file expects to
//! elaborate. The controls are declarations Clean accepted before the fix;
//! they keep a regression that makes EVERYTHING fail from passing as a
//! repair of the rows.

use crate::tactic::builtins::builtin_tactic_patterns;
use crate::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, ElabResult,
    FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file_with_tactics;

/// Elaborate `src` declaration by declaration into `env`, threading one
/// `FileContext` through the same preprocess-then-elaborate loop `clean
/// check` runs (so `universe`, `namespace`, `section` and `variable` persist),
/// and return the first failure as its `Debug` rendering together with the
/// index of the declaration that produced it.
///
/// A `namespace`/`section` block returns `Ok(Multiple(..))` even when one of
/// its members failed — the failure is an `ElabResult::Failed` LEAF, not an
/// `Err` (see `lean4_corpus_tests::assert_all_ok`) — so every leaf is walked;
/// checking only the outer `Result` passes a block whose members failed.
pub(crate) fn elab_into(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    src: &str,
) -> Option<String> {
    let patterns = builtin_tactic_patterns();
    let decls = parse_file_with_tactics(src, &patterns)
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}\n{src}"));
    for (index, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, file_ctx);
        match elaborate_decl_and_register_with_context_and_warning(env, &processed, file_ctx) {
            Err(e) => return Some(format!("declaration #{index}: {e:?}")),
            Ok(registered) => {
                let mut leaves = Vec::new();
                registered.result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    if let ElabResult::Failed { name, error, .. } = leaf {
                        return Some(format!("declaration #{index}, member `{name}`: {error:?}"));
                    }
                }
            }
        }
    }
    None
}

/// Elaborate `base` (which must succeed) and then `target`, returning the
/// target's first failure, or `None` when every target declaration
/// elaborated and passed the kernel re-check.
pub(crate) fn elab_after(base: &str, target: &str) -> Option<String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    if let Some(e) = elab_into(&mut env, &mut file_ctx, base) {
        panic!("the shared fixture base must elaborate, got: {e}");
    }
    elab_into(&mut env, &mut file_ctx, target)
}

pub(crate) fn assert_elaborates(base: &str, target: &str, label: &str) {
    if let Some(e) = elab_after(base, target) {
        panic!("{label} must elaborate and kernel-check (pinned Lean accepts it), got: {e}");
    }
}

/// The harness itself: a failure inside a `namespace … end` block is an
/// `ElabResult::Failed` leaf of an `Ok` result, and `assert_elaborates` must
/// still report it. Without the leaf walk this test does not panic and so
/// FAILS — a harness that only reads the outer `Result` passed the C2 rows'
/// `leftInverse_iff_comp` while `clean check` reported it failed.
#[test]
#[should_panic(expected = "member `NsMask.bad`")]
fn test_harness_sees_failure_inside_namespace_block() {
    assert_elaborates(
        "",
        "namespace NsMask\ndef bad : Nat := Bool.true\nend NsMask\n",
        "harness self-test",
    );
}

// ---------------------------------------------------------------------------
// Root cause 1: `unify_meta` is a partial port of `processAssignment`.
// ---------------------------------------------------------------------------

/// The shape of `Mathlib/Logic/Function/Basic.lean`'s function-property
/// definitions, over RIGID universes so no fixture can pass by silently
/// monomorphising a level.
const FN_BASE: &str = "\
universe u v w
def Fn.Injective {α : Sort u} {β : Sort v} (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
def Fn.Surjective {α : Sort u} {β : Sort v} (f : α → β) : Prop := ∀ b, Exists fun a => f a = b
def Fn.Bijective {α : Sort u} {β : Sort v} (f : α → β) : Prop := Fn.Injective f ∧ Fn.Surjective f
def Fn.LeftInverse {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
def Fn.RightInverse {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop := Fn.LeftInverse f g
theorem Fn.LeftInverse.injective {α : Sort u} {β : Sort v} {g : β → α} {f : α → β}
    (h : Fn.LeftInverse g f) : Fn.Injective f :=
  fun a b faeqfb => ((h a).symm.trans (congrArg g faeqfb)).trans (h b)
theorem Fn.RightInverse.surjective {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}
    (h : Fn.RightInverse g f) : Fn.Surjective f :=
  fun y => ⟨g y, h y⟩
theorem Fn.LeftInverse.rightInverse {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}
    (h : Fn.LeftInverse g f) : Fn.RightInverse f g := h
theorem Fn.RightInverse.leftInverse {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}
    (h : Fn.RightInverse g f) : Fn.LeftInverse f g := h
axiom Fn.surjInv {α : Sort u} {β : Sort v} {f : α → β} (h : Fn.Surjective f) (b : β) : α
axiom Fn.leftInverse_surjInv {α : Sort u} {β : Sort v} {f : α → β} (hf : Fn.Bijective f) :
    Fn.LeftInverse (Fn.surjInv hf.2) f
axiom Fn.rightInverse_surjInv {α : Sort u} {β : Sort v} {f : α → β} (hf : Fn.Surjective f) :
    Fn.RightInverse (Fn.surjInv hf) f
def Fn.extend {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β) (g : α → γ) (j : β → γ) :
    β → γ := fun b => j b
";

/// CONTROL: the annotated existential binder never needed `ctxApprox`.
#[test]
fn test_ctx_approx_annotated_exists_binder_control_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_stmt_ctl {α : Sort u} {β : Sort v} {f : α → β}\n    \
         (h : ∃ g : β → α, Fn.LeftInverse g f) : True := True.intro\n",
        "control: `∃ g : β → α, LeftInverse g f`",
    );
}

/// CONTROL: `dite`'s result type supplied by hand, so every lambda has an
/// expected Pi and no binder type is an outer metavariable. (The instance is
/// named rather than written `_`: an explicit `_` in an instance slot is a
/// separate, unrelated gap of this tree.)
#[test]
fn test_ctx_approx_dite_with_explicit_motive_control_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_or_not_ctl {a b : Prop} [inst : Decidable a] (h : a → b) : b ∨ ¬a :=\n  \
         @dite (b ∨ ¬a) a inst (fun x => Or.inl (h x)) (fun y => Or.inr y)\n",
        "control: `@dite (b ∨ ¬a) …`",
    );
}

/// C1, the minimal face: the untyped `∃ g` binder's type is an OUTER
/// metavariable `?T`; `LeftInverse`'s implicit type arguments `?α ?β` are
/// minted INSIDE the binder, so `?T =?= ?β → ?α` asks an outer metavariable
/// to hold two inner ones. Lean restricts `?α ?β` to `?T`'s context
/// (`ctxApprox`); Clean returned `Stuck`, reported as `Cannot infer type`.
#[test]
fn test_ctx_approx_untyped_exists_binder_against_inner_implicits_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_stmt_only {α : Sort u} {β : Sort v} {f : α → β}\n    \
         (h : ∃ g, Fn.LeftInverse g f) : True := True.intro\n",
        "row `Function.bijective_iff_has_inverse`'s statement (`∃ g, LeftInverse g f`)",
    );
}

/// C1, the row `Function.bijective_iff_has_inverse` verbatim (modulo the
/// section variables, spelled as binders).
#[test]
fn test_ctx_approx_bijective_iff_has_inverse_row_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_bijective_iff_has_inverse {α : Sort u} {β : Sort v} {f : α → β} :\n    \
         Fn.Bijective f ↔ ∃ g, Fn.LeftInverse g f ∧ Fn.RightInverse g f :=\n  \
         ⟨fun hf => ⟨_, Fn.leftInverse_surjInv hf, Fn.rightInverse_surjInv hf.2⟩,\n   \
         fun ⟨_, gl, gr⟩ => ⟨gl.injective, gr.surjective⟩⟩\n",
        "row `Function.bijective_iff_has_inverse`",
    );
}

/// C1, the row `Function.extend_injective`'s statement: `fun g ↦ extend f g
/// e'` — the lambda binder's type against `extend`'s `γ`, minted in the body.
#[test]
fn test_ctx_approx_untyped_lambda_binder_against_inner_implicit_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_extend_stmt {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}\n    \
         (e' : β → γ) (h : Fn.Injective fun g => Fn.extend f g e') : True := True.intro\n",
        "row `Function.extend_injective`'s statement",
    );
}

/// C1, the row `eq_rec_on_bijective`: the `·` binder's type against an inner
/// `_` hole (`?T =?= C ?h`). The row's STATEMENT is pinned (with `sorry`),
/// and the same `·`-against-`_` shape with a term proof.
///
/// The row's own proof, `| _, _, rfl => …`, then meets a SEPARATE wall:
/// `Unknown free variable` from the equation compiler, which the fully
/// explicit spelling `@Eq.ndrec α a C x a' h` — no hole, nothing for
/// `ctxApprox` to do — hits identically on the pre-fix binary. It is not this
/// root cause and is not pinned here.
#[test]
fn test_ctx_approx_cdot_binder_against_inner_hole_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_eq_rec_on_bijective {α : Sort u} {C : α → Sort v} :\n    \
         ∀ {a a' : α} (h : a = a'), Fn.Bijective (@Eq.ndrec _ _ C · _ h) := sorry\n\
         theorem c1_eq_rec_refl {α : Sort u} {C : α → Sort v} {a : α} :\n    \
         Fn.Bijective (@Eq.ndrec _ _ C · _ (Eq.refl a)) :=\n  \
         ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩\n",
        "row `eq_rec_on_bijective` (statement) and its `Eq.refl` instance",
    );
}

/// C1, the row `Decidable.or_not_of_imp`: `Or.inl ∘ h` is a lambda whose
/// binder type is `dite`'s outer `?α`-side metavariable, while `Or.inl`'s
/// implicit is minted inside it (`Or b ?m =?= ?T`). The verifier measured
/// that the propagation gates alone cannot clear this row; `ctxApprox` does.
#[test]
fn test_ctx_approx_dite_with_composed_branch_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c1_or_not_of_imp {a b : Prop} [Decidable a] (h : a → b) : b ∨ ¬a :=\n  \
         dite _ (Or.inl ∘ h) Or.inr\n",
        "row `Decidable.or_not_of_imp`",
    );
}

/// C1, the diagnoser's OTHER reading of that row, measured rather than
/// argued: an instance-implicit binder in the MIDDLE of the spine
/// (`(c : Prop) [Decidable c] (t : c → α) …`) with explicit `fun` branches.
/// The expected-type pre-pinning gates walk one Pi binder per surface
/// argument and so never pin `α` here (Lean's `getForallBody` skips
/// non-explicit binders), which left the branch binder an outer metavariable:
/// on main's frozen binary `n2` dies `Cannot infer type` while `n1` — the same
/// axiom without the instance binder — passes. `ctxApprox` clears it without
/// touching the gates; both are pinned so a later gate change cannot trade one
/// for the other.
#[test]
fn test_ctx_approx_midspine_instance_binder_elaborates() {
    assert_elaborates(
        "universe u\n\
         axiom mydite0 {α : Sort u} (c : Prop) (t : c → α) (e : ¬c → α) : α\n\
         axiom mydite1 {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : ¬c → α) : α\n",
        "theorem n1 {a b : Prop} (h : a → b) : b ∨ ¬a :=\n  \
         mydite0 a (fun ha => Or.inl (h ha)) (fun hn => Or.inr hn)\n\
         theorem n2 {a b : Prop} [Decidable a] (h : a → b) : b ∨ ¬a :=\n  \
         mydite1 a (fun ha => Or.inl (h ha)) (fun hn => Or.inr hn)\n\
         theorem o2 {a b : Prop} [Decidable a] (h : a → b) : b ∨ ¬a :=\n  \
         mydite1 _ (Or.inl ∘ h) Or.inr\n",
        "a mid-spine `[Decidable c]` binder before the branches",
    );
}

/// C2, the row `Function.LeftInverse.surjective`: `h.rightInverse` solves
/// `?g`/`?f` of `RightInverse.surjective` by δ-unfolding, and the type
/// implicit that occurs only in `?g : ?β → ?α` was never assigned — Lean's
/// `checkTypesAndAssign` unifies `?g`'s type with `g`'s and solves it.
#[test]
fn test_check_types_and_assign_leftinverse_surjective_row_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c2_leftInverse_surjective {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : Fn.LeftInverse f g) : Fn.Surjective f :=\n  h.rightInverse.surjective\n",
        "row `Function.LeftInverse.surjective`",
    );
}

/// C2, the row `Function.RightInverse.injective`.
#[test]
fn test_check_types_and_assign_rightinverse_injective_row_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c2_rightInverse_injective {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : Fn.RightInverse f g) : Fn.Injective f :=\n  h.leftInverse.injective\n",
        "row `Function.RightInverse.injective`",
    );
}

/// C2, minimal: no definition is unfolded and no `∘` occurs. Applying `ce3`
/// to `h : ∀ x, f (g x) = x` solves `?f := f` and `?g := g` structurally;
/// `?α` occurs only in their TYPES and needs `checkTypesAndAssign`.
#[test]
fn test_check_types_and_assign_implicit_only_in_meta_types_elaborates() {
    assert_elaborates(
        FN_BASE,
        "theorem c2_ce3 {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : ∀ x, f (g x) = x) : @Eq (β → β) (fun x => f (g x)) id := funext h\n\
         theorem c2_v6d {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : ∀ x, f (g x) = x) : @Eq (β → β) (fun x => f (g x)) id := c2_ce3 h\n",
        "minimal C2 face `v6d`",
    );
}

// ---------------------------------------------------------------------------
// Root cause 2: the unifier reduced the function part (and a flex
// application's partner) of an application before comparing it.
// ---------------------------------------------------------------------------

/// A `Preorder`/`LinearOrder` shape whose `<`/`min` are PROJECTION functions:
/// the WHNF of `LT.lt ?α X ?a` is `X.1 ?a`, which drops `?α`.
const ORDER_BASE: &str = "\
class Preorder1 (α : Type) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
axiom not_lt_iff_zz0 {α : Type} [Preorder1 α] {a b : α} : ¬a < b ↔ ¬a ≤ b ∨ b ≤ a
class LinOrd2 (α : Type) extends LE α, Min α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
axiom min_eq_left_zz {α : Type} [inst : LinOrd2 α] {a b : α}
    (h : @LE.le α (@LinOrd2.toLE α inst) a b) : @Min.min α (@LinOrd2.toMin α inst) a b = a
";

/// Row `not_lt_iff_le_imp_ge`'s face (`Mathlib/Order/Basic.lean`): matching
/// `¬ ?a < ?b` reduced `LT.lt ?α X ?a` to `X.1 ?a`, never assigned `?α`, and
/// `simp` refused the match (`lhs-meta-leak`) and made no progress.
#[test]
fn test_unreduced_head_simp_matches_projection_function_lt() {
    assert_elaborates(
        ORDER_BASE,
        "theorem r28c {α : Type} [Preorder1 α] {a b : α} : ¬ a < b ↔ ¬a ≤ b ∨ b ≤ a := by\n  \
         simp only [not_lt_iff_zz0]\n",
        "row `not_lt_iff_le_imp_ge` (`¬a < b` through the projection function)",
    );
}

/// Row `min_rec`'s face: `simp only [min_eq_left, hab]` made no progress on
/// `Min.min α (LinearOrder.toMin α inst) a b = a` — the Mathlib spelling
/// through the parent-projection FUNCTION.
#[test]
fn test_unreduced_head_simp_matches_projection_function_min() {
    assert_elaborates(
        ORDER_BASE,
        "theorem r30m {α : Type} [inst : LinOrd2 α] {a b : α}\n    \
         (hab : @LE.le α (@LinOrd2.toLE α inst) a b) :\n    \
         @Min.min α (@LinOrd2.toMin α inst) a b = a := by\n  \
         simp only [min_eq_left_zz, hab]\n",
        "row `min_rec` (`min` through the parent projection function)",
    );
}

/// A flex application against a DEFINED head: `?g (f x) =?= surjInv h (f x)`.
/// Reducing `surjInv h (f x)` first split it first-order against the unfolded
/// body and captured the bound `x` (`?g := chooseAx (fun a => f a = f x)`);
/// Lean solves `?g := surjInv h`. This is the wall
/// `Function.bijective_iff_has_inverse` meets once its statement elaborates.
#[test]
fn test_unreduced_head_flex_application_against_defined_head() {
    assert_elaborates(
        "universe u v\n\
         def Fn.Surjective {α : Sort u} {β : Sort v} (f : α → β) : Prop := \
         ∀ b, Exists fun a => f a = b\n\
         def Fn.LeftInverse {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop := \
         ∀ x, g (f x) = x\n\
         axiom Fn.chooseAx {α : Sort u} {p : α → Prop} (h : Exists p) : α\n\
         noncomputable def Fn.surjInv {α : Sort u} {β : Sort v} {f : α → β} \
         (h : Fn.Surjective f) (b : β) : α := Fn.chooseAx (h b)\n\
         axiom Fn.leftInverse_surjInv {α : Sort u} {β : Sort v} {f : α → β} \
         (hf : Fn.Surjective f) : Fn.LeftInverse (Fn.surjInv hf) f\n",
        "theorem flex_def {α : Sort u} {β : Sort v} {f : α → β} (hf : Fn.Surjective f) :\n    \
         ∃ g : β → α, Fn.LeftInverse g f :=\n  ⟨_, Fn.leftInverse_surjInv hf⟩\n",
        "`?g (f x) =?= surjInv h (f x)`",
    );
}

/// The FALLBACK half: a failed unreduced attempt is rolled back before the
/// historical reduced comparison runs. `sel2 ?x ?x =?= sel2 1 2` compared
/// argument by argument assigns `?x := 1` and then fails `1 =?= 2`; if that
/// assignment survived, the reduced comparison `?x =?= 2` (both sides
/// δ-unfold to their second argument) would fail too. Lean's lazy delta does
/// the same: `tryHeuristic` fails on the arguments, then both sides unfold.
#[test]
fn test_unreduced_head_failed_attempt_rolls_back_before_reduced_fallback() {
    assert_elaborates(
        "def sel2 (a b : Nat) : Nat := b\n\
         axiom P : Nat → Prop\n\
         axiom mk1 {x : Nat} : P (sel2 x 2)\n\
         axiom mk2 {x : Nat} : P (sel2 x x)\n",
        "theorem rb1 : P (sel2 1 2) := mk1\n\
         theorem rb2 : P (sel2 1 2) := mk2\n",
        "`sel2 ?x ?x =?= sel2 1 2` (argument-first fails, reduced succeeds)",
    );
}

// ---------------------------------------------------------------------------
// Root cause 3: an unannotated `fun x =>` binder with no expected Pi was
// minted `?T : Type` (Sort 1) instead of Lean's `?T : Sort ?u`.
// ---------------------------------------------------------------------------

const UNIVERSES: &str = "universe u v w\n";

/// CONTROLS: an expected Pi, an explicit `@Eq`, and a `_`-typed binder never
/// minted the `Type` metavariable; a Prop-valued untyped binder was accepted
/// through the `Sort`-arm's cumulativity and must stay accepted.
#[test]
fn test_untyped_binder_controls_elaborate() {
    assert_elaborates(
        UNIVERSES,
        "theorem j3 {β : Sort u} {α : Sort v} (f : α → β) (g : β → α) (h : id = f ∘ g) : True :=\n  \
         True.intro\n\
         theorem j5 {β : Sort u} {α : Sort v} (f : α → β) (g : β → α)\n    \
         (h : @Eq (β → β) (f ∘ g) id) : True := True.intro\n\
         theorem j6b {β : Sort u} (f : β → β) (h : (fun (x : _) => f x) = f) : True := True.intro\n\
         theorem tp (P : Prop) (h : P) : (fun x => x) h = h := rfl\n\
         theorem tp2 (P : Prop) (h : P) : True := (fun _ => True.intro) h\n",
        "controls j3/j5/j6b and the Prop-binder cumulativity pair tp/tp2",
    );
}

/// The rows' face, over RIGID universes: `f ∘ g` (desugared to
/// `fun x => f (g x)`) and `fun x => f x` on the LHS of `=`, where no Pi is
/// expected — `cannot assign rigid universe parameter u := 1`
/// (`Function.comp_update`, `Function.update_comp_eq_of_injective`,
/// `Function.update_comp_eq_of_injective'`, `Function.Involutive.comp_self`).
#[test]
fn test_untyped_binder_on_equation_lhs_over_rigid_sort_elaborates() {
    assert_elaborates(
        UNIVERSES,
        "theorem j1 {β : Sort u} {α : Sort v} (f : α → β) (g : β → α) (h : f ∘ g = f ∘ g) : True :=\n  \
         True.intro\n\
         theorem j4 {β : Sort u} (f : β → β) (g : β → β) (h : f ∘ g = id) : True := True.intro\n\
         theorem j6 {β : Sort u} (f : β → β) (h : (fun x => f x) = f) : True := True.intro\n",
        "`f ∘ g = …` and `(fun x => f x) = f` over `Sort u`",
    );
}

/// The rows with their proofs: `Involutive.comp_self` and the
/// `LeftInverse.comp_eq_id` shape.
#[test]
fn test_untyped_binder_comp_rows_with_proofs_elaborate() {
    assert_elaborates(
        UNIVERSES,
        "def Fn.Involutive {α : Sort u} (f : α → α) : Prop := ∀ x, f (f x) = x\n\
         theorem comp_self {α : Sort u} {f : α → α} (h : Fn.Involutive f) : f ∘ f = id := funext h\n\
         theorem comp_eq_id {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : ∀ x, f (g x) = x) : f ∘ g = id := funext h\n",
        "`Involutive.comp_self` / `LeftInverse.comp_eq_id`",
    );
}

/// The SILENT face: over a level METAVARIABLE (`Sort _`, which Mathlib's
/// `Sort*` also is here) the binder's `Type` was not refused but ASSIGNED
/// (`?u := 1`), registering a strictly weaker declaration that a later use at
/// `Prop` then fails against — the declaration was counted a success.
#[test]
fn test_untyped_binder_does_not_monomorphize_sort_metavariable() {
    assert_elaborates(
        UNIVERSES,
        "theorem t1 {α β : Sort _} (f : α → β) (g : β → α) : f ∘ g = f ∘ g := rfl\n\
         theorem useP (f : True → True) (g : True → True) : f ∘ g = f ∘ g := t1 f g\n\
         def ext0 {β γ : Sort _} (j : β → γ) : β → γ := fun b => j b\n\
         def u0 {β γ : Prop} (j : β → γ) : β → γ := ext0 j\n",
        "`t1`/`ext0` stated at `Sort _`, used at `Prop`",
    );
}

/// The rows `leftInverse_iff_comp` and `rightInverse_iff_comp` with their
/// own proofs (`⟨comp_eq_id, congrFun⟩`), over DECLARED universes — the form
/// Lean elaborates once `levelMVarToParamHeaders` has turned the header's
/// universe metavariables into parameters. On this package's base every
/// theorem here died `cannot assign rigid universe parameter v := 1`
/// (measured through `clean check`).
#[test]
fn test_pkg4_iff_comp_rows_over_declared_universes_elaborate() {
    assert_elaborates(
        UNIVERSES,
        "namespace Fy\n\
         def LeftInverse {α β} (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x\n\
         def RightInverse {α β} (g : β → α) (f : α → β) : Prop := LeftInverse f g\n\
         theorem LeftInverse.comp_eq_id {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : LeftInverse f g) : f ∘ g = id := funext h\n\
         theorem leftInverse_iff_comp {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} :\n    \
         LeftInverse f g ↔ f ∘ g = id :=\n  ⟨LeftInverse.comp_eq_id, congrFun⟩\n\
         theorem RightInverse.comp_eq_id {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}\n    \
         (h : RightInverse f g) : g ∘ f = id := funext h\n\
         theorem rightInverse_iff_comp {α : Sort u} {β : Sort v} {f : α → β} {g : β → α} :\n    \
         RightInverse f g ↔ g ∘ f = id :=\n  ⟨RightInverse.comp_eq_id, congrFun⟩\n\
         end Fy\n",
        "`leftInverse_iff_comp` / `rightInverse_iff_comp` over `Sort u` / `Sort v`",
    );
}

/// The binder-type metavariable is Lean's NATURAL one (`elabType` mints it
/// with `mkFreshTypeMVar`), so `ctxApprox` may narrow it. `∃ g, ∀ x, some x =
/// g ∧ …` asks the OUTER `g : ?G` to hold `Option ?X`, where the untyped `∀
/// x` binder's `?X` was minted inside `g`'s binder; the same through an
/// untyped `fun x` binder. Minted opaque (`fresh_meta`), `?X` could not be
/// narrowed and each statement died `CannotInfer`.
#[test]
fn test_untyped_binder_meta_is_natural_and_narrowable() {
    assert_elaborates(
        "",
        "theorem pk1 (h : ∃ g, ∀ x, some x = g ∧ x = 0) : True := True.intro\n\
         theorem pk2 (h : ∃ g, ∀ x, g = some x ∧ x = 0) : True := True.intro\n\
         theorem pk3 (h : ∃ g, (fun x => g = some x ∧ x = 0) = fun _ => True) : True :=\n  \
         True.intro\n",
        "`∃ g, ∀ x, some x = g ∧ …` and the `fun x` twin",
    );
}

/// All three root causes together, as the source-elaboration gate spells the
/// rows: `Sort _` section variables, `∘` on the left of `=`, and the C2 rows
/// `LeftInverse.surjective`, `RightInverse.injective` and `RightInverse.comp`
/// with the `comp_eq_id` lemmas the `iff_comp` rows are proved from.
///
/// `leftInverse_iff_comp` / `rightInverse_iff_comp` themselves are NOT here:
/// over a level METAVARIABLE their `congrFun` half poses `Eq.{?b} =?=
/// Eq.{imax ?u ?v}` and the drain refuses the equations that follow. Lean never
/// meets them — `levelMVarToParamHeaders` (`Lean/Elab/MutualDef.lean:1145`)
/// turns a theorem header's universe metavariables into PARAMETERS before the
/// body is elaborated — so they wait on that separate root cause. The same
/// rows over declared universes, which is what Lean elaborates after that
/// step, are pinned by
/// `test_pkg4_iff_comp_rows_over_declared_universes_elaborate`.
#[test]
fn test_pkg4_rows_over_sort_section_variables_elaborate() {
    assert_elaborates(
        "namespace Fx\n\
         def Injective {α β : Sort _} (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
         def Surjective {α β : Sort _} (f : α → β) : Prop := ∀ b, Exists fun a => f a = b\n\
         def LeftInverse {α β} (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x\n\
         def RightInverse {α β} (g : β → α) (f : α → β) : Prop := LeftInverse f g\n\
         theorem LeftInverse.injective {α β} {g : β → α} {f : α → β} : \
         LeftInverse g f → Injective f :=\n  \
         fun h a b faeqfb => ((h a).symm.trans (congrArg g faeqfb)).trans (h b)\n\
         theorem RightInverse.surjective {α β} {f : α → β} {g : β → α} \
         (h : RightInverse g f) : Surjective f :=\n  fun y => ⟨g y, h y⟩\n\
         end Fx\n",
        "namespace Fx\n\
         section\n\
         variable {α β γ : Sort _} {f : α → β}\n\
         theorem LeftInverse.rightInverse {f : α → β} {g : β → α} (h : LeftInverse g f) : \
         RightInverse f g := h\n\
         theorem RightInverse.leftInverse {f : α → β} {g : β → α} (h : RightInverse g f) : \
         LeftInverse f g := h\n\
         theorem LeftInverse.surjective {f : α → β} {g : β → α} (h : LeftInverse f g) : \
         Surjective f :=\n  h.rightInverse.surjective\n\
         theorem RightInverse.injective {f : α → β} {g : β → α} (h : RightInverse f g) : \
         Injective f :=\n  h.leftInverse.injective\n\
         theorem LeftInverse.comp_eq_id {f : α → β} {g : β → α} (h : LeftInverse f g) : \
         f ∘ g = id := funext h\n\
         theorem RightInverse.comp_eq_id {f : α → β} {g : β → α} (h : RightInverse f g) : \
         g ∘ f = id := funext h\n\
         theorem LeftInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} \
         (hf : LeftInverse f g)\n    (hh : LeftInverse h i) : LeftInverse (h ∘ f) (g ∘ i) :=\n  \
         fun a ↦ (congrArg h (hf (i a))).trans (hh a)\n\
         theorem RightInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} \
         (hf : RightInverse f g)\n    (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=\n  \
         LeftInverse.comp hh hf\n\
         end\n\
         end Fx\n",
        "the C2 rows over `Sort _` section variables",
    );
}
