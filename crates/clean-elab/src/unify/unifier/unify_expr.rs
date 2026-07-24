// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core expression unification dispatch — structural comparison after WHNF reduction.

use crate::stack_safe;
use clean_kernel::expr::{BigNat, Literal, ZFCSetExpr};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};
use std::sync::LazyLock;

use super::{Unifier, UnifyResult};

/// Cached Nat.zero name for Nat literal/constructor unification.
static NAT_ZERO_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.zero"));
/// Cached Nat.succ name for Nat literal/constructor unification.
static NAT_SUCC_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.succ"));
static BOOL_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool"));

/// Check if an expression is Nat zero (either `Nat.zero` constructor or `Lit(Nat(0))`).
///
/// Mirrors `TypeChecker::is_nat_zero_expr` from the kernel's `is_def_eq_offset`.
fn is_nat_zero(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => matches!(n, BigNat::Small(0)),
        ExprKind::Const(name, levels) => levels.is_empty() && *name == *NAT_ZERO_NAME,
        _ => false,
    }
}

/// Check if an expression is the `Bool` type constant (no universe args).
fn is_bool_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels) if levels.is_empty() && *name == *BOOL_NAME)
}

/// Check if an expression is `Prop` (i.e., `Sort 0`).
fn is_prop_sort(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Sort(level) if level.is_zero())
}

/// Whether the two sides are a `Bool` ↔ `Prop` pair (in either order).
///
/// `Bool` and `Prop` are NOT definitionally equal in Lean 4 — they are
/// distinct types bridged only by `Decidable.decide`. We treat them as
/// unifiable here as a lenient elaboration fallback for sites where a
/// `decide`-style coercion is the intended interpretation. The kernel
/// `is_def_eq` is consulted first in [`Unifier::try_kernel_def_eq`]; this
/// case is reached only when the kernel itself cannot prove equality.
///
/// Soundness caveat: programs accepted here may still be rejected by the
/// kernel during final checking. Do not rely on this for trusted defeq.
fn is_bool_prop_pair(left: &Expr, right: &Expr) -> bool {
    (is_bool_const(left) && is_prop_sort(right)) || (is_prop_sort(left) && is_bool_const(right))
}

/// Check if an expression is a Nat successor and return the predecessor.
///
/// Handles both:
/// - `Lit(Nat(n))` where n > 0 -> returns `Lit(Nat(n-1))`
/// - `App(Nat.succ, x)` -> returns `x`
///
/// Mirrors `TypeChecker::is_nat_succ_expr` from the kernel's `is_def_eq_offset`.
fn is_nat_succ(e: &Expr) -> Option<Expr> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            let pred = n.pred()?;
            Some(Expr::from_kind(ExprKind::Lit(Literal::Nat(pred))))
        }
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, levels) = f.kind() {
                if levels.is_empty() && *name == *NAT_SUCC_NAME {
                    return Some(arg.as_ref().clone());
                }
            }
            None
        }
        _ => None,
    }
}

impl<'a> Unifier<'a> {
    fn unify_with_whnf(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        stack_safe(|| {
            let left_whnf = self.try_whnf(left);
            let right_whnf = self.try_whnf(right);
            self.unify_core(&left_whnf, &right_whnf)
        })
    }

    /// Kernel def-eq fallback for cases the structural unifier cannot handle,
    /// such as Nat literal / constructor equivalence (e.g., `Lit(Nat(0))` vs
    /// `Const("Nat.zero")`).
    ///
    /// The kernel's `is_def_eq` has special handling for Nat/String
    /// literal-constructor equivalence via `is_def_eq_offset` and
    /// `nat_lit_to_constructor`/`string_lit_to_constructor`.
    fn try_kernel_def_eq(&self, left: &Expr, right: &Expr) -> UnifyResult {
        let tc_cache = self.tc_cache.borrow();
        if let Some(tc) = tc_cache.as_ref() {
            if tc.is_def_eq(left, right) {
                return UnifyResult::Success;
            }
        }
        if is_bool_prop_pair(left, right) {
            return UnifyResult::Success;
        }
        UnifyResult::Failure(format!(
            "cannot unify expressions of different shape: {:?} vs {:?}",
            std::mem::discriminant(left.kind()),
            std::mem::discriminant(right.kind())
        ))
    }

    fn unify_zfc_set_expr(&mut self, left: &ZFCSetExpr, right: &ZFCSetExpr) -> UnifyResult {
        match (left, right) {
            (ZFCSetExpr::Empty, ZFCSetExpr::Empty)
            | (ZFCSetExpr::Infinity, ZFCSetExpr::Infinity) => UnifyResult::Success,
            (ZFCSetExpr::Singleton(e1), ZFCSetExpr::Singleton(e2))
            | (ZFCSetExpr::Union(e1), ZFCSetExpr::Union(e2))
            | (ZFCSetExpr::PowerSet(e1), ZFCSetExpr::PowerSet(e2))
            | (ZFCSetExpr::Choice(e1), ZFCSetExpr::Choice(e2)) => self.unify_with_whnf(e1, e2),
            (ZFCSetExpr::Pair(a1, b1), ZFCSetExpr::Pair(a2, b2)) => {
                match self.unify_with_whnf(a1, a2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(b1, b2)
            }
            (
                ZFCSetExpr::Separation {
                    set: set1,
                    pred: pred1,
                },
                ZFCSetExpr::Separation {
                    set: set2,
                    pred: pred2,
                },
            ) => {
                match self.unify_with_whnf(set1, set2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(pred1, pred2)
            }
            (
                ZFCSetExpr::Replacement {
                    set: set1,
                    func: func1,
                },
                ZFCSetExpr::Replacement {
                    set: set2,
                    func: func2,
                },
            ) => {
                match self.unify_with_whnf(set1, set2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(func1, func2)
            }
            _ => UnifyResult::Failure(format!(
                "cannot unify ZFC set expressions of different shape: {:?} vs {:?}",
                std::mem::discriminant(left),
                std::mem::discriminant(right)
            )),
        }
    }

    pub(super) fn unify_core(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        stack_safe(|| self.unify_core_inner(left, right))
    }

    fn unify_core_inner(&mut self, left: &Expr, right: &Expr) -> UnifyResult {
        // If they're already equal, we're done
        if left == right {
            return UnifyResult::Success;
        }

        // Check for metavariables BEFORE any further WHNF reduction
        // to ensure we can still assign to metas even after reduction
        if let Some(meta_id) = self.as_meta(left) {
            // For two distinct bare metas, prefer the historical left-to-right
            // assignment but reverse it when that direction is scope-stuck.
            // Example: outer `?m : {}` versus inner `?n : {x}` cannot safely
            // assign `?m := ?n`, while `?n := ?m` is the sound most-general
            // solution. The forward Stuck path is mutation-free, so the reverse
            // attempt needs no rollback.
            let forward = self.unify_meta(meta_id, right);
            if matches!(forward, UnifyResult::Stuck) {
                if let Some(right_meta) = self.as_meta(right) {
                    if right_meta != meta_id {
                        return self.unify_meta(right_meta, left);
                    }
                }
            }
            return forward;
        }

        if let Some(meta_id) = self.as_meta(right) {
            return self.unify_meta(meta_id, left);
        }

        // Miller-pattern higher-order unification.
        //
        // Handles constraints `?m x₁ … xₙ =?= t` where the metavariable head is
        // applied to arguments (so the bare-meta checks above did not fire).
        // When x₁ … xₙ are distinct locals and the occurs/scope checks pass,
        // this assigns the unique most-general solution `?m := λ x₁ … xₙ. t`;
        // otherwise it defers. See `pattern.rs`.
        //
        // `None` means neither side is a flex application, so we fall through to
        // the normal structural dispatch (which handles, e.g., `?m =?= ?m`
        // already excluded above, and ordinary applications).
        if let Some(result) = self.try_pattern_unify(left, right) {
            return result;
        }

        // If discriminants don't match and we have WHNF capability,
        // try reducing again (in case reduction reveals more structure).
        // This handles recursive calls where sub-expressions weren't yet reduced.
        if std::mem::discriminant(left.kind()) != std::mem::discriminant(right.kind())
            && self.has_whnf()
        {
            let left_whnf = self.try_whnf(left);
            let right_whnf = self.try_whnf(right);
            // Only recurse if we made progress
            if &left_whnf != left || &right_whnf != right {
                return self.unify_core(&left_whnf, &right_whnf);
            }
        }

        // Nat literal/constructor equivalence (mirrors kernel is_def_eq_offset).
        //
        // The kernel's WHNF reduces `Nat.add Nat.zero Nat.zero` to `Lit(Nat(0))`
        // but leaves `Const(Nat.zero)` unreduced (it's a constructor). The kernel's
        // def_eq handles this via `is_def_eq_offset` in the lazy delta loop, but
        // the elaborator's unifier must handle it independently. Without this,
        // proof terms involving Nat arithmetic on concrete constructors fail with
        // "different shape: Discriminant(Const) vs Discriminant(Lit)".
        if is_nat_zero(left) && is_nat_zero(right) {
            return UnifyResult::Success;
        }
        // Two Nat LITERALS: unify iff equal — decided in O(1) on the value.
        //
        // This MUST precede the successor-peel below. `is_nat_succ` on a literal
        // decrements it by one, so peeling two DISTINCT literals recurses
        // `min(a, b)` deep — and the operands `a`, `b` of two distinct `Float`
        // bit-patterns compared under `@Eq Float (Float.mk a) (Float.mk b)` (a
        // `rfl` on unequal Floats) are ~10^18-scale, which exhausts the stack /
        // memory (25 GB+ before OOM-kill) instead of rejecting. Equal literals are
        // already caught by the `left == right` short-circuit above; here we
        // decide the UNEQUAL case as a loud, immediate failure. Mirrors the
        // kernel's `is_def_eq_offset` two-literal fast path.
        if let (ExprKind::Lit(Literal::Nat(a)), ExprKind::Lit(Literal::Nat(b))) =
            (left.kind(), right.kind())
        {
            return if a == b {
                UnifyResult::Success
            } else {
                UnifyResult::Failure(format!("Nat literal mismatch: {a:?} vs {b:?}"))
            };
        }
        if let (Some(pred_l), Some(pred_r)) = (is_nat_succ(left), is_nat_succ(right)) {
            return self.unify_with_whnf(&pred_l, &pred_r);
        }

        match (left.kind(), right.kind()) {
            // Both are sorts - unify levels
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.unify_levels(l1, l2),

            // Both are constants
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                if n1 == n2 && ls1.len() == ls2.len() {
                    // Unify universe levels
                    for (l1, l2) in ls1.iter().zip(ls2.iter()) {
                        match self.unify_levels(l1, l2) {
                            UnifyResult::Success => {}
                            other => return other,
                        }
                    }
                    UnifyResult::Success
                } else {
                    UnifyResult::Failure(format!("const mismatch: {n1:?} vs {n2:?}"))
                }
            }

            // Both are bound variables
            (ExprKind::BVar(i1), ExprKind::BVar(i2)) => {
                if i1 == i2 {
                    UnifyResult::Success
                } else {
                    UnifyResult::Failure(format!("bvar mismatch: {i1} vs {i2}"))
                }
            }

            // Both are free variables (non-metavars at this point)
            (ExprKind::FVar(id1), ExprKind::FVar(id2)) => {
                if id1 == id2 {
                    UnifyResult::Success
                } else {
                    UnifyResult::Failure(format!("fvar mismatch: {id1:?} vs {id2:?}"))
                }
            }

            // Application
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                // Rigid-spine guard (#rw-typeclass-head): if BOTH sides are
                // applications whose ultimate spine heads are *rigid* constants
                // (not metavariables / flex applications), they can only unify
                // when the head `Name`s agree AND the spines have the same
                // length. Without this guard, the outermost-only App/App
                // decomposition below pairs arguments *positionally* even when
                // the heads disagree or the arities differ — e.g.
                //   `Nat.add ?a Nat.zero`   (head Nat.add, 2 args)
                // vs
                //   `Eq Nat X n`            (head Eq, 3 args)
                // would pair `(Nat.add ?a) ≟ (Eq Nat X)` and `Nat.zero ≟ n`,
                // burying the bare metavar `?a` against a mismatched subterm and
                // *wrongly succeeding* with `?a := (Eq Nat X …)`. That spurious
                // root-level success then suppresses the rw matcher's recursion
                // into the real subterm. Returning Failure here (a *safe reject*:
                // the assembled rewrite proof is kernel-rechecked regardless)
                // lets the matcher fall through to structural recursion instead.
                //
                // The guard is intentionally narrow: it fires ONLY when both
                // heads are rigid consts. A metavar / flex head on either side is
                // handled by the Miller path earlier (`try_pattern_unify`) and by
                // the bare-meta checks at the top of `unify_core_inner`, so this
                // never blocks legitimate higher-order assignments. Genuinely
                // def-eq applications with the same head still pass (matching
                // name + arity).
                //
                // To stay conservative for the *general* unifier (this arm is on
                // the hot path of all elaboration), we do NOT fail blindly: two
                // distinct rigid heads can still be def-eq when one δ-unfolds to
                // the other under a transparency the entry WHNF did not apply. We
                // therefore first try a full WHNF of BOTH whole applications and,
                // if either made progress, retry `unify_core` on the reduced
                // forms — recovering exactly the cases the pre-existing
                // `unify_core(f1_whnf, f2_whnf)` recursion would have. Only when
                // no progress is possible do we reject, the same verdict the
                // `Const`-arm mismatch reaches, just without first pairing the
                // spines positionally and burying a metavar.
                //
                // The rw subterm matcher does not depend on the *strict* form of
                // this guard: it skips the full unifier at rigid-head mismatched
                // nodes (`rigid_const_head_mismatch` in rewrite.rs) and uses
                // `unify_no_initial_whnf`, so the harmful
                // `Nat.add ?a Nat.zero → ?a` collapse never reaches here on that
                // path. This guard is purely extra safety against positional
                // mis-pairing of unrelated rigid applications.
                if self.rigid_spine_head_mismatch(left, right) {
                    if self.has_whnf() {
                        let left_whnf = self.try_whnf(left);
                        let right_whnf = self.try_whnf(right);
                        if &left_whnf != left || &right_whnf != right {
                            return self.unify_core(&left_whnf, &right_whnf);
                        }
                    }
                    return UnifyResult::Failure(format!(
                        "rigid head/arity mismatch: {:?} vs {:?}",
                        left.get_app_fn().kind(),
                        right.get_app_fn().kind()
                    ));
                }
                // Apply WHNF to subterms for consistency with Pi/Lam handling (#379)
                // — but NEVER reduce a subterm pair that is already
                // syntactically identical: identical subterms are def-eq
                // as-is, and for ground interpreter-style subterms (huge
                // normal forms) the reduce-before-compare ordering is the
                // measured >12GB wall the `unify` entry fast path guards
                // against (see the comment there). The partial-application
                // `f` side matters as much as the argument side: in
                // `Sem.run (stepNWithContext …) st`, the whole interpreter
                // call sits inside `f1`/`f2`.
                if f1 != f2 {
                    let f1_whnf = self.try_whnf(f1);
                    let f2_whnf = self.try_whnf(f2);
                    match self.unify_core(&f1_whnf, &f2_whnf) {
                        UnifyResult::Success => {}
                        other => return other,
                    }
                }
                if a1 == a2 {
                    return UnifyResult::Success;
                }
                // Targeted exception: do NOT Î´-unfold an argument whose head is
                // an `Irreducible` constant (the Track II `Nat.land`/`lor`/`xor`)
                // WHEN the OPPOSITE argument is a bare metavariable, so the
                // metavar is assigned the SURFACE head a later `rw`/`unfold`
                // relies on. Gating on "opposite is a bare meta" confines it to
                // metavar assignment; general structural unification keeps #379
                // WHNF. Soundness unchanged (kernel re-checks the proof term).
                let a1_keep = self.head_is_protected_def(a1) && self.as_meta(a2).is_some();
                let a2_keep = self.head_is_protected_def(a2) && self.as_meta(a1).is_some();
                let a1_whnf = if a1_keep {
                    (**a1).clone()
                } else {
                    self.try_whnf(a1)
                };
                let a2_whnf = if a2_keep {
                    (**a2).clone()
                } else {
                    self.try_whnf(a2)
                };
                self.unify_core(&a1_whnf, &a2_whnf)
            }

            // Lambda and Pi
            //
            // BinderInfo is deliberately IGNORED, mirroring Lean 4's `isDefEq`
            // (and Clean's own kernel defeq, `tc/def_eq/binding.rs`, which
            // never compares binder infos): implicitness is elaboration
            // metadata, not term structure. Failing on `bi1 != bi2` here made
            // every higher-kinded head over the prelude's `{α : Type u} →
            // Type u`-spelled type formers (`Option`/`List`) unsolvable
            // against a Lean-faithful `(Type u → Type v)` class parameter —
            // the class's codomain universe was left unassigned, generalized
            // at decl level, and the kernel re-check rightly rejected
            // (audit rows a02–a06/a09–a12, `TooManyArguments`/`Pi vs Pi`
            // signatures in docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md).
            // SOUNDNESS: unification acceptance is not trust-bearing — every
            // elaborated declaration is still re-checked by the unmodified
            // kernel, whose defeq already ignores binder info (fails closed).
            (ExprKind::Lam(_, ty1, body1), ExprKind::Lam(_, ty2, body2))
            | (ExprKind::Pi(_, ty1, body1), ExprKind::Pi(_, ty2, body2)) => {
                // Apply WHNF to subterms before comparison (#379)
                // This handles cases where the body contains reducible applications,
                // e.g., `P A A (Rel_refl A)` where P is a lambda motive
                let ty1_whnf = self.try_whnf(ty1);
                let ty2_whnf = self.try_whnf(ty2);
                match self.unify_core(&ty1_whnf, &ty2_whnf) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                // Open the binder with a fresh local FVar before comparing the
                // bodies (mirrors Lean 4's `isDefEq` forallE/lambdaE path). The
                // bodies are compared with `BVar(0)` replaced by a genuine local
                // `x : ty1`, so a higher-order constraint such as `?f (BVar 0)
                // =?= f (BVar 0)` becomes `?f x =?= f x` — now `x` is a real
                // pattern argument and the Miller-pattern solver in `pattern.rs`
                // can assign `?f := f`. Without this, the loose `BVar(0)` is not
                // a pattern argument (pattern.rs requires bare `FVar`s), so
                // under-binder implicits like `funext`'s `{f g}` stay unsolved
                // and the bodies spuriously fail to unify.
                //
                // The fvar is popped on every exit path. Because it only ever
                // appears as a pattern argument that is abstracted back out of
                // the metavariable assignment (pattern.rs `abstract_fvar`), it
                // does not leak into the solution; if abstraction ever failed
                // the kernel re-check of the assembled term would reject it
                // (fails closed — never an unsound accept).
                let (cmp1, cmp2, opened) = match self.push_binder_local(&ty1_whnf) {
                    Some(fvar) => {
                        let x = Expr::fvar(fvar);
                        (body1.instantiate(&x), body2.instantiate(&x), true)
                    }
                    // Legacy (no-WHNF) mode: keep the historical loose-BVar
                    // comparison.
                    None => ((**body1).clone(), (**body2).clone(), false),
                };

                // Monad-application preservation (flex App vs reducible App).
                //
                // When one body is a flex application `?m e₁ … eₙ` (head is an
                // unassigned metavariable — e.g. the `?m ?β` codomain of `mapM`'s
                // `f : α → ?m ?β`) and the other is itself an `App` *before* WHNF
                // (e.g. the monadic abbreviation `Sem Nat = App(Sem, Nat)`), then
                // WHNF-ing the rigid side would δ-unfold `Sem Nat` into its Pi form
                // (`MState → Except SErr (Nat × MState)`), destroying the spine the
                // flex metavariable must structurally unify against. The result is
                // a spurious "App vs Pi" failure (`?m ?β =?= MyState → …`).
                //
                // Mirror the do-notation `expected_do_result_components` policy
                // (elab_do.rs): try the *unreduced* App forms first so `?m`/`?β`
                // are solved against the surface monad spine. Only fall back to the
                // WHNF path if the unreduced attempt does not succeed, preserving
                // #379 behavior for genuinely reducible motive bodies. The
                // assignment is provisional and kernel-re-checked, so this never
                // weakens soundness.
                let result = {
                    if (self.is_flex_app(&cmp1) && cmp2.is_app())
                        || (self.is_flex_app(&cmp2) && cmp1.is_app())
                    {
                        if let UnifyResult::Success = self.unify_core(&cmp1, &cmp2) {
                            UnifyResult::Success
                        } else {
                            let body1_whnf = self.try_whnf(&cmp1);
                            let body2_whnf = self.try_whnf(&cmp2);
                            self.unify_core(&body1_whnf, &body2_whnf)
                        }
                    } else {
                        let body1_whnf = self.try_whnf(&cmp1);
                        let body2_whnf = self.try_whnf(&cmp2);
                        self.unify_core(&body1_whnf, &body2_whnf)
                    }
                };
                if opened {
                    self.pop_binder_local();
                }
                result
            }

            // Let
            (ExprKind::Let(_, ty1, val1, body1, _), ExprKind::Let(_, ty2, val2, body2, _)) => {
                // Apply WHNF to subterms for consistency (#379)
                let ty1_whnf = self.try_whnf(ty1);
                let ty2_whnf = self.try_whnf(ty2);
                match self.unify_core(&ty1_whnf, &ty2_whnf) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                let val1_whnf = self.try_whnf(val1);
                let val2_whnf = self.try_whnf(val2);
                match self.unify_core(&val1_whnf, &val2_whnf) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                let body1_whnf = self.try_whnf(body1);
                let body2_whnf = self.try_whnf(body2);
                self.unify_core(&body1_whnf, &body2_whnf)
            }

            // Literals
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => {
                if l1 == l2 {
                    UnifyResult::Success
                } else {
                    UnifyResult::Failure(format!("literal mismatch: {l1:?} vs {l2:?}"))
                }
            }

            // Projection
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                if n1 != n2 || i1 != i2 {
                    return UnifyResult::Failure(format!(
                        "projection mismatch: {n1}.{i1} vs {n2}.{i2}"
                    ));
                }
                // Apply WHNF to subterms for consistency (#379)
                self.unify_with_whnf(e1, e2)
            }

            // MData is transparent for unification.
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                self.unify_with_whnf(inner1, inner2)
            }
            (ExprKind::MData(_, inner), _) => self.unify_with_whnf(inner, right),
            (_, ExprKind::MData(_, inner)) => self.unify_with_whnf(left, inner),

            // Squash unifies by unifying the wrapped term.
            (ExprKind::Squash(inner1), ExprKind::Squash(inner2)) => {
                self.unify_with_whnf(inner1, inner2)
            }

            // Explicit leaf-mode expressions.
            (ExprKind::SProp, ExprKind::SProp)
            | (ExprKind::CubicalInterval, ExprKind::CubicalInterval)
            | (ExprKind::CubicalI0, ExprKind::CubicalI0)
            | (ExprKind::CubicalI1, ExprKind::CubicalI1) => UnifyResult::Success,

            // Cubical structural expressions.
            (
                ExprKind::CubicalPath {
                    ty: ty1,
                    left: left1,
                    right: right1,
                },
                ExprKind::CubicalPath {
                    ty: ty2,
                    left: left2,
                    right: right2,
                },
            ) => {
                match self.unify_with_whnf(ty1, ty2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                match self.unify_with_whnf(left1, left2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(right1, right2)
            }
            (
                ExprKind::CubicalPathLam { body: body1 },
                ExprKind::CubicalPathLam { body: body2 },
            ) => self.unify_with_whnf(body1, body2),
            (
                ExprKind::CubicalPathApp {
                    path: path1,
                    arg: arg1,
                },
                ExprKind::CubicalPathApp {
                    path: path2,
                    arg: arg2,
                },
            ) => {
                match self.unify_with_whnf(path1, path2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(arg1, arg2)
            }
            (
                ExprKind::CubicalHComp {
                    ty: ty1,
                    phi: phi1,
                    u: u1,
                    base: base1,
                },
                ExprKind::CubicalHComp {
                    ty: ty2,
                    phi: phi2,
                    u: u2,
                    base: base2,
                },
            ) => {
                match self.unify_with_whnf(ty1, ty2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                match self.unify_with_whnf(phi1, phi2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                match self.unify_with_whnf(u1, u2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(base1, base2)
            }
            (
                ExprKind::CubicalTransp {
                    ty: ty1,
                    phi: phi1,
                    base: base1,
                },
                ExprKind::CubicalTransp {
                    ty: ty2,
                    phi: phi2,
                    base: base2,
                },
            ) => {
                match self.unify_with_whnf(ty1, ty2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                match self.unify_with_whnf(phi1, phi2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(base1, base2)
            }

            // ZFC structural expressions.
            (ExprKind::ZFCSet(set1), ExprKind::ZFCSet(set2)) => self.unify_zfc_set_expr(set1, set2),
            (
                ExprKind::ZFCMem {
                    element: elem1,
                    set: set1,
                },
                ExprKind::ZFCMem {
                    element: elem2,
                    set: set2,
                },
            ) => {
                match self.unify_with_whnf(elem1, elem2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(set1, set2)
            }
            (
                ExprKind::ZFCComprehension {
                    domain: domain1,
                    pred: pred1,
                },
                ExprKind::ZFCComprehension {
                    domain: domain2,
                    pred: pred2,
                },
            ) => {
                match self.unify_with_whnf(domain1, domain2) {
                    UnifyResult::Success => {}
                    other => return other,
                }
                self.unify_with_whnf(pred1, pred2)
            }

            // Fall back to kernel def-eq for Nat/String literal ↔ constructor, etc.
            _ => self.try_kernel_def_eq(left, right),
        }
    }
}
