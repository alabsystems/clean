// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder-safe env declaration builder.
//!
//! Provides `EnvDeclBuilder` which constructs Pi/Lambda binder expressions using
//! temporary FVars instead of manual de Bruijn index arithmetic. This eliminates
//! the bug class where manual depth counting produces off-by-one bvar indices
//! (see #1403, #1442, #1443, #1444).
//!
//! ## Binder-safety vs signature-safety
//!
//! This builder provides **binder-safety**: it prevents off-by-one de Bruijn
//! index bugs by using FVars as named placeholders during construction, then
//! abstracting them into BVars when closing binders.
//!
//! **Signature-safety** (correct universe levels, sort shapes, and type
//! arities) can be checked through `finish_decl_checked`, which validates
//! declaration type/value pairs with the kernel `TypeChecker` before insertion.
//! This complements (not replaces) `Environment::add_decl` checks.
//!
//! The builder now retains local binder type context captured by `fresh_local`.
//! This context is used by `infer_open_expr_type` for contract checks on open
//! expressions during migration work.
//!
//! # Usage
//!
//! ```text
//! let mut b = EnvDeclBuilder::new();
//! let (alpha_id, alpha) = b.fresh_local(type_u.clone());
//! let (inst_id, inst) = b.fresh_local(Expr::app(topological_space.clone(), alpha.clone()));
//! // ... build body using alpha, inst as Expr ...
//! let body = ...; // uses alpha, inst as Expr::FVar
//! let closed = b.mk_pi(inst_id, BinderInfo::InstImplicit,
//!     Expr::app(topological_space.clone(), alpha.clone()),
//!     body);
//! let result = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), closed);
//! let final_expr = b.finish(result);
//! ```

#[cfg(test)]
use crate::env::Environment;
use crate::expr::{stack_safe, BinderInfo, Expr, ExprKind, FVarId, ZFCSetExpr};
#[cfg(test)]
use crate::name::Name;
#[cfg(test)]
use crate::tc::{LocalContext, TypeChecker, TypeError};

/// Builder for constructing declaration types/values using FVar-based binders.
///
/// Instead of manually computing de Bruijn indices, callers create named
/// locals (`fresh_local`), reference them in expression construction, and then
/// close binders with `mk_pi`/`mk_lam` which internally call `abstract_fvar`.
///
/// # Migration pattern (replacing raw `Expr::bvar`)
///
/// Before (error-prone manual index arithmetic):
/// ```text
/// // Π (α : Type u), Π (x : α), α
/// let body = Expr::bvar(0);                      // x
/// let inner = Expr::pi(Default, Expr::bvar(0), body); // Π (x : α), α — but α is bvar(0)?
/// // ↑ Off-by-one bugs here are the #1444 root cause
/// ```
///
/// After (binder-safe builder):
/// ```text
/// let mut b = EnvDeclBuilder::new();
/// let (alpha_id, alpha) = b.fresh_local(type_u);     // α as FVar
/// let (x_id, x) = b.fresh_local(alpha.clone());      // x as FVar
/// let inner = b.mk_pi(x_id, Default, alpha.clone(), alpha.clone()); // Π (x : α), α
/// let result = b.mk_pi(alpha_id, Implicit, type_u, inner);
/// let closed = b.finish(result); // panics if any FVar leaked
/// ```
///
/// # Nested builders
///
/// Use `child_of` when building sub-expressions that introduce their own
/// binders but still reference outer variables:
/// ```text
/// let mut outer = EnvDeclBuilder::new();
/// let (alpha_id, alpha) = outer.fresh_local(type_u);
/// let inner_pi = {
///     let mut inner = EnvDeclBuilder::child_of(&outer);
///     let (x_id, x) = inner.fresh_local(alpha.clone());
///     inner.mk_pi(x_id, Default, alpha.clone(), x)
/// };
/// // inner_pi still contains alpha as FVar — outer closes it
/// let result = outer.mk_pi(alpha_id, Implicit, type_u, inner_pi);
/// outer.finish(result);
/// ```
///
/// # Safety invariants
///
/// - FVars allocated by this builder have IDs in `[start_fvar, next_fvar)`.
/// - Child builders (via `child_of`) start from the parent's `next_fvar`, so
///   each builder owns a disjoint ID range.
/// - `finish()` asserts no FVars remain (all binders closed).
/// - `finish_child()` asserts only this builder's FVars are closed; parent
///   FVars are tolerated.
pub(crate) struct EnvDeclBuilder {
    start_fvar: u64,
    next_fvar: u64,
    locals: Vec<(FVarId, Expr)>,
}

impl EnvDeclBuilder {
    /// Create a new builder with a starting FVar counter.
    ///
    /// Uses a high base to avoid collision with any runtime FVarIds from the
    /// type checker (which starts from 0 and increments).
    pub(crate) fn new() -> Self {
        let base = 0x8000_0000_0000_0000;
        EnvDeclBuilder {
            start_fvar: base,
            next_fvar: base,
            locals: Vec::new(),
        }
    }

    /// Create a child builder that continues from the parent's FVar counter.
    ///
    /// Nested builders MUST use this instead of `new()` to avoid FVar ID
    /// collisions (#1544). The child builder's FVar ID range starts where
    /// the parent's current counter is, so each builder owns a disjoint range.
    ///
    /// Use `finish_child()` instead of `finish()` when the child expression
    /// may still reference parent FVars that haven't been abstracted yet.
    pub(crate) fn child_of(parent: &EnvDeclBuilder) -> Self {
        EnvDeclBuilder {
            start_fvar: parent.next_fvar,
            next_fvar: parent.next_fvar,
            locals: Vec::new(),
        }
    }

    /// Allocate a fresh local variable with the given type.
    ///
    /// Returns `(id, fvar_expr)` where `fvar_expr` is `Expr::fvar(id)`.
    /// Use `fvar_expr` in subsequent expression construction, then close
    /// with `mk_pi` or `mk_lam` using the `id`.
    ///
    /// The type parameter is retained so the builder can reconstruct local
    /// context for checked migration and contract tests.
    pub(crate) fn fresh_local(&mut self, ty: Expr) -> (FVarId, Expr) {
        let id = FVarId::new(self.next_fvar);
        self.next_fvar += 1;
        self.locals.push((id, ty));
        (id, Expr::fvar(id))
    }

    /// Build `Π (x : ty), body` by abstracting `id` out of `body`.
    ///
    /// Replaces all occurrences of `FVar(id)` in `body` with `BVar(0)` and
    /// shifts existing bound variables up, producing a well-formed Pi binder.
    pub(crate) fn mk_pi(&self, id: FVarId, bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
        let body_closed = body.abstract_fvar(id);
        Expr::pi(bi, ty, body_closed)
    }

    /// Build `λ (x : ty), body` by abstracting `id` out of `body`.
    ///
    /// Replaces all occurrences of `FVar(id)` in `body` with `BVar(0)` and
    /// shifts existing bound variables up, producing a well-formed Lambda binder.
    pub(crate) fn mk_lam(&self, id: FVarId, bi: BinderInfo, ty: Expr, body: Expr) -> Expr {
        let body_closed = body.abstract_fvar(id);
        Expr::lam(bi, ty, body_closed)
    }

    /// Finalize an expression, asserting it contains no leaked FVars.
    ///
    /// Use this on root builders where the expression must be fully closed.
    /// For child builders whose expressions may still contain parent FVars,
    /// use `finish_child()` instead.
    ///
    /// # Panics
    ///
    /// Panics if the expression still contains free variables, which indicates
    /// a builder usage error (forgot to close a binder).
    pub(crate) fn finish(&self, e: Expr) -> Expr {
        assert!(
            !e.has_fvar_quick(),
            "EnvDeclBuilder::finish: expression still contains free variables. \
             Did you forget to close a binder with mk_pi/mk_lam?"
        );
        e
    }

    /// Finalize a child builder expression, checking only for this builder's
    /// own leaked FVars.
    ///
    /// Parent FVars are tolerated because they will be abstracted later by the
    /// parent builder. Only FVars allocated by THIS builder (IDs in
    /// `[start_fvar, next_fvar)`) are treated as leaks.
    ///
    /// # Panics
    ///
    /// Panics if the expression contains FVars owned by this builder that
    /// were not closed with `mk_pi`/`mk_lam`.
    pub(crate) fn finish_child(&self, e: Expr) -> Expr {
        assert!(
            !contains_fvar_in_range(&e, self.start_fvar, self.next_fvar),
            "EnvDeclBuilder::finish_child: expression contains leaked FVars \
             from this builder (range [{:#x}, {:#x})). \
             Did you forget to close a binder with mk_pi/mk_lam?",
            self.start_fvar,
            self.next_fvar,
        );
        e
    }
}

/// Test-only methods. Will be promoted to `pub(crate)` when checked migration
/// call sites are wired into production (#1444).
#[cfg(test)]
impl EnvDeclBuilder {
    /// Infer type for an expression that may still contain this builder's fvars.
    pub(crate) fn infer_open_expr_type(
        &self,
        env: &Environment,
        e: &Expr,
    ) -> Result<Expr, TypeError> {
        let tc = TypeChecker::with_context_and_mode(env, self.local_context(), env.mode());
        tc.infer_type(e)
    }

    /// Finalize declaration type/value expressions with semantic checks.
    ///
    /// - Ensures type expression is closed and inhabits a sort.
    /// - Ensures value (if present) is closed and has the declared type.
    pub(crate) fn finish_decl_checked(
        &self,
        env: &Environment,
        type_: Expr,
        value: Option<Expr>,
    ) -> Result<(Expr, Option<Expr>), TypeError> {
        let type_ = self.finish(type_);

        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc.infer_sort(&type_)?;

        let value = match value {
            Some(v) => {
                let v = self.finish(v);
                tc.check_type(&v, &type_)?;
                Some(v)
            }
            None => None,
        };

        Ok((type_, value))
    }

    fn local_context(&self) -> LocalContext {
        let mut ctx = LocalContext::new();
        for (id, ty) in &self.locals {
            ctx.push_with_id(*id, Name::anon(), ty.clone(), BinderInfo::Default);
        }
        ctx
    }
}

/// Check if an expression contains any FVar with ID in `[start, end)`.
///
/// Uses O(1) metadata guard: returns `false` immediately if the expression
/// has no fvars at all. Otherwise traverses the expression tree.
fn contains_fvar_in_range(e: &Expr, start: u64, end: u64) -> bool {
    if !e.has_fvar_quick() {
        return false;
    }
    stack_safe(|| contains_fvar_in_range_inner(e, start, end))
}

fn contains_fvar_in_range_inner(e: &Expr, start: u64, end: u64) -> bool {
    if !e.has_fvar_quick() {
        return false;
    }
    match e.kind() {
        ExprKind::FVar(id) => {
            let v = id.as_u64();
            v >= start && v < end
        }
        ExprKind::App(f, a) => {
            contains_fvar_in_range_inner(f, start, end)
                || contains_fvar_in_range_inner(a, start, end)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_fvar_in_range_inner(ty, start, end)
                || contains_fvar_in_range_inner(body, start, end)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_fvar_in_range_inner(ty, start, end)
                || contains_fvar_in_range_inner(val, start, end)
                || contains_fvar_in_range_inner(body, start, end)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) | ExprKind::Squash(e) => {
            contains_fvar_in_range_inner(e, start, end)
        }
        ExprKind::CubicalPath { ty, left, right } => {
            contains_fvar_in_range_inner(ty, start, end)
                || contains_fvar_in_range_inner(left, start, end)
                || contains_fvar_in_range_inner(right, start, end)
        }
        ExprKind::CubicalPathLam { body } => contains_fvar_in_range_inner(body, start, end),
        ExprKind::CubicalPathApp { path, arg } => {
            contains_fvar_in_range_inner(path, start, end)
                || contains_fvar_in_range_inner(arg, start, end)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            contains_fvar_in_range_inner(ty, start, end)
                || contains_fvar_in_range_inner(phi, start, end)
                || contains_fvar_in_range_inner(u, start, end)
                || contains_fvar_in_range_inner(base, start, end)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            contains_fvar_in_range_inner(ty, start, end)
                || contains_fvar_in_range_inner(phi, start, end)
                || contains_fvar_in_range_inner(base, start, end)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            contains_fvar_in_range_inner(ty, start, end)
                || contains_fvar_in_range_inner(r, start, end)
                || contains_fvar_in_range_inner(s, start, end)
                || contains_fvar_in_range_inner(base, start, end)
        }
        ExprKind::ZFCMem { element, set } => {
            contains_fvar_in_range_inner(element, start, end)
                || contains_fvar_in_range_inner(set, start, end)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            contains_fvar_in_range_inner(domain, start, end)
                || contains_fvar_in_range_inner(pred, start, end)
        }
        ExprKind::ZFCSet(set_expr) => match set_expr {
            ZFCSetExpr::Singleton(a)
            | ZFCSetExpr::Union(a)
            | ZFCSetExpr::PowerSet(a)
            | ZFCSetExpr::Choice(a) => contains_fvar_in_range_inner(a, start, end),
            ZFCSetExpr::Pair(a, b)
            | ZFCSetExpr::Separation { set: a, pred: b }
            | ZFCSetExpr::Replacement { set: a, func: b } => {
                contains_fvar_in_range_inner(a, start, end)
                    || contains_fvar_in_range_inner(b, start, end)
            }
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => false,
        },
        ExprKind::BVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;
    use crate::env::Declaration;
    use crate::expr::{BinderInfo, Expr, ExprKind};
    use crate::level::Level;
    use crate::name::Name;
    use crate::tc::TypeError;

    #[test]
    fn test_simple_pi() {
        // Build: Π (x : Prop), Prop
        // Expected: Pi(Default, Sort(0), Sort(0)) — non-dependent
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (x_id, _x) = b.fresh_local(prop.clone());
        let result = b.mk_pi(x_id, BinderInfo::Default, prop.clone(), prop.clone());
        let final_expr = b.finish(result);

        // Body doesn't mention x, so it should be Pi(Default, Prop, Prop)
        match final_expr.kind() {
            ExprKind::Pi(bi, ty, body) => {
                assert_eq!(bi.info, BinderInfo::Default);
                assert!(matches!(ty.kind(), ExprKind::Sort(Level::Zero)));
                assert!(matches!(body.kind(), ExprKind::Sort(Level::Zero)));
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_dependent_pi() {
        // Build: Π (x : Prop), x
        // Expected: Pi(Default, Sort(0), BVar(0))
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (x_id, x) = b.fresh_local(prop.clone());
        let result = b.mk_pi(x_id, BinderInfo::Default, prop.clone(), x);
        let final_expr = b.finish(result);

        match final_expr.kind() {
            ExprKind::Pi(bi, ty, body) => {
                assert_eq!(bi.info, BinderInfo::Default);
                assert!(matches!(ty.kind(), ExprKind::Sort(Level::Zero)));
                assert!(matches!(body.kind(), ExprKind::BVar(0)));
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_nested_pi() {
        // Build: Π (x : Prop) (y : Prop), x
        // Expected: Pi(Default, Prop, Pi(Default, Prop, BVar(1)))
        // x is bound by outer pi, so under inner pi it's BVar(1)
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (x_id, x) = b.fresh_local(prop.clone());
        let (y_id, _y) = b.fresh_local(prop.clone());

        // Close inner first (y), then outer (x)
        let inner = b.mk_pi(y_id, BinderInfo::Default, prop.clone(), x.clone());
        let result = b.mk_pi(x_id, BinderInfo::Default, prop.clone(), inner);
        let final_expr = b.finish(result);

        match final_expr.kind() {
            ExprKind::Pi(_, _, body) => match body.kind() {
                ExprKind::Pi(_, _, inner_body) => {
                    assert!(
                        matches!(inner_body.kind(), ExprKind::BVar(1)),
                        "Expected BVar(1) for x under two pi binders, got {:?}",
                        inner_body.kind()
                    );
                }
                _ => panic!("Expected inner Pi"),
            },
            _ => panic!("Expected outer Pi"),
        }
    }

    #[test]
    fn test_lambda() {
        // Build: λ (x : Prop), x
        // Expected: Lam(Default, Sort(0), BVar(0))
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (x_id, x) = b.fresh_local(prop.clone());
        let result = b.mk_lam(x_id, BinderInfo::Default, prop.clone(), x);
        let final_expr = b.finish(result);

        match final_expr.kind() {
            ExprKind::Lam(bi, ty, body) => {
                assert_eq!(bi.info, BinderInfo::Default);
                assert!(matches!(ty.kind(), ExprKind::Sort(Level::Zero)));
                assert!(matches!(body.kind(), ExprKind::BVar(0)));
            }
            _ => panic!("Expected Lam"),
        }
    }

    #[test]
    fn test_mixed_pi_lam() {
        // Build: Π (α : Type), λ (x : α), x
        // Expected: Pi(Default, Sort(1), Lam(Default, BVar(0), BVar(0)))
        let mut b = EnvDeclBuilder::new();
        let type_ = Expr::type_();
        let (alpha_id, alpha) = b.fresh_local(type_.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());

        let lam = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), x);
        let result = b.mk_pi(alpha_id, BinderInfo::Default, type_.clone(), lam);
        let final_expr = b.finish(result);

        match final_expr.kind() {
            ExprKind::Pi(_, _, body) => match body.kind() {
                ExprKind::Lam(_, ty, lam_body) => {
                    // ty should be BVar(0) = α under the pi
                    assert!(
                        matches!(ty.kind(), ExprKind::BVar(0)),
                        "Expected BVar(0), got {:?}",
                        ty.kind()
                    );
                    // body should be BVar(0) = x under the lambda
                    assert!(
                        matches!(lam_body.kind(), ExprKind::BVar(0)),
                        "Expected BVar(0), got {:?}",
                        lam_body.kind()
                    );
                }
                _ => panic!("Expected Lam"),
            },
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_no_leaked_fvars() {
        // finish should pass when all FVars are closed
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (x_id, x) = b.fresh_local(prop.clone());
        let result = b.mk_pi(x_id, BinderInfo::Default, prop.clone(), x);
        // Should not panic
        let _ = b.finish(result);
    }

    #[test]
    #[should_panic(expected = "still contains free variables")]
    fn test_leaked_fvar_panics() {
        // finish should panic when FVars leak
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (_x_id, x) = b.fresh_local(prop.clone());
        // Not closing x — should panic
        let _ = b.finish(x);
    }

    #[test]
    fn test_child_of_no_fvar_collision() {
        // Regression test for #1544: nested builders must not collide.
        let mut outer = EnvDeclBuilder::new();
        let type_ = Expr::type_();
        let (alpha_id, alpha) = outer.fresh_local(type_.clone());

        let inner_pi = {
            let mut inner = EnvDeclBuilder::child_of(&outer);
            let (x_id, x) = inner.fresh_local(alpha.clone());
            inner.mk_pi(x_id, BinderInfo::Default, alpha.clone(), x)
        };

        let (pi_id, _) = outer.fresh_local(inner_pi.clone());
        let e = outer.mk_pi(pi_id, BinderInfo::Default, inner_pi, alpha.clone());
        let e = outer.mk_pi(alpha_id, BinderInfo::Default, type_.clone(), e);
        let final_expr = outer.finish(e);

        match final_expr.kind() {
            ExprKind::Pi(_, _, body) => match body.kind() {
                ExprKind::Pi(_, pi_ty, result) => {
                    match pi_ty.kind() {
                        ExprKind::Pi(_, d, b) => {
                            assert!(matches!(d.kind(), ExprKind::BVar(0)));
                            assert!(matches!(b.kind(), ExprKind::BVar(0)));
                        }
                        _ => panic!("Expected inner Pi"),
                    }
                    assert!(matches!(result.kind(), ExprKind::BVar(1)));
                }
                _ => panic!("Expected hypothesis Pi"),
            },
            _ => panic!("Expected outer Pi"),
        }
    }

    #[test]
    fn test_finish_child_tolerates_parent_fvars() {
        // Child builder expressions may still contain parent FVars.
        // finish_child() should pass as long as the child's own FVars are closed.
        // Regression test for #1589: s.finish(e) panicked on Rat.inv construction
        // because child builder 'e' contained parent fvar 'r'.
        let mut parent = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (_r_id, r) = parent.fresh_local(prop.clone());

        let child_result = {
            let mut child = EnvDeclBuilder::child_of(&parent);
            let (x_id, x) = child.fresh_local(prop.clone());
            // Body references both child fvar x (closed by mk_lam) and parent fvar r
            let body = Expr::app(x, r.clone());
            let e = child.mk_lam(x_id, BinderInfo::Default, prop.clone(), body);
            // finish_child should succeed: child fvar x is closed, parent fvar r is tolerated
            child.finish_child(e)
        };

        // The result should still have fvars (parent's r), so finish() would panic
        assert!(child_result.has_fvar_quick());
    }

    #[test]
    #[should_panic(expected = "leaked FVars from this builder")]
    fn test_finish_child_catches_own_leaked_fvars() {
        // finish_child() should still catch leaked FVars that belong to THIS builder.
        let mut parent = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (_r_id, r) = parent.fresh_local(prop.clone());

        let mut child = EnvDeclBuilder::child_of(&parent);
        let (_x_id, x) = child.fresh_local(prop.clone());
        // Body uses child fvar x but doesn't close it with mk_lam/mk_pi
        let body = Expr::app(x, r);
        // finish_child should panic: child fvar x was not closed
        let _ = child.finish_child(body);
    }

    #[test]
    fn test_infer_open_expr_type_uses_retained_local_context() {
        let env = Environment::new();
        let mut b = EnvDeclBuilder::new();
        let prop = Expr::prop();
        let (_x_id, x) = b.fresh_local(prop.clone());

        let inferred = b
            .infer_open_expr_type(&env, &x)
            .expect("builder should infer open local type from retained context");
        assert_eq!(inferred, prop);
    }

    #[test]
    fn test_finish_decl_checked_rejects_type_incoherent_declaration() {
        let env = Environment::new();
        let b = EnvDeclBuilder::new();

        // Shape-only checks pass: both expressions are closed.
        let decl_ty = b.finish(Expr::prop());
        let bad_value = b.finish(Expr::type_());

        let err = b
            .finish_decl_checked(&env, decl_ty, Some(bad_value))
            .expect_err("checked declaration finalization must reject type mismatch");
        assert!(matches!(err, TypeError::TypeMismatch { .. }));
    }

    #[test]
    fn test_finish_decl_checked_catches_migrated_identity_shape_regression() {
        let env = Environment::new();
        let mut b = EnvDeclBuilder::new();

        // Declaration type: Π (α : Type), α -> α
        let sort1 = Expr::type_();
        let (alpha_id, alpha) = b.fresh_local(sort1.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let fn_type = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), x);
        let decl_ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort1.clone(), fn_type);
        let decl_ty = b.finish(decl_ty);

        // Wrong migrated value shape: λ α x, α (returns type-level term)
        let mut vb = EnvDeclBuilder::new();
        let (v_alpha_id, v_alpha) = vb.fresh_local(sort1.clone());
        let (v_x_id, _v_x) = vb.fresh_local(v_alpha.clone());
        let bad_inner = vb.mk_lam(
            v_x_id,
            BinderInfo::Default,
            v_alpha.clone(),
            v_alpha.clone(),
        );
        let bad_value = vb.mk_lam(v_alpha_id, BinderInfo::Implicit, sort1.clone(), bad_inner);
        let bad_value = vb.finish(bad_value);

        let err = vb
            .finish_decl_checked(&env, decl_ty.clone(), Some(bad_value.clone()))
            .expect_err("checked path must reject migrated declaration shape regressions");
        // The type checker may return TypeMismatch, ExpectedSort, or other
        // errors depending on how it resolves the Pi/BVar structure.
        // The critical invariant is that finish_decl_checked rejects the
        // malformed declaration — any TypeError variant satisfies this.
        match &err {
            TypeError::TypeMismatch { .. } | TypeError::ExpectedSort { .. } => {}
            other => panic!("expected TypeMismatch or ExpectedSort, got: {other:?}"),
        }

        // Old unchecked insertion path accepts the same malformed declaration.
        let mut unchecked_env = Environment::new();
        unchecked_env.add_decl_unchecked(Declaration::Definition {
            name: Name::from_string("decl_builder.bad_id"),
            level_params: vec![],
            type_: decl_ty,
            value: bad_value,
            is_reducible: true,
        });
        assert_const(&unchecked_env, "decl_builder.bad_id");
    }
}
