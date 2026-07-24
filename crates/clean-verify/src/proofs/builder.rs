// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term builder API for constructing `Expr` trees with automatic
//! de Bruijn index management.
//!
//! The `ProofBuilder` tracks named variable scopes so callers can refer to
//! bound variables by name instead of manually computing de Bruijn indices.
//! This eliminates the ~200 LOC boilerplate per proof that arises from
//! hand-constructing `Expr` trees with exact universe levels, binder info,
//! and de Bruijn indices.
//!
//! # Example
//!
//! Build the identity proof `fun (A : Type) (x : A) => x`:
//!
//! ```text
//! let mut b = ProofBuilder::new();
//! let proof = b.lam("A", b.type_(), |b| {
//!     b.lam("x", b.var("A"), |b| {
//!         b.var("x")
//!     })
//! });
//! ```
//!
//! The builder automatically resolves `var("x")` to `bvar(0)` and
//! `var("A")` to `bvar(1)` based on binding depth.

use clean_kernel::{BinderInfo, Expr, Level, Name};

/// Builder for constructing proof term `Expr` trees with automatic
/// de Bruijn index resolution via named variable tracking.
///
/// The scope stack grows as `lam`/`pi` closures are entered. Calling
/// `var(name)` resolves the name to the correct `Expr::bvar(idx)` by
/// searching the scope from innermost to outermost.
#[must_use]
pub(crate) struct ProofBuilder {
    /// Stack of bound variable names, ordered outermost-first.
    /// The last element is the innermost (most recently bound) variable.
    scope: Vec<String>,
}

impl ProofBuilder {
    /// Create a new builder with an empty scope.
    pub(crate) fn new() -> Self {
        ProofBuilder { scope: Vec::new() }
    }

    // ── Core expression constructors (thin wrappers) ─────────────────

    /// Bound variable by explicit de Bruijn index.
    pub(crate) fn bvar(&self, idx: u32) -> Expr {
        Expr::bvar(idx)
    }

    /// Sort expression from a universe level.
    pub(crate) fn sort(&self, level: Level) -> Expr {
        Expr::sort(level)
    }

    /// Prop (Sort 0).
    pub(crate) fn prop(&self) -> Expr {
        Expr::prop()
    }

    /// Type (Sort 1).
    pub(crate) fn type_(&self) -> Expr {
        Expr::type_()
    }

    /// Constant reference from a dotted name string, no universe levels.
    pub(crate) fn const_expr(&self, name: &str) -> Expr {
        Expr::const_str(name)
    }

    /// Constant reference with explicit universe levels.
    pub(crate) fn const_levels(&self, name: &str, levels: Vec<Level>) -> Expr {
        Expr::const_str_levels(name, levels)
    }

    /// Natural number literal.
    pub(crate) fn nat_lit(&self, n: u64) -> Expr {
        Expr::nat_lit(n)
    }

    // ── Named variable lookup ────────────────────────────────────────

    /// Resolve a named variable to its de Bruijn index.
    ///
    /// Searches the scope from innermost (last) to outermost (first).
    /// The de Bruijn index is `scope.len() - 1 - position` where
    /// `position` is the index in the scope vec.
    ///
    /// # Panics
    ///
    /// Panics if `name` is not in scope. This is intentional: an unknown
    /// variable name during proof construction is always a programming error.
    pub(crate) fn var(&self, name: &str) -> Expr {
        let pos = self
            .scope
            .iter()
            .rposition(|n| n == name)
            .unwrap_or_else(|| {
                panic!(
                    "variable '{name}' not in scope; current scope: {:?}",
                    self.scope
                )
            });
        let idx = (self.scope.len() - 1 - pos) as u32;
        Expr::bvar(idx)
    }

    /// Check whether a variable name is currently in scope.
    pub(crate) fn has_var(&self, name: &str) -> bool {
        self.scope.iter().any(|n| n == name)
    }

    // ── Binding constructs with scope tracking ───────────────────────

    /// Lambda abstraction with explicit (default) binder info.
    ///
    /// The `ty` argument is evaluated in the current scope (before the
    /// new variable is pushed). The `body` closure receives the builder
    /// with the new variable in scope.
    pub(crate) fn lam(
        &mut self,
        name: &str,
        ty: Expr,
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.binder(name, ty, BinderInfo::Default, body, true)
    }

    /// Lambda abstraction with implicit binder info (`{x : T}`).
    pub(crate) fn lam_implicit(
        &mut self,
        name: &str,
        ty: Expr,
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.binder(name, ty, BinderInfo::Implicit, body, true)
    }

    /// Pi/forall type with explicit (default) binder info.
    pub(crate) fn pi(
        &mut self,
        name: &str,
        ty: Expr,
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.binder(name, ty, BinderInfo::Default, body, false)
    }

    /// Pi/forall type with implicit binder info (`{x : T}`).
    pub(crate) fn pi_implicit(
        &mut self,
        name: &str,
        ty: Expr,
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.binder(name, ty, BinderInfo::Implicit, body, false)
    }

    /// Non-dependent arrow type `from -> to`.
    pub(crate) fn arrow(&self, from: Expr, to: Expr) -> Expr {
        Expr::arrow(from, to)
    }

    /// Internal: build a binder (lam or pi) with scope management.
    fn binder(
        &mut self,
        name: &str,
        ty: Expr,
        info: BinderInfo,
        body: impl FnOnce(&mut Self) -> Expr,
        is_lam: bool,
    ) -> Expr {
        self.scope.push(name.to_string());
        let body_expr = body(self);
        self.scope.pop();
        if is_lam {
            Expr::lam(info, ty, body_expr)
        } else {
            Expr::pi(info, ty, body_expr)
        }
    }

    // ── Application helpers ──────────────────────────────────────────

    /// Function application `func arg`.
    pub(crate) fn app(&self, func: Expr, arg: Expr) -> Expr {
        Expr::app(func, arg)
    }

    /// Multi-argument application `func arg1 arg2 ... argN`.
    ///
    /// Applies arguments left-to-right: `app_n(f, [a, b, c])` = `((f a) b) c`.
    pub(crate) fn app_n(&self, func: Expr, args: Vec<Expr>) -> Expr {
        Expr::apps(func, args)
    }

    // ── Equality proof combinators ───────────────────────────────────
    //
    // These build Expr application trees for standard equality lemmas.
    // They mirror the Lean 4 API: `@Eq.refl`, `@Eq.symm`, etc.
    // Universe level `u` is left as zero for simplicity; callers can use
    // `const_levels` for polymorphic versions.

    /// `@Eq.refl ty val` -- proof that `val = val`.
    pub(crate) fn eq_refl(&self, ty: Expr, val: Expr) -> Expr {
        Expr::apps(self.const_expr("Eq.refl"), [ty, val])
    }

    /// `@Eq.symm ty a b proof` -- from `a = b` produce `b = a`.
    pub(crate) fn eq_symm(&self, ty: Expr, a: Expr, b: Expr, proof: Expr) -> Expr {
        Expr::apps(self.const_expr("Eq.symm"), [ty, a, b, proof])
    }

    /// `@Eq.trans ty a b c h1 h2` -- from `a = b` and `b = c` produce `a = c`.
    pub(crate) fn eq_trans(&self, ty: Expr, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.const_expr("Eq.trans"), [ty, a, b, c, h1, h2])
    }

    /// `@congrArg alpha beta f a b proof` -- congruence in the argument position.
    ///
    /// Given `proof : a = b`, produces `f a = f b`.
    pub(crate) fn congr_arg(
        &self,
        alpha: Expr,
        beta: Expr,
        f: Expr,
        a: Expr,
        b: Expr,
        proof: Expr,
    ) -> Expr {
        Expr::apps(self.const_expr("congrArg"), [alpha, beta, f, a, b, proof])
    }

    /// `@Nat.rec motive zero_case succ_case n` -- Nat recursor application.
    pub(crate) fn nat_rec(&self, motive: Expr, zero_case: Expr, succ_case: Expr, n: Expr) -> Expr {
        Expr::apps(
            self.const_expr("Nat.rec"),
            [motive, zero_case, succ_case, n],
        )
    }

    /// `@Bool.casesOn motive b true_case false_case` -- Bool case split.
    pub(crate) fn bool_cases(
        &self,
        motive: Expr,
        b: Expr,
        true_case: Expr,
        false_case: Expr,
    ) -> Expr {
        Expr::apps(
            self.const_expr("Bool.casesOn"),
            [motive, b, true_case, false_case],
        )
    }

    // ── Domain-specific combinators (DefEq, Typing, etc.) ────────────

    /// `DefEq.refl e` -- reflexivity of definitional equality.
    pub(crate) fn def_eq_refl(&self, e: Expr) -> Expr {
        self.app(self.const_expr("DefEq.refl"), e)
    }

    /// `DefEq.symm a b h` -- symmetry of definitional equality.
    pub(crate) fn def_eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.const_expr("DefEq.symm"), [a, b, h])
    }

    /// `DefEq.trans a b c h1 h2` -- transitivity of definitional equality.
    pub(crate) fn def_eq_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.const_expr("DefEq.trans"), [a, b, c, h1, h2])
    }

    /// `DefEq.app_cong f f' a a' hf ha` -- application congruence.
    pub(crate) fn def_eq_app_cong(
        &self,
        f: Expr,
        f_prime: Expr,
        a: Expr,
        a_prime: Expr,
        hf: Expr,
        ha: Expr,
    ) -> Expr {
        Expr::apps(
            self.const_expr("DefEq.app_cong"),
            [f, f_prime, a, a_prime, hf, ha],
        )
    }

    // ── Multi-binder helpers ──────────────────────────────────────────

    /// Multi-lambda abstraction from a slice of (name, type) pairs.
    ///
    /// `lam_n(&[("a", ty_a), ("b", ty_b)], |b| body)` produces
    /// `fun (a : ty_a) (b : ty_b) => body` with both names in scope
    /// inside the body closure.
    ///
    /// Types are pre-evaluated before any scope push. If a later type
    /// needs to reference an earlier binder, use nested `lam` calls instead.
    pub(crate) fn lam_n(
        &mut self,
        names_types: &[(&str, Expr)],
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.binder_n(names_types, body, true)
    }

    /// Multi-pi type from a slice of (name, type) pairs.
    ///
    /// `pi_n(&[("a", ty_a), ("b", ty_b)], |b| body)` produces
    /// `forall (a : ty_a) (b : ty_b), body`.
    pub(crate) fn pi_n(
        &mut self,
        names_types: &[(&str, Expr)],
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.binder_n(names_types, body, false)
    }

    /// Internal: build nested binders (lam or pi) from a slice.
    fn binder_n(
        &mut self,
        names_types: &[(&str, Expr)],
        body: impl FnOnce(&mut Self) -> Expr,
        is_lam: bool,
    ) -> Expr {
        // Push all names into scope
        for (name, _) in names_types {
            self.scope.push(name.to_string());
        }

        // Evaluate the body with all names in scope
        let body_expr = body(self);

        // Pop all names
        for _ in 0..names_types.len() {
            self.scope.pop();
        }

        // Build nested binders from inside out (reverse iteration)
        let mut result = body_expr;
        for (_, ty) in names_types.iter().rev() {
            if is_lam {
                result = Expr::lam(BinderInfo::Default, ty.clone(), result);
            } else {
                result = Expr::pi(BinderInfo::Default, ty.clone(), result);
            }
        }
        result
    }

    // ── Let binding ─────────────────────────────────────────────────

    /// Let binding with scope tracking.
    ///
    /// `let_expr("x", ty, val, |b| body)` produces `let x : ty := val in body`.
    /// The variable `x` is in scope inside the body closure.
    pub(crate) fn let_expr(
        &mut self,
        name: &str,
        ty: Expr,
        val: Expr,
        body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        self.scope.push(name.to_string());
        let body_expr = body(self);
        self.scope.pop();
        Expr::let_named(Name::from_string(name), ty, val, body_expr, false)
    }

    // ── Additional DefEq combinators ────────────────────────────────

    /// `DefEq.lam_cong A A' b b' hA hb` -- lambda congruence.
    ///
    /// Given `hA : DefEq A A'` and `hb : DefEq b b'`, produces
    /// `DefEq (lam A b) (lam A' b')`.
    pub(crate) fn def_eq_lam_cong(
        &self,
        a: Expr,
        a_prime: Expr,
        b: Expr,
        b_prime: Expr,
        ha: Expr,
        hb: Expr,
    ) -> Expr {
        Expr::apps(
            self.const_expr("DefEq.lam_cong"),
            [a, a_prime, b, b_prime, ha, hb],
        )
    }

    /// `DefEq.pi_cong A A' B B' hA hB` -- pi congruence.
    ///
    /// Given `hA : DefEq A A'` and `hB : DefEq B B'`, produces
    /// `DefEq (pi A B) (pi A' B')`.
    pub(crate) fn def_eq_pi_cong(
        &self,
        a: Expr,
        a_prime: Expr,
        b: Expr,
        b_prime: Expr,
        ha: Expr,
        hb: Expr,
    ) -> Expr {
        Expr::apps(
            self.const_expr("DefEq.pi_cong"),
            [a, a_prime, b, b_prime, ha, hb],
        )
    }

    /// `DefEq.beta A b a B u hA hb ha` -- typed beta reduction.
    ///
    /// Produces `DefEq (app (lam A b) a) (instantiate b a)`.
    pub(crate) fn def_eq_beta(
        &self,
        a_dom: Expr,
        body: Expr,
        arg: Expr,
        body_ty: Expr,
        u: Expr,
        h_a_dom: Expr,
        h_body: Expr,
        h_arg: Expr,
    ) -> Expr {
        Expr::apps(
            self.const_expr("DefEq.beta"),
            [a_dom, body, arg, body_ty, u, h_a_dom, h_body, h_arg],
        )
    }

    // ── Typing combinators ──────────────────────────────────────────

    /// `Typing e T` -- typing judgment application.
    pub(crate) fn typing(&self, e: Expr, t: Expr) -> Expr {
        Expr::apps(self.const_expr("Typing"), [e, t])
    }

    /// `has_type e T` -- has_type predicate application.
    pub(crate) fn has_type_expr(&self, e: Expr, t: Expr) -> Expr {
        Expr::apps(self.const_expr("has_type"), [e, t])
    }

    // ── Value / WHNF combinators ────────────────────────────────────

    /// `IsValue e` -- value predicate.
    pub(crate) fn is_value_expr(&self, e: Expr) -> Expr {
        self.app(self.const_expr("IsValue"), e)
    }

    /// `IsValue.sort n` -- sort is a value.
    pub(crate) fn is_value_sort(&self, n: Expr) -> Expr {
        self.app(self.const_expr("IsValue.sort"), n)
    }

    /// `IsValue.lam ty body` -- lambda is a value.
    pub(crate) fn is_value_lam(&self, ty: Expr, body: Expr) -> Expr {
        Expr::apps(self.const_expr("IsValue.lam"), [ty, body])
    }

    /// `IsValue.pi ty body` -- pi type is a value.
    pub(crate) fn is_value_pi(&self, ty: Expr, body: Expr) -> Expr {
        Expr::apps(self.const_expr("IsValue.pi"), [ty, body])
    }

    /// `whnf_to e e'` -- WHNF reduction predicate.
    pub(crate) fn whnf_to_expr(&self, e: Expr, e_prime: Expr) -> Expr {
        Expr::apps(self.const_expr("whnf_to"), [e, e_prime])
    }

    /// `WhnfTo.refl e h` -- WHNF reflexivity constructor.
    pub(crate) fn whnf_to_refl(&self, e: Expr, h: Expr) -> Expr {
        Expr::apps(self.const_expr("WhnfTo.refl"), [e, h])
    }

    // ── Logical combinators ─────────────────────────────────────────

    /// `AndType.intro h1 h2` -- conjunction introduction.
    pub(crate) fn and_intro(&self, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.const_expr("AndType.intro"), [h1, h2])
    }

    /// `Or.inl h` -- left disjunction introduction.
    pub(crate) fn or_inl(&self, h: Expr) -> Expr {
        self.app(self.const_expr("Or.inl"), h)
    }

    /// `Or.inr h` -- right disjunction introduction.
    pub(crate) fn or_inr(&self, h: Expr) -> Expr {
        self.app(self.const_expr("Or.inr"), h)
    }

    // ── Ordering / comparison combinators ────────────────────────────

    /// `le_trans a b c h1 h2` -- transitivity of `<=`.
    pub(crate) fn le_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.const_expr("le_trans"), [a, b, c, h1, h2])
    }

    // ── String literal ──────────────────────────────────────────────

    /// String literal expression.
    pub(crate) fn str_lit(&self, s: &str) -> Expr {
        Expr::str_lit(s)
    }

    // ── Scope depth query ────────────────────────────────────────────

    /// Current binding depth (number of variables in scope).
    pub(crate) fn depth(&self) -> usize {
        self.scope.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::ExprKind;

    // ── Helper: extract ExprKind for pattern matching ─────────────────

    fn is_bvar(e: &Expr, expected_idx: u32) -> bool {
        matches!(e.kind(), ExprKind::BVar(idx) if *idx == expected_idx)
    }

    fn is_const_named(e: &Expr, expected: &str) -> bool {
        matches!(e.kind(), ExprKind::Const(name, _) if name.to_string() == expected)
    }

    // ── Basic constructor tests ──────────────────────────────────────

    #[test]
    fn test_proof_builder_bvar_returns_correct_index() {
        let b = ProofBuilder::new();
        let e = b.bvar(42);
        assert!(is_bvar(&e, 42));
    }

    #[test]
    fn test_proof_builder_const_expr_returns_const() {
        let b = ProofBuilder::new();
        let e = b.const_expr("Nat.add");
        assert!(is_const_named(&e, "Nat.add"));
    }

    #[test]
    fn test_proof_builder_prop_and_type() {
        let b = ProofBuilder::new();
        assert!(b.prop().is_sort());
        assert!(b.type_().is_sort());
    }

    // ── Named variable resolution ────────────────────────────────────

    #[test]
    fn test_proof_builder_var_resolves_innermost() {
        // fun (x : Prop) => x
        // Inside the lambda, var("x") should be bvar(0)
        let mut b = ProofBuilder::new();
        let result = b.lam("x", b.prop(), |b| b.var("x"));

        match result.kind() {
            ExprKind::Lam(_, _, body) => {
                assert!(is_bvar(body, 0), "x should resolve to bvar(0)");
            }
            _ => panic!("expected Lam"),
        }
    }

    #[test]
    fn test_proof_builder_var_resolves_outer() {
        // fun (A : Type) (x : A) => A
        // Inside the inner lambda, var("A") should be bvar(1)
        let mut b = ProofBuilder::new();
        let result = b.lam("A", b.type_(), |b| b.lam("x", b.var("A"), |b| b.var("A")));

        // Navigate to inner body
        match result.kind() {
            ExprKind::Lam(_, _, outer_body) => match outer_body.kind() {
                ExprKind::Lam(_, _, inner_body) => {
                    assert!(is_bvar(inner_body, 1), "A should resolve to bvar(1)");
                }
                _ => panic!("expected inner Lam"),
            },
            _ => panic!("expected outer Lam"),
        }
    }

    #[test]
    fn test_proof_builder_var_type_position_uses_outer_scope() {
        // fun (A : Type) (x : A) => x
        // The type of x is `A`. When evaluating the type argument to lam("x", ...),
        // the scope only contains ["A"], so var("A") = bvar(0).
        // But inside the body closure, scope = ["A", "x"], so var("x") = bvar(0)
        // and var("A") = bvar(1).
        let mut b = ProofBuilder::new();
        let result = b.lam("A", b.type_(), |b| b.lam("x", b.var("A"), |b| b.var("x")));

        match result.kind() {
            ExprKind::Lam(_, _, outer_body) => match outer_body.kind() {
                ExprKind::Lam(_, ty, body) => {
                    // ty of x is A, which was bvar(0) in the outer scope
                    assert!(is_bvar(ty, 0), "type of x should be bvar(0) = A");
                    // body is x = bvar(0) in the inner scope
                    assert!(is_bvar(body, 0), "body should be bvar(0) = x");
                }
                _ => panic!("expected inner Lam"),
            },
            _ => panic!("expected outer Lam"),
        }
    }

    #[test]
    #[should_panic(expected = "not in scope")]
    fn test_proof_builder_var_panics_on_unknown() {
        let b = ProofBuilder::new();
        let _ = b.var("nonexistent");
    }

    #[test]
    fn test_proof_builder_has_var() {
        let mut b = ProofBuilder::new();
        assert!(!b.has_var("x"));
        let _ = b.lam("x", b.prop(), |b| {
            assert!(b.has_var("x"));
            assert!(!b.has_var("y"));
            b.var("x")
        });
        assert!(!b.has_var("x"));
    }

    #[test]
    fn test_proof_builder_scope_restored_after_lam() {
        let mut b = ProofBuilder::new();
        assert_eq!(b.depth(), 0);
        let _ = b.lam("x", b.prop(), |b| {
            assert_eq!(b.depth(), 1);
            b.var("x")
        });
        assert_eq!(b.depth(), 0);
    }

    // ── Pi type tests ────────────────────────────────────────────────

    #[test]
    fn test_proof_builder_pi_constructs_pi_type() {
        let mut b = ProofBuilder::new();
        let result = b.pi("A", b.type_(), |b| b.var("A"));
        assert!(result.is_pi());
    }

    // ── Application tests ────────────────────────────────────────────

    #[test]
    fn test_proof_builder_app_constructs_application() {
        let b = ProofBuilder::new();
        let f = b.const_expr("f");
        let a = b.const_expr("a");
        let result = b.app(f, a);
        assert!(result.is_app());
    }

    #[test]
    fn test_proof_builder_app_n_multi_arg() {
        let b = ProofBuilder::new();
        let f = b.const_expr("f");
        let a = b.const_expr("a");
        let bb = b.const_expr("b");
        let c = b.const_expr("c");
        let result = b.app_n(f, vec![a, bb, c]);

        // Result should be ((f a) b) c — three nested applications
        assert!(result.is_app());
        match result.kind() {
            ExprKind::App(inner, arg_c) => {
                assert!(is_const_named(arg_c, "c"));
                assert!(inner.is_app());
                match inner.kind() {
                    ExprKind::App(inner2, arg_b) => {
                        assert!(is_const_named(arg_b, "b"));
                        assert!(inner2.is_app());
                    }
                    _ => panic!("expected nested App"),
                }
            }
            _ => panic!("expected App"),
        }
    }

    // ── Equality combinator tests ────────────────────────────────────

    #[test]
    fn test_proof_builder_eq_refl_structure() {
        let b = ProofBuilder::new();
        let ty = b.const_expr("Nat");
        let val = b.nat_lit(42);
        let result = b.eq_refl(ty, val);

        // Should be: App(App(Const("Eq.refl"), Const("Nat")), Lit(42))
        assert!(result.is_app());
        let head = result.get_app_fn();
        assert!(is_const_named(head, "Eq.refl"));
        assert_eq!(result.get_app_num_args(), 2);
    }

    #[test]
    fn test_proof_builder_eq_symm_structure() {
        let b = ProofBuilder::new();
        let result = b.eq_symm(
            b.const_expr("T"),
            b.const_expr("a"),
            b.const_expr("b"),
            b.const_expr("h"),
        );
        let head = result.get_app_fn();
        assert!(is_const_named(head, "Eq.symm"));
        assert_eq!(result.get_app_num_args(), 4);
    }

    #[test]
    fn test_proof_builder_eq_trans_structure() {
        let b = ProofBuilder::new();
        let result = b.eq_trans(
            b.const_expr("T"),
            b.const_expr("a"),
            b.const_expr("b"),
            b.const_expr("c"),
            b.const_expr("h1"),
            b.const_expr("h2"),
        );
        let head = result.get_app_fn();
        assert!(is_const_named(head, "Eq.trans"));
        assert_eq!(result.get_app_num_args(), 6);
    }

    // ── Reconstruct existing proofs ──────────────────────────────────
    //
    // These tests build proof term Exprs that correspond to existing proofs
    // in library.rs, verifying structural equivalence.

    /// Reconstruct `def_eq_refl`:
    /// `fun (e : KExpr) => DefEq.refl e`
    #[test]
    fn test_proof_builder_reconstruct_def_eq_refl() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam("e", kexpr, |b| b.def_eq_refl(b.var("e")));

        // Verify structure: Lam(_, KExpr, App(Const("DefEq.refl"), BVar(0)))
        match proof.kind() {
            ExprKind::Lam(_, ty, body) => {
                assert!(is_const_named(ty, "KExpr"), "type should be KExpr");
                match body.kind() {
                    ExprKind::App(func, arg) => {
                        assert!(
                            is_const_named(func, "DefEq.refl"),
                            "func should be DefEq.refl"
                        );
                        assert!(is_bvar(arg, 0), "arg should be bvar(0) = e");
                    }
                    _ => panic!("expected App in body"),
                }
            }
            _ => panic!("expected Lam"),
        }
    }

    /// Reconstruct `def_eq_symm`:
    /// `fun (a : KExpr) (b : KExpr) (h : DefEq a b) => DefEq.symm a b h`
    #[test]
    fn test_proof_builder_reconstruct_def_eq_symm() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam("a", kexpr.clone(), |b| {
            let kexpr = b.const_expr("KExpr");
            b.lam("b", kexpr, |b| {
                // Type of h: DefEq a b
                // At this scope depth, a = bvar(1), b = bvar(0)
                let def_eq_a_b = b.app_n(b.const_expr("DefEq"), vec![b.var("a"), b.var("b")]);
                b.lam("h", def_eq_a_b, |b| {
                    b.def_eq_symm(b.var("a"), b.var("b"), b.var("h"))
                })
            })
        });

        // Navigate to innermost body: DefEq.symm a b h
        match proof.kind() {
            ExprKind::Lam(_, _, body1) => match body1.kind() {
                ExprKind::Lam(_, _, body2) => match body2.kind() {
                    ExprKind::Lam(_, _, body3) => {
                        // body3 = DefEq.symm a b h
                        let head = body3.get_app_fn();
                        assert!(
                            is_const_named(head, "DefEq.symm"),
                            "head should be DefEq.symm"
                        );
                        assert_eq!(body3.get_app_num_args(), 3);

                        // Check args: a=bvar(2), b=bvar(1), h=bvar(0)
                        let args = body3.get_app_args();
                        assert!(is_bvar(args[0], 2), "first arg should be bvar(2) = a");
                        assert!(is_bvar(args[1], 1), "second arg should be bvar(1) = b");
                        assert!(is_bvar(args[2], 0), "third arg should be bvar(0) = h");
                    }
                    _ => panic!("expected innermost Lam"),
                },
                _ => panic!("expected middle Lam"),
            },
            _ => panic!("expected outer Lam"),
        }
    }

    /// Reconstruct `def_eq_trans`:
    /// `fun (a : KExpr) (b : KExpr) (c : KExpr) (h1 : DefEq a b) (h2 : DefEq b c)
    ///    => DefEq.trans a b c h1 h2`
    #[test]
    fn test_proof_builder_reconstruct_def_eq_trans() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam("a", kexpr.clone(), |b| {
            let kexpr = b.const_expr("KExpr");
            b.lam("b", kexpr.clone(), |b| {
                let kexpr = b.const_expr("KExpr");
                b.lam("c", kexpr, |b| {
                    // h1 : DefEq a b
                    let h1_ty = b.app_n(b.const_expr("DefEq"), vec![b.var("a"), b.var("b")]);
                    b.lam("h1", h1_ty, |b| {
                        // h2 : DefEq b c
                        let h2_ty = b.app_n(b.const_expr("DefEq"), vec![b.var("b"), b.var("c")]);
                        b.lam("h2", h2_ty, |b| {
                            b.def_eq_trans(
                                b.var("a"),
                                b.var("b"),
                                b.var("c"),
                                b.var("h1"),
                                b.var("h2"),
                            )
                        })
                    })
                })
            })
        });

        // Navigate to the innermost body (5 lambdas deep)
        let mut current = &proof;
        for _ in 0..5 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                _ => panic!("expected Lam"),
            }
        }

        // current = DefEq.trans a b c h1 h2
        let head = current.get_app_fn();
        assert!(
            is_const_named(head, "DefEq.trans"),
            "head should be DefEq.trans"
        );
        assert_eq!(current.get_app_num_args(), 5);

        let args = current.get_app_args();
        // scope at depth 5: ["a", "b", "c", "h1", "h2"]
        // a = bvar(4), b = bvar(3), c = bvar(2), h1 = bvar(1), h2 = bvar(0)
        assert!(is_bvar(args[0], 4), "a should be bvar(4)");
        assert!(is_bvar(args[1], 3), "b should be bvar(3)");
        assert!(is_bvar(args[2], 2), "c should be bvar(2)");
        assert!(is_bvar(args[3], 1), "h1 should be bvar(1)");
        assert!(is_bvar(args[4], 0), "h2 should be bvar(0)");
    }

    /// Test shadowing: inner variable with same name shadows outer.
    #[test]
    fn test_proof_builder_shadowing() {
        let mut b = ProofBuilder::new();
        let result = b.lam("x", b.prop(), |b| {
            b.lam("x", b.prop(), |b| {
                b.var("x") // should be bvar(0) — the inner x
            })
        });

        match result.kind() {
            ExprKind::Lam(_, _, body) => match body.kind() {
                ExprKind::Lam(_, _, inner_body) => {
                    assert!(is_bvar(inner_body, 0), "inner x should shadow to bvar(0)");
                }
                _ => panic!("expected inner Lam"),
            },
            _ => panic!("expected outer Lam"),
        }
    }

    /// Test that depth tracks correctly through nested binders.
    #[test]
    fn test_proof_builder_depth_tracking() {
        let mut b = ProofBuilder::new();
        assert_eq!(b.depth(), 0);

        let _ = b.lam("a", b.prop(), |b| {
            assert_eq!(b.depth(), 1);
            b.lam("b", b.prop(), |b| {
                assert_eq!(b.depth(), 2);
                b.pi("c", b.prop(), |b| {
                    assert_eq!(b.depth(), 3);
                    b.var("a")
                })
            })
        });

        assert_eq!(b.depth(), 0);
    }

    /// Test mixed lam and pi produce correct ExprKind variants.
    #[test]
    fn test_proof_builder_mixed_lam_pi() {
        let mut b = ProofBuilder::new();

        let pi_expr = b.pi("A", b.type_(), |b| b.arrow(b.var("A"), b.var("A")));
        assert!(pi_expr.is_pi());

        let lam_expr = b.lam("A", b.type_(), |b| b.lam("x", b.var("A"), |b| b.var("x")));
        assert!(lam_expr.is_lam());
    }

    /// Test implicit binder info is preserved.
    #[test]
    fn test_proof_builder_implicit_binder_info() {
        let mut b = ProofBuilder::new();

        let result = b.lam_implicit("A", b.type_(), |b| b.var("A"));
        match result.kind() {
            ExprKind::Lam(bd, _, _) => {
                assert_eq!(bd.info, BinderInfo::Implicit);
            }
            _ => panic!("expected Lam"),
        }

        let result = b.pi_implicit("A", b.type_(), |b| b.var("A"));
        match result.kind() {
            ExprKind::Pi(bd, _, _) => {
                assert_eq!(bd.info, BinderInfo::Implicit);
            }
            _ => panic!("expected Pi"),
        }
    }

    /// Boilerplate comparison: building def_eq_app_cong with builder vs raw Expr.
    ///
    /// With builder (~10 LOC):
    /// ```text
    /// b.lam("f", kexpr, |b| b.lam("f'", kexpr, |b| b.lam("a", kexpr, |b|
    ///     b.lam("a'", kexpr, |b| b.lam("hf", ..., |b| b.lam("ha", ..., |b|
    ///         b.def_eq_app_cong(b.var("f"), b.var("f'"), b.var("a"), b.var("a'"),
    ///                           b.var("hf"), b.var("ha"))))))))
    /// ```
    ///
    /// Without builder (~30+ LOC of manual bvar index computation).
    #[test]
    fn test_proof_builder_reconstruct_def_eq_app_cong() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam("f", kexpr.clone(), |b| {
            let kexpr = b.const_expr("KExpr");
            b.lam("f'", kexpr.clone(), |b| {
                let kexpr = b.const_expr("KExpr");
                b.lam("a", kexpr.clone(), |b| {
                    let kexpr = b.const_expr("KExpr");
                    b.lam("a'", kexpr, |b| {
                        let hf_ty = b.app_n(b.const_expr("DefEq"), vec![b.var("f"), b.var("f'")]);
                        b.lam("hf", hf_ty, |b| {
                            let ha_ty =
                                b.app_n(b.const_expr("DefEq"), vec![b.var("a"), b.var("a'")]);
                            b.lam("ha", ha_ty, |b| {
                                b.def_eq_app_cong(
                                    b.var("f"),
                                    b.var("f'"),
                                    b.var("a"),
                                    b.var("a'"),
                                    b.var("hf"),
                                    b.var("ha"),
                                )
                            })
                        })
                    })
                })
            })
        });

        // Navigate 6 lambdas deep to the body
        let mut current = &proof;
        for _ in 0..6 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                _ => panic!("expected Lam"),
            }
        }

        let head = current.get_app_fn();
        assert!(is_const_named(head, "DefEq.app_cong"));
        assert_eq!(current.get_app_num_args(), 6);

        let args = current.get_app_args();
        // scope: ["f", "f'", "a", "a'", "hf", "ha"]
        // f=5, f'=4, a=3, a'=2, hf=1, ha=0
        assert!(is_bvar(args[0], 5), "f");
        assert!(is_bvar(args[1], 4), "f'");
        assert!(is_bvar(args[2], 3), "a");
        assert!(is_bvar(args[3], 2), "a'");
        assert!(is_bvar(args[4], 1), "hf");
        assert!(is_bvar(args[5], 0), "ha");
    }

    // ── lam_n / pi_n tests ──────────────────────────────────────────

    /// lam_n with 3 params produces correct nested lambdas.
    #[test]
    fn test_proof_builder_lam_n_basic() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam_n(
            &[("a", kexpr.clone()), ("b", kexpr.clone()), ("c", kexpr)],
            |b| b.var("b"),
        );

        // Navigate 3 lambdas deep
        let mut current = &proof;
        for _ in 0..3 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                _ => panic!("expected Lam"),
            }
        }
        // scope was ["a", "b", "c"], b = bvar(1)
        assert!(is_bvar(current, 1), "b should be bvar(1)");
    }

    /// lam_n with empty slice returns body directly.
    #[test]
    fn test_proof_builder_lam_n_empty() {
        let mut b = ProofBuilder::new();
        let result = b.lam_n(&[], |b| b.const_expr("X"));
        assert!(is_const_named(&result, "X"));
    }

    /// lam_n scope is restored after call.
    #[test]
    fn test_proof_builder_lam_n_scope_restored() {
        let mut b = ProofBuilder::new();
        assert_eq!(b.depth(), 0);
        let _ = b.lam_n(&[("x", b.prop()), ("y", b.prop())], |b| {
            assert_eq!(b.depth(), 2);
            b.var("x")
        });
        assert_eq!(b.depth(), 0);
    }

    /// pi_n produces nested Pi types.
    #[test]
    fn test_proof_builder_pi_n_basic() {
        let mut b = ProofBuilder::new();
        let result = b.pi_n(&[("A", b.type_()), ("B", b.type_())], |b| {
            b.arrow(b.var("A"), b.var("B"))
        });
        assert!(result.is_pi());
        match result.kind() {
            ExprKind::Pi(_, _, body) => assert!(body.is_pi()),
            _ => panic!("expected Pi"),
        }
    }

    /// lam_n produces equivalent structure to nested lam calls.
    #[test]
    fn test_proof_builder_lam_n_equals_nested_lam() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        // Build with lam_n
        let via_lam_n = b.lam_n(&[("a", kexpr.clone()), ("b", kexpr.clone())], |b| {
            b.def_eq_symm(b.var("a"), b.var("b"), b.const_expr("h"))
        });

        // Build with nested lam
        let via_nested = b.lam("a", kexpr.clone(), |b| {
            b.lam("b", kexpr, |b| {
                b.def_eq_symm(b.var("a"), b.var("b"), b.const_expr("h"))
            })
        });

        // Both should produce the same structure
        // Navigate to body of both and compare
        fn inner_body(e: &Expr) -> &Expr {
            match e.kind() {
                ExprKind::Lam(_, _, b1) => match b1.kind() {
                    ExprKind::Lam(_, _, b2) => b2.as_ref(),
                    _ => panic!("expected inner Lam"),
                },
                _ => panic!("expected outer Lam"),
            }
        }

        let body_n = inner_body(&via_lam_n);
        let body_nested = inner_body(&via_nested);

        // Both bodies should be DefEq.symm(bvar(1), bvar(0), Const("h"))
        assert_eq!(body_n.get_app_num_args(), body_nested.get_app_num_args());
        let args_n = body_n.get_app_args();
        let args_nested = body_nested.get_app_args();
        assert!(is_bvar(args_n[0], 1));
        assert!(is_bvar(args_nested[0], 1));
        assert!(is_bvar(args_n[1], 0));
        assert!(is_bvar(args_nested[1], 0));
    }

    // ── let_expr tests ──────────────────────────────────────────────

    #[test]
    fn test_proof_builder_let_expr_basic() {
        let mut b = ProofBuilder::new();
        let result = b.let_expr("x", b.const_expr("Nat"), b.nat_lit(42), |b| b.var("x"));
        assert!(result.is_let());
    }

    #[test]
    fn test_proof_builder_let_expr_scope_restored() {
        let mut b = ProofBuilder::new();
        assert_eq!(b.depth(), 0);
        let _ = b.let_expr("x", b.prop(), b.prop(), |b| {
            assert_eq!(b.depth(), 1);
            assert!(b.has_var("x"));
            b.var("x")
        });
        assert_eq!(b.depth(), 0);
        assert!(!b.has_var("x"));
    }

    // ── DefEq congruence combinator tests ───────────────────────────

    #[test]
    fn test_proof_builder_def_eq_lam_cong_structure() {
        let b = ProofBuilder::new();
        let result = b.def_eq_lam_cong(
            b.const_expr("A"),
            b.const_expr("A'"),
            b.const_expr("b"),
            b.const_expr("b'"),
            b.const_expr("hA"),
            b.const_expr("hb"),
        );
        let head = result.get_app_fn();
        assert!(is_const_named(head, "DefEq.lam_cong"));
        assert_eq!(result.get_app_num_args(), 6);
    }

    #[test]
    fn test_proof_builder_def_eq_pi_cong_structure() {
        let b = ProofBuilder::new();
        let result = b.def_eq_pi_cong(
            b.const_expr("A"),
            b.const_expr("A'"),
            b.const_expr("B"),
            b.const_expr("B'"),
            b.const_expr("hA"),
            b.const_expr("hB"),
        );
        let head = result.get_app_fn();
        assert!(is_const_named(head, "DefEq.pi_cong"));
        assert_eq!(result.get_app_num_args(), 6);
    }

    #[test]
    fn test_proof_builder_def_eq_beta_structure() {
        let b = ProofBuilder::new();
        let result = b.def_eq_beta(
            b.const_expr("A"),
            b.const_expr("b"),
            b.const_expr("a"),
            b.const_expr("B"),
            b.nat_lit(0),
            b.const_expr("hA"),
            b.const_expr("hb"),
            b.const_expr("ha"),
        );
        let head = result.get_app_fn();
        assert!(is_const_named(head, "DefEq.beta"));
        assert_eq!(result.get_app_num_args(), 8);
    }

    // ── Typing combinator tests ─────────────────────────────────────

    #[test]
    fn test_proof_builder_typing_structure() {
        let b = ProofBuilder::new();
        let result = b.typing(b.const_expr("e"), b.const_expr("T"));
        let head = result.get_app_fn();
        assert!(is_const_named(head, "Typing"));
        assert_eq!(result.get_app_num_args(), 2);
    }

    #[test]
    fn test_proof_builder_has_type_expr_structure() {
        let b = ProofBuilder::new();
        let result = b.has_type_expr(b.const_expr("e"), b.const_expr("T"));
        let head = result.get_app_fn();
        assert!(is_const_named(head, "has_type"));
        assert_eq!(result.get_app_num_args(), 2);
    }

    // ── Value / WHNF combinator tests ───────────────────────────────

    #[test]
    fn test_proof_builder_is_value_expr_structure() {
        let b = ProofBuilder::new();
        let result = b.is_value_expr(b.const_expr("e"));
        assert!(result.is_app());
        let head = result.get_app_fn();
        assert!(is_const_named(head, "IsValue"));
    }

    #[test]
    fn test_proof_builder_is_value_constructors() {
        let b = ProofBuilder::new();

        let sort_val = b.is_value_sort(b.nat_lit(1));
        assert!(is_const_named(sort_val.get_app_fn(), "IsValue.sort"));

        let lam_val = b.is_value_lam(b.const_expr("T"), b.const_expr("body"));
        assert!(is_const_named(lam_val.get_app_fn(), "IsValue.lam"));
        assert_eq!(lam_val.get_app_num_args(), 2);

        let pi_val = b.is_value_pi(b.const_expr("T"), b.const_expr("body"));
        assert!(is_const_named(pi_val.get_app_fn(), "IsValue.pi"));
        assert_eq!(pi_val.get_app_num_args(), 2);
    }

    #[test]
    fn test_proof_builder_whnf_to_structure() {
        let b = ProofBuilder::new();
        let result = b.whnf_to_expr(b.const_expr("e"), b.const_expr("e'"));
        let head = result.get_app_fn();
        assert!(is_const_named(head, "whnf_to"));
        assert_eq!(result.get_app_num_args(), 2);
    }

    #[test]
    fn test_proof_builder_whnf_to_refl_structure() {
        let b = ProofBuilder::new();
        let result = b.whnf_to_refl(b.const_expr("e"), b.const_expr("h"));
        let head = result.get_app_fn();
        assert!(is_const_named(head, "WhnfTo.refl"));
        assert_eq!(result.get_app_num_args(), 2);
    }

    // ── Logical combinator tests ────────────────────────────────────

    #[test]
    fn test_proof_builder_and_intro_structure() {
        let b = ProofBuilder::new();
        let result = b.and_intro(b.const_expr("h1"), b.const_expr("h2"));
        let head = result.get_app_fn();
        assert!(is_const_named(head, "AndType.intro"));
        assert_eq!(result.get_app_num_args(), 2);
    }

    #[test]
    fn test_proof_builder_or_inl_inr_structure() {
        let b = ProofBuilder::new();

        let left = b.or_inl(b.const_expr("h"));
        assert!(is_const_named(left.get_app_fn(), "Or.inl"));

        let right = b.or_inr(b.const_expr("h"));
        assert!(is_const_named(right.get_app_fn(), "Or.inr"));
    }

    // ── le_trans test ───────────────────────────────────────────────

    #[test]
    fn test_proof_builder_le_trans_structure() {
        let b = ProofBuilder::new();
        let result = b.le_trans(
            b.nat_lit(1),
            b.nat_lit(2),
            b.nat_lit(3),
            b.const_expr("h1"),
            b.const_expr("h2"),
        );
        let head = result.get_app_fn();
        assert!(is_const_named(head, "le_trans"));
        assert_eq!(result.get_app_num_args(), 5);
    }

    // ── str_lit test ────────────────────────────────────────────────

    #[test]
    fn test_proof_builder_str_lit() {
        let b = ProofBuilder::new();
        let result = b.str_lit("hello");
        assert!(result.is_lit());
    }

    // ── Comprehensive reconstruction with new combinators ───────────

    /// Reconstruct `def_eq_lam_cong` proof from library.rs using
    /// lam_n + the new def_eq_lam_cong combinator:
    /// `fun (A A' b b' : KExpr) (hA : DefEq A A') (hb : DefEq b b')
    ///    => DefEq.lam_cong A A' b b' hA hb`
    ///
    /// This demonstrates the boilerplate reduction: 6 nested lam calls
    /// compressed into 1 lam_n + 2 lam calls.
    #[test]
    fn test_proof_builder_reconstruct_lam_cong_with_lam_n() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam_n(
            &[
                ("A", kexpr.clone()),
                ("A'", kexpr.clone()),
                ("b", kexpr.clone()),
                ("b'", kexpr),
            ],
            |b| {
                let ha_ty = b.app_n(b.const_expr("DefEq"), vec![b.var("A"), b.var("A'")]);
                b.lam("hA", ha_ty, |b| {
                    let hb_ty = b.app_n(b.const_expr("DefEq"), vec![b.var("b"), b.var("b'")]);
                    b.lam("hb", hb_ty, |b| {
                        b.def_eq_lam_cong(
                            b.var("A"),
                            b.var("A'"),
                            b.var("b"),
                            b.var("b'"),
                            b.var("hA"),
                            b.var("hb"),
                        )
                    })
                })
            },
        );

        // Navigate 6 lambdas deep
        let mut current = &proof;
        for _ in 0..6 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                _ => panic!("expected Lam"),
            }
        }

        let head = current.get_app_fn();
        assert!(is_const_named(head, "DefEq.lam_cong"));
        assert_eq!(current.get_app_num_args(), 6);

        // scope: ["A", "A'", "b", "b'", "hA", "hb"]
        // A=5, A'=4, b=3, b'=2, hA=1, hb=0
        let args = current.get_app_args();
        assert!(is_bvar(args[0], 5), "A");
        assert!(is_bvar(args[1], 4), "A'");
        assert!(is_bvar(args[2], 3), "b");
        assert!(is_bvar(args[3], 2), "b'");
        assert!(is_bvar(args[4], 1), "hA");
        assert!(is_bvar(args[5], 0), "hb");
    }

    /// Reconstruct a WHNF proof using the new IsValue + WhnfTo combinators:
    /// `fun (e : KExpr) (h : is_value e) => WhnfTo.refl e (value_is_whnf e h)`
    #[test]
    fn test_proof_builder_reconstruct_value_whnf_proof() {
        let mut b = ProofBuilder::new();
        let kexpr = b.const_expr("KExpr");

        let proof = b.lam("e", kexpr, |b| {
            let is_val_ty = b.is_value_expr(b.var("e"));
            b.lam("h", is_val_ty, |b| {
                let witness = b.app_n(b.const_expr("value_is_whnf"), vec![b.var("e"), b.var("h")]);
                b.whnf_to_refl(b.var("e"), witness)
            })
        });

        // Navigate 2 lambdas deep
        let mut current = &proof;
        for _ in 0..2 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                _ => panic!("expected Lam"),
            }
        }

        // Body should be WhnfTo.refl e (value_is_whnf e h)
        let head = current.get_app_fn();
        assert!(is_const_named(head, "WhnfTo.refl"));
        assert_eq!(current.get_app_num_args(), 2);
    }

    /// Test AndType.intro with builder in a lambda context.
    #[test]
    fn test_proof_builder_and_intro_in_context() {
        let mut b = ProofBuilder::new();
        let proof = b.lam("h1", b.prop(), |b| {
            b.lam("h2", b.prop(), |b| b.and_intro(b.var("h1"), b.var("h2")))
        });

        // Navigate 2 lambdas deep
        let mut current = &proof;
        for _ in 0..2 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                _ => panic!("expected Lam"),
            }
        }

        let head = current.get_app_fn();
        assert!(is_const_named(head, "AndType.intro"));
        let args = current.get_app_args();
        assert!(is_bvar(args[0], 1), "h1 should be bvar(1)");
        assert!(is_bvar(args[1], 0), "h2 should be bvar(0)");
    }
}
