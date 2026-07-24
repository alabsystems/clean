// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term builder DSL for constructing kernel-verified proof terms.
//!
//! Building `Declaration::Theorem` proof terms requires manually constructing
//! Expr trees with exact universe levels, binder info, and type annotations.
//! This module provides `ProofBuilder` which handles the boilerplate:
//!
//! - Universe levels are provided explicitly for correctness
//! - Lambda/Pi binders handle de Bruijn indices correctly via `EnvDeclBuilder`
//! - Every `register_theorem` uses `add_decl` for kernel verification
//!
//! # Universe level conventions
//!
//! Lean 4 constants like `@Eq.{u}` are universe-polymorphic. When constructing
//! concrete proofs about `Nat` (which lives in `Type` = Sort 1), the universe
//! level must be `1` (= `Level::succ(Level::zero())`). For polymorphic theorems,
//! use `Level::param(Name::from_string("u"))` and register with
//! `register_theorem_poly`.
//!
//! The builder provides two families of equality combinators:
//! - `eq_nat`, `eq_refl_nat`, etc.: Hardcode universe level 1 (for Nat proofs)
//! - `eq_at`, `eq_refl_at`, etc.: Take an explicit `Level` argument

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Universe level 1 (= `Type`). Used for types that live in Type, like Nat.
fn level_one() -> Level {
    Level::succ(Level::zero())
}

/// Proof term builder for constructing kernel-verified proof terms.
///
/// Wraps `EnvDeclBuilder` and provides high-level proof combinators that
/// handle universe levels, binder info, and type annotations. Dramatically
/// reduces the boilerplate needed to construct `Declaration::Theorem` terms.
///
/// The builder is stateless: it does not cache or modify the environment.
/// Registration methods take `&mut Environment` for `add_decl` verification.
pub(crate) struct ProofBuilder {
    /// Universe parameter name for polymorphic constructions.
    u: Name,
}

impl ProofBuilder {
    /// Create a new proof builder.
    pub(crate) fn new() -> Self {
        ProofBuilder {
            u: Name::from_string("u"),
        }
    }

    // =========================================================================
    // Common types
    // =========================================================================

    /// `Prop` (Sort 0).
    pub(crate) fn prop(&self) -> Expr {
        Expr::prop()
    }

    /// `Sort u` for the builder's universe parameter.
    pub(crate) fn sort_u(&self) -> Expr {
        Expr::sort(Level::param(self.u.clone()))
    }

    /// `Nat` constant reference.
    pub(crate) fn nat(&self) -> Expr {
        Expr::const_str("Nat")
    }

    /// `Nat.zero` constant reference.
    pub(crate) fn nat_zero(&self) -> Expr {
        Expr::const_str("Nat.zero")
    }

    /// `Nat.succ` constant reference.
    pub(crate) fn nat_succ(&self) -> Expr {
        Expr::const_str("Nat.succ")
    }

    /// `@Nat.succ n` -- apply the successor to a term.
    pub(crate) fn nat_succ_of(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ(), n)
    }

    /// Build a Nat literal: `Nat.zero` or `Nat.succ (... Nat.zero)`.
    pub(crate) fn nat_lit(&self, n: u32) -> Expr {
        let mut result = self.nat_zero();
        for _ in 0..n {
            result = self.nat_succ_of(result);
        }
        result
    }

    /// Non-dependent function type: `from -> to`.
    pub(crate) fn arrow(&self, from: Expr, to: Expr) -> Expr {
        Expr::arrow(from, to)
    }

    // =========================================================================
    // Constant references
    // =========================================================================

    /// Reference a named constant with no universe levels.
    pub(crate) fn const_ref(&self, name: &str) -> Expr {
        Expr::const_str(name)
    }

    /// Reference a named constant with the given universe levels.
    pub(crate) fn const_ref_levels(&self, name: &str, levels: Vec<Level>) -> Expr {
        Expr::const_str_levels(name, levels)
    }

    // =========================================================================
    // Core building blocks
    // =========================================================================

    /// Function application: `f arg`.
    pub(crate) fn app(&self, f: Expr, arg: Expr) -> Expr {
        Expr::app(f, arg)
    }

    /// Multi-argument application: `f a1 a2 ... an`.
    pub(crate) fn apps(&self, f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(f, args)
    }

    /// Build a lambda: `fun (name : ty) => body`.
    ///
    /// The closure receives the bound variable and returns the body.
    /// De Bruijn indices are handled automatically.
    pub(crate) fn lam(&self, name: &str, ty: Expr, body: impl FnOnce(Expr) -> Expr) -> Expr {
        let _ = name; // Name is for documentation; de Bruijn doesn't use it
        let mut b = EnvDeclBuilder::new();
        let (id, var) = b.fresh_local(ty.clone());
        let body_expr = body(var);
        let result = b.mk_lam(id, BinderInfo::Default, ty, body_expr);
        b.finish(result)
    }

    /// Build a Pi/forall type: `(name : ty) -> body`.
    ///
    /// The closure receives the bound variable and returns the body.
    /// De Bruijn indices are handled automatically.
    pub(crate) fn pi(&self, name: &str, ty: Expr, body: impl FnOnce(Expr) -> Expr) -> Expr {
        let _ = name;
        let mut b = EnvDeclBuilder::new();
        let (id, var) = b.fresh_local(ty.clone());
        let body_expr = body(var);
        let result = b.mk_pi(id, BinderInfo::Default, ty, body_expr);
        b.finish(result)
    }

    // =========================================================================
    // Multi-binder construction
    // =========================================================================

    /// Build a term with multiple binders using `EnvDeclBuilder` directly.
    ///
    /// The closure receives a mutable `EnvDeclBuilder` and must return an
    /// expression with all FVars closed (via `mk_pi`/`mk_lam`).
    pub(crate) fn build(&self, f: impl FnOnce(&mut EnvDeclBuilder) -> Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let result = f(&mut b);
        b.finish(result)
    }

    // =========================================================================
    // Equality (universe-explicit)
    // =========================================================================

    /// Build `@Eq.{level} T a b` at an explicit universe level.
    pub(crate) fn eq_at(&self, level: Level, ty: Expr, a: Expr, b: Expr) -> Expr {
        let eq_const = self.const_ref_levels("Eq", vec![level]);
        Expr::apps(eq_const, [ty, a, b])
    }

    /// Build `@Eq.refl.{level} T a` at an explicit universe level.
    pub(crate) fn eq_refl_at(&self, level: Level, ty: Expr, a: Expr) -> Expr {
        let refl = self.const_ref_levels("Eq.refl", vec![level]);
        Expr::apps(refl, [ty, a])
    }

    /// Build `@Eq.symm.{level} T a b h` at an explicit universe level.
    pub(crate) fn eq_symm_at(&self, level: Level, ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let symm = self.const_ref_levels("Eq.symm", vec![level]);
        Expr::apps(symm, [ty, a, b, h])
    }

    /// Build `@Eq.trans.{level} T a b c hab hbc` at an explicit universe level.
    pub(crate) fn eq_trans_at(
        &self,
        level: Level,
        ty: Expr,
        a: Expr,
        b: Expr,
        c: Expr,
        hab: Expr,
        hbc: Expr,
    ) -> Expr {
        let trans = self.const_ref_levels("Eq.trans", vec![level]);
        Expr::apps(trans, [ty, a, b, c, hab, hbc])
    }

    // =========================================================================
    // Equality (Nat-specialized, level = 1)
    // =========================================================================

    /// Build `@Eq.{1} Nat a b`.
    pub(crate) fn eq_nat(&self, a: Expr, b: Expr) -> Expr {
        self.eq_at(level_one(), self.nat(), a, b)
    }

    /// Build `@Eq.refl.{1} Nat a`.
    pub(crate) fn eq_refl_nat(&self, a: Expr) -> Expr {
        self.eq_refl_at(level_one(), self.nat(), a)
    }

    /// Build `@Eq.symm.{1} Nat a b h`.
    pub(crate) fn eq_symm_nat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.eq_symm_at(level_one(), self.nat(), a, b, h)
    }

    /// Build `@Eq.trans.{1} Nat a b c hab hbc`.
    pub(crate) fn eq_trans_nat(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        self.eq_trans_at(level_one(), self.nat(), a, b, c, hab, hbc)
    }

    // =========================================================================
    // And (conjunction)
    // =========================================================================

    /// Build `@And a b`.
    pub(crate) fn and(&self, a: Expr, b: Expr) -> Expr {
        let and_const = self.const_ref("And");
        Expr::apps(and_const, [a, b])
    }

    /// Build `@And.intro a b ha hb`.
    pub(crate) fn and_intro(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        let intro = self.const_ref("And.intro");
        Expr::apps(intro, [a, b, ha, hb])
    }

    // =========================================================================
    // Nat recursion
    // =========================================================================

    /// Build `@Nat.rec.{1} motive base step n` -- Type-valued Nat recursion.
    pub(crate) fn nat_rec(&self, motive: Expr, base: Expr, step: Expr, n: Expr) -> Expr {
        let nat_rec = self.const_ref_levels("Nat.rec", vec![level_one()]);
        Expr::apps(nat_rec, [motive, base, step, n])
    }

    // =========================================================================
    // Registration
    // =========================================================================

    /// Register a monomorphic theorem via `add_decl` (kernel-verified).
    pub(crate) fn register_theorem(
        &self,
        env: &mut Environment,
        name: &str,
        ty: Expr,
        proof: Expr,
    ) -> Result<(), EnvError> {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }

    /// Register a universe-polymorphic theorem with level parameter `u`.
    pub(crate) fn register_theorem_poly(
        &self,
        env: &mut Environment,
        name: &str,
        ty: Expr,
        proof: Expr,
    ) -> Result<(), EnvError> {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![self.u.clone()],
            type_: ty,
            value: proof,
        })
    }

    /// Register a definition via `add_decl` (kernel-verified).
    pub(crate) fn register_definition(
        &self,
        env: &mut Environment,
        name: &str,
        ty: Expr,
        value: Expr,
    ) -> Result<(), EnvError> {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
