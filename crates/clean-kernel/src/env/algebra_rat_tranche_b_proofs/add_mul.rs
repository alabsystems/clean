// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tranche B add/mul proofs for `Rat.{zero_add, add_zero, one_mul, mul_one}`.
//!
//! Split out of `mod.rs` for the 500-line per-file budget (#3581). Shares
//! helpers with the parent module via `super::*`. The numerator-chain
//! helpers (`build_zero_add_num_chain`, `build_add_zero_num_chain`) are
//! local to this file since no other tranche uses them.

use super::*;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build a proof of `Int.add x y = target` for the `zero_add` pattern.
///
/// Inputs:
/// - `zero_times_den`  : `Int.mul Int.zero (Int.ofNat denom_a)` (x).
/// - `numa_times_one`  : `Int.mul num_a int_one`                (y).
/// - `num_a`           : `Rat.num a`                            (target).
///
/// Returns `h_num : Int.add zero_times_den numa_times_one = num_a`
/// built from `Int.zero_mul + Int.zero_add + Int.mul_one` and two `Eq.trans`
/// through a single `congrArg (fun x => Int.add x numa_times_one)`.
#[cfg(any(test, feature = "math-overlays"))]
fn build_zero_add_num_chain(
    sym: &TrancheBSymbols,
    b: &EnvDeclBuilder,
    denom_a: &Expr,
    num_a: &Expr,
    zero_times_den: Expr,
    numa_times_one: Expr,
) -> Expr {
    // h1 : Int.mul Int.zero (Int.ofNat (Rat.denom a)) = Int.zero
    let h1 = Expr::app(
        sym.int_zero_mul.clone(),
        Expr::app(sym.int_of_nat.clone(), denom_a.clone()),
    );
    // motive_add = fun x : Int => Int.add x numa_times_one
    let motive_add_num = {
        let mut fb = EnvDeclBuilder::child_of(b);
        let (x_id, x) = fb.fresh_local(sym.int_type.clone());
        let body = Expr::app(Expr::app(sym.int_add.clone(), x), numa_times_one.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, sym.int_type.clone(), body);
        fb.finish_child(lam)
    };
    // step_num_a : Int.add zero_times_den y = Int.add Int.zero y
    let step_num_a = mk_congr_arg(
        sym,
        &sym.int_type,
        &sym.int_type,
        zero_times_den.clone(),
        sym.int_zero.clone(),
        motive_add_num,
        h1,
    );
    // h2 : Int.add Int.zero y = y
    let h2 = Expr::app(sym.int_zero_add.clone(), numa_times_one.clone());
    // h3 : Int.mul num_a int_one = num_a
    let h3 = Expr::app(sym.int_mul_one.clone(), num_a.clone());

    let lhs_num = Expr::app(
        Expr::app(sym.int_add.clone(), zero_times_den),
        numa_times_one.clone(),
    );
    let int_add_zero_numa_one = Expr::app(
        Expr::app(sym.int_add.clone(), sym.int_zero.clone()),
        numa_times_one.clone(),
    );
    let tr_ab = mk_eq_trans(
        sym,
        &sym.int_type,
        lhs_num.clone(),
        int_add_zero_numa_one,
        numa_times_one.clone(),
        step_num_a,
        h2,
    );
    mk_eq_trans(
        sym,
        &sym.int_type,
        lhs_num,
        numa_times_one,
        num_a.clone(),
        tr_ab,
        h3,
    )
}

/// Build a proof of `Int.add x y = target` for the `add_zero` pattern.
///
/// Inputs:
/// - `numa_times_one`  : `Int.mul num_a int_one`                (x).
/// - `zero_times_den`  : `Int.mul Int.zero (Int.ofNat denom_a)` (y).
/// - `num_a`           : `Rat.num a`                            (target).
///
/// Returns `h_num : Int.add numa_times_one zero_times_den = num_a` built
/// from `Int.mul_one + Int.zero_mul + Int.add_zero` and two `Eq.trans`
/// through two `congrArg`s (one on each side of `Int.add`).
#[cfg(any(test, feature = "math-overlays"))]
fn build_add_zero_num_chain(
    sym: &TrancheBSymbols,
    b: &EnvDeclBuilder,
    denom_a: &Expr,
    num_a: &Expr,
    numa_times_one: Expr,
    zero_times_den: Expr,
) -> Expr {
    // h1 : Int.mul num_a int_one = num_a
    let h1 = Expr::app(sym.int_mul_one.clone(), num_a.clone());
    // motive_left = fun x : Int => Int.add x zero_times_den
    let motive_left = {
        let mut fb = EnvDeclBuilder::child_of(b);
        let (x_id, x) = fb.fresh_local(sym.int_type.clone());
        let body = Expr::app(Expr::app(sym.int_add.clone(), x), zero_times_den.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, sym.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step_a = mk_congr_arg(
        sym,
        &sym.int_type,
        &sym.int_type,
        numa_times_one.clone(),
        num_a.clone(),
        motive_left,
        h1,
    );
    // h2 : Int.mul Int.zero (Int.ofNat denom_a) = Int.zero
    let h2 = Expr::app(
        sym.int_zero_mul.clone(),
        Expr::app(sym.int_of_nat.clone(), denom_a.clone()),
    );
    // motive_right = fun y : Int => Int.add num_a y
    let motive_right = {
        let mut fb = EnvDeclBuilder::child_of(b);
        let (y_id, y) = fb.fresh_local(sym.int_type.clone());
        let body = Expr::app(Expr::app(sym.int_add.clone(), num_a.clone()), y);
        let lam = fb.mk_lam(y_id, BinderInfo::Default, sym.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step_b = mk_congr_arg(
        sym,
        &sym.int_type,
        &sym.int_type,
        zero_times_den.clone(),
        sym.int_zero.clone(),
        motive_right,
        h2,
    );
    // h3 : Int.add num_a Int.zero = num_a
    let h3 = Expr::app(sym.int_add_zero.clone(), num_a.clone());

    let lhs_num = Expr::app(
        Expr::app(sym.int_add.clone(), numa_times_one),
        zero_times_den.clone(),
    );
    let mid1 = Expr::app(
        Expr::app(sym.int_add.clone(), num_a.clone()),
        zero_times_den,
    );
    let mid2 = Expr::app(
        Expr::app(sym.int_add.clone(), num_a.clone()),
        sym.int_zero.clone(),
    );
    let tr_ab = mk_eq_trans(
        sym,
        &sym.int_type,
        lhs_num.clone(),
        mid1,
        mid2.clone(),
        step_a,
        step_b,
    );
    mk_eq_trans(sym, &sym.int_type, lhs_num, mid2, num_a.clone(), tr_ab, h3)
}

impl Environment {
    /// Register `Rat.zero_add : ∀ a : Rat, Rat.add Rat.zero a = a` as a
    /// kernel-checked `Declaration::Theorem`.
    ///
    /// # Proof
    ///
    /// After `Rat.add` delta-reduces and `Rat.num Rat.zero` / `Rat.denom Rat.zero`
    /// iota-reduce:
    ///
    /// ```text
    /// LHS_num = Int.add (Int.mul Int.zero (Int.ofNat (Rat.denom a)))
    ///                   (Int.mul (Rat.num a) int_one)
    /// LHS_den = Nat.mul nat_one (Rat.denom a)
    /// ```
    ///
    /// Numerator chain via `build_zero_add_num_chain`; denominator chain
    /// is the single lemma `Nat.one_mul (Rat.denom a)`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn register_rat_zero_add_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = TrancheBSymbols::new();
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

        // Stated type: ∀ a : Rat, Rat.add Rat.zero a = a.
        let (type_, b, a_id, a) = build_unary_rat_eq_type(
            &sym,
            |a| Expr::app(Expr::app(rat_add.clone(), rat_zero.clone()), a.clone()),
            |a| a.clone(),
        );

        // Build proof body with `a` in scope.
        let num_a = Expr::app(sym.rat_num.clone(), a.clone());
        let denom_a = Expr::app(sym.rat_denom.clone(), a.clone());

        // Post-reduction LHS components.
        let zero_times_den = Expr::app(
            Expr::app(sym.int_mul.clone(), sym.int_zero.clone()),
            Expr::app(sym.int_of_nat.clone(), denom_a.clone()),
        );
        let numa_times_one = Expr::app(
            Expr::app(sym.int_mul.clone(), num_a.clone()),
            sym.int_one_lit.clone(),
        );
        let lhs_num = Expr::app(
            Expr::app(sym.int_add.clone(), zero_times_den.clone()),
            numa_times_one.clone(),
        );
        let lhs_den = Expr::app(
            Expr::app(sym.nat_mul.clone(), sym.nat_one_lit.clone()),
            denom_a.clone(),
        );

        let h_num =
            build_zero_add_num_chain(&sym, &b, &denom_a, &num_a, zero_times_den, numa_times_one);
        let h_den = Expr::app(sym.nat_one_mul.clone(), denom_a.clone());

        let body = combine_num_den(&sym, &b, lhs_num, num_a, lhs_den, denom_a, h_num, h_den);

        let value_raw = b.mk_lam(a_id, BinderInfo::Default, sym.rat_type.clone(), body);
        let value = b.finish(value_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3581). The kernel
        // accepts this only if:
        //   (a) `Rat.add Rat.zero a` delta+iota-reduces to the explicit
        //       `Rat.mk LHS_num LHS_den` form, and
        //   (b) `a` structure-eta-expands to `Rat.mk (Rat.num a) (Rat.denom a)`.
        // Both are standard kernel def-eq behaviour for reducible definitions
        // and 1-ctor non-recursive inductives. No `sorry`, no axiom wrapping.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `Rat.add_zero : ∀ a : Rat, Rat.add a Rat.zero = a`.
    /// Symmetric to `Rat.zero_add`; numerator chain via
    /// `build_add_zero_num_chain`; denominator is `Nat.mul_one (Rat.denom a)`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn register_rat_add_zero_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = TrancheBSymbols::new();
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

        let (type_, b, a_id, a) = build_unary_rat_eq_type(
            &sym,
            |a| Expr::app(Expr::app(rat_add.clone(), a.clone()), rat_zero.clone()),
            |a| a.clone(),
        );

        let num_a = Expr::app(sym.rat_num.clone(), a.clone());
        let denom_a = Expr::app(sym.rat_denom.clone(), a.clone());

        let numa_times_one = Expr::app(
            Expr::app(sym.int_mul.clone(), num_a.clone()),
            sym.int_one_lit.clone(),
        );
        let zero_times_den = Expr::app(
            Expr::app(sym.int_mul.clone(), sym.int_zero.clone()),
            Expr::app(sym.int_of_nat.clone(), denom_a.clone()),
        );
        let lhs_num = Expr::app(
            Expr::app(sym.int_add.clone(), numa_times_one.clone()),
            zero_times_den.clone(),
        );
        let lhs_den = Expr::app(
            Expr::app(sym.nat_mul.clone(), denom_a.clone()),
            sym.nat_one_lit.clone(),
        );

        let h_num =
            build_add_zero_num_chain(&sym, &b, &denom_a, &num_a, numa_times_one, zero_times_den);
        let h_den = Expr::app(sym.nat_mul_one.clone(), denom_a.clone());

        let body = combine_num_den(&sym, &b, lhs_num, num_a, lhs_den, denom_a, h_num, h_den);

        let value_raw = b.mk_lam(a_id, BinderInfo::Default, sym.rat_type.clone(), body);
        let value = b.finish(value_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3581). Same rationale
        // as `register_rat_zero_add_proof`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `Rat.one_mul : ∀ a : Rat, Rat.mul Rat.one a = a`.
    ///
    /// After `Rat.mul` delta-reduces (and `Rat.num Rat.one ≡ int_one`,
    /// `Rat.denom Rat.one ≡ nat_one`):
    ///
    /// ```text
    /// LHS_num = Int.mul int_one (Rat.num a)
    /// LHS_den = Nat.mul nat_one (Rat.denom a)
    /// ```
    ///
    /// Numerator: `Int.one_mul (Rat.num a)`. Denominator: `Nat.one_mul (Rat.denom a)`.
    #[cfg(test)]
    pub(crate) fn register_rat_one_mul_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.one_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = TrancheBSymbols::new();
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);

        let (type_, b, a_id, a) = build_unary_rat_eq_type(
            &sym,
            |a| Expr::app(Expr::app(rat_mul.clone(), rat_one.clone()), a.clone()),
            |a| a.clone(),
        );

        let num_a = Expr::app(sym.rat_num.clone(), a.clone());
        let denom_a = Expr::app(sym.rat_denom.clone(), a.clone());

        let lhs_num = Expr::app(
            Expr::app(sym.int_mul.clone(), sym.int_one_lit.clone()),
            num_a.clone(),
        );
        let lhs_den = Expr::app(
            Expr::app(sym.nat_mul.clone(), sym.nat_one_lit.clone()),
            denom_a.clone(),
        );

        let h_num = Expr::app(sym.int_one_mul.clone(), num_a.clone());
        let h_den = Expr::app(sym.nat_one_mul.clone(), denom_a.clone());

        let body = combine_num_den(&sym, &b, lhs_num, num_a, lhs_den, denom_a, h_num, h_den);

        let value_raw = b.mk_lam(a_id, BinderInfo::Default, sym.rat_type.clone(), body);
        let value = b.finish(value_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3581).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `Rat.mul_one : ∀ a : Rat, Rat.mul a Rat.one = a`.
    /// Symmetric to `Rat.one_mul`.
    #[cfg(test)]
    pub(crate) fn register_rat_mul_one_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = TrancheBSymbols::new();
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);

        let (type_, b, a_id, a) = build_unary_rat_eq_type(
            &sym,
            |a| Expr::app(Expr::app(rat_mul.clone(), a.clone()), rat_one.clone()),
            |a| a.clone(),
        );

        let num_a = Expr::app(sym.rat_num.clone(), a.clone());
        let denom_a = Expr::app(sym.rat_denom.clone(), a.clone());

        let lhs_num = Expr::app(
            Expr::app(sym.int_mul.clone(), num_a.clone()),
            sym.int_one_lit.clone(),
        );
        let lhs_den = Expr::app(
            Expr::app(sym.nat_mul.clone(), denom_a.clone()),
            sym.nat_one_lit.clone(),
        );

        let h_num = Expr::app(sym.int_mul_one.clone(), num_a.clone());
        let h_den = Expr::app(sym.nat_mul_one.clone(), denom_a.clone());

        let body = combine_num_den(&sym, &b, lhs_num, num_a, lhs_den, denom_a, h_num, h_den);

        let value_raw = b.mk_lam(a_id, BinderInfo::Default, sym.rat_type.clone(), body);
        let value = b.finish(value_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3581).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}
