// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Rat.add_assoc` from Int/Nat ring axioms.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Rat.add_assoc`
//! (see `algebra_field_inst.rs::init_rat_field_inst`) with a
//! `Declaration::Theorem` whose body is a genuine kernel-checked proof term
//! built from `Int.right_distrib`, `Int.mul_assoc`, `Int.mul_comm`,
//! `Int.add_assoc`, `Int.ofNat_mul`, and `Nat.mul_assoc`, chained via
//! `congrArg` + `Eq.trans` into `Rat.mk`.
//!
//! # Proof sketch (Phase 3 of #3572)
//!
//! Let `nX := Rat.num X`, `dX := Rat.denom X`, `pX := Int.ofNat dX`
//! for `X ∈ {a, b, c}`. `Rat.add` is reducible:
//!
//! ```text
//! Rat.add a b := Rat.mk (nA·pB + nB·pA) (dA * dB)
//! ```
//!
//! After delta on the nested `Rat.add`s and iota on `Rat.num` / `Rat.denom`:
//!
//! ```text
//! LHS = Rat.mk ((nA·pB + nB·pA)·pC + nC·Int.ofNat(dA·dB)) ((dA·dB)·dC)
//! RHS = Rat.mk (nA·Int.ofNat(dB·dC) + (nB·pC + nC·pB)·pA) (dA·(dB·dC))
//! ```
//!
//! **Denominator equality** `h_den : (dA·dB)·dC = dA·(dB·dC)` is just
//! `Nat.mul_assoc dA dB dC`.
//!
//! **Numerator equality** `h_num` is built by chaining 8 Int-arithmetic
//! equalities (Int.right_distrib, Int.ofNat_mul, Int.mul_assoc×3,
//! Int.mul_comm×2, Int.add_assoc, Int.right_distrib⁻¹, Int.ofNat_mul⁻¹)
//! with `Eq.trans` + `congrArg`. See `h_num.rs` for the stage-by-stage
//! implementation.
//!
//! # Axiom closure
//!
//! The proof term references:
//!
//! - `Int.right_distrib`, `Int.mul_assoc`, `Int.mul_comm`, `Int.add_assoc`,
//!   `Int.ofNat_mul` — `Declaration::Axiom` in `data_types_int_lemmas.rs`
//!   (primitives at the Int layer, foundational at the Rat layer).
//! - `Nat.mul_assoc` — `Declaration::Axiom` in `data_types_nat_lemmas.rs`
//!   (primitive at the Nat layer, foundational at the Rat layer).
//! - `Eq.trans`, `Eq.symm`, `congrArg` — `Declaration::Theorem` in
//!   `core_eq/*` (kernel-checked).
//! - `Rat.mk`, `Rat.num`, `Rat.denom`, `Rat.add`, `Int.add`, `Int.mul`,
//!   `Int.ofNat`, `Nat.mul` — constructor / reducible Definitions.
//!
//! The transitive axiom closure of `Rat.add_assoc` therefore reduces to
//! `{Int.right_distrib, Int.mul_assoc, Int.mul_comm, Int.add_assoc,
//! Int.ofNat_mul, Nat.mul_assoc}`. None are Rat-domain assumptions; all
//! are Int/Nat primitives.
//!
//! Tracks issue #3572 (Phase 3). See `algebra_rat_add_comm_proof.rs`
//! (#3572 Phase 2) for the sibling `Rat.add_comm` proof whose pattern
//! this extends; `Rat.add_assoc` differs in needing Int ring-normalization
//! across three denominators (rather than a single commute).
//!
//! # Module layout
//!
//! - `mod.rs` (this file): docs, public `Environment::register_rat_add_assoc_proof`,
//!   type builder, `Rat.mk`-level assembly helper, and an inline idempotency
//!   test.
//! - `mod_helpers.rs`: shared `AddAssocSymbols`, `Terms`, Int/Nat shortcuts,
//!   motive builders, `eq_symm_of`, `int_congr`, `int_trans`.
//! - `h_num.rs`: `build_h_num` — the 8-step Int-ring normalization split
//!   into four ≤80-line stage helpers.

#![allow(non_snake_case)]

mod h_num;
mod mod_helpers;

use super::algebra_rat_tranche_b_proofs::{build_rat_mk_den_motive, mk_congr_arg, mk_eq_trans};
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::name::Name;

use self::h_num::{build_h_num, HNumResult};
use self::mod_helpers::{extract_terms, n_mul, AddAssocSymbols, Terms};

/// Binder/type bundle returned from `build_rat_add_assoc_type`.
struct AddAssocBinders {
    type_: Expr,
    builder: EnvDeclBuilder,
    a_id: FVarId,
    a: Expr,
    b_id: FVarId,
    b: Expr,
    c_id: FVarId,
    c: Expr,
}

/// Build the theorem type
/// `∀ a b c : Rat, Eq Rat (Rat.add (Rat.add a b) c) (Rat.add a (Rat.add b c))`.
fn build_rat_add_assoc_type(sym: &AddAssocSymbols) -> AddAssocBinders {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(sym.tb.rat_type.clone());
    let (b_id, bv) = b.fresh_local(sym.tb.rat_type.clone());
    let (c_id, c) = b.fresh_local(sym.tb.rat_type.clone());

    let ab = Expr::app(Expr::app(sym.rat_add.clone(), a.clone()), bv.clone());
    let lhs = Expr::app(Expr::app(sym.rat_add.clone(), ab), c.clone());

    let bc = Expr::app(Expr::app(sym.rat_add.clone(), bv.clone()), c.clone());
    let rhs = Expr::app(Expr::app(sym.rat_add.clone(), a.clone()), bc);

    let concl = Expr::apps(sym.tb.eq_rat.clone(), [sym.tb.rat_type.clone(), lhs, rhs]);
    let ty = b.mk_pi(c_id, BinderInfo::Default, sym.tb.rat_type.clone(), concl);
    let ty = b.mk_pi(b_id, BinderInfo::Default, sym.tb.rat_type.clone(), ty);
    let ty = b.mk_pi(a_id, BinderInfo::Default, sym.tb.rat_type.clone(), ty);
    let type_ = b.finish(ty);
    AddAssocBinders {
        type_,
        builder: b,
        a_id,
        a,
        b_id,
        b: bv,
        c_id,
        c,
    }
}

/// Lift the Int-numerator and Nat-denominator equalities into a single
/// `Rat.mk`-level equality via two `congrArg` applications joined by
/// `Eq.trans`. Mirrors the `combine_num_den` pattern used by Tranche B
/// but inlined here so we can reuse the explicit endpoint expressions.
fn assemble_rat_mk_equality(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    h_num: Expr,
    h_den: Expr,
    lhs_num: &Expr,
    rhs_num: &Expr,
    lhs_den: &Expr,
    rhs_den: &Expr,
) -> Expr {
    let motive_num = {
        let mut fb = EnvDeclBuilder::child_of(b);
        let (x_id, x) = fb.fresh_local(sym.tb.int_type.clone());
        let body = Expr::app(Expr::app(sym.tb.rat_mk.clone(), x), lhs_den.clone());
        let lam = fb.mk_lam(x_id, BinderInfo::Default, sym.tb.int_type.clone(), body);
        fb.finish_child(lam)
    };
    let step1 = mk_congr_arg(
        &sym.tb,
        &sym.tb.int_type,
        &sym.tb.rat_type,
        lhs_num.clone(),
        rhs_num.clone(),
        motive_num,
        h_num,
    );

    let motive_den = build_rat_mk_den_motive(&sym.tb, b, rhs_num);
    let step2 = mk_congr_arg(
        &sym.tb,
        &sym.tb.nat_type,
        &sym.tb.rat_type,
        lhs_den.clone(),
        rhs_den.clone(),
        motive_den,
        h_den,
    );

    let rat_mk_lhs = Expr::app(
        Expr::app(sym.tb.rat_mk.clone(), lhs_num.clone()),
        lhs_den.clone(),
    );
    let rat_mk_mid = Expr::app(
        Expr::app(sym.tb.rat_mk.clone(), rhs_num.clone()),
        lhs_den.clone(),
    );
    let rat_mk_rhs = Expr::app(
        Expr::app(sym.tb.rat_mk.clone(), rhs_num.clone()),
        rhs_den.clone(),
    );

    mk_eq_trans(
        &sym.tb,
        &sym.tb.rat_type,
        rat_mk_lhs,
        rat_mk_mid,
        rat_mk_rhs,
        step1,
        step2,
    )
}

/// Compute the LHS/RHS denominator expressions ((dA·dB)·dC and dA·(dB·dC)).
fn build_denom_endpoints(sym: &AddAssocSymbols, t: &Terms) -> (Expr, Expr) {
    let lhs_den = n_mul(sym, n_mul(sym, t.d_a.clone(), t.d_b.clone()), t.d_c.clone());
    let rhs_den = n_mul(sym, t.d_a.clone(), n_mul(sym, t.d_b.clone(), t.d_c.clone()));
    (lhs_den, rhs_den)
}

/// Close the three outer `∀ a b c : Rat` lambdas around `body`.
fn close_three_binders(
    sym: &AddAssocSymbols,
    b: &mut EnvDeclBuilder,
    a_id: FVarId,
    b_id: FVarId,
    c_id: FVarId,
    body: Expr,
) -> Expr {
    let v = b.mk_lam(c_id, BinderInfo::Default, sym.tb.rat_type.clone(), body);
    let v = b.mk_lam(b_id, BinderInfo::Default, sym.tb.rat_type.clone(), v);
    let v = b.mk_lam(a_id, BinderInfo::Default, sym.tb.rat_type.clone(), v);
    b.finish(v)
}

impl Environment {
    /// Register `Rat.add_assoc` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body chains ring-normalization equalities at the Int layer
    /// (`Int.right_distrib`, `Int.mul_assoc`, `Int.mul_comm`, `Int.add_assoc`,
    /// `Int.ofNat_mul`) with `Nat.mul_assoc` at the Nat layer, combined via
    /// `congrArg` + `Eq.trans` into a `Rat.mk`-level equality.  The kernel
    /// closes both endpoints via delta on `Rat.add` + iota on `Rat.num` /
    /// `Rat.denom`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_rat_arith()` has registered `Rat.add`,
    ///           `Rat.num`, `Rat.denom`, `Rat.mk`.
    /// REQUIRES: `self.init_int_arith_lemmas()` has registered
    ///           `Int.add_assoc`, `Int.mul_assoc`, `Int.mul_comm`,
    ///           `Int.right_distrib`, `Int.add`, `Int.mul`, `Int.ofNat`.
    /// REQUIRES: `self.init_int_nat_conv_lemmas()` has registered
    ///           `Int.ofNat_mul`.
    /// REQUIRES: `self.init_nat_arith_lemmas()` has registered
    ///           `Nat.mul_assoc`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`,
    ///           `Eq.symm`, `congrArg`.
    /// ENSURES: On success, `Rat.add_assoc` is a `Declaration::Theorem`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_rat_add_assoc_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_int_nat_conv_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = AddAssocSymbols::new();
        let mut binders = build_rat_add_assoc_type(&sym);
        let t = extract_terms(&sym, &binders.a, &binders.b, &binders.c);

        let HNumResult {
            proof: h_num,
            lhs_num,
            rhs_num,
        } = build_h_num(&sym, &binders.builder, &t);
        let h_den = Expr::apps(
            sym.nat_mul_assoc.clone(),
            [t.d_a.clone(), t.d_b.clone(), t.d_c.clone()],
        );
        let (lhs_den, rhs_den) = build_denom_endpoints(&sym, &t);

        let body = assemble_rat_mk_equality(
            &sym,
            &binders.builder,
            h_num,
            h_den,
            &lhs_num,
            &rhs_num,
            &lhs_den,
            &rhs_den,
        );

        let value = close_three_binders(
            &sym,
            &mut binders.builder,
            binders.a_id,
            binders.b_id,
            binders.c_id,
            body,
        );

        // SOUNDNESS: Real kernel-checked proof term (#3572 Phase 3).
        // Int-ring normalization via `Int.right_distrib`, `Int.mul_assoc`,
        // `Int.mul_comm`, `Int.add_assoc`, `Int.ofNat_mul` + `Nat.mul_assoc`
        // combined via `congrArg` + `Eq.trans` into `Rat.mk`-equality.
        // Kernel closes both endpoints via delta on `Rat.add` + iota on
        // `Rat.num` / `Rat.denom`. No `sorry`, no self-reference.
        // Replaces the prior `Declaration::Axiom`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: binders.type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;

    /// Minimal sanity test kept inline next to the helpers. The broader
    /// guard-test suite (theorem-kind pin, proof-body-is-not-axiom-ref,
    /// transitive closure, and FOUNDATIONAL_AXIOMS removal) lives in
    /// `tests_algebra_rat_add_assoc.rs` per the Phase 2/3 test-file split.
    #[test]
    fn test_rat_add_assoc_idempotent() {
        let mut env = Environment::new();
        env.init_rat_field_inst().expect("first init");
        env.init_rat_field_inst().expect("second init (idempotent)");
        env.register_rat_add_assoc_proof()
            .expect("direct re-registration (idempotent)");
        let info = env
            .get_const(&Name::from_string("Rat.add_assoc"))
            .expect("Rat.add_assoc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
