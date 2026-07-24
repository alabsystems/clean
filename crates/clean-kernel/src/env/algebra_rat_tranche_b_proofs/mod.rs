// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of Rat field-instance "Tranche B" identities (#3581).
//!
//! Tranche B is the set of single-variable Rat identities that collapse
//! under delta/iota reduction on the reducible `Rat.*` definitions plus
//! a small number of foundational `Int.*` / `Nat.*` lemmas. The tranche
//! was isolated by `reports/audit/2026-04-20-rat-field-axiom-triage.md`.
//!
//! # Status
//!
//! | Axiom           | Status              | Proof mechanism                         |
//! |-----------------|---------------------|-----------------------------------------|
//! | `Rat.inv_zero`  | **Proved**          | Pure `Eq.refl` — delta/iota collapse.   |
//! | `Rat.zero_add`  | **Proved**          | `Int.zero_mul` + `Int.zero_add` + `Int.mul_one` + `Nat.one_mul` chained via `Eq.trans` and `congrArg` into `Rat.mk`; kernel finishes the delta on `Rat.add` + structure-eta on `Rat`. |
//! | `Rat.add_zero`  | **Proved**          | Symmetric to `zero_add`; uses `Int.mul_zero` + `Int.add_zero` + `Int.mul_one` + `Nat.mul_one`. |
//! | `Rat.one_mul`   | **Proved**          | `Int.one_mul` + `Nat.one_mul` + two `congrArg`s + `Eq.trans`. |
//! | `Rat.mul_one`   | **Proved**          | `Int.mul_one` + `Nat.mul_one` + two `congrArg`s + `Eq.trans`. |
//! | `Rat.zero_mul`  | **Not tractable under current `Rat` carrier** | LHS denom reduces to `Nat.mul 1 denom_a`, RHS (`Rat.zero`) denom is `Nat.succ Nat.zero`; both type-check but `Rat.mk` is a constructor (no quotient). Same equivalence-class obstruction the triage report flags for `Rat.add_left_neg`. Deferred. |
//! | `Rat.mul_zero`  | **Not tractable under current `Rat` carrier** | Symmetric to `zero_mul`. Deferred. |
//!
//! # Proof sketch
//!
//! The four `{zero,add}_{add,zero} / {one,mul}_{mul,one}` identities all
//! have the same shape: after `Rat.add` / `Rat.mul` delta-reduces, the goal
//! becomes
//!
//! ```text
//! Rat.mk LHS_num LHS_den = Rat.mk (Rat.num a) (Rat.denom a)
//! ```
//!
//! where `LHS_num` / `LHS_den` are `Int` / `Nat` expressions that reduce
//! to `Rat.num a` / `Rat.denom a` via foundational `Int.*` / `Nat.*`
//! equalities. The RHS is further def-equal to `a` itself via
//! structure-eta on `Rat` (1 constructor, 0 indices, non-recursive — see
//! `crate::tc::eta::is_structure_like`).
//!
//! The proof term is therefore:
//!
//! 1. Build `h_num : LHS_num = Rat.num a` by `Eq.trans`-chaining the
//!    component-level `Int.*` equalities (`Int.zero_mul`, `Int.zero_add`,
//!    `Int.mul_one`, etc.) under `congrArg` motives.
//! 2. Build `h_den : LHS_den = Rat.denom a` similarly with `Nat.*`.
//! 3. `step1 = congrArg (fun n => Rat.mk n LHS_den) h_num`.
//! 4. `step2 = congrArg (fun d => Rat.mk (Rat.num a) d) h_den`.
//! 5. `Eq.trans step1 step2 : Rat.mk LHS_num LHS_den = Rat.mk (Rat.num a) (Rat.denom a) ≡ a`.
//!
//! The kernel's definitional equality handles both endpoints (delta on
//! `Rat.add`/`Rat.mul` and structure-eta on `a ≡ Rat.mk (Rat.num a) (Rat.denom a)`).
//!
//! # Axiom closure
//!
//! Each proof depends only on:
//!
//! - `Int.zero_mul`, `Int.zero_add`, `Int.mul_one`, `Int.mul_zero`,
//!   `Int.add_zero`, `Int.one_mul` — Int primitives (foundational at
//!   the Rat layer).
//! - `Nat.one_mul`, `Nat.mul_one` — Nat primitives (foundational).
//! - `Eq.trans`, `Eq.refl`, `congrArg` — kernel-level `Declaration::Theorem`s.
//! - `Rat.mk`, `Rat.num`, `Rat.denom` — constructor / reducible projections.
//!
//! Classifies as `ProofQuality::AxiomDependent` with
//! `{Int.zero_mul, Int.zero_add, Int.mul_one, Nat.one_mul}` (and similar)
//! in the transitive closure.  None of these are `Rat.*` self-references
//! — the axiom-wrapper masquerade (#3559) is avoided.
//!
//! Tracks #3581. Sibling proofs: `algebra_rat_mul_comm_proof.rs` (#3572
//! Phase 1) and `order_nat_le_trans_proof.rs` (#3552).
//!
//! # Module layout
//!
//! - `mod.rs` (this file): shared helpers (`TrancheBSymbols`,
//!   `mk_congr_arg`, `mk_eq_trans`, `build_unary_rat_eq_type`,
//!   `build_rat_mk_num_motive`, `build_rat_mk_den_motive`,
//!   `combine_num_den`) and `Environment::register_rat_inv_zero_proof`
//!   (pure `Eq.refl`).
//! - `add_mul.rs`: the four more elaborate proofs that share the
//!   numerator-chain / denominator-chain skeleton
//!   (`register_rat_{zero_add, add_zero, one_mul, mul_one}_proof`).
//!   Split out to satisfy the 500-line per-file budget (#3581).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

pub(super) mod add_mul;

#[cfg(test)]
mod tests;

/// Reusable expression handles threaded through the Tranche B proof
/// helpers.  Built once per `register_*_proof` entry point.
pub(super) struct TrancheBSymbols {
    pub(super) rat_type: Expr,
    pub(super) int_type: Expr,
    pub(super) nat_type: Expr,
    pub(super) rat_mk: Expr,
    pub(super) rat_num: Expr,
    pub(super) rat_denom: Expr,
    pub(super) int_zero: Expr,
    /// `Int.ofNat (Nat.succ Nat.zero)` — the canonical `int_one` literal
    /// matching the shape `Int.mul_one` / `Int.one_mul` expect.
    pub(super) int_one_lit: Expr,
    pub(super) int_add: Expr,
    pub(super) int_mul: Expr,
    pub(super) int_of_nat: Expr,
    /// `Nat.succ Nat.zero` — matches the `nat_one` shape `Nat.one_mul`
    /// and `Nat.mul_one` expect, and the `Rat.denom Rat.zero` / `Rat.denom Rat.one`
    /// iota-reduced form.
    pub(super) nat_one_lit: Expr,
    pub(super) nat_mul: Expr,
    pub(super) int_zero_add: Expr,
    pub(super) int_add_zero: Expr,
    pub(super) int_zero_mul: Expr,
    #[allow(dead_code)]
    pub(super) int_mul_zero: Expr,
    pub(super) int_one_mul: Expr,
    pub(super) int_mul_one: Expr,
    pub(super) nat_one_mul: Expr,
    pub(super) nat_mul_one: Expr,
    /// `Eq.{1}` at `Sort (succ zero)` (Rat/Int/Nat all live at Type 0).
    pub(super) eq_rat: Expr,
    #[allow(dead_code)]
    pub(super) eq_int: Expr,
    #[allow(dead_code)]
    pub(super) eq_nat: Expr,
    /// `Eq.trans.{1}` at the appropriate universe.
    pub(super) eq_trans: Expr,
    /// `congrArg.{1,1}`.
    pub(super) congr_arg: Expr,
}

impl TrancheBSymbols {
    pub(super) fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one_lit = Expr::app(nat_succ, nat_zero);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_one_lit = Expr::app(int_of_nat.clone(), nat_one_lit.clone());

        Self {
            rat_type: Expr::const_(Name::from_string("Rat"), vec![]),
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_num: Expr::const_(Name::from_string("Rat.num"), vec![]),
            rat_denom: Expr::const_(Name::from_string("Rat.denom"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_one_lit,
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat,
            nat_one_lit,
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            int_zero_add: Expr::const_(Name::from_string("Int.zero_add"), vec![]),
            int_add_zero: Expr::const_(Name::from_string("Int.add_zero"), vec![]),
            int_zero_mul: Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
            int_mul_zero: Expr::const_(Name::from_string("Int.mul_zero"), vec![]),
            int_one_mul: Expr::const_(Name::from_string("Int.one_mul"), vec![]),
            int_mul_one: Expr::const_(Name::from_string("Int.mul_one"), vec![]),
            nat_one_mul: Expr::const_(Name::from_string("Nat.one_mul"), vec![]),
            nat_mul_one: Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_int: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }
}

/// Build a `congrArg` specialized at `(α, β)` where both live at
/// `Sort (succ zero)` (Int/Nat/Rat).  All three required uses fit.
pub(super) fn mk_congr_arg(
    sym: &TrancheBSymbols,
    dom_ty: &Expr,
    cod_ty: &Expr,
    lhs: Expr,
    rhs: Expr,
    motive: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(
        sym.congr_arg.clone(),
        [dom_ty.clone(), cod_ty.clone(), lhs, rhs, motive, h],
    )
}

/// Build an `Eq.trans` specialized at `α = Sort (succ zero)` (Rat etc.).
/// The caller supplies the shared type `alpha` (Rat, Int, or Nat).
pub(super) fn mk_eq_trans(
    sym: &TrancheBSymbols,
    alpha: &Expr,
    a: Expr,
    b: Expr,
    c: Expr,
    hab: Expr,
    hbc: Expr,
) -> Expr {
    Expr::apps(sym.eq_trans.clone(), [alpha.clone(), a, b, c, hab, hbc])
}

/// Build the theorem type `∀ a : Rat, Eq Rat LHS RHS` where `build_lhs`
/// and `build_rhs` receive the outer Rat local and produce the two sides
/// of the equality.
pub(super) fn build_unary_rat_eq_type(
    sym: &TrancheBSymbols,
    build_lhs: impl FnOnce(&Expr) -> Expr,
    build_rhs: impl FnOnce(&Expr) -> Expr,
) -> (Expr, EnvDeclBuilder, FVarId, Expr) {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(sym.rat_type.clone());
    let lhs = build_lhs(&a);
    let rhs = build_rhs(&a);
    let concl = Expr::apps(sym.eq_rat.clone(), [sym.rat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, sym.rat_type.clone(), concl);
    let type_ = b.finish(ty_raw);
    (type_, b, a_id, a)
}

/// Build the `Rat.mk n LHS_den` motive `fun n : Int => Rat.mk n den`.
pub(super) fn build_rat_mk_num_motive(
    sym: &TrancheBSymbols,
    b: &EnvDeclBuilder,
    den: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (x_id, x) = fb.fresh_local(sym.int_type.clone());
    let body = Expr::app(Expr::app(sym.rat_mk.clone(), x), den.clone());
    let lam = fb.mk_lam(x_id, BinderInfo::Default, sym.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the `Rat.mk num d` motive `fun d : Nat => Rat.mk num d`.
pub(super) fn build_rat_mk_den_motive(
    sym: &TrancheBSymbols,
    b: &EnvDeclBuilder,
    num: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (y_id, y) = fb.fresh_local(sym.nat_type.clone());
    let body = Expr::app(Expr::app(sym.rat_mk.clone(), num.clone()), y);
    let lam = fb.mk_lam(y_id, BinderInfo::Default, sym.nat_type.clone(), body);
    fb.finish_child(lam)
}

/// Assemble the final `Rat`-level proof body from a numerator-equality
/// and denominator-equality, plus the explicit endpoint `Rat.mk` terms.
///
/// Returns a proof of `Rat.mk lhs_num lhs_den = Rat.mk rhs_num rhs_den`.
pub(super) fn combine_num_den(
    sym: &TrancheBSymbols,
    b: &EnvDeclBuilder,
    lhs_num: Expr,
    rhs_num: Expr,
    lhs_den: Expr,
    rhs_den: Expr,
    h_num: Expr,
    h_den: Expr,
) -> Expr {
    // step1 : Rat.mk lhs_num lhs_den = Rat.mk rhs_num lhs_den
    let motive_num = build_rat_mk_num_motive(sym, b, &lhs_den);
    let step1 = mk_congr_arg(
        sym,
        &sym.int_type,
        &sym.rat_type,
        lhs_num.clone(),
        rhs_num.clone(),
        motive_num,
        h_num,
    );

    // step2 : Rat.mk rhs_num lhs_den = Rat.mk rhs_num rhs_den
    let motive_den = build_rat_mk_den_motive(sym, b, &rhs_num);
    let step2 = mk_congr_arg(
        sym,
        &sym.nat_type,
        &sym.rat_type,
        lhs_den.clone(),
        rhs_den.clone(),
        motive_den,
        h_den,
    );

    let rat_mk_lhs = Expr::app(Expr::app(sym.rat_mk.clone(), lhs_num), lhs_den.clone());
    let rat_mk_mid = Expr::app(Expr::app(sym.rat_mk.clone(), rhs_num.clone()), lhs_den);
    let rat_mk_rhs = Expr::app(Expr::app(sym.rat_mk.clone(), rhs_num), rhs_den);

    mk_eq_trans(
        sym,
        &sym.rat_type,
        rat_mk_lhs,
        rat_mk_mid,
        rat_mk_rhs,
        step1,
        step2,
    )
}

impl Environment {
    /// Register `Rat.inv_zero : Rat.inv Rat.zero = Rat.zero` as a
    /// kernel-checked `Declaration::Theorem`.
    ///
    /// # Proof
    ///
    /// `Rat.inv Rat.zero` reduces to `Rat.zero` by pure delta/iota on the
    /// reducible `Rat.inv` definition. The proof term is therefore
    /// `@Eq.refl.{1} Rat Rat.zero`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_rat()` has registered `Rat`, `Rat.mk`,
    ///           `Rat.num`, `Rat.denom`, `Rat.zero`.
    /// REQUIRES: `self.init_rat_arith()` has registered the reducible
    ///           `Rat.inv` definition.
    /// REQUIRES: `self.init_eq()` has registered `Eq` and `Eq.refl`.
    /// ENSURES: On success, `Rat.inv_zero` is a `Declaration::Theorem`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_rat_inv_zero_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_eq()?;

        let type1 = Level::succ(Level::zero());
        let rat_type = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_inv = Expr::const_(Name::from_string("Rat.inv"), vec![]);

        let lhs = Expr::app(rat_inv, rat_zero.clone());
        let type_ = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            [rat_type.clone(), lhs, rat_zero.clone()],
        );

        let value = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
            [rat_type, rat_zero],
        );

        // SOUNDNESS: Real kernel-checked proof term (#3581). `Eq.refl` on
        // `Rat.zero` is accepted only if the kernel's definitional equality
        // reduces `Rat.inv Rat.zero` to `Rat.zero`. All three reductions
        // (delta on `Rat.inv`, iota on `Int.rec` and `Nat.rec`) are purely
        // computational. No `sorry`, no axiom wrapping.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}
