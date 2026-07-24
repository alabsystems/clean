// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Rat.add_comm` from `Int.add_comm` + `Nat.mul_comm`.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Rat.add_comm`
//! (see `algebra_field_inst.rs::init_rat_field_inst`) with a
//! `Declaration::Theorem` whose body is a genuine kernel-checked proof term
//! built by two `congrArg`s chained with `Eq.trans`.
//!
//! # Proof sketch (Phase 2 of #3572; design doc
//! `designs/2026-04-20-rat-ordered-field-constructive.md`, Addendum Phase 2)
//!
//! `Rat.add` is a reducible `Declaration::Definition`:
//!
//! ```text
//! Rat.add a b := Rat.mk
//!                  (Int.add (Int.mul (Rat.num a) (Int.ofNat (Rat.denom b)))
//!                           (Int.mul (Rat.num b) (Int.ofNat (Rat.denom a))))
//!                  (Nat.mul (Rat.denom a) (Rat.denom b))
//! ```
//!
//! Let `nA := Rat.num a`, `dA := Rat.denom a`, `nB := Rat.num b`,
//! `dB := Rat.denom b`, and the two summand blocks
//!
//! ```text
//! T_ab := Int.mul nA (Int.ofNat dB)
//! T_ba := Int.mul nB (Int.ofNat dA)
//! ```
//!
//! So under delta reduction both sides become
//!
//! ```text
//! LHS = Rat.mk (Int.add T_ab T_ba) (Nat.mul dA dB)
//! RHS = Rat.mk (Int.add T_ba T_ab) (Nat.mul dB dA)
//! ```
//!
//! The proof term chains
//!
//! 1. `h_num : Int.add T_ab T_ba = Int.add T_ba T_ab` from `Int.add_comm T_ab T_ba`
//! 2. `h_den : Nat.mul dA dB = Nat.mul dB dA` from `Nat.mul_comm dA dB`
//! 3. `step1 = congrArg (fun x : Int => Rat.mk x (Nat.mul dA dB)) h_num`
//!    `      : Rat.mk (Int.add T_ab T_ba) (Nat.mul dA dB)`
//!    `      = Rat.mk (Int.add T_ba T_ab) (Nat.mul dA dB)`
//! 4. `step2 = congrArg (fun y : Nat => Rat.mk (Int.add T_ba T_ab) y) h_den`
//!    `      : Rat.mk (Int.add T_ba T_ab) (Nat.mul dA dB)`
//!    `      = Rat.mk (Int.add T_ba T_ab) (Nat.mul dB dA)`
//! 5. `Eq.trans step1 step2` has the target shape.
//!
//! The delta reduction at both endpoints is handled by the kernel's definitional
//! equality when the theorem's stated type (`Rat.add a b = Rat.add b a`) is
//! compared against the proof term's inferred type (the spelt-out `Rat.mk` form).
//!
//! # Axiom closure
//!
//! The proof term mentions only foundational names and two Int/Nat-level
//! axioms:
//!
//! - `Int.add_comm` — already a `Declaration::Axiom` in
//!   `data_types_int_lemmas.rs`; kernel-primitive Int arithmetic axiom.
//! - `Nat.mul_comm` — already a `Declaration::Axiom` in
//!   `data_types_nat_lemmas.rs`; kernel-primitive Nat arithmetic axiom.
//! - `Eq.trans`, `congrArg` — `Declaration::Theorem` (not axioms); see
//!   `core_eq/basic.rs` and `core_eq/congruence.rs`.
//! - `Rat.mk`, `Rat.num`, `Rat.denom`, `Rat.add`, `Int.mul`, `Int.ofNat` —
//!   constructor / reducible Definitions.
//!
//! The transitive axiom closure of `Rat.add_comm` therefore reduces to
//! `{Int.add_comm, Nat.mul_comm}` (both are themselves plain `Axiom` with
//! no deps). Both are Int/Nat primitives, NOT Rat-domain assumptions; they
//! are foundational at the Rat layer.
//!
//! Tracks issue #3572 (Phase 2/3). See `algebra_rat_mul_comm_proof.rs`
//! (#3572 Phase 1) for the sibling `Rat.mul_comm` proof that pioneered
//! this pattern; `Rat.add_comm` differs only in the compound numerator
//! shape (requires `Int.ofNat` handle plumbing for the denominator
//! coercion inside each summand).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

/// Small bundle of reusable `Expr` handles threaded through the proof
/// helpers. Built once in `register_rat_add_comm_proof`.
struct RatAddCommSymbols {
    rat_type: Expr,
    int_type: Expr,
    nat_type: Expr,
    rat_mk: Expr,
    rat_num: Expr,
    rat_denom: Expr,
    rat_add: Expr,
    int_add: Expr,
    int_mul: Expr,
    nat_mul: Expr,
    /// `Int.ofNat : Nat → Int` — new vs Phase 1 (Rat.add coerces each
    /// denominator into Int via this wrapper).
    int_of_nat: Expr,
    int_add_comm: Expr,
    nat_mul_comm: Expr,
    /// `Eq.{1}` applied at `Sort (succ zero)` (Rat/Int/Nat all live here).
    eq_rat: Expr,
    /// `Eq.trans.{1}` at the same universe.
    eq_trans_rat: Expr,
    /// `congrArg.{1,1}` — suits all uses below (α,β ∈ {Int,Nat,Rat}).
    congr_arg: Expr,
}

impl RatAddCommSymbols {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            rat_type: Expr::const_(Name::from_string("Rat"), vec![]),
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_num: Expr::const_(Name::from_string("Rat.num"), vec![]),
            rat_denom: Expr::const_(Name::from_string("Rat.denom"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_add_comm: Expr::const_(Name::from_string("Int.add_comm"), vec![]),
            nat_mul_comm: Expr::const_(Name::from_string("Nat.mul_comm"), vec![]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans_rat: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }
}

/// Build the theorem type `∀ a b : Rat, Eq Rat (Rat.add a b) (Rat.add b a)`
/// plus the outer Rat locals `(a_id, a, bv_id, bv)` — returned so the caller
/// can reuse them inside the matching value lambdas.
fn build_rat_add_comm_type(
    sym: &RatAddCommSymbols,
) -> (Expr, EnvDeclBuilder, FVarId, Expr, FVarId, Expr) {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(sym.rat_type.clone());
    let (bv_id, bv) = b.fresh_local(sym.rat_type.clone());

    let rat_add_ab = Expr::app(Expr::app(sym.rat_add.clone(), a.clone()), bv.clone());
    let rat_add_ba = Expr::app(Expr::app(sym.rat_add.clone(), bv.clone()), a.clone());
    let concl = Expr::apps(
        sym.eq_rat.clone(),
        [sym.rat_type.clone(), rat_add_ab, rat_add_ba],
    );
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, sym.rat_type.clone(), concl);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, sym.rat_type.clone(), ty_raw);
    let type_ = b.finish(ty_raw);
    (type_, b, a_id, a, bv_id, bv)
}

/// Component expressions extracted from the outer Rat locals `a`, `bv`.
struct Components {
    /// `Nat.mul denom_a denom_b` / `Nat.mul denom_b denom_a`.
    nat_mul_ab: Expr,
    nat_mul_ba: Expr,
    /// Inner `Int.mul` summands (`T_ab := nA * ofNat dB`, `T_ba := nB * ofNat dA`).
    t_ab: Expr,
    t_ba: Expr,
    /// Numerator sums `Int.add T_ab T_ba` / `Int.add T_ba T_ab`.
    num_lhs: Expr,
    num_rhs: Expr,
    /// Denominator arguments (kept around for constructing `Nat.mul_comm dA dB`).
    denom_a: Expr,
    denom_b: Expr,
}

fn build_components(sym: &RatAddCommSymbols, a: &Expr, bv: &Expr) -> Components {
    let num_a = Expr::app(sym.rat_num.clone(), a.clone());
    let num_b = Expr::app(sym.rat_num.clone(), bv.clone());
    let denom_a = Expr::app(sym.rat_denom.clone(), a.clone());
    let denom_b = Expr::app(sym.rat_denom.clone(), bv.clone());
    // ofNat wrappers (Rat.add injects these; proof body must match exactly).
    let of_nat_da = Expr::app(sym.int_of_nat.clone(), denom_a.clone());
    let of_nat_db = Expr::app(sym.int_of_nat.clone(), denom_b.clone());
    // T_ab := Int.mul num_a (Int.ofNat denom_b)
    let t_ab = Expr::app(Expr::app(sym.int_mul.clone(), num_a), of_nat_db);
    // T_ba := Int.mul num_b (Int.ofNat denom_a)
    let t_ba = Expr::app(Expr::app(sym.int_mul.clone(), num_b), of_nat_da);
    // Numerator sums.
    let num_lhs = Expr::app(Expr::app(sym.int_add.clone(), t_ab.clone()), t_ba.clone());
    let num_rhs = Expr::app(Expr::app(sym.int_add.clone(), t_ba.clone()), t_ab.clone());
    // Denominator products.
    let nat_mul_ab = Expr::app(
        Expr::app(sym.nat_mul.clone(), denom_a.clone()),
        denom_b.clone(),
    );
    let nat_mul_ba = Expr::app(
        Expr::app(sym.nat_mul.clone(), denom_b.clone()),
        denom_a.clone(),
    );
    Components {
        nat_mul_ab,
        nat_mul_ba,
        t_ab,
        t_ba,
        num_lhs,
        num_rhs,
        denom_a,
        denom_b,
    }
}

/// Build a single `congrArg` step specialized for `Int` or `Nat` domain.
/// `ty` is the domain type (`Int` or `Nat`); `lhs`/`rhs` are the pre/post
/// commute forms; `f` is the motive lambda; `h` is the component equality.
fn build_congr_arg_step(
    sym: &RatAddCommSymbols,
    ty: &Expr,
    lhs: Expr,
    rhs: Expr,
    f: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(
        sym.congr_arg.clone(),
        [ty.clone(), sym.rat_type.clone(), lhs, rhs, f, h],
    )
}

/// Build the motive `fun x : Int => Rat.mk x (Nat.mul denom_a denom_b)`
/// under a child builder (FVar ranges disjoint from the outer scope).
fn build_f_num(sym: &RatAddCommSymbols, b: &EnvDeclBuilder, nat_mul_ab: &Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (x_id, x) = fb.fresh_local(sym.int_type.clone());
    let body = Expr::app(Expr::app(sym.rat_mk.clone(), x), nat_mul_ab.clone());
    let lam = fb.mk_lam(x_id, BinderInfo::Default, sym.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the motive `fun y : Nat => Rat.mk num_rhs y`.
fn build_f_den(sym: &RatAddCommSymbols, b: &EnvDeclBuilder, num_rhs: &Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (y_id, y) = fb.fresh_local(sym.nat_type.clone());
    let body = Expr::app(Expr::app(sym.rat_mk.clone(), num_rhs.clone()), y);
    let lam = fb.mk_lam(y_id, BinderInfo::Default, sym.nat_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the inner `congrArg + Eq.trans` proof term assuming `a` / `bv` are
/// the outer Rat locals.  The returned `Expr` is the body of the `λ a b =>`
/// lambda that the caller wraps.
fn build_rat_add_comm_body(
    sym: &RatAddCommSymbols,
    b: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
) -> Expr {
    let c = build_components(sym, a, bv);

    // Component-level equalities.
    // h_num : Int.add T_ab T_ba = Int.add T_ba T_ab
    //       = Int.add_comm T_ab T_ba
    let h_num = Expr::apps(sym.int_add_comm.clone(), [c.t_ab.clone(), c.t_ba.clone()]);
    // h_den : Nat.mul denom_a denom_b = Nat.mul denom_b denom_a
    //       = Nat.mul_comm denom_a denom_b
    let h_den = Expr::apps(
        sym.nat_mul_comm.clone(),
        [c.denom_a.clone(), c.denom_b.clone()],
    );

    // Two congrArg invocations.
    let f_num = build_f_num(sym, b, &c.nat_mul_ab);
    let f_den = build_f_den(sym, b, &c.num_rhs);
    let step1 = build_congr_arg_step(
        sym,
        &sym.int_type,
        c.num_lhs.clone(),
        c.num_rhs.clone(),
        f_num,
        h_num,
    );
    let step2 = build_congr_arg_step(
        sym,
        &sym.nat_type,
        c.nat_mul_ab.clone(),
        c.nat_mul_ba.clone(),
        f_den,
        h_den,
    );

    // Three Eq.trans endpoints at the Rat level.
    let rat_mk_lhs = Expr::app(
        Expr::app(sym.rat_mk.clone(), c.num_lhs),
        c.nat_mul_ab.clone(),
    );
    let rat_mk_mid = Expr::app(
        Expr::app(sym.rat_mk.clone(), c.num_rhs.clone()),
        c.nat_mul_ab,
    );
    let rat_mk_rhs = Expr::app(Expr::app(sym.rat_mk.clone(), c.num_rhs), c.nat_mul_ba);

    Expr::apps(
        sym.eq_trans_rat.clone(),
        [
            sym.rat_type.clone(),
            rat_mk_lhs,
            rat_mk_mid,
            rat_mk_rhs,
            step1,
            step2,
        ],
    )
}

impl Environment {
    /// Register `Rat.add_comm` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body chains two `congrArg` applications with `Eq.trans`,
    /// reducing `Rat`-level equality to `Int.add_comm` + `Nat.mul_comm` via
    /// the reducible `Rat.add` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_rat_arith()` has registered `Rat.add`,
    ///           `Rat.num`, `Rat.denom`, and `Rat.mk`.
    /// REQUIRES: `self.init_int_arith_lemmas()` has registered `Int.add_comm`,
    ///           `Int.add`, `Int.mul`, and `Int.ofNat`.
    /// REQUIRES: `self.init_nat_arith_lemmas()` has registered `Nat.mul_comm`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `congrArg`.
    /// ENSURES: On success, `Rat.add_comm` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive` modulo foundational closure.
    /// ENSURES: Idempotent — if `Rat.add_comm` is already registered, returns
    ///          `Ok(())` without modification.
    pub(crate) fn register_rat_add_comm_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Ensure dependencies are registered.
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = RatAddCommSymbols::new();
        let (type_, b, a_id, a, bv_id, bv) = build_rat_add_comm_type(&sym);
        let body = build_rat_add_comm_body(&sym, &b, &a, &bv);

        // Close the outer lambdas: λ a b => body.
        let value_raw = b.mk_lam(bv_id, BinderInfo::Default, sym.rat_type.clone(), body);
        let value_raw = b.mk_lam(a_id, BinderInfo::Default, sym.rat_type.clone(), value_raw);
        let value = b.finish(value_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3572 Phase 2). Two
        // `congrArg` applications composed with `Eq.trans`, reducing the
        // Rat-level commutativity to `Int.add_comm` + `Nat.mul_comm` via
        // delta on the reducible `Rat.add` definition. No `sorry`, no
        // self-reference. Replaces the prior `Declaration::Axiom`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
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
    /// `tests_algebra_rat_add_comm.rs` per the Phase 2 test-file split.
    #[test]
    fn test_rat_add_comm_idempotent() {
        let mut env = Environment::new();
        env.init_rat_field_inst().expect("first init");
        // Second call is a no-op through the `rat_field_inst_init` flag and
        // the explicit guard in `register_rat_add_comm_proof`.
        env.init_rat_field_inst().expect("second init (idempotent)");
        env.register_rat_add_comm_proof()
            .expect("direct re-registration (idempotent)");
        let info = env
            .get_const(&Name::from_string("Rat.add_comm"))
            .expect("Rat.add_comm should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
