// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of `Rat.mul_assoc` from `Int.mul_assoc` + `Nat.mul_assoc`.
//!
//! Replaces the prior `Declaration::Axiom` registration of `Rat.mul_assoc`
//! (see `algebra_field_inst.rs::init_rat_field_inst`) with a
//! `Declaration::Theorem` whose body is a genuine kernel-checked proof term
//! built by two `congrArg`s chained with `Eq.trans`.
//!
//! # Proof sketch (Phase 3 of Tranche C, Part of #3582; see
//! `reports/2026-04-20-3582-rat-left-distrib-blocker.md` for why this
//! Phase 3 theorem projects cleanly while `Rat.left_distrib` /
//! `Rat.right_distrib` still need the `Rat.mk_eq_mk_of_cross_eq` bridge)
//!
//! `Rat.mul` is a reducible `Declaration::Definition`:
//!
//! ```text
//! Rat.mul a b := Rat.mk (Int.mul (Rat.num a) (Rat.num b))
//!                       (Nat.mul (Rat.denom a) (Rat.denom b))
//! ```
//!
//! Let `nA := Rat.num a`, `nB := Rat.num b`, `nC := Rat.num c`,
//! `dA := Rat.denom a`, `dB := Rat.denom b`, `dC := Rat.denom c`.
//!
//! The kernel unfolds `Rat.mul` twice on each side and reduces `Rat.num /
//! Rat.denom` applied to `Rat.mk` via iota:
//!
//! ```text
//! LHS = Rat.mul (Rat.mul a b) c
//!     = Rat.mk (Int.mul (Int.mul nA nB) nC)
//!              (Nat.mul (Nat.mul dA dB) dC)
//! RHS = Rat.mul a (Rat.mul b c)
//!     = Rat.mk (Int.mul nA (Int.mul nB nC))
//!              (Nat.mul dA (Nat.mul dB dC))
//! ```
//!
//! Both sides differ only in the associativity bracketing of the
//! numerator and denominator — no bridge axiom (`Rat.mk_eq_mk_of_cross_eq`)
//! is needed because each side is already a `Rat.mk ... ...` term after
//! reduction. The proof chains
//!
//! 1. `h_num : Int.mul (Int.mul nA nB) nC = Int.mul nA (Int.mul nB nC)`
//!    from `Int.mul_assoc nA nB nC`
//! 2. `h_den : Nat.mul (Nat.mul dA dB) dC = Nat.mul dA (Nat.mul dB dC)`
//!    from `Nat.mul_assoc dA dB dC`
//! 3. `step1 = congrArg (fun x : Int => Rat.mk x (Nat.mul (Nat.mul dA dB) dC))
//!                      h_num`
//!    `      : Rat.mk (Int.mul (Int.mul nA nB) nC) (Nat.mul (Nat.mul dA dB) dC)`
//!    `      = Rat.mk (Int.mul nA (Int.mul nB nC))  (Nat.mul (Nat.mul dA dB) dC)`
//! 4. `step2 = congrArg (fun y : Nat => Rat.mk (Int.mul nA (Int.mul nB nC)) y)
//!                      h_den`
//!    `      : Rat.mk (Int.mul nA (Int.mul nB nC)) (Nat.mul (Nat.mul dA dB) dC)`
//!    `      = Rat.mk (Int.mul nA (Int.mul nB nC)) (Nat.mul dA (Nat.mul dB dC))`
//! 5. `Eq.trans step1 step2` has the target shape.
//!
//! The delta reduction at both endpoints is handled by the kernel's definitional
//! equality when the theorem's stated type
//! (`Rat.mul (Rat.mul a b) c = Rat.mul a (Rat.mul b c)`) is compared against
//! the proof term's inferred type (the spelt-out `Rat.mk` form above).
//!
//! # Axiom closure
//!
//! The proof term mentions only foundational names and two Int/Nat-level
//! axioms:
//!
//! - `Int.mul_assoc` — `Declaration::Axiom` in `data_types_int_lemmas.rs`;
//!   kernel-primitive Int arithmetic axiom.
//! - `Nat.mul_assoc` — `Declaration::Axiom` in `data_types_nat_lemmas.rs`;
//!   kernel-primitive Nat arithmetic axiom.
//! - `Eq.trans`, `congrArg` — `Declaration::Theorem` (not axioms); see
//!   `core_eq/basic.rs` and `core_eq/congruence.rs`.
//! - `Rat.mk`, `Rat.num`, `Rat.denom`, `Rat.mul`, `Int.mul`, `Nat.mul` —
//!   constructor / reducible Definitions.
//!
//! The transitive axiom closure of `Rat.mul_assoc` therefore reduces to
//! `{Int.mul_assoc, Nat.mul_assoc}` (both plain `Axiom` with no deps).
//! Both are Int/Nat primitives, NOT Rat-domain assumptions; they are
//! foundational at the Rat layer.
//!
//! Tracks issue #3582 (Tranche C Phase 3 — `Rat.mul_assoc`). See
//! `algebra_rat_mul_comm_proof.rs` (#3572 Phase 1) and
//! `algebra_rat_add_comm_proof.rs` (#3572 Phase 2) for the two-binder
//! sibling proofs that pioneered this pattern; `Rat.mul_assoc` is the
//! three-binder extension and does NOT require the
//! `Rat.mk_eq_mk_of_cross_eq` bridge (#3585) because both sides share the
//! same `Rat.mk ... ...` shape after delta+iota reduction, differing only
//! in bracketing of `Int.mul` / `Nat.mul`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

/// Small bundle of reusable `Expr` handles threaded through the proof
/// helpers. Built once in `register_rat_mul_assoc_proof`.
struct RatMulAssocSymbols {
    rat_type: Expr,
    int_type: Expr,
    nat_type: Expr,
    rat_mk: Expr,
    rat_num: Expr,
    rat_denom: Expr,
    rat_mul: Expr,
    int_mul: Expr,
    nat_mul: Expr,
    int_mul_assoc: Expr,
    nat_mul_assoc: Expr,
    /// `Eq.{1}` applied at `Sort (succ zero)` (Rat/Int/Nat all live here).
    eq_rat: Expr,
    /// `Eq.trans.{1}` at the same universe.
    eq_trans_rat: Expr,
    /// `congrArg.{1,1}` — suits all uses below (α,β ∈ {Int,Nat,Rat}).
    congr_arg: Expr,
}

impl RatMulAssocSymbols {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            rat_type: Expr::const_(Name::from_string("Rat"), vec![]),
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_num: Expr::const_(Name::from_string("Rat.num"), vec![]),
            rat_denom: Expr::const_(Name::from_string("Rat.denom"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            int_mul_assoc: Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
            nat_mul_assoc: Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_trans_rat: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
        }
    }
}

/// Build the theorem type
/// `∀ a b c : Rat, Eq Rat (Rat.mul (Rat.mul a b) c) (Rat.mul a (Rat.mul b c))`
/// plus the outer Rat locals — returned so the caller can reuse them inside
/// the matching value lambdas.
fn build_rat_mul_assoc_type(
    sym: &RatMulAssocSymbols,
) -> (
    Expr,
    EnvDeclBuilder,
    FVarId,
    Expr,
    FVarId,
    Expr,
    FVarId,
    Expr,
) {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(sym.rat_type.clone());
    let (bv_id, bv) = b.fresh_local(sym.rat_type.clone());
    let (c_id, c) = b.fresh_local(sym.rat_type.clone());

    // lhs = Rat.mul (Rat.mul a b) c
    let rat_mul_ab = Expr::app(Expr::app(sym.rat_mul.clone(), a.clone()), bv.clone());
    let lhs = Expr::app(Expr::app(sym.rat_mul.clone(), rat_mul_ab), c.clone());
    // rhs = Rat.mul a (Rat.mul b c)
    let rat_mul_bc = Expr::app(Expr::app(sym.rat_mul.clone(), bv.clone()), c.clone());
    let rhs = Expr::app(Expr::app(sym.rat_mul.clone(), a.clone()), rat_mul_bc);
    let concl = Expr::apps(sym.eq_rat.clone(), [sym.rat_type.clone(), lhs, rhs]);
    let ty_raw = b.mk_pi(c_id, BinderInfo::Default, sym.rat_type.clone(), concl);
    let ty_raw = b.mk_pi(bv_id, BinderInfo::Default, sym.rat_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, sym.rat_type.clone(), ty_raw);
    let type_ = b.finish(ty_raw);
    (type_, b, a_id, a, bv_id, bv, c_id, c)
}

/// Component expressions extracted from the outer Rat locals `a`, `bv`, `c`.
struct Components {
    /// Numerator projections.
    num_a: Expr,
    num_b: Expr,
    num_c: Expr,
    /// Denominator projections.
    denom_a: Expr,
    denom_b: Expr,
    denom_c: Expr,
    /// `Int.mul (Int.mul nA nB) nC`.
    int_mul_lhs: Expr,
    /// `Int.mul nA (Int.mul nB nC)`.
    int_mul_rhs: Expr,
    /// `Nat.mul (Nat.mul dA dB) dC`.
    nat_mul_lhs: Expr,
    /// `Nat.mul dA (Nat.mul dB dC)`.
    nat_mul_rhs: Expr,
}

fn build_components(sym: &RatMulAssocSymbols, a: &Expr, bv: &Expr, c: &Expr) -> Components {
    let num_a = Expr::app(sym.rat_num.clone(), a.clone());
    let num_b = Expr::app(sym.rat_num.clone(), bv.clone());
    let num_c = Expr::app(sym.rat_num.clone(), c.clone());
    let denom_a = Expr::app(sym.rat_denom.clone(), a.clone());
    let denom_b = Expr::app(sym.rat_denom.clone(), bv.clone());
    let denom_c = Expr::app(sym.rat_denom.clone(), c.clone());

    // Int.mul (Int.mul nA nB) nC
    let int_mul_ab = Expr::app(Expr::app(sym.int_mul.clone(), num_a.clone()), num_b.clone());
    let int_mul_lhs = Expr::app(Expr::app(sym.int_mul.clone(), int_mul_ab), num_c.clone());
    // Int.mul nA (Int.mul nB nC)
    let int_mul_bc = Expr::app(Expr::app(sym.int_mul.clone(), num_b.clone()), num_c.clone());
    let int_mul_rhs = Expr::app(Expr::app(sym.int_mul.clone(), num_a.clone()), int_mul_bc);

    // Nat.mul (Nat.mul dA dB) dC
    let nat_mul_ab = Expr::app(
        Expr::app(sym.nat_mul.clone(), denom_a.clone()),
        denom_b.clone(),
    );
    let nat_mul_lhs = Expr::app(Expr::app(sym.nat_mul.clone(), nat_mul_ab), denom_c.clone());
    // Nat.mul dA (Nat.mul dB dC)
    let nat_mul_bc = Expr::app(
        Expr::app(sym.nat_mul.clone(), denom_b.clone()),
        denom_c.clone(),
    );
    let nat_mul_rhs = Expr::app(Expr::app(sym.nat_mul.clone(), denom_a.clone()), nat_mul_bc);

    Components {
        num_a,
        num_b,
        num_c,
        denom_a,
        denom_b,
        denom_c,
        int_mul_lhs,
        int_mul_rhs,
        nat_mul_lhs,
        nat_mul_rhs,
    }
}

/// Build a single `congrArg` step specialized for `Int` or `Nat` domain.
/// `ty` is the domain type (`Int` or `Nat`); `lhs`/`rhs` are the pre/post
/// reassociation forms; `f` is the motive lambda; `h` is the component
/// equality.
fn build_congr_arg_step(
    sym: &RatMulAssocSymbols,
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

/// Build the motive
/// `fun x : Int => Rat.mk x (Nat.mul (Nat.mul denom_a denom_b) denom_c)`
/// under a child builder (FVar ranges disjoint from the outer scope).
fn build_f_num(sym: &RatMulAssocSymbols, b: &EnvDeclBuilder, nat_mul_lhs: &Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (x_id, x) = fb.fresh_local(sym.int_type.clone());
    let body = Expr::app(Expr::app(sym.rat_mk.clone(), x), nat_mul_lhs.clone());
    let lam = fb.mk_lam(x_id, BinderInfo::Default, sym.int_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the motive
/// `fun y : Nat => Rat.mk (Int.mul num_a (Int.mul num_b num_c)) y`.
fn build_f_den(sym: &RatMulAssocSymbols, b: &EnvDeclBuilder, int_mul_rhs: &Expr) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(b);
    let (y_id, y) = fb.fresh_local(sym.nat_type.clone());
    let body = Expr::app(Expr::app(sym.rat_mk.clone(), int_mul_rhs.clone()), y);
    let lam = fb.mk_lam(y_id, BinderInfo::Default, sym.nat_type.clone(), body);
    fb.finish_child(lam)
}

/// Build the inner `congrArg + Eq.trans` proof term assuming `a` / `bv` / `c`
/// are the outer Rat locals. The returned `Expr` is the body of the
/// `λ a b c =>` lambda that the caller wraps.
fn build_rat_mul_assoc_body(
    sym: &RatMulAssocSymbols,
    b: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    c: &Expr,
) -> Expr {
    let comp = build_components(sym, a, bv, c);

    // Component-level equalities.
    // h_num : Int.mul (Int.mul nA nB) nC = Int.mul nA (Int.mul nB nC)
    //       = Int.mul_assoc nA nB nC
    let h_num = Expr::apps(
        sym.int_mul_assoc.clone(),
        [comp.num_a.clone(), comp.num_b.clone(), comp.num_c.clone()],
    );
    // h_den : Nat.mul (Nat.mul dA dB) dC = Nat.mul dA (Nat.mul dB dC)
    //       = Nat.mul_assoc dA dB dC
    let h_den = Expr::apps(
        sym.nat_mul_assoc.clone(),
        [
            comp.denom_a.clone(),
            comp.denom_b.clone(),
            comp.denom_c.clone(),
        ],
    );

    // Two congrArg invocations.
    let f_num = build_f_num(sym, b, &comp.nat_mul_lhs);
    let f_den = build_f_den(sym, b, &comp.int_mul_rhs);
    let step1 = build_congr_arg_step(
        sym,
        &sym.int_type,
        comp.int_mul_lhs.clone(),
        comp.int_mul_rhs.clone(),
        f_num,
        h_num,
    );
    let step2 = build_congr_arg_step(
        sym,
        &sym.nat_type,
        comp.nat_mul_lhs.clone(),
        comp.nat_mul_rhs.clone(),
        f_den,
        h_den,
    );

    // Three Eq.trans endpoints at the Rat level.
    let rat_mk_lhs = Expr::app(
        Expr::app(sym.rat_mk.clone(), comp.int_mul_lhs),
        comp.nat_mul_lhs.clone(),
    );
    let rat_mk_mid = Expr::app(
        Expr::app(sym.rat_mk.clone(), comp.int_mul_rhs.clone()),
        comp.nat_mul_lhs,
    );
    let rat_mk_rhs = Expr::app(
        Expr::app(sym.rat_mk.clone(), comp.int_mul_rhs),
        comp.nat_mul_rhs,
    );

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
    /// Register `Rat.mul_assoc` as a kernel-checked `Declaration::Theorem`.
    ///
    /// The proof body chains two `congrArg` applications with `Eq.trans`,
    /// reducing `Rat`-level associativity to `Int.mul_assoc` +
    /// `Nat.mul_assoc` via the reducible `Rat.mul` definition.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_rat_arith()` has registered `Rat.mul`,
    ///           `Rat.num`, `Rat.denom`, and `Rat.mk`.
    /// REQUIRES: `self.init_int_arith_lemmas()` has registered `Int.mul_assoc`
    ///           and `Int.mul`.
    /// REQUIRES: `self.init_nat_arith_lemmas()` has registered `Nat.mul_assoc`
    ///           and `Nat.mul`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.trans`, `congrArg`.
    /// ENSURES: On success, `Rat.mul_assoc` is a `Declaration::Theorem`.
    /// ENSURES: Idempotent — if `Rat.mul_assoc` is already registered, returns
    ///          `Ok(())` without modification.
    pub(crate) fn register_rat_mul_assoc_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // Ensure dependencies are registered.
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;
        self.init_nat_arith_lemmas()?;
        self.init_eq()?;

        let sym = RatMulAssocSymbols::new();
        let (type_, b, a_id, a, bv_id, bv, c_id, c) = build_rat_mul_assoc_type(&sym);
        let body = build_rat_mul_assoc_body(&sym, &b, &a, &bv, &c);

        // Close the outer lambdas: λ a b c => body.
        let value_raw = b.mk_lam(c_id, BinderInfo::Default, sym.rat_type.clone(), body);
        let value_raw = b.mk_lam(bv_id, BinderInfo::Default, sym.rat_type.clone(), value_raw);
        let value_raw = b.mk_lam(a_id, BinderInfo::Default, sym.rat_type.clone(), value_raw);
        let value = b.finish(value_raw);

        // SOUNDNESS: Real kernel-checked proof term (#3582 Tranche C Phase 3).
        // Two `congrArg` applications composed with `Eq.trans`, reducing the
        // Rat-level associativity to `Int.mul_assoc` + `Nat.mul_assoc` via
        // delta on the reducible `Rat.mul` definition and iota on
        // `Rat.num / Rat.denom` applied to `Rat.mk`. No `sorry`, no
        // self-reference, no bridge axiom. Replaces the prior
        // `Declaration::Axiom` at `algebra_field_inst.rs:159-163`.
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
    /// `tests_algebra_rat_mul_assoc.rs` per the per-phase companion file
    /// convention (mirrors Phase 2 `tests_algebra_rat_add_comm.rs`).
    #[test]
    fn test_rat_mul_assoc_idempotent() {
        let mut env = Environment::new();
        env.init_rat_field_inst().expect("first init");
        // Second call is a no-op through the `rat_field_inst_init` flag and
        // the explicit guard in `register_rat_mul_assoc_proof`.
        env.init_rat_field_inst().expect("second init (idempotent)");
        env.register_rat_mul_assoc_proof()
            .expect("direct re-registration (idempotent)");
        let info = env
            .get_const(&Name::from_string("Rat.mul_assoc"))
            .expect("Rat.mul_assoc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_rat_mul_assoc_type_checks_as_theorem() {
        let mut env = Environment::new();
        env.init_rat_field_inst().expect("init");
        let info = env
            .get_const(&Name::from_string("Rat.mul_assoc"))
            .expect("Rat.mul_assoc should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Rat.mul_assoc should be Declaration::Theorem (post-#3582 Phase 3), got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Rat.mul_assoc Theorem must have a stored proof term"
        );
    }
}
