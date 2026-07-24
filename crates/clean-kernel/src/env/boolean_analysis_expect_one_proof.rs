// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proofs of the uniform-expectation normalization `E[1] = 1` and
//! the CLOSED diagonal character orthonormality `E[χ_S·χ_S] = 1` — rungs
//! A4-A6 of the Parseval assembly (A1-A3 live in
//! `boolean_analysis_fin_sum_const_one_proof.rs`):
//!
//! - A4a `Nat.one_le_two_pow : ∀ n, Nat.le 1 (Nat.pow 2 n)` — positivity of the
//!   cube size. `Nat.pow_le_pow_right 2 0 n (1 ≤ 2) (Nat.zero_le n)` gives
//!   `2^0 ≤ 2^n`, and `2^0 ≡ 1` definitionally.
//!
//! - A4b `Rat.natCast_ne_zero_of_pos : ∀ m, Nat.le 1 m →`
//!   `(Eq Rat (Rat.mk (Int.ofNat m) 1) Rat.zero → False)` — a positive Nat cast
//!   into the `Rat := Quot Rat.Raw.Equiv` quotient is nonzero. The quotient
//!   equality is INVERTED by transporting along it through a `Quot.lift`
//!   discriminator `P := Quot.lift (fun r => Equiv r zeroRaw) resp` (respect by
//!   `Equiv.symm`/`Equiv.trans` + `propext` — FOUNDATIONAL): `P Rat.zero` holds
//!   by `Equiv.refl`, so `Eq.subst` along the hypothesis yields
//!   `Equiv (Raw.mk (ofNat m) 1) zeroRaw`, which unfolds to the Int equation
//!   `(ofNat m)·1 = 0·1`. `Int.mul_one`/`Int.zero_mul` reduce it to
//!   `ofNat m = Int.zero`; `congrArg Int.toNat` + `Int.toNat_ofNat` reflect it
//!   to `Eq Nat m 0`; substituting into `1 ≤ m` gives `1 ≤ 0`, killed by
//!   `Nat.not_succ_le_zero`.
//!
//! - A5 `BoolAnalysis.Expect_const_one : ∀ n, Expect n (fun _ => 1) = 1` — THE
//!   normalization. `Expect n (const 1)` δβ-unfolds to
//!   `Rat.div (Fin.sum (2^n) (const 1)) D` with `D = Rat.mk (Int.ofNat (2^n)) 1`;
//!   `Fin.sum_const_one` (A2) rewrites the numerator to `D` (under
//!   `congrArg (Rat.div · D)`), and `Rat.div_self_of_ne_zero` (A3) with the
//!   A4 nonzero witness collapses `D/D` to `1`.
//!
//! - A6 `BoolAnalysis.chi_self_inner_eq_one : ∀ n S,`
//!   `Expect n (fun x => chi n S x * chi n S x) = 1` — the DIAGONAL character
//!   orthonormality, fully closed: `Eq.trans` of the landed
//!   `chi_self_inner_eq_expect_one` (E[χ_S²] = E[1]) with A5.
//!
//! All kernel-checked `Declaration::Theorem`s. The closure reaches `propext`
//! and `Quot.sound` — both FOUNDATIONAL (the certified base), so every rung is
//! `ProofQuality::Constructive` with an EMPTY admitted-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the Expect-normalization rungs.
struct ExpectOneConsts {
    nat: Expr,
    int: Expr,
    rat: Expr,
    prop: Expr,
    false_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    nat_zero_le: Expr,
    nat_pow: Expr,
    nat_pow_le_pow_right: Expr,
    nat_not_succ_le_zero: Expr,
    int_of_nat: Expr,
    int_zero: Expr,
    int_mul: Expr,
    int_to_nat: Expr,
    int_mul_one: Expr,
    int_zero_mul: Expr,
    int_tonat_ofnat: Expr,
    rat_mk: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_div: Expr,
    rat_mul: Expr,
    fin_sum: Expr,
    fin: Expr,
    // Quot machinery over Rat.Raw / Rat.Raw.Equiv.
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    raw_equiv_refl: Expr,
    raw_equiv_symm: Expr,
    raw_equiv_trans: Expr,
    quot_lift_prop: Expr,
    propext: Expr,
    // Eq toolkit.
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // BoolAnalysis layer.
    expect: Expr,
    chi: Expr,
    hcpoint: Expr,
    // A-rung consumers.
    fin_sum_const_one: Expr,
    rat_div_self_of_ne_zero: Expr,
    chi_self_inner_eq_expect_one: Expr,
}

impl ExpectOneConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            int: Expr::const_(Name::from_string("Int"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            false_: Expr::const_(Name::from_string("False"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_refl: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            nat_le_step: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            nat_zero_le: Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_pow_le_pow_right: Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
            nat_not_succ_le_zero: Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_to_nat: Expr::const_(Name::from_string("Int.toNat"), vec![]),
            int_mul_one: Expr::const_(Name::from_string("Int.mul_one"), vec![]),
            int_zero_mul: Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
            int_tonat_ofnat: Expr::const_(Name::from_string("Int.toNat_ofNat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            raw: Expr::const_(Name::from_string("Rat.Raw"), vec![]),
            raw_mk: Expr::const_(Name::from_string("Rat.Raw.mk"), vec![]),
            raw_equiv: Expr::const_(Name::from_string("Rat.Raw.Equiv"), vec![]),
            raw_equiv_refl: Expr::const_(Name::from_string("Rat.Raw.Equiv.refl"), vec![]),
            raw_equiv_symm: Expr::const_(Name::from_string("Rat.Raw.Equiv.symm"), vec![]),
            raw_equiv_trans: Expr::const_(Name::from_string("Rat.Raw.Equiv.trans"), vec![]),
            quot_lift_prop: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![l1.clone(), l1.clone()],
            ),
            propext: Expr::const_(Name::from_string("propext"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            expect: Expr::const_(Name::from_string("BoolAnalysis.Expect"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            fin_sum_const_one: Expr::const_(Name::from_string("Fin.sum_const_one"), vec![]),
            rat_div_self_of_ne_zero: Expr::const_(
                Name::from_string("Rat.div_self_of_ne_zero"),
                vec![],
            ),
            chi_self_inner_eq_expect_one: Expr::const_(
                Name::from_string("BoolAnalysis.chi_self_inner_eq_expect_one"),
                vec![],
            ),
        }
    }

    // ── Nat helpers ──
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }
    fn nat_one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    fn nat_two(&self) -> Expr {
        self.succ(self.nat_one())
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_two(), n.clone()])
    }

    // ── Int helpers ──
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }
    /// `Int.ofNat 1`.
    fn int_one(&self) -> Expr {
        self.of_nat(self.nat_one())
    }
    fn imul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [a, b])
    }

    // ── Eq toolkit (per carrier) ──
    fn eq_at(&self, ty: &Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [ty.clone(), l, r])
    }
    fn symm_at(&self, ty: &Expr, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [ty.clone(), l, r, h])
    }
    fn trans_at(&self, ty: &Expr, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [ty.clone(), a, b, c, h1, h2])
    }
    /// `@congrArg A B a1 a2 f h : Eq B (f a1) (f a2)`.
    fn congr(&self, a_ty: &Expr, b_ty: &Expr, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [a_ty.clone(), b_ty.clone(), a1, a2, f, h],
        )
    }

    // ── Rat / Raw helpers ──
    /// `Rat.mk (Int.ofNat m) 1` — the Nat cast.
    fn rat_natcast(&self, m: Expr) -> Expr {
        Expr::apps(self.rat_mk.clone(), [self.of_nat(m), self.nat_one()])
    }
    /// `Rat.Raw.mk i d`.
    fn raw_of(&self, i: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [i, d])
    }
    /// `Rat.Raw.mk Int.zero 1` — the canonical zero representative
    /// (`Rat.zero ≡ Quot.mk zeroRaw` definitionally).
    fn zero_raw(&self) -> Expr {
        self.raw_of(self.int_zero.clone(), self.nat_one())
    }
    /// `Rat.Raw.Equiv p q`.
    fn equiv(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.raw_equiv.clone(), [p, q])
    }

    // ── BoolAnalysis helpers ──
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `fun (_ : HCPoint n) => Rat.one` — the const-1 integrand.
    fn const_one_integrand(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, _x) = b.fresh_local(hcp.clone());
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, self.rat_one.clone()))
    }
    /// `fun (_ : Fin m) => Rat.one` — the const-1 summand (Fin.sum_const_one's
    /// LHS shape).
    fn const_one_fin_fn(&self, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = Expr::app(self.fin.clone(), m.clone());
        let (i_id, _i) = b.fresh_local(fin_m.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_m, self.rat_one.clone()))
    }
}

// ===========================================================================
// A4a: Nat.one_le_two_pow
// ===========================================================================

/// `∀ (n : Nat), Nat.le 1 (Nat.pow 2 n)`.
fn one_le_two_pow_type(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let concl = c.le(c.nat_one(), c.pow2(&n));
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
}

/// `fun n => Nat.pow_le_pow_right 2 0 n (le 1 2) (Nat.zero_le n)`.
///
/// The result type `le (pow 2 0) (pow 2 n)` is def-eq to `le 1 (pow 2 n)`
/// (`pow 2 0 ≡ 1` by the carrier's base ι-step). The `1 ≤ 2` witness is
/// `Nat.le.step 1 1 (Nat.le.refl 1)`.
fn one_le_two_pow_value(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let one = c.nat_one();
    // le 1 2 := Nat.le.step 1 1 (Nat.le.refl 1).
    let le_refl_1 = Expr::app(c.nat_le_refl.clone(), one.clone());
    let h12 = Expr::apps(c.nat_le_step.clone(), [one.clone(), one.clone(), le_refl_1]);
    let zero_le_n = Expr::app(c.nat_zero_le.clone(), n.clone());
    let body = Expr::apps(
        c.nat_pow_le_pow_right.clone(),
        [c.nat_two(), c.nat_zero.clone(), n.clone(), h12, zero_le_n],
    );
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
}

// ===========================================================================
// A4b: Rat.natCast_ne_zero_of_pos
// ===========================================================================

/// `∀ (m : Nat), Nat.le 1 m → Eq Rat (Rat.mk (Int.ofNat m) 1) Rat.zero → False`.
fn natcast_ne_zero_type(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let pos_ty = c.le(c.nat_one(), m.clone());
    let (pos_id, _pos) = b.fresh_local(pos_ty.clone());
    let eq0_ty = c.eq_at(&c.rat, c.rat_natcast(m.clone()), c.rat_zero.clone());
    let (h_id, _h) = b.fresh_local(eq0_ty.clone());
    let r = b.mk_pi(h_id, BinderInfo::Default, eq0_ty, c.false_.clone());
    let r = b.mk_pi(pos_id, BinderInfo::Default, pos_ty, r);
    let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// The `Quot.lift` zero-class discriminator
/// `P := fun (a : Rat) => @Quot.lift Raw Equiv Prop (fun r => Equiv r zeroRaw) resp a`,
/// where `resp q q' hq := propext _ _ (trans (symm hq) ·) (trans hq ·)`.
fn is_zero_motive(c: &ExpectOneConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (a_id, a) = b.fresh_local(c.rat.clone());

    // g := fun (r : Raw) => Equiv r zeroRaw.
    let g = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (r_id, r) = d.fresh_local(c.raw.clone());
        let body = c.equiv(r, c.zero_raw());
        d.finish_child(d.mk_lam(r_id, BinderInfo::Default, c.raw.clone(), body))
    };

    // resp := fun (q q' : Raw) (hq : Equiv q q') =>
    //   propext (Equiv q zeroRaw) (Equiv q' zeroRaw)
    //     (fun hz => Equiv.trans q' q zeroRaw (Equiv.symm q q' hq) hz)
    //     (fun hz => Equiv.trans q q' zeroRaw hq hz)
    let resp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (q_id, q) = d.fresh_local(c.raw.clone());
        let (q2_id, q2) = d.fresh_local(c.raw.clone());
        let hq_ty = c.equiv(q.clone(), q2.clone());
        let (hq_id, hq) = d.fresh_local(hq_ty.clone());

        let p1 = c.equiv(q.clone(), c.zero_raw());
        let p2 = c.equiv(q2.clone(), c.zero_raw());

        // fwd : Equiv q zeroRaw → Equiv q' zeroRaw.
        let fwd = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (hz_id, hz) = e.fresh_local(p1.clone());
            let symm_hq = Expr::apps(
                c.raw_equiv_symm.clone(),
                [q.clone(), q2.clone(), hq.clone()],
            );
            let body = Expr::apps(
                c.raw_equiv_trans.clone(),
                [q2.clone(), q.clone(), c.zero_raw(), symm_hq, hz],
            );
            e.finish_child(e.mk_lam(hz_id, BinderInfo::Default, p1.clone(), body))
        };
        // bwd : Equiv q' zeroRaw → Equiv q zeroRaw.
        let bwd = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (hz_id, hz) = e.fresh_local(p2.clone());
            let body = Expr::apps(
                c.raw_equiv_trans.clone(),
                [q.clone(), q2.clone(), c.zero_raw(), hq.clone(), hz],
            );
            e.finish_child(e.mk_lam(hz_id, BinderInfo::Default, p2.clone(), body))
        };

        // Faithful `propext : {a b} → (a ↔ b) → a = b` takes one `Iff`; package
        // the two implications via `Iff.intro p1 p2 fwd bwd`.
        let iff = Expr::apps(
            Expr::const_(Name::from_string("Iff.intro"), vec![]),
            [p1.clone(), p2.clone(), fwd, bwd],
        );
        let pe = Expr::apps(c.propext.clone(), [p1, p2, iff]);
        let lam = d.mk_lam(hq_id, BinderInfo::Default, hq_ty, pe);
        let lam = d.mk_lam(q2_id, BinderInfo::Default, c.raw.clone(), lam);
        let lam = d.mk_lam(q_id, BinderInfo::Default, c.raw.clone(), lam);
        d.finish_child(lam)
    };

    let lift = Expr::apps(
        c.quot_lift_prop.clone(),
        [
            c.raw.clone(),
            c.raw_equiv.clone(),
            c.prop.clone(),
            g,
            resp,
            a.clone(),
        ],
    );
    b.finish_child(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), lift))
}

/// See the module doc for the proof route.
fn natcast_ne_zero_value(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let pos_ty = c.le(c.nat_one(), m.clone());
    let (pos_id, pos) = b.fresh_local(pos_ty.clone());
    let cast_m = c.rat_natcast(m.clone());
    let eq0_ty = c.eq_at(&c.rat, cast_m.clone(), c.rat_zero.clone());
    let (h_id, h) = b.fresh_local(eq0_ty.clone());

    // P : Rat → Prop (the zero-class discriminator).
    let motive = is_zero_motive(c, &b);

    // pz : P Rat.zero — defeq to `Equiv zeroRaw zeroRaw`, by Equiv.refl.
    let pz = Expr::app(c.raw_equiv_refl.clone(), c.zero_raw());

    // hsymm : Rat.zero = cast_m.
    let hsymm = c.symm_at(&c.rat, cast_m.clone(), c.rat_zero.clone(), h.clone());

    // pe : P cast_m := Eq.subst Rat P Rat.zero cast_m hsymm pz.
    //   Defeq-unfolds to `Equiv (Raw.mk (ofNat m) 1) zeroRaw`, i.e.
    //   `Eq Int ((ofNat m)·(ofNat 1)) (Int.zero·(ofNat 1))`.
    let pe = Expr::apps(
        c.eq_subst.clone(),
        [
            c.rat.clone(),
            motive,
            c.rat_zero.clone(),
            cast_m.clone(),
            hsymm,
            pz,
        ],
    );

    // ── Int chain: ofNat m = Int.zero ──
    let of_m = c.of_nat(m.clone());
    let o1 = c.int_one();
    let mul_m_1 = c.imul(of_m.clone(), o1.clone());
    let mul_0_1 = c.imul(c.int_zero.clone(), o1.clone());

    // s0 : ofNat m = (ofNat m)·1   (symm of Int.mul_one).
    let s0 = c.symm_at(
        &c.int,
        mul_m_1.clone(),
        of_m.clone(),
        Expr::app(c.int_mul_one.clone(), of_m.clone()),
    );
    // s2 : Int.zero·1 = Int.zero   (Int.zero_mul).
    let s2 = Expr::app(c.int_zero_mul.clone(), o1.clone());
    // (pe ; s2) : (ofNat m)·1 = Int.zero.
    let mid = c.trans_at(
        &c.int,
        mul_m_1.clone(),
        mul_0_1.clone(),
        c.int_zero.clone(),
        pe,
        s2,
    );
    // heq : ofNat m = Int.zero.
    let heq = c.trans_at(
        &c.int,
        of_m.clone(),
        mul_m_1.clone(),
        c.int_zero.clone(),
        s0,
        mid,
    );

    // ── Reflect to Nat: m = 0 ──
    // t1' : m = toNat (ofNat m)   (symm of Int.toNat_ofNat m).
    let tonat_of_m = Expr::app(c.int_to_nat.clone(), of_m.clone());
    let t1p = c.symm_at(
        &c.nat,
        tonat_of_m.clone(),
        m.clone(),
        Expr::app(c.int_tonat_ofnat.clone(), m.clone()),
    );
    // t2 : toNat (ofNat m) = toNat Int.zero   (congrArg Int.toNat heq).
    let tonat_zero = Expr::app(c.int_to_nat.clone(), c.int_zero.clone());
    let t2 = c.congr(
        &c.int,
        &c.nat,
        of_m.clone(),
        c.int_zero.clone(),
        c.int_to_nat.clone(),
        heq,
    );
    // t3 : toNat Int.zero = 0   (Int.toNat_ofNat 0; Int.zero ≡ ofNat 0).
    let t3 = Expr::app(c.int_tonat_ofnat.clone(), c.nat_zero.clone());
    // hm0 : m = 0.
    let t23 = c.trans_at(
        &c.nat,
        tonat_of_m.clone(),
        tonat_zero.clone(),
        c.nat_zero.clone(),
        t2,
        t3,
    );
    let hm0 = c.trans_at(&c.nat, m.clone(), tonat_of_m, c.nat_zero.clone(), t1p, t23);

    // ── Kill: 1 ≤ m  +  m = 0  ⇒  1 ≤ 0  ⇒  False ──
    // le_motive := fun (z : Nat) => le 1 z.
    let le_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.nat.clone());
        let body = c.le(c.nat_one(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let hle0 = Expr::apps(
        c.eq_subst.clone(),
        [
            c.nat.clone(),
            le_motive,
            m.clone(),
            c.nat_zero.clone(),
            hm0,
            pos,
        ],
    );
    // Nat.not_succ_le_zero 0 hle0 : False   (le 1 0 ≡ le (succ 0) 0).
    let falsum = Expr::apps(c.nat_not_succ_le_zero.clone(), [c.nat_zero.clone(), hle0]);

    let val = b.mk_lam(h_id, BinderInfo::Default, eq0_ty, falsum);
    let val = b.mk_lam(pos_id, BinderInfo::Default, pos_ty, val);
    let val = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

// ===========================================================================
// A5: BoolAnalysis.Expect_const_one
// ===========================================================================

/// `∀ (n : Nat), Eq Rat (Expect n (fun _ => Rat.one)) Rat.one`.
fn expect_const_one_type(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let lhs = Expr::apps(c.expect.clone(), [n.clone(), c.const_one_integrand(&b, &n)]);
    let concl = c.eq_at(&c.rat, lhs, c.rat_one.clone());
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
}

/// `fun n => Eq.trans (congrArg (Rat.div · D) (Fin.sum_const_one (2^n)))`
/// `              (Rat.div_self_of_ne_zero D (natCast_ne_zero_of_pos (2^n) (one_le_two_pow n)))`.
fn expect_const_one_value(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let p2n = c.pow2(&n);
    // D := Rat.mk (Int.ofNat (2^n)) 1 — Expect's denominator AND (by A2) the
    // value of the const-1 numerator.
    let d_rat = c.rat_natcast(p2n.clone());

    // lhs := Expect n (fun _ => 1)  — δβ-unfolds to Rat.div (Fin.sum (2^n) (const 1)) D.
    let lhs = Expr::apps(c.expect.clone(), [n.clone(), c.const_one_integrand(&b, &n)]);
    let num = Expr::apps(
        c.fin_sum.clone(),
        [p2n.clone(), c.const_one_fin_fn(&b, &p2n)],
    );

    // div_by_d := fun (s : Rat) => Rat.div s D.
    let div_by_d = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = d.fresh_local(c.rat.clone());
        let body = Expr::apps(c.rat_div.clone(), [s, d_rat.clone()]);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
    };

    // step1 : Rat.div num D = Rat.div D D   (congrArg over Fin.sum_const_one (2^n)).
    //   The stated LHS is defeq to `Expect n (fun _ => 1)`.
    let sum_eq = Expr::app(c.fin_sum_const_one.clone(), p2n.clone());
    let step1 = c.congr(&c.rat, &c.rat, num, d_rat.clone(), div_by_d, sum_eq);

    // ne : Eq Rat D Rat.zero → False.
    let one_le = Expr::app(
        Expr::const_(Name::from_string("Nat.one_le_two_pow"), vec![]),
        n.clone(),
    );
    let ne = Expr::apps(
        Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]),
        [p2n.clone(), one_le],
    );
    // step2 : Rat.div D D = Rat.one.
    let step2 = Expr::apps(c.rat_div_self_of_ne_zero.clone(), [d_rat.clone(), ne]);

    let div_dd = Expr::apps(c.rat_div.clone(), [d_rat.clone(), d_rat.clone()]);
    let proof = c.trans_at(&c.rat, lhs, div_dd, c.rat_one.clone(), step1, step2);

    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), proof))
}

// ===========================================================================
// A6: BoolAnalysis.chi_self_inner_eq_one — the CLOSED diagonal orthonormality
// ===========================================================================

/// `fun (x : HCPoint n) => chi n S x · chi n S x` — the self-inner-product
/// integrand (byte-for-byte the shape `chi_self_inner_eq_expect_one` states).
fn chi_sq_integrand(c: &ExpectOneConsts, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let chi_sx = Expr::apps(c.chi.clone(), [n.clone(), s.clone(), x]);
    let body = Expr::apps(c.rat_mul.clone(), [chi_sx.clone(), chi_sx]);
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ (n : Nat) (S : HCPoint n), Eq Rat (Expect n (fun x => chi n S x * chi n S x)) Rat.one`.
fn chi_self_inner_one_type(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let lhs = Expr::apps(
        c.expect.clone(),
        [n.clone(), chi_sq_integrand(c, &b, &n, &s)],
    );
    let concl = c.eq_at(&c.rat, lhs, c.rat_one.clone());
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

/// `fun n S => Eq.trans (chi_self_inner_eq_expect_one n S) (Expect_const_one n)`.
fn chi_self_inner_one_value(c: &ExpectOneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());

    let lhs = Expr::apps(
        c.expect.clone(),
        [n.clone(), chi_sq_integrand(c, &b, &n, &s)],
    );
    let mid = Expr::apps(c.expect.clone(), [n.clone(), c.const_one_integrand(&b, &n)]);

    let leg1 = Expr::apps(
        c.chi_self_inner_eq_expect_one.clone(),
        [n.clone(), s.clone()],
    );
    let leg2 = Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.Expect_const_one"), vec![]),
        n.clone(),
    );
    let proof = c.trans_at(&c.rat, lhs, mid, c.rat_one.clone(), leg1, leg2);

    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register the A4-A6 Expect-normalization rungs:
    /// `Nat.one_le_two_pow`, `Rat.natCast_ne_zero_of_pos`,
    /// `BoolAnalysis.Expect_const_one`, and the closed diagonal orthonormality
    /// `BoolAnalysis.chi_self_inner_eq_one`. Idempotent.
    pub(crate) fn register_expect_one_theorems(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_rat()?;
        self.init_boolean_analysis_foundations()?;
        // A1-A3 (Rat.add_natCast_one, Fin.sum_const_one, Rat.div_self_of_ne_zero).
        self.register_fin_sum_const_one_theorems()?;
        // A4a dependencies.
        self.register_nat_pow_le_pow_right_proof()?;
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.register_nat_not_succ_le_zero_theorem()?;
        // A4b dependencies.
        self.register_int_tonat_ofnat_proof()?;
        self.register_int_zero_mul_proof()?;
        // A6 dependency (the landed diagonal E[χ²] = E[1]).
        self.register_chi_self_inner_theorem()?;

        let c = ExpectOneConsts::new();

        if self
            .get_const(&Name::from_string("Nat.one_le_two_pow"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Nat.one_le_two_pow"),
                level_params: vec![],
                type_: one_le_two_pow_type(&c),
                value: one_le_two_pow_value(&c),
            })?;
        }

        if self
            .get_const(&Name::from_string("Rat.natCast_ne_zero_of_pos"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Rat.natCast_ne_zero_of_pos"),
                level_params: vec![],
                type_: natcast_ne_zero_type(&c),
                value: natcast_ne_zero_value(&c),
            })?;
        }

        if self
            .get_const(&Name::from_string("BoolAnalysis.Expect_const_one"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.Expect_const_one"),
                level_params: vec![],
                type_: expect_const_one_type(&c),
                value: expect_const_one_value(&c),
            })?;
        }

        if self
            .get_const(&Name::from_string("BoolAnalysis.chi_self_inner_eq_one"))
            .is_none()
        {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.chi_self_inner_eq_one"),
                level_params: vec![],
                type_: chi_self_inner_one_type(&c),
                value: chi_self_inner_one_value(&c),
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_expect_one_theorems()
            .expect("register_expect_one_theorems");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&Name::from_string(name)),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(name))
                .expect("deps")
                .is_empty(),
            "{name}'s transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_one_le_two_pow_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Nat.one_le_two_pow");
    }

    #[test]
    fn test_natcast_ne_zero_of_pos_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Rat.natCast_ne_zero_of_pos");
    }

    #[test]
    fn test_expect_const_one_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.Expect_const_one");
    }

    /// THE closed diagonal orthonormality: `E[χ_S·χ_S] = 1` as a genuine
    /// kernel-checked constructive Theorem with empty admitted-axiom closure.
    #[test]
    fn test_chi_self_inner_eq_one_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.chi_self_inner_eq_one");
    }
}
