// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.ofNat_mul_subNatNat : ∀ j p q : Nat,
//!     Eq Int (Int.mul (Int.ofNat j) (Int.subNatNat p q))
//!            (Int.subNatNat (Nat.mul j p) (Nat.mul j q))`.
//!
//! Scaling a clamped difference `p - q` by a non-negative integer `ofNat j`
//! distributes through `Int.subNatNat`:
//! `j*(p - q) = (j*p) - (j*q)`. This is the multiplication-over-truncated-
//! subtraction lemma that was the documented blocker for a constructive
//! `Int.left_distrib`: the mixed-sign `Int.add b c` branches normalize to
//! `Int.subNatNat`, and this lemma lets `Int.mul (ofNat j) ·` cross that
//! `subNatNat` to distribute over an honest two-term sum.
//!
//! # Proof sketch
//!
//! `Int.subNatNat` satisfies (constructively, via the registered lemmas):
//!
//! ```text
//! subNatNat p 0          = ofNat p           (iota; subNatNat_zero_right)
//! subNatNat 0 (succ q)   = negSucc q         (subNatNat_zero_succ)
//! subNatNat (succ p) (succ q) = subNatNat p q (subNatNat_succ_succ)
//! ```
//!
//! and `Int.mul` (reducible Definition):
//!
//! ```text
//! mul (ofNat j) (ofNat r)   = ofNat    (Nat.mul j r)
//! mul (ofNat j) (negSucc r) = negOfNat (Nat.mul j (succ r))
//! ```
//!
//! `Nat.add`/`Nat.mul` recurse on their SECOND argument, so
//! `Nat.mul j 0 ι→ 0` and `Nat.mul j (succ p) ι→ Nat.add (Nat.mul j p) j`
//! definitionally.
//!
//! Prove `P(p,q) := Eq (mul (ofNat j) (subNatNat p q))
//!                     (subNatNat (Nat.mul j p) (Nat.mul j q))` by nested
//! `@Nat.rec.{0}` — OUTER on `q` (motive `λ qt => ∀ pt, P(pt, qt)`), INNER on
//! `p` in the successor-`q` branch:
//!
//! - **q = 0** (`∀ p, P(p, 0)`): `subNatNat p 0 ι→ ofNat p`, so LHS
//!   `ι→ ofNat (Nat.mul j p)`. `Nat.mul j 0 ι→ 0`, so RHS
//!   `subNatNat (Nat.mul j p) 0 ι→ ofNat (Nat.mul j p)`. Closes by
//!   `λ p => @Eq.refl.{1} Int (ofNat (Nat.mul j p))`.
//! - **q = succ q'**, outer IH `ih_q : ∀ p, P(p, q')`. Induct on `p`:
//!   - **p = 0**: rewrite LHS `subNatNat 0 (succ q')` to `negSucc q'` with
//!     `subNatNat_zero_succ q'` (then `mul (ofNat j) (negSucc q')
//!     ι→ negOfNat (Nat.mul j (succ q'))`), and rewrite RHS
//!     `subNatNat (Nat.mul j 0) (Nat.mul j (succ q'))
//!     ≡ subNatNat 0 (Nat.mul j (succ q'))` to `negOfNat (Nat.mul j (succ q'))`
//!     with `subNatNat_zero_left`. `Eq.trans` of the two glues them.
//!   - **p = succ p'** (inner IH unused): chain
//!     `e1 := congrArg (mul (ofNat j)) (subNatNat_succ_succ p' q')`,
//!     `e2 := ih_q p'` (`mul (ofNat j) (subNatNat p' q')
//!            = subNatNat (Nat.mul j p') (Nat.mul j q')`), and
//!     `e3 := Eq.symm (subNatNat_add_add (Nat.mul j p') (Nat.mul j q') j)`
//!     (whose RHS `subNatNat (Nat.add (Nat.mul j p') j)
//!     (Nat.add (Nat.mul j q') j)` is defn-equal to
//!     `subNatNat (Nat.mul j (succ p')) (Nat.mul j (succ q'))`) via `Eq.trans`.
//!
//! # Axiom closure
//!
//! The proof mentions only kernel machinery / constructors / reducible
//! Definitions and the constructive `Declaration::Theorem`s
//! `Int.subNatNat_succ_succ`, `Int.subNatNat_zero_succ`,
//! `Int.subNatNat_zero_left`, `Int.subNatNat_add_add` (all #3604). None are
//! `Declaration::Axiom`, so `env.axiom_deps("Int.ofNat_mul_subNatNat")` is
//! empty and the proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling proofs:
//! - `algebra_int_negsucc_mul_sub_nat_nat_proof.rs` (negSucc analogue).
//! - `algebra_int_left_distrib_proof.rs` (consumer).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntOfNatMulSubNatNatConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_rec: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_neg_of_nat: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    snn_succ_succ: Expr,
    snn_zero_succ: Expr,
    snn_zero_left: Expr,
    snn_add_add: Expr,
}

impl IntOfNatMulSubNatNatConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![type1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            snn_succ_succ: Expr::const_(Name::from_string("Int.subNatNat_succ_succ"), vec![]),
            snn_zero_succ: Expr::const_(Name::from_string("Int.subNatNat_zero_succ"), vec![]),
            snn_zero_left: Expr::const_(Name::from_string("Int.subNatNat_zero_left"), vec![]),
            snn_add_add: Expr::const_(Name::from_string("Int.subNatNat_add_add"), vec![]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.int_mul.clone(), a), b)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn neg_of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_of_nat.clone(), n)
    }

    fn sub_nat_nat(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.int_sub_nat_nat.clone(), m), n)
    }

    fn nmul(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_mul.clone(), x), y)
    }

    fn nadd(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), x), y)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn eq_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }

    fn refl_int(&self, t: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.int_type.clone(), t])
    }

    fn symm_int(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int_type.clone(), a, b, h])
    }

    fn trans_int(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.int_type.clone(), x, y, z, h1, h2],
        )
    }

    /// `congrArg Int Int a1 a2 f h : Eq Int (f a1) (f a2)`.
    fn congr_arg_int(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int_type.clone(), self.int_type.clone(), a1, a2, f, h],
        )
    }

    fn snn_succ_succ(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.snn_succ_succ.clone(), [m, n])
    }

    fn snn_zero_succ(&self, n: Expr) -> Expr {
        Expr::app(self.snn_zero_succ.clone(), n)
    }

    fn snn_zero_left(&self, n: Expr) -> Expr {
        Expr::app(self.snn_zero_left.clone(), n)
    }

    fn snn_add_add(&self, a: Expr, b: Expr, d: Expr) -> Expr {
        Expr::apps(self.snn_add_add.clone(), [a, b, d])
    }

    /// `P(p, q) := Eq (mul (ofNat j) (subNatNat p q)) (subNatNat (j*p) (j*q))`.
    fn prop(&self, j: &Expr, p: Expr, q: Expr) -> Expr {
        let lhs = self.mul(
            self.of_nat(j.clone()),
            self.sub_nat_nat(p.clone(), q.clone()),
        );
        let rhs = self.sub_nat_nat(self.nmul(j.clone(), p), self.nmul(j.clone(), q));
        self.eq_int(lhs, rhs)
    }

    /// `λ x : Int => mul (ofNat j) x` — the congruence target for `e1`.
    fn mul_ofnat_fn(&self, parent: &EnvDeclBuilder, j: &Expr) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = fb.fresh_local(self.int_type.clone());
        let body = self.mul(self.of_nat(j.clone()), x);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
        fb.finish_child(lam)
    }
}

/// Build the closed Pi type.
fn build_type(c: &IntOfNatMulSubNatNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (j_id, j) = b.fresh_local(c.nat_type.clone());
    let (p_id, p) = b.fresh_local(c.nat_type.clone());
    let (q_id, q) = b.fresh_local(c.nat_type.clone());
    let concl = c.prop(&j, p, q);
    let ty = b.mk_pi(q_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty = b.mk_pi(p_id, BinderInfo::Default, c.nat_type.clone(), ty);
    let ty = b.mk_pi(j_id, BinderInfo::Default, c.nat_type.clone(), ty);
    b.finish(ty)
}

/// Outer motive (induction on q): `λ qt : Nat => ∀ pt : Nat, P(pt, qt)`.
fn build_outer_motive(c: &IntOfNatMulSubNatNatConsts, parent: &EnvDeclBuilder, j: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (qt_id, qt) = mb.fresh_local(c.nat_type.clone());
    let (pt_id, pt) = mb.fresh_local(c.nat_type.clone());
    let body = c.prop(j, pt, qt.clone());
    let pi = mb.mk_pi(pt_id, BinderInfo::Default, c.nat_type.clone(), body);
    let lam = mb.mk_lam(qt_id, BinderInfo::Default, c.nat_type.clone(), pi);
    mb.finish_child(lam)
}

/// Outer base (q = 0): `λ p : Nat => @Eq.refl.{1} Int (ofNat (Nat.mul j p))`.
fn build_outer_base(c: &IntOfNatMulSubNatNatConsts, parent: &EnvDeclBuilder, j: &Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (p_id, p) = bb.fresh_local(c.nat_type.clone());
    let refl = c.refl_int(c.of_nat(c.nmul(j.clone(), p.clone())));
    let lam = bb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), refl);
    bb.finish_child(lam)
}

/// Outer step (q = succ q'): `λ q' (ih_q : ∀p, P(p,q')) => @Nat.rec.{0} ... p`.
fn build_outer_step(c: &IntOfNatMulSubNatNatConsts, parent: &EnvDeclBuilder, j: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (qp_id, qp) = sb.fresh_local(c.nat_type.clone());

    // ih_q : ∀ pt, P(pt, q')
    let ih_q_ty = {
        let mut ib = EnvDeclBuilder::child_of(&sb);
        let (pt_id, pt) = ib.fresh_local(c.nat_type.clone());
        let body = c.prop(j, pt, qp.clone());
        let pi = ib.mk_pi(pt_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(pi)
    };
    let (ihq_id, ih_q) = sb.fresh_local(ih_q_ty.clone());

    let succ_qp = c.succ(qp.clone());

    // Inner motive (induction on p): `λ pt : Nat => P(pt, succ q')`.
    let inner_motive = {
        let mut mb = EnvDeclBuilder::child_of(&sb);
        let (pt_id, pt) = mb.fresh_local(c.nat_type.clone());
        let body = c.prop(j, pt, succ_qp.clone());
        let lam = mb.mk_lam(pt_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // Inner base (p = 0): P(0, succ q').
    //   LHS  = mul (ofNat j) (subNatNat 0 (succ q'))
    //   RHS  = subNatNat (Nat.mul j 0) (Nat.mul j (succ q'))
    //         ≡ subNatNat 0 (Nat.mul j (succ q'))
    //   e_lhs := congrArg (mul (ofNat j)) (subNatNat_zero_succ q')
    //          : LHS = mul (ofNat j) (negSucc q')  [≡ negOfNat (j*(succ q'))]
    //   e_rhs := Eq.symm (subNatNat_zero_left (Nat.mul j (succ q')))
    //          : negOfNat (j*(succ q')) = subNatNat 0 (j*(succ q'))
    //   Eq.trans e_lhs e_rhs.
    let inner_base = {
        let lhs0 = c.mul(
            c.of_nat(j.clone()),
            c.sub_nat_nat(c.nat_zero.clone(), succ_qp.clone()),
        );
        let mid = c.mul(c.of_nat(j.clone()), c.neg_succ(qp.clone()));
        let prod = c.nmul(j.clone(), succ_qp.clone());
        let rhs0 = c.sub_nat_nat(c.nat_zero.clone(), prod.clone());

        let f = c.mul_ofnat_fn(&sb, j);
        let e_lhs = c.congr_arg_int(
            c.sub_nat_nat(c.nat_zero.clone(), succ_qp.clone()),
            c.neg_succ(qp.clone()),
            f,
            c.snn_zero_succ(qp.clone()),
        );
        let e_rhs = c.symm_int(
            rhs0.clone(),
            c.neg_of_nat(prod.clone()),
            c.snn_zero_left(prod),
        );
        c.trans_int(lhs0, mid, rhs0, e_lhs, e_rhs)
    };

    // Inner step (p = succ p'): P(succ p', succ q'). Inner IH unused.
    let inner_step = {
        let mut isb = EnvDeclBuilder::child_of(&sb);
        let (pp_id, pp) = isb.fresh_local(c.nat_type.clone());
        let inner_ih_ty = c.prop(j, pp.clone(), succ_qp.clone());
        let (iih_id, _iih) = isb.fresh_local(inner_ih_ty.clone());

        let succ_pp = c.succ(pp.clone());

        // A = mul (ofNat j) (subNatNat (succ p') (succ q'))
        let a = c.mul(
            c.of_nat(j.clone()),
            c.sub_nat_nat(succ_pp.clone(), succ_qp.clone()),
        );
        // B = mul (ofNat j) (subNatNat p' q')
        let bexpr = c.mul(c.of_nat(j.clone()), c.sub_nat_nat(pp.clone(), qp.clone()));
        // Cexpr = subNatNat (j*p') (j*q')
        let j_pp = c.nmul(j.clone(), pp.clone());
        let j_qp = c.nmul(j.clone(), qp.clone());
        let cexpr = c.sub_nat_nat(j_pp.clone(), j_qp.clone());
        // D = subNatNat (Nat.add (j*p') j) (Nat.add (j*q') j)  [≡ goal RHS]
        let dexpr = c.sub_nat_nat(
            c.nadd(j_pp.clone(), j.clone()),
            c.nadd(j_qp.clone(), j.clone()),
        );

        // e1 := congrArg (mul (ofNat j)) (subNatNat_succ_succ p' q')
        let f = c.mul_ofnat_fn(&isb, j);
        let e1 = c.congr_arg_int(
            c.sub_nat_nat(succ_pp.clone(), succ_qp.clone()),
            c.sub_nat_nat(pp.clone(), qp.clone()),
            f,
            c.snn_succ_succ(pp.clone(), qp.clone()),
        );
        // e2 := ih_q p'
        let e2 = Expr::app(ih_q.clone(), pp.clone());
        // t1 := Eq.trans A B Cexpr e1 e2
        let t1 = c.trans_int(a.clone(), bexpr, cexpr.clone(), e1, e2);
        // e3 := Eq.symm (subNatNat_add_add (j*p') (j*q') j)
        let e3 = c.symm_int(
            dexpr.clone(),
            cexpr.clone(),
            c.snn_add_add(j_pp, j_qp, j.clone()),
        );
        // t2 := Eq.trans A Cexpr D t1 e3
        let t2 = c.trans_int(a, cexpr, dexpr, t1, e3);

        let lam_iih = isb.mk_lam(iih_id, BinderInfo::Default, inner_ih_ty, t2);
        let lam_pp = isb.mk_lam(pp_id, BinderInfo::Default, c.nat_type.clone(), lam_iih);
        isb.finish_child(lam_pp)
    };

    // λ p => @Nat.rec.{0} inner_motive inner_base inner_step p
    let inner_lam = {
        let mut pb = EnvDeclBuilder::child_of(&sb);
        let (p_id, p) = pb.fresh_local(c.nat_type.clone());
        let rec_app = Expr::apps(c.nat_rec.clone(), [inner_motive, inner_base, inner_step, p]);
        let lam = pb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        pb.finish_child(lam)
    };

    let lam_ihq = sb.mk_lam(ihq_id, BinderInfo::Default, ih_q_ty, inner_lam);
    let lam_qp = sb.mk_lam(qp_id, BinderInfo::Default, c.nat_type.clone(), lam_ihq);
    sb.finish_child(lam_qp)
}

/// Body: `λ (j p q : Nat) => (@Nat.rec.{0} outer_motive outer_base outer_step q) p`.
fn build_value(c: &IntOfNatMulSubNatNatConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (j_id, j) = vb.fresh_local(c.nat_type.clone());
    let (p_id, p) = vb.fresh_local(c.nat_type.clone());
    let (q_id, q) = vb.fresh_local(c.nat_type.clone());

    let outer_motive = build_outer_motive(c, &vb, &j);
    let outer_base = build_outer_base(c, &vb, &j);
    let outer_step = build_outer_step(c, &vb, &j);

    let rec_q = Expr::apps(c.nat_rec.clone(), [outer_motive, outer_base, outer_step, q]);
    let body = Expr::app(rec_q, p);
    let val = vb.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), body);
    let val = vb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = vb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Int.ofNat_mul_subNatNat` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.negOfNat`, `Int.mul`, `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// REQUIRES: `Int.subNatNat_succ_succ`, `Int.subNatNat_zero_succ`,
    ///           `Int.subNatNat_zero_left`, `Int.subNatNat_add_add` are
    ///           registered as constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.ofNat_mul_subNatNat` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_ofnat_mul_sub_nat_nat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.ofNat_mul_subNatNat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;
        self.register_int_sub_nat_nat_zero_succ_proof()?;
        self.register_int_sub_nat_nat_zero_left_proof()?;
        self.register_int_sub_nat_nat_add_add_proof()?;

        let c = IntOfNatMulSubNatNatConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Nat.rec.{0}` (outer on `q`, inner on `p`). The `q = 0` branch
        // closes by `λ p => @Eq.refl.{1} Int (ofNat (Nat.mul j p))`. The
        // `p = 0` corner of the successor-`q` branch glues
        // `Int.subNatNat_zero_succ` (LHS) and `Int.subNatNat_zero_left` (RHS)
        // via `Eq.trans`; the `p = succ p'` corner chains
        //   congrArg (mul (ofNat j)) (Int.subNatNat_succ_succ p' q')
        //   ih_q p'
        //   Eq.symm (Int.subNatNat_add_add (j*p') (j*q') j)
        // via `Eq.trans`. No `sorry`, no self-reference, no domain-axiom
        // dependency (all four feeder `subNatNat` lemmas are constructive
        // #3604).
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
    use crate::env::{ConstantKind, ProofQuality};

    #[test]
    fn test_int_ofnat_mul_sub_nat_nat_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_ofnat_mul_sub_nat_nat_proof()
            .expect("first registration");
        env.register_int_ofnat_mul_sub_nat_nat_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.ofNat_mul_subNatNat"))
            .expect("Int.ofNat_mul_subNatNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_ofnat_mul_sub_nat_nat_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_ofnat_mul_sub_nat_nat_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.ofNat_mul_subNatNat"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        // Peel three outer λ (j, p, q); body is `(Nat.rec ... q) p`.
        let mut body = value.clone();
        for _ in 0..3 {
            body = match body.kind() {
                ExprKind::Lam(_, _, inner) => (**inner).clone(),
                k => panic!("expected outer λ, got {:?}", k),
            };
        }
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Nat.rec",
                "proof root must be Nat.rec, got Const({:?})",
                n.to_string()
            ),
            k => panic!("expected Const(Nat.rec, ..) at proof root, got {:?}", k),
        }
    }

    #[test]
    fn test_int_ofnat_mul_sub_nat_nat_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_ofnat_mul_sub_nat_nat_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.ofNat_mul_subNatNat"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.ofNat_mul_subNatNat must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_ofnat_mul_sub_nat_nat_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_ofnat_mul_sub_nat_nat_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.ofNat_mul_subNatNat"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.ofNat_mul_subNatNat must be Constructive, got {:?}",
            quality
        );
    }
}
