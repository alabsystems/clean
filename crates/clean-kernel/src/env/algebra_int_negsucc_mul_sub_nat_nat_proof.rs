// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.negSucc_mul_subNatNat : ∀ j p q : Nat,
//!     Eq Int (Int.mul (Int.negSucc j) (Int.subNatNat p q))
//!            (Int.subNatNat (Nat.mul (Nat.succ j) q) (Nat.mul (Nat.succ j) p))`.
//!
//! Scaling a clamped difference `p - q` by the negative integer
//! `negSucc j = -(j+1)` distributes through `Int.subNatNat` with a sign flip:
//! `-(j+1)*(p - q) = (j+1)*q - (j+1)*p`. The negative companion of
//! `Int.ofNat_mul_subNatNat`; together they let `Int.left_distrib` push a
//! multiplication across the mixed-sign `Int.add b c` (which normalizes to
//! `Int.subNatNat`).
//!
//! # Proof sketch
//!
//! `Int.mul` (reducible Definition) on a `negSucc` left factor:
//!
//! ```text
//! mul (negSucc j) (ofNat r)   = negOfNat (Nat.mul (succ j) r)
//! mul (negSucc j) (negSucc r) = ofNat    (Nat.mul (succ j) (succ r))
//! ```
//!
//! Prove `Q(p,q) := Eq (mul (negSucc j) (subNatNat p q))
//!                     (subNatNat (Nat.mul (succ j) q) (Nat.mul (succ j) p))`
//! by nested `@Nat.rec.{0}` — OUTER on `q` (motive `λ qt => ∀ pt, Q(pt, qt)`),
//! INNER on `p` in the successor-`q` branch:
//!
//! - **q = 0** (`∀ p, Q(p, 0)`): `subNatNat p 0 ι→ ofNat p`, so LHS
//!   `ι→ negOfNat (Nat.mul (succ j) p)`. `Nat.mul (succ j) 0 ι→ 0`, so RHS
//!   `subNatNat 0 (Nat.mul (succ j) p)`. Discharged by
//!   `λ p => Eq.symm (subNatNat_zero_left (Nat.mul (succ j) p))`.
//! - **q = succ q'**, outer IH `ih_q : ∀ p, Q(p, q')`. Induct on `p`:
//!   - **p = 0**: rewrite LHS `subNatNat 0 (succ q')` to `negSucc q'` with
//!     `subNatNat_zero_succ q'`; then `mul (negSucc j) (negSucc q')
//!     ι→ ofNat (Nat.mul (succ j) (succ q'))`, which is defn-equal to the RHS
//!     `subNatNat (Nat.mul (succ j) (succ q')) (Nat.mul (succ j) 0)` (the
//!     second index reduces to `0` and `subNatNat r 0 ι→ ofNat r`). So the
//!     single `congrArg` already has the goal type.
//!   - **p = succ p'** (inner IH unused): chain
//!     `e1 := congrArg (mul (negSucc j)) (subNatNat_succ_succ p' q')`,
//!     `e2 := ih_q p'`, and
//!     `e3 := Eq.symm (subNatNat_add_add (Nat.mul (succ j) q')
//!            (Nat.mul (succ j) p') (succ j))` via `Eq.trans`.
//!
//! # Axiom closure
//!
//! Mentions only kernel machinery / constructors / reducible Definitions and
//! the constructive `Declaration::Theorem`s `Int.subNatNat_succ_succ`,
//! `Int.subNatNat_zero_succ`, `Int.subNatNat_zero_left`,
//! `Int.subNatNat_add_add` (#3604). `env.axiom_deps("Int.negSucc_mul_subNatNat")`
//! is empty; the proof quality is `ProofQuality::Constructive`.
//!
//! Tracks #3604. Sibling: `algebra_int_ofnat_mul_sub_nat_nat_proof.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntNegSuccMulSubNatNatConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_rec: Expr,
    int_mul: Expr,
    int_neg_succ: Expr,
    int_neg_of_nat: Expr,
    int_sub_nat_nat: Expr,
    eq_const: Expr,
    #[cfg(test)]
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    snn_succ_succ: Expr,
    snn_zero_succ: Expr,
    snn_zero_left: Expr,
    snn_add_add: Expr,
}

impl IntNegSuccMulSubNatNatConsts {
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
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_neg_of_nat: Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            #[cfg(test)]
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

    /// `Q(p,q) := Eq (mul (negSucc j) (subNatNat p q))
    ///               (subNatNat (Nat.mul (succ j) q) (Nat.mul (succ j) p))`.
    fn prop(&self, sj: &Expr, j: &Expr, p: Expr, q: Expr) -> Expr {
        let lhs = self.mul(
            self.neg_succ(j.clone()),
            self.sub_nat_nat(p.clone(), q.clone()),
        );
        let rhs = self.sub_nat_nat(self.nmul(sj.clone(), q), self.nmul(sj.clone(), p));
        self.eq_int(lhs, rhs)
    }

    /// `λ x : Int => mul (negSucc j) x`.
    fn mul_negsucc_fn(&self, parent: &EnvDeclBuilder, j: &Expr) -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = fb.fresh_local(self.int_type.clone());
        let body = self.mul(self.neg_succ(j.clone()), x);
        let lam = fb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
        fb.finish_child(lam)
    }
}

/// Build the closed Pi type.
fn build_type(c: &IntNegSuccMulSubNatNatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (j_id, j) = b.fresh_local(c.nat_type.clone());
    let (p_id, p) = b.fresh_local(c.nat_type.clone());
    let (q_id, q) = b.fresh_local(c.nat_type.clone());
    let sj = c.succ(j.clone());
    let concl = c.prop(&sj, &j, p, q);
    let ty = b.mk_pi(q_id, BinderInfo::Default, c.nat_type.clone(), concl);
    let ty = b.mk_pi(p_id, BinderInfo::Default, c.nat_type.clone(), ty);
    let ty = b.mk_pi(j_id, BinderInfo::Default, c.nat_type.clone(), ty);
    b.finish(ty)
}

/// Outer motive (induction on q): `λ qt : Nat => ∀ pt : Nat, Q(pt, qt)`.
fn build_outer_motive(
    c: &IntNegSuccMulSubNatNatConsts,
    parent: &EnvDeclBuilder,
    sj: &Expr,
    j: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (qt_id, qt) = mb.fresh_local(c.nat_type.clone());
    let (pt_id, pt) = mb.fresh_local(c.nat_type.clone());
    let body = c.prop(sj, j, pt, qt.clone());
    let pi = mb.mk_pi(pt_id, BinderInfo::Default, c.nat_type.clone(), body);
    let lam = mb.mk_lam(qt_id, BinderInfo::Default, c.nat_type.clone(), pi);
    mb.finish_child(lam)
}

/// Outer base (q = 0):
/// `λ p : Nat => Eq.symm (subNatNat_zero_left (Nat.mul (succ j) p))`.
fn build_outer_base(c: &IntNegSuccMulSubNatNatConsts, parent: &EnvDeclBuilder, sj: &Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (p_id, p) = bb.fresh_local(c.nat_type.clone());
    let prod = c.nmul(sj.clone(), p.clone());
    // Eq.symm Int (subNatNat 0 prod) (negOfNat prod) (subNatNat_zero_left prod)
    //   : Eq (negOfNat prod) (subNatNat 0 prod)
    let proof = c.symm_int(
        c.sub_nat_nat(c.nat_zero.clone(), prod.clone()),
        c.neg_of_nat(prod.clone()),
        c.snn_zero_left(prod),
    );
    let lam = bb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), proof);
    bb.finish_child(lam)
}

/// Outer step (q = succ q').
fn build_outer_step(
    c: &IntNegSuccMulSubNatNatConsts,
    parent: &EnvDeclBuilder,
    sj: &Expr,
    j: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (qp_id, qp) = sb.fresh_local(c.nat_type.clone());

    // ih_q : ∀ pt, Q(pt, q')
    let ih_q_ty = {
        let mut ib = EnvDeclBuilder::child_of(&sb);
        let (pt_id, pt) = ib.fresh_local(c.nat_type.clone());
        let body = c.prop(sj, j, pt, qp.clone());
        let pi = ib.mk_pi(pt_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(pi)
    };
    let (ihq_id, ih_q) = sb.fresh_local(ih_q_ty.clone());

    let succ_qp = c.succ(qp.clone());

    // Inner motive: `λ pt : Nat => Q(pt, succ q')`.
    let inner_motive = {
        let mut mb = EnvDeclBuilder::child_of(&sb);
        let (pt_id, pt) = mb.fresh_local(c.nat_type.clone());
        let body = c.prop(sj, j, pt, succ_qp.clone());
        let lam = mb.mk_lam(pt_id, BinderInfo::Default, c.nat_type.clone(), body);
        mb.finish_child(lam)
    };

    // Inner base (p = 0): Q(0, succ q').
    //   e := congrArg (mul (negSucc j)) (subNatNat_zero_succ q')
    //      : mul (negSucc j) (subNatNat 0 (succ q')) = mul (negSucc j) (negSucc q')
    //   mul (negSucc j) (negSucc q') ≡ ofNat ((succ j)*(succ q')) ≡ goal RHS
    //   (RHS = subNatNat ((succ j)*(succ q')) ((succ j)*0) ≡ ofNat ((succ j)*(succ q'))).
    let inner_base = {
        let f = c.mul_negsucc_fn(&sb, j);
        c.congr_arg_int(
            c.sub_nat_nat(c.nat_zero.clone(), succ_qp.clone()),
            c.neg_succ(qp.clone()),
            f,
            c.snn_zero_succ(qp.clone()),
        )
    };

    // Inner step (p = succ p'): Q(succ p', succ q'). Inner IH unused.
    let inner_step = {
        let mut isb = EnvDeclBuilder::child_of(&sb);
        let (pp_id, pp) = isb.fresh_local(c.nat_type.clone());
        let inner_ih_ty = c.prop(sj, j, pp.clone(), succ_qp.clone());
        let (iih_id, _iih) = isb.fresh_local(inner_ih_ty.clone());

        let succ_pp = c.succ(pp.clone());

        // A = mul (negSucc j) (subNatNat (succ p') (succ q'))
        let a = c.mul(
            c.neg_succ(j.clone()),
            c.sub_nat_nat(succ_pp.clone(), succ_qp.clone()),
        );
        // B = mul (negSucc j) (subNatNat p' q')
        let bexpr = c.mul(c.neg_succ(j.clone()), c.sub_nat_nat(pp.clone(), qp.clone()));
        // Cexpr = subNatNat ((succ j)*q') ((succ j)*p')
        let sj_qp = c.nmul(sj.clone(), qp.clone());
        let sj_pp = c.nmul(sj.clone(), pp.clone());
        let cexpr = c.sub_nat_nat(sj_qp.clone(), sj_pp.clone());
        // D = subNatNat (Nat.add ((succ j)*q') (succ j)) (Nat.add ((succ j)*p') (succ j))
        //   ≡ subNatNat ((succ j)*(succ q')) ((succ j)*(succ p')) = goal RHS
        let dexpr = c.sub_nat_nat(
            c.nadd(sj_qp.clone(), sj.clone()),
            c.nadd(sj_pp.clone(), sj.clone()),
        );

        let f = c.mul_negsucc_fn(&isb, j);
        let e1 = c.congr_arg_int(
            c.sub_nat_nat(succ_pp.clone(), succ_qp.clone()),
            c.sub_nat_nat(pp.clone(), qp.clone()),
            f,
            c.snn_succ_succ(pp.clone(), qp.clone()),
        );
        let e2 = Expr::app(ih_q.clone(), pp.clone());
        let t1 = c.trans_int(a.clone(), bexpr, cexpr.clone(), e1, e2);
        let e3 = c.symm_int(
            dexpr.clone(),
            cexpr.clone(),
            c.snn_add_add(sj_qp, sj_pp, sj.clone()),
        );
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
fn build_value(c: &IntNegSuccMulSubNatNatConsts) -> Expr {
    let mut vb = EnvDeclBuilder::new();
    let (j_id, j) = vb.fresh_local(c.nat_type.clone());
    let (p_id, p) = vb.fresh_local(c.nat_type.clone());
    let (q_id, q) = vb.fresh_local(c.nat_type.clone());

    let sj = c.succ(j.clone());
    let outer_motive = build_outer_motive(c, &vb, &sj, &j);
    let outer_base = build_outer_base(c, &vb, &sj);
    let outer_step = build_outer_step(c, &vb, &sj, &j);

    let rec_q = Expr::apps(c.nat_rec.clone(), [outer_motive, outer_base, outer_step, q]);
    let body = Expr::app(rec_q, p);
    let val = vb.mk_lam(q_id, BinderInfo::Default, c.nat_type.clone(), body);
    let val = vb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), val);
    let val = vb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), val);
    vb.finish(val)
}

impl Environment {
    /// Register `Int.negSucc_mul_subNatNat` as a kernel-checked
    /// `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_arith()` has registered `Int`, `Int.negSucc`,
    ///           `Int.negOfNat`, `Int.mul`, `Int.subNatNat`.
    /// REQUIRES: `self.init_nat()` has registered `Nat`, `Nat.zero`,
    ///           `Nat.succ`, `Nat.add`, `Nat.mul`, `Nat.rec`.
    /// REQUIRES: `self.init_eq()` has registered `Eq`, `Eq.refl`, `Eq.symm`,
    ///           `Eq.trans`, `congrArg`.
    /// REQUIRES: `Int.subNatNat_succ_succ`, `Int.subNatNat_zero_succ`,
    ///           `Int.subNatNat_zero_left`, `Int.subNatNat_add_add` are
    ///           registered as constructive `Declaration::Theorem`s.
    /// ENSURES: On success, `Int.negSucc_mul_subNatNat` is a
    ///          `Declaration::Theorem` with `proof_quality == Constructive`.
    /// ENSURES: Idempotent.
    pub(crate) fn register_int_negsucc_mul_sub_nat_nat_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.negSucc_mul_subNatNat");
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

        let c = IntNegSuccMulSubNatNatConsts::new();
        let type_ = build_type(&c);
        let value = build_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (#3604). Nested
        // `@Nat.rec.{0}` (outer on `q`, inner on `p`); negative companion of
        // `Int.ofNat_mul_subNatNat`. The `q = 0` branch closes by
        // `λ p => Eq.symm (Int.subNatNat_zero_left (Nat.mul (succ j) p))`. The
        // `p = 0` corner of the successor-`q` branch is a single
        // `congrArg (mul (negSucc j)) (Int.subNatNat_zero_succ q')` (the RHS
        // reduces definitionally to `ofNat ((succ j)*(succ q'))`). The
        // `p = succ p'` corner chains
        //   congrArg (mul (negSucc j)) (Int.subNatNat_succ_succ p' q')
        //   ih_q p'
        //   Eq.symm (Int.subNatNat_add_add ((succ j)*q') ((succ j)*p') (succ j))
        // via `Eq.trans`. No `sorry`, no self-reference, no domain-axiom
        // dependency (all four feeder lemmas are constructive #3604).
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
    fn test_int_negsucc_mul_sub_nat_nat_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_negsucc_mul_sub_nat_nat_proof()
            .expect("first registration");
        env.register_int_negsucc_mul_sub_nat_nat_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.negSucc_mul_subNatNat"))
            .expect("Int.negSucc_mul_subNatNat should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_negsucc_mul_sub_nat_nat_proof_uses_nat_rec() {
        use crate::expr::ExprKind;
        let mut env = Environment::new();
        env.register_int_negsucc_mul_sub_nat_nat_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.negSucc_mul_subNatNat"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
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
    fn test_int_negsucc_mul_sub_nat_nat_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_negsucc_mul_sub_nat_nat_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.negSucc_mul_subNatNat"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.negSucc_mul_subNatNat must have empty axiom closure, got {:?}",
            domain_deps
        );
    }

    #[test]
    fn test_int_negsucc_mul_sub_nat_nat_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_negsucc_mul_sub_nat_nat_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.negSucc_mul_subNatNat"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.negSucc_mul_subNatNat must be Constructive, got {:?}",
            quality
        );
    }
}
