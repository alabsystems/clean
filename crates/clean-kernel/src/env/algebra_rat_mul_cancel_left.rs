// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational positive-left multiplicative cancellation for `≤`.
//!
//! # Why this module exists
//!
//! The verified per-coordinate squared dual-HC chain
//! (`designs/2026-06-12-kkl-endgame-worked-chain.md`) closes with the algebraic
//! step
//!
//! ```text
//!   2^{4n-4}·W²·(W²)  ≤  2^{4n-4}·W²·(16·Inf³)   ⟹   W² ≤ 16·Inf³
//! ```
//!
//! i.e. cancellation of a STRICTLY POSITIVE common left factor across a `≤`.
//! Only the FORWARD product-monotonicity lemmas (`Rat.mul_le_mul_of_nonneg_*`,
//! the strict `Rat.mul_lt_mul_of_pos_left`) exist on the branch; the cancelling
//! (reverse) direction over `Rat` is absent. This module lands it as a clean,
//! reusable, general-purpose `Rat` lemma:
//!
//! ```text
//! Rat.le_of_mul_le_mul_left_pos :
//!   ∀ (a b c : Rat), Rat.lt Rat.zero c → Rat.le (c·a) (c·b) → Rat.le a b
//! ```
//!
//! # Proof shape (constructive, no subtraction algebra)
//!
//! 1. `hne : c = 0 → False`  := `Rat.ne_zero_of_pos c hc`.
//! 2. `h0c : 0 ≤ c`          := `And.left (Iff.mp (Rat.lt_iff_le_not_le 0 c) hc)`.
//! 3. case-split `Rat.le_total a b : Or (a≤b) (b≤a)` via `@Or.rec` to the Prop
//!    goal `a ≤ b`:
//!    - **left** `hab : a ≤ b` — that IS the goal.
//!    - **right** `hba : b ≤ a` — combined with the hypothesis it pins `a = b`:
//!      * `hcb_ca : c·b ≤ c·a` := `Rat.mul_le_mul_of_nonneg_left c b a hba h0c`.
//!      * `heq : c·a = c·b`    := `Rat.le_antisymm (c·a) (c·b) hcab hcb_ca`.
//!      * cancel `c` on the left to get `a = b`:
//!          `a = 1·a = (inv c·c)·a = inv c·(c·a) = inv c·(c·b) = (inv c·c)·b
//!             = 1·b = b`,
//!        where `inv c·c = c·inv c = 1` (`Rat.mul_comm` + `Rat.mul_inv_cancel`),
//!        the middle `inv c·(c·a) = inv c·(c·b)` is `congrArg (inv c·_) heq`, and
//!        the regroupings are `Rat.mul_assoc` / `Rat.one_mul`.
//!      * `a ≤ b` := `Eq.subst (fun t => a ≤ t) heq_ab (Rat.le_refl a)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (every leaf — `Rat.ne_zero_of_pos`, `Rat.lt_iff_le_not_le`,
//! `Rat.le_total`, `Rat.le_antisymm`, `Rat.mul_le_mul_of_nonneg_left`,
//! `Rat.mul_inv_cancel`, `Rat.mul_assoc`/`_comm`/`one_mul`, `Rat.le_refl`,
//! `Iff.mp`/`And.left`/`Or.rec`/`Eq` built-ins — is foundational-only). NO
//! `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.le_of_mul_le_mul_left_pos`.
struct CancelLeftConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    ne_zero_of_pos: Expr,
    lt_iff_le_not_le: Expr,
    le_total: Expr,
    le_antisymm: Expr,
    le_refl: Expr,
    mul_le_left: Expr,
    mul_inv_cancel: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    one_mul: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    or_c: Expr,
    or_rec: Expr,
    #[cfg(test)]
    eq_c: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl CancelLeftConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            le_total: k("Rat.le_total"),
            le_antisymm: k("Rat.le_antisymm"),
            le_refl: k("Rat.le_refl"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            one_mul: k("Rat.one_mul"),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            #[cfg(test)]
            eq_c: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    #[cfg(test)]
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }
    #[cfg(test)]
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_c.clone(), [self.rat.clone(), a, b])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a b f h : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `Rat.ne_zero_of_pos c hc : c = 0 → False`.
    fn ne_zero_of_pos(&self, c: Expr, hc: Expr) -> Expr {
        Expr::apps(self.ne_zero_of_pos.clone(), [c, hc])
    }
    /// `0 ≤ a` from `0 < a` via `And.left (Iff.mp (lt_iff_le_not_le 0 a) h)`.
    fn le_of_lt0(&self, a: Expr, hlt: Expr) -> Expr {
        let zero = self.rat_zero.clone();
        let le_0a = self.le(zero.clone(), a.clone());
        let not_le_a0 = Expr::app(self.not_c.clone(), self.le(a.clone(), zero.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_0a.clone(), not_le_a0.clone()]);
        let lt_0a = self.lt(zero.clone(), a.clone());
        let iff = Expr::apps(self.lt_iff_le_not_le.clone(), [zero, a]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_0a, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_0a, not_le_a0, mp])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.le_antisymm a b (a≤b)(b≤a) : Eq Rat a b`.
    fn le_antisymm(&self, a: Expr, b: Expr, hab: Expr, hba: Expr) -> Expr {
        Expr::apps(self.le_antisymm.clone(), [a, b, hab, hba])
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a)
    }
    /// `Rat.mul_inv_cancel a (h : a = 0 → False) : a·(inv a) = 1`.
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
}

impl Environment {
    /// Register `Rat.le_of_mul_le_mul_left_pos`. Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    ///
    /// `∀ a b c, 0 < c → c·a ≤ c·b → a ≤ b`. See the module docs for the proof.
    pub fn register_rat_le_of_mul_le_mul_left_pos(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_mul_le_mul_left_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_and()?;
        self.init_or()?;
        self.init_iff()?;
        // Rat.ne_zero_of_pos, Rat.le_total, Rat.le_antisymm, Rat.lt_iff_le_not_le,
        // Rat.le_refl, Rat.inv, Rat.mul_inv_cancel, Rat.mul_assoc/_comm/one_mul.
        self.init_algebra_rat_inv_dyadic()?;
        // Rat.mul_le_mul_of_nonneg_left.
        self.init_boolean_analysis_order_toolkit()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CancelLeftConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_cancel_left(&c, false),
            value: build_cancel_left(&c, true),
        })
    }
}

/// Build the type (`for_value = false`, all binders Pi) or proof value
/// (`for_value = true`, all binders Lam + conclusion replaced by the proof term).
fn build_cancel_left(c: &CancelLeftConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());

    let hc_ty = c.lt(c.rat_zero.clone(), cv.clone()); // 0 < c
    let ca = c.mul(cv.clone(), a.clone()); // c·a
    let cb = c.mul(cv.clone(), bv.clone()); // c·b
    let hcab_ty = c.le(ca.clone(), cb.clone()); // c·a ≤ c·b
    let concl = c.le(a.clone(), bv.clone()); // a ≤ b

    let (hc_id, hc) = b.fresh_local(hc_ty.clone());
    let (hcab_id, hcab) = b.fresh_local(hcab_ty.clone());

    let tail = if for_value {
        build_cancel_left_proof(c, &b, &a, &bv, &cv, &ca, &cb, hc, hcab)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hcab_id, hcab_ty, tail);
    let e = bind(&b, hc_id, hc_ty, e);
    let e = bind(&b, cv_id, c.rat.clone(), e);
    let e = bind(&b, bv_id, c.rat.clone(), e);
    let e = bind(&b, a_id, c.rat.clone(), e);
    b.finish(e)
}

/// The proof term for `a ≤ b` given `hc : 0 < c`, `hcab : c·a ≤ c·b`.
#[allow(clippy::too_many_arguments)]
fn build_cancel_left_proof(
    c: &CancelLeftConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    cv: &Expr,
    ca: &Expr,
    cb: &Expr,
    hc: Expr,
    hcab: Expr,
) -> Expr {
    let h0c = c.le_of_lt0(cv.clone(), hc.clone()); // 0 ≤ c
    let hne = c.ne_zero_of_pos(cv.clone(), hc); // c = 0 → False

    let le_ab = c.le(a.clone(), bv.clone()); // a ≤ b
    let le_ba = c.le(bv.clone(), a.clone()); // b ≤ a
    let or_ty = Expr::apps(c.or_c.clone(), [le_ab.clone(), le_ba.clone()]);
    let total = Expr::apps(c.le_total.clone(), [a.clone(), bv.clone()]);

    // motive := fun (_ : Or (a≤b) (b≤a)) => a ≤ b.
    let or_motive = {
        let mut om = EnvDeclBuilder::child_of(parent);
        let (hh_id, _) = om.fresh_local(or_ty.clone());
        om.finish_child(om.mk_lam(hh_id, BinderInfo::Default, or_ty.clone(), le_ab.clone()))
    };

    // left: fun (hab : a≤b) => hab.
    let left_fn = {
        let mut lb = EnvDeclBuilder::child_of(parent);
        let (hab_id, hab) = lb.fresh_local(le_ab.clone());
        lb.finish_child(lb.mk_lam(hab_id, BinderInfo::Default, le_ab.clone(), hab))
    };

    // right: fun (hba : b≤a) => (proof of a≤b via cancellation).
    let right_fn = {
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (hba_id, hba) = rb.fresh_local(le_ba.clone());

        // hcb_ca : c·b ≤ c·a  := mul_le_mul_of_nonneg_left c b a hba h0c.
        let hcb_ca = c.mul_le_left(cv.clone(), bv.clone(), a.clone(), hba, h0c.clone());
        // heq : c·a = c·b  := le_antisymm (c·a) (c·b) hcab hcb_ca.
        let heq = c.le_antisymm(ca.clone(), cb.clone(), hcab.clone(), hcb_ca);

        // Cancel c on the left:  a = b.
        let inv_c = c.inv(cv.clone()); // inv c
        let one = c.rat_one.clone();

        // cinv : c·(inv c) = 1   ; inv_c_c : (inv c)·c = 1.
        let cinv = c.mul_inv_cancel(cv.clone(), hne); // c·inv c = 1
        let c_invc = c.mul(cv.clone(), inv_c.clone()); // c·inv c
        let invc_c = c.mul(inv_c.clone(), cv.clone()); // inv c·c
                                                       // comm : inv c·c = c·inv c.
        let comm_invc_c = c.mul_comm(inv_c.clone(), cv.clone());
        // invc_c_eq_one : inv c·c = 1   (trans comm cinv).
        let invc_c_eq_one = c.trans(
            invc_c.clone(),
            c_invc.clone(),
            one.clone(),
            comm_invc_c,
            cinv,
        );

        // For x ∈ {a, b}:  x = (inv c·c)·x   then  = inv c·(c·x).
        //   step_x1 : x = 1·x          symm (one_mul x)
        //   step_x2 : 1·x = (inv c·c)·x   congrArg (fun t => t·x) (symm invc_c_eq_one)
        //   step_x3 : (inv c·c)·x = inv c·(c·x)   mul_assoc (inv c) c x
        // chain to:  x = inv c·(c·x).
        let to_invc_cx = |x: &Expr| -> Expr {
            let one_x = c.mul(one.clone(), x.clone()); // 1·x
            let invcc_x = c.mul(invc_c.clone(), x.clone()); // (inv c·c)·x
            let invc_cx = c.mul(inv_c.clone(), c.mul(cv.clone(), x.clone())); // inv c·(c·x)
                                                                              // step1 : x = 1·x
            let one_mul_x = c.one_mul(x.clone()); // 1·x = x
            let step1 = c.symm(one_x.clone(), x.clone(), one_mul_x);
            // step2 : 1·x = (inv c·c)·x   via congrArg (fun t => t·x) (symm invc_c_eq_one)
            let f_mul_x = {
                let mut e = EnvDeclBuilder::child_of(parent);
                let (t_id, t) = e.fresh_local(c.rat.clone());
                e.finish_child(e.mk_lam(
                    t_id,
                    BinderInfo::Default,
                    c.rat.clone(),
                    c.mul(t, x.clone()),
                ))
            };
            let invc_c_eq_one_symm = c.symm(invc_c.clone(), one.clone(), invc_c_eq_one.clone());
            let step2 = c.congr_arg(one.clone(), invc_c.clone(), f_mul_x, invc_c_eq_one_symm);
            // step3 : (inv c·c)·x = inv c·(c·x)   mul_assoc.
            let step3 = c.mul_assoc(inv_c.clone(), cv.clone(), x.clone());
            // chain x = 1·x = (inv c·c)·x = inv c·(c·x)
            let t12 = c.trans(x.clone(), one_x, invcc_x.clone(), step1, step2);
            c.trans(x.clone(), invcc_x, invc_cx, t12, step3)
        };

        // a = inv c·(c·a) ; b = inv c·(c·b).
        let a_eq = to_invc_cx(a); // a = inv c·(c·a)
        let b_eq = to_invc_cx(bv); // b = inv c·(c·b)
        let invc_ca = c.mul(inv_c.clone(), ca.clone()); // inv c·(c·a)
        let invc_cb = c.mul(inv_c.clone(), cb.clone()); // inv c·(c·b)

        // mid : inv c·(c·a) = inv c·(c·b)   congrArg (fun t => inv c·t) heq.
        let f_invc = {
            let mut e = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = e.fresh_local(c.rat.clone());
            e.finish_child(e.mk_lam(
                t_id,
                BinderInfo::Default,
                c.rat.clone(),
                c.mul(inv_c.clone(), t),
            ))
        };
        let mid = c.congr_arg(ca.clone(), cb.clone(), f_invc, heq);

        // b_eq_symm : inv c·(c·b) = b.
        let b_eq_symm = c.symm(bv.clone(), invc_cb.clone(), b_eq);
        // a = inv c·(c·a) = inv c·(c·b) = b.
        let t_amid = c.trans(a.clone(), invc_ca.clone(), invc_cb.clone(), a_eq, mid);
        let heq_ab = c.trans(a.clone(), invc_cb, bv.clone(), t_amid, b_eq_symm); // a = b

        // a ≤ b := Eq.subst (fun t => a ≤ t) (a:=a)(b:=b) heq_ab (le_refl a).
        let motive = {
            let mut e = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = e.fresh_local(c.rat.clone());
            e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), c.le(a.clone(), t)))
        };
        let body = c.subst(motive, a.clone(), bv.clone(), heq_ab, c.le_refl(a.clone()));
        rb.finish_child(rb.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), body))
    };

    // @Or.rec (a≤b) (b≤a) motive left right total.
    Expr::apps(
        c.or_rec.clone(),
        [le_ab, le_ba, or_motive, left_fn, right_fn, total],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_le_of_mul_le_mul_left_pos()
            .expect("register_rat_le_of_mul_le_mul_left_pos");
        env.register_rat_le_of_mul_le_mul_left_pos()
            .expect("idempotent");
        env
    }

    /// The cancellation lemma is a kernel-checked, `Constructive`, empty-closure
    /// Theorem.
    #[test]
    fn test_rat_le_of_mul_le_mul_left_pos_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("Rat.le_of_mul_le_mul_left_pos");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
