// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Fin.skipNth_ne_p` — the image of `Fin.skipNth k p` avoids `p` (val level):
//!
//! ```text
//! Fin.skipNth_ne_p : (k)(p : Fin (k+1))(j : Fin k) →
//!   @Eq Nat (Fin.val (k+1) (Fin.skipNth k p j)) (Fin.val (k+1) p) → False
//! ```
//!
//! This is the pointwise side-condition for the complement-sum `Fin.sum_congr`
//! in the 2-cycle step: every term `skipNth k' p i` is `≠ p`, so the off-`p`
//! coherence `Fin.sigmaComplement_coh_ne` applies at it.
//!
//! Case-split `Nat.decLt (val j) (val p)` (Decidable.rec.{0}):
//! - lt: `skipNth_lt` ⇒ `val (skipNth …) ≡ val j < val p`, so `= val p` is false
//!   (`val j < val p` + `val j = val p` ⇒ `val p < val p` ⇒ `Nat.lt_irrefl`).
//! - ge: `skipNth_ge` ⇒ `val (skipNth …) ≡ succ (val j)`.  `¬(val j < val p)` ⇒
//!   `val p ≤ val j < succ (val j)`, so `succ (val j) = val p` ⇒ `val p < val p`
//!   (`Nat.lt_of_lt_of_le`) ⇒ `Nat.lt_irrefl`.
//!
//! Constructive, empty admitted-axiom closure.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct SkipNePConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_lt: Expr,
    nat_dec_lt: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    skip_nth: Expr,
    skip_nth_lt: Expr,
    skip_nth_ge: Expr,
    nat_lt_irrefl: Expr,
    nat_lt_of_lt_of_le: Expr,
    nat_le_of_succ_le_succ: Expr,
    nat_not_lt: Expr, // Nat.not_lt : Iff (¬ a<b) (b≤a)
    iff_mp: Expr,     // Iff.mp
    fin_cast_succ: Expr,
    fin_mk: Expr,
    nat_succ_lt_succ: Expr,
    decidable: Expr,
    decidable_rec0: Expr,
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_ndrec: Expr,
    congr_arg: Expr,
    false_c: Expr,
}

impl SkipNePConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_succ: k("Nat.succ"),
            nat_lt: k("Nat.lt"),
            nat_dec_lt: k("Nat.decLt"),
            fin: k("Fin"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            skip_nth: k("Fin.skipNth"),
            skip_nth_lt: k("Fin.skipNth_lt"),
            skip_nth_ge: k("Fin.skipNth_ge"),
            nat_lt_irrefl: k("Nat.lt_irrefl"),
            nat_lt_of_lt_of_le: k("Nat.lt_of_lt_of_le"),
            nat_le_of_succ_le_succ: k("Nat.le_of_succ_le_succ"),
            nat_not_lt: k("Nat.not_lt"),
            iff_mp: Expr::const_(Name::from_string("Iff.mp"), vec![]),
            fin_cast_succ: k("Fin.castSucc"),
            fin_mk: k("Fin.mk"),
            nat_succ_lt_succ: k("Nat.succ_lt_succ"),
            decidable: k("Decidable"),
            decidable_rec0: Expr::const_(Name::from_string("Decidable.rec"), vec![l0.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_ndrec: Expr::const_(Name::from_string("Eq.ndrec"), vec![l0.clone(), l1]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            false_c: k("False"),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }
    fn lt(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a.clone(), b.clone()])
    }
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    fn skip(&self, k: &Expr, p: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.skip_nth.clone(), [k.clone(), p.clone(), j.clone()])
    }
}

fn skip_ne_p_type(c: &SkipNePConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);
    let (p_id, p) = b.fresh_local(fin_succ.clone());
    let (j_id, j) = b.fresh_local(fin_k.clone());
    let skipped = c.skip(&k, &p, &j);
    let val_skip = c.val(&succ_k, &skipped);
    let val_p = c.val(&succ_k, &p);
    let e_ty = c.eq_nat(val_skip, val_p);
    let (e_id, _e) = b.fresh_local(e_ty.clone());
    let body = b.mk_pi(e_id, BinderInfo::Default, e_ty, c.false_c.clone());
    let body = b.mk_pi(j_id, BinderInfo::Default, fin_k, body);
    let body = b.mk_pi(p_id, BinderInfo::Default, fin_succ, body);
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body))
}

fn skip_ne_p_value(c: &SkipNePConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);
    let (p_id, p) = b.fresh_local(fin_succ.clone());
    let (j_id, j) = b.fresh_local(fin_k.clone());

    let val_j = c.val(&k, &j);
    let val_p = c.val(&succ_k, &p);
    let prop = c.lt(&val_j, &val_p); // val j < val p
    let skipped = c.skip(&k, &p, &j);
    let val_skip = c.val(&succ_k, &skipped);
    let e_ty = c.eq_nat(val_skip.clone(), val_p.clone());

    // We dispatch on `Nat.decLt (val j) (val p)` with a dependent motive over the
    // discriminant so `skipNth k p j` ι-reduces per branch.  Concretely the
    // motive is `fun dd => (val (skip_rec dd) = val p) → False` where `skip_rec
    // dd` reconstructs `skipNth`'s ite at `dd`.  Simpler: `skipNth` is an `ite`,
    // not a raw rec, so it does NOT auto-reduce on `dd`.  Instead we use the
    // collapse lemmas `skipNth_lt`/`skipNth_ge`, which rewrite `skipNth k p j` to
    // its branch value given a proof/disproof of the guard — exactly what each
    // Decidable.rec minor supplies.  The motive is then `fun _ => (e_ty) → False`
    // BUT `e_ty` mentions `skipNth` which is stable across `dd`, so a constant
    // motive is fine here (no σ''-style stuck rec).
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (dd_id, _dd) = d.fresh_local(dec_prop.clone());
        let arr = Expr::pi(BinderInfo::Default, e_ty.clone(), c.false_c.clone());
        d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_prop, arr))
    };

    let val_fn = Expr::app(c.fin_val.clone(), succ_k.clone()); // Fin.val (k+1) : Fin (k+1) → Nat
    let cast_j = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), j.clone()]); // castSucc k j

    // ── lt minor (isTrue): fun (hlt : val j < val p) (e : val (skipNth)=val p) =>
    //      h_sk : val (skipNth) = val (castSucc j)  [congrArg val (skipNth_lt …)].
    //      val (castSucc j) ≡ val j (defeq), so e2 : val j = val p := (h_sk.symm).trans e.
    //      Transport hlt : val j < val p along e2 to val p < val p; Nat.lt_irrefl.
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (hlt_id, hlt) = d.fresh_local(prop.clone());
        let (e_id, e) = d.fresh_local(e_ty.clone());
        // skipNth_lt k p j hlt : skipNth k p j = castSucc k j
        let sk_lt = Expr::apps(
            c.skip_nth_lt.clone(),
            [k.clone(), p.clone(), j.clone(), hlt.clone()],
        );
        // h_sk : val (skipNth) = val (castSucc j)  [congrArg (Fin.val (k+1)) sk_lt]
        let h_sk = Expr::apps(
            c.congr_arg.clone(),
            [
                fin_succ.clone(),
                c.nat.clone(),
                skipped.clone(),
                cast_j.clone(),
                val_fn.clone(),
                sk_lt,
            ],
        );
        let val_cast = c.val(&succ_k, &cast_j); // ≡ val j
                                                // h_sk.symm : val (castSucc j) = val (skipNth)
        let h_sk_sym = Expr::apps(
            c.eq_symm.clone(),
            [c.nat.clone(), val_skip.clone(), val_cast.clone(), h_sk],
        );
        // e2 : val (castSucc j) = val p   [h_sk.symm.trans e]
        let e2 = Expr::apps(
            c.eq_trans.clone(),
            [
                c.nat.clone(),
                val_cast.clone(),
                val_skip.clone(),
                val_p.clone(),
                h_sk_sym,
                e.clone(),
            ],
        );
        // motive_t := fun (t : Nat) => Nat.lt t (val p)
        let motive_t = {
            let mut t = EnvDeclBuilder::child_of(&d);
            let (x_id, x) = t.fresh_local(c.nat.clone());
            let body = c.lt(&x, &val_p);
            t.finish_child(t.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body))
        };
        // hlt : Nat.lt (val j) (val p) ≡ Nat.lt (val (castSucc j)) (val p) (defeq);
        // @Eq.ndrec Nat (val (castSucc j)) motive_t hlt (val p) e2 : Nat.lt (val p) (val p)
        let lt_pp = Expr::apps(
            c.eq_ndrec.clone(),
            [
                c.nat.clone(),
                val_cast.clone(),
                motive_t,
                hlt.clone(),
                val_p.clone(),
                e2,
            ],
        );
        let body = Expr::apps(c.nat_lt_irrefl.clone(), [val_p.clone(), lt_pp]);
        let body = d.mk_lam(e_id, BinderInfo::Default, e_ty.clone(), body);
        d.finish_child(d.mk_lam(hlt_id, BinderInfo::Default, prop.clone(), body))
    };

    // ── ge minor (isFalse): fun (hge : ¬(val j < val p)) (e : val (skipNth)=val p) =>
    //      h_sk : val (skipNth) = val (skip_shift)  [congrArg val (skipNth_ge …)].
    //      val (skip_shift) ≡ succ (val j) (defeq).  e2 : succ (val j) = val p.
    //      hle : val p ≤ val j  [Iff.mp (Nat.not_lt …) hge].
    //      Rewrite val p → succ (val j) in hle via e2.symm:
    //        Nat.le (succ (val j)) (val j) ≡ Nat.lt (val j) (val j) ⇒ Nat.lt_irrefl.
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let not_prop = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
        let (hge_id, hge) = d.fresh_local(not_prop.clone());
        let (e_id, e) = d.fresh_local(e_ty.clone());

        // skip_shift = Fin.mk (k+1) (succ (val j)) (Nat.succ_lt_succ (val j) k (Fin.isLt k j))
        let islt = Expr::apps(c.fin_islt.clone(), [k.clone(), j.clone()]);
        let bound = Expr::apps(c.nat_succ_lt_succ.clone(), [val_j.clone(), k.clone(), islt]);
        let succ_vj = c.succ(&val_j);
        let skip_shift = Expr::apps(c.fin_mk.clone(), [succ_k.clone(), succ_vj.clone(), bound]);
        let val_shift = c.val(&succ_k, &skip_shift); // ≡ succ (val j)

        // skipNth_ge k p j hge : skipNth k p j = skip_shift
        let sk_ge = Expr::apps(
            c.skip_nth_ge.clone(),
            [k.clone(), p.clone(), j.clone(), hge.clone()],
        );
        // h_sk : val (skipNth) = val (skip_shift)
        let h_sk = Expr::apps(
            c.congr_arg.clone(),
            [
                fin_succ.clone(),
                c.nat.clone(),
                skipped.clone(),
                skip_shift.clone(),
                val_fn.clone(),
                sk_ge,
            ],
        );
        // h_sk.symm : val (skip_shift) = val (skipNth)
        let h_sk_sym = Expr::apps(
            c.eq_symm.clone(),
            [c.nat.clone(), val_skip.clone(), val_shift.clone(), h_sk],
        );
        // e2 : val (skip_shift) = val p   [h_sk.symm.trans e]   (val_shift ≡ succ (val j))
        let e2 = Expr::apps(
            c.eq_trans.clone(),
            [
                c.nat.clone(),
                val_shift.clone(),
                val_skip.clone(),
                val_p.clone(),
                h_sk_sym,
                e.clone(),
            ],
        );

        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        // Nat.not_lt (val j) (val p) : Iff (¬ (val j < val p)) (val p ≤ val j)
        let not_lt_iff = Expr::apps(c.nat_not_lt.clone(), [val_j.clone(), val_p.clone()]);
        let hle = Expr::apps(
            c.iff_mp.clone(),
            [
                not_prop.clone(),
                Expr::apps(nat_le.clone(), [val_p.clone(), val_j.clone()]),
                not_lt_iff,
                hge.clone(),
            ],
        );
        // hle : Nat.le (val p) (val j).  Rewrite val p → val (skip_shift) via e2.symm:
        //   motive_t := fun (t : Nat) => Nat.le t (val j)
        let motive_t = {
            let mut t = EnvDeclBuilder::child_of(&d);
            let (x_id, x) = t.fresh_local(c.nat.clone());
            let body = Expr::apps(nat_le.clone(), [x, val_j.clone()]);
            t.finish_child(t.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body))
        };
        // e2.symm : val p = val (skip_shift)
        let e2_sym = Expr::apps(
            c.eq_symm.clone(),
            [c.nat.clone(), val_shift.clone(), val_p.clone(), e2],
        );
        // @Eq.ndrec Nat (val p) motive_t hle (val (skip_shift)) e2.symm
        //   : Nat.le (val (skip_shift)) (val j) ≡ Nat.le (succ (val j)) (val j) ≡ Nat.lt (val j)(val j)
        let le_shift_j = Expr::apps(
            c.eq_ndrec.clone(),
            [
                c.nat.clone(),
                val_p.clone(),
                motive_t,
                hle,
                val_shift.clone(),
                e2_sym,
            ],
        );
        // Nat.lt_irrefl (val j) le_shift_j : False
        let body = Expr::apps(c.nat_lt_irrefl.clone(), [val_j.clone(), le_shift_j]);
        let body = d.mk_lam(e_id, BinderInfo::Default, e_ty.clone(), body);
        d.finish_child(d.mk_lam(hge_id, BinderInfo::Default, not_prop.clone(), body))
    };

    let discr = Expr::apps(c.nat_dec_lt.clone(), [val_j.clone(), val_p.clone()]);
    // @Decidable.rec.{0} prop motive isFalse isTrue discr : (val (skipNth)=val p) → False
    let rec_app = Expr::apps(
        c.decidable_rec0.clone(),
        [prop.clone(), motive, is_false_min, is_true_min, discr],
    );

    pre_close(
        c, &b, &k, &p, &j, rec_app, k_id, p_id, j_id, &fin_succ, &fin_k,
    )
}

#[allow(clippy::too_many_arguments)]
fn pre_close(
    _c: &SkipNePConsts,
    b: &EnvDeclBuilder,
    _k: &Expr,
    _p: &Expr,
    _j: &Expr,
    rec_app: Expr,
    k_id: crate::expr::FVarId,
    p_id: crate::expr::FVarId,
    j_id: crate::expr::FVarId,
    fin_succ: &Expr,
    fin_k: &Expr,
) -> Expr {
    let body = b.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), rec_app);
    let body = b.mk_lam(p_id, BinderInfo::Default, fin_succ.clone(), body);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, nat, body))
}

impl Environment {
    /// Register `Fin.skipNth_ne_p` (see module docs). Constructive, empty axiom
    /// closure. Idempotent.
    pub(crate) fn register_fin_skip_ne_p(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.skipNth_ne_p");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_lt()?;
        self.init_fin()?;
        self.init_decidable()?;
        self.register_fin_skip_nth_collapse()?; // skipNth + skipNth_lt + skipNth_ge
        self.register_nat_dec_le_lt_proof()?; // Nat.decLt
        self.register_nat_lt_irrefl_theorem()?; // Nat.lt_irrefl
        self.init_nat_trans_lt_le_lt()?; // Nat.lt_of_lt_of_le
        self.register_nat_le_of_succ_le_succ_theorem()?; // Nat.le_of_succ_le_succ
        self.init_nat_totality_proofs()?; // Nat.not_lt (Iff form)

        let c = SkipNePConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: skip_ne_p_type(&c),
            value: skip_ne_p_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_skip_ne_p_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_ne_p().expect("register");
        env.register_fin_skip_ne_p().expect("idempotent");

        let name = Name::from_string("Fin.skipNth_ne_p");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("skipNth_ne_p must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
