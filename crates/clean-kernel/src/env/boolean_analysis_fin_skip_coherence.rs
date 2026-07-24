// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two `Fin.skipNth` reindex coherences for the interior (`p = castSucc p'`)
//! case of `Fin.sum_remove`:
//!
//! ```text
//! Fin.skipNth_castSucc_last :        (A)
//!   (m)(p' : Fin (m+1)) →
//!     @Eq (Fin (m+2)) (Fin.skipNth (m+1) (Fin.castSucc (m+1) p') (Fin.last m))
//!                     (Fin.last (m+1))
//!
//! Fin.skipNth_castSucc_castSucc :    (B)
//!   (m)(p' : Fin (m+1))(j : Fin m) →
//!     @Eq (Fin (m+2)) (Fin.skipNth (m+1) (Fin.castSucc (m+1) p') (Fin.castSucc m j))
//!                     (Fin.castSucc (m+1) (Fin.skipNth m p' j))
//! ```
//!
//! Both reduce `skipNth` via `Fin.skipNth_lt` / `Fin.skipNth_ge` (the `ite`
//! collapse, given a proof / disproof of the guard `val · < val (castSucc p') ≡
//! val · < val p'`), then close at the `Fin (m+2)` level by `Fin.eq_of_val_eq`
//! on a `val`-equality that reduces to `Eq.refl`.
//!
//! - **A**: `val (last m) ≡ m`, and `m < val p'` is false (`val p' ≤ m` from
//!   `Fin.isLt p'`), so `skipNth_ge` shifts to val `succ m ≡ m+1 ≡ val (last
//!   (m+1))`.
//! - **B**: case-split `Nat.decLt (val j) (val p')`.  TRUE → both sides reduce
//!   (via `skipNth_lt` twice + `castSucc`) to val `val j`.  FALSE → both reduce
//!   (via `skipNth_ge` twice + `castSucc`) to val `succ (val j)`.
//!
//! Constructive, empty admitted-axiom closure.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct CohConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_lt: Expr,
    nat_dec_lt: Expr,
    fin: Expr,
    fin_mk: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_eq_of_val: Expr,
    skip_nth: Expr,
    skip_nth_lt: Expr,
    skip_nth_ge: Expr,
    nat_succ_lt_succ: Expr,
    nat_lt_irrefl: Expr,
    nat_lt_of_lt_of_le: Expr,
    nat_le_of_succ_le_succ: Expr,
    decidable: Expr,
    decidable_rec0: Expr, // Decidable.rec.{0} — Prop motive (the Eq goal)
    eq1: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    eq_refl_nat: Expr,
    congr_arg: Expr,
    nat_c: Expr,
}

impl CohConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let l0 = Level::zero();
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_succ: k("Nat.succ"),
            nat_lt: k("Nat.lt"),
            nat_dec_lt: k("Nat.decLt"),
            fin: k("Fin"),
            fin_mk: k("Fin.mk"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            fin_eq_of_val: k("Fin.eq_of_val_eq"),
            skip_nth: k("Fin.skipNth"),
            skip_nth_lt: k("Fin.skipNth_lt"),
            skip_nth_ge: k("Fin.skipNth_ge"),
            nat_succ_lt_succ: k("Nat.succ_lt_succ"),
            nat_lt_irrefl: k("Nat.lt_irrefl"),
            nat_lt_of_lt_of_le: k("Nat.lt_of_lt_of_le"),
            nat_le_of_succ_le_succ: k("Nat.le_of_succ_le_succ"),
            decidable: k("Decidable"),
            decidable_rec0: Expr::const_(Name::from_string("Decidable.rec"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_refl_nat: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            nat_c: k("Nat"),
        }
    }

    /// `Fin.mk (n+1) (Nat.succ (Fin.val n x)) (Nat.succ_lt_succ (val x) n (Fin.isLt n x))`
    /// — the `skip_shift` image of `x : Fin n` (val `= val x + 1`).
    fn skip_shift(&self, n: &Expr, x: &Expr) -> Expr {
        let n1 = self.succ(n);
        let val_x = self.val(n, x);
        let islt = Expr::apps(self.fin_islt.clone(), [n.clone(), x.clone()]);
        let bound = Expr::apps(
            self.nat_succ_lt_succ.clone(),
            [val_x.clone(), n.clone(), islt],
        );
        Expr::apps(self.fin_mk.clone(), [n1, self.succ(&val_x), bound])
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
    fn cast_succ(&self, k: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [k.clone(), j.clone()])
    }
    fn last(&self, k: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), k.clone())
    }
    fn skip(&self, k: &Expr, p: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.skip_nth.clone(), [k.clone(), p.clone(), j.clone()])
    }
    fn eq_fin(&self, n: &Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.fin_of(n), l, r])
    }
}

// ===========================================================================
// (A) Fin.skipNth_castSucc_last
// ===========================================================================
fn coh_a_type(c: &CohConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let m1 = c.succ(&m); // m+1
    let m2 = c.succ(&m1); // m+2
    let fin_m1 = c.fin_of(&m1);
    let (p_id, p) = b.fresh_local(fin_m1.clone());
    let cs_p = c.cast_succ(&m1, &p); // castSucc (m+1) p' : Fin (m+2)
    let last_m = c.last(&m); // Fin.last m : Fin (m+1)
    let lhs = c.skip(&m1, &cs_p, &last_m); // : Fin (m+2)
    let rhs = c.last(&m1); // Fin.last (m+1) : Fin (m+2)
    let concl = c.eq_fin(&m2, lhs, rhs);
    let e = b.mk_pi(p_id, BinderInfo::Default, fin_m1, concl);
    b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
}

fn coh_a_value(c: &CohConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let m1 = c.succ(&m);
    let m2 = c.succ(&m1);
    let fin_m1 = c.fin_of(&m1);
    let (p_id, p) = b.fresh_local(fin_m1.clone());

    let cs_p = c.cast_succ(&m1, &p);
    let last_m = c.last(&m);
    let last_m1 = c.last(&m1);
    let val_p = c.val(&m1, &p); // val p'
    let val_last_m = c.val(&m1, &last_m); // ≡ m
    let val_cs_p = c.val(&m2, &cs_p); // ≡ val p'

    // hle : Nat.le (val p') m  := Nat.le_of_succ_le_succ (val p') m (Fin.isLt (m+1) p')
    //   Fin.isLt (m+1) p' : Nat.lt (val p') (m+1) ≡ Nat.le (succ (val p')) (succ m)
    let islt_p = Expr::apps(c.fin_islt.clone(), [m1.clone(), p.clone()]);
    let hle = Expr::apps(
        c.nat_le_of_succ_le_succ.clone(),
        [val_p.clone(), m.clone(), islt_p],
    );

    // hge : Nat.lt (val (last m)) (val (castSucc p')) → False
    //   := fun (hlt : Nat.lt (val (last m)) (val (castSucc p'))) =>
    //        Nat.lt_irrefl m (Nat.lt_of_lt_of_le m (val p') m hlt hle)
    //   (`hlt` is the HYPOTHESIS; `val (last m) ≡ m`, `val (castSucc p') ≡ val p'`
    //    so it fills the `LT.lt m (val p')` slot by defeq.)
    let hge = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hyp = c.lt(&val_last_m, &val_cs_p);
        let (hlt_id, hlt) = d.fresh_local(hyp.clone());
        // Nat.lt_of_lt_of_le m (val p') m hlt hle : Nat.lt m m
        let lt_mm = Expr::apps(
            c.nat_lt_of_lt_of_le.clone(),
            [
                m.clone(),
                val_p.clone(),
                m.clone(),
                hlt.clone(),
                hle.clone(),
            ],
        );
        // Nat.lt_irrefl m lt_mm : False
        let body = Expr::apps(c.nat_lt_irrefl.clone(), [m.clone(), lt_mm]);
        d.finish_child(d.mk_lam(hlt_id, BinderInfo::Default, hyp, body))
    };

    // e1 : skipNth (m+1) (castSucc p') (last m) = skip_shift (m+1) (last m)
    //   := Fin.skipNth_ge (m+1) (castSucc p') (last m) hge
    let lhs = c.skip(&m1, &cs_p, &last_m);
    let shift = {
        // mirror skip_shift: Fin.mk (m+2) (succ (val (last m))) (Nat.succ_lt_succ (val (last m)) (m+1) (Fin.isLt (m+1) (last m)))
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let succ_lt_succ = Expr::const_(Name::from_string("Nat.succ_lt_succ"), vec![]);
        let islt_last = Expr::apps(c.fin_islt.clone(), [m1.clone(), last_m.clone()]);
        let bound = Expr::apps(succ_lt_succ, [val_last_m.clone(), m1.clone(), islt_last]);
        Expr::apps(fin_mk, [m2.clone(), c.succ(&val_last_m), bound])
    };
    let e1 = Expr::apps(
        c.skip_nth_ge.clone(),
        [m1.clone(), cs_p.clone(), last_m.clone(), hge],
    );

    // e2 : shift = last (m+1)
    //   := Fin.eq_of_val_eq (m+2) shift (last (m+1)) (Eq.refl Nat (succ (val (last m))))
    //   val shift ≡ succ (val (last m)) ≡ succ m;  val (last (m+1)) ≡ m+1 ≡ succ m.
    let hval = Expr::apps(
        c.eq_refl_nat.clone(),
        [c.nat_c.clone(), c.succ(&val_last_m)],
    );
    let e2 = Expr::apps(
        c.fin_eq_of_val.clone(),
        [m2.clone(), shift.clone(), last_m1.clone(), hval],
    );

    // chain: lhs = shift = last (m+1)
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.fin_of(&m2), lhs, shift, last_m1, e1, e2],
    );

    let e = b.mk_lam(p_id, BinderInfo::Default, fin_m1, proof);
    b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
}

include!("boolean_analysis_fin_skip_coherence_b.rs");

impl Environment {
    /// Register coherence (A) `Fin.skipNth_castSucc_last` (see module docs).
    /// Constructive, empty axiom closure. Idempotent.
    pub(crate) fn register_fin_skip_coherence_a(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.skipNth_castSucc_last");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_lt()?;
        self.init_fin()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_fin_skip_nth_collapse()?; // skipNth + skipNth_ge
        self.register_nat_lt_irrefl_theorem()?; // Nat.lt_irrefl
        self.init_nat_trans_lt_le_lt()?; // Nat.lt_of_lt_of_le
        self.register_nat_le_of_succ_le_succ_theorem()?; // Nat.le_of_succ_le_succ
        self.init_nat_top_level_ordering()?; // Nat.succ_lt_succ (for skip_shift bound)
        {
            let fc = super::nn_verify_fin_sum::FinSumConsts::new();
            self.ensure_fin_cast_succ(&fc)?;
            self.ensure_fin_last(&fc)?;
        }

        let c = CohConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: coh_a_type(&c),
            value: coh_a_value(&c),
        })
    }

    /// Register coherence (B) `Fin.skipNth_castSucc_castSucc` (see module docs).
    /// Constructive, empty axiom closure. Idempotent.
    pub(crate) fn register_fin_skip_coherence_b(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.skipNth_castSucc_castSucc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_lt()?;
        self.init_fin()?;
        self.init_decidable()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_fin_skip_nth_collapse()?; // skipNth + skipNth_lt + skipNth_ge
        self.register_nat_dec_le_lt_proof()?; // Nat.decLt
        self.init_nat_top_level_ordering()?; // Nat.succ_lt_succ
        {
            let fc = super::nn_verify_fin_sum::FinSumConsts::new();
            self.ensure_fin_cast_succ(&fc)?;
            self.ensure_fin_last(&fc)?;
        }

        let c = CohConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: coh_b_type(&c),
            value: coh_b_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_skip_coherence_a_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_coherence_a().expect("register");
        env.register_fin_skip_coherence_a().expect("idempotent");

        let name = Name::from_string("Fin.skipNth_castSucc_last");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("value"), &info.type_)
            .expect("coherence A must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_fin_skip_coherence_b_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_skip_coherence_b().expect("register");
        env.register_fin_skip_coherence_b().expect("idempotent");

        let name = Name::from_string("Fin.skipNth_castSucc_castSucc");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("value"), &info.type_)
            .expect("coherence B must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
