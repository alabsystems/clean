// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 6a** (`pigeonhole-pos`): the general-`n` pigeonhole.
//!
//! [`Fin.exists_ge_of_sum_ge`] is stated for `Fin (Nat.succ m)`; the KKL finish
//! needs it over an arbitrary `Fin n` with `0 < n` (the `Fin 0` case being
//! excluded by positivity, never by an admitted fact). THIS lands that lift via
//! `Nat.rec.{0}` over `n`:
//!
//! ```text
//! Fin.exists_ge_of_sum_ge_pos :
//!   ∀ (n : Nat) (c : Rat) (f : Fin n → Rat),
//!     Nat.lt Nat.zero n →
//!     Rat.le (Fin.sum n (fun _ => c)) (Fin.sum n f) →
//!     Exists (i : Fin n) (Rat.le c (f i))
//! ```
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! `Nat.rec.{0}` with motive
//! `M m := (c : Rat) → (f : Fin m → Rat) → Nat.lt 0 m → Σ(const c) ≤ Σf →
//!         ∃ i : Fin m, c ≤ f i`:
//! - **zero**: `M 0` takes `Nat.lt 0 0 ≡ Nat.le (succ 0) 0`, refuted by
//!   `Nat.not_succ_le_zero 0`; `False.elim` closes the existential.
//! - **succ m'**: `M (succ m')` is (def-eq) the signature of
//!   `Fin.exists_ge_of_sum_ge m'`; return it directly (the `0 < succ m'`
//!   positivity hypothesis is discarded).
//!
//! Both leaves (`Fin.exists_ge_of_sum_ge`, `Nat.not_succ_le_zero`, `False.elim`)
//! are `Constructive` with empty admitted-axiom closure, so this lift is too.
//! No axiom added/removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct PhPosConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    fin: Expr,
    fin_sum: Expr,
    nat_le: Expr,
    u1: Level,
}

impl PhPosConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            nat_le: k("Nat.le"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    /// `Nat.lt 0 n ≡ Nat.le (succ 0) n`.
    fn pos(&self, n: &Expr) -> Expr {
        Expr::apps(
            self.nat_le.clone(),
            [self.succ(&self.nat_zero.clone()), n.clone()],
        )
    }
    /// `fun (_ : Fin n) => c`.
    fn const_fn(&self, parent: &EnvDeclBuilder, n: &Expr, c: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, _i) = b.fresh_local(fin_n.clone());
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, c.clone()))
    }
    /// `Exists.{1} (Fin n) (fun i => c ≤ f i)`.
    fn exists_ge(&self, parent: &EnvDeclBuilder, n: &Expr, c: &Expr, f: &Expr) -> Expr {
        let pred = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let fin_n = self.fin_of(n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let body = self.rat_le(c.clone(), Expr::app(f.clone(), i));
            b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Exists"), vec![self.u1.clone()]),
            [self.fin_of(n), pred],
        )
    }
}

/// `∀ (n c f), 0 < n → Σ(const c) ≤ Σf → ∃ i, c ≤ f i`.
fn pos_type(c: &PhPosConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let fn_ty = c.fin_to_rat(&n);
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let pos_ty = c.pos(&n);
    let (hp_id, _) = b.fresh_local(pos_ty.clone());
    let const_c = c.const_fn(&b, &n, &cv);
    let h_ty = c.rat_le(c.sum(&n, const_c), c.sum(&n, f.clone()));
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let concl = c.exists_ge(&b, &n, &cv, &f);

    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(hp_id, BinderInfo::Default, pos_ty, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `fun n => Nat.rec.{0} motive zero succ n`, where the recursor lands the
/// motive `M n := (c)(f)(0<n)(Σconst ≤ Σf) → ∃ i, c ≤ f i`.
fn pos_value(c: &PhPosConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n_top) = b.fresh_local(c.nat.clone());

    // motive m := (c : Rat) → (f : Fin m → Rat) → 0 < m → Σconst ≤ Σf → ∃ i, c ≤ f i.
    let motive_at = |parent: &EnvDeclBuilder, m: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (cv_id, cv) = d.fresh_local(c.rat.clone());
        let fn_ty = c.fin_to_rat(m);
        let (f_id, f) = d.fresh_local(fn_ty.clone());
        let pos_ty = c.pos(m);
        let (hp_id, _) = d.fresh_local(pos_ty.clone());
        let const_c = c.const_fn(&d, m, &cv);
        let h_ty = c.rat_le(c.sum(m, const_c), c.sum(m, f.clone()));
        let (h_id, _) = d.fresh_local(h_ty.clone());
        let concl = c.exists_ge(&d, m, &cv, &f);
        let e = d.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let e = d.mk_pi(hp_id, BinderInfo::Default, pos_ty, e);
        let e = d.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
        d.finish_child(d.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e))
    };
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let body = motive_at(&d, &m);
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // zero : M 0 = (c)(f)(0<0)(_) → ∃ i, c ≤ f i.  `0<0` is refuted.
    let zero_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let zero = c.nat_zero.clone();
        let (cv_id, cv) = d.fresh_local(c.rat.clone());
        let fn_ty = c.fin_to_rat(&zero);
        let (f_id, f) = d.fresh_local(fn_ty.clone());
        let pos_ty = c.pos(&zero);
        let (hp_id, hp) = d.fresh_local(pos_ty.clone());
        let const_c = c.const_fn(&d, &zero, &cv);
        let h_ty = c.rat_le(c.sum(&zero, const_c), c.sum(&zero, f.clone()));
        let (h_id, _h) = d.fresh_local(h_ty.clone());
        let goal = c.exists_ge(&d, &zero, &cv, &f);
        // Nat.not_succ_le_zero 0 hp : False.  (hp : Nat.le (succ 0) 0.)
        let h_false = Expr::apps(
            Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
            [c.nat_zero.clone(), hp],
        );
        let body = Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [goal, h_false],
        );
        let e = d.mk_lam(h_id, BinderInfo::Default, h_ty, body);
        let e = d.mk_lam(hp_id, BinderInfo::Default, pos_ty, e);
        let e = d.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
        d.finish_child(d.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e))
    };

    // succ : (m' : Nat) → M m' → M (succ m').  Discard the IH; the goal is
    //   (c)(f)(0<succ m')(Σconst ≤ Σf) → ∃ i:Fin(succ m'), c ≤ f i, which is
    //   def-eq to `Fin.exists_ge_of_sum_ge m' c f (the sum-hyp)`.
    let succ_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (mp_id, mp) = d.fresh_local(c.nat.clone());
        let ih_ty = motive_at(&d, &mp);
        let (ih_id, _ih) = d.fresh_local(ih_ty.clone());
        let sm = c.succ(&mp);
        let (cv_id, cv) = d.fresh_local(c.rat.clone());
        let fn_ty = c.fin_to_rat(&sm);
        let (f_id, f) = d.fresh_local(fn_ty.clone());
        let pos_ty = c.pos(&sm);
        let (hp_id, _hp) = d.fresh_local(pos_ty.clone());
        let const_c = c.const_fn(&d, &sm, &cv);
        let h_ty = c.rat_le(c.sum(&sm, const_c), c.sum(&sm, f.clone()));
        let (h_id, h) = d.fresh_local(h_ty.clone());
        // Fin.exists_ge_of_sum_ge m' c f h : ∃ i : Fin (succ m'), c ≤ f i.
        let body = Expr::apps(
            Expr::const_(Name::from_string("Fin.exists_ge_of_sum_ge"), vec![]),
            [mp.clone(), cv.clone(), f.clone(), h],
        );
        let e = d.mk_lam(h_id, BinderInfo::Default, h_ty, body);
        let e = d.mk_lam(hp_id, BinderInfo::Default, pos_ty, e);
        let e = d.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
        let e = d.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
        let e = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
        d.finish_child(d.mk_lam(mp_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, n_top.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app))
}

impl Environment {
    /// Register `Fin.exists_ge_of_sum_ge_pos` — **RUNG 6a**: the general-`n`
    /// (`0 < n`) pigeonhole / averaging step. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_fin_exists_ge_of_sum_ge_pos(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.exists_ge_of_sum_ge_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_fin_exists_ge_of_sum_ge()?; // Fin.exists_ge_of_sum_ge (+ Fin.sum spine)
        self.init_exists()?;
        self.init_true_false()?; // False.elim
        self.register_nat_not_succ_le_zero_theorem()?; // Nat.not_succ_le_zero

        let c = PhPosConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: pos_type(&c),
            value: pos_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_exists_ge_of_sum_ge_pos_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_fin_exists_ge_of_sum_ge_pos()
            .expect("register_fin_exists_ge_of_sum_ge_pos");
        let nm = Name::from_string("Fin.exists_ge_of_sum_ge_pos");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("pigeonhole-pos proof must check: {e:?}"));
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

    #[test]
    fn test_pigeonhole_pos_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_fin_exists_ge_of_sum_ge_pos().expect("first");
        env.register_fin_exists_ge_of_sum_ge_pos()
            .expect("idempotent");
    }
}
