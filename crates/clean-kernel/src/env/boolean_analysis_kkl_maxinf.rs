// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 6b** (`maxinf`): the genuine `∃ i` MAX-INFLUENCE bound,
//! the faithful KKL conclusion.
//!
//! Combines the conditional sharp-KKL variance bound (rung 5,
//! [`kkl_conditional_var_bound`], `(k+1)·Var ≤ I[f]+I[f]`) with the general-`n`
//! pigeonhole (rung 6a, [`Fin.exists_ge_of_sum_ge_pos`]) to extract a SINGLE
//! coordinate with large influence:
//!
//! ```text
//! BoolAnalysis.kkl_exists_max_influence :
//!   ∀ (n k : Nat) (f : BoolFn n) (d : Rat),
//!     Nat.lt Nat.zero n →
//!     Rat.le Rat.zero d → Rat.lt (Rat.mul d d) Rat.one →
//!     (∀ i, Rat.le Rat.zero (Influence n f i)) →
//!     (∀ i, Rat.le (Influence n f i) (Rat.mul d d)) →        -- max influence ≤ δ²
//!     Rat.le (Rat.mul (natCast (k+1))                        -- (k+1)·t ≤ I[f]
//!                     (Rat.mul (9^k) (Rat.mul d (TotalInfluence n f))))
//!            (TotalInfluence n f) →
//!     Exists (i : Fin n)
//!       (Rat.le (Rat.mul (natCast (Nat.succ k)) (Variance n f))      -- (k+1)·Var
//!               (Rat.add (Rat.mul (natCast n) (Influence n f i))     -- ≤ n·Inf_i + n·Inf_i
//!                        (Rat.mul (natCast n) (Influence n f i)))) }  --  = 2·n·Inf_i
//! ```
//!
//! i.e. under the genuine small-influence regime `max_i Inf_i ≤ δ² < 1`, SOME
//! coordinate `i` carries influence `Inf_i ≥ ((k+1)·Var)/(2·n)` — the GENUINE
//! KKL max-influence lower bound (O'Donnell Thm 9.28). Non-trivial `∃ i`,
//! explicit positive constants (`k+1`, the factor `2` via the doubled sum, `n`).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Write `K := natCast(k+1)`, `V := Var`, `I := TotalInfluence n f ≡ Σ_i Inf_i`,
//! `Nn := natCast n`, `c := K·V`, `g i := Nn·Inf_i`, `F i := g i + g i`.
//!
//! 1. cond : K·V ≤ I + I               (kkl_conditional_var_bound …).
//! 2. hNn : 0 ≤ Nn                      (natCast_nonneg n).
//! 3. h_scaled : Nn·(K·V) ≤ Nn·(I+I)   (mul_le_mul_of_nonneg_left Nn (K·V)(I+I) cond hNn).
//! 4. e_distrib : Nn·(I+I) = Nn·I + Nn·I   (left_distrib Nn I I).
//! 5. eSc : Σ(const (K·V)) = Nn·(K·V)   (Fin.sum_const n (K·V)).
//! 6. eSg : Σ g = Nn·I                  (Fin.sum_smul n Nn Inf, with Σ_i Inf_i ≡ I).
//! 7. eSF : Σ F = Σ g + Σ g = Nn·I + Nn·I   (Fin.sum_add n g g ⬝ congr both legs eSg).
//! 8. hsum : Σ(const (K·V)) ≤ Σ F        (transport (3) along (4),(5),(7)).
//! 9. ∃ i, K·V ≤ F i := Fin.exists_ge_of_sum_ge_pos n (K·V) F hpos hsum,
//!    and `F i ≡ Nn·Inf_i + Nn·Inf_i` is the conclusion body.
//!
//! Every leaf is a `Constructive` empty-closure Theorem, so this rung is too.
//! No axiom added/removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct MaxInfConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_of_nat: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    pow_nat: Expr,
    fin: Expr,
    bool_fn: Expr,
    influence: Expr,
    variance: Expr,
    total_influence: Expr,
    u1: Level,
}

impl MaxInfConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_of_nat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            pow_nat: k("Rat.powNat"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            variance: k("BoolAnalysis.Variance"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn one_nat(&self) -> Expr {
        self.succ(&self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    fn rat_lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    fn rat_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.zero"), vec![])
    }
    fn rat_one(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.one"), vec![])
    }
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.one_nat(),
            ],
        )
    }
    fn pow9(&self, k: &Expr) -> Expr {
        Expr::apps(
            self.pow_nat.clone(),
            [
                Expr::app(self.rat_of_nat.clone(), self.nat_lit(9)),
                k.clone(),
            ],
        )
    }
    fn pos_nat(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            [self.succ(&self.nat_zero.clone()), n.clone()],
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    /// `∀ i, Rat.le Rat.zero (Influence n f i)`.
    fn h0_hyp(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.rat_le(self.rat_zero(), self.influence_of(n, f, &i));
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `∀ i, Rat.le (Influence n f i) (d·d)`.
    fn h1_hyp(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, dd: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.rat_le(self.influence_of(n, f, &i), dd.clone());
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `g := fun (i : Fin n) => (natCast n)·Inf_i`.
    fn g_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let nn = self.natcast(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.mul(nn, self.influence_of(n, f, &i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `F := fun (i : Fin n) => (natCast n)·Inf_i + (natCast n)·Inf_i`.
    fn f_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let nn = self.natcast(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let gi = self.mul(nn.clone(), self.influence_of(n, f, &i));
        let body = self.add(gi.clone(), gi);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `Inf := fun (i : Fin n) => Influence n f i`.
    fn inf_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.influence_of(n, f, &i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    fn fin_sum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum"), vec![]),
            [n.clone(), g],
        )
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `congrArg (fun z => z + right) h : a + right = b + right`.
    fn congr_add_r(
        &self,
        parent: &EnvDeclBuilder,
        right: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.add(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg (fun z => left + z) h : left + a = left + b`.
    fn congr_add_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.add(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
}

include!("boolean_analysis_kkl_maxinf_build.rs");

impl Environment {
    /// Register `BoolAnalysis.kkl_exists_max_influence` — **RUNG 6b**: the
    /// genuine `∃ i` max-influence KKL bound `∃ i, (k+1)·Var ≤ 2·n·Inf_i` under
    /// the small-influence regime. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_kkl_exists_max_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_exists_max_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.left_distrib
        self.register_kkl_conditional_var_bound()?; // rung 5
        self.register_fin_exists_ge_of_sum_ge_pos()?; // rung 6a
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.init_fin_sum()?; // Fin.sum_smul, Fin.sum_add
        self.register_fin_sum_const()?; // Fin.sum_const
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = MaxInfConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_maxinf(&c, false),
            value: build_maxinf(&c, true),
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
    fn test_kkl_exists_max_influence_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_exists_max_influence()
            .expect("register_kkl_exists_max_influence");
        let nm = Name::from_string("BoolAnalysis.kkl_exists_max_influence");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("maxinf proof must check: {e:?}"));
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
    fn test_maxinf_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_exists_max_influence().expect("first");
        env.register_kkl_exists_max_influence().expect("idempotent");
    }
}
