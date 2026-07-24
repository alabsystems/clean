// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — STEP 2 (sub-lemma 2c): the **influence normalization**
//! `m_i · 2^n = 4^n · Influence n f i`.
//!
//! ## What this proves
//!
//! `dualhc_final_le` consumes `IsRpow32 (m_i · 2^n) r` where `m_i := subsetSum n
//! (fun x => (D_i f x · D_i f x)·(½·½))` is STEP-2's support measure. The sharp
//! KKL charge supplies the NORMALIZED `IsRpow32 (Inf_i) (r_i)`. The
//! bridge that lets `rpow32_scale` connect them is the measure-normalization
//! identity that `m_i·2^n` is the `4^n`-scaled influence:
//!
//! ```text
//! BoolAnalysis.dualhc_m_pow2_eq_4pow_influence :
//!   ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
//!     @Eq Rat
//!       (Rat.mul m_i D)                              -- m_i · 2^n
//!       (Rat.mul (Rat.mul D D) (Influence n f i))    -- 4^n · Inf_i  (4^n = 2^n·2^n)
//! ```
//!
//! with `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ 2^n` (the `Expect`/`subsetSum`
//! normalizer — byte-identical to `acoeff_eq_pow2_fourier`'s `cube` and the
//! `Influence`/`Expect` denominator). The `D` carried here is the `ofNat(2^n)`
//! cast spelling; `dualhc_final_le`'s `Rat.powNat 2 n` spelling coincides with it
//! by `powNat_two_eq_ofNat_pow`, so the `4^n = D·D = (powNat 2 n)·(powNat 2 n)`
//! form `rpow32_scale` (at `c := 2^n`) produces is reached with one
//! spelling-rewrite at the call site.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Write `P := subsetSum n (fun x => ind(disagree x))` (the un-normalized
//! influence numerator) and recall `Influence n f i ≡ Expect n (ind∘disagree) ≡
//! Rat.div P D ≡ P · D⁻¹` DEFINITIONALLY (`Expect`, `Rat.div`, `subsetSum` all
//! reducible to the same `Fin.sum (2^n) (·∘hcDecode)`).
//!
//! 1. `dualhc_step2_m_eq_disagree_mass n f i` (LANDED): `m_i = P`. `congrArg
//!    (·D)` gives `m_i·D = P·D`.
//! 2. **`cube_mul_self_eq_mul_div_cancel`** (this module): `D · (D · Inf_i) = D·P`
//!    where `D·Inf_i ≡ D·(P·D⁻¹) = P` (the `D⁻¹`-cancel needs `D ≠ 0`,
//!    `two_pow_rat_ne_zero n`), regrouped so the surviving `D` lands on the LEFT
//!    of `Inf_i`. Precisely it proves `P·D = D·(D·Inf_i)`, i.e. the `4^n`-regroup
//!    `P·D = (D·D)·Inf_i` after one `mul_assoc`.
//! 3. `Eq.trans` (1)·(2)·(assoc) : `m_i·D = (D·D)·Inf_i`.
//!
//! Every leaf (`dualhc_step2_m_eq_disagree_mass`, `Rat.mul_inv_cancel`,
//! `two_pow_rat_ne_zero`, `Rat.mul_assoc`, `Rat.mul_comm`, `Rat.one_mul`,
//! `Eq.refl/symm/trans/congrArg`) is `Constructive` with empty closure, so this
//! bridge is too. NO axiom is added or removed; the soundness-certificate golden
//! TCB is unchanged. NOT wired into the always-on `init_boolean_analysis`
//! aggregate (reachable via `init_boolean_analysis_kkl_dualhc_norminfl`).
//! Idempotent.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the influence-normalization bridge. All `subsetSum` / `pm` /
/// `ind` / `hcFlip` / `D` spellings are byte-for-byte the landed `Step2Consts`
/// (`boolean_analysis_kkl_dualhc_step2.rs`) and `Influence`/`Expect`
/// (`boolean_analysis.rs`) conventions so the brick instances stay def-eq.
struct NormInflConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_inv: Expr,
    rat_two: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    pm: Expr,
    ind: Expr,
    hc_flip: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    subset_sum: Expr,
    influence: Expr,
    u1: Level,
}

impl NormInflConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_inv: k("Rat.inv"),
            rat_two: k("Rat.two"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            pm: k("BoolAnalysis.pm"),
            ind: k("BoolAnalysis.ind"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            influence: k("BoolAnalysis.Influence"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    fn one(&self) -> Expr {
        self.order.rat_one.clone()
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn ind_of(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `Nat.pow 2 n`. Byte-matches `subsetSum`/`Expect`/`Step2` `pow2`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    /// `D := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ 2^n` (the normalizer; byte-
    /// identical to `NpConsts::denom` / `acoeff` `cube` / `Expect` denom).
    fn denom(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), self.pow2(n)), one],
        )
    }
    /// `D_i f x := pm (f x) − pm (f (hcFlip n x i))`. Byte-matches
    /// `Step2Consts::deriv`.
    fn deriv(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, x, i));
        self.order.sub(self.pm_of(fx), self.pm_of(fflip))
    }
    /// `m_i := subsetSum n (fun x => (D_i f x · D_i f x)·(½·½))` — byte-identical
    /// to `dualhc_step2_m_eq_disagree_mass`'s LHS / `dualhc_final_le`'s `m`.
    fn m_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let g = self.deriv(n, f, &x, i);
        let half = self.half();
        let body = self.mul(self.mul(g.clone(), g), self.mul(half.clone(), half));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    fn m_of(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        self.ssum(n, self.m_fn(parent, n, f, i))
    }
    /// `fun x => ind (Bool.not (Bool.beq (f x) (f (hcFlip n x i))))` — byte-
    /// identical to `Step2`'s `ind_fn` AND `Influence`'s summand.
    fn ind_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, &x, i));
        let beq = Expr::apps(self.bool_beq.clone(), [fx, fflip]);
        let differ = Expr::app(self.bool_not.clone(), beq);
        let body = self.ind_of(differ);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `P := subsetSum n (ind_fn)` — the un-normalized influence numerator.
    fn p_of(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        self.ssum(n, self.ind_fn(parent, n, f, i))
    }
    /// `@congrArg.{1,1} Rat Rat a b g h : g a = g b`.
    fn congr_arg(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat(), self.rat(), a, b, g, h],
        )
    }
    fn lam_rat<F: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), a)
    }
    /// `Rat.mul_inv_cancel a (h : a ≠ 0) : a·a⁻¹ = 1`.
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]),
            [a, h],
        )
    }
    /// `two_pow_rat_ne_zero n : D = 0 → False`.
    fn d_ne_zero(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("BoolAnalysis.two_pow_rat_ne_zero"),
                vec![],
            ),
            n.clone(),
        )
    }
}

impl Environment {
    /// Register the STEP-2c influence-normalization bridge. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_norminfl(&mut self) -> Result<(), EnvError> {
        self.register_cube_mul_div_self_cancel()?;
        self.register_dualhc_m_pow2_eq_4pow_influence_norminfl_recovered()?;
        Ok(())
    }

    /// `BoolAnalysis.cube_mul_div_self_cancel :
    ///   ∀ (n : Nat) (P : Rat),
    ///     @Eq Rat (Rat.mul P D) (Rat.mul (Rat.mul D D) (Rat.mul P (Rat.inv D)))`,
    /// `D := 2^n` (`ofNat(2^n)` cast). The `4^n`-regroup identity:
    /// `P·D = (D·D)·(P·D⁻¹)`, the pure field-algebra core that turns the
    /// `D⁻¹`-normalized `Influence ≡ P·D⁻¹` back into the un-normalized `P` after
    /// scaling by `D·D`. Proof (RHS → LHS, then `symm`):
    ///
    /// ```text
    ///   (D·D)·(P·D⁻¹)
    /// = D·(D·(P·D⁻¹))            [mul_assoc D D (P·D⁻¹)]
    /// = D·((D·P)·D⁻¹)           [congr (D·) (symm (mul_assoc D P D⁻¹))]
    /// = D·((P·D)·D⁻¹)           [congr (D·∘(·D⁻¹)) (mul_comm D P)]
    /// = D·(P·(D·D⁻¹))           [congr (D·) (mul_assoc P D D⁻¹)]
    /// = D·(P·1)                 [congr (D·∘(P·)) (mul_inv_cancel D)]
    /// = D·P                     [congr (D·) (mul_one P)]   ... we use mul_comm to land P·D
    /// = P·D                     [mul_comm D P]
    /// ```
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_cube_mul_div_self_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.cube_mul_div_self_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.mul_assoc, Rat.mul_comm, Rat.one_mul, Rat.mul_inv_cancel, inv, congrArg
        self.init_rat_field_inst()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_two_pow_rat_ne_zero()?; // D ≠ 0

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NormInflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_cube_cancel(&c, false),
            value: build_cube_cancel(&c, true),
        })
    }

    /// `BoolAnalysis.dualhc_m_pow2_eq_4pow_influence` — see the module docs.
    /// `m_i · 2^n = (2^n · 2^n) · Influence n f i`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_dualhc_m_pow2_eq_4pow_influence_norminfl_recovered(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_m_pow2_eq_4pow_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Influence (reducible def), pm, ind, hcFlip
        self.init_beq()?;
        self.register_subset_sum()?;
        self.init_rat()?;
        self.init_boolean_analysis_kkl_dualhc_step2()?; // dualhc_step2_m_eq_disagree_mass
        self.register_cube_mul_div_self_cancel()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NormInflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_m_norm(&c, false),
            value: build_m_norm(&c, true),
        })
    }
}

// Term builders (`build_cube_cancel`, `build_m_norm`) live in the sibling
// include to keep this file under the 500-line convention.
include!("boolean_analysis_kkl_dualhc_norminfl_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_norminfl()
            .expect("init_boolean_analysis_kkl_dualhc_norminfl");
        env.init_boolean_analysis_kkl_dualhc_norminfl()
            .expect("idempotent");
        env
    }

    fn assert_ct(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_cube_mul_div_self_cancel_is_constructive_theorem() {
        assert_ct(&env(), "BoolAnalysis.cube_mul_div_self_cancel");
    }

    #[test]
    fn test_dualhc_m_pow2_eq_4pow_influence_is_constructive_theorem() {
        assert_ct(&env(), "BoolAnalysis.dualhc_m_pow2_eq_4pow_influence");
    }
}
