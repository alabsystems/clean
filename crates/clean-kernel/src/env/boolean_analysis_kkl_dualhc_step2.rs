// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **STEP 2**: the R2 4th-power Hölder lemma INSTANTIATED at the
//! genuine halved discrete derivative, in the un-normalized `subsetSum` world.
//!
//! R2 (`sum_prod_pow4_le_m3_sumpow4`) is the abstract algebraic core, stated over
//! an arbitrary `Fin N → Rat` index with the two-valued structure carried as
//! EXPLICIT hypotheses H1–H6. STEP 2 pins it to the concrete instance the dual-HC
//! chain needs:
//!
//! ```text
//!   N   := 2^n                                   (= Nat.pow 2 n)
//!   e   := fun jx => (D_i f (hcDecode n jx)) · half     (halved derivative)
//!   chi := fun jx => (g·g)·(half·half)  at g = D_i f (hcDecode n jx)
//!   w   := fun jx => W (hcDecode n jx)           (ANY weight W : HCPoint n → Rat)
//!   m   := Fin.sum (2^n) chi
//! ```
//!
//! where `D_i f x := pm (f x) − pm (f (hcFlip n x i)) ∈ {0,±2}` and
//! `half := Rat.inv Rat.two`. Because `subsetSum n G ≡ Fin.sum (2^n) (fun j =>
//! G (hcDecode n j))` *reducibly* (the def of `subsetSum`), the conclusion's
//! `Fin.sum (2^n) (fun jx => body (hcDecode n jx))` is def-eq to
//! `subsetSum n (fun x => body x)`, so STEP 2 reads, after that fold:
//!
//! ```text
//! BoolAnalysis.dualhc_step2_holder_inst :
//!   ∀ (n : Nat) (f : BoolFn n) (i : Fin n) (w : HCPoint n → Rat),
//!     Rat.le
//!       (pow4 (subsetSum n (fun x => Rat.mul (Rat.mul (D_i f x) half) (w x))))
//!       (Rat.mul (Rat.mul m (Rat.mul m m))
//!                (subsetSum n (fun x => pow4 (w x))))
//!     where m := subsetSum n (fun x => Rat.mul (Rat.mul (D_i f x) (D_i f x))
//!                                              (Rat.mul half half))
//! ```
//!
//! i.e. `(Σ_x (D_i f x · half)·w x)⁴ ≤ m³ · Σ_x (w x)⁴`, with `m = ¼·Σ_x (D_i f x)²`
//! the un-normalized (`2^n·Inf_i`-proportional) support measure. The genuine
//! analytic content is R2 itself; STEP 2 supplies the SIX hypotheses pointwise:
//!
//!   * H1  `chi = e·e`         := `half_deriv_chi_eq_sq g`
//!   * H2  `e·chi = e`         := `half_deriv_e_chi_eq_e g (deriv_cube_eq_four_deriv a b)`
//!   * H3  `chi·chi = chi`     := `half_deriv_chi_sq_eq_chi g (disagree_sq_self_eq_four_mul a b)`
//!   * H4  `chi ≤ 1`           := `half_deriv_chi_le_one g (disagree_sq_le_four a b)`
//!   * H5  `0 ≤ m`             := `Fin.sum_nonneg` over `mul_nonneg (sq_nonneg g)(sq_nonneg half)`
//!   * H6  `m = Fin.sum (2^n) chi` := `Eq.refl` (m is THAT sum, def-eq through subsetSum)
//!
//! with `g := D_i f (hcDecode n jx) = pm a − pm b`, `a := f (hcDecode n jx)`,
//! `b := f (hcFlip n (hcDecode n jx) i)`. Every leaf is a landed `Constructive`
//! empty-closure Theorem (R2 + the GLUE-4 HALVED bridges + the integer `{0,±2}`
//! cube atoms + `Fin.sum_nonneg`/`Rat.mul_nonneg`/`Rat.sq_nonneg`), so STEP 2 is
//! `Constructive` with EMPTY admitted-axiom closure. No axiom added or removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for STEP 2. The `D_i f` / `subsetSum` / `half` spellings are
/// byte-identical to `boolean_analysis_deriv_4norm.rs`, `boolean_analysis_kkl_dualhc_half2.rs`
/// and `boolean_analysis_subset_sum.rs` so every leaf instance is def-eq.
struct Step2Consts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_two: Expr,
    rat_inv: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_nonneg: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    hc_flip: Expr,
    pm: Expr,
    subset_sum: Expr,
    mul_nonneg: Expr,
    sq_nonneg: Expr,
    // landed lemma const-heads.
    holder: Expr,
    half_chi_eq_sq: Expr,
    half_e_chi_eq_e: Expr,
    half_chi_sq_eq_chi: Expr,
    half_chi_le_one: Expr,
    deriv_cube: Expr,
    disagree_sq_self: Expr,
    disagree_sq_le_four: Expr,
    // STEP-2b: m = subsetSum(ind∘disagree) bridge atoms.
    ind: Expr,
    bool_beq: Expr,
    bool_not: Expr,
    subset_sum_congr: Expr,
    mul_comm: Expr,
    mul_assoc: Expr,
    mul_one: Expr,
    congr_arg: Expr,
    disagree_sq_bridge: Expr,
    four_half_sq_eq_one: Expr,
}

impl Step2Consts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_two: k("Rat.two"),
            rat_inv: k("Rat.inv"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            mul_nonneg: k("Rat.mul_nonneg"),
            sq_nonneg: k("Rat.sq_nonneg"),
            holder: k("BoolAnalysis.sum_prod_pow4_le_m3_sumpow4"),
            half_chi_eq_sq: k("BoolAnalysis.half_deriv_chi_eq_sq"),
            half_e_chi_eq_e: k("BoolAnalysis.half_deriv_e_chi_eq_e"),
            half_chi_sq_eq_chi: k("BoolAnalysis.half_deriv_chi_sq_eq_chi"),
            half_chi_le_one: k("BoolAnalysis.half_deriv_chi_le_one"),
            deriv_cube: k("BoolAnalysis.deriv_cube_eq_four_deriv"),
            disagree_sq_self: k("BoolAnalysis.disagree_sq_self_eq_four_mul"),
            disagree_sq_le_four: k("BoolAnalysis.disagree_sq_le_four"),
            ind: k("BoolAnalysis.ind"),
            bool_beq: k("Bool.beq"),
            bool_not: k("Bool.not"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            mul_comm: k("Rat.mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_one: k("Rat.mul_one"),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![
                    crate::level::Level::succ(crate::level::Level::zero()),
                    crate::level::Level::succ(crate::level::Level::zero()),
                ],
            ),
            disagree_sq_bridge: k("BoolAnalysis.disagree_sq_bridge"),
            four_half_sq_eq_one: k("BoolAnalysis.four_half_sq_eq_one"),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.order.sub(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    #[cfg(test)]
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.order.rat_zero.clone(), a)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    /// `half := Rat.inv Rat.two`. Byte-matches `Half2Consts::half`.
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    /// `2^n := Nat.pow 2 n`. Byte-matches `subsetSum`'s `pow2`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Fin.sum N h`.
    fn fin_sum(&self, n: &Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), h])
    }
    /// `subsetSum n G`.
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `t·t`.
    fn sq(&self, t: Expr) -> Expr {
        self.mul(t.clone(), t)
    }
    /// `(t·t)·(t·t)`.
    fn pow4(&self, t: Expr) -> Expr {
        let s = self.sq(t);
        self.mul(s.clone(), s)
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    /// `hcDecode n j`.
    fn decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `hcFlip n x i`.
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    /// `a := f x`, `b := f (hcFlip n x i)` — the two Bool args of the deriv atoms.
    fn deriv_args(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> (Expr, Expr) {
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, x, i));
        (fx, fflip)
    }
    /// `D_i f x := pm (f x) − pm (f (hcFlip n x i))`. Byte-matches
    /// `DerivConsts::deriv`.
    fn deriv(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let (a, b) = self.deriv_args(n, f, x, i);
        self.sub(self.pm_of(a), self.pm_of(b))
    }
    /// `Fin.sum_nonneg N f h : 0 ≤ Fin.sum N f`.
    fn sum_nonneg(&self, n: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_nonneg.clone(), [n.clone(), f, h])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `@Eq.refl Rat x : x = x`.
    fn eq_refl(&self, x: Expr) -> Expr {
        Expr::apps(self.order.eq_refl.clone(), [self.rat(), x])
    }
    /// `sum_prod_pow4_le_m3_sumpow4 N e w chi m H1..H6`.
    fn holder(
        &self,
        n_pow: &Expr,
        e: Expr,
        w: Expr,
        chi: Expr,
        m: Expr,
        h1: Expr,
        h2: Expr,
        h3: Expr,
        h4: Expr,
        h5: Expr,
        h6: Expr,
    ) -> Expr {
        Expr::apps(
            self.holder.clone(),
            [n_pow.clone(), e, w, chi, m, h1, h2, h3, h4, h5, h6],
        )
    }

    // ── STEP-2b helpers (m = subsetSum(ind∘disagree)) ───────────────────────
    /// `four := Rat.mk (Int.ofNat 4) 1` — byte-matches `disagree_sq_bridge`'s 4.
    fn four(&self) -> Expr {
        let mut four_nat = self.nat_zero.clone();
        for _ in 0..4 {
            four_nat = Expr::app(self.nat_succ.clone(), four_nat);
        }
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), one],
        )
    }
    fn ind_of(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    /// `disagree x := Bool.not (Bool.beq (f x) (f (hcFlip n x i)))`. Byte-matches
    /// `Influence`'s summand and `DerivConsts::disagree`.
    fn disagree(&self, n: &Expr, f: &Expr, x: &Expr, i: &Expr) -> Expr {
        let (a, b) = self.deriv_args(n, f, x, i);
        Expr::app(
            self.bool_not.clone(),
            Expr::apps(self.bool_beq.clone(), [a, b]),
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    /// `congrArg.{1,1} Rat Rat a b f (h:a=b) : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }
    /// `disagree_sq_bridge a b : 4·ind(disagree) = g·g`.
    fn bridge(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.disagree_sq_bridge.clone(), [a, b])
    }
    /// `subsetSum_congr n g h hyp : subsetSum n g = subsetSum n h`.
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, hyp: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, hyp])
    }
    /// Build `fun (t : Rat) => f(t)` for `congrArg`.
    fn lam_rat<F: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }
}

impl Environment {
    /// Register STEP 2 (`dualhc_step2_holder_inst`). Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_step2(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_step2_holder_inst()?;
        self.register_dualhc_step2_m_eq_disagree_mass()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_step2_holder_inst` — R2 pinned at the halved
    /// derivative over the `2^n` cube index. See the module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_step2_holder_inst(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_step2_holder_inst");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, hcFlip, hcDecode, BoolFn, HCPoint
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?; // subsetSum (reducible def to Fin.sum)
        self.init_fin_sum()?; // Fin.sum, Fin.sum_nonneg
        self.init_boolean_analysis_order_toolkit()?; // mul_nonneg, sq_nonneg
        self.init_algebra_rat_halves()?; // Rat.two, Rat.inv (half spelling)
        self.register_sum_prod_pow4_le_m3_sumpow4()?; // R2
        self.init_boolean_analysis_kkl_dualhc_half2()?; // GLUE-4 HALVED (H1-H4)
        self.init_boolean_analysis_kkl_dualhc_halfderiv()?; // deriv_cube_eq_four_deriv (H2)
        self.register_disagree_sq_self_eq_four_mul()?; // H3 integer hyp
                                                       // disagree_sq_le_four (H4 integer hyp) is registered by half2 above.

        let c = Step2Consts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_step2(&c, false),
            value: build_step2(&c, true),
        })
    }

    /// `BoolAnalysis.dualhc_step2_m_eq_disagree_mass` — STEP-2b, the bridge
    /// identifying R2's support measure `m` with the un-normalized influence
    /// numerator (`= 2^n·Inf_i`):
    ///
    /// ```text
    /// ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
    ///   subsetSum n (fun x => Rat.mul (Rat.mul (D_i f x) (D_i f x))
    ///                                 (Rat.mul half half))
    ///   = subsetSum n (fun x => ind (Bool.not (Bool.beq (f x) (f (hcFlip n x i)))))
    /// ```
    ///
    /// i.e. `m = Σ_x ind(disagree x)`. Proof: `subsetSum_congr` over the pointwise
    /// ring identity `(g·g)·(h·h) = ind(disagree x)` for `g := pm a − pm b`,
    /// `a := f x`, `b := f (hcFlip n x i)`, `h := half`:
    /// `(g·g)·(h·h) = (4·ind)·(h·h)` [`disagree_sq_bridge` symm, congr] `=
    /// (ind·4)·(h·h)` [`mul_comm` congr] `= ind·(4·(h·h))` [`mul_assoc`] `= ind·1`
    /// [`four_half_sq_eq_one` congr] `= ind` [`mul_one`]. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_step2_m_eq_disagree_mass(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_step2_m_eq_disagree_mass");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, ind, hcFlip, BoolFn, HCPoint, Bool.beq/not
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_beq()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?; // mul_comm, mul_assoc, mul_one
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_disagree_sq_bridge()?; // 4·ind = g·g
        self.register_four_half_sq_eq_one()?; // 4·(h·h) = 1

        let c = Step2Consts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_m_eq_mass(&c, false),
            value: build_m_eq_mass(&c, true),
        })
    }
}

// STEP-2 holder-instantiation term builders live in the sibling build file
// to keep each file under the 500-line convention.
include!("boolean_analysis_kkl_dualhc_step2_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_step2()
            .expect("init_boolean_analysis_kkl_dualhc_step2");
        env.init_boolean_analysis_kkl_dualhc_step2()
            .expect("idempotent");
        env
    }

    fn assert_constructive_theorem(env: &Environment, name: &str) {
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
    fn test_dualhc_step2_holder_inst_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.dualhc_step2_holder_inst");
    }

    #[test]
    fn test_dualhc_step2_m_eq_disagree_mass_is_constructive_theorem() {
        assert_constructive_theorem(&env(), "BoolAnalysis.dualhc_step2_m_eq_disagree_mass");
    }
}
