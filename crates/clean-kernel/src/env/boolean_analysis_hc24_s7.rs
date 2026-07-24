// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **S7 parallelogram-summed** identity of the
//! `hc24_core` operator induction.
//!
//! S7 collapses the two square-sums `SG`, `SH` of the `gPart` / `liftH` legs
//! into the single `(n+1)`-cube square-sum `SF'`:
//!
//! ```text
//! BoolAnalysis.hc24S7 : ∀ (n : Nat) (F : HCPoint (n+1) → Rat),
//!   @Eq Rat (Rat.add SG SH) (Rat.mul (1+1) SF')
//! ```
//!
//! with
//! - `SG := Fin.sum (2^n) (fun x' => sq (gPart n F (hcDecode n x')))`,
//! - `SH := Fin.sum (2^n) (fun x' => sq (liftH n F (hcDecode n x')))`,
//! - `SF' := Fin.sum (2^(n+1)) (fun jx => sq (F (hcDecode (n+1) jx)))`,
//! - `sq x := x·x`, `(1+1) := Rat.add Rat.one Rat.one`.
//!
//! ## Proof route
//!
//! Abbreviate, per outer point `x' : Fin (2^n)` (write `dec := hcDecode n`):
//! `m x' := F (extendF n (dec x'))`, `c x' := F (extendT n (dec x'))`, and
//! `mSq x' := sq (m x')`, `cSq x' := sq (c x')`.
//!
//! 1. `Eq.symm (Fin.sum_add (2^n) gSq hSq)` : `SG + SH = Σ_{x'}(gSq x' + hSq x')`.
//! 2. `Fin.sum_congr` with the pointwise parallelogram
//!    `Rat.add_sq_add_sub_sq (m x') (c x')` (which proves
//!    `(m+c)·(m+c) + (m−c)·(m−c) = (1+1)·(m·m) + (1+1)·(c·c)`, **defeq** to
//!    `gSq x' + hSq x' = (1+1)·mSq x' + (1+1)·cSq x'` since `gPart` / `liftH` /
//!    `Rat.sub` are reducible) : `Σ_{x'}(gSq + hSq) = Σ_{x'}((1+1)·mSq + (1+1)·cSq)`.
//! 3. `Fin.sum_add (2^n) (fun x'=>(1+1)·mSq) (fun x'=>(1+1)·cSq)` :
//!    `= Σ_{x'}((1+1)·mSq) + Σ_{x'}((1+1)·cSq)`.
//! 4. `Fin.sum_smul (2^n) (1+1) mSq` (and `cSq`) : `= (1+1)·SM + (1+1)·SC`,
//!    `SM := Σ_{x'} mSq`, `SC := Σ_{x'} cSq`.
//! 5. `finSumPow2SuccSplit Fsq` (`Fsq := fun jx => sq (F (hcDecode (n+1) jx))`)
//!    : `SF' = Σ_{x'}(Fsq (castP (castAdd x'))) + Σ_{x'}(Fsq (castP (addNat x')))`,
//!    then `Fin.sum_congr` with the decode↔extend bridges
//!    `hcDecode_castP_castAdd_extendF` / `_addNat_extendT` rewrites each LOW/HIGH
//!    summand to `mSq` / `cSq`, giving `SF' = SM + SC`.
//! 6. `Rat.left_distrib (1+1) SM SC` : `(1+1)·(SM+SC) = (1+1)·SM + (1+1)·SC`;
//!    `cong_right ((1+1)·_)` of step 5 : `(1+1)·(SM+SC) = (1+1)·SF'`. Chain
//!    steps 1–6: `SG + SH = (1+1)·SF'`.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! leaves are `Fin.sum_add`, `Fin.sum_smul`, `Fin.sum_congr`,
//! `finSumPow2SuccSplit`, `Rat.add_sq_add_sub_sq`, `Rat.left_distrib`, the two
//! decode↔extend bridges, and the `Eq`/`congrArg` built-ins.

use super::boolean_analysis_hc24_core_base::Hc24Consts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants + smart-constructors for the S7 identity.
struct S7Consts {
    o: Hc24Consts,
    l1: Level,
    cast_add: Expr,
    add_nat: Expr,
    g_part: Expr,
    lift_h: Expr,
    extend_f: Expr,
    extend_t: Expr,
}

impl S7Consts {
    fn new() -> Self {
        Self {
            o: Hc24Consts::new(),
            l1: Level::succ(Level::zero()),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            g_part: Expr::const_(Name::from_string("BoolAnalysis.gPart"), vec![]),
            lift_h: Expr::const_(Name::from_string("BoolAnalysis.liftH"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.o.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    fn two(&self) -> Expr {
        self.add(self.o.rat_one.clone(), self.o.rat_one.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            n.clone(),
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        self.o.fin_of(n)
    }
    fn pow2(&self, n: &Expr) -> Expr {
        self.o.pow2(n)
    }
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        self.o.sum(n, f)
    }
    fn sq(&self, x: &Expr) -> Expr {
        self.o.sq(x)
    }
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        self.o.decode(n, k)
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.o.eq_rat(l, r)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.o.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans(a, b, cc, h1, h2)
    }

    fn g_part_at(&self, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.g_part.clone(), [n.clone(), f.clone(), x.clone()])
    }
    fn lift_h_at(&self, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.lift_h.clone(), [n.clone(), f.clone(), x.clone()])
    }
    fn ext_f(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.extend_f.clone(), [n.clone(), x.clone()])
    }
    fn ext_t(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.extend_t.clone(), [n.clone(), x.clone()])
    }

    /// `Fin.sum_add n f g : Σ(fun i => f i + g i) = Σ f + Σ g`.
    fn sum_add(&self, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            [n.clone(), f.clone(), g.clone()],
        )
    }
    /// `Fin.sum_smul n c f : Σ(fun i => c·(f i)) = c·Σ f`.
    fn sum_smul(&self, n: &Expr, c: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            [n.clone(), c.clone(), f.clone()],
        )
    }
    /// `Fin.sum_congr n f g h : Σ f = Σ g`.
    fn sum_congr(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `finSumPow2SuccSplit n F : Σ_{2^(n+1)} F = Σ_{2^n} LOW + Σ_{2^n} HIGH`.
    fn pow2_split(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.finSumPow2SuccSplit"),
                vec![],
            ),
            [n.clone(), f.clone()],
        )
    }
    /// `Rat.add_sq_add_sub_sq m c : (m+c)(m+c)+(m−c)(m−c) = (1+1)(m·m)+(1+1)(c·c)`.
    fn parallelogram(&self, m: &Expr, c: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add_sq_add_sub_sq"), vec![]),
            [m.clone(), c.clone()],
        )
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn ldist(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            [a.clone(), b.clone(), c.clone()],
        )
    }
    /// The decode↔extend bridge `hcDecode (n+1) (castP (idx k)) = extend* n (dec k)`.
    fn bridge(&self, low: bool, n: &Expr, k: &Expr) -> Expr {
        let name = if low {
            "BoolAnalysis.hcDecode_castP_castAdd_extendF"
        } else {
            "BoolAnalysis.hcDecode_castP_addNat_extendT"
        };
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![]),
            [n.clone(), k.clone()],
        )
    }

    /// `@congrArg Rat Rat from to f h : f from = f to`.
    fn congr_arg(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat(), self.rat(), from, to, f, h],
        )
    }
    /// `@congrArg (HCPoint (n+1)) Rat from to f h : f from = f to`.
    fn congr_arg_pt(&self, sn: &Expr, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.o.hcpoint_of(sn), self.rat(), from, to, f, h],
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.hc24S7` — the S7 parallelogram-summed identity
    /// `SG + SH = (1+1)·SF'`. Idempotent; axiom-free.
    pub(crate) fn register_hc24_s7(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_add, Fin.sum_smul, Fin.sum_congr
        self.register_fin_sum_pow2_succ_split()?; // finSumPow2SuccSplit
        self.init_boolean_analysis_fourth_power()?; // Rat.add_sq_add_sub_sq
        self.init_boolean_analysis_peel_parts()?; // gPart
        self.register_lift_h()?; // liftH
        self.init_boolean_analysis_noise_extend_bridge()?; // decode↔extend bridges
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.left_distrib
        }
        self.init_boolean_analysis_hc_bounds()?; // Rat order/le surface (for Hc24Consts)

        let name = Name::from_string("BoolAnalysis.hc24S7");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = S7Consts::new();
        let (type_, value) = build_s7(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

include!("boolean_analysis_hc24_s7_build.rs");

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc24_s7_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_hc24_s7().expect("register_hc24_s7");
        env.register_hc24_s7().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc24S7");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc24S7 proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
