// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3,4)` campaign — the norm-split residual (D) of the §11.1
//! `H_CLOSE` discharge: `norm43_cubed (m+1) F s r hs = (Σ_k W_k)³`, the NNReal
//! `2^{m+1} = 2^m + 2^m` reindex of the `4/3`-norm cube.
//!
//! `BoolAnalysis.finSum_two_point_close` (the §11.1 algebraic skeleton) consumes
//! the minor premise `h_split : Ncubed = ((Σ W)·(Σ W))·(Σ W)`. At the `H_CLOSE`
//! instance `Ncubed := norm43_cubed (m+1) F s r hs`, and the natural `W` is the
//! per-low-coordinate sum of the two `4/3`-norm half-contributions:
//!
//! ```text
//!   W_k := contribution(decode (m+1) (castP (castAdd (2^m)(2^m) k)))
//!        + contribution(decode (m+1) (castP (addNat  (2^m)(2^m) k)))
//! ```
//!
//! where `castP : Fin (2^m + 2^m) → Fin (2^(m+1))` is the `NNReal.finSum_cast`
//! transport along `(Nat.pow_two_succ m).symm` and `contribution g … x :=
//! pow43Gen |g x| (s x)(r x) …` is `norm43`'s `cube_summand`. This module proves
//!
//! ```text
//! BoolAnalysis.norm43_cubed_succ_split :
//!   ∀ (m : Nat)(F s r : HCPoint (m+1) → Rat)(hs : ∀ x, 0 ≤ s x),
//!     @Eq NNReal (norm43_cubed (m+1) F s r hs)
//!                (((NNReal.finSum (2^m) W)·(NNReal.finSum (2^m) W))
//!                 · (NNReal.finSum (2^m) W))
//! ```
//!
//! It is a STRUCTURAL `Eq` — no inequality, no root, no AM-GM. The new content is
//! the NNReal `2^{m+1}`-cube split `BoolAnalysis.nnFinSumPow2SuccSplit` (the
//! NNReal dual of the landed Rat `BoolAnalysis.finSumPow2SuccSplit`, built from
//! the landed `NNReal.finSum_cast` / `NNReal.finSum_split_add`) plus the
//! `NNReal.finSum_add` merge of the two halves into `Σ_k W_k`, then a cube
//! congruence (`norm43_cubed`/`norm43` are reducible, so `Ncubed ≡ (Σ_{2^{m+1}}
//! Φ)³` by δ-unfold).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Declaration::Axiom`. FORBIDDEN here: `Rat.dist`,
//! `Real` / `Real.sqrt`, `NNReal.sqrt`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants + smart-constructors for the norm-split residual (D).
struct NsConsts {
    nat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_add: Expr,
    nat_pow: Expr,
    two: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_abs: Expr,
    rat_abs_nonneg: Expr,
    fin: Expr,
    fin_cast_add: Expr,
    fin_add_nat: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_finsum: Expr,
    nnreal_finsum_cast: Expr,
    nnreal_finsum_split: Expr,
    nnreal_finsum_add: Expr,
    pow43_gen: Expr,
    norm43_cubed: Expr,
    pow_two_succ: Expr,
    l1: Level,
}

impl NsConsts {
    fn new() -> Self {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let n1 = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), n1);
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_succ,
            nat_zero,
            nat_add: k("Nat.add"),
            nat_pow: k("Nat.pow"),
            two,
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_abs: k("Rat.abs"),
            rat_abs_nonneg: k("Rat.abs_nonneg"),
            fin: k("Fin"),
            fin_cast_add: k("Fin.castAdd"),
            fin_add_nat: k("Fin.addNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_finsum: k("NNReal.finSum"),
            nnreal_finsum_cast: k("NNReal.finSum_cast"),
            nnreal_finsum_split: k("NNReal.finSum_split_add"),
            nnreal_finsum_add: k("NNReal.finSum_add"),
            pow43_gen: k("NNReal.pow43Gen"),
            norm43_cubed: k("BoolAnalysis.norm43_cubed"),
            pow_two_succ: k("Nat.pow_two_succ"),
            l1: Level::succ(Level::zero()),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn fn_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn nat_add_(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a.clone(), b.clone()])
    }
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn cube(&self, t: &Expr) -> Expr {
        self.nnmul(&self.nnmul(t, t), t)
    }
    fn finsum(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [n.clone(), f.clone()])
    }
    fn forall_scale_nonneg_ty(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let mut d = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let zero_le = Expr::apps(
            self.rat_le.clone(),
            [self.rat_zero.clone(), Expr::app(s.clone(), x)],
        );
        d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, zero_le))
    }
    fn decode(&self, n: &Expr, jx: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), jx.clone()])
    }
    /// `pow43Gen |F x| (s x)(r x) (abs_nonneg (F x)) (hs x)` — `norm43`'s
    /// per-point `cube_summand` contribution (byte-for-byte `Norm43Consts`).
    fn contribution(&self, f: &Expr, s: &Expr, r: &Expr, hs: &Expr, x: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let abs_fx = Expr::app(self.rat_abs.clone(), fx.clone());
        let sx = Expr::app(s.clone(), x.clone());
        let rx = Expr::app(r.clone(), x.clone());
        let hx = Expr::app(self.rat_abs_nonneg.clone(), fx);
        let hsx = Expr::app(hs.clone(), x.clone());
        Expr::apps(self.pow43_gen.clone(), [abs_fx, sx, rx, hx, hsx])
    }
    /// `cube_summand n F s r hs := fun (jx : Fin (2^n)) => contribution … (decode n jx)`
    /// — byte-for-byte `norm43`'s summand, so `norm43 n F s r hs ≡ finSum (2^n) Φ`.
    fn cube_summand(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        r: &Expr,
        hs: &Expr,
    ) -> Expr {
        let fin = self.fin_of(&self.pow2(n));
        let mut b = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = b.fresh_local(fin.clone());
        let x = self.decode(n, &jx);
        let body = self.contribution(f, s, r, hs, &x);
        b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin, body))
    }
    /// `norm43_cubed n F s r hs : NNReal`.
    fn norm43_cubed_app(&self, n: &Expr, f: &Expr, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.norm43_cubed.clone(),
            [n.clone(), f.clone(), s.clone(), r.clone(), hs.clone()],
        )
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                h1,
                h2,
            ],
        )
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@congrArg NNReal NNReal from to f h`.
    fn congr_arg_nn(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                from.clone(),
                to.clone(),
                f,
                h,
            ],
        )
    }

    /// `castP m mapped : Fin (2^(m+1))` — the `2^m+2^m → 2^(m+1)` transport, the
    /// `NNReal.finSum_cast` summand's `cast_{b→a}` (`@Eq.ndrec Nat (2^m+2^m) (fun
    /// k => Fin k) mapped (2^(m+1)) (pow_two_succ m).symm`). Byte-for-byte the Rat
    /// `finSumPow2SuccSplit` `castP`.
    fn cast_p(&self, parent: &EnvDeclBuilder, m: &Expr, mapped: &Expr) -> Expr {
        let p2m = self.pow2(m);
        let sum_pow = self.nat_add_(&p2m, &p2m);
        let sm = self.succ(m);
        let p2sm = self.pow2(&sm);
        let e_fwd = Expr::app(self.pow_two_succ.clone(), m.clone());
        let e = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nat.clone(), p2sm.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (k_id, k) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&k);
            mb.finish_child(mb.mk_lam(k_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.nat.clone(), sum_pow, motive, mapped.clone(), p2sm, e],
        )
    }
}

include!("boolean_analysis_hc43_norm_split_build.rs");

/// The concrete merged weight `W := fun (k : Fin (2^m)) =>
///   contribution(decode (m+1) (castP (castAdd k)))
/// + contribution(decode (m+1) (castP (addNat k)))` — byte-for-byte the `W` that
/// `BoolAnalysis.norm43_cubed_succ_split` (premise D) pins, exposed so the
/// `hc43_core_step_v2` discharge passes the SAME `W` to
/// `finSum_two_point_close` (D's `h_split` then aligns positionally). Parametric
/// in a parent builder + the `(m, F, s, r, hs)` binders.
pub(super) fn norm43_merged_w(
    parent: &EnvDeclBuilder,
    m: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
) -> Expr {
    let c = NsConsts::new();
    merged_w_fn(&c, parent, m, f, s, r, hs)
}

impl Environment {
    /// Register `BoolAnalysis.nnFinSumPow2SuccSplit` and
    /// `BoolAnalysis.norm43_cubed_succ_split` (premise (D) of §11.1). Idempotent;
    /// both kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub fn init_boolean_analysis_hc43_norm_split(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum_split()?; // NNReal.finSum_cast / finSum_split_add
        self.init_algebra_nnreal_finsum_add()?; // NNReal.finSum_add
        self.init_boolean_analysis_norm43()?; // norm43, norm43_cubed, pow43Gen, hcDecode
        self.register_hc_sum_split_theorem()?; // Nat.pow_two_succ, Fin.castAdd/addNat
        self.init_eq()?;

        let c = NsConsts::new();
        self.register_nn_finsum_pow2_succ_split(&c)?;
        self.register_norm43_cubed_succ_split(&c)?;
        Ok(())
    }

    fn register_nn_finsum_pow2_succ_split(&mut self, c: &NsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.nnFinSumPow2SuccSplit");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_nn_pow2_succ_split(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_norm43_cubed_succ_split(&mut self, c: &NsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.norm43_cubed_succ_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_norm43_cubed_succ_split(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "BoolAnalysis.nnFinSumPow2SuccSplit",
        "BoolAnalysis.norm43_cubed_succ_split",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_norm_split()
            .expect("init_boolean_analysis_hc43_norm_split");
        env.init_boolean_analysis_hc43_norm_split()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_norm43_cubed_succ_split_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_norm43_cubed_succ_split_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
