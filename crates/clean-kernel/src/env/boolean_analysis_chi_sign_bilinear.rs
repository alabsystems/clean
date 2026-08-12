// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SIGN-side bilinear induction `subsetSum_chi_sign_bilinear` — the dual of
//! `subsetSum_chi_bilinear`.
//!
//!   `∀ (n : Nat) (S T : HCPoint n),`
//!   `  subsetSum n (fun x => chi n S x · chi n T x)`
//!   `    = Fin.prod n (fun i => 1 + pm(S i)·pm(T i))`
//!
//! Gates `S, T` are fixed; the SUM ranges over the SIGN cube point `x`. The
//! gate-side `subsetSum_chi_bilinear` instead fixes the two signs `x, y` and
//! sums over the gate `S`. Both land the SAME product form, so the diagonal
//! (`2^n`) and off-diagonal (`= 0` for `S ≠ T`) values are then read off by the
//! EXISTING `prod_diag_eq_cube` / `prod_offdiag_eq_zero` collapse.
//!
//! `Nat.rec` on `n`, mirroring the gate-side induction exactly with the SIGN
//! split (`subsetSum_split` is carrier-agnostic — it splits the cube sum by the
//! top decoded bit regardless of whether the point is read as a gate or a sign):
//!
//!   subsetSum (k+1) (χ_S·χ_T)
//!     →[subsetSum_split]  Σ_j LO(j) + Σ_j HI(j)
//!     →[sum_add⁻¹]        Σ_j (LO(j) + HI(j))
//!     →[combine + comm]   Σ_j  c_top · prefix(j)
//!     →[sum_smul]         c_top · Σ_j prefix(j)
//!     →[IH]               c_top · Fin.prod k (1 + pm(rS i)pm(rT i))
//!     →[comm + prod_succ⁻¹] Fin.prod (k+1) (1 + pm(S i)pm(T i))
//!
//! where `c_top = 1 + pm(S last)·pm(T last)` and the per-index combine
//! `chi_sign_bilinear_pair_combine` collapses `LO(j)+HI(j) = prefix(j)·c_top`
//! using the SIGN-side peel `chi_sign_pair_succ` and the SIGN-side per-coordinate
//! pair sum `chi_sign_factor_pair_sum`. Kernel-checked, constructive (empty
//! admitted-axiom closure).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Consts for the sign-side combine + induction (decode/restrict/testBit + the
/// sign-side peel / pair-sum leaves).
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct SignBiConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    pm: Expr,
    btrue: Expr,
    bfalse: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_add: Expr,
    two: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_last: Expr,
    fin_cast_succ: Expr,
    cast_add: Expr,
    add_nat: Expr,
    hc_decode: Expr,
    chi: Expr,
    subset_sum: Expr,
    fin_sum: Expr,
    fin_prod: Expr,
    nat_rec: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
    #[cfg(test)]
    bool_rec1: Expr,
    congr_arg_br: Expr,
    congr_arg_hr: Expr,
    eq_trans_bool: Expr,
    testbit: Expr,
    testbit_lt_pow: Expr,
    testbit_add_self: Expr,
    restrict_lo: Expr,
    restrict_hi: Expr,
    decode_lo_bit: Expr,
    decode_hi_bit: Expr,
    left_distrib: Expr,
    subset_sum_split: Expr,
    sum_add: Expr,
    sum_smul: Expr,
    sum_congr: Expr,
    prod_succ: Expr,
    sign_peel: Expr,
    sign_pair_sum: Expr,
    base_zero: Expr,
    eq1: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    #[cfg(test)]
    eq_refl1: Expr,
    congr_arg_rr: Expr,
    rat_mul_comm: Expr,
}

impl SignBiConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let z = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let s = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let two = Expr::app(s.clone(), Expr::app(s.clone(), z));
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            nat_succ: s,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            two,
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            chi: Expr::const_(Name::from_string("BoolAnalysis.chi"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_prod: Expr::const_(Name::from_string("Fin.prod"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            #[cfg(test)]
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            congr_arg_br: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr_arg_hr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            testbit_lt_pow: Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
            testbit_add_self: Expr::const_(
                Name::from_string("Nat.testBit_add_two_pow_self"),
                vec![],
            ),
            restrict_lo: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_restrict_castAdd"),
                vec![],
            ),
            restrict_hi: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_restrict_addNat"),
                vec![],
            ),
            decode_lo_bit: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_castP_castAdd"),
                vec![],
            ),
            decode_hi_bit: Expr::const_(
                Name::from_string("BoolAnalysis.hcDecode_castP_addNat"),
                vec![],
            ),
            left_distrib: Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            subset_sum_split: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_split"),
                vec![],
            ),
            sum_add: Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            sum_smul: Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            prod_succ: Expr::const_(Name::from_string("Fin.prod_succ"), vec![]),
            sign_peel: Expr::const_(Name::from_string("BoolAnalysis.chi_sign_pair_succ"), vec![]),
            sign_pair_sum: Expr::const_(
                Name::from_string("BoolAnalysis.chi_sign_factor_pair_sum"),
                vec![],
            ),
            base_zero: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_chi_sign_bilinear_zero"),
                vec![],
            ),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            #[cfg(test)]
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            congr_arg_rr: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            rat_mul_comm: Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    fn chi(&self, n: Expr, s: Expr, x: Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n, s, x])
    }
    fn pm(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm_rat(&self, l: Expr, r: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), l, r, h])
    }
    fn congr_rat(&self, from: Expr, to: Expr, motive: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_rr.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, motive, h],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn fsum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    /// `fun (i : Fin n) => p (Fin.castSucc n i)`.
    fn restrict(&self, parent: &EnvDeclBuilder, n: &Expr, p: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cs = Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i]);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, Expr::app(p.clone(), cs)))
    }
    /// `factor sb xb = @Bool.rec (fun _ => Rat) Rat.one (1 - 2·⟦xb⟧) sb`.
    fn factor(&self, parent: &EnvDeclBuilder, sb: Expr, xb: Expr) -> Expr {
        let l1 = Level::succ(Level::zero());
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1]);
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, _t) = mb.fresh_local(self.bool_.clone());
            mb.finish_child(mb.mk_lam(
                t_id,
                BinderInfo::Default,
                self.bool_.clone(),
                self.rat.clone(),
            ))
        };
        let rat_two = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    self.two.clone(),
                ),
                Expr::app(
                    self.nat_succ.clone(),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                ),
            ],
        );
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let embed = Expr::apps(
            bool_rec.clone(),
            [motive.clone(), rat_zero, self.rat_one.clone(), xb],
        );
        let signed = Expr::apps(
            Expr::const_(Name::from_string("Rat.sub"), vec![]),
            [self.rat_one.clone(), self.mul(rat_two, embed)],
        );
        Expr::apps(bool_rec, [motive, self.rat_one.clone(), signed, sb])
    }

    /// `castP n (idx_map (2^n) (2^n) j) : Fin (2^(n+1))`.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), j.clone()]);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), self.fin_of(&m)))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat.clone(), sum_pow, motive, mapped, p2sn, e],
        )
    }
    /// `hcDecode (n+1) (castP n idx_map j) : HCPoint (n+1)` — one cube SIGN half.
    fn decoded(&self, parent: &EnvDeclBuilder, n: &Expr, idx_map: &Expr, j: &Expr) -> Expr {
        let cp = self.cast_p(parent, n, idx_map, j);
        Expr::apps(self.hc_decode.clone(), [self.succ(n), cp])
    }
}

include!("boolean_analysis_chi_sign_bilinear_combine.rs");
include!("boolean_analysis_chi_sign_bilinear_ind.rs");

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_sign_bilinear`: the SIGN-side
    /// character bilinear collapse
    /// `Σ_x χ_S(x)·χ_T(x) = Π_i (1 + pm(S i)·pm(T i))`, by `Nat.rec` on `n`.
    /// Dual of `subsetSum_chi_bilinear`. Kernel-checked, constructive (empty
    /// admitted-axiom closure). Idempotent.
    pub(crate) fn register_subset_sum_chi_sign_bilinear_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_sign_bilinear");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_split()?;
        self.register_chi_sign_pair_succ_theorem()?;
        self.register_chi_sign_factor_pair_sum_theorem()?;
        self.register_hc_decode_split_theorems()?;
        self.register_subset_sum_chi_sign_bilinear_zero_theorem()?;
        self.register_chi_sign_bilinear_pair_combine_theorem()?;
        self.init_fin_sum()?;
        self.register_fin_prod_succ_theorem()?;

        // Re-entrancy guard: `init_boolean_analysis` may register this name.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = SignBiConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sign_ind_type(&c),
            value: build_sign_ind_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check(env: &Environment, name_str: &str) {
        let name = Name::from_string(name_str);
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name_str} must be a Theorem"
        );
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .unwrap_or_else(|e| panic!("{name_str} must type-check: {e:?}"));
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "{name_str} must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_sign_bilinear_zero_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init");
        env.register_subset_sum_chi_sign_bilinear_zero_theorem()
            .expect("register zero");
        check(&env, "BoolAnalysis.subsetSum_chi_sign_bilinear_zero");
    }

    #[test]
    fn test_sign_bilinear_pair_combine_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init");
        env.register_chi_sign_bilinear_pair_combine_theorem()
            .expect("register combine");
        check(&env, "BoolAnalysis.chi_sign_bilinear_pair_combine");
    }

    #[test]
    fn test_subset_sum_chi_sign_bilinear_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_subset_sum_chi_sign_bilinear_theorem()
            .expect("register bilinear");
        env.register_subset_sum_chi_sign_bilinear_theorem()
            .expect("idempotent");
        check(&env, "BoolAnalysis.subsetSum_chi_sign_bilinear");
    }
}
