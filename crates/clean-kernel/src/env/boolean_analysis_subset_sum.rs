// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `BoolAnalysis.subsetSum` — the unnormalized sum of a `Rat`-valued quantity
//! over all `2^n` subsets `S ⊆ [n]` of the hypercube index set.
//!
//! ```text
//! subsetSum (n : Nat) (G : HCPoint n -> Rat) : Rat :=
//!   Fin.sum (Nat.pow 2 n) (fun (j : Fin (Nat.pow 2 n)) => G (hcDecode n j))
//! ```
//!
//! THE KEY INSIGHT: a subset `S ⊆ [n]` IS its indicator `HCPoint n = Fin n ->
//! Bool`, and `hcDecode n` enumerates exactly the `2^n` such indicators. So the
//! "sum over all `2^n` subsets" is the SAME cube-sum apparatus that powers
//! `Expect` — `subsetSum n G` is literally the `Expect` numerator (`Expect n g
//! = subsetSum n g / 2^n`). Every `Fin.sum` lemma (`Fin.sum_succ`,
//! `Fin.sum_add`, `Fin.sum_congr`, `Fin.sum_smul`, …) and the cube-split
//! machinery (`hcSumSplit`) therefore applies verbatim to the SUBSET index.
//!
//! Registered as a reducible `Declaration::Definition`: no axiom added/removed,
//! so the soundness certificate's golden TCB is unchanged and it re-verifies
//! under C1. The closure bottoms out in `Fin.sum` / `hcDecode` (both reducible,
//! admitted-axiom-free), so any theorem stated over it stays
//! `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `BoolAnalysis.subsetSum (n : Nat) (G : HCPoint n -> Rat) : Rat`
    /// `:= Fin.sum (Nat.pow 2 n) (fun j => G (hcDecode n j))`.
    ///
    /// The unnormalized cube sum (the `Expect` numerator). Reusable: every
    /// `Fin.sum` lemma applies to the subset index. Idempotent.
    pub(crate) fn register_subset_sum(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.subsetSum"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Prerequisites: the foundational cube apparatus (HCPoint, hcDecode) and
        // the Fin.sum carrier.
        self.init_boolean_analysis_foundations()?;
        self.init_fin_sum()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);

        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);
        let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
        // `HCPoint n -> Rat`.
        let hcpoint_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcpoint_of(n), rat.clone());

        // Type: (n : Nat) -> (HCPoint n -> Rat) -> Rat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let g_type = hcpoint_to_rat(&n);
            let (g_id, _g) = b.fresh_local(g_type.clone());
            let r = b.mk_pi(g_id, BinderInfo::Default, g_type, rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n : Nat) (G : HCPoint n -> Rat) =>
        //   Fin.sum (Nat.pow 2 n) (fun (j : Fin (Nat.pow 2 n)) => G (hcDecode n j))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let g_type = hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_type.clone());

            // summand: fun (j : Fin (Nat.pow 2 n)) => G (hcDecode n j)
            let summand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_pow = Expr::app(fin.clone(), pow2(&n));
                let (j_id, j) = ch.fresh_local(fin_pow.clone());
                let decoded = Expr::apps(hc_decode.clone(), [n.clone(), j]);
                let body = Expr::app(g.clone(), decoded);
                let r = ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body);
                ch.finish_child(r)
            };

            let body = Expr::apps(fin_sum.clone(), [pow2(&n), summand]);
            let r = b.mk_lam(g_id, BinderInfo::Default, g_type, body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.subsetSum"));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.subsetSum"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.subsetSum_congr : forall (n : Nat) (G H : HCPoint n -> Rat),
    ///   (forall (S : HCPoint n), Eq Rat (G S) (H S)) ->
    ///   Eq Rat (subsetSum n G) (subsetSum n H)`.
    ///
    /// The congruence wrapper: `subsetSum` respects pointwise equality of its
    /// integrand. Proved by reducing both sides to `Fin.sum` (def-unfold) and
    /// applying `Fin.sum_congr` to the lifted hypothesis
    /// `H_j : G (hcDecode n j) = H (hcDecode n j)` (instantiate the pointwise
    /// hypothesis at `hcDecode n j`). Kernel-checked, constructive (closure ⊆
    /// `Fin.sum_congr` ∪ defs, all admitted-axiom-free). Idempotent.
    pub(crate) fn register_subset_sum_congr(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_congr");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        // `Fin.sum_congr` lives in the Fin.sum single-proof overlay.
        self.init_fin_sum()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let fin_sum_congr = Expr::const_(Name::from_string("Fin.sum_congr"), vec![]);
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
        let eq1 = Expr::const_(
            Name::from_string("Eq"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );

        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);
        let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
        let hcpoint_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcpoint_of(n), rat.clone());
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [rat.clone(), l, r]);

        // `fun (j : Fin (2^n)) => G (hcDecode n j)` — the Fin.sum summand for `G`.
        let decoded_fn = |b: &EnvDeclBuilder, n: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_pow = Expr::app(fin.clone(), pow2(n));
            let (j_id, j) = ch.fresh_local(fin_pow.clone());
            let decoded = Expr::apps(hc_decode.clone(), [n.clone(), j]);
            let body = Expr::app(g.clone(), decoded);
            ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
        };

        // Type: forall (n) (G H : HCPoint n -> Rat),
        //   (forall (S : HCPoint n), G S = H S) -> subsetSum n G = subsetSum n H
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let g_type = hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_type.clone());
            let (h_id, h) = b.fresh_local(g_type.clone());

            // hyp: forall (S : HCPoint n), G S = H S
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = eq_rat(Expr::app(g.clone(), s.clone()), Expr::app(h.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            let (hyp_id, _hyp) = b.fresh_local(hyp.clone());

            let ss_g = Expr::apps(subset_sum.clone(), [n.clone(), g.clone()]);
            let ss_h = Expr::apps(subset_sum.clone(), [n.clone(), h.clone()]);
            let concl = eq_rat(ss_g, ss_h);

            let r = b.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(h_id, BinderInfo::Default, g_type.clone(), r);
            let r = b.mk_pi(g_id, BinderInfo::Default, g_type, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n) (G H) (hyp) =>
        //   Fin.sum_congr (2^n) (j => G (hcDecode n j)) (j => H (hcDecode n j))
        //     (fun (j : Fin (2^n)) => hyp (hcDecode n j))
        //
        // The conclusion `subsetSum n G = subsetSum n H` δ-unfolds (subsetSum
        // reducible) to `Fin.sum (2^n) (j => G (hcDecode n j)) = Fin.sum (2^n)
        // (j => H (hcDecode n j))`, which is exactly Fin.sum_congr's conclusion.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let g_type = hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(g_type.clone());
            let (h_id, h) = b.fresh_local(g_type.clone());
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = eq_rat(Expr::app(g.clone(), s.clone()), Expr::app(h.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            let (hyp_id, hyp_fv) = b.fresh_local(hyp.clone());

            let g_dec = decoded_fn(&b, &n, &g);
            let h_dec = decoded_fn(&b, &n, &h);

            // lifted pointwise eq: fun (j : Fin (2^n)) => hyp (hcDecode n j)
            let lifted = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_pow = Expr::app(fin.clone(), pow2(&n));
                let (j_id, j) = ch.fresh_local(fin_pow.clone());
                let decoded = Expr::apps(hc_decode.clone(), [n.clone(), j]);
                let body = Expr::app(hyp_fv.clone(), decoded);
                ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
            };

            let proof = Expr::apps(fin_sum_congr.clone(), [pow2(&n), g_dec, h_dec, lifted]);

            let r = b.mk_lam(hyp_id, BinderInfo::Default, hyp, proof);
            let r = b.mk_lam(h_id, BinderInfo::Default, g_type.clone(), r);
            let r = b.mk_lam(g_id, BinderInfo::Default, g_type, r);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.subsetSum_split : forall (n : Nat) (G : HCPoint (n+1) -> Rat),`
    /// `  Eq Rat (subsetSum (n+1) G) (Rat.add LOW HIGH)`
    ///
    /// The subset-sum last-coordinate split: the sum over all `2^(n+1)` subsets
    /// of `[n+1]` decomposes into the subsets NOT containing coordinate `n` (LOW
    /// half, top bit `0`) plus the subsets CONTAINING coordinate `n` (HIGH half,
    /// top bit `1`). LOW/HIGH are the exact `2^n`-cube halves that `hcSumSplit`
    /// (the cube-bit recursion split) produces.
    ///
    /// Proof: `subsetSum (n+1) G` δ-unfolds (subsetSum reducible) to
    /// `Fin.sum (2^(n+1)) (fun k => G (hcDecode (n+1) k))`, which is EXACTLY
    /// `hcSumSplit`'s LHS — so the proof is `hcSumSplit n G` verbatim. This is
    /// the subset-induction split the Fourier-expansion route consumes (split
    /// subsets by the last coordinate, then the IH gives the n-case).
    /// Kernel-checked, constructive (closure = that of `hcSumSplit`, empty).
    /// Idempotent.
    pub(crate) fn register_subset_sum_split(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_hc_sum_split_theorem()?; // hcSumSplit

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let cast_add = Expr::const_(Name::from_string("Fin.castAdd"), vec![]);
        let add_nat = Expr::const_(Name::from_string("Fin.addNat"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let hc_sum_split = Expr::const_(Name::from_string("BoolAnalysis.hcSumSplit"), vec![]);
        let pow_two_succ = Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]);
        let eq_symm1 = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );
        let eq_ndrec_fin = Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![
                crate::level::Level::succ(crate::level::Level::zero()),
                crate::level::Level::succ(crate::level::Level::zero()),
            ],
        );
        let eq1 = Expr::const_(
            Name::from_string("Eq"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );

        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);
        let succ = |n: &Expr| Expr::app(nat_succ.clone(), n.clone());
        let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
        let hcpoint_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcpoint_of(n), rat.clone());
        let fin_of = |n: &Expr| Expr::app(fin.clone(), n.clone());
        let eq_rat = |l: Expr, r: Expr| Expr::apps(eq1.clone(), [rat.clone(), l, r]);

        // castP m a x e := @Eq.ndrec Nat m (fun mm => Fin mm) x a e  (transport a
        // Fin element along e : Eq Nat m a). Mirrors `cast_fin` in hcSumSplit.
        let cast_fin = |from: &Expr, to: &Expr, x: &Expr, e: &Expr, b: &EnvDeclBuilder| -> Expr {
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(b);
                let (m_id, m) = mb.fresh_local(nat.clone());
                let body = fin_of(&m);
                mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
            };
            Expr::apps(
                eq_ndrec_fin.clone(),
                [
                    nat.clone(),
                    from.clone(),
                    motive,
                    x.clone(),
                    to.clone(),
                    e.clone(),
                ],
            )
        };

        // mk_half(idx_map) := fun (i : Fin (2^n)) =>
        //   G (hcDecode (n+1) (castP (2^n+2^n) (2^(n+1)) (idx_map (2^n) (2^n) i) e_sym))
        let mk_half = |b: &EnvDeclBuilder, n: &Expr, g: &Expr, idx_map: &Expr| -> Expr {
            let mut hb = EnvDeclBuilder::child_of(b);
            let sn = succ(n);
            let p2n = pow2(n);
            let p2sn = pow2(&sn);
            let sum_pow = Expr::apps(nat_add.clone(), [p2n.clone(), p2n.clone()]);
            let (i_id, i) = hb.fresh_local(fin_of(&p2n));
            let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), i.clone()]);
            let e_fwd = Expr::app(pow_two_succ.clone(), n.clone());
            let e_sym = Expr::apps(
                eq_symm1.clone(),
                [nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
            );
            let casted = cast_fin(&sum_pow, &p2sn, &mapped, &e_sym, &hb);
            let decoded = Expr::apps(hc_decode.clone(), [sn.clone(), casted]);
            let body = Expr::app(g.clone(), decoded);
            hb.finish_child(hb.mk_lam(i_id, BinderInfo::Default, fin_of(&p2n), body))
        };

        // RHS(n,G) := Rat.add (Fin.sum (2^n) LOW) (Fin.sum (2^n) HIGH)
        let rhs_of = |b: &EnvDeclBuilder, n: &Expr, g: &Expr| -> Expr {
            let p2n = pow2(n);
            let low = Expr::apps(fin_sum.clone(), [p2n.clone(), mk_half(b, n, g, &cast_add)]);
            let high = Expr::apps(fin_sum.clone(), [p2n.clone(), mk_half(b, n, g, &add_nat)]);
            Expr::apps(rat_add.clone(), [low, high])
        };

        // Type: forall (n) (G : HCPoint (n+1) -> Rat),
        //   subsetSum (n+1) G = Rat.add (Fin.sum (2^n) LOW) (Fin.sum (2^n) HIGH)
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let sn = succ(&n);
            let g_ty = hcpoint_to_rat(&sn);
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let lhs = Expr::apps(subset_sum.clone(), [sn.clone(), g.clone()]);
            let rhs = rhs_of(&b, &n, &g);
            let body = eq_rat(lhs, rhs);
            let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, body);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n) (G) => hcSumSplit n G.
        // hcSumSplit's conclusion is `Fin.sum (2^(n+1)) (fun k => G (hcDecode
        // (n+1) k)) = Rat.add LOW HIGH`. The LHS δ-unfolds from `subsetSum (n+1)
        // G` (subsetSum reducible), and the RHS is byte-identical to rhs_of, so
        // `hcSumSplit n G` directly inhabits this statement's type.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let sn = succ(&n);
            let g_ty = hcpoint_to_rat(&sn);
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let proof = Expr::apps(hc_sum_split.clone(), [n.clone(), g.clone()]);
            let r = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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

    #[test]
    fn test_subset_sum_is_reducible_definition() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum().expect("register_subset_sum");
        let name = Name::from_string("BoolAnalysis.subsetSum");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum value must check against its type");
    }

    #[test]
    fn test_subset_sum_congr_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_congr()
            .expect("register_subset_sum_congr");
        let name = Name::from_string("BoolAnalysis.subsetSum_congr");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_congr proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "subsetSum_congr must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_congr's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_subset_sum_split_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_split()
            .expect("register_subset_sum_split");
        let name = Name::from_string("BoolAnalysis.subsetSum_split");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_split proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "subsetSum_split must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_split's transitive axiom closure must be empty"
        );
    }
}
