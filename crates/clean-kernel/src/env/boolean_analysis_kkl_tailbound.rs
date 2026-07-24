// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K2b layer: the `subsetSum` monotonicity spine of the tail
//! bound.
//!
//! ```text
//! BoolAnalysis.subsetSum_le_of_pointwise :
//!   ∀ (n : Nat) (g h : HCPoint n → Rat),
//!     (∀ S : HCPoint n, g S ≤ h S) → subsetSum n g ≤ subsetSum n h
//! ```
//!
//! This is the "lift via sum_le" half of the KKL spectral tail bound: once the
//! per-subset bound `k·ind(k ≤ |S|)·w S ≤ |S|·w S` is established pointwise, the
//! subset-sum monotonicity here lifts it to
//! `k·subsetSum n (…) ≤ subsetSum n (|S|·w S)`. Stated over arbitrary integrands
//! `g, h` (not just the `f̂²` weight) for reuse.
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! `subsetSum n G` δ-unfolds (reducible) to `Fin.sum (2^n) (fun j => G (hcDecode
//! n j))`, so the goal is exactly `Fin.sum_le`'s conclusion at the decoded
//! integrands. Instantiate the pointwise hypothesis at `hcDecode n j`:
//!   `Fin.sum_le (2^n) (j => g (hcDecode n j)) (j => h (hcDecode n j))
//!      (fun j => hyp (hcDecode n j))`.
//!
//! Every dependency (`Fin.sum_le`, `subsetSum`, `hcDecode`) is `Constructive`
//! with empty closure, so the lemma is too.
//!
//! The threshold-indicator tail bound proper
//! `k·subsetSum n (fun S => ind(k ≤ setSize S)·w S) ≤ subsetSum n (setSize·w S)`
//! additionally needs the per-S decidable case-split on `k ≤ setSize S` (a
//! `Nat`/`Rat`-popcount indicator); that pointwise step is the residual the
//! monotonicity here is designed to consume.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `BoolAnalysis.subsetSum_le_of_pointwise :
    ///   ∀ (n) (g h : HCPoint n → Rat),
    ///     (∀ S, g S ≤ h S) → subsetSum n g ≤ subsetSum n h`.
    ///
    /// Subset-sum monotonicity (the `Fin.sum_le` lift through `hcDecode`).
    /// Kernel-checked, constructive, empty closure. Idempotent.
    pub fn register_subset_sum_le_of_pointwise(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_fin_sum_le_theorem()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_sum_le = Expr::const_(Name::from_string("Fin.sum_le"), vec![]);
        let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le_rat = Expr::const_(Name::from_string("instLERat"), vec![]);

        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);
        let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());
        let hcpoint_to_rat = |n: &Expr| Expr::pi(BinderInfo::Default, hcpoint_of(n), rat.clone());
        let rat_le =
            |l: Expr, r: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le_rat.clone(), l, r]);

        // `fun (j : Fin (2^n)) => G (hcDecode n j)` — the Fin.sum summand for G.
        let decoded_fn = |b: &EnvDeclBuilder, n: &Expr, g: &Expr| -> Expr {
            let mut ch = EnvDeclBuilder::child_of(b);
            let fin_pow = Expr::app(fin.clone(), pow2(n));
            let (j_id, j) = ch.fresh_local(fin_pow.clone());
            let decoded = Expr::apps(hc_decode.clone(), [n.clone(), j]);
            let body = Expr::app(g.clone(), decoded);
            ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
        };

        // Type: ∀ (n) (g h : HCPoint n → Rat),
        //   (∀ S, g S ≤ h S) → subsetSum n g ≤ subsetSum n h
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let fn_ty = hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (h_id, h) = b.fresh_local(fn_ty.clone());

            // hyp : ∀ (S : HCPoint n), g S ≤ h S
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = rat_le(Expr::app(g.clone(), s.clone()), Expr::app(h.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            let (hyp_id, _hyp) = b.fresh_local(hyp.clone());

            let ss_g = Expr::apps(subset_sum.clone(), [n.clone(), g.clone()]);
            let ss_h = Expr::apps(subset_sum.clone(), [n.clone(), h.clone()]);
            let concl = rat_le(ss_g, ss_h);

            let r = b.mk_pi(hyp_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(h_id, BinderInfo::Default, fn_ty.clone(), r);
            let r = b.mk_pi(g_id, BinderInfo::Default, fn_ty, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            b.finish(r)
        };

        // Value: fun (n) (g h) (hyp) =>
        //   Fin.sum_le (2^n) (j => g (hcDecode n j)) (j => h (hcDecode n j))
        //     (fun (j : Fin (2^n)) => hyp (hcDecode n j))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let fn_ty = hcpoint_to_rat(&n);
            let (g_id, g) = b.fresh_local(fn_ty.clone());
            let (h_id, h) = b.fresh_local(fn_ty.clone());
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let body = rat_le(Expr::app(g.clone(), s.clone()), Expr::app(h.clone(), s));
                ch.finish_child(ch.mk_pi(s_id, BinderInfo::Default, hcp, body))
            };
            let (hyp_id, hyp_fv) = b.fresh_local(hyp.clone());

            let g_dec = decoded_fn(&b, &n, &g);
            let h_dec = decoded_fn(&b, &n, &h);

            // lifted pointwise ≤ : fun (j : Fin (2^n)) => hyp (hcDecode n j)
            let lifted = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_pow = Expr::app(fin.clone(), pow2(&n));
                let (j_id, j) = ch.fresh_local(fin_pow.clone());
                let decoded = Expr::apps(hc_decode.clone(), [n.clone(), j]);
                let body = Expr::app(hyp_fv.clone(), decoded);
                ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
            };

            let proof = Expr::apps(fin_sum_le.clone(), [pow2(&n), g_dec, h_dec, lifted]);

            let r = b.mk_lam(hyp_id, BinderInfo::Default, hyp, proof);
            let r = b.mk_lam(h_id, BinderInfo::Default, fn_ty.clone(), r);
            let r = b.mk_lam(g_id, BinderInfo::Default, fn_ty, r);
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
    fn test_subset_sum_le_of_pointwise_is_constructive_theorem() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_le_of_pointwise()
            .expect("register_subset_sum_le_of_pointwise");
        let name = Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_le_of_pointwise proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "subsetSum_le_of_pointwise must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "subsetSum_le_of_pointwise's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_subset_sum_le_of_pointwise_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_subset_sum_le_of_pointwise().expect("first");
        env.register_subset_sum_le_of_pointwise()
            .expect("second (idempotent)");
    }
}
