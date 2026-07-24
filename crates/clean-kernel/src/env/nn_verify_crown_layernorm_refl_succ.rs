// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1 sub-piece of the C004 faithful-carrier redesign: the
//! symmetric step-case companion to
//! `NNVerify.C004.crown_backward_layernorm_faithful_refl_zero` (#3488),
//! proving that `IBP.forward_layernorm_faithful` reduces to its input
//! bounds `B` at `n = Nat.succ k` via one `Nat.rec` step-case step.
//!
//! ## Content
//!
//! One `Declaration::Theorem` is registered here:
//! `NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ` (see
//! `register_ibp_forward_layernorm_faithful_refl_succ` for the full
//! docstring and proof derivation).
//!
//! ## Why a sibling module
//!
//! Kept in its own file so `nn_verify_crown_layernorm.rs` and
//! `nn_verify_crown_layernorm_faithful.rs` stay under the 500-line
//! limit while new Phase 1 theorems land. Mirrors the
//! `nn_verify_crown_layernorm_proofs.rs` split pattern.
//!
//! Part of #3373 — tracks the
//! `designs/2026-04-20-c004-faithful-carrier-redesign.md` rollout.

use super::nn_verify_crown_layernorm_proofs::CrownLayerNormConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ`
    /// — a constructive theorem over the faithful IBP carrier at
    /// `n = Nat.succ k`.
    ///
    /// ```text
    /// forall (k : Nat) (γ β : NNVec (Nat.succ k)) (ε : Rat)
    ///        (B : IntervalBounds (Nat.succ k)),
    ///   @Eq (IntervalBounds (Nat.succ k))
    ///       (NNVerify.IBP.forward_layernorm_faithful (Nat.succ k) γ β ε B)
    ///       B
    /// ```
    ///
    /// Phase 1 sub-piece of the C004 faithful-carrier redesign per
    /// `designs/2026-04-20-c004-faithful-carrier-redesign.md`. Symmetric
    /// companion to `crown_backward_layernorm_faithful_refl_zero`:
    /// where the CROWN theorem exercises the `Nat.rec` **base case** at
    /// `n = 0` (CROWN-faithful returns its input `B` there), this one
    /// exercises the `Nat.rec` **step case** at `n = Nat.succ k`
    /// (IBP-faithful returns its input `B` there — see the
    /// `build_faithful_value` step body at `want_b_at_zero = false` in
    /// `nn_verify_crown_layernorm_faithful.rs`).
    ///
    /// Discriminator content (Rule M1/M2 demasquerade audit):
    ///
    /// * The LHS iota-reduces to `B` via one `Nat.rec` step on
    ///   `Nat.succ k`. The proof is `@Eq.refl.{1} (IntervalBounds
    ///   (Nat.succ k)) B` — a refl on a symbolic bound variable `B`,
    ///   NOT on a collapsed identity like `zero_ib (Nat.succ k)`.
    /// * If the IBP-faithful step case were replaced with `zero_ib n`
    ///   (the old Rule M2 pattern), the LHS would reduce to
    ///   `zero_ib (Nat.succ k)`, and `Eq.refl B` would fail to
    ///   type-check for a symbolic `B`.
    /// * The CROWN-faithful step case returns `zero_ib n` at
    ///   `Nat.succ k`, not `B`, so this proof does NOT type-check
    ///   against CROWN-faithful — defeating Rule M1 alias collapse.
    ///
    /// Together with `crown_backward_layernorm_faithful_refl_zero`,
    /// these two theorems cover BOTH `Nat.rec` arms of BOTH faithful
    /// carriers:
    ///
    /// | Carrier       | n = 0          | n = Nat.succ k |
    /// |---------------|----------------|----------------|
    /// | CROWN-faithful| `B` (refl_zero)| `zero_ib n`    |
    /// | IBP-faithful  | `zero_ib 0`    | `B` (this thm) |
    ///
    /// The pair forms a kernel-verified **discriminator
    /// demonstration** — any future proof attempting to close
    /// CROWN-faithful = IBP-faithful by `Eq.refl` would have to hold
    /// under both rows, and no single `Eq.refl` can witness both
    /// columns because the carriers disagree at every `n`. This is the
    /// Phase 1 foundation on which the real CROWN=IBP equivalence
    /// proof (requiring Rat interval arithmetic and dense-Jacobian
    /// content, see `designs/2026-04-20-c004-faithful-carrier-redesign.md`
    /// §Proof Strategy) will be built.
    ///
    /// # Contract
    ///
    /// REQUIRES: `NNVerify.IBP.forward_layernorm_faithful` registered
    /// (via `register_ibp_forward_layernorm_faithful`) plus `Nat`,
    /// `Nat.succ`, `NNVec`, `IntervalBounds`, `Rat`, `Eq`, `Eq.refl`.
    ///
    /// ENSURES: Idempotent. Const registered under the stated name.
    /// ENSURES: `Declaration::Theorem` with non-trivial proof value
    /// whose outer lambda binds `k` and whose innermost body is
    /// `@Eq.refl.{1} (IB (Nat.succ k)) B` on a BVar witness (Rule M4
    /// sentinel).
    ///
    /// Part of #3373 — C004 faithful-carrier demasquerade, Phase 1
    /// sub-piece. Does not close the hypothesis-free C004 equality
    /// obligations or T41. The public Step 1 / Step 2 / chain / headline
    /// names are separately hypothesis-wrapped over local equality
    /// witnesses.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ibp_forward_layernorm_faithful_refl_succ(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ibp_faithful = Expr::const_(
            Name::from_string("NNVerify.IBP.forward_layernorm_faithful"),
            vec![],
        );
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );

        // Type: forall (k : Nat) (γ β : NNVec (Nat.succ k)) (ε : Rat)
        //              (B : IntervalBounds (Nat.succ k)),
        //   @Eq (IB (Nat.succ k)) (ibp_faithful (Nat.succ k) γ β ε B) B
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let succ_k = Expr::app(nat_succ.clone(), k.clone());
            let vec_succ_k = c.vec_of(succ_k.clone());
            let ib_succ_k = c.ib_of(succ_k.clone());
            let (gamma_id, gamma) = b.fresh_local(vec_succ_k.clone());
            let (beta_id, beta) = b.fresh_local(vec_succ_k.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_succ_k.clone());
            let lhs = Expr::apps(
                ibp_faithful.clone(),
                [succ_k.clone(), gamma, beta, eps, bnd.clone()],
            );
            let concl = c.ib_eq(&succ_k, lhs, bnd);
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_succ_k, concl);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_succ_k.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_succ_k, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Proof: fun (k : Nat) (γ β : NNVec (Nat.succ k)) (ε : Rat)
        //            (B : IntervalBounds (Nat.succ k)) =>
        //          @Eq.refl.{1} (IntervalBounds (Nat.succ k)) B
        // Kernel iota-reduces LHS `ibp_faithful (Nat.succ k) γ β ε B`
        // to `B` via one Nat.rec step-case step, so `Eq.refl B`
        // closes.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let succ_k = Expr::app(nat_succ, k);
            let vec_succ_k = c.vec_of(succ_k.clone());
            let ib_succ_k = c.ib_of(succ_k);
            let (gamma_id, _) = b.fresh_local(vec_succ_k.clone());
            let (beta_id, _) = b.fresh_local(vec_succ_k.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_succ_k.clone());
            let body = Expr::app(Expr::app(eq_refl, ib_succ_k.clone()), bnd);
            let r = b.mk_lam(bnd_id, BinderInfo::Default, ib_succ_k, body);
            let r = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(beta_id, BinderInfo::Default, vec_succ_k.clone(), r);
            let r = b.mk_lam(gamma_id, BinderInfo::Default, vec_succ_k, r);
            let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Succ-case iota-unfold on faithful IBP carrier at `Nat.succ k`.
        // IBP-faithful returns BVar `B` at succ by step body; `Eq.refl B`
        // type-checks only because the carrier preserves its input at
        // succ. Symmetric companion to refl_zero (Site 5): covers BOTH
        // Nat.rec arms of BOTH faithful carriers. See triage report
        // reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md
        // Site 6. Tracking: #3646, #3597, #3373, #3488.
        // MASQUERADE-ALLOW: faithful carrier, BVar refl (#3646 Site 6).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
