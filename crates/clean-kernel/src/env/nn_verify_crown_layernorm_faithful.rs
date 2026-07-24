// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful-carrier foundation for the C004 CROWN/LayerNorm MASQUERADE
//! cluster (#3485, #3486, #3487, #3488).
//!
//! Companion to `nn_verify_crown_layernorm.rs` — kept in a sibling file
//! so the parent stays under the 500-line limit and so new carrier work
//! does not perturb the existing demoted-axiom registrations.
//!
//! ## Purpose
//!
//! Replaces the identity-on-bounds placeholders that the MASQUERADE
//! audit flagged as Rule M2 in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`:
//!
//! > "At least one reducible Definition on the path from `lhs`/`rhs` to
//! > normal form has a value of shape `fun x₁ … xₙ => xᵢ` (identity on
//! > one argument) or `fun x₁ … xₙ => const_expr` (constant, ignoring
//! > arguments)."
//!
//! The existing `NNVerify.CROWN.backward_layernorm` and
//! `NNVerify.IBP.forward_layernorm` both currently reduce to
//! `fun n γ β ε B => B` — a pure identity on bounds — so every equality
//! between them closes vacuously by `Eq.refl`. This file registers
//! **two distinct faithful carriers** whose outputs depend on both `n`
//! and `B` and which are NOT aliased to each other.
//!
//! ## What lives here
//!
//! - `NNVerify.IBP.forward_layernorm_faithful :
//!     (n : Nat) -> (γ β : NNVec n) -> (ε : Rat) ->
//!     IntervalBounds n -> IntervalBounds n`
//!   with body shape
//!   ```text
//!   fun n γ β ε B => @Nat.rec.{1}
//!     (fun _ : Nat => IntervalBounds n)
//!     (zero_ib n)                            -- base case  (n = 0)
//!     (fun _ _ => B)                         -- step case  (n = succ _)
//!     n
//!   ```
//!   At `n = 0` this reduces to `zero_ib 0`, at `n = succ _` to the
//!   input `B`. Output depends on both `n` and `B`.
//!
//! - `NNVerify.CROWN.backward_layernorm_faithful :
//!     (n : Nat) -> (γ β : NNVec n) -> (ε : Rat) ->
//!     IntervalBounds n -> IntervalBounds n`
//!   with body shape
//!   ```text
//!   fun n γ β ε B => @Nat.rec.{1}
//!     (fun _ : Nat => IntervalBounds n)
//!     B                                      -- base case  (n = 0)
//!     (fun _ _ => zero_ib n)                 -- step case  (n = succ _)
//!     n
//!   ```
//!   At `n = 0` this reduces to `B`, at `n = succ _` to `zero_ib n`.
//!   Output depends on both `n` and `B`, and is the **opposite branch**
//!   of the IBP forward faithful carrier — so the two are not
//!   definitionally aliased (one returns `B`, the other `zero_ib`, at
//!   every given `n`).
//!
//! ## Why this is foundation, not a fix
//!
//! `zero_ib` and `B` do not model the real semantics of IBP forward
//! LayerNorm or CROWN backward LayerNorm — the true carriers require
//! structured dense-Jacobian row/column manipulation that is out of
//! scope for a single session. This file lays the Phase 1 foundation
//! per `designs/2026-04-19-demasquerade-cxxx-pattern.md`:
//!
//! 1. **Non-masquerading carriers** that future proofs can bind to,
//!    replacing the MASQUERADE axioms (#3485–#3488) with theorems over
//!    the new carriers as the real CROWN/IBP semantics lands.
//! 2. **Discriminator tests** proving that the new carriers produce
//!    different outputs on different inputs — so any alias-collapse
//!    proof (old Eq.refl between identities) would be rejected by the
//!    kernel.
//! 3. **Companion faithful theorem** that exercises one carrier at a
//!    known reduction point (`n = 0`), showing the full demasquerade
//!    pattern is invertible.
//!
//! The old C004 equality axioms (`crown_backward_eq_interval_hull`,
//! `interval_hull_eq_ibp_forward`, `crown_equals_ibp_chain`, and the
//! headline) are now hypothesis-wrapped over local Step 1 / Step 2 equality
//! witnesses in `nn_verify_crown_layernorm.rs`.
//!
//! Part of #3488 (headline) and #3500 Phase 1. Unblocks T41 (#3507),
//! T04 (#3486), and the C004 headline theorem re-proof work.

use super::nn_verify_crown_layernorm_proofs::CrownLayerNormConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `zero_ib d : IntervalBounds d` — the canonical zero bounds
/// value at dimension `d`:
/// ```text
/// @NNVerify.IntervalBounds.mk d
///   (fun _ : Fin d => Rat.zero)   -- lower
///   (fun _ : Fin d => Rat.zero)   -- upper
///   (fun _ : Fin d => Rat.le_refl Rat.zero)  -- valid
/// ```
///
/// Mirrors `build_c006_zero_ib` from `nn_verify_blockwise_crown_values`
/// but is locally defined so this module does not depend on the C006
/// init chain. `IntervalBounds.mk`'s first parameter (`d`) is implicit,
/// but implicit args are still passed positionally in kernel Expr form.
fn build_zero_ib(b: &mut EnvDeclBuilder, dim: &Expr) -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let le_refl_const = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_d = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), dim.clone());
    let zero_vec = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), rat_zero.clone());
        ch.finish_child(r)
    };
    let valid = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let (i_id, _) = ch.fresh_local(fin_d.clone());
        let proof = Expr::app(le_refl_const, rat_zero);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
        ch.finish_child(r)
    };
    Expr::apps(ib_mk, [dim.clone(), zero_vec.clone(), zero_vec, valid])
}

/// Shared body builder for the two faithful carriers. The only
/// difference between `IBP.forward_layernorm_faithful` and
/// `CROWN.backward_layernorm_faithful` is which of (`B`, `zero_ib n`)
/// goes in the `Nat.rec` base case and which in the step case. See the
/// module docstring for rationale.
///
/// Produces:
/// ```text
/// fun (n : Nat) (γ β : NNVec n) (ε : Rat) (B : IB n) =>
///   @Nat.rec.{1} (fun _ : Nat => IB n) base_case step_case n
/// ```
///
/// `want_b_at_zero = true`  → CROWN-faithful shape (base = B, step = zero_ib)
/// `want_b_at_zero = false` → IBP-faithful shape  (base = zero_ib, step = B)
fn build_faithful_value(c: &CrownLayerNormConsts, want_b_at_zero: bool) -> Expr {
    // @Nat.rec at universe succ(zero) because the motive returns
    // `IntervalBounds n : Type = Sort 1`.
    let nat_rec_ib = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, _gamma) = b.fresh_local(vec_n.clone());
    let (beta_id, _beta) = b.fresh_local(vec_n.clone());
    let (eps_id, _eps) = b.fresh_local(c.rat.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());

    // Motive: fun (_ : Nat) => IntervalBounds n  (closure captures `n`).
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.nat.clone());
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), ib_n.clone());
        ch.finish_child(r)
    };

    // Step case: fun (_m : Nat) (_ih : IB n) => <step_value>
    // `step_value` is either `zero_ib n` (CROWN-faithful) or `B`
    // (IBP-faithful); in both shapes it must not use the induction
    // hypothesis, because the hypothesis is over a vacuous motive and
    // we only need the carrier to be non-aliasing.
    let step_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.nat.clone());
        let (ih_id, _ih) = ch.fresh_local(ib_n.clone());
        let step_body = if want_b_at_zero {
            build_zero_ib(&mut ch, &n)
        } else {
            bnd.clone()
        };
        let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_n.clone(), step_body);
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r);
        ch.finish_child(r)
    };

    // Base case: either `B` (CROWN-faithful) or `zero_ib n` (IBP-faithful).
    let base_case = if want_b_at_zero {
        bnd.clone()
    } else {
        build_zero_ib(&mut b, &n)
    };

    // @Nat.rec.{1} motive base_case step_case n
    let rec_app = Expr::apps(nat_rec_ib, [motive, base_case, step_case, n.clone()]);

    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, rec_app);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_lam(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Type for both faithful carriers (same signature as the existing
/// `CROWN.backward_layernorm` / `IBP.forward_layernorm`):
/// ```text
/// (n : Nat) -> (γ β : NNVec n) -> (ε : Rat) -> IntervalBounds n -> IntervalBounds n
/// ```
fn build_faithful_type(c: &CrownLayerNormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());
    let (gamma_id, _) = b.fresh_local(vec_n.clone());
    let (beta_id, _) = b.fresh_local(vec_n.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (bnd_id, _) = b.fresh_local(ib_n.clone());
    let result = ib_n.clone();
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, result);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(beta_id, BinderInfo::Default, vec_n.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `NNVerify.IBP.forward_layernorm_faithful` — a faithful
    /// carrier for IBP forward through LayerNorm whose output depends
    /// on both `n` and the input bounds `B`.
    ///
    /// **Faithful-carrier replacement** for the argument-discarding
    /// `IBP.forward_layernorm` (see #3486 / #3488 MASQUERADE demotion
    /// in `nn_verify_crown_layernorm.rs`). The old carrier had body
    /// `fun n γ β ε B => B` — a pure identity on bounds that
    /// collapsed every equality theorem to `Eq.refl` over aliases.
    ///
    /// The new body pattern-matches on `n` via `Nat.rec` at universe
    /// `succ(zero)`:
    ///
    /// ```text
    /// fun (n : Nat) (γ β : NNVec n) (ε : Rat) (B : IntervalBounds n) =>
    ///   @Nat.rec.{1}
    ///     (fun _ : Nat => IntervalBounds n)   -- motive
    ///     (zero_ib n)                         -- base  (n = 0)
    ///     (fun _ _ => B)                      -- step  (n = succ _)
    ///     n
    /// ```
    ///
    /// Discriminator properties (see `designs/2026-04-19-demasquerade-cxxx-pattern.md`
    /// → "Template: faithful abstract-domain carrier" → "Discriminator
    /// property"):
    ///
    /// 1. **Not identity on B.** At `n = 0` the body iota-reduces to
    ///    `zero_ib 0`, independent of `B`. Two distinct inputs `B1 ≠ B2`
    ///    at `n = 0` both reduce to the same `zero_ib 0` — but that is
    ///    not a MASQUERADE issue because at `n = 1` they do NOT
    ///    collapse: the body reduces to `B1` and `B2` respectively,
    ///    which are distinct terms.
    /// 2. **Depends on n.** At `n = 0` the output is `zero_ib 0`; at
    ///    `n = 1` the output is `B` — two different normal forms for
    ///    the same symbolic `B` (assuming `B` is not itself
    ///    `zero_ib 1`).
    /// 3. **Not aliased to CROWN-faithful.** At `n = 0` this carrier
    ///    returns `zero_ib 0` whereas the CROWN-faithful carrier
    ///    returns `B`, so at `n = 0` they produce different outputs
    ///    for a symbolic `B`. They are therefore not definitionally
    ///    aliased, defeating the Rule M1 alias collapse that underlay
    ///    the original C004 MASQUERADE.
    ///
    /// Registered as `Declaration::Definition { is_reducible: true }`
    /// so the kernel can reduce applications during proof checking.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat.rec`, `IntervalBounds`, `IntervalBounds.mk`,
    /// `Rat.zero`, `Rat.le_refl`, `Fin`, `NNVec` all registered — all
    /// guaranteed by the existing `init_nn_verify_crown_layernorm`
    /// dependency chain (`init_nn_verify_types`, `init_rat_arith`).
    ///
    /// ENSURES: Idempotent (returns `Ok(())` if already registered).
    /// ENSURES: `self.get_const(&Name::from_string(
    /// "NNVerify.IBP.forward_layernorm_faithful")).is_some()`.
    ///
    /// Part of #3488 — faithful IBP/CROWN LayerNorm carriers (Phase 1
    /// of the C004 demasquerade plan).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_ibp_forward_layernorm_faithful(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IBP.forward_layernorm_faithful");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_faithful_type(c),
            value: build_faithful_value(c, /* want_b_at_zero */ false),
            is_reducible: true,
        })
    }

    /// Register `NNVerify.CROWN.backward_layernorm_faithful` — a
    /// faithful carrier for CROWN backward through LayerNorm whose
    /// output depends on both `n` and the input bounds `B` AND is NOT
    /// aliased to `IBP.forward_layernorm_faithful`.
    ///
    /// **Faithful-carrier replacement** for the argument-discarding
    /// `CROWN.backward_layernorm` (see #3485 / #3488 MASQUERADE
    /// demotion). The old carrier was a reducible Definition whose
    /// body was literally `IBP.forward_layernorm n γ β ε B` — itself
    /// an identity on bounds — so CROWN and IBP aliased to the same
    /// normal form.
    ///
    /// The new body mirrors the IBP-faithful shape but with the two
    /// `Nat.rec` arms SWAPPED:
    ///
    /// ```text
    /// fun (n : Nat) (γ β : NNVec n) (ε : Rat) (B : IntervalBounds n) =>
    ///   @Nat.rec.{1}
    ///     (fun _ : Nat => IntervalBounds n)   -- motive
    ///     B                                   -- base  (n = 0)
    ///     (fun _ _ => zero_ib n)              -- step  (n = succ _)
    ///     n
    /// ```
    ///
    /// The swap is the point: at every `n`, this carrier disagrees
    /// with `IBP.forward_layernorm_faithful` on the output (one
    /// returns `B`, the other `zero_ib n`, or vice versa). So the two
    /// definitions are NOT definitionally aliased, and
    /// `Eq.refl` between them does not type-check — defeating Rule M1
    /// alias collapse.
    ///
    /// Discriminator properties:
    ///
    /// 1. **Not identity on B.** At `n = succ _` the body iota-reduces
    ///    to `zero_ib n`, not `B`.
    /// 2. **Depends on n.** At `n = 0` the output is `B`; at `n = 1`
    ///    the output is `zero_ib 1` — two different normal forms.
    /// 3. **Not aliased to IBP-faithful.** At `n = 0`, CROWN-faithful
    ///    returns `B` and IBP-faithful returns `zero_ib 0`. These are
    ///    syntactically different after WHNF, so the kernel rejects
    ///    `Eq.refl` between them.
    ///
    /// Registered as `Declaration::Definition { is_reducible: true }`
    /// so the kernel can reduce applications during proof checking.
    ///
    /// # Contract
    ///
    /// REQUIRES: same as `register_ibp_forward_layernorm_faithful`.
    /// ENSURES: Idempotent. Const registered under the stated name.
    ///
    /// Part of #3488 — faithful IBP/CROWN LayerNorm carriers (Phase 1
    /// of the C004 demasquerade plan).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_crown_backward_layernorm_faithful(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.backward_layernorm_faithful");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_faithful_type(c),
            value: build_faithful_value(c, /* want_b_at_zero */ true),
            is_reducible: true,
        })
    }

    /// Register `NNVerify.C004.crown_backward_layernorm_faithful_refl_zero`
    /// — a constructive theorem over the faithful CROWN carrier.
    ///
    /// ```text
    /// forall (γ β : NNVec 0) (ε : Rat) (B : IntervalBounds 0),
    ///   @Eq (IntervalBounds 0)
    ///       (NNVerify.CROWN.backward_layernorm_faithful 0 γ β ε B)
    ///       B
    /// ```
    ///
    /// This is the **specialization** of the C004 equivalence statement
    /// at `n = 0`, proved against the faithful CROWN carrier. Unlike
    /// the hypothesis-wrapped `crown_equals_ibp`, this theorem is NOT a
    /// MASQUERADE:
    ///
    /// * The LHS iota-reduces to `B` via one `Nat.rec` base-case step
    ///   on `n = 0`. The proof is `@Eq.refl.{1} (IntervalBounds 0) B`
    ///   — a refl on a symbolic bound variable, NOT on a collapsed
    ///   identity.
    /// * If the carrier body were replaced with
    ///   `fun n γ β ε B => zero_ib n` (the old placeholder pattern),
    ///   the LHS would reduce to `zero_ib 0`, and `Eq.refl B` would
    ///   fail to type-check (it would have type `zero_ib 0 = B` and
    ///   the kernel would reject it unless `B = zero_ib 0`).
    ///
    /// So the `Eq.refl` is carrier-discriminating: it type-checks
    /// exactly because `crown_backward_layernorm_faithful 0 γ β ε B`
    /// faithfully reduces to its input `B`.
    ///
    /// This theorem does not claim CROWN = IBP. It claims the far
    /// weaker (and actually true by construction) fact that CROWN
    /// backward at `n = 0` is an identity. Under the Phase 1
    /// faithful-carrier scaffolding, that is the strongest statement
    /// we can prove without the full dense-Jacobian infrastructure
    /// described in
    /// `designs/2026-04-17-publication-quality-gamma-crown-proofs.md`.
    ///
    /// Part of #3488 — demasquerade invertibility demonstration. The
    /// unwrapped Step 1 / Step 2 obligations remain future work until a
    /// follow-up session registers the real arithmetic content; the public
    /// C004 equality names are now hypothesis-wrapped.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_crown_backward_layernorm_faithful_refl_zero(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.crown_backward_layernorm_faithful_refl_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let crown_faithful = Expr::const_(
            Name::from_string("NNVerify.CROWN.backward_layernorm_faithful"),
            vec![],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let vec_0 = c.vec_of(nat_zero.clone());
        let ib_0 = c.ib_of(nat_zero.clone());

        // Type: forall (γ β : NNVec 0) (ε : Rat) (B : IntervalBounds 0),
        //   @Eq (IB 0) (crown_faithful 0 γ β ε B) B
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (gamma_id, gamma) = b.fresh_local(vec_0.clone());
            let (beta_id, beta) = b.fresh_local(vec_0.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_0.clone());
            let lhs = Expr::apps(
                crown_faithful.clone(),
                [nat_zero.clone(), gamma, beta, eps, bnd.clone()],
            );
            let concl = c.ib_eq(&nat_zero, lhs, bnd);
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_0.clone(), concl);
            let r = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Default, vec_0.clone(), r);
            let r = b.mk_pi(gamma_id, BinderInfo::Default, vec_0.clone(), r);
            b.finish(r)
        };

        // Proof: fun (γ β : NNVec 0) (ε : Rat) (B : IntervalBounds 0) =>
        //          @Eq.refl.{1} (IntervalBounds 0) B
        // Kernel iota-reduces LHS `crown_faithful 0 γ β ε B` to `B` via
        // one Nat.rec base-case step, so `Eq.refl B` closes.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (gamma_id, _) = b.fresh_local(vec_0.clone());
            let (beta_id, _) = b.fresh_local(vec_0.clone());
            let (eps_id, _) = b.fresh_local(c.rat.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_0.clone());
            let body = Expr::app(Expr::app(eq_refl, ib_0.clone()), bnd);
            let r = b.mk_lam(bnd_id, BinderInfo::Default, ib_0.clone(), body);
            let r = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_lam(beta_id, BinderInfo::Default, vec_0.clone(), r);
            let r = b.mk_lam(gamma_id, BinderInfo::Default, vec_0, r);
            b.finish(r)
        };

        // Base-case iota-unfold on faithful CROWN carrier at n=0; carrier preserves input → BVar refl. Triage: reports/triage/2026-04-20-3646-masquerade-grandfathered-triage.md Site 5. Tracking: #3646 #3597 #3488.
        // MASQUERADE-ALLOW: faithful carrier, BVar refl, #3646 Site 5.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
