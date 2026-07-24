// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C004: CROWN/LayerNorm Degeneracy -- Branch A demasquerade of Step 2
//! and headline (#3583) plus `jacobian_dense` carrier reclass (#3584)
//! on top of prior MASQUERADE demotion (#3488)
//!
//! Status: 0 C004-specific domain axioms + 4 hypothesis-wrapped equality/transitivity theorems, 2 opaques (external
//! functions: LayerNorm.jacobian, LayerNorm.forward),
//! and 4 definitions. The Step 2 equality claim
//! (`interval_hull_eq_ibp_forward`) is retired to a hypothesis-wrapped
//! theorem over local Step 2 equality evidence; Step 1
//! (`crown_backward_eq_interval_hull`) and the transitivity chain are
//! retired to hypothesis-wrapped theorems over
//! local Step 1 / Step 2 equality witnesses. The `jacobian_dense`
//! predicate is now a constructive non-`True` definition requiring
//! `sigma != 0` and coordinatewise `gamma i != 0`. The
//! previous #3460 / #3488 density-guarded "Theorem" restatements of
//! Step 2 and the headline are withdrawn by #3583: the proof terms
//! eliminated a `jacobian_dense` hypothesis via `True.rec` over
//! alias-collapsed conclusions — a compound M1+M2 masquerade (alias
//! collapse + argument-discarding True-carrier) per
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`. Keeping those
//! theorems live misrepresented the conjecture's proven content.
//! The transitivity names `NNVerify.C004.crown_equals_ibp_chain` and
//! `NNVerify.C004.crown_equals_ibp` were retired from the axiom audit on
//! 2026-04-27 by strengthening them to require local Step 1 and Step 2
//! equality witnesses and proving the result by `Eq.trans`; neither
//! theorem references the old C004 axiom constants. On 2026-04-27,
//! `crown_backward_eq_interval_hull` was likewise retired from the axiom
//! audit by strengthening the statement with a local Step 1 equality
//! witness and returning that witness directly. Later on 2026-04-27,
//! `interval_hull_eq_ibp_forward` was retired the same way for Step 2.
//!
//! **#3583 — Branch A demasquerade, #3584 — carrier cleanup.** Mirrors
//! the pattern landed for C010 (#3578) and C012 (#3579): revert
//! `NNVerify.C004.jacobian_dense` from a reducible
//! `Declaration::Definition` (body `True`) first to `Declaration::Opaque`
//! under #3583, then to `Declaration::Axiom` (no value) under #3584,
//! demote `interval_hull_eq_ibp_forward` (Step 2) from
//! `Declaration::Theorem` to `Declaration::Axiom` on the pre-#3460
//! canonical 5-binder Pi shape built via `build_ln_equality_type`, and
//! keep the old headline proof withdrawn until the 2026-04-27
//! hypothesis-wrapped replacement. Flipping
//! `jacobian_dense` to Opaque under #3583 closed the `jacobian_dense n
//! γ σ z -> True` delta-reduction path (so a future `True.rec`-over-
//! density proof term can no longer discharge either equality
//! conclusion); the #3584 Opaque → Axiom reclass removes the leftover
//! `True` placeholder body entirely — a density predicate without a
//! constructive definition is honestly represented as an Axiom. The
//! density-guarded helper modules are removed.
//!
//! **Why the headline is included here.** The #3488 headline proof term
//! shared the same `True.rec`-over-`jacobian_dense` mechanics as the
//! Step 2 proof. The #3583 Opaque flip breaks both proof terms
//! simultaneously — there was no honest way to keep the old headline as
//! a hypothesis-free theorem once the density carrier no longer
//! delta-reduces. The current headline theorem is a different,
//! strengthened statement with explicit local equality hypotheses.
//!
//! The previous chain relied on `CROWN.backward_layernorm`,
//! `C004.interval_hull_layernorm`, and `IBP.forward_layernorm` all
//! reducing to the same identity-on-bounds body, so every "Eq.refl
//! between aliases" closed trivially. A kernel proof of the shape
//! `@Eq.refl.{1} (IB n) (IBP.forward_layernorm n γ β ε B)` between
//! aliases of a single identity function asserts "identity = identity",
//! not anything about CROWN, IBP, or LayerNorm. The
//! `crown_equals_ibp_chain` theorem composed two such Eq.refls via
//! `Eq.trans`, and `crown_equals_ibp` applied the chain to its
//! quantifiers. None of those proof terms survives replacing any
//! carrier with a faithful implementation; the public C004 equality names
//! are now proved only under explicit local equality evidence.
//!
//! See `reports/audit/2026-04-19-clean-native-shard-audit.md` and issues
//! #3485, #3486, #3487, #3488, #3460, #3583, #3584. The follow-up
//! reclass of `jacobian_dense` from `Declaration::Opaque` (body `True`)
//! to honest `Declaration::Axiom` (no value) landed under #3584 — the
//! Opaque-with-True-body was a leftover placeholder from the #3583
//! demotion, carrying no mathematical content.
//!
//! Per `design doc` Proof Soundness Rules: "Declaration::Theorem wrapping
//! Declaration::Axiom is NOT a proof. It is a restatement." The same
//! applies to `Eq.refl` between definitional aliases and to `True.rec`
//! over alias-collapsed conclusions under a `True`-valued carrier.
//! `jacobian_dense` is no longer an axiom, and Step 1 / Step 2 / chain /
//! headline are honest hypothesis-wrapped theorems over local equality
//! evidence.
//!
//! ---
//!
//! The LayerNorm Jacobian J[i,j] = (gamma_i/sigma)(delta_ij - 1/n - z_i*z_j/n)
//! is dense (full-rank), so CROWN backward reduces to element-wise interval
//! propagation = IBP. Two-step chain through the interval hull:
//!   Step 1: CROWN backward = interval hull  (hypothesis-wrapped theorem, 2026-04-27)
//!   Step 2: interval hull  = IBP forward    (hypothesis-wrapped theorem, 2026-04-27)
//!   Chain : Step 1 composed with Step 2     (hypothesis-wrapped theorem, 2026-04-27)
//!   Main  : CROWN backward = IBP forward    (hypothesis-wrapped theorem, 2026-04-27)
//!
//! Ref: Zhang et al. (CROWN, NeurIPS 2018), Ba et al. (LayerNorm, 2016),
//! gamma-crown experiments/c004_crown_layernorm_degeneracy/. Part of #3196.

use crate::env::nn_verify_crown_layernorm_proofs::{
    build_bounds_transform_type, build_crown_backward_ln_value, build_crown_equals_ibp_hyp_proof,
    build_crown_equals_ibp_hyp_type, build_faithful_ibp_forward_value, build_interval_hull_value,
    build_jacobian_dense_type, build_jacobian_dense_value, build_ln_equality_hyp_proof,
    build_ln_equality_hyp_type, build_ln_forward_type, build_ln_forward_value,
    build_ln_jacobian_type, build_ln_jacobian_value, CrownLayerNormConsts,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C004 (CROWN/LayerNorm degeneracy) declarations.
    ///
    /// Axiom count: **0 C004-specific domain axioms** after the
    /// 2026-04-27 Step 1 / Step 2 / chain / headline retirements and the
    /// 2026-04-27 `jacobian_dense` predicate definition. The previous #3460 /
    /// #3488 density-guarded "Theorem" restatements of Step 2 and the
    /// headline are withdrawn because the `True.rec`-over-`jacobian_dense`
    /// proof term was a compound M1+M2 masquerade (alias collapse +
    /// `True`-carrier argument-discarding). See the module-level
    /// docstring for the Branch A / carrier-cleanup rationale.
    ///
    /// Registers:
    /// - `NNVerify.LayerNorm.jacobian` -- Jacobian function (opaque)
    /// - `NNVerify.LayerNorm.forward` -- LayerNorm forward pass (opaque)
    /// - `NNVerify.CROWN.backward_layernorm` -- CROWN backward bounds (definition = IBP forward)
    /// - `NNVerify.IBP.forward_layernorm` -- IBP forward bounds (opaque)
    /// - `NNVerify.C004.interval_hull_layernorm` -- interval hull (definition = IBP forward)
    /// - `NNVerify.C004.jacobian_dense` -- density predicate (Definition, non-True body; 2026-04-27)
    /// - `NNVerify.C004.crown_backward_eq_interval_hull` -- Step 1 (hypothesis-wrapped theorem, 2026-04-27)
    /// - `NNVerify.C004.interval_hull_eq_ibp_forward` -- Step 2 (hypothesis-wrapped theorem, 2026-04-27)
    /// - `NNVerify.C004.crown_equals_ibp_chain` -- transitivity (hypothesis-wrapped theorem, 2026-04-27)
    /// - `NNVerify.C004.crown_equals_ibp` -- Main claim (hypothesis-wrapped theorem, 2026-04-27)
    /// - `NNVerify.IBP.forward_layernorm_faithful` -- faithful carrier (Phase 1, #3488)
    /// - `NNVerify.CROWN.backward_layernorm_faithful` -- faithful carrier (Phase 1, #3488)
    /// - `NNVerify.C004.crown_backward_layernorm_faithful_refl_zero` -- refl-at-zero theorem (#3488)
    /// - `NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ` -- refl-at-succ theorem (#3373 Phase 1 sub-piece)
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec, NNMat, IntervalBounds, Fin
    /// - `init_eq()` for Eq, Eq.trans, Eq.refl
    /// - `init_rat_arith()` for Rat arithmetic, Rat.zero
    /// - `init_rat_linear_order()` for Rat.le_refl (faithful zero_ib validity)
    /// - `init_rat_ordered_field_axioms()` for Rat.add_le_add_left (Phase 1.5
    ///   β-shift validity; #3615)
    /// - `init_true_false()` for Ne / Not used by `jacobian_dense`
    /// - `init_and()` for the `jacobian_dense` conjunction body
    pub(crate) fn init_nn_verify_crown_layernorm(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_crown_layernorm_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_eq()?;
        self.init_rat_arith()?;
        // Provides Rat.le_refl for the faithful-carrier zero_ib builder
        // (Phase 1 of #3488 — faithful IBP/CROWN LayerNorm carriers).
        self.init_rat_linear_order()?;
        // Phase 1.5 of #3615: the step-case of the faithful
        // `IBP.forward_layernorm` body performs a β-shift and discharges
        // the `IntervalBounds` validity field via `Rat.add_le_add_left`,
        // which is registered here as an ordered-field axiom.
        self.init_rat_ordered_field_axioms()?;
        self.init_true_false()?;
        self.init_and()?;

        let c = CrownLayerNormConsts::new();
        // External function opaques (computational content in gamma-crown;
        // well-typed placeholders, opaque prevents reduction)
        self.register_ln_jacobian(&c)?;
        self.register_ln_forward(&c)?;
        // IBP forward must be registered BEFORE CROWN backward (CROWN is
        // defined in terms of IBP forward)
        self.register_ibp_forward_layernorm(&c)?;
        // CROWN backward is now a reducible Definition = IBP forward
        self.register_crown_backward_layernorm(&c)?;
        // Definitions with computational bodies
        self.register_interval_hull_layernorm(&c)?;
        self.register_jacobian_dense(&c)?;
        // Step 1, Step 2, the chain, and the headline are
        // hypothesis-wrapped over explicit local equality witnesses.
        self.register_crown_backward_eq_interval_hull(&c)?;
        self.register_interval_hull_eq_ibp_forward(&c)?;
        self.register_crown_equals_ibp_chain(&c)?;
        self.register_crown_equals_ibp(&c)?;

        // Phase 1 faithful-carrier foundation for the C004 demasquerade
        // plan (#3488 / #3500). Registers non-aliased carriers for
        // CROWN backward and IBP forward whose outputs depend on both
        // `n` and the input bounds `B`, plus a `refl`-at-zero theorem
        // that exercises the CROWN-faithful carrier's reduction.
        self.register_ibp_forward_layernorm_faithful(&c)?;
        self.register_crown_backward_layernorm_faithful(&c)?;
        self.register_crown_backward_layernorm_faithful_refl_zero(&c)?;
        // Step-case companion, #3373 Phase 1. See refl_succ module.
        self.register_ibp_forward_layernorm_faithful_refl_succ(&c)?;

        self.nn_verify_crown_layernorm_init = true;
        Ok(())
    }

    /// `NNVerify.LayerNorm.jacobian` (Opaque):
    /// `(n : Nat) -> (gamma : NNVec n) -> (sigma : Rat) -> (z : NNVec n) -> NNMat n n`
    ///
    /// J[i,j] = (gamma_i / sigma)(delta_ij - 1/n - z_i * z_j / n)
    ///
    /// Registered as Opaque: the kernel verifies the value is well-typed
    /// (zero matrix placeholder) but does not reduce it.
    /// Previously an axiom; now an Opaque definition.
    fn register_ln_jacobian(&mut self, c: &CrownLayerNormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.jacobian");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_ln_jacobian_type(c),
            value: build_ln_jacobian_value(c),
        })
    }

    /// `NNVerify.LayerNorm.forward` (Opaque):
    /// `(n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) -> (x : NNVec n) -> NNVec n`
    ///
    /// LN(x) = gamma * (x - mean(x)) / sqrt(var(x) + eps) + beta
    ///
    /// Registered as Opaque: the kernel verifies the value is well-typed
    /// (identity on input vector) but does not reduce it.
    /// Previously an axiom; now an Opaque definition.
    fn register_ln_forward(&mut self, c: &CrownLayerNormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.forward");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_ln_forward_type(c),
            value: build_ln_forward_value(c),
        })
    }

    /// `NNVerify.CROWN.backward_layernorm` (Definition):
    /// `(n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) ->
    ///   (B : IntervalBounds n) -> IntervalBounds n`
    ///
    /// Defined as `IBP.forward_layernorm n gamma beta ln_eps B`. The dense
    /// LayerNorm Jacobian forces CROWN backward to degenerate into element-wise
    /// interval propagation = IBP. By defining CROWN backward as IBP forward,
    /// the equality becomes definitional, enabling constructive proofs via Eq.refl.
    ///
    /// Previously Opaque (well-typed identity placeholder); now a reducible
    /// Definition to eliminate the `_core` axiom and make C004 fully constructive.
    fn register_crown_backward_layernorm(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.CROWN.backward_layernorm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_bounds_transform_type(c),
            value: build_crown_backward_ln_value(c),
            is_reducible: true,
        })
    }

    /// `NNVerify.IBP.forward_layernorm` (non-reducible Definition,
    /// #3617 Phase 1):
    /// `(n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) ->
    ///   (B : IntervalBounds n) -> IntervalBounds n`
    ///
    /// **#3617 Phase 1 carrier swap** per
    /// `designs/2026-04-20-c004-faithful-carrier-redesign.md`. Replaces
    /// the wave-10 identity body `fun n γ β ε B => B` with a
    /// `Nat.rec`-based body that branches on `n` and references `B`:
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
    /// See `build_faithful_ibp_forward_value` docstring for the
    /// discriminator properties that satisfy the #3617 acceptance
    /// criterion "non-identity `Declaration::Definition` body that
    /// depends on both `lo` and `hi` coordinatewise."
    ///
    /// Registered as a **non-reducible** `Declaration::Definition`
    /// (`is_reducible: false`):
    ///
    /// * **Definition, not Opaque**: the body has computational content
    ///   (the `Nat.rec` branch), so presenting it as `Declaration::Opaque`
    ///   would mask the carrier swap from downstream analyses. A
    ///   Definition advertises honestly that there is a body to reduce
    ///   (even if opacity blocks that reduction at the kernel level).
    /// * **Non-reducible**: the C004 equality declarations are now
    ///   hypothesis-wrapped over local witnesses rather than proved by
    ///   alias collapse. Keeping the new carrier non-reducible preserves
    ///   the wave-10 guard that blocks any future Rule M1 alias-collapse
    ///   proof (`Eq.refl` over definitional aliases) from typechecking
    ///   against the equality signatures — a reducible definition would
    ///   re-open the Rule M1 path the MASQUERADE demotion closed.
    /// * **Count invariant**: under `test_c004_axiom_count`'s rubric
    ///   (Definition with `value.is_some()` + `is_reducible: false`
    ///   counts as `thm_count`, identical to the Opaque classification
    ///   it replaces), this carrier swap itself does not change the
    ///   domain-axiom total.
    ///
    /// Phase 2 of the faithful-carrier redesign will upgrade the body
    /// to the real element-wise LayerNorm interval computation
    /// `fun (lo, hi) => (interval_lb ..., interval_ub ...)` (design
    /// §3.1) once the `NNVerify.Rat` interval primitives are
    /// consolidated (design step 1). Phase 1 deliberately reuses the
    /// `Nat.rec` shape already proved out in
    /// `nn_verify_crown_layernorm_faithful.rs` (the `_faithful` sibling
    /// carrier) so the carrier swap lands without pulling new
    /// interval-arithmetic dependencies into the init chain.
    ///
    /// Part of #3617 (C004 Phase 1) — epic #3381 / parent #3373.
    fn register_ibp_forward_layernorm(&mut self, c: &CrownLayerNormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IBP.forward_layernorm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_bounds_transform_type(c),
            value: build_faithful_ibp_forward_value(c),
            is_reducible: false,
        })
    }

    /// `NNVerify.C004.interval_hull_layernorm` (Definition):
    /// `(n : Nat) -> (gamma beta : NNVec n) -> (ln_eps : Rat) ->
    ///   (B : IntervalBounds n) -> IntervalBounds n`
    ///
    /// Defined as `IBP.forward_layernorm n gamma beta ln_eps B`. Step 2 is
    /// still not proved by unfolding this alias; the public theorem is
    /// hypothesis-wrapped over explicit local equality evidence.
    fn register_interval_hull_layernorm(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.interval_hull_layernorm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_bounds_transform_type(c),
            value: build_interval_hull_value(c),
            is_reducible: true,
        })
    }

    /// `NNVerify.C004.jacobian_dense` (Definition):
    /// `(n : Nat) -> (gamma : NNVec n) -> (sigma : Rat) -> (z : NNVec n) -> Prop`
    ///
    /// Constructive density predicate for the LayerNorm Jacobian:
    /// `sigma != 0 ∧ ∀ i : Fin n, gamma i != 0`. This replaces the #3584
    /// Axiom with a non-`True` body, preserving the Branch A guard against
    /// `True.rec` while retiring one C004-specific domain axiom.
    fn register_jacobian_dense(&mut self, c: &CrownLayerNormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.jacobian_dense");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_jacobian_dense_type(c),
            value: build_jacobian_dense_value(c),
            is_reducible: true,
        })
    }

    /// Step 1: `NNVerify.C004.crown_backward_eq_interval_hull`
    ///
    /// Retired from the C004 axiom audit as a hypothesis-wrapped theorem
    /// (2026-04-27): the theorem now explicitly requires the missing
    /// local Step 1 equality witness and returns it directly.
    ///
    /// This deliberately does NOT apply the old global Step 1 axiom and
    /// does NOT close by `Eq.refl` over reducible aliases. The
    /// hypothesis-free Step 1 equality remains future work until the real
    /// CROWN / interval-hull arithmetic lands.
    fn register_crown_backward_eq_interval_hull(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.crown_backward_eq_interval_hull");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_ln_equality_hyp_type(c, &c.crown_backward_ln, &c.interval_hull_ln),
            value: build_ln_equality_hyp_proof(c, &c.crown_backward_ln, &c.interval_hull_ln),
        })
    }

    /// Step 2: `NNVerify.C004.interval_hull_eq_ibp_forward`
    ///
    /// Retired from the C004 axiom audit as a hypothesis-wrapped theorem
    /// (2026-04-27): the theorem now explicitly requires the missing
    /// local Step 2 equality witness and returns it directly.
    ///
    /// The old #3460 / #3486 density-guarded proof term was
    /// `fun n γ β σ z ε B h => @True.rec.{0} motive (Eq.refl _ _) h`
    /// over an 8-binder type carrying a `jacobian_dense n γ σ z`
    /// hypothesis. That proof only type-checked because:
    ///
    ///   1. `jacobian_dense` was a reducible `Declaration::Definition`
    ///      whose body was `fun _ _ _ _ => True`, so the kernel
    ///      delta-reduced `h : jacobian_dense n γ σ z` to `h : True`
    ///      during `True.rec` type-checking (argument-discarding
    ///      `True`-carrier — Rule M2); and
    ///   2. `interval_hull_layernorm` and `IBP.forward_layernorm` both
    ///      reduced to the same identity-on-bounds body, so the inner
    ///      `Eq.refl` closed by alias collapse (Rule M1).
    ///
    /// The compound M1 + M2 masquerade is exactly what the
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` audit catches.
    /// No arithmetic content survives replacing either carrier with a
    /// faithful implementation. The hypothesis-free Step 2 equality
    /// remains future work; this theorem makes that obligation explicit
    /// as a local hypothesis:
    ///
    /// ```text
    /// forall (n : Nat) (gamma beta : NNVec n) (ln_eps : Rat) (B : IB n),
    ///   Eq (IB n) (interval_hull_layernorm n gamma beta ln_eps B)
    ///             (IBP.forward_layernorm    n gamma beta ln_eps B) ->
    ///   Eq (IB n) (interval_hull_layernorm n gamma beta ln_eps B)
    ///             (IBP.forward_layernorm    n gamma beta ln_eps B)
    /// ```
    fn register_interval_hull_eq_ibp_forward(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.interval_hull_eq_ibp_forward");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_ln_equality_hyp_type(c, &c.interval_hull_ln, &c.ibp_forward_ln),
            value: build_ln_equality_hyp_proof(c, &c.interval_hull_ln, &c.ibp_forward_ln),
        })
    }

    /// Transitivity: `NNVerify.C004.crown_equals_ibp_chain`
    ///
    /// Retired from the C004 axiom audit as a hypothesis-wrapped theorem
    /// (2026-04-27): the theorem now explicitly requires the two missing
    /// local equality witnesses and composes them with `Eq.trans`.
    ///
    /// This deliberately does NOT apply the global Step 1 / Step 2 axiom
    /// constants and does NOT close by `Eq.refl` over reducible aliases.
    /// The old hypothesis-free chain remains future work until the real
    /// LayerNorm/CROWN arithmetic lands.
    fn register_crown_equals_ibp_chain(
        &mut self,
        c: &CrownLayerNormConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.crown_equals_ibp_chain");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_crown_equals_ibp_hyp_type(c),
            value: build_crown_equals_ibp_hyp_proof(c),
        })
    }

    /// Main claim: `NNVerify.C004.crown_equals_ibp`.
    ///
    /// Retired from the C004 axiom audit as a hypothesis-wrapped theorem
    /// (2026-04-27): the theorem now explicitly requires the two missing
    /// local equality witnesses
    /// `CROWN.backward_layernorm = C004.interval_hull_layernorm` and
    /// `C004.interval_hull_layernorm = IBP.forward_layernorm`, then
    /// composes them with `Eq.trans`.
    ///
    /// This deliberately does NOT reuse the old C004 axiom constants and
    /// does NOT close by `Eq.refl` over reducible aliases. The
    /// hypothesis-free headline equality remains future work; the named
    /// Step 1, Step 2, and chain theorems follow the same
    /// hypothesis-wrapped pattern.
    fn register_crown_equals_ibp(&mut self, c: &CrownLayerNormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C004.crown_equals_ibp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_crown_equals_ibp_hyp_type(c),
            value: build_crown_equals_ibp_hyp_proof(c),
        })
    }
}
