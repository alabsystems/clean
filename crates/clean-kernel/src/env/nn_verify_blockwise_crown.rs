// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C006: Block-wise CROWN Equals Monolithic CROWN - HYPOTHESIS WRAPPED
//!
//! **Status (2026-04-19 demotion, #3489-#3494; 2026-04-20 carrier
//! cleanup, #3500/#3638; 2026-04-26 Phase 2/3; 2026-04-27 induction
//! wrapper):** This file registers zero core `Declaration::Axiom`
//! entries and four hypothesis-wrapped `Declaration::Theorem`
//! entries (`blockwise_base`, `blockwise_step`, `blockwise_nat_induction`,
//! `blockwise_equals_monolithic`), reducible
//! indexed carrier definitions (`Block.compose`, `Block.monolithic_crown`,
//! and `C006.mono_step`), plus opaque proposition/function placeholders
//! (`Block.ibp_transfer`, `C006.per_block_crown_matches_mono`,
//! `C006.follows_from_c004`).
//!
//! **SOUNDNESS:** Previously these four C006 claims were registered as
//! `Declaration::Theorem` with Eq.refl / Nat.rec proof terms. The
//! 2026-04-19 NN-verify shard audit
//! (`reports/audit/2026-04-19-clean-native-shard-audit.md`, entries 5-8)
//! established that the proofs close only because both `Block.compose`
//! and `Block.monolithic_crown` were reducible Definitions whose body is
//! literally `zero_ib (block_dim k)`. The `Nat.rec` scaffolding over a
//! vacuous predicate cannot establish anything about real CROWN
//! composition. Per the design doc Proof Soundness Rules, a Theorem
//! wrapping a syntactic tautology is a masquerade, not a proof.
//!
//! - **Theorem -> Axiom** (#3489, #3491, #3492, #3493): the four
//!   former `Declaration::Theorem` entries were demoted so the axiom
//!   count honestly reflects the unverified claim.
//! - **Definition -> Opaque** (#3500 Branch A, 2026-04-20):
//!   `Block.compose` and `Block.monolithic_crown` are co-demoted to
//!   `Declaration::Opaque` with the SAME body. The δ-reduction path
//!   `compose k … = monolithic k … = zero_ib (block_dim k)` is closed,
//!   so no future downstream theorem can re-introduce the same
//!   masquerade via alias collapse.
//! - **Phase 1 indexed carriers** (#3638, 2026-04-20): `Block.compose`
//!   and `Block.monolithic_crown` become reducible indexed Nat.rec
//!   carriers with distinct step functions.
//! - **Phase 2 headline theorem** (2026-04-26): `blockwise_equals_monolithic`
//!   is promoted to a theorem by adding the missing pointwise hypothesis
//!   `forall i X, crown_block i X = mono_step ... i X`; the proof is a
//!   real Nat.rec using that hypothesis plus the induction hypothesis.
//! - **Phase 3 base theorem** (2026-04-26): `blockwise_base` is promoted to a
//!   theorem by adding the missing input-zero hypothesis `B = zero_ib`; the
//!   proof reuses that hypothesis for both k=0 carrier reductions.
//!
//! Refs: #3489, #3491, #3492, #3493, #3500.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//! See: reports/audit/2026-04-19-clean-native-shard-audit.md
//!
//! ---
//!
//! Formalizes the result that for a network N = B_k . LN . B_{k-1} . LN . ... . B_1,
//! where LN is LayerNorm and B_i are transformer blocks, the block-wise CROWN
//! computation (CROWN each block independently with interval transfer at LN
//! boundaries) produces bounds identical to monolithic CROWN over the entire
//! network.
//!
//! # Mathematical Background
//!
//! By C004 (CROWN through LayerNorm = IBP), CROWN backward propagation through
//! LayerNorm degenerates to interval propagation. Cross-block CROWN correlations
//! carry zero information through LayerNorm boundaries. Therefore block-wise
//! CROWN with interval transfer equals full network CROWN.
//!
//! # Proof Architecture
//!
//! The hypothesis-free C006 claim is still not proved. The theorem surface now
//! exposes the missing local evidence explicitly:
//! - **Base (k=0)**: `blockwise_base` theorem — hypothesis-wrapped
//!   zero-input value characterization.
//! - **Step (k -> k+1)**: `blockwise_step` theorem — hypothesis-wrapped
//!   pointwise step evidence matching `crown_block` to `mono_step`.
//! - **Combinator**: `blockwise_nat_induction` theorem — hypothesis-wrapped
//!   local induction evidence (`forall j, inner j`) returning the `k` case.
//! - **Headline theorem**: `blockwise_equals_monolithic` now has an extra
//!   per-block mono-step hypothesis and is proved constructively from it.
//!
//! Theorem type/proof builders live in `nn_verify_blockwise_crown_defs`.
//!
//! Part of #3197.

use super::nn_verify_blockwise_crown_base;
use super::nn_verify_blockwise_crown_defs;
use super::nn_verify_blockwise_crown_hyp;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C006 block-wise CROWN proof construction.
pub(super) struct BlockwiseCrownConsts {
    pub(super) nat: Expr,
    pub(super) nat_zero: Expr,
    pub(super) nat_succ: Expr,
    pub(super) rat: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) eq: Expr,
    pub(super) prop: Expr,
    pub(super) block_compose: Expr,
    pub(super) monolithic_crown: Expr,
}

impl BlockwiseCrownConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            prop: Expr::sort(Level::zero()),
            block_compose: Expr::const_(Name::from_string("NNVerify.Block.compose"), vec![]),
            monolithic_crown: Expr::const_(
                Name::from_string("NNVerify.Block.monolithic_crown"),
                vec![],
            ),
        }
    }

    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    pub(super) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    pub(super) fn ib_eq(&self, d: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.ib_of(d.clone())), lhs),
            rhs,
        )
    }

    /// Type for block dimension family: `(i : Nat) -> Nat`
    pub(super) fn block_dim_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nat.clone())
    }

    /// Apply dimension family: `block_dim i`
    pub(super) fn dim_at(&self, block_dim: &Expr, i: Expr) -> Expr {
        Expr::app(block_dim.clone(), i)
    }

    /// Type for LN parameter families: `(i : Nat) -> NNVec (block_dim i)`
    pub(super) fn ln_param_family_ty(&self, outer: &EnvDeclBuilder, block_dim: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(self.nat.clone());
        let body = self.vec_of(self.dim_at(block_dim, i));
        let r = ch.mk_pi(i_id, BinderInfo::Default, self.nat.clone(), body);
        ch.finish_child(r)
    }

    /// Type for per-block CROWN function family:
    /// `(i : Nat) -> IB (block_dim i) -> IB (block_dim (i+1))`
    pub(super) fn crown_block_family_ty(&self, outer: &EnvDeclBuilder, block_dim: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(self.nat.clone());
        let ib_in = self.ib_of(self.dim_at(block_dim, i.clone()));
        let ib_out = self.ib_of(self.dim_at(block_dim, Expr::app(self.nat_succ.clone(), i)));
        let body = Expr::pi(BinderInfo::Default, ib_in, ib_out);
        let r = ch.mk_pi(i_id, BinderInfo::Default, self.nat.clone(), body);
        ch.finish_child(r)
    }
}

// Type builders (build_ibp_transfer_type, build_block_compose_type) and
// Opaque register functions (register_ibp_transfer, register_block_compose,
// register_monolithic_crown, build_c006_zero_ib) are in
// nn_verify_blockwise_crown_values.rs

impl Environment {
    /// Initialize C006 (block-wise CROWN = monolithic) declarations.
    ///
    /// Registers 10 declarations (zero remaining core C006 axioms,
    /// 4 hypothesis-wrapped theorems, 3 reducible carrier/helper definitions,
    /// and 3 opaque placeholders):
    /// - `Block.ibp_transfer` — interval transfer through LayerNorm (Opaque)
    /// - `Block.compose` — block-wise CROWN composition (Definition;
    ///   Phase-1 indexed Nat.rec carrier)
    /// - `Block.monolithic_crown` — monolithic CROWN over entire network
    ///   (Definition; Phase-1 indexed Nat.rec carrier)
    /// - `C006.mono_step` — monolithic successor helper (Definition)
    /// - `C006.per_block_crown_matches_mono` — pointwise hypothesis
    ///   placeholder (Opaque Prop)
    /// - `C006.blockwise_base` — base case (hypothesis-wrapped theorem)
    /// - `C006.blockwise_step` — step case (hypothesis-wrapped theorem)
    /// - `C006.blockwise_nat_induction` — induction combinator
    ///   (hypothesis-wrapped theorem)
    /// - `C006.blockwise_equals_monolithic` — headline theorem
    ///   (hypothesis-wrapped Phase-2 theorem)
    /// - `C006.follows_from_c004` — C004 -> C006 implication (Opaque,
    ///   returns `Prop`)
    ///
    /// The former `Declaration::Theorem` registrations (#3375) closed
    /// with `Eq.refl` / `Nat.rec` only because `Block.compose` and
    /// `Block.monolithic_crown` were reducible Definitions with identical
    /// placeholder bodies. That pathway is closed now: the remaining
    /// unwrapped helper claims are Axioms, the wrapped base/headline
    /// theorems state their extra hypotheses explicitly, and the Phase-1
    /// carriers have distinct indexed step bodies so no δ-reduction can collapse
    /// `compose = monolithic` to the old shared `zero_ib` body.
    ///
    /// Depends on:
    /// - `init_nn_verify_crown_layernorm()` for C004 declarations
    /// - `init_nn_verify_types()` for NNVec, IntervalBounds
    /// - `init_eq()` for Eq
    /// - `init_rat_linear_order()` for Rat.le_refl (used in zero_ib value terms)
    pub fn init_nn_verify_blockwise_crown(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_blockwise_crown_init {
            return Ok(());
        }
        self.init_nn_verify_shared_bootstrap()?;
        self.init_nn_verify_crown_layernorm()?;

        let c = BlockwiseCrownConsts::new();
        self.register_ibp_transfer(&c)?;
        // #3638 Phase 1: register mono_step BEFORE monolithic_crown —
        // the latter's body references `C006.mono_step` as a Const and the
        // kernel's add_decl requires referenced consts to exist first.
        self.register_mono_step(&c)?;
        self.register_per_block_crown_matches_mono(&c)?;
        self.register_block_compose(&c)?;
        self.register_monolithic_crown(&c)?;
        self.register_blockwise_base(&c)?;
        self.register_blockwise_step(&c)?;
        self.register_blockwise_equals_monolithic_impl(&c)?;
        self.register_follows_from_c004(&c)?;

        self.nn_verify_blockwise_crown_init = true;
        Ok(())
    }

    // Opaque register functions (register_ibp_transfer, register_block_compose,
    // register_monolithic_crown, build_c006_zero_ib) and type builders
    // (build_ibp_transfer_type, build_block_compose_type) are in
    // nn_verify_blockwise_crown_values.rs

    /// Base case theorem: under `B = zero_ib`, both k=0 carriers equal `zero_ib`.
    ///
    /// SOUNDNESS (2026-04-19 demotion, #3489, finalized #3519): previously
    /// registered as a `Declaration::Theorem` with an `And.intro` of two
    /// `Eq.refl` proofs that closes only because `Block.compose` and
    /// `Block.monolithic_crown` are reducible Definitions whose body is
    /// `zero_ib (block_dim k)`. The kernel was proving "zero = zero," not
    /// anything about real CROWN composition. Auditor round 6 F3 finding
    /// (reports/audit/2026-04-19-auditor-round6.md) confirmed the Theorem
    /// registration contradicted the documented axiom_audit entry for C006
    /// (`masquerade_demoted`, axioms: 8). The claim was demoted to
    /// Declaration::Axiom to match the documented audit decision. See
    /// reports/audit/2026-04-19-clean-native-shard-audit.md entry 5.
    ///
    /// Phase 3 (2026-04-26): with the indexed Phase-1 carriers, k=0 reduces
    /// to the input bounds `B`, not to the zero interval. The theorem is
    /// therefore re-promoted only after adding the explicit hypothesis
    /// `B = zero_ib`; the proof is `And.intro h h` after carrier reduction.
    fn register_blockwise_base(&mut self, c: &BlockwiseCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C006.blockwise_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: nn_verify_blockwise_crown_base::build_blockwise_base_type(c),
            value: nn_verify_blockwise_crown_base::build_blockwise_base_proof(c),
        })
    }

    /// Inductive step theorem: given local pointwise step evidence and
    /// compose k = monolithic k, derive succ k.
    ///
    /// SOUNDNESS (2026-04-19 demotion, #3491): previously registered as a
    /// `Declaration::Theorem` whose body lambda-bound the induction
    /// hypothesis and never referenced it — the conclusion closed by
    /// `Eq.refl` because both carriers reduce to the same `zero_ib` at
    /// any k. An inductive step that ignores its induction hypothesis
    /// is a canonical sign of a vacuous predicate.
    /// See reports/audit/2026-04-19-clean-native-shard-audit.md entry 6.
    fn register_blockwise_step(&mut self, c: &BlockwiseCrownConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C006.blockwise_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: nn_verify_blockwise_crown_hyp::build_blockwise_step_hyp_type(c),
            value: nn_verify_blockwise_crown_hyp::build_blockwise_step_hyp_proof(c),
        })
    }

    fn register_blockwise_equals_monolithic_impl(
        &mut self,
        c: &BlockwiseCrownConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.C006.blockwise_equals_monolithic",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.register_blockwise_nat_induction(c)?;
        // Phase 2 (2026-04-26): promote the headline name back to a real
        // theorem by adding the missing per-block hypothesis
        //   forall i X, crown_block i X = mono_step ... i X.
        // The proof is a Nat.rec over k whose successor branch consumes both
        // that hypothesis and the induction hypothesis via Eq.trans/congrArg.
        // It does not delegate to `blockwise_nat_induction`.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.C006.blockwise_equals_monolithic"),
            level_params: vec![],
            type_: nn_verify_blockwise_crown_hyp::build_blockwise_equals_monolithic_hyp_type(c),
            value: nn_verify_blockwise_crown_hyp::build_blockwise_equals_monolithic_hyp_proof(c),
        })
    }

    /// Hypothesis-wrapped induction combinator theorem.
    ///
    /// SOUNDNESS (2026-04-19 demotion, #3492, finalized #3519): previously a
    /// `Declaration::Theorem` with a real `Nat.rec` proof term combining
    /// `blockwise_base` and `blockwise_step`. The `Nat.rec` scaffolding
    /// is genuine Rust code, but both arguments it propagates (base and
    /// step) close by `Eq.refl` over placeholder carriers — the induction
    /// runs over a vacuous predicate. Moreover `blockwise_step` is itself an
    /// axiom post-demotion, so the Nat.rec successor case delegates to an
    /// unproven claim. Auditor round 6 F3 finding
    /// (reports/audit/2026-04-19-auditor-round6.md) confirmed the Theorem
    /// registration contradicted the documented axiom_audit entry. Now
    /// demoted to Declaration::Axiom to match the audit decision so the
    /// masquerade was not counted as a substantive theorem. The live theorem
    /// keeps the missing induction evidence explicit as a local hypothesis
    /// `forall j, compose j ... = monolithic_crown j ...` and returns the
    /// requested `k` instance.
    /// See reports/audit/2026-04-19-clean-native-shard-audit.md entry 7.
    fn register_blockwise_nat_induction(
        &mut self,
        c: &BlockwiseCrownConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C006.blockwise_nat_induction");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: nn_verify_blockwise_crown_hyp::build_blockwise_nat_induction_hyp_type(c),
            value: nn_verify_blockwise_crown_hyp::build_blockwise_nat_induction_hyp_proof(c),
        })
    }

    /// `NNVerify.C006.follows_from_c004` — C004 implies C006 (for any block count).
    ///
    /// The type is `forall n gamma beta eps B, (CROWN.backward_layernorm ... = IBP.forward_layernorm ...) -> Prop`.
    /// Since the conclusion is `Prop`, this is a proposition-valued function,
    /// trivially inhabited by returning `True` for any input.
    /// Converted from Axiom to Opaque (Category A: proposition-valued function).
    fn register_follows_from_c004(&mut self, c: &BlockwiseCrownConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C006.follows_from_c004"))
            .is_some()
        {
            return Ok(());
        }
        let ty = nn_verify_blockwise_crown_defs::build_follows_from_c004_type(c);
        let value = nn_verify_blockwise_crown_defs::build_follows_from_c004_value(c);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.C006.follows_from_c004"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
