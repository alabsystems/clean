// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C004 Rat Interval Primitives (Step 1 of
//! `designs/2026-04-20-c004-faithful-carrier-redesign.md`)
//!
//! Consolidates the four scalar `Rat` interval primitives that the C004
//! faithful carrier redesign needs for its element-wise LayerNorm
//! interval arithmetic bodies:
//!
//! | Name                               | Meaning |
//! |------------------------------------|---------|
//! | `NNVerify.Rat.interval_add`        | `(I ⊕ J) := (lo₁+lo₂, hi₁+hi₂)` |
//! | `NNVerify.Rat.interval_mul_by_pos` | `(s ·₊ I) := (s·lo, s·hi)`  (sound for `0 ≤ s`) |
//! | `NNVerify.Rat.interval_mul_by_neg` | `(s ·₋ I) := (s·hi, s·lo)`  (sound for `s ≤ 0`) |
//! | `NNVerify.Rat.interval_hull`       | `hull I J := (min lo₁ lo₂, max hi₁ hi₂)` |
//!
//! These are the named entry points the design doc §3.1/§3.2 calls for
//! when building `IBP.forward_layernorm_real`, `CROWN.backward_layernorm_real`,
//! and `C004.interval_hull_layernorm_real`. The underlying carrier type
//! is the existing `NNVerify.Interval` structure registered in
//! `nn_verify_interval_primitives.rs` (fields `lo`, `hi : Rat`).
//!
//! ## Relationship to `nn_verify_interval_primitives.rs`
//!
//! The sibling module `nn_verify_interval_primitives.rs` already registers
//! a generic `NNVerify.Interval.add` / `scalar_mul_pos` / `scalar_mul_neg`
//! trio plus `scalar_mul` (min/max variant). This module re-exposes those
//! operations under the **design-doc-mandated names** (so downstream
//! carrier work can refer to `interval_add` / `interval_mul_by_pos` /
//! `interval_mul_by_neg` exactly as the design doc specifies) and adds the
//! missing `interval_hull` primitive.
//!
//! Each Definition body is a thin wrapper:
//!
//! ```text
//! NNVerify.Rat.interval_add I J        := NNVerify.Interval.add I J
//! NNVerify.Rat.interval_mul_by_pos s I := NNVerify.Interval.scalar_mul_pos s I
//! NNVerify.Rat.interval_mul_by_neg s I := NNVerify.Interval.scalar_mul_neg s I
//! NNVerify.Rat.interval_hull I J       := NNVerify.Interval.mk (Rat.min I.lo J.lo) (Rat.max I.hi J.hi)
//! ```
//!
//! Registered as `Declaration::Definition` with `is_reducible: true` so
//! downstream proofs may discharge endpoint equalities via δ-reduction +
//! `Eq.refl`.
//!
//! ## Soundness
//!
//! No `add_decl_unchecked`, no `add_decl_structural`, no domain-specific
//! axioms. Every registered Definition is type-checked by the kernel via
//! `add_decl`. The type-check is the soundness proof: each body constructs
//! its output using already-type-checked building blocks (`Rat.add`,
//! `Rat.mul`, `Rat.min`, `Rat.max`, `NNVerify.Interval.mk`).
//!
//! ## Monotonicity lemmas
//!
//! The design doc also lists "monotonicity lemmas" (e.g., that
//! `interval_add` preserves the `lo ≤ hi` invariant when both inputs do,
//! that `interval_mul_by_pos` preserves order under a non-negative scale,
//! etc.). Those lemmas require proof terms over the existing `Rat`
//! ordered-field axioms; they are deferred to Step 4 of the design
//! (`crown_le_ibp_on_dense` / `ibp_le_crown_on_dense`) and tracked as a
//! follow-up slice under #3615. Step 1 only registers the carrier
//! primitives — the object-language definitions downstream lemmas will
//! range over.
//!
//! Part of #3615 (C004 Phase 1 — Step 1). Blocks: Step 2 (carrier body
//! swap in `nn_verify_crown_layernorm.rs`), Step 4 (core lemmas in the
//! follow-up `nn_verify_crown_ibp_equiv.rs`).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants used across the Rat interval primitive registrations.
struct RatIntervalConsts {
    rat: Expr,
    interval: Expr,
    interval_mk: Expr,
    interval_add: Expr,
    interval_smul_pos: Expr,
    interval_smul_neg: Expr,
    rat_min: Expr,
    rat_max: Expr,
}

impl RatIntervalConsts {
    fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            interval: Expr::const_(Name::from_string("NNVerify.Interval"), vec![]),
            interval_mk: Expr::const_(Name::from_string("NNVerify.Interval.mk"), vec![]),
            interval_add: Expr::const_(Name::from_string("NNVerify.Interval.add"), vec![]),
            interval_smul_pos: Expr::const_(
                Name::from_string("NNVerify.Interval.scalar_mul_pos"),
                vec![],
            ),
            interval_smul_neg: Expr::const_(
                Name::from_string("NNVerify.Interval.scalar_mul_neg"),
                vec![],
            ),
            rat_min: Expr::const_(Name::from_string("Rat.min"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
        }
    }

    /// Projection `I.lo` (field index 0).
    fn lo_proj(i: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.Interval"), 0, i.clone())
    }

    /// Projection `I.hi` (field index 1).
    fn hi_proj(i: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.Interval"), 1, i.clone())
    }
}

impl Environment {
    /// Initialize the C004 Step-1 `Rat` interval primitives (design
    /// `2026-04-20-c004-faithful-carrier-redesign.md` §3).
    ///
    /// Depends on `init_nn_verify_interval_primitives()` for the
    /// underlying `NNVerify.Interval` structure + generic
    /// `NNVerify.Interval.add` / `scalar_mul_pos` / `scalar_mul_neg`
    /// operations, and on `init_rat_minmax()` (transitively via
    /// `init_nn_verify_interval_primitives`) for `Rat.min` / `Rat.max`.
    ///
    /// Idempotent: safe to call multiple times.
    pub fn init_nn_verify_rat_interval(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_rat_interval_init {
            return Ok(());
        }
        self.init_nn_verify_interval_primitives()?;
        let c = RatIntervalConsts::new();
        self.register_rat_interval_add(&c)?;
        self.register_rat_interval_mul_by_pos(&c)?;
        self.register_rat_interval_mul_by_neg(&c)?;
        self.register_rat_interval_hull(&c)?;
        self.nn_verify_rat_interval_init = true;
        Ok(())
    }

    /// `NNVerify.Rat.interval_add (I J : NNVerify.Interval) : NNVerify.Interval`
    /// `  := NNVerify.Interval.add I J`
    ///
    /// Design-doc entry point; delegates to the already-registered
    /// generic `NNVerify.Interval.add`.
    fn register_rat_interval_add(&mut self, c: &RatIntervalConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let (j_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                j_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let body = Expr::apps(c.interval_add.clone(), [i, j]);
            let e = b.mk_lam(j_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Rat.interval_mul_by_pos (s : Rat) (I : Interval) : Interval`
    /// `  := NNVerify.Interval.scalar_mul_pos s I`
    ///
    /// Design-doc entry point; sound only when `0 ≤ s` (positive scale).
    /// Delegates to the already-registered `NNVerify.Interval.scalar_mul_pos`.
    fn register_rat_interval_mul_by_pos(&mut self, c: &RatIntervalConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_mul_by_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.rat.clone());
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                i_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let body = Expr::apps(c.interval_smul_pos.clone(), [s, i]);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Rat.interval_mul_by_neg (s : Rat) (I : Interval) : Interval`
    /// `  := NNVerify.Interval.scalar_mul_neg s I`
    ///
    /// Design-doc entry point; sound only when `s ≤ 0` (negative scale —
    /// endpoints swap under sign flip). Delegates to the already-registered
    /// `NNVerify.Interval.scalar_mul_neg`.
    fn register_rat_interval_mul_by_neg(&mut self, c: &RatIntervalConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_mul_by_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, _) = b.fresh_local(c.rat.clone());
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                i_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let body = Expr::apps(c.interval_smul_neg.clone(), [s, i]);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.Rat.interval_hull (I J : Interval) : Interval`
    /// `  := NNVerify.Interval.mk (Rat.min I.lo J.lo) (Rat.max I.hi J.hi)`
    ///
    /// The design-doc §3.3 primitive used to define the intermediate
    /// `C004.interval_hull_layernorm_real` carrier:
    ///
    /// ```text
    /// hull_of (L₁, U₁) (L₂, U₂) := (min L₁ L₂, max U₁ U₂)
    /// ```
    ///
    /// Sound when both inputs satisfy `lo ≤ hi`: the minimum of the two
    /// lower bounds is ≤ the minimum of the two upper bounds ≤ the
    /// maximum of the two upper bounds. Formalizing that validity
    /// invariant is deferred to a follow-up monotonicity-lemma slice
    /// (Step 4 of the design, tracked under #3615 follow-ups). The
    /// carrier itself is registered as a reducible Definition so
    /// downstream uses (`C004.interval_hull_layernorm_real`) can
    /// discharge endpoint equalities via δ-reduction.
    fn register_rat_interval_hull(&mut self, c: &RatIntervalConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_hull");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, _) = b.fresh_local(c.interval.clone());
            let (j_id, _) = b.fresh_local(c.interval.clone());
            let r = b.mk_pi(
                j_id,
                BinderInfo::Default,
                c.interval.clone(),
                c.interval.clone(),
            );
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let lo_min = Expr::apps(
                c.rat_min.clone(),
                [
                    RatIntervalConsts::lo_proj(&i),
                    RatIntervalConsts::lo_proj(&j),
                ],
            );
            let hi_max = Expr::apps(
                c.rat_max.clone(),
                [
                    RatIntervalConsts::hi_proj(&i),
                    RatIntervalConsts::hi_proj(&j),
                ],
            );
            let body = Expr::apps(c.interval_mk.clone(), [lo_min, hi_max]);
            let e = b.mk_lam(j_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
