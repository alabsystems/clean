// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stratified Hurkens block, groups A-D: the Hurkens objects, the literal
//! Level terms the pi rule produces, the denotational level pins, and the
//! Level/KExpr no-confusion transport probes.
//!
//! Split out of the parent module purely for file size; registration order
//! is still fixed by `add_stratified_hurkens_block` in `mod.rs`, which calls
//! this half first.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

use super::*;

impl Specification {
    /// Groups A-D of the stratified Hurkens block. Called only by
    /// `add_stratified_hurkens_block`, and only before `add_hurkens_block`.
    pub(super) fn add_hurkens_objects(&mut self) -> Result<(), SpecError> {
        // --- Group A: the Hurkens objects (Blocking.lean:82-92) ---
        self.add_recursive_def(
            SRC_POWR,
            "powr X = Pi X. sort 0 — the powerset-style formation PX = X -> sort 0 of \
             Hurkens' paradox, as a KExpr constructor term (Blocking.lean:82). X sits in \
             domain position (no de Bruijn shift); the codomain sort 0 is closed. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_POWR2,
            "powr2 X = powr (powr X) — PPX (Blocking.lean:85). Plain def.",
        )?;
        self.add_recursive_def(
            SRC_U0_ARROW,
            "U0_arrow = (PP X -> X) under U0's outer binder: pi with domain powr2 (bvar 0) \
             (X at binder depth 0) and codomain bvar 1 (X under the arrow's own binder). \
             Faithful de Bruijn translation of Blocking.lean:92's inner pi. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_U0_BODY,
            "U0_body = (PPX -> X) -> PPX under U0's outer binder: pi with domain U0_arrow \
             and codomain powr2 (bvar 1) (X under the arrow binder). Blocking.lean:92. \
             Plain def.",
        )?;
        self.add_recursive_def(
            SRC_U0,
            "U0 = Pi X : sort 0. ((PPX -> X) -> PPX) — Hurkens' powerful universe with \
             level-0 annotations, as a CLOSED KExpr (Blocking.lean:91-92). Plain def.",
        )?;

        // --- Group B: the literal Level terms ---
        self.add_recursive_def(
            SRC_POWR_LEVEL,
            "powr_level = imax 0 1 as a LITERAL Level constructor term — the exact sort \
             index TypingCtx's pi rule produces for powr X when X : sort 0. The spec's \
             Level.imax is a plain constructor (no smart-constructor collapse), so this is \
             NOT the literal succ zero; hk_level_val pins its VALUE to 1. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_POWR2_LEVEL,
            "powr2_level = imax powr_level 1 — the literal sort index of powr2 X when \
             X : sort 0. Value pinned to 1 by powr2_level_val_one. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_U0_ARROW_LEVEL,
            "U0_arrow_level = imax powr2_level 0 — the literal sort index of the inner \
             arrow PPX -> X. This is the ONE place the corpus fires the impredicative \
             clause imax 1 0 = 0 (Blocking.lean:136-138); here it stays a literal imax, and \
             only its VALUE is 0 (U0_arrow_level_val_zero). Plain def.",
        )?;
        self.add_recursive_def(
            SRC_U0_LEVEL,
            "U0_level = imax 1 (imax U0_arrow_level powr2_level) — the literal sort index \
             the pi rule produces for U0. The spec has no level normalization, so \
             typingctx_U0_formable states THIS term; its value is pinned to 1 \
             (U0_level_val_one), matching the corpus U0_formable : sort 1. Plain def.",
        )?;

        // --- Group C: denotational semantics + pins ---
        self.add_recursive_def(
            SRC_HK_MAX_NAT,
            "hk_max_nat n m = n + (m - n) = max(n, m) under truncated subtraction — the \
             Nat max used to interpret Level.max in hk_level_val. Plain def.",
        )?;
        self.add_recursive_def(
            SRC_HK_LEVEL_VAL,
            "hk_level_val rho l: the standard denotational Nat value of a Level under a \
             parameter assignment rho (zero->0, succ->+1, max->hk_max_nat, imax->imax_nat, \
             param nm->rho nm). Computes by Level.rec on constructors, so the module's \
             concrete (param-free) levels evaluate by Eq.refl for EVERY rho. Plain def.",
        )?;
        self.add_definition(SpecDefinition {
            name: "powr_level_val_one".to_string(),
            type_src: TY_POWR_LEVEL_VAL_ONE.to_string(),
            value_src: Some(VAL_POWR_LEVEL_VAL_ONE.to_string()),
            is_axiom: false,
            description: "Value pin: hk_level_val rho powr_level = 1 for every rho, by Eq.refl \
                          computation (imax_nat 0 1 = 1) — the corpus imax_zero_one \
                          (Blocking.lean:96). PX lands one level up SEMANTICALLY even though \
                          the literal is an imax term. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_level_val".to_string(),
                "powr_level".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "powr2_level_val_one".to_string(),
            type_src: TY_POWR2_LEVEL_VAL_ONE.to_string(),
            value_src: Some(VAL_POWR2_LEVEL_VAL_ONE.to_string()),
            is_axiom: false,
            description: "Value pin: hk_level_val rho powr2_level = 1 for every rho, by Eq.refl \
                          computation (imax_nat 1 1 = 1) — the corpus imax_one_one \
                          (Blocking.lean:97). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_level_val".to_string(),
                "powr2_level".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "U0_arrow_level_val_zero".to_string(),
            type_src: TY_U0_ARROW_LEVEL_VAL_ZERO.to_string(),
            value_src: Some(VAL_U0_ARROW_LEVEL_VAL_ZERO.to_string()),
            is_axiom: false,
            description: "Value pin: hk_level_val rho U0_arrow_level = 0 for every rho, by \
                          Eq.refl computation (imax_nat 1 0 = 0) — the impredicative clause \
                          fires SEMANTICALLY on the inner arrow PPX -> X exactly as in the \
                          corpus U0_formable (Blocking.lean:136-138), while the LITERAL level \
                          stays a non-zero imax term. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_level_val".to_string(),
                "U0_arrow_level".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "U0_level_val_one".to_string(),
            type_src: TY_U0_LEVEL_VAL_ONE.to_string(),
            value_src: Some(VAL_U0_LEVEL_VAL_ONE.to_string()),
            is_axiom: false,
            description: "Value pin: hk_level_val rho U0_level = 1 for every rho, by Eq.refl \
                          computation — U0 exists at semantic level 1, the reflected \
                          counterpart of the corpus U0_formable : HasType [] U0 (sort 1) \
                          (Blocking.lean:129). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_level_val".to_string(),
                "U0_level".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group D: no-confusion probes ---
        self.add_recursive_def(
            SRC_HK_LEVEL_ZERO_FLAG,
            "hk_level_zero_flag l: Empty at Level.zero, ConstFreeUnit at succ/max/imax/param. \
             The transport probe for Level no-confusion against zero: from Eq Level X zero \
             with X a non-zero constructor, Eq.substType carries ConstFreeUnit.triv into \
             Empty. Computes by Level.rec on constructors. Plain def.",
        )?;
        self.add_definition(SpecDefinition {
            name: "level_succ_ne_zero".to_string(),
            type_src: TY_LEVEL_SUCC_NE_ZERO.to_string(),
            value_src: Some(VAL_LEVEL_SUCC_NE_ZERO.to_string()),
            is_axiom: false,
            description: "Level no-confusion: the literal Level.succ a is never the literal \
                          Level.zero (transport ConstFreeUnit.triv along the equation into \
                          hk_level_zero_flag zero = Empty). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_level_zero_flag".to_string(),
                "Eq.substType".to_string(),
                "ConstFreeUnit.triv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "level_imax_ne_zero".to_string(),
            type_src: TY_LEVEL_IMAX_NE_ZERO.to_string(),
            value_src: Some(VAL_LEVEL_IMAX_NE_ZERO.to_string()),
            is_axiom: false,
            description: "Level no-confusion, THE ENGINE OF THE BLOCK: the literal \
                          Level.imax a b is never the literal Level.zero, for ANY a b — in \
                          the conv-free literal-level TypingCtx the impredicative escape \
                          imax n 0 = 0 never fires syntactically, so no pi rule conclusion \
                          can be sort zero. (The corpus engine powr2_not_small needs the \
                          sharper second-component-is-succ fact because its imax is a \
                          Nat-valued FUNCTION; here the constructor disequality suffices — \
                          see the module docs honesty note.) Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_level_zero_flag".to_string(),
                "Eq.substType".to_string(),
                "ConstFreeUnit.triv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_recursive_def(
            SRC_HK_NONPI_FLAG,
            "hk_nonpi_flag e: Empty at KExpr.pi, ConstFreeUnit at the other eight \
             constructors. The transport probe for KExpr head discrimination against pi \
             (the six non-pi inversion arms). Computes by KExpr.rec on constructors. \
             Plain def.",
        )?;
        self.add_definition(SpecDefinition {
            name: "hk_kill_nonpi".to_string(),
            type_src: TY_HK_KILL_NONPI.to_string(),
            value_src: Some(VAL_HK_KILL_NONPI.to_string()),
            is_axiom: false,
            description: "KExpr discrimination against pi: from Eq KExpr x (pi PA PB) and an \
                          inhabitant of hk_nonpi_flag x (ConstFreeUnit.triv at any concrete \
                          non-pi constructor, where the flag computes), Empty follows by \
                          Eq.substType transport. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_nonpi_flag".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "hk_nonpi_flag_witness".to_string(),
            type_src: TY_HK_NONPI_FLAG_WITNESS.to_string(),
            value_src: Some(VAL_HK_NONPI_FLAG_WITNESS.to_string()),
            is_axiom: false,
            description: "PREMISE-SATISFIABILITY WITNESS for the discrimination probe: \
                          hk_nonpi_flag IS INHABITED, at sort 0. hk_kill_nonpi assumes \
                          hk_nonpi_flag x as a hypothesis, and until this was registered \
                          nothing in the spec CONCLUDED it — the six non-pi arms of \
                          typingctx_pi_small_inv pass ConstFreeUnit.triv inline, which is a \
                          use and not a supply. A flag that were Empty at every former would \
                          make hk_kill_nonpi unusable while every axiom-shaped metric stayed \
                          green, so the flag's positive side is pinned here: at a sort the \
                          KExpr.rec computes to ConstFreeUnit and the witness is one \
                          constructor. Read with hk_kill_nonpi, which is the NEGATIVE side \
                          (Empty at KExpr.pi). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "hk_nonpi_flag".to_string(),
                "ConstFreeUnit.triv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
