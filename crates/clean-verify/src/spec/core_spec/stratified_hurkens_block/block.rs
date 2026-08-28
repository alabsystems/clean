// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stratified Hurkens block, groups E-G: the positive half (powr / powr2 /
//! U0 typings), the block itself (structural rule inversion), and the ground
//! non-vacuity witnesses over the empty const-env.
//!
//! Split out of the parent module purely for file size; these registrations
//! depend on groups A-D and run after them.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

use super::*;

impl Specification {
    /// Groups E-G of the stratified Hurkens block. Called only by
    /// `add_stratified_hurkens_block`, and only after `add_hurkens_objects`.
    pub(super) fn add_hurkens_block(&mut self) -> Result<(), SpecError> {
        // --- Group E: the positive half ---
        self.add_definition(SpecDefinition {
            name: "typingctx_powr_ty".to_string(),
            type_src: TY_TYPINGCTX_POWR_TY.to_string(),
            value_src: Some(VAL_TYPINGCTX_POWR_TY.to_string()),
            is_axiom: false,
            description: "Corpus powr_ty (Blocking.lean:101-105) for the conv-free TypingCtx: \
                          if X : sort 0 in G then powr X : sort powr_level in G, by one pi \
                          rule application (domain premise hX, codomain premise the sort \
                          rule under cons X G). The sort index is the LITERAL imax 0 1 the \
                          rule produces (no level normalization in this judgment); its value \
                          is pinned to 1 by powr_level_val_one. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtx".to_string(),
                "powr".to_string(),
                "powr_level".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_powr2_ty".to_string(),
            type_src: TY_TYPINGCTX_POWR2_TY.to_string(),
            value_src: Some(VAL_TYPINGCTX_POWR2_TY.to_string()),
            is_axiom: false,
            description: "Corpus powr2_ty (Blocking.lean:108-112) for the conv-free TypingCtx: \
                          if X : sort 0 in G then powr2 X : sort powr2_level in G — pi rule on \
                          top of typingctx_powr_ty. Literal sort index, value pinned to 1 by \
                          powr2_level_val_one. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtx".to_string(),
                "typingctx_powr_ty".to_string(),
                "powr2".to_string(),
                "powr2_level".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_U0_formable".to_string(),
            type_src: TY_TYPINGCTX_U0_FORMABLE.to_string(),
            value_src: Some(VAL_TYPINGCTX_U0_FORMABLE.to_string()),
            is_axiom: false,
            description: "HALF ONE of the block, corpus U0_formable (Blocking.lean:129-151): \
                          Hurkens' powerful universe U0 EXISTS in the empty context, at \
                          sort U0_level — the LITERAL nested-imax Level the pi rule produces \
                          (this judgment has no level normalization; U0_level's VALUE is \
                          pinned to 1 by U0_level_val_one, the corpus's sort 1). The three \
                          var-rule premises discharge by Eq.refl on ctx_lookup, exactly the \
                          typingctx_var_witness pattern. Under an ARBITRARY const-typing env \
                          tenv. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtx".to_string(),
                "typingctx_powr2_ty".to_string(),
                "U0".to_string(),
                "U0_level".to_string(),
                "ctx_lookup".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group F: the block ---
        self.add_recursive_def(
            SRC_TYPINGCTX_PI_SMALL_INV,
            "Structural rule inversion for the conv-free TypingCtx, generalized for the \
             recursor: any derivation whose subject is a pi and whose type is the literal \
             sort Level.zero is refutable. Motive: forall PA PB, e = pi PA PB -> \
             T = sort zero -> Empty, dispatched over the seven TypingCtx minors in \
             declaration order (var sort pi lam app const let_). Six arms have a non-pi \
             subject (bvar/sort/lam/app/const/let_) and die on the subject equation via \
             hk_kill_nonpi with a computing ConstFreeUnit.triv; the pi arm — the only rule \
             that can conclude a pi — has conclusion sort (imax n m), a LITERAL imax, and \
             dies by sort_universe_consistency + level_imax_ne_zero. Because TypingCtx is \
             conv-free there is no conversion rescue to refute (the TypingCtxConv variant \
             is NOT covered here; see the module docs). Plain def, zero axiom_deps.",
        )?;
        self.add_definition(SpecDefinition {
            name: "typingctx_pi_not_small".to_string(),
            type_src: TY_TYPINGCTX_PI_NOT_SMALL.to_string(),
            value_src: Some(VAL_TYPINGCTX_PI_NOT_SMALL.to_string()),
            is_axiom: false,
            description: "NO pi is small in the conv-free TypingCtx: for every context, \
                          const-env and A B, TypingCtx tenv G (pi A B) (sort Level.zero) is \
                          refutable — typingctx_pi_small_inv at two Eq.refl equations. This \
                          is STRONGER than the corpus block (which needs the P-spine shape) \
                          because this judgment's pi conclusions carry literal imax levels; \
                          see the module docs honesty note. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "typingctx_pi_small_inv".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_powr2_not_small".to_string(),
            type_src: TY_TYPINGCTX_POWR2_NOT_SMALL.to_string(),
            value_src: Some(VAL_TYPINGCTX_POWR2_NOT_SMALL.to_string()),
            is_axiom: false,
            description: "Corpus powr2_not_small (Blocking.lean:117-124) specialized to \
                          sort zero, for the conv-free TypingCtx: PPX can never be small, in \
                          any context, under any const-env. Instance of typingctx_pi_not_small \
                          (powr2 X unfolds to a pi). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "typingctx_pi_not_small".to_string(),
                "powr2".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_U0_not_small".to_string(),
            type_src: TY_TYPINGCTX_U0_NOT_SMALL.to_string(),
            value_src: Some(VAL_TYPINGCTX_U0_NOT_SMALL.to_string()),
            is_axiom: false,
            description: "HALF TWO of the block, corpus U0_not_small (Blocking.lean:154-165) \
                          for the conv-free TypingCtx: Hurkens' powerful universe can NEVER \
                          be small — TypingCtx tenv G U0 (sort Level.zero) -> Empty for \
                          EVERY context G and const-env tenv. With typingctx_U0_formable \
                          this is the two-halves shape of the corpus: U0 exists one \
                          (semantic) level up and never at level 0, so the Type:Type \
                          ingredient Hurkens' paradox feeds on is unavailable in the \
                          stratified reflected judgment. Conv-free judgment; the \
                          TypingCtxConv variant is NOT covered (module docs). \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "typingctx_pi_not_small".to_string(),
                "U0".to_string(),
                "U0_body".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_powr2_never_small".to_string(),
            type_src: TY_TYPINGCTX_POWR2_NEVER_SMALL.to_string(),
            value_src: Some(VAL_TYPINGCTX_POWR2_NEVER_SMALL.to_string()),
            is_axiom: false,
            description: "Corpus-shaped restatement of typingctx_powr2_not_small (k != 0 for \
                          ANY sort k that PPX inhabits, k pinned by Eq Level k Level.zero): \
                          transport the derivation along the level equation, then the block. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "typingctx_powr2_not_small".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_U0_never_small".to_string(),
            type_src: TY_TYPINGCTX_U0_NEVER_SMALL.to_string(),
            value_src: Some(VAL_TYPINGCTX_U0_NEVER_SMALL.to_string()),
            is_axiom: false,
            description: "Corpus-shaped restatement of typingctx_U0_not_small (k != 0 for ANY \
                          sort k that U0 inhabits): transport along the level equation, then \
                          the block. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "typingctx_U0_not_small".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // --- Group G: ground non-vacuity witnesses ---
        self.add_definition(SpecDefinition {
            name: "typingctx_powr_witness".to_string(),
            type_src: TY_TYPINGCTX_POWR_WITNESS.to_string(),
            value_src: Some(VAL_TYPINGCTX_POWR_WITNESS.to_string()),
            is_axiom: false,
            description: "Ground non-vacuity witness for the positive half: powr (bvar 0) : \
                          sort powr_level in context [sort 0] under the empty const-env — \
                          typingctx_powr_ty fed by the var rule with a computing Eq.refl \
                          ctx_lookup premise (the typingctx_var_witness pattern). \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "typingctx_powr_ty".to_string(),
                "ctx_lookup".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_definition(SpecDefinition {
            name: "typingctx_U0_witness".to_string(),
            type_src: TY_TYPINGCTX_U0_WITNESS.to_string(),
            value_src: Some(VAL_TYPINGCTX_U0_WITNESS.to_string()),
            is_axiom: false,
            description: "Ground non-vacuity witness for the block's positive half: U0 : \
                          sort U0_level in the empty context under the empty const-env — \
                          typingctx_U0_formable instantiated. Together with \
                          typingctx_U0_not_small this is the corpus's two-halves pair in \
                          ground form. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["typingctx_U0_formable".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
