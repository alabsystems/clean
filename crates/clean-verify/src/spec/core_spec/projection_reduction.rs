// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Computed projection extraction and its staged parallel-reduction extension.
//!
//! The raw selector uses stored constructor parameters and actual arguments.
//! Its substitution/lift and semantic-universe lemmas feed a relation containing
//! projection beta, with old-reduction embedding and new-relation constructor
//! transport. Two local extraction overlaps have actual common-reduct proofs.
//!
//! These 62 checked proof records, eight transparent data definitions and three
//! Type-valued carriers do not migrate acceptance, establish global confluence,
//! prove dependent field typing, or connect executing Rust. Raw reduction keeps
//! its weaker guards; fixture computations are not source-admission theorems.
//!
//! Exact tuple provenance: projection-extension-registration.hm0ldx.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod bindings;
mod joins;
mod relation;
mod selector;
mod universes;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    selector::DECLARATIONS
        .iter()
        .chain(bindings::DECLARATIONS)
        .chain(universes::DECLARATIONS)
        .chain(relation::DECLARATIONS)
        .chain(joins::DECLARATIONS)
}

const PROOF_ROOTS: &[&str] = &[
    "projection_post_whnf_proj",
    "projection_post_whnf_field_intro",
    "projection_post_whnf_field_inv_type",
    "projection_post_whnf_transport",
    "projection_post_whnf_prod_before_zero",
    "projection_post_whnf_prod_after_zero",
    "projection_post_whnf_prod_before_one",
    "projection_post_whnf_prod_after_one",
    "projection_post_whnf_prod_transport_zero",
    "projection_post_whnf_prod_transport_one",
    "projection_post_whnf_missing_metadata",
    "projection_post_whnf_missing_argument",
    "projection_post_whnf_outer_app_refused",
    "projection_post_whnf_outer_sort_refused",
    "projection_post_whnf_nonconstant_head_refused",
    "projection_post_whnf_struct_name_ignored",
    "projection_post_whnf_prod_universe_arity_ignored",
    "projection_post_whnf_declared_field_count_ignored",
    "projection_post_whnf_field_inv",
    "projection_selected_map_head",
    "projection_post_whnf_field_instantiate_at",
    "projection_post_whnf_instantiate_at",
    "projection_post_whnf_field_lift_at",
    "projection_post_whnf_lift_at",
    "projection_binding_select",
    "projection_binding_substitution_computes",
    "projection_binding_lifting_computes",
    "projection_binding_substitution_caller",
    "projection_binding_lifting_caller",
    "projection_post_whnf_universe_compat",
    "projection_universe_subject_related",
    "projection_universe_source_select",
    "projection_universe_target_select",
    "projection_universe_selected_compat",
    "projection_universe_nonzero_caller",
    "projection_universe_not_syntactic",
    "par_reduces_cd_to_cdp",
    "par_reduces_cdp_list_refl",
    "par_reduces_cdp_list_append",
    "par_reduces_cdp_list_tail",
    "par_reduces_cdp_list_drop",
    "par_reduces_cdp_list_head_some",
    "par_reduces_cdp_list_length",
    "ctor_metadata_spine_preserved_cdp",
    "ctor_metadata_head_preserved_cdp",
    "ctor_metadata_selected_position_cdp",
    "ctor_metadata_selected_field_cdp",
    "ctor_metadata_spine_length_cdp",
    "projection_post_whnf_transport_cdp",
    "cdp_prod_inner_extract",
    "cdp_prod_inner_step",
    "cdp_prod_outer_step",
    "cdp_prod_head_preserved",
    "cdp_prod_length_preserved",
    "cdp_prod_selected_zero",
    "cdp_prod_old_beta_embedded",
    "cdp_prod_outer_extract",
    "cdp_prod_selector_transport",
    "projection_post_whnf_deterministic",
    "par_cdp_projection_beta_beta",
    "par_cdp_projection_beta_cong",
    "par_cdp_prod_beta_projection_join",
];

const DATA_NAMES: &[&str] = &[
    "projection_post_whnf_field",
    "projection_post_whnf_reduct",
    "projection_post_whnf_zero_fields_env",
    "projection_binding_field",
    "projection_binding_subject",
    "projection_universe_subject",
    "cdp_prod_inner_projection",
    "cdp_prod_outer_before",
];

const INDUCTIVE_NAMES: &[&str] = &[
    "par_reduces_cdp",
    "par_reduces_cdp_list",
    "ParCDPCtorSpineView",
];

impl Specification {
    /// Full bundle only, after actual reflected constructor rigidity.
    pub(super) fn add_projection_reduction(&mut self) -> Result<(), SpecError> {
        debug_assert_eq!(
            declarations().count(),
            PROOF_ROOTS.len() + DATA_NAMES.len() + INDUCTIVE_NAMES.len()
        );
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Projection-extended raw parallel reduction or its pointwise constructor evidence. Global confluence and acceptance migration remain separate.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked computed projection selection, algebraic compatibility, new-relation transport or local critical overlap; not dependent typing or executing Rust refinement.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent raw projection selector or computational caller data; no source-admission claim.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_projection_post_whnf_selected_endpoint",
        r"par_reduces_cd the_red_env ctor_spine_prod_redex (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_post_whnf_prod_transport_zero",
    ),
    (
        "forged_projection_post_whnf_missing_argument",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (KExpr.proj kcre_prod_type_name (Nat.succ (Nat.succ Nat.zero)) kcre_witness_prod_value)) (@OptionType.some KExpr rfnz_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero)",
    ),
    (
        "forged_projection_post_whnf_outer_shape",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env kcre_witness_prod_value) (@OptionType.some KExpr rfnz_zero)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero)",
    ),
    (
        "forged_projection_binding_capture",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (instantiate_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject)
   (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero))
 (@OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)))",
        r"projection_binding_substitution_caller",
    ),
    (
        "forged_projection_binding_unshifted",
        r"@Eq (OptionType KExpr)
 (projection_post_whnf_reduct the_red_env
  (lift_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) Nat.zero (Nat.succ (Nat.succ Nat.zero))))
 (@OptionType.some KExpr projection_binding_field)",
        r"projection_binding_lifting_caller",
    ),
    (
        "forged_projection_universe_wrong_head",
        r"KExprUniverseEq projection_prod_ctor (KExpr.const kcre_prod_type_name (@ListType.nil Level))",
        r"kexprUniverseEq_refl projection_prod_ctor",
    ),
    (
        "forged_projection_universe_wrong_slot",
        r"KExprUniverseEq (KExpr.sort (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero)) rfnz_zero",
        r"projection_universe_nonzero_caller",
    ),
    (
        "forged_cdp_selected_endpoint",
        r"par_reduces_cdp the_red_env cdp_prod_inner_projection (KExpr.app rfnz_succ rfnz_zero)",
        r"cdp_prod_selected_zero",
    ),
    (
        "forged_projection_deterministic_field",
        r"@Eq KExpr rfnz_zero (KExpr.app rfnz_succ rfnz_zero)",
        r"projection_post_whnf_deterministic the_red_env
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) rfnz_zero rfnz_zero
  projection_post_whnf_prod_after_zero projection_post_whnf_prod_after_zero",
    ),
    (
        "forged_projection_join_left_endpoint",
        r"forall (C : Type)
 (next : forall (b : KExpr), par_reduces_cdp the_red_env rfnz_zero b ->
  par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) b -> C), C",
        r"fun (C : Type)
 (next : forall (b : KExpr), par_reduces_cdp the_red_env rfnz_zero b ->
  par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) b -> C) => par_cdp_prod_beta_projection_join C next",
    ),
];

#[cfg(test)]
#[path = "projection_reduction/tests.rs"]
mod tests;
