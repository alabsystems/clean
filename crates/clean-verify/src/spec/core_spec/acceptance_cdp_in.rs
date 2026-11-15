// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Crystal E4: `KernelAcceptsIn`, the env-indexed algorithmic successor of
//! `KernelInfersIn`, and its declarative target `TypingProjIn`.
//!
//! The deployed release `infer_type` exposes a Pi / Sort by a FULL `whnf_impl`,
//! which whnf-reduces a recursor's major premise (with delta) before rule lookup
//! and reduces a projection of a constructor application. `KernelInfersIn`'s
//! whnf premise is `whnf_red_step_star`, whose iota fires only on an already
//! constructor-headed major and which has projection congruence but no
//! projection beta. Here every whnf premise is `par_reduces_cdp_star` (the
//! projection-extended parallel reduction: the major pre-pass is a sequence of
//! steps on the major followed by head iota, and `projection_beta` is the
//! projection-of-constructor step) and every conversion premise is
//! `DefEqCDPIn`. `KernelInfersIn` embeds (`kernel_infers_in_to_accepts_in`).
//!
//! `KernelAcceptsIn.proj` is the `Proj` inference arm (`infer_proj_type`): the
//! subject's type is whnf'd to a one-constructor structure application and the
//! constructor telescope is walked, parameters then fields, a preceding field's
//! body taking `Proj(S, j, e)`. No env-indexed typing judgment had a projection
//! rule, so soundness targets `TypingProjIn`: `TypingCDPCtxConvIn` (into which
//! `TypingCtxConvIn` embeds) plus Lean 4's primitive-projection rule over the
//! same walks (`typing_cdp_to_proj_in`). Its conversion is `DefEqCDPIn`, which
//! `TypingCtxConvIn` could not carry: `DefEqIn` has no projection beta.
//!
//! `KernelAcceptsTcIn` / `TypingTcIn` (`typed_relations`) are the
//! TYPED-CONVERSION successors: one `Bool`-indexed family per side (typing and
//! conversion are one judgment, since the spec elaborator has no mutual
//! inductives), over contexts of entries that carry a let-local's value. They
//! carry proof irrelevance, lambda eta, unit-like and structure eta, let-local
//! zeta and the Nat literal / constructor correspondence; `KernelAcceptsIn`
//! and `TypingProjIn` embed into them over the declarations-only context
//! (`kernel_accepts_in_to_tc_in`, `typing_proj_in_to_tc_in`), and
//! `kernel_accepts_tc_in_sound` is the soundness theorem.
//!
//! Scope, stated. The relation models CHECK mode (`infer_only = false`). The
//! deployed Prop-structure projection validation is NOT a premise: both
//! relations accept projections of Prop structures without it, so the target is
//! weaker than Lean's there, and the metatheory of the new rule (subject
//! reduction for projection beta, consistency) is open. The walks omit the
//! source's premature parameter stop, and constructor metadata is read from
//! `R`'s table while constant types come from `tenv`; relating both to the
//! deployed environment is a representation obligation. Not extracted Rust
//! execution. Every witness runs in a supplied, non-seed environment and needs
//! the premise shape it witnesses.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

mod inference;
mod k_witnesses;
mod name_blind;
mod native_nat;
pub use native_nat::NATIVE_NAT_PROOF_NAMES;
mod prepass;
mod projection;
mod quot_witnesses;
mod string_literal;
pub use string_literal::{ACCEPTS_TC_STRING_NAME_ALIASES, STRING_LITERAL_PROOF_NAMES};
mod typed_relations;
mod typed_soundness;
mod typed_witnesses;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str),
}

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    inference::DECLARATIONS
        .iter()
        .chain(prepass::DECLARATIONS)
        .chain(projection::DECLARATIONS)
        .chain(name_blind::DECLARATIONS)
        .chain(typed_relations::DECLARATIONS)
        .chain(typed_soundness::DECLARATIONS)
        .chain(typed_witnesses::DECLARATIONS)
        .chain(k_witnesses::DECLARATIONS)
}

/// Every PROOF this stage registers (inductives and data fixtures excluded), in
/// registration order: the name list the census test reads. It is a `const`, as
/// the sibling stages' `*_NAMES` lists are, and it cannot drift from the one
/// declaration table: `proof_names_match_the_declaration_table` below derives it
/// from the table and compares.
pub const ACCEPTS_IN_PROOF_NAMES: &[&str] = &[
    "typing_cdp_to_proj_in",
    "kernel_accepts_in_sound",
    "whnf_red_step_star_to_par_cdp_star",
    "kernel_infers_in_to_accepts_in",
    "accepts_prepass_computes",
    "accepts_prepass_starved",
    "accepts_prepass_head_iota_declines",
    "accepts_prepass_head_delta_declines",
    "accepts_prepass_trace",
    "kernel_accepts_in_prepass_pi",
    "accepts_prepass_pi_sound",
    "accepts_prepass_seed_has_no_anonymous_recursor",
    "accepts_prepass_env_not_seed",
    "accepts_proj_computes",
    "accepts_proj_wh3_stuck",
    "accepts_proj_trace",
    "kernel_accepts_in_proj_pi",
    "accepts_proj_pi_sound",
    "accepts_proj_seed_has_no_anonymous_inductive",
    "accepts_proj_env_not_seed",
    "accepts_proj_var_struct",
    "kernel_accepts_in_proj_field_zero",
    "accepts_proj_field_zero_sound",
    "accepts_proj_control_field_bound",
    "accepts_dep_struct",
    "accepts_params_cons_witness",
    "accepts_dep_field_one_walk",
    "kernel_accepts_in_proj_dependent_field",
    "accepts_proj_dependent_field_sound",
    "def_eq_cdp_in_proj_field_name_blind",
    "accepts_proj_names_differ",
    "accepts_proj_other_computes",
    "def_eq_cdp_in_proj_name_blind_witness",
    "lctx_decls_lookup",
    "kernel_accepts_tc_in_sound",
    "kernel_accepts_in_to_tc_in",
    "typing_proj_in_to_tc_in",
    "kernel_accepts_in_tc_sound",
    "kernel_accepts_tc_in_proof_irrel",
    "accepts_tc_proof_irrel_sound",
    "kernel_accepts_tc_in_eta",
    "accepts_tc_eta_sound",
    "accepts_unit_like",
    "kernel_accepts_tc_in_unit_like",
    "accepts_unit_like_sound",
    "accepts_unit_env_not_seed",
    "accepts_struct_ctor",
    "accepts_struct_fields",
    "kernel_accepts_tc_in_struct_eta",
    "accepts_struct_eta_sound",
    "accepts_tc_let_zeta_arg",
    "kernel_accepts_tc_in_let_body",
    "kernel_accepts_tc_in_let_zeta",
    "accepts_tc_let_zeta_sound",
    "accepts_tc_offset_peel",
    "accepts_tc_iota_major_literal",
    "kernel_accepts_tc_in_lit_two",
    "accepts_tc_lit_two_sound",
    "accepts_k_admit",
    "kernel_accepts_tc_in_k_like",
    "accepts_tc_k_like_sound",
    "typing_tc_in_k_like_is_proof_irrel",
    "kernel_accepts_tc_in_quot_lift",
    "accepts_tc_quot_lift_sound",
    "kernel_accepts_tc_in_quot_ind",
    "accepts_tc_quot_ind_sound",
    "kernel_accepts_tc_in_quot_lift_extra_arg",
    "accepts_tc_quot_lift_extra_arg_sound",
    "accepts_k_iota_witness",
    "accepts_k_eq_rec_admitted",
];

/// The reflected builtin names the Nat literal rules key on, as registered by
/// this stage: `(alias, real kernel name)`. Each alias is `kcre_name_<tag>` for
/// the tag the validated interning table assigns the real name, looked up at
/// registration -- never a typed-in tag, so a regenerated table cannot move the
/// rule onto another constant.
pub const ACCEPTS_TC_NAT_NAME_ALIASES: &[(&str, &str)] = &[
    ("accepts_tc_nat_zero_name", "Nat.zero"),
    ("accepts_tc_nat_succ_name", "Nat.succ"),
];

/// The reflected quotient names the `quot_lift` / `quot_ind` rules key on,
/// read from the validated interning table at registration exactly as the Nat
/// literal aliases are. The names are reserved native rule keys of the
/// generator (`red_env_reflect::RESERVED_NATIVE_RULE_KEYS`): no reflected
/// RecEnv/DefEnv entry mentions them.
pub const ACCEPTS_TC_QUOT_NAME_ALIASES: &[(&str, &str)] = &[
    ("accepts_tc_quot_mk_name", "Quot.mk"),
    ("accepts_tc_quot_lift_name", "Quot.lift"),
    ("accepts_tc_quot_ind_name", "Quot.ind"),
];

impl Specification {
    /// Full bundle only, after `add_projection_typing` (TypingCDPCtxConvIn,
    /// DefEqCDPIn, par_reduces_cdp_star), the projection telescope/metadata
    /// stages and the WH3 soundness stage.
    pub(super) fn add_acceptance_cdp_in(&mut self) -> Result<(), SpecError> {
        for (alias, real) in ACCEPTS_TC_NAT_NAME_ALIASES {
            let tag = self.reflected_name_tag(real)?;
            self.add_recursive_def(
                &format!("def {alias} : Name := kcre_name_{tag}"),
                "The reflected builtin name a Nat literal rule of KernelAcceptsTcIn / TypingTcIn keys on, read from the validated interning table at registration.",
            )?;
        }
        for (alias, real) in ACCEPTS_TC_QUOT_NAME_ALIASES {
            let tag = self.reflected_name_tag(real)?;
            self.add_recursive_def(
                &format!("def {alias} : Name := kcre_name_{tag}"),
                "The reflected quotient name a quot_lift / quot_ind rule of KernelAcceptsTcIn / TypingTcIn keys on, read from the validated interning table at registration (a reserved native rule key).",
            )?;
        }
        self.add_accepts_tc_string_prelude()?;
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Crystal E4 relation with checked eliminator: the projection walks, the declarative TypingProjIn, or the check-mode algorithmic KernelAcceptsIn over finite projection-extended reduction traces. Not extracted Rust execution; not an axiom.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked KernelAcceptsIn soundness, embedding, name-blind projection conversion, or non-seed witness/control computation; no assumed reduction, typing, admission or source-execution claim.",
                )?,
                DeclarationInput::Data(source) => self.add_recursive_def(
                    source,
                    "Transparent finite witness data (environment, metadata, term or context); not an admission or typing claim.",
                )?,
            }
        }
        for proof in quot_witnesses::proofs() {
            theorem(
                self,
                proof.name,
                &proof.ty,
                &proof.value,
                "Checked quotient-rule witness or its soundness corollary: a Quot.lift / Quot.ind redex (major reached by a beta conversion, or under a trailing argument) related to its function argument applied to the quoted value; no assumed reduction, typing or source-execution claim.",
            )?;
        }
        self.add_accepts_tc_native_nat()?;
        self.add_accepts_tc_string_witnesses()?;
        let (ty, value) = k_witnesses::iota_witness();
        theorem(
            self,
            "accepts_k_iota_witness",
            &ty,
            &value,
            "Checked K-like witness: a K-flagged recursor applied to a HYPOTHESIS reaches its constructor by KernelAcceptsTcIn.k_like and then reduces by iota; no assumed reduction, typing or source-execution claim.",
        )?;
        let [(rule_name, rule_ty, rule_value), (name, ty, value)] = k_witnesses::seed_witness(
            self.reflected_name_tag("Eq")?,
            self.reflected_name_tag("Eq.refl")?,
            self.reflected_name_tag("Eq.rec")?,
        );
        self.add_recursive_def(
            &format!("def {rule_name} : {rule_ty} := {rule_value}"),
            "The reflected seed's Eq.rec rule for Eq.refl, read off kernel_core_red_env by the model's own lookup (data, not an admission claim).",
        )?;
        theorem(
            self,
            &name,
            &ty,
            &value,
            "Checked: the reflected seed's K-flagged recursor Eq.rec satisfies the K admission predicate RecKAdmitIn, every fact a computation over kernel_core_red_env.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kernel_accepts_in_records_parse() {
        let mut names = std::collections::HashSet::new();
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => {
                    crate::test_utils::parse_check(source).expect("E4 relation parses");
                }
                DeclarationInput::Proof(name, ty, body) => {
                    assert!(names.insert(*name), "{name} registered twice");
                    clean_parser::parse_decl(&format!("def {name} : {ty} := {body}"))
                        .expect("E4 proof record parses");
                }
                DeclarationInput::Data(source) => {
                    clean_parser::parse_decl(source).expect("E4 data record parses");
                }
            }
        }
        for proof in quot_witnesses::proofs() {
            assert!(names.insert(proof.name), "{} registered twice", proof.name);
            clean_parser::parse_decl(&format!(
                "def {} : {} := {}",
                proof.name, proof.ty, proof.value
            ))
            .expect("E4 quotient witness parses");
        }
    }

    /// The same list, derived from the declaration table.
    fn accepts_in_proof_names() -> Vec<&'static str> {
        declarations()
            .filter_map(|declaration| match declaration {
                DeclarationInput::Proof(name, _, _) => Some(*name),
                DeclarationInput::Inductive(_) | DeclarationInput::Data(_) => None,
            })
            .chain(quot_witnesses::proofs().into_iter().map(|proof| proof.name))
            .chain(["accepts_k_iota_witness", "accepts_k_eq_rec_admitted"])
            .collect()
    }

    #[test]
    fn proof_names_match_the_declaration_table() {
        assert_eq!(accepts_in_proof_names(), ACCEPTS_IN_PROOF_NAMES);
    }
}
