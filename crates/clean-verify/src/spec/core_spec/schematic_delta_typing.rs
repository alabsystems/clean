// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derive instantiated delta-body typing from one schematic body derivation.
//!
//! This stage runs inside the subject-reduction bundle, after its coherence
//! interface and closed-term weakening theorem. Delta universe closure follows
//! from stored body support; iota universe closure remains explicit. Typing an
//! instantiated output is never a field.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn delta_typing_theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    pub(super) fn add_srb_schematic_delta_typing(&mut self) -> Result<(), SpecError> {
        delta_typing_theorem(
            self,
            "tec_delta_universe_closed",
            r"forall (tenv : KDeclEnv), TypingEnvCoherent tenv ->
forall (s : Name -> Level) (e : KExpr) (e' : KExpr),
delta_reduces e e' -> delta_reduces (instL s e) (instL s e')",
            r"fun (tenv : KDeclEnv) (W : TypingEnvCoherent tenv) =>
delta_reduces_instL_supported (tec_def_body_supported tenv W)",
            "Derive actual fixed-environment delta universe closure from support of stored schematic bodies, guarded lookup inversion, preserved arity and proved substitution fusion. This is not a coherence field or per-instantiated-output assumption.",
        )?;
        delta_typing_theorem(
            self,
            "tec_defn_inst_typed",
            r"forall (tenv : KDeclEnv), RedEnvFaithful the_red_env -> TypingEnvCoherent tenv ->
forall (n : Name) (defn : KDefSig),
@Eq (OptionType KDefSig) (kdef_for (red_def the_red_env) n) (@OptionType.some KDefSig defn) ->
forall (us : ListType Level) (G : ListType KExpr),
TypingCtxConv tenv G (kdef_inst_value defn us) (kconst_inst_type (kdef_signature defn) us)",
            r"fun (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env) (W : TypingEnvCoherent tenv)
(n : Name) (defn : KDefSig)
(get : @Eq (OptionType KDefSig) (kdef_for (red_def the_red_env) n) (@OptionType.some KDefSig defn))
(us : ListType Level) (G : ListType KExpr) =>
typingctxconv_closed_weaken_empty tenv hf W
  (kdef_inst_value defn us) (kconst_inst_type (kdef_signature defn) us)
  (instL_preserves_top_level_closed (paramSubstN (kconst_params (kdef_signature defn)) us)
    (kdef_value defn) (tec_def_body_closed tenv W n defn get))
  (instL_preserves_top_level_closed (paramSubstN (kconst_params (kdef_signature defn)) us)
    (kconst_type (kdef_signature defn))
    (tec_tenv_closed tenv W n (kdef_signature defn) (tec_def_signature tenv W n defn get)))
  (typingctxconv_instLevels tenv (tec_tenv_supported tenv W)
    (kconst_params (kdef_signature defn)) us
    (tec_delta_universe_closed tenv W (paramSubstN (kconst_params (kdef_signature defn)) us))
    (tec_iota_universe_closed tenv W (paramSubstN (kconst_params (kdef_signature defn)) us))
    (@ListType.nil KExpr) (kdef_value defn) (kconst_type (kdef_signature defn))
    (tec_def_body_typed tenv W n defn get)) G",
            "One schematic empty-context body-typing derivation is instantiated by the proved TypingCtxConv universe-substitution theorem, then weakened using derived closedness. Shared signature parameters instantiate both body and type. Delta universe closure is derived from stored body support; iota closure remains explicit. No per-instance typing is assumed.",
        )?;

        delta_typing_theorem(
            self,
            "tec_defval_typed",
            r"forall (tenv : KDeclEnv), RedEnvFaithful the_red_env -> TypingEnvCoherent tenv ->
forall (n : Name) (us : ListType Level) (v : KExpr) (A : KExpr),
@Eq (OptionType KExpr) (kdef_value_at (red_def the_red_env) n us) (@OptionType.some KExpr v) ->
@Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) ->
forall (G : ListType KExpr), TypingCtxConv tenv G v A",
            r"fun (tenv : KDeclEnv) (hf : RedEnvFaithful the_red_env) (W : TypingEnvCoherent tenv)
(n : Name) (us : ListType Level) (v : KExpr) (A : KExpr)
(value_get : @Eq (OptionType KExpr) (kdef_value_at (red_def the_red_env) n us) (@OptionType.some KExpr v))
(type_get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A))
(G : ListType KExpr) =>
kdef_value_at_some_inv (red_def the_red_env) n us v value_get (TypingCtxConv tenv G v A)
  (fun (defn : KDefSig)
    (get : @Eq (OptionType KDefSig) (kdef_for (red_def the_red_env) n) (@OptionType.some KDefSig defn))
    (arity : kconst_arity (kdef_signature defn) us)
    (value_eq : @Eq KExpr v (kdef_inst_value defn us)) =>
    @Eq.substType KExpr (fun (value : KExpr) => TypingCtxConv tenv G value A)
      (kdef_inst_value defn us) v (@Eq.symm KExpr v (kdef_inst_value defn us) value_eq)
      (@Eq.substType KExpr (fun (ty : KExpr) => TypingCtxConv tenv G (kdef_inst_value defn us) ty)
        (kconst_inst_type (kdef_signature defn) us) A
        (option_some_inj KExpr (kconst_inst_type (kdef_signature defn) us) A
          (@Eq.trans (OptionType KExpr)
            (@OptionType.some KExpr (kconst_inst_type (kdef_signature defn) us))
            (kdecl_type_at tenv n us) (@OptionType.some KExpr A)
            (@Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us)
              (@OptionType.some KExpr (kconst_inst_type (kdef_signature defn) us))
              (kdecl_type_at_intro tenv n (kdef_signature defn) us
                (tec_def_signature tenv W n defn get) arity)) type_get))
        (tec_defn_inst_typed tenv hf W n defn get us G)))",
            "Invert actual guarded value lookup, recover the shared signature and exact arity, and identify the queried type through computed type lookup. Typing follows from tec_defn_inst_typed; this replaces the former assumed defval_typed field.",
        )
    }
}
