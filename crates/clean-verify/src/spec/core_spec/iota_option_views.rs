// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Unchanged Type-valued Option views, promoted before guarded iota consumers.
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use std::collections::HashSet;
impl Specification {
    pub(super) fn add_iota_option_type_views(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "option_none_ne_some_type".to_string(),
            type_src: concat!(
                "forall (b : Type) (r : b) (C : Type), ",
                "Eq (OptionType b) (OptionType.none b) (OptionType.some b r) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (b : Type) (r : b) (C : Type) ",
                    "(h : Eq (OptionType b) (OptionType.none b) (OptionType.some b r)) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType (OptionType b) (opt_is_none b) ",
                    "(OptionType.none b) (OptionType.some b r) h Nat.zero)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Type-valued OptionType no-confusion: none /= some, discharging a Type-valued goal C. Empty discriminator (none -> Nat inhabited by zero, some -> Empty) transported along the false equation via opt_is_none + Empty.rec (any sort). The Type-valued sibling of option_none_ne_some, needed where the goal is in Type (par_reduces_c_list). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_is_none".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "opt_bind_some_inv_type".to_string(),
            type_src: concat!(
                "forall (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type), ",
                "Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r) -> ",
                "(forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (r : b) (C : Type) ",
                    "(h : Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r)) ",
                    "(k : forall (w : a), Eq (OptionType a) o (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) => ",
                    "OptionType.rec a ",
                    "(fun (o0 : OptionType a) => ",
                    "Eq (OptionType b) (opt_bind a b o0 f) (OptionType.some b r) -> ",
                    "(forall (w : a), Eq (OptionType a) o0 (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) -> C) ",
                    "(fun (h0 : Eq (OptionType b) (opt_bind a b (OptionType.none a) f) (OptionType.some b r)) ",
                    "(k0 : forall (w : a), Eq (OptionType a) (OptionType.none a) (OptionType.some a w) -> ",
                    "Eq (OptionType b) (f w) (OptionType.some b r) -> C) => ",
                    "option_none_ne_some_type b r C h0) ",
                    "(fun (w : a) ",
                    "(h0 : Eq (OptionType b) (opt_bind a b (OptionType.some a w) f) (OptionType.some b r)) ",
                    "(k0 : forall (w0 : a), Eq (OptionType a) (OptionType.some a w) (OptionType.some a w0) -> ",
                    "Eq (OptionType b) (f w0) (OptionType.some b r) -> C) => ",
                    "k0 w (Eq.refl (OptionType a) (OptionType.some a w)) h0) ",
                    "o h k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Type-valued sibling of opt_bind_some_inv (C : Type): CPS inversion of opt_bind into a Type-valued continuation, via OptionType.rec (large-eliminating) + option_none_ne_some_type for the absurd none case. The leaf of the Type-valued inverter tower the (a)-join (par_strips_witness_c_star, a Type inductive) needs. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "OptionType.rec".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}
