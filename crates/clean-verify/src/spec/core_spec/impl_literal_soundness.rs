// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Literal cases of the existing implementation-model soundness theorem.
//!
//! These terms remove the former impossible literal guard. They concern
//! `ImplInfer`; the separate compiler-extracted Rust attachment must still
//! establish that actual execution produces such derivations.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_impl_literal_soundness(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "impl_sound_lit".to_string(),
            type_src: concat!(
                "forall (tenvK : KDeclEnv) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (l : ImplLit), ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.lit l) rho) ",
                "(to_kexpr (impl_lit_type l) rho)"
            ).to_string(),
            value_src: Some(concat!(
                "fun (tenvK : KDeclEnv) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (l : ImplLit) => ",
                "@ImplLit.rec (fun (v : ImplLit) => ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.lit v) rho) ",
                "(to_kexpr (impl_lit_type v) rho)) ",
                "(fun (n : Nat) => @TypingCtxConv.lit_nat tenvK Gk n) ",
                "(fun (n : Nat) => @TypingCtxConv.lit_string tenvK Gk n) l"
            ).to_string()),
            is_axiom: false,
            description: "Both implementation-model literal kinds translate to their exact declarative literal type. There is no impossible premise. Builtin names use the validated shared reflection table; this does not establish the production environment invariant or actual Rust execution correspondence.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplLit.rec".to_string(),
                "TypingCtxConv.lit_nat".to_string(),
                "TypingCtxConv.lit_string".to_string(),
                "to_kexpr".to_string(),
                "impl_lit_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })
    }

    pub(super) fn add_impl_literal_soundness_witnesses(&mut self) -> Result<(), SpecError> {
        let tenv = "(fun (_ : Name) => @OptionType.none ImplConstInfo)";
        let tenvk = "(fun (_ : Name) => @OptionType.none KConstSig)";
        for (name, kind, literal, literal_type) in [
            (
                "impl_infer_sound_nat_literal",
                "natVal",
                "literal_nat",
                "literal_nat_type",
            ),
            (
                "impl_infer_sound_string_literal",
                "strVal",
                "literal_string",
                "literal_string_type",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (n : Nat), TypingCtxConv {tenvk} (@ListType.nil KExpr) ({literal} n) {literal_type}"
                ),
                value_src: Some(format!(
                    "fun (n : Nat) => impl_infer_sound {tenv} {tenvk} \
                     (@ListType.nil Name) tenvrepc_empty Nat.zero LCtx.nil \
                     (ImplExpr.lit (ImplLit.{kind} n)) \
                     (impl_lit_type (ImplLit.{kind} n)) Nat.zero \
                     (@ImplInfer.lit {tenv} (@ListType.nil Name) Nat.zero LCtx.nil (ImplLit.{kind} n)) \
                     ImplUnit.mk (@ListType.nil Nat) (@ListType.nil KExpr) ctx_rep_nil_witness"
                )),
                is_axiom: false,
                description: format!(
                    "Run the assembled impl_infer_sound theorem for every {kind} payload, deriving the literal guard by ImplUnit.mk. Empty environments witness the model-to-model theorem's premises; this is not a claim that a production prelude or Rust execution has been verified."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "impl_infer_sound".to_string(),
                    "tenvrepc_empty".to_string(),
                    "ImplInfer.lit".to_string(),
                    "ImplUnit.mk".to_string(),
                    "ctx_rep_nil_witness".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }
}
