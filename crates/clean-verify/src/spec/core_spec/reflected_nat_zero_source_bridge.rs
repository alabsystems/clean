// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked bridge to the actual emitted four-signature Nat typing environment.
//!
//! These eight proofs are the exact checked terms from
//! scratch/reflected-nat-zero-source-bridge.rs. They use genuine generated
//! kcre_nat_*_signature / kcre_nat_tenv declarations, not a copied handwritten
//! substitute for producer output. rfnz_source_tenv_eq is a checked computational
//! equality, not an additional assumption or a function-extensionality axiom.
//!
//! The bridge transports finite support, stored/instance RHS typing, and the
//! concrete universe-one input/raw-output typings. The actual guarded iota step
//! is reused unchanged: it depends on kernel_core_red_env, not the typing
//! environment. The parent reflected_nat_zero_typing module supplies its real
//! argument typings and the stored-lookup-to-instance-typing derivation.
//!
//! Source data emission/fidelity and checked model typing remain distinct from
//! a formal proof of executing the source validator, general admission,
//! all-input iota preservation, or Rust execution refinement.
//! Proof records only desugar checked binders into explicit forall/fun.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

struct CheckedProof {
    name: &'static str,
    type_src: &'static str,
    value_src: &'static str,
    description: &'static str,
}

const PROOFS: &[CheckedProof] = &[
    CheckedProof {
        name: "rfnz_source_tenv_eq",
        type_src: r"@Eq KDeclEnv rfnz_tenv kcre_nat_tenv",
        value_src: r"@Eq.refl KDeclEnv rfnz_tenv",
        description: "Exact function equality between the explicit four-entry model environment and the genuine emitted Nat signature environment; checked by computation, not assumed.",
    },
    CheckedProof {
        name: "rfnz_source_lookup_agrees",
        type_src: r"forall (n : Name),
 @Eq (OptionType KConstSig) (rfnz_tenv n) (kcre_nat_tenv n)",
        value_src: r"fun (n : Name) =>
 Eq.cong KDeclEnv (OptionType KConstSig) (fun (tenv : KDeclEnv) => tenv n)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq",
        description: "Pointwise audit of actual stored signature agreement, derived from the checked environment equality.",
    },
    CheckedProof {
        name: "rfnz_source_tenv_supported",
        type_src: r"KDeclEnvTypeParamSupported kcre_nat_tenv",
        value_src: r"Eq.subst KDeclEnv (fun (tenv : KDeclEnv) => KDeclEnvTypeParamSupported tenv)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_tenv_supported",
        description: "Transport finite schematic type support to the actual emitted signature environment.",
    },
    CheckedProof {
        name: "rfnz_source_stored_rhs_typed",
        type_src: r"TypingCtx kcre_nat_tenv (@ListType.nil KExpr) kcre_witness_nat_zero_rhs
  (rfnz_rule_type (Level.param rfnz_parameter))",
        value_src: r"Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtx tenv (@ListType.nil KExpr)
   kcre_witness_nat_zero_rhs (rfnz_rule_type (Level.param rfnz_parameter)))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_stored_rhs_typed",
        description: "Transport the directly typed actual stored Nat.zero RHS to the genuine emitted signature environment.",
    },
    CheckedProof {
        name: "rfnz_source_lookup_instance_typed",
        type_src: r"forall (rule : RecRule)
 (found : @Eq (OptionType RecRule)
  (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
  (@OptionType.some RecRule rule)) (u : Level),
 TypingCtx kcre_nat_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance kcre_nat_rec_signature (recrule_rhs rule)
   (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u)",
        value_src: r"fun (rule : RecRule)
 (found : @Eq (OptionType RecRule)
  (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
  (@OptionType.some RecRule rule)) (u : Level) =>
 Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtx tenv (@ListType.nil KExpr)
   (recursor_rhs_instance kcre_nat_rec_signature (recrule_rhs rule)
    (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq
  (rfnz_lookup_instance_typed rule found u)",
        description: "Typing of an actually looked-up once-instantiated zero rule in the emitted environment, preserving the prior stored-typing and universe-substitution proof.",
    },
    CheckedProof {
        name: "rfnz_source_actual_instance_typed",
        type_src: r"forall (u : Level),
 TypingCtx kcre_nat_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs
   (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u)",
        value_src: r"fun (u : Level) =>
 rfnz_source_lookup_instance_typed
  (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  rfnz_actual_zero_rule u",
        description: "The actual stored zero-rule lookup yields RHS instance typing at every raw universe in the emitted typing environment.",
    },
    CheckedProof {
        name: "rfnz_source_input_typed",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
  rfnz_input rfnz_nat",
        value_src: r"Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv
   (@ListType.nil KExpr) rfnz_input rfnz_nat)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_input_typed",
        description: "The genuine universe-one actual-name input is typed in the emitted environment; this is a bounded caller, not general source admission.",
    },
    CheckedProof {
        name: "rfnz_source_raw_result_typed",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
  rfnz_raw_result rfnz_nat",
        value_src: r"Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv
   (@ListType.nil KExpr) rfnz_raw_result rfnz_nat)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_raw_result_typed",
        description: "The actual guarded raw output is typed in the emitted environment, transported from the explicit constructive caller rather than assumed subject reduction.",
    },
];

fn proof_definition(proof: &CheckedProof) -> SpecDefinition {
    SpecDefinition {
        name: proof.name.to_string(),
        type_src: proof.type_src.to_string(),
        value_src: Some(proof.value_src.to_string()),
        is_axiom: false,
        description: proof.description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    }
}

impl Specification {
    /// Requires add_reflected_nat_zero_typing and the actual five generated Nat
    /// signature/environment records. No additional data or axioms are declared.
    pub(super) fn add_reflected_nat_zero_source_bridge(&mut self) -> Result<(), SpecError> {
        for proof in PROOFS {
            self.add_definition(proof_definition(proof))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{proof_definition, CheckedProof, PROOFS};
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name, TypeChecker};

    const PROOF_ROOTS: &[&str] = &[
        "rfnz_source_tenv_eq",
        "rfnz_source_lookup_agrees",
        "rfnz_source_tenv_supported",
        "rfnz_source_stored_rhs_typed",
        "rfnz_source_lookup_instance_typed",
        "rfnz_source_actual_instance_typed",
        "rfnz_source_input_typed",
        "rfnz_source_raw_result_typed",
    ];

    // Exact original checked declarations, used only to verify record fidelity.
    const PROTOTYPES: &[&str] = &[
        r"def rfnz_source_tenv_eq : @Eq KDeclEnv rfnz_tenv kcre_nat_tenv :=
 @Eq.refl KDeclEnv rfnz_tenv",
        r"def rfnz_source_lookup_agrees (n : Name) :
 @Eq (OptionType KConstSig) (rfnz_tenv n) (kcre_nat_tenv n) :=
 Eq.cong KDeclEnv (OptionType KConstSig) (fun (tenv : KDeclEnv) => tenv n)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq",
        r"def rfnz_source_tenv_supported : KDeclEnvTypeParamSupported kcre_nat_tenv :=
 Eq.subst KDeclEnv (fun (tenv : KDeclEnv) => KDeclEnvTypeParamSupported tenv)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_tenv_supported",
        r"def rfnz_source_stored_rhs_typed :
 TypingCtx kcre_nat_tenv (@ListType.nil KExpr) kcre_witness_nat_zero_rhs
  (rfnz_rule_type (Level.param rfnz_parameter)) :=
 Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtx tenv (@ListType.nil KExpr)
   kcre_witness_nat_zero_rhs (rfnz_rule_type (Level.param rfnz_parameter)))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_stored_rhs_typed",
        r"def rfnz_source_lookup_instance_typed (rule : RecRule)
 (found : @Eq (OptionType RecRule)
  (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
  (@OptionType.some RecRule rule)) (u : Level) :
 TypingCtx kcre_nat_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance kcre_nat_rec_signature (recrule_rhs rule)
   (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u) :=
 Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtx tenv (@ListType.nil KExpr)
   (recursor_rhs_instance kcre_nat_rec_signature (recrule_rhs rule)
    (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq
  (rfnz_lookup_instance_typed rule found u)",
        r"def rfnz_source_actual_instance_typed (u : Level) :
 TypingCtx kcre_nat_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs
   (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u) :=
 rfnz_source_lookup_instance_typed
  (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  rfnz_actual_zero_rule u",
        r"def rfnz_source_input_typed :
 TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
  rfnz_input rfnz_nat :=
 Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv
   (@ListType.nil KExpr) rfnz_input rfnz_nat)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_input_typed",
        r"def rfnz_source_raw_result_typed :
 TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
  rfnz_raw_result rfnz_nat :=
 Eq.substType KDeclEnv
  (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv
   (@ListType.nil KExpr) rfnz_raw_result rfnz_nat)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_raw_result_typed",
    ];

    // Exact three independently rejected proof statements/bodies.
    const REFUSALS: &[CheckedProof] = &[
        CheckedProof {
            name: "rfnz_source_empty_environment_forgery",
            type_src: r"@Eq KDeclEnv kcre_nat_tenv (fun (_n : Name) => @OptionType.none KConstSig)",
            value_src: r"@Eq.refl KDeclEnv kcre_nat_tenv",
            description:
                "Deliberately invalid actual generated-data bridge proof; must be rejected.",
        },
        CheckedProof {
            name: "rfnz_source_missing_universe_forgery",
            type_src: r"@Eq (OptionType KExpr)
  (kdecl_type_at kcre_nat_tenv fixture_nat_rec_name (@ListType.nil Level))
  (@OptionType.some KExpr (rfnz_rec_type (Level.succ Level.zero)))",
            value_src: r"@Eq.refl (OptionType KExpr)
  (@OptionType.some KExpr (rfnz_rec_type (Level.succ Level.zero)))",
            description:
                "Deliberately invalid actual generated-data bridge proof; must be rejected.",
        },
        CheckedProof {
            name: "rfnz_source_wrong_result_type_forgery",
            type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
  rfnz_raw_result (KExpr.sort Level.zero)",
            value_src: r"rfnz_source_raw_result_typed",
            description:
                "Deliberately invalid actual generated-data bridge proof; must be rejected.",
        },
    ];

    #[test]
    fn reflected_nat_source_bridge_sources_preserve_checked_proofs() {
        use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl, SurfaceExpr};
        fn fragment(source: &str, span: Span) -> Vec<&str> {
            source[span.start..span.end].split_whitespace().collect()
        }
        assert_eq!(PROOFS.len(), 8);
        assert_eq!(PROTOTYPES.len(), PROOFS.len());
        assert_eq!(PROOF_ROOTS.len(), PROOFS.len());
        for ((proof, source), root) in PROOFS.iter().zip(PROTOTYPES).zip(PROOF_ROOTS) {
            assert_eq!(proof.name, *root);
            parse_check(source).expect("original source bridge proof parses");
            parse_check(&format!(
                "def {} : {} := {}",
                proof.name, proof.type_src, proof.value_src
            ))
            .expect("explicit checked proof record parses");
            let SurfaceDecl::Def {
                name,
                binders,
                ty: Some(result),
                val,
                ..
            } = parse_decl(source).expect("original checked proof AST")
            else {
                panic!("expected checked bridge definition")
            };
            assert_eq!(
                name,
                clean_parser::parse_name(proof.name).expect("explicit source name")
            );
            assert_ne!(proof.value_src.trim(), proof.name, "no self-constant proof");
            let ty = parse_expr(proof.type_src).expect("explicit proof type");
            let value = parse_expr(proof.value_src).expect("explicit proof body");
            if binders.is_empty() {
                assert_eq!(
                    fragment(source, result.span()),
                    fragment(proof.type_src, ty.span()),
                    "{name}: result"
                );
                assert_eq!(
                    fragment(source, val.span()),
                    fragment(proof.value_src, value.span()),
                    "{name}: body"
                );
            } else {
                let SurfaceExpr::Pi(_, type_binders, explicit_result) = ty else {
                    panic!("{name}: expected forall")
                };
                let SurfaceExpr::Lambda(_, value_binders, explicit_body) = value else {
                    panic!("{name}: expected fun")
                };
                assert_eq!(type_binders.len(), binders.len(), "{name}: type binders");
                assert_eq!(value_binders.len(), binders.len(), "{name}: value binders");
                for ((original, type_binder), value_binder) in
                    binders.iter().zip(&type_binders).zip(&value_binders)
                {
                    assert_eq!(
                        fragment(source, original.span),
                        fragment(proof.type_src, type_binder.span),
                        "{name}: forall binder"
                    );
                    assert_eq!(
                        fragment(source, original.span),
                        fragment(proof.value_src, value_binder.span),
                        "{name}: fun binder"
                    );
                }
                assert_eq!(
                    fragment(source, result.span()),
                    fragment(proof.type_src, explicit_result.span()),
                    "{name}: result"
                );
                assert_eq!(
                    fragment(source, val.span()),
                    fragment(proof.value_src, explicit_body.span()),
                    "{name}: body"
                );
            }
        }
        assert_eq!(REFUSALS.len(), 3);
        for refusal in REFUSALS {
            parse_check(&format!(
                "def {} : {} := {}",
                refusal.name, refusal.type_src, refusal.value_src
            ))
            .expect("forgery is well parsed");
        }
    }

    #[test]
    fn reflected_nat_source_bridge_actual_roots_values_types_and_closures_recheck() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for proof in PROOFS {
                let definition = spec
                    .definitions()
                    .get(proof.name)
                    .expect("registered source bridge root");
                let name = Name::from_string(proof.name);
                let constant = spec
                    .env()
                    .get_const(&name)
                    .expect("actual kernel source bridge root");
                let ty = definition
                    .elaborated_type
                    .as_ref()
                    .expect("actual elaborated type");
                let value = definition
                    .elaborated_value
                    .as_ref()
                    .expect("actual elaborated value");
                assert!(!definition.is_axiom, "{}", proof.name);
                assert_ne!(constant.kind, ConstantKind::Axiom, "{}", proof.name);
                assert_eq!(
                    definition.category,
                    AxiomCategory::DerivedLemma,
                    "{}",
                    proof.name
                );
                assert_eq!(
                    definition.proof_status,
                    ProofStatus::DerivedProved,
                    "{}",
                    proof.name
                );
                assert_eq!(
                    definition.type_src, proof.type_src,
                    "{}: exact type source",
                    proof.name
                );
                assert_eq!(
                    definition.value_src.as_deref(),
                    Some(proof.value_src),
                    "{}: exact proof source",
                    proof.name
                );
                assert_eq!(
                    &constant.type_, ty,
                    "{}: kernel/metadata type agreement",
                    proof.name
                );
                assert_eq!(
                    constant.value.as_ref(),
                    Some(value),
                    "{}: kernel/metadata value agreement",
                    proof.name
                );
                assert!(
                    !matches!(value.kind(), ExprKind::Const(found, _) if found == &name),
                    "{}: no self-constant proof",
                    proof.name
                );
                spec.verify_definition(proof.name)
                    .expect("actual proof body rechecks");
                assert!(
                    spec.env()
                        .axiom_deps(&name)
                        .expect("actual domain-closure root exists")
                        .is_empty(),
                    "{}: domain axioms",
                    proof.name
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&name)
                        .expect("actual foundational-closure root exists")
                        .is_empty(),
                    "{}: foundational axioms",
                    proof.name
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, proof.name).is_empty(),
                    "{}",
                    proof.name
                );
            }
            // The proof's source environment comes from actual emitted records,
            // whose roots must exist as definitions, not be absent or axiomatized.
            for root in [
                "kcre_nat_type_signature",
                "kcre_nat_zero_signature",
                "kcre_nat_succ_signature",
                "kcre_nat_rec_signature",
                "kcre_nat_tenv",
            ] {
                let name = Name::from_string(root);
                let definition = spec
                    .definitions()
                    .get(root)
                    .expect("actual generated record");
                let constant = spec
                    .env()
                    .get_const(&name)
                    .expect("actual generated kernel root");
                assert!(!definition.is_axiom, "{root}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{root}");
                assert_eq!(
                    Some(&constant.type_),
                    definition.elaborated_type.as_ref(),
                    "{root}: actual generated type"
                );
                assert_eq!(
                    constant.value.as_ref(),
                    definition.elaborated_value.as_ref(),
                    "{root}: actual generated value"
                );
                assert!(constant.value.is_some(), "{root}: actual generated body");
                spec.verify_definition(root)
                    .expect("actual generated record rechecks");
                assert!(
                    spec.env()
                        .axiom_deps(&name)
                        .expect("generated domain-closure root exists")
                        .is_empty(),
                    "{root}"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&name)
                        .expect("generated foundational-closure root exists")
                        .is_empty(),
                    "{root}"
                );
            }
        });
    }

    #[test]
    fn reflected_nat_source_bridge_real_instance_input_step_and_output_callers_check() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for (value_src, type_src) in [
                (
                    "rfnz_source_actual_instance_typed (Level.succ (Level.param rfnz_parameter))",
                    "TypingCtx kcre_nat_tenv (@ListType.nil KExpr) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level (Level.succ (Level.param rfnz_parameter)) (@ListType.nil Level))) (rfnz_rule_type (Level.succ (Level.param rfnz_parameter)))",
                ),
                (
                    "rfnz_source_input_typed",
                    "TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input rfnz_nat",
                ),
                (
                    "rfnz_guarded_step",
                    "iota_step (red_rec kernel_core_red_env) rfnz_input rfnz_raw_result",
                ),
                (
                    "rfnz_source_raw_result_typed",
                    "TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat",
                ),
            ] {
                let value = spec.elaborate_source(value_src, "actual source-bridge caller").expect("caller elaborates");
                let expected = spec.elaborate_source(type_src, "actual source-bridge caller type").expect("caller type elaborates");
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let inferred = checker.infer_type(&value).expect("caller checks");
                assert!(checker.is_def_eq(&inferred, &expected), "{value_src}");
            }
        });
    }

    #[test]
    fn reflected_nat_source_bridge_rejects_false_environment_arity_and_output_type() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for refusal in REFUSALS {
                parse_check(&format!(
                    "def {} : {} := {}",
                    refusal.name, refusal.type_src, refusal.value_src
                ))
                .expect("forged statement and proof are well parsed");
                let error = spec.add_definition(proof_definition(refusal))
                    .expect_err("false generated environment, missing argument, or output type must be rejected");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(
                    !spec.definitions().contains_key(refusal.name),
                    "{}: rejected record absent",
                    refusal.name
                );
                assert!(
                    spec.env()
                        .get_const(&Name::from_string(refusal.name))
                        .is_none(),
                    "{}: rejected kernel root absent",
                    refusal.name
                );
            }
        });
    }
}
