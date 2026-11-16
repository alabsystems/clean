// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{checked_definition, Registration, DECLARATIONS, REGISTRATIONS};
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};
use clean_kernel::{ConstantKind, ExprKind, Name, TypeChecker};

const PROOF_ROOTS: &[&str] = &[
    "rfnz_parameter_list",
    "rfnz_signature_shape",
    "rfnz_nat_lookup",
    "rfnz_zero_lookup",
    "rfnz_succ_lookup",
    "rfnz_rec_lookup",
    "rfnz_nat_typed",
    "rfnz_zero_typed",
    "rfnz_succ_typed",
    "rfnz_motive_typed",
    "rfnz_zero_domain_typed",
    "rfnz_sarm_typed",
    "rfnz_rhs_typed",
    "rfnz_stored_rhs_shape",
    "rfnz_stored_rhs_typed",
    "rfnz_actual_metadata",
    "rfnz_actual_zero_rule",
    "rfnz_lookup_rhs_typed",
    "rfnz_rec_signature_supported",
    "rfnz_tenv_extend_supported",
    "rfnz_tenv_supported",
    "rfnz_rhs_instance_shape",
    "rfnz_rule_type_instance_shape",
    "rfnz_lookup_instance_typed",
    "rfnz_actual_instance_typed",
    "rfnz_self_parameter_instance_typed",
    "rfnz_rec_typed",
    "rfnz_motive_core_typed",
    "rfnz_minor_core_typed",
    "rfnz_motive_beta",
    "rfnz_minor_type_conversion",
    "rfnz_motive_argument_typed",
    "rfnz_zero_argument_typed",
    "rfnz_minor_argument_typed",
    "rfnz_input_typed",
    "rfnz_guarded_step",
    "rfnz_raw_result_typed",
];
const REUSED_PROOF: &str = "nz_typing_to_semantic";

struct Refusal {
    name: &'static str,
    type_src: &'static str,
    value_src: &'static str,
}

// The seven retained scratch refusals plus a direct input-type forgery.
// Runtime tests must establish refusal; a parse failure never counts.
const REFUSALS: &[Refusal] = &[
    Refusal {
        name: "rfnz_forged_stored_parameter",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr) kcre_witness_nat_zero_rhs (rfnz_rule_type (Level.param Name.anonymous))",
        value_src: r"rfnz_stored_rhs_typed",
    },
    Refusal {
        name: "rfnz_forged_zero_type",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr) rfnz_zero (KExpr.sort (Level.succ Level.zero))",
        value_src: r"rfnz_zero_typed (@ListType.nil KExpr)",
    },
    Refusal {
        name: "rfnz_forged_missing_universe",
        type_src: r"@Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_rec_name (@ListType.nil Level)) (@OptionType.some KExpr (rfnz_rec_type Level.zero))",
        value_src: r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_rec_type Level.zero))",
    },
    Refusal {
        name: "rfnz_forged_double_instance",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs
   (@ListType.cons Level (Level.succ (Level.param rfnz_parameter)) (@ListType.nil Level)))
  (rfnz_rule_type (Level.succ (Level.succ (Level.param rfnz_parameter))))",
        value_src: r"rfnz_actual_instance_typed (Level.succ (Level.param rfnz_parameter))",
    },
    Refusal {
        name: "rfnz_forged_erased_result_universe",
        type_src: r"iota_step (red_rec rfnz_env) rfnz_input
  (KExpr.app (KExpr.app (KExpr.app
   (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs
(@ListType.cons Level Level.zero (@ListType.nil Level)))
   rfnz_motive) rfnz_zero) rfnz_minor)",
        value_src: r"rfnz_guarded_step",
    },
    Refusal {
        name: "rfnz_forged_normalized_iota_target",
        type_src: r"iota_step (red_rec rfnz_env) rfnz_input rfnz_zero",
        value_src: r"rfnz_guarded_step",
    },
    Refusal {
        name: "rfnz_forged_raw_output_type",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.sort Level.zero)",
        value_src: r"rfnz_raw_result_typed",
    },
    Refusal {
        name: "rfnz_forged_input_type",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_input (KExpr.sort Level.zero)",
        value_src: r"rfnz_input_typed",
    },
];

#[test]
fn reflected_nat_zero_sources_parse_and_preserve_checked_terms() {
    use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl, SurfaceExpr};
    fn fragment(source: &str, span: Span) -> Vec<&str> {
        source[span.start..span.end].split_whitespace().collect()
    }
    assert_eq!(DECLARATIONS.len(), 56);
    assert_eq!(REGISTRATIONS.len(), DECLARATIONS.len());
    assert_eq!(PROOF_ROOTS.len(), 37);
    let mut data = 0;
    let mut proofs = 0;
    let mut seen = std::collections::HashSet::new();
    for (index, registration) in REGISTRATIONS.iter().enumerate() {
        let (source, _) = DECLARATIONS[index];
        parse_check(source).expect("original checked declaration parses");
        let SurfaceDecl::Def {
            name,
            binders,
            ty: Some(result),
            val,
            ..
        } = parse_decl(source).expect("original declaration AST")
        else {
            panic!("expected explicit checked definition")
        };
        assert!(seen.insert(name.clone()), "duplicate registration");
        assert_ne!(
            name,
            clean_parser::parse_name(REUSED_PROOF).expect("explicit source name"),
            "existing embedding is reused, not re-registered"
        );
        match registration {
            Registration::Data {
                declaration_index,
                name: registered,
            } => {
                data += 1;
                assert_eq!(*declaration_index, index);
                assert_eq!(
                    clean_parser::parse_name(registered).expect("explicit source name"),
                    name
                );
                assert!(!PROOF_ROOTS.contains(registered));
            }
            Registration::Proof {
                declaration_index,
                name: registered,
                type_src,
                value_src,
            } => {
                proofs += 1;
                assert_eq!(*declaration_index, index);
                assert_eq!(
                    clean_parser::parse_name(registered).expect("explicit source name"),
                    name
                );
                assert!(PROOF_ROOTS.contains(registered));
                assert_ne!(value_src.trim(), *registered, "no self-constant proof");
                parse_check(&format!("def {registered} : {type_src} := {value_src}"))
                    .expect("explicit proof record parses");
                let parsed_type = parse_expr(type_src).expect("explicit theorem type");
                let parsed_value = parse_expr(value_src).expect("explicit theorem body");
                if binders.is_empty() {
                    assert_eq!(
                        fragment(source, result.span()),
                        fragment(type_src, parsed_type.span()),
                        "{name}: result"
                    );
                    assert_eq!(
                        fragment(source, val.span()),
                        fragment(value_src, parsed_value.span()),
                        "{name}: body"
                    );
                } else {
                    let SurfaceExpr::Pi(_, type_binders, explicit_result) = parsed_type else {
                        panic!("{name}: expected forall")
                    };
                    let SurfaceExpr::Lambda(_, value_binders, explicit_body) = parsed_value else {
                        panic!("{name}: expected fun")
                    };
                    assert_eq!(type_binders.len(), binders.len(), "{name}: type binders");
                    assert_eq!(value_binders.len(), binders.len(), "{name}: value binders");
                    for ((original, type_binder), value_binder) in
                        binders.iter().zip(&type_binders).zip(&value_binders)
                    {
                        assert_eq!(
                            fragment(source, original.span),
                            fragment(type_src, type_binder.span),
                            "{name}: forall binder"
                        );
                        assert_eq!(
                            fragment(source, original.span),
                            fragment(value_src, value_binder.span),
                            "{name}: fun binder"
                        );
                    }
                    assert_eq!(
                        fragment(source, result.span()),
                        fragment(type_src, explicit_result.span()),
                        "{name}: result"
                    );
                    assert_eq!(
                        fragment(source, val.span()),
                        fragment(value_src, explicit_body.span()),
                        "{name}: body"
                    );
                }
            }
        }
    }
    assert_eq!((data, proofs), (19, 37));
    assert_eq!(REFUSALS.len(), 8);
    for refusal in REFUSALS {
        parse_check(&format!(
            "def {} : {} := {}",
            refusal.name, refusal.type_src, refusal.value_src
        ))
        .expect("forged statement and proof parse before refusal is tested");
    }
}

#[test]
fn reflected_nat_zero_actual_roots_values_types_and_closures_recheck() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let names = REGISTRATIONS
            .iter()
            .map(|registration| match registration {
                Registration::Data { name, .. } | Registration::Proof { name, .. } => *name,
            })
            .chain(std::iter::once(REUSED_PROOF));
        for root in names {
            let definition = spec
                .definitions()
                .get(root)
                .expect("registered declaration root");
            let name = Name::from_string(root);
            let constant = spec
                .env()
                .get_const(&name)
                .expect("actual kernel environment root");
            let ty = definition
                .elaborated_type
                .as_ref()
                .expect("actual elaborated type");
            let value = definition
                .elaborated_value
                .as_ref()
                .expect("actual elaborated value");
            assert!(!definition.is_axiom, "{root}");
            assert_ne!(constant.kind, ConstantKind::Axiom, "{root}");
            assert_eq!(
                &constant.type_, ty,
                "{root}: kernel/metadata type agreement"
            );
            assert_eq!(
                constant.value.as_ref(),
                Some(value),
                "{root}: kernel/metadata value agreement"
            );
            assert!(
                !matches!(value.kind(), ExprKind::Const(found, _) if found == &name),
                "{root}: not a self-constant proof"
            );
            spec.verify_definition(root)
                .expect("actual body checks against actual stored type");
            assert!(
                spec.env()
                    .axiom_deps(&name)
                    .expect("actual domain-closure root exists")
                    .is_empty(),
                "{root}: domain axioms"
            );
            assert!(
                spec.env()
                    .foundational_axiom_deps(&name)
                    .expect("actual foundational-closure root exists")
                    .is_empty(),
                "{root}: foundational axioms"
            );
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, root).is_empty(),
                "{root}"
            );
        }
        for registration in REGISTRATIONS {
            if let Registration::Proof {
                name,
                type_src,
                value_src,
                ..
            } = registration
            {
                let definition = spec.definitions().get(*name).expect("actual proof record");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                assert_eq!(
                    definition.proof_status,
                    ProofStatus::DerivedProved,
                    "{name}"
                );
                assert_eq!(
                    definition.type_src, *type_src,
                    "{name}: exact registered type source"
                );
                assert_eq!(
                    definition.value_src.as_deref(),
                    Some(*value_src),
                    "{name}: exact registered body source"
                );
            }
        }
        let embedding = spec
            .definitions()
            .get(REUSED_PROOF)
            .expect("existing embedding");
        assert_eq!(embedding.category, AxiomCategory::DerivedLemma);
        assert_eq!(embedding.proof_status, ProofStatus::DerivedProved);
    });
}

#[test]
fn reflected_nat_zero_real_instance_input_guarded_and_output_callers_check() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        for (value_src, type_src) in [
            (
                "rfnz_actual_instance_typed (Level.succ (Level.param rfnz_parameter))",
                "TypingCtx rfnz_tenv (@ListType.nil KExpr) (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level (Level.succ (Level.param rfnz_parameter)) (@ListType.nil Level))) (rfnz_rule_type (Level.succ (Level.param rfnz_parameter)))",
            ),
            (
                "rfnz_lookup_instance_typed (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs) rfnz_actual_zero_rule (Level.succ Level.zero)",
                "TypingCtx rfnz_tenv (@ListType.nil KExpr) (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) (rfnz_rule_type (Level.succ Level.zero))",
            ),
            (
                "rfnz_input_typed",
                "TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_input rfnz_nat",
            ),
            (
                "rfnz_guarded_step",
                "iota_step (red_rec kernel_core_red_env) rfnz_input rfnz_raw_result",
            ),
            (
                "rfnz_raw_result_typed",
                "TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat",
            ),
        ] {
            let value = spec.elaborate_source(value_src, "actual reflected Nat.zero caller").expect("real caller elaborates");
            let expected = spec.elaborate_source(type_src, "actual reflected Nat.zero result type").expect("real result type elaborates");
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            let inferred = checker.infer_type(&value).expect("actual caller checks");
            assert!(checker.is_def_eq(&inferred, &expected), "{value_src}");
        }
    });
}

#[test]
fn reflected_nat_zero_rejects_forged_parameter_input_guarded_and_output_claims() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for refusal in REFUSALS {
            parse_check(&format!(
                "def {} : {} := {}",
                refusal.name, refusal.type_src, refusal.value_src
            ))
            .expect("forged theorem is well parsed");
            let error = spec
                .add_definition(checked_definition(
                    refusal.name,
                    refusal.type_src,
                    refusal.value_src,
                    "Deliberately invalid reflected Nat.zero proof; must be rejected.",
                ))
                .expect_err(
                    "forged type, universe, arity, or immediate raw result must be refused",
                );
            assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
            assert!(
                !spec.definitions().contains_key(refusal.name),
                "{}: rejected proof record absent",
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
