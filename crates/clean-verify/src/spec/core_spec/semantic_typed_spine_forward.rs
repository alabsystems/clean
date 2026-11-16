// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Forward application reconstruction for the existing TypedRawPiSpine.
//!
//! The five declarations preserve the independently checked names, types and
//! proof bodies from scratch/semantic_typed_spine_forward.rs (5ae86b52d).
//! The registration records only desugar declaration binders into forall/fun.
//! Actual typed arguments are inputs in the existing trace; this does not claim
//! to obtain them from nothing. The generic theorem needs no faithfulness,
//! coherence, candidate model, subject reduction or desired output premise.
//! The two dependent-identity callers are inhabited model examples, not source
//! admission, general iota preservation or Rust execution correspondence.
//!
//! Exact dependency/check provenance:
//! scratch/self-verification-typed-spine-forward-2026-09-09.md.

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
        name: "typed_raw_pi_spine_apply",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U), forall (h : KExpr),
 TypingCtxConvIn R tenv G h F -> TypingCtxConvIn R tenv G (apply_spine args h) U",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) => @TypedRawPiSpine.rec R tenv G
  (fun (F0 : KExpr) (xs : ListType KExpr) (V : KExpr)
   (_tr : TypedRawPiSpine R tenv G F0 xs V) => forall (h : KExpr),
   TypingCtxConvIn R tenv G h F0 -> TypingCtxConvIn R tenv G (apply_spine xs h) V)
  (fun (F0 : KExpr) (h : KExpr) (head : TypingCtxConvIn R tenv G h F0) => head)
  (fun (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (V : KExpr)
   (argument : TypingCtxConvIn R tenv G a A)
   (_tail : TypedRawPiSpine R tenv G (instantiate B a) rest V)
   (ih : forall (h : KExpr), TypingCtxConvIn R tenv G h (instantiate B a) ->
    TypingCtxConvIn R tenv G (apply_spine rest h) V)
   (h : KExpr) (head : TypingCtxConvIn R tenv G h (KExpr.pi A B)) =>
   ih (KExpr.app h a) (@TypingCtxConvIn.app R tenv G h a A B head argument))
  F args U trace",
        description: "Forward reconstruction from the existing typed raw-Pi spine. Each step uses the actual application rule; argument typings come from the supplied trace, not a new oracle.",
    },
    CheckedProof {
        name: "typed_raw_pi_spine_const_apply",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr)
 (lookup : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
 (trace : TypedRawPiSpine R tenv G F args U), TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) U",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr)
 (lookup : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
 (trace : TypedRawPiSpine R tenv G F args U) => typed_raw_pi_spine_apply R tenv G F args U trace (KExpr.const n us)
  (@TypingCtxConvIn.const R tenv G n us F lookup)",
        description: "Actual guarded constant lookup constructs the head typing before the existing trace reconstructs its application spine.",
    },
    CheckedProof {
        name: "typed_raw_pi_spine_identity_trace",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr), TypedRawPiSpine R tenv G
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
 typed_spine_identity_args (KExpr.sort (Level.succ Level.zero))",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) => @TypedRawPiSpine.cons R tenv G
  (KExpr.sort (Level.succ (Level.succ Level.zero)))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
  (KExpr.sort (Level.succ Level.zero))
  (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))
  (KExpr.sort (Level.succ Level.zero))
  (@TypingCtxConvIn.sort R tenv G (Level.succ Level.zero))
  (@TypedRawPiSpine.cons R tenv G
   (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
   (KExpr.sort Level.zero) (@ListType.nil KExpr) (KExpr.sort (Level.succ Level.zero))
   (@TypingCtxConvIn.sort R tenv G Level.zero)
   (@TypedRawPiSpine.nil R tenv G (KExpr.sort (Level.succ Level.zero))))",
        description: "Two real sort-typed arguments form the dependent identity trace; the second domain is the actual instantiated first argument.",
    },
    CheckedProof {
        name: "typed_raw_pi_spine_identity_body_apply",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr), TypingCtxConvIn R tenv G
 (apply_spine typed_spine_identity_args
  (typed_spine_identity_value (Level.succ (Level.succ Level.zero))))
 (KExpr.sort (Level.succ Level.zero))",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) => typed_raw_pi_spine_apply R tenv G
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  typed_spine_identity_args (KExpr.sort (Level.succ Level.zero))
  (typed_raw_pi_spine_identity_trace R tenv G)
  (typed_spine_identity_value (Level.succ (Level.succ Level.zero)))
  (typed_spine_identity_body_typed R tenv G (Level.succ (Level.succ Level.zero)))",
        description: "The genuinely inhabited dependent identity lambda is applied through the proved forward API; no assumed body typing or recursor-preservation claim.",
    },
    CheckedProof {
        name: "typed_raw_pi_spine_identity_const_apply",
        type_src: r"forall (R : RedEnv) (G : ListType KExpr), TypingCtxConvIn R typed_spine_identity_tenv G
 (apply_spine typed_spine_identity_args (KExpr.const Name.anonymous (@ListType.nil Level)))
 (KExpr.sort (Level.succ Level.zero))",
        value_src: r"fun (R : RedEnv) (G : ListType KExpr) => typed_raw_pi_spine_const_apply R typed_spine_identity_tenv G Name.anonymous (@ListType.nil Level)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  typed_spine_identity_args (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_lookup
  (typed_raw_pi_spine_identity_trace R typed_spine_identity_tenv G)",
        description: "The registered singleton identity signature and its actual guarded lookup exercise the constant forward wrapper.",
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
    /// Requires semantic_typed_spine, including its dependent identity value,
    /// argument list, actual body typing and guarded signature lookup.
    /// Registers five actual checked proof bodies, with no status mutation.
    pub(super) fn add_semantic_typed_spine_forward(&mut self) -> Result<(), SpecError> {
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
        "typed_raw_pi_spine_apply",
        "typed_raw_pi_spine_const_apply",
        "typed_raw_pi_spine_identity_trace",
        "typed_raw_pi_spine_identity_body_apply",
        "typed_raw_pi_spine_identity_const_apply",
    ];

    // Byte-identical original checked declaration strings; the parser test
    // verifies the explicit registration records retain every binder and body.
    const PROTOTYPES: &[&str] = &[
        r"def typed_raw_pi_spine_apply (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
 (F : KExpr) (args : ListType KExpr) (U : KExpr)
 (trace : TypedRawPiSpine R tenv G F args U) : forall (h : KExpr),
 TypingCtxConvIn R tenv G h F -> TypingCtxConvIn R tenv G (apply_spine args h) U :=
 @TypedRawPiSpine.rec R tenv G
  (fun (F0 : KExpr) (xs : ListType KExpr) (V : KExpr)
   (_tr : TypedRawPiSpine R tenv G F0 xs V) => forall (h : KExpr),
   TypingCtxConvIn R tenv G h F0 -> TypingCtxConvIn R tenv G (apply_spine xs h) V)
  (fun (F0 : KExpr) (h : KExpr) (head : TypingCtxConvIn R tenv G h F0) => head)
  (fun (A : KExpr) (B : KExpr) (a : KExpr) (rest : ListType KExpr) (V : KExpr)
   (argument : TypingCtxConvIn R tenv G a A)
   (_tail : TypedRawPiSpine R tenv G (instantiate B a) rest V)
   (ih : forall (h : KExpr), TypingCtxConvIn R tenv G h (instantiate B a) ->
    TypingCtxConvIn R tenv G (apply_spine rest h) V)
   (h : KExpr) (head : TypingCtxConvIn R tenv G h (KExpr.pi A B)) =>
   ih (KExpr.app h a) (@TypingCtxConvIn.app R tenv G h a A B head argument))
  F args U trace",
        r"def typed_raw_pi_spine_const_apply (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (F : KExpr)
 (args : ListType KExpr) (U : KExpr)
 (lookup : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
 (trace : TypedRawPiSpine R tenv G F args U) :
 TypingCtxConvIn R tenv G (apply_spine args (KExpr.const n us)) U :=
 typed_raw_pi_spine_apply R tenv G F args U trace (KExpr.const n us)
  (@TypingCtxConvIn.const R tenv G n us F lookup)",
        r"def typed_raw_pi_spine_identity_trace (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) : TypedRawPiSpine R tenv G
 (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
 typed_spine_identity_args (KExpr.sort (Level.succ Level.zero)) :=
 @TypedRawPiSpine.cons R tenv G
  (KExpr.sort (Level.succ (Level.succ Level.zero)))
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)))
  (KExpr.sort (Level.succ Level.zero))
  (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))
  (KExpr.sort (Level.succ Level.zero))
  (@TypingCtxConvIn.sort R tenv G (Level.succ Level.zero))
  (@TypedRawPiSpine.cons R tenv G
   (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
   (KExpr.sort Level.zero) (@ListType.nil KExpr) (KExpr.sort (Level.succ Level.zero))
   (@TypingCtxConvIn.sort R tenv G Level.zero)
   (@TypedRawPiSpine.nil R tenv G (KExpr.sort (Level.succ Level.zero))))",
        r"def typed_raw_pi_spine_identity_body_apply (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) : TypingCtxConvIn R tenv G
 (apply_spine typed_spine_identity_args
  (typed_spine_identity_value (Level.succ (Level.succ Level.zero))))
 (KExpr.sort (Level.succ Level.zero)) :=
 typed_raw_pi_spine_apply R tenv G
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  typed_spine_identity_args (KExpr.sort (Level.succ Level.zero))
  (typed_raw_pi_spine_identity_trace R tenv G)
  (typed_spine_identity_value (Level.succ (Level.succ Level.zero)))
  (typed_spine_identity_body_typed R tenv G (Level.succ (Level.succ Level.zero)))",
        r"def typed_raw_pi_spine_identity_const_apply (R : RedEnv) (G : ListType KExpr) :
 TypingCtxConvIn R typed_spine_identity_tenv G
 (apply_spine typed_spine_identity_args (KExpr.const Name.anonymous (@ListType.nil Level)))
 (KExpr.sort (Level.succ Level.zero)) :=
 typed_raw_pi_spine_const_apply R typed_spine_identity_tenv G Name.anonymous (@ListType.nil Level)
  (typed_spine_identity_type (Level.succ (Level.succ Level.zero)))
  typed_spine_identity_args (KExpr.sort (Level.succ Level.zero)) typed_spine_identity_lookup
  (typed_raw_pi_spine_identity_trace R typed_spine_identity_tenv G)",
    ];

    const NEGATIVE_CONTROLS: &[CheckedProof] = &[
        CheckedProof {
            name: "typed_raw_pi_spine_forged_residual",
            type_src: r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr), TypingCtxConvIn R tenv G
 (apply_spine typed_spine_identity_args
  (typed_spine_identity_value (Level.succ (Level.succ Level.zero))))
 (KExpr.sort Level.zero)",
            value_src: r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) => typed_raw_pi_spine_identity_body_apply R tenv G",
            description: "Well-parsed forged typed-spine endpoint; expected type refusal.",
        },
        CheckedProof {
            name: "typed_raw_pi_spine_forged_domain",
            type_src: r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr), TypedRawPiSpine R tenv G
 (typed_spine_identity_type (Level.succ Level.zero))
 typed_spine_identity_args (KExpr.sort (Level.succ Level.zero))",
            value_src: r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) => typed_raw_pi_spine_identity_trace R tenv G",
            description: "Well-parsed forged typed-spine endpoint; expected type refusal.",
        },
    ];

    #[test]
    fn typed_spine_forward_sources_parse_and_preserve_checked_terms() {
        use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl, SurfaceExpr};
        fn fragment(source: &str, span: Span) -> Vec<&str> {
            source[span.start..span.end].split_whitespace().collect()
        }

        assert_eq!(PROOFS.len(), 5);
        assert_eq!(PROTOTYPES.len(), PROOFS.len());
        assert_eq!(PROOF_ROOTS.len(), PROOFS.len());
        for ((proof, prototype), root) in PROOFS.iter().zip(PROTOTYPES).zip(PROOF_ROOTS) {
            assert_eq!(proof.name, *root);
            parse_check(prototype).expect("checked prototype parses");
            parse_check(&format!(
                "def {} : {} := {}",
                proof.name, proof.type_src, proof.value_src
            ))
            .expect("explicit checked record parses");
            let SurfaceDecl::Def {
                name,
                binders,
                ty: Some(result),
                val,
                ..
            } = parse_decl(prototype).expect("checked prototype AST")
            else {
                panic!("expected a definition prototype")
            };
            assert_eq!(
                clean_parser::parse_name(proof.name).expect("explicit source name"),
                name
            );
            let SurfaceExpr::Pi(_, type_binders, explicit_result) =
                parse_expr(proof.type_src).expect("explicit theorem type")
            else {
                panic!("expected explicit forall")
            };
            let SurfaceExpr::Lambda(_, value_binders, explicit_body) =
                parse_expr(proof.value_src).expect("explicit theorem body")
            else {
                panic!("expected explicit fun")
            };
            assert_eq!(
                binders.len(),
                type_binders.len(),
                "{}: type binders",
                proof.name
            );
            assert_eq!(
                binders.len(),
                value_binders.len(),
                "{}: value binders",
                proof.name
            );
            for ((original, type_binder), value_binder) in
                binders.iter().zip(&type_binders).zip(&value_binders)
            {
                assert_eq!(
                    fragment(prototype, original.span),
                    fragment(proof.type_src, type_binder.span),
                    "{}: forall binder",
                    proof.name
                );
                assert_eq!(
                    fragment(prototype, original.span),
                    fragment(proof.value_src, value_binder.span),
                    "{}: fun binder",
                    proof.name
                );
            }
            assert_eq!(
                fragment(prototype, result.span()),
                fragment(proof.type_src, explicit_result.span()),
                "{}: result type",
                proof.name
            );
            assert_eq!(
                fragment(prototype, val.span()),
                fragment(proof.value_src, explicit_body.span()),
                "{}: proof body",
                proof.name
            );
            assert_ne!(proof.value_src.trim(), proof.name, "no self-constant proof");
        }
        for proof in NEGATIVE_CONTROLS {
            parse_check(&format!(
                "def {} : {} := {}",
                proof.name, proof.type_src, proof.value_src
            ))
            .expect("negative control must parse");
        }
    }

    #[test]
    fn typed_spine_forward_actual_roots_values_types_and_closures_recheck() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for proof in PROOFS {
                let definition = spec
                    .definitions()
                    .get(proof.name)
                    .expect("registered proof record");
                let name = Name::from_string(proof.name);
                let constant = spec
                    .env()
                    .get_const(&name)
                    .expect("actual environment root");
                let ty = definition
                    .elaborated_type
                    .as_ref()
                    .expect("actual elaborated type");
                let value = definition
                    .elaborated_value
                    .as_ref()
                    .expect("actual elaborated body");
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
                assert_eq!(definition.type_src, proof.type_src, "{}", proof.name);
                assert_eq!(
                    definition.value_src.as_deref(),
                    Some(proof.value_src),
                    "{}",
                    proof.name
                );
                assert_eq!(&constant.type_, ty, "{}: stored type agrees", proof.name);
                assert_eq!(
                    constant.value.as_ref(),
                    Some(value),
                    "{}: stored value agrees",
                    proof.name
                );
                assert!(
                    !matches!(value.kind(), ExprKind::Const(found, _) if found == &name),
                    "{}: registered body is not its own constant",
                    proof.name
                );
                spec.verify_definition(proof.name)
                    .expect("actual body rechecks against actual type");
                let domains = spec
                    .env()
                    .axiom_deps(&name)
                    .expect("root exists for domain closure");
                let foundations = spec
                    .env()
                    .foundational_axiom_deps(&name)
                    .expect("root exists for foundational closure");
                assert!(
                    domains.is_empty(),
                    "{}: domain axioms {domains:?}",
                    proof.name
                );
                assert!(
                    foundations.is_empty(),
                    "{}: foundational axioms {foundations:?}",
                    proof.name
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, proof.name).is_empty(),
                    "{}",
                    proof.name
                );
            }
        });
    }

    #[test]
    fn typed_spine_forward_real_identity_callers_check() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            let environment = "(RedEnv.mk RecEnv.empty DefEnv.empty IndCtorEnv.empty)";
            let context = "(@ListType.nil KExpr)";
            for (value_src, head) in [
                (
                    format!("typed_raw_pi_spine_identity_body_apply {environment} typed_spine_identity_tenv {context}"),
                    "(typed_spine_identity_value (Level.succ (Level.succ Level.zero)))",
                ),
                (
                    format!("typed_raw_pi_spine_identity_const_apply {environment} {context}"),
                    "(KExpr.const Name.anonymous (@ListType.nil Level))",
                ),
            ] {
                let type_src = format!("TypingCtxConvIn {environment} typed_spine_identity_tenv {context} (apply_spine typed_spine_identity_args {head}) (KExpr.sort (Level.succ Level.zero))");
                let value = spec.elaborate_source(&value_src, "actual forward caller").expect("actual caller elaborates");
                let expected = spec.elaborate_source(&type_src, "actual caller result type").expect("actual caller result type elaborates");
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let inferred = checker.infer_type(&value).expect("actual caller typechecks");
                assert!(checker.is_def_eq(&inferred, &expected), "{value_src}");
            }
        });
    }

    #[test]
    fn typed_spine_forward_rejects_forged_residual_and_domain() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for proof in NEGATIVE_CONTROLS {
                parse_check(&format!(
                    "def {} : {} := {}",
                    proof.name, proof.type_src, proof.value_src
                ))
                .expect("forged endpoint/domain is well parsed");
                let error = spec
                    .add_definition(proof_definition(proof))
                    .expect_err("a wrong residual or initial universe domain must be refused");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(
                    !spec.definitions().contains_key(proof.name),
                    "rejected proof must not be registered"
                );
                assert!(
                    spec.env()
                        .get_const(&Name::from_string(proof.name))
                        .is_none(),
                    "rejected proof must not appear in the kernel environment"
                );
            }
        });
    }
}
