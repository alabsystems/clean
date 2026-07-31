// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{bool_ref, eq_ref, list_ref, nat_ref, nat_succ, nat_zero};
use crate::{
    coq_import::{
        translate_term, translate_term_with_context, Binder, CaseBranch, CaseInfo, Constr,
        ConstructRef, CoqName, InductiveRef, TranslationContext, UniverseInstance,
    },
    BinderInfo, ExprKind, Level, Name,
};

#[test]
fn coq_translate_nat_inductive_maps_to_lean_nat() {
    let expr = translate_term(&Constr::Ind(nat_ref())).expect("translate nat");
    let ExprKind::Const(name, levels) = expr.kind() else {
        panic!("expected const, got {:?}", expr.kind());
    };
    assert_eq!(name, &Name::from_string("Nat"));
    assert!(levels.is_empty());
}

#[test]
fn coq_translate_bool_constructors_map_to_lean_bool() {
    let false_expr = translate_term(&Constr::Construct(ConstructRef {
        inductive: bool_ref().name,
        constructor_index: 1,
        constructor_name: Some("false".to_string()),
        universes: UniverseInstance::default(),
    }))
    .expect("translate false");
    let true_expr = translate_term(&Constr::Construct(ConstructRef {
        inductive: bool_ref().name,
        constructor_index: 2,
        constructor_name: Some("true".to_string()),
        universes: UniverseInstance::default(),
    }))
    .expect("translate true");

    assert!(
        matches!(false_expr.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Bool.false"))
    );
    assert!(
        matches!(true_expr.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Bool.true"))
    );
}

#[test]
fn coq_translate_list_application_preserves_universe_and_argument() {
    let expr = translate_term(&Constr::app(
        Constr::Ind(list_ref()),
        vec![Constr::Ind(nat_ref())],
    ))
    .expect("translate list nat");
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    let ExprKind::Const(name, levels) = head.kind() else {
        panic!("expected const head, got {:?}", head.kind());
    };
    assert_eq!(name, &Name::from_string("List"));
    assert_eq!(levels.len(), 1);
    assert_eq!(levels[0], Level::param(Name::from_string("u")));
    assert_eq!(args.len(), 1);
    assert!(
        matches!(args[0].kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat"))
    );
}

#[test]
fn coq_translate_list_case_uses_cases_on_with_parameter_first() {
    let list_nat = Constr::app(Constr::Ind(list_ref()), vec![Constr::Ind(nat_ref())]);
    let term = Constr::Case(CaseInfo {
        inductive: CoqName::from_dotted("Coq.Init.Datatypes.list"),
        universes: UniverseInstance {
            levels: vec![super::super::UniverseLevel::Param("u".to_string())],
        },
        eliminator: None,
        parameters: vec![Constr::Ind(nat_ref())],
        indices: vec![],
        motive: Box::new(Constr::Lambda {
            binder: Binder::anonymous(list_nat),
            body: Box::new(Constr::Ind(nat_ref())),
        }),
        scrutinee: Box::new(Constr::app(
            Constr::Construct(ConstructRef {
                inductive: CoqName::from_dotted("Coq.Init.Datatypes.list"),
                constructor_index: 1,
                constructor_name: Some("nil".to_string()),
                universes: UniverseInstance {
                    levels: vec![super::super::UniverseLevel::Param("u".to_string())],
                },
            }),
            vec![Constr::Ind(nat_ref())],
        )),
        branches: vec![
            CaseBranch {
                constructor: None,
                binders: vec![],
                body: Box::new(nat_zero()),
            },
            CaseBranch {
                constructor: None,
                binders: vec![
                    Binder::explicit("head", Constr::Ind(nat_ref())),
                    Binder::explicit(
                        "tail",
                        Constr::app(Constr::Ind(list_ref()), vec![Constr::Ind(nat_ref())]),
                    ),
                ],
                body: Box::new(nat_succ(nat_zero())),
            },
        ],
    });

    let expr = translate_term(&term).expect("translate list case");
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("List.casesOn"))
    );
    // Lean-faithful casesOn order: params → motive → indices → scrutinee
    // (major) → branches (minors).
    assert_eq!(args.len(), 5);
    assert!(
        matches!(args[0].kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat"))
    );
    assert!(matches!(args[1].kind(), ExprKind::Lam(_, _, _)));
    // Scrutinee (List.nil Nat) comes before the branches.
    assert!(
        matches!(args[2].get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::from_string("List.nil"))
    );
    assert!(
        matches!(args[3].kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.zero"))
    );
    assert!(matches!(args[4].kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn coq_translate_basic_term_forms_preserve_binding_and_application_shape() {
    let context = TranslationContext::with_locals([Some("x".to_string())]);
    let var_expr = translate_term_with_context(&Constr::Var(CoqName::from_dotted("x")), &context)
        .expect("translate local var");
    assert!(matches!(var_expr.kind(), ExprKind::BVar(0)));

    let lambda_expr = translate_term(&Constr::Lambda {
        binder: Binder::explicit("x", Constr::Ind(nat_ref())),
        body: Box::new(Constr::Var(CoqName::from_dotted("x"))),
    })
    .expect("translate lambda");
    let ExprKind::Lam(binder, ty, body) = lambda_expr.kind() else {
        panic!("expected lambda, got {:?}", lambda_expr.kind());
    };
    assert_eq!(binder.info, BinderInfo::Default);
    assert!(matches!(ty.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat")));
    assert!(matches!(body.kind(), ExprKind::BVar(0)));

    let pi_expr = translate_term(&Constr::Prod {
        binder: Binder::explicit("x", Constr::Ind(nat_ref())),
        body: Box::new(Constr::Var(CoqName::from_dotted("x"))),
    })
    .expect("translate prod");
    let ExprKind::Pi(binder, ty, body) = pi_expr.kind() else {
        panic!("expected pi, got {:?}", pi_expr.kind());
    };
    assert_eq!(binder.info, BinderInfo::Default);
    assert!(matches!(ty.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat")));
    assert!(matches!(body.kind(), ExprKind::BVar(0)));

    let app_expr = translate_term(&Constr::app(
        Constr::const_("Coq.Init.Peano.plus"),
        vec![nat_zero(), nat_zero()],
    ))
    .expect("translate application");
    let head = app_expr.get_app_fn();
    let args = app_expr.get_app_args();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.add"))
    );
    assert_eq!(args.len(), 2);
    assert!(
        matches!(args[0].kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.zero"))
    );
    assert!(
        matches!(args[1].kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.zero"))
    );
}

#[test]
fn coq_translate_names_ignore_empty_path_segments() {
    let alias_expr = translate_term(&Constr::Const {
        name: CoqName::from_dotted(".Coq..Init.Peano.plus."),
        universes: UniverseInstance::default(),
    })
    .expect("translate alias with empty segments");
    assert!(
        matches!(alias_expr.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.add"))
    );

    let fallback_expr = translate_term(&Constr::Const {
        name: CoqName::from_dotted(".My..Module.term."),
        universes: UniverseInstance::default(),
    })
    .expect("translate fallback name with empty segments");
    let ExprKind::Const(name, levels) = fallback_expr.kind() else {
        panic!("expected const, got {:?}", fallback_expr.kind());
    };
    assert_eq!(name, &Name::from_string("My.Module.term"));
    assert!(levels.is_empty());
}

#[test]
fn coq_translate_unknown_nested_module_paths_round_trip() {
    for (term, lean_name) in [
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Company.Project.Feature.Tree"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Company.Project.Feature.Tree",
        ),
        (
            Constr::Construct(ConstructRef {
                inductive: CoqName::from_dotted("Company.Project.Feature.Tree"),
                constructor_index: 2,
                constructor_name: Some("leaf".to_string()),
                universes: UniverseInstance::default(),
            }),
            "Company.Project.Feature.Tree.leaf",
        ),
    ] {
        let expr =
            translate_term(&term).unwrap_or_else(|err| panic!("translate {lean_name}: {err}"));
        let ExprKind::Const(name, levels) = expr.kind() else {
            panic!("expected const for {lean_name}, got {:?}", expr.kind());
        };
        assert_eq!(name, &Name::from_string(lean_name));
        assert!(levels.is_empty(), "unexpected universes for {lean_name}");
    }
}

#[test]
fn coq_translate_extended_stdlib_mappings_cover_types_relations_and_constructors() {
    for (term, lean_name) in [
        (
            Constr::Const {
                name: CoqName::from_dotted("Coq.Init.Peano.plus"),
                universes: UniverseInstance::default(),
            },
            "Nat.add",
        ),
        (
            Constr::Const {
                name: CoqName::from_dotted("Coq.Init.Peano.mult"),
                universes: UniverseInstance::default(),
            },
            "Nat.mul",
        ),
        (Constr::Ind(eq_ref()), "Eq"),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Datatypes.option"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Option",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Datatypes.prod"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Prod",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Datatypes.sum"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Sum",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Datatypes.unit"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Unit",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Specif.sig"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Subtype",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Peano.le"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Nat.le",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Peano.lt"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Nat.lt",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("BinNums.Z"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Int",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("BinNums.positive"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Nat",
        ),
        (
            Constr::Construct(ConstructRef {
                inductive: CoqName::from_dotted("Coq.Init.Logic.eq"),
                constructor_index: 1,
                constructor_name: Some("eq_refl".to_string()),
                universes: UniverseInstance::default(),
            }),
            "Eq.refl",
        ),
    ] {
        let expr =
            translate_term(&term).unwrap_or_else(|err| panic!("translate {lean_name}: {err}"));
        let ExprKind::Const(name, levels) = expr.kind() else {
            panic!("expected const for {lean_name}, got {:?}", expr.kind());
        };
        assert_eq!(name, &Name::from_string(lean_name));
        assert!(levels.is_empty(), "unexpected universes for {lean_name}");
    }
}

#[test]
fn coq_translate_stdlib_type_aliases_cover_short_and_nested_names() {
    for (coq_name, lean_name) in [
        ("nat", "Nat"),
        ("Datatypes.list", "List"),
        ("option", "Option"),
        ("Coq.Arith.PeanoNat.Nat", "Nat"),
        ("Coq.Init.Specif.sigT", "Sigma"),
        ("Coq.ZArith.BinInt.Z", "Int"),
    ] {
        let expr = translate_term(&Constr::Ind(InductiveRef {
            name: CoqName::from_dotted(coq_name),
            index: 0,
            universes: UniverseInstance::default(),
        }))
        .unwrap_or_else(|err| panic!("translate {coq_name} to {lean_name}: {err}"));
        let ExprKind::Const(name, levels) = expr.kind() else {
            panic!("expected const for {coq_name}, got {:?}", expr.kind());
        };
        assert_eq!(name, &Name::from_string(lean_name));
        assert!(levels.is_empty(), "unexpected universes for {coq_name}");
    }
}

#[test]
fn coq_imported_stdlib_propositions_translate_to_lean_names() {
    let mut context = TranslationContext::empty();
    context.import_stdlib_propositions();

    for (term, lean_name) in [
        (
            Constr::Const {
                name: CoqName::from_dotted("Coq.Init.Logic.not"),
                universes: UniverseInstance::default(),
            },
            "Not",
        ),
        (
            Constr::Const {
                name: CoqName::from_dotted("Coq.Init.Logic.iff"),
                universes: UniverseInstance::default(),
            },
            "Iff",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Logic.and"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "And",
        ),
        (
            Constr::Ind(InductiveRef {
                name: CoqName::from_dotted("Coq.Init.Logic.ex"),
                index: 0,
                universes: UniverseInstance::default(),
            }),
            "Exists",
        ),
        (
            Constr::Construct(ConstructRef {
                inductive: CoqName::from_dotted("Coq.Init.Logic.and"),
                constructor_index: 1,
                constructor_name: Some("conj".to_string()),
                universes: UniverseInstance::default(),
            }),
            "And.intro",
        ),
    ] {
        let expr = translate_term_with_context(&term, &context)
            .unwrap_or_else(|err| panic!("translate {lean_name}: {err}"));
        let ExprKind::Const(name, levels) = expr.kind() else {
            panic!("expected const for {lean_name}, got {:?}", expr.kind());
        };
        assert_eq!(name, &Name::from_string(lean_name));
        assert!(levels.is_empty(), "unexpected universes for {lean_name}");
    }
}

#[test]
fn coq_translate_coinductive_block_fails_closed() {
    use crate::coq_import::{
        translate_inductive_decl, CoqImportError, InductiveBody, InductiveKind, MutualInductiveDecl,
    };

    // A CoInductive block must be rejected, never silently admitted as a
    // least-fixpoint inductive (which would be a different type and would
    // receive an induction principle the greatest fixpoint must not have).
    let decl = MutualInductiveDecl {
        kind: InductiveKind::CoInductive,
        universe_params: vec![],
        num_params: 0,
        params: vec![],
        bodies: vec![InductiveBody {
            name: CoqName::from_dotted("Coq.Lists.Streams.Stream"),
            type_: Constr::prop(),
            constructors: vec![],
        }],
    };

    let context = TranslationContext::default();
    match translate_inductive_decl(&decl, &context) {
        Err(CoqImportError::CoinductiveUnsupported { name }) => {
            assert_eq!(name, "Coq.Lists.Streams.Stream");
        }
        other => panic!("CoInductive block must fail closed, got {other:?}"),
    }
}

#[test]
fn coq_translate_plain_inductive_block_still_translates() {
    use crate::coq_import::{
        translate_inductive_decl, InductiveBody, InductiveKind, MutualInductiveDecl,
    };

    // Companion pin for the fail-closed CoInductive check: an ordinary
    // Inductive block with the same shape must keep translating.
    let decl = MutualInductiveDecl {
        kind: InductiveKind::Inductive,
        universe_params: vec![],
        num_params: 0,
        params: vec![],
        bodies: vec![InductiveBody {
            name: CoqName::from_dotted("Test.Empty"),
            type_: Constr::prop(),
            constructors: vec![],
        }],
    };

    let context = TranslationContext::default();
    let translated =
        translate_inductive_decl(&decl, &context).expect("plain inductive must translate");
    assert_eq!(translated.types.len(), 1);
}
