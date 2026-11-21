// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Authority-boundary regressions for inductive admission and iota rules.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

fn two_ctor_enum(name: &str) -> InductiveDecl {
    let ind_name = Name::from_string(name);
    let ind = Expr::const_(ind_name.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(&format!("{name}.left")),
                    type_: ind.clone(),
                },
                Constructor {
                    name: Name::from_string(&format!("{name}.right")),
                    type_: ind,
                },
            ],
        }],
    }
}

#[derive(Debug, PartialEq, Eq)]
struct FamilyTableShape {
    constants: usize,
    origins: usize,
    verification: usize,
    inductives: usize,
    constructors: usize,
    recursors: usize,
    structure_fields: usize,
    classes: usize,
    instance_classes: usize,
    instance_names: usize,
    param_names: usize,
    param_binder_infos: usize,
    generation: u64,
}

fn family_table_shape(env: &Environment) -> FamilyTableShape {
    FamilyTableShape {
        constants: env.constants.len(),
        origins: env.constant_origins.len(),
        verification: env.declaration_verification.len(),
        inductives: env.inductives.len(),
        constructors: env.constructors.len(),
        recursors: env.recursors.len(),
        structure_fields: env.structure_fields.len(),
        classes: env.classes.len(),
        instance_classes: env.instances.len(),
        instance_names: env.instance_names.len(),
        param_names: env.param_names.len(),
        param_binder_infos: env.param_binder_infos.len(),
        generation: env.generation,
    }
}

fn replace_final_pi_domain(type_: &Expr, replacement: Expr) -> Expr {
    let ExprKind::Pi(binder, domain, codomain) = type_.kind() else {
        panic!("expected a nonempty Pi telescope, got {type_:?}");
    };
    if matches!(codomain.kind(), ExprKind::Pi(..)) {
        Expr::pi(
            *binder,
            domain.as_ref().clone(),
            replace_final_pi_domain(codomain, replacement),
        )
    } else {
        Expr::pi(*binder, replacement, codomain.as_ref().clone())
    }
}

fn assert_recursor_collision_rolls_back(name: &str, core_only: bool) {
    let mut env = Environment::new();
    let rec_name = Name::from_string(&format!("{name}.rec"));
    env.add_decl(Declaration::Axiom {
        name: rec_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("collision fixture should register");

    let tables_before = family_table_shape(&env);
    let verification_before = env.declaration_verification(&rec_name);

    let family_name = Name::from_string(name);
    let ctor_name = Name::from_string(&format!("{name}.left"));
    let declaration = two_ctor_enum(name);
    let result = if core_only {
        env.add_inductive_core(declaration)
    } else {
        env.add_inductive(declaration)
    };
    let error = result.expect_err("occupied generated recursor name must reject the family");
    assert!(matches!(error, EnvError::DuplicateName(name) if name == rec_name));

    assert_eq!(family_table_shape(&env), tables_before);
    assert_eq!(env.declaration_verification(&rec_name), verification_before);
    assert!(env.get_const(&family_name).is_none());
    assert!(env.get_inductive(&family_name).is_none());
    assert!(env.get_const(&ctor_name).is_none());
    assert!(env.get_constructor(&ctor_name).is_none());
    assert!(
        env.get_const(&rec_name).is_some(),
        "collision fixture was lost"
    );
}

#[test]
fn inductive_recursor_name_collision_rolls_back_every_family_table() {
    assert_recursor_collision_rolls_back("AtomicFamily", false);
}

#[test]
fn inductive_core_recursor_name_collision_uses_same_transaction() {
    assert_recursor_collision_rolls_back("AtomicCoreFamily", true);
}

#[test]
fn recursor_full_validation_rejects_duplicate_rule_and_missing_constructor() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Roster"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Roster.rec");
    let left = Name::from_string("Roster.left");
    let rec = env
        .recursors
        .get_mut(&rec_name)
        .expect("generated recursor");
    assert_eq!(rec.rules.len(), 2);
    rec.rules[1].constructor_name = left;
    env.declaration_verification
        .insert(rec_name.clone(), DeclarationVerification::StructuralOnly);

    let error = env
        .validate_and_stamp_recursor(&rec_name)
        .expect_err("duplicate rule key must not earn full authority");
    assert!(format!("{error:?}").contains("duplicate rule"));
    assert_eq!(
        env.declaration_verification(&rec_name),
        Some(DeclarationVerification::StructuralOnly)
    );
}

#[test]
fn recursor_full_validation_rejects_well_formed_wrong_rule_rhs() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Subject"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Subject.rec");
    let rec = env
        .recursors
        .get_mut(&rec_name)
        .expect("generated recursor");
    assert_eq!(rec.rules.len(), 2);

    // Both RHSs have the same closed lambda shape.  Reusing the left rule for
    // the right constructor is therefore syntactically well formed, but returns
    // the left minor (`motive left`) where `motive right` is required.
    rec.rules[1].rhs = rec.rules[0].rhs.clone();
    env.declaration_verification
        .insert(rec_name.clone(), DeclarationVerification::StructuralOnly);

    let error = env
        .validate_and_stamp_recursor(&rec_name)
        .expect_err("wrong-typed reduction payload must not earn full authority");
    assert!(format!("{error:?}").contains("violates subject reduction"));
    assert_eq!(
        env.declaration_verification(&rec_name),
        Some(DeclarationVerification::StructuralOnly)
    );
}

#[test]
fn read_only_recursor_authentication_accepts_canonical_packets() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Canonical"))
        .expect("valid enum should register");

    for suffix in ["rec", "casesOn", "recOn"] {
        let name = Name::from_string(&format!("Canonical.{suffix}"));
        env.authenticate_recursor_readonly(&name)
            .unwrap_or_else(|error| panic!("canonical `{name}` packet must authenticate: {error}"));
    }
}

#[test]
fn read_only_recursor_authentication_rejects_reordered_rules() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Ordered"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Ordered.rec");
    env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor")
        .rules
        .swap(0, 1);

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("constructor rules are positional reduction authority");
    assert!(
        error.contains("canonical declaration order"),
        "reordered rules must report their positional disagreement, got {error}"
    );
}

#[test]
fn read_only_recursor_authentication_rejects_missing_rule() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("Missing"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("Missing.rec");
    env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor")
        .rules
        .pop();

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("a partial constructor roster must not authenticate");
    assert!(
        error.contains("rules but num_minors") || error.contains("has 2 constructors"),
        "missing rule must report an exact arity disagreement, got {error}"
    );
}

#[test]
fn read_only_recursor_authentication_rejects_overapplied_major_spine() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("MajorSpine"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("MajorSpine.rec");
    let overapplied_major = Expr::app(
        Expr::const_(Name::from_string("MajorSpine"), vec![]),
        Expr::type_(),
    );
    let malformed_type = replace_final_pi_domain(
        &env.get_recursor(&rec_name)
            .expect("generated recursor")
            .type_,
        overapplied_major,
    );
    env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor")
        .type_ = malformed_type.clone();
    env.constants
        .get_mut(&rec_name)
        .expect("generated recursor constant")
        .type_ = malformed_type;

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("an overapplied major premise must not be truncated to its expected prefix");
    assert!(
        error.contains("major premise supplies 1 inductive arguments, expected 0"),
        "overapplied major spine must report its exact arity, got {error}"
    );
}

#[test]
fn read_only_recursor_authentication_rejects_overapplied_constructor_return_spine() {
    let mut env = Environment::new();
    env.add_inductive(two_ctor_enum("ReturnSpine"))
        .expect("valid enum should register");
    let rec_name = Name::from_string("ReturnSpine.rec");
    let ctor_name = Name::from_string("ReturnSpine.left");
    let malformed_type = Expr::app(
        Expr::const_(Name::from_string("ReturnSpine"), vec![]),
        Expr::type_(),
    );
    env.constructors
        .get_mut(&ctor_name)
        .expect("generated constructor")
        .type_ = malformed_type.clone();
    env.constants
        .get_mut(&ctor_name)
        .expect("generated constructor constant")
        .type_ = malformed_type;

    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("an overapplied constructor return must not expose only an index prefix");
    assert!(
        error.contains("return supplies 1 inductive arguments, expected 0"),
        "overapplied constructor return must report its exact arity, got {error}"
    );
}

/// `IhNat | zero | succ (n : IhNat)`: the smallest recursive family, so its
/// `succ` rule carries an induction-hypothesis argument.
fn recursive_nat(name: &str) -> InductiveDecl {
    let ind_name = Name::from_string(name);
    let ind = Expr::const_(ind_name.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind_name,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(&format!("{name}.zero")),
                    type_: ind.clone(),
                },
                Constructor {
                    name: Name::from_string(&format!("{name}.succ")),
                    type_: Expr::arrow(ind.clone(), ind),
                },
            ],
        }],
    }
}

/// Rebuild `rhs` (a lambda telescope over params, motive, minors and fields)
/// with the major premise of its induction hypothesis `I.rec … n` replaced by
/// the hypothesis's own second argument, the `zero` minor: `I.rec m z s z`.
fn with_ill_typed_ih_major(rhs: &Expr, rec_name: &Name) -> Expr {
    match rhs.kind() {
        ExprKind::Lam(binder, ty, body) => Expr::lam(
            *binder,
            ty.as_ref().clone(),
            with_ill_typed_ih_major(body, rec_name),
        ),
        ExprKind::App(f, ih) => {
            assert!(
                matches!(ih.get_app_fn().kind(), ExprKind::Const(n, _) if n == rec_name),
                "the succ rule's last argument must be the induction hypothesis, got {ih:?}"
            );
            let args = ih.get_app_args();
            assert_eq!(args.len(), 4, "IH is `rec motive zero succ n`, got {ih:?}");
            let forged = Expr::apps(
                ih.get_app_fn().clone(),
                [
                    args[0].clone(),
                    args[1].clone(),
                    args[2].clone(),
                    args[1].clone(),
                ],
            );
            Expr::app(f.as_ref().clone(), forged)
        }
        other => panic!("unexpected succ rule body {other:?}"),
    }
}

/// leanprover/lean4#15705 (and the stored-artifact shape of #14806): Lean's
/// `check_recursors` inferred a rule's reduct with `infer_only = true`, so an
/// induction-hypothesis argument of the wrong type was never checked, because
/// the minor's result type does not mention it. Here the `succ` rule's IH is
/// `IhNat.rec motive zero succ zero`: the major is the `zero` MINOR, of type
/// `motive IhNat.zero`, where an `IhNat` is required. Clean must refuse the
/// forged rule on each authority path a recursor record takes:
/// - import: `admit_imported_recursor` compares a stored record with the one the
///   kernel generates from the resident family (Lean's
///   `checkPostponedRecursors`);
/// - stamping: `validate_and_stamp_recursor` runs a FULL `check_type` of each
///   rule's reduct (the check upstream's `infer_only` skipped);
/// - read-only: `authenticate_recursor_readonly`, the same subject-reduction
///   check without the stamp.
/// The honest record is the control on every path.
#[test]
fn recursor_rule_with_ill_typed_ih_argument_is_refused() {
    let mut env = Environment::new();
    env.add_inductive(recursive_nat("IhNat"))
        .expect("valid recursive family should register");
    let rec_name = Name::from_string("IhNat.rec");
    let honest = env
        .get_recursor(&rec_name)
        .expect("generated recursor")
        .clone();
    assert_eq!(honest.rules.len(), 2);
    assert_eq!(
        honest.rules[1].constructor_name,
        Name::from_string("IhNat.succ")
    );
    let mut forged = honest.clone();
    forged.rules[1].rhs = with_ill_typed_ih_major(&honest.rules[1].rhs, &rec_name);
    assert_ne!(
        forged.rules[1].rhs, honest.rules[1].rhs,
        "subject: the forgery must differ"
    );

    // Import path.
    env.admit_imported_recursor(
        honest.clone(),
        &mut imported_family::GeneratedRecursorCache::new(),
    )
    .unwrap_or_else(|error| panic!("control: the honest record must be admitted: {error:?}"));
    let error = env
        .admit_imported_recursor(
            forged.clone(),
            &mut imported_family::GeneratedRecursorCache::new(),
        )
        .expect_err("a stored rule with an ill-typed IH must not be admitted");
    assert!(
        matches!(&error, EnvError::ImportedFamilyRecordMismatch { .. }),
        "the import refusal must be the family-record comparison, got {error:?}"
    );

    // Stamping and read-only paths, over the resident table.
    env.authenticate_recursor_readonly(&rec_name)
        .unwrap_or_else(|error| panic!("control: the honest rules must authenticate: {error}"));
    env.declaration_verification
        .insert(rec_name.clone(), DeclarationVerification::StructuralOnly);
    env.validate_and_stamp_recursor(&rec_name)
        .unwrap_or_else(|error| panic!("control: honest rules must validate: {error:?}"));

    *env.recursors
        .get_mut(&rec_name)
        .expect("generated recursor") = forged;
    env.declaration_verification
        .insert(rec_name.clone(), DeclarationVerification::StructuralOnly);
    let error = format!(
        "{:?}",
        env.validate_and_stamp_recursor(&rec_name)
            .expect_err("an ill-typed induction hypothesis must not earn full authority")
    );
    assert!(
        error.contains("rule 1") && error.contains("violates subject reduction"),
        "the stamping refusal must name the succ rule's subject-reduction check, got {error}"
    );
    assert_eq!(
        env.declaration_verification(&rec_name),
        Some(DeclarationVerification::StructuralOnly)
    );
    let error = env
        .authenticate_recursor_readonly(&rec_name)
        .expect_err("a forged rule must not authenticate");
    assert!(
        error.contains("rule 1") && error.contains("violates subject reduction"),
        "the read-only refusal must name the succ rule's subject-reduction check, got {error}"
    );
}

#[test]
fn test_recursor_preserves_constructor_field_binder_annotations() {
    let mut env = Environment::new();
    env.init_eq().expect("Eq");
    env.init_nat().expect("genuine Nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let dict_name = Name::from_string("BinderDict");
    let dict = Expr::const_(dict_name.clone(), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: dict_name,
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("BinderDict.mk"),
                type_: Expr::arrow(nat.clone(), dict.clone()),
            }],
        }],
    })
    .expect("checked dictionary family");
    let probe_name = Name::from_string("BinderProbe");
    let probe = Expr::const_(probe_name.clone(), vec![]);
    let at_n = Expr::app(probe.clone(), Expr::bvar(0));
    let mut constructors = Vec::new();
    let mut expected = Vec::new();
    for (name, binder) in [
        ("implicit", BinderInfo::Implicit),
        ("strict", BinderInfo::StrictImplicit),
        ("explicit", BinderInfo::Default),
    ] {
        constructors.push(Constructor {
            name: probe_name.clone().str(name),
            type_: Expr::pi(binder, nat.clone(), at_n.clone()),
        });
        expected.push(vec![binder]);
    }
    let eq_n = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat.clone(), Expr::bvar(0), Expr::bvar(0)],
    );
    constructors.push(Constructor {
        name: probe_name.clone().str("dependentExplicit"),
        type_: Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(
                BinderInfo::Default,
                eq_n,
                Expr::app(probe.clone(), Expr::bvar(1)),
            ),
        ),
    });
    expected.push(vec![BinderInfo::Default, BinderInfo::Default]);
    constructors.push(Constructor {
        name: probe_name.clone().str("instance"),
        type_: Expr::pi(
            BinderInfo::InstImplicit,
            dict,
            Expr::app(probe, Expr::const_(Name::from_string("Nat.zero"), vec![])),
        ),
    });
    expected.push(vec![BinderInfo::InstImplicit]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: probe_name,
            type_: Expr::arrow(nat, Expr::type_()),
            constructors,
        }],
    })
    .expect("checked indexed family");
    let rec = env
        .get_recursor(&Name::from_string("BinderProbe.rec"))
        .expect("generated recursor");
    let mut cursor = &rec.type_;
    let ExprKind::Pi(motive, _, body) = &cursor.kind else {
        panic!("motive binder");
    };
    assert_eq!(motive.info, BinderInfo::Implicit);
    cursor = body;
    for field_infos in &expected {
        let ExprKind::Pi(_, minor, body) = &cursor.kind else {
            panic!("minor binder");
        };
        let mut field_cursor = &**minor;
        for expected in field_infos {
            let ExprKind::Pi(binder, _, body) = &field_cursor.kind else {
                panic!("constructor field binder");
            };
            assert_eq!(binder.info, *expected);
            field_cursor = body;
        }
        cursor = body;
    }
    for (rule, field_infos) in rec.rules.iter().zip(expected) {
        let mut cursor = &rule.rhs;
        for _ in 0..rec.num_params + rec.num_motives + rec.num_minors {
            let ExprKind::Lam(binder, _, body) = &cursor.kind else {
                panic!("rule prefix lambda");
            };
            assert_eq!(binder.info, BinderInfo::Default);
            cursor = body;
        }
        for expected in field_infos {
            let ExprKind::Lam(binder, _, body) = &cursor.kind else {
                panic!("rule field lambda");
            };
            assert_eq!(binder.info, expected);
            cursor = body;
        }
    }
}

#[test]
fn empty_recursor_motives_remain_explicit_in_every_eliminator_order() {
    let mut env = Environment::with_prelude();
    for name in ["Nat.rec", "Nat.casesOn", "Nat.recOn"] {
        let name = Name::from_string(name);
        let constant = env.get_const(&name).expect("nonempty control eliminator");
        let ExprKind::Pi(motive, _, _) = constant.type_.kind() else {
            panic!("nonempty motive binder");
        };
        assert_eq!(motive.info, BinderInfo::Implicit, "{name}");
    }
    for (name, type_) in [
        ("EmptyMotiveProp", Expr::prop()),
        ("EmptyMotiveType", Expr::type_()),
    ] {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(name),
                type_,
                constructors: vec![],
            }],
        })
        .expect("checked empty family");
        for suffix in ["rec", "casesOn", "recOn"] {
            let name = Name::from_string(name).str(suffix);
            let constant = env.get_const(&name).expect("generated eliminator");
            let ExprKind::Pi(motive, _, body) = constant.type_.kind() else {
                panic!("motive binder");
            };
            assert_eq!(motive.info, BinderInfo::Default, "{name}");
            let ExprKind::Pi(major, _, _) = body.kind() else {
                panic!("major binder");
            };
            assert_eq!(major.info, BinderInfo::Default, "{name}");
            assert_eq!(
                env.declaration_verification(&name),
                Some(DeclarationVerification::FullKernelCheck),
                "{name}"
            );
        }
    }
}
