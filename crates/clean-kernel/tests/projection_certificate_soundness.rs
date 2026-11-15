// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Projection certificates must enforce the same Prop-elimination restriction
//! as strict projection inference, even when the inner certificate is genuine.

use clean_kernel::cert::{CertVerifier, ProofCert};
use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::{TypeChecker, TypeError};
use std::sync::Arc;

fn structure_with_nat_field(name: &str, in_prop: bool) -> (Environment, Name, Expr) {
    let mut env = Environment::new();
    env.init_nat()
        .expect("the actual Nat declarations must be admitted");
    let struct_name = Name::from_string(name);
    let ctor_name = Name::from_string(&format!("{name}.mk"));
    let struct_type = Expr::const_(struct_name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: if in_prop { Expr::prop() } else { Expr::type_() },
            constructors: vec![Constructor {
                name: ctor_name.clone(),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::const_(Name::from_string("Nat"), vec![]),
                    struct_type,
                ),
            }],
        }],
    })
    .expect("the structure and its constructor must be admitted");
    let inner = Expr::app(Expr::const_(ctor_name, vec![]), Expr::nat_lit(7));
    (env, struct_name, inner)
}

#[test]
fn certificate_rejects_non_prop_field_of_prop_structure() {
    let (env, struct_name, inner) = structure_with_nat_field("PropWithDataCert", true);
    let tc = TypeChecker::new(&env);
    let (inner_type, inner_cert) = tc
        .infer_type_with_cert(&inner)
        .expect("the actual constructor application must be well typed");
    assert_eq!(inner_type, Expr::const_(struct_name.clone(), vec![]));
    let mut inner_verifier = CertVerifier::new(&env);
    assert_eq!(
        inner_verifier
            .verify(&inner_cert, &inner)
            .expect("the genuine inner certificate must verify"),
        inner_type
    );

    let projection = Expr::proj(struct_name.clone(), 0, inner);
    let strict_result = tc.infer_type_with_cert(&projection);
    assert!(
        matches!(
            strict_result,
            Err(TypeError::InvalidProjFromProp { field_idx: 0 })
        ),
        "strict inference must reject Prop-to-Nat projection: {strict_result:?}"
    );
    assert!(matches!(
        TypeChecker::new(&env).infer_type(&projection),
        Err(TypeError::InvalidProjFromProp { field_idx: 0 })
    ));

    // The only manually supplied rule is the forbidden projection. Its inner
    // certificate, inner type, and stored field type are all genuine; rejecting
    // an arbitrary forged field-type claim is not enough to cover this case.
    let cert = ProofCert::Proj {
        struct_name,
        idx: 0,
        expr_cert: Arc::new(inner_cert),
        expr_type: Box::new(inner_type),
        field_type: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };
    let mut verifier = CertVerifier::new(&env);
    let result = verifier.verify(&cert, &projection);
    assert!(
        result.is_err(),
        "certificate verification must reject the same forbidden projection; got {result:?}"
    );
}

#[test]
fn certificate_accepts_nat_field_of_non_prop_structure() {
    let (env, struct_name, inner) = structure_with_nat_field("DataWithNatCert", false);
    let projection = Expr::proj(struct_name, 0, inner);
    let tc = TypeChecker::new(&env);
    let (field_type, cert) = tc
        .infer_type_with_cert(&projection)
        .expect("ordinary data projection must remain accepted");
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    assert_eq!(field_type, nat_type);
    assert_eq!(
        TypeChecker::new(&env).infer_type(&projection).unwrap(),
        nat_type
    );
    let mut verifier = CertVerifier::new(&env);
    assert_eq!(
        verifier
            .verify(&cert, &projection)
            .expect("the valid projection certificate must verify"),
        nat_type
    );
}

fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn projection_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("admit Nat");
    env.init_eq().expect("admit Eq");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("ProjectionCertTrue"),
            type_: Expr::prop(),
            constructors: vec![Constructor {
                name: Name::from_string("ProjectionCertTrue.intro"),
                type_: const_expr("ProjectionCertTrue"),
            }],
        }],
    })
    .expect("admit the inhabited proposition used by the controls");
    env
}

/// Field domains are expressed in the context of their preceding fields.
fn add_prop_structure(env: &mut Environment, name: &str, fields: Vec<Expr>) -> Name {
    let struct_name = Name::from_string(name);
    let ctor_type = fields.into_iter().rev().fold(const_expr(name), |body, ty| {
        Expr::pi(BinderInfo::Default, ty, body)
    });
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::prop(),
            constructors: vec![Constructor {
                name: Name::from_string(&format!("{name}.mk")),
                type_: ctor_type,
            }],
        }],
    })
    .expect("admit the actual Prop structure and constructor");
    struct_name
}

fn constructor_app(name: &str, arguments: Vec<Expr>) -> Expr {
    arguments
        .into_iter()
        .fold(const_expr(&format!("{name}.mk")), Expr::app)
}

fn genuine_inner(env: &Environment, inner: &Expr) -> (Expr, ProofCert) {
    let tc = TypeChecker::new(env);
    let checked_type = tc
        .infer_type_full(inner)
        .expect("the inner term must pass full App/domain checking");
    let (inner_type, inner_cert) = tc
        .infer_type_with_cert(inner)
        .expect("generate the actual inner certificate");
    assert_eq!(inner_type, checked_type);
    let mut verifier = CertVerifier::new(env);
    assert_eq!(
        verifier
            .verify(&inner_cert, inner)
            .expect("independently verify the genuine inner certificate"),
        inner_type
    );
    (inner_type, inner_cert)
}

fn assert_projection_accepts(
    env: &Environment,
    tc: &TypeChecker<'_>,
    projection: &Expr,
    expected_type: &Expr,
) {
    // Use a fresh checker so certificate generation cannot prefill the cache.
    // In release builds these calls exercise the production fast inference path.
    let public_tc = TypeChecker::new(env);
    for _ in 0..2 {
        let actual = public_tc
            .infer_type(projection)
            .expect("public inference must accept on first and repeated lookup");
        assert!(public_tc.is_def_eq(&actual, expected_type));
    }
    let (field_type, cert) = tc
        .infer_type_with_cert(projection)
        .expect("strict projection inference must accept the permitted field");
    assert!(tc.is_def_eq(&field_type, expected_type));
    let mut verifier = CertVerifier::new(env);
    assert_eq!(
        verifier
            .verify(&cert, projection)
            .expect("the permitted projection certificate must verify"),
        field_type
    );
}

fn assert_projection_rejects(
    env: &Environment,
    struct_name: Name,
    idx: u32,
    inner: Expr,
    field_type: Expr,
    rejected_field: u32,
) {
    let (inner_type, inner_cert) = genuine_inner(env, &inner);
    let projection = Expr::proj(struct_name.clone(), idx, inner);
    let public_result = TypeChecker::new(env).infer_type(&projection);
    assert!(
        matches!(public_result, Err(TypeError::InvalidProjFromProp { field_idx })
            if field_idx == rejected_field),
        "public inference must also reject this projection: {public_result:?}"
    );
    let tc = TypeChecker::new(env);
    let strict = tc.infer_type_with_cert(&projection);
    assert!(
        matches!(strict, Err(TypeError::InvalidProjFromProp { field_idx })
            if field_idx == rejected_field),
        "expected the actual Prop-elimination refusal at field {rejected_field}, got {strict:?}"
    );
    let cert = ProofCert::Proj {
        struct_name,
        idx,
        expr_cert: Arc::new(inner_cert),
        expr_type: Box::new(inner_type),
        field_type: Box::new(field_type),
    };
    let mut verifier = CertVerifier::new(env);
    assert!(
        verifier.verify(&cert, &projection).is_err(),
        "a correct claimed domain cannot authorize forbidden Prop elimination"
    );
}

fn eq_nat(left: Expr, right: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                const_expr("Nat"),
            ),
            left,
        ),
        right,
    )
}

#[test]
fn certificate_accepts_independent_prop_field_after_nat_field() {
    let mut env = projection_env();
    let name = "NatThenProofCert";
    let struct_name = add_prop_structure(
        &mut env,
        name,
        vec![const_expr("Nat"), const_expr("ProjectionCertTrue")],
    );
    let inner = constructor_app(
        name,
        vec![Expr::nat_lit(7), const_expr("ProjectionCertTrue.intro")],
    );
    let _ = genuine_inner(&env, &inner);
    let projection = Expr::proj(struct_name.clone(), 1, inner.clone());
    let tc = TypeChecker::new(&env);
    assert_projection_accepts(&env, &tc, &projection, &const_expr("ProjectionCertTrue"));
    // Skipping the unrelated first domain must not cache it as a valid target.
    assert!(matches!(
        tc.infer_type_with_cert(&Expr::proj(struct_name, 0, inner)),
        Err(TypeError::InvalidProjFromProp { field_idx: 0 })
    ));
}

#[test]
fn certificate_accepts_prop_field_before_nat_on_first_and_repeated_lookup() {
    let mut env = projection_env();
    let name = "ProofThenNatCert";
    let struct_name = add_prop_structure(
        &mut env,
        name,
        vec![const_expr("ProjectionCertTrue"), const_expr("Nat")],
    );
    let inner = constructor_app(
        name,
        vec![const_expr("ProjectionCertTrue.intro"), Expr::nat_lit(7)],
    );
    let _ = genuine_inner(&env, &inner);
    let projection = Expr::proj(struct_name.clone(), 0, inner.clone());
    let tc = TypeChecker::new(&env);
    // Both calls must succeed: an error after filling a valid prefix is not a
    // substitute for returning the requested permitted projection correctly.
    for _ in 0..2 {
        assert_projection_accepts(&env, &tc, &projection, &const_expr("ProjectionCertTrue"));
    }
    assert!(matches!(
        tc.infer_type_with_cert(&Expr::proj(struct_name, 1, inner)),
        Err(TypeError::InvalidProjFromProp { field_idx: 1 })
    ));
}

#[test]
fn certificate_rejects_prop_field_depending_on_forbidden_nat_projection() {
    let mut env = projection_env();
    let name = "DependentNatProofCert";
    let struct_name = add_prop_structure(
        &mut env,
        name,
        vec![const_expr("Nat"), eq_nat(Expr::bvar(0), Expr::bvar(0))],
    );
    let seven = Expr::nat_lit(7);
    let refl = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            const_expr("Nat"),
        ),
        seven.clone(),
    );
    let inner = constructor_app(name, vec![seven, refl]);
    let prior_projection = Expr::proj(struct_name.clone(), 0, inner.clone());
    assert_projection_rejects(
        &env,
        struct_name,
        1,
        inner,
        eq_nat(prior_projection.clone(), prior_projection),
        0,
    );
}

#[test]
fn certificate_accepts_forall_nat_prop_field() {
    let mut env = projection_env();
    let name = "ForallProofCert";
    let field_type = Expr::pi(
        BinderInfo::Default,
        const_expr("Nat"),
        const_expr("ProjectionCertTrue"),
    );
    let struct_name = add_prop_structure(&mut env, name, vec![field_type.clone()]);
    let proof = Expr::lam(
        BinderInfo::Default,
        const_expr("Nat"),
        const_expr("ProjectionCertTrue.intro"),
    );
    let inner = constructor_app(name, vec![proof]);
    let _ = genuine_inner(&env, &inner);
    let projection = Expr::proj(struct_name, 0, inner);
    let tc = TypeChecker::new(&env);
    assert_projection_accepts(&env, &tc, &projection, &field_type);
}

#[test]
fn certificate_rejects_prop_sort_as_a_field_type() {
    let mut env = projection_env();
    let name = "PropositionDataCert";
    let struct_name = add_prop_structure(&mut env, name, vec![Expr::prop()]);
    let inner = constructor_app(name, vec![const_expr("ProjectionCertTrue")]);
    // The field is a proposition, not a proof: Prop : Type, never Prop : Prop.
    assert_projection_rejects(&env, struct_name, 0, inner, Expr::prop(), 0);
}

fn add_proof_box(env: &mut Environment) -> Name {
    let name = Name::from_string("ContextProofBox");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            constructors: vec![Constructor {
                name: Name::from_string("ContextProofBox.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(0),
                        Expr::app(const_expr("ContextProofBox"), Expr::bvar(1)),
                    ),
                ),
            }],
        }],
    })
    .expect("admit ContextProofBox (P : Prop) with one field of type P");
    name
}

#[test]
fn certificate_accepts_prop_projection_under_lambda_binders() {
    let mut env = projection_env();
    let struct_name = add_proof_box(&mut env);
    // fun (P : Prop) (p : ContextProofBox P) => p.0
    // The field's Prop classification must use the actual binder context.
    let term = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(const_expr("ContextProofBox"), Expr::bvar(0)),
            Expr::proj(struct_name, 0, Expr::bvar(0)),
        ),
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(const_expr("ContextProofBox"), Expr::bvar(0)),
            Expr::bvar(1),
        ),
    );
    let (actual, _) = genuine_inner(&env, &term);
    assert_eq!(actual, expected);
}

#[test]
fn certificate_projection_equality_uses_equality_engines_nested_binders() {
    let mut env = projection_env();
    let struct_name = add_proof_box(&mut env);
    // The genuine term proves Eq P h h. Conversion changes only the first
    // proof argument to p.0, which is definitionally equal by proof irrelevance.
    let term = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(const_expr("ContextProofBox"), Expr::bvar(0)),
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq.refl"), vec![Level::zero()]),
                        Expr::bvar(2),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(const_expr("ContextProofBox"), Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
                            Expr::bvar(2),
                        ),
                        Expr::proj(struct_name, 0, Expr::bvar(1)),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    );
    let (actual, inner) = genuine_inner(&env, &term);
    assert_ne!(actual, expected, "this must exercise a real conversion");
    TypeChecker::new(&env)
        .check_type(&term, &expected)
        .expect("the actual kernel must accept the proof-irrelevant conversion");
    let cert = ProofCert::DefEq {
        inner: Arc::new(inner),
        expected_type: Box::new(expected.clone()),
        actual_type: Box::new(actual),
        eq_steps: vec![],
    };
    // This verifier starts with NO local binders. The equality engine itself
    // introduces P, p, h while comparing the two Pi types. Resetting that
    // context to self.context when typing p.0 must not be an unnoticed shortcut.
    let mut verifier = CertVerifier::new(&env);
    assert_eq!(
        verifier
            .verify(&cert, &term)
            .expect("projection inference must retain equality-engine binders"),
        expected
    );
}

#[test]
fn certificate_accepts_contextual_prop_field_after_unused_nat() {
    let mut env = projection_env();
    let struct_name = Name::from_string("ContextNatProofBox");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            constructors: vec![Constructor {
                name: Name::from_string("ContextNatProofBox.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::pi(
                        BinderInfo::Default,
                        const_expr("Nat"),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(1),
                            Expr::app(const_expr("ContextNatProofBox"), Expr::bvar(2)),
                        ),
                    ),
                ),
            }],
        }],
    })
    .expect("admit ContextNatProofBox (P : Prop) with independent Nat and P fields");
    // fun (P : Prop) (s : ContextNatProofBox P) => s.1
    // After substituting P, the first field's body still contains OUTER
    // BVars, but not its own bvar0. It must skip Nat and lower those outer
    // indices, rather than mistake has_loose_bvars() for dependency on Nat.
    let term = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(const_expr("ContextNatProofBox"), Expr::bvar(0)),
            Expr::proj(struct_name, 1, Expr::bvar(0)),
        ),
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(const_expr("ContextNatProofBox"), Expr::bvar(0)),
            Expr::bvar(1),
        ),
    );
    let (actual, _) = genuine_inner(&env, &term);
    assert_eq!(actual, expected);
}
