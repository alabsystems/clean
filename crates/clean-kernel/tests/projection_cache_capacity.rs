// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Projection results must survive eviction during the same telescope walk.

use clean_kernel::cert::CertVerifier;
use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn field_structure(proofs: bool, field_count: u32) -> (Environment, Name, Expr, Expr) {
    let mut env = Environment::new();
    env.init_nat().expect("admit the actual Nat declarations");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("CacheProof"),
            type_: Expr::prop(),
            constructors: vec![Constructor {
                name: Name::from_string("CacheProof.intro"),
                type_: const_expr("CacheProof"),
            }],
        }],
    })
    .expect("admit the inhabited proposition for the positive control");

    let name = if proofs {
        "ProofCacheFields"
    } else {
        "DataCacheFields"
    };
    let struct_name = Name::from_string(name);
    let field_type = const_expr(if proofs { "CacheProof" } else { "Nat" });
    let mut ctor_type = const_expr(name);
    for _ in 0..field_count {
        ctor_type = Expr::pi(BinderInfo::Default, field_type.clone(), ctor_type);
    }
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: if proofs { Expr::prop() } else { Expr::type_() },
            constructors: vec![Constructor {
                name: Name::from_string(&format!("{name}.mk")),
                type_: ctor_type,
            }],
        }],
    })
    .expect("admit the actual structure and constructor");
    let mut inner = const_expr(&format!("{name}.mk"));
    for index in 0..field_count {
        let field = if proofs {
            const_expr("CacheProof.intro")
        } else {
            Expr::nat_lit(7 + u64::from(index))
        };
        inner = Expr::app(inner, field);
    }
    assert_eq!(
        TypeChecker::new(&env)
            .infer_type_full(&inner)
            .expect("the actual constructor application must fully type-check"),
        const_expr(name)
    );
    (env, struct_name, inner, field_type)
}

fn assert_capacity_invariant(capacity: usize, proofs: bool) {
    // trim_if_needed runs before each insert and slides only when len > cap.
    // Evict field0 from BOTH generations before lookup: cap0 needs3 fields,
    // cap1 needs5. Three fields at cap1 would not exercise the reported bug.
    let field_count = u32::try_from(2 * (capacity + 1) + 1)
        .expect("the fixed tiny capacities fit the projection index type");
    let (env, struct_name, inner, field_type) = field_structure(proofs, field_count);
    let projections = (0..field_count)
        .map(|index| Expr::proj(struct_name.clone(), index, inner.clone()))
        .collect::<Vec<_>>();
    let baseline_tc = TypeChecker::new(&env);
    let baseline = projections
        .iter()
        .map(|projection| {
            let ty = baseline_tc
                .infer_type(projection)
                .expect("the default-capacity projection must succeed");
            assert_eq!(ty, field_type);
            ty
        })
        .collect::<Vec<_>>();

    let ascending = (0..projections.len()).collect::<Vec<_>>();
    let descending = (0..projections.len()).rev().collect::<Vec<_>>();
    for (first, second) in [(&ascending, &descending), (&descending, &ascending)] {
        let mut public_tc = TypeChecker::new(&env);
        let mut cert_tc = TypeChecker::new(&env);
        // The public setter stores this exact capacity; there is no minimum
        // clamp. A performance setting must not invent an out-of-bounds index.
        public_tc.set_max_cache_entries(capacity);
        cert_tc.set_max_cache_entries(capacity);
        for &index in first.iter().chain(second.iter()).chain(first.iter()) {
            let ty = public_tc
                .infer_type(&projections[index])
                .unwrap_or_else(|error| {
                    panic!("capacity {capacity}, proofs={proofs}, index {index}: {error:?}")
                });
            assert_eq!(ty, baseline[index]);
            let (cert_type, cert) = cert_tc
                .infer_type_with_cert(&projections[index])
                .expect("certificate-producing inference must also survive eviction");
            assert_eq!(cert_type, baseline[index]);
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(&cert, &projections[index])
                    .expect("the returned certificate must independently verify"),
                baseline[index]
            );
        }
    }
}

#[test]
fn non_prop_projection_survives_zero_capacity_eviction() {
    assert_capacity_invariant(0, false);
}

#[test]
fn non_prop_projection_survives_one_capacity_eviction() {
    assert_capacity_invariant(1, false);
}

#[test]
fn prop_projection_survives_zero_capacity_eviction() {
    assert_capacity_invariant(0, true);
}

#[test]
fn prop_projection_survives_one_capacity_eviction() {
    assert_capacity_invariant(1, true);
}

fn dependent_field_structure(field_count: usize) -> (Environment, Name, Expr) {
    // Reuse the actually admitted inhabited proposition, not an assumed field
    // witness. The original structure also remains independently well typed.
    let (mut env, _, _, _) = field_structure(true, 3);
    let struct_name = Name::from_string("DependentCacheFields");
    let mut domains = vec![
        // P : Prop; h : P; f : P -> P, each in its preceding field context.
        Expr::prop(),
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
    ];
    domains.resize(field_count, const_expr("Nat"));
    let ctor_type = domains
        .into_iter()
        .rev()
        .fold(const_expr("DependentCacheFields"), |body, domain| {
            Expr::pi(BinderInfo::Default, domain, body)
        });
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: struct_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("DependentCacheFields.mk"),
                type_: ctor_type,
            }],
        }],
    })
    .expect("admit the actual dependent constructor telescope");
    let mut inner = Expr::app(
        Expr::app(
            Expr::app(
                const_expr("DependentCacheFields.mk"),
                const_expr("CacheProof"),
            ),
            const_expr("CacheProof.intro"),
        ),
        Expr::lam(BinderInfo::Default, const_expr("CacheProof"), Expr::bvar(0)),
    );
    for index in 3..field_count {
        inner = Expr::app(
            inner,
            Expr::nat_lit(u64::try_from(index).expect("the tiny fixture index fits u64")),
        );
    }
    assert_eq!(
        TypeChecker::new(&env)
            .infer_type_full(&inner)
            .expect("the actual dependent constructor application must fully type-check"),
        const_expr("DependentCacheFields")
    );
    (env, struct_name, inner)
}

fn assert_dependent_capacity_invariant(capacity: usize) {
    // Evict even field2, whose function type depends on field0 across the
    // unused field1 binder. Five fields at cap0 and seven at cap1 outlive both
    // sliding generations for every dependent target, not just field0.
    let field_count = 3 + 2 * (capacity + 1);
    let (env, struct_name, inner) = dependent_field_structure(field_count);
    let projections = (0..field_count)
        .map(|index| {
            Expr::proj(
                struct_name.clone(),
                u32::try_from(index).expect("the tiny fixture index fits u32"),
                inner.clone(),
            )
        })
        .collect::<Vec<_>>();
    // Handwritten expected types pin both the selected domain and substitution
    // by the actual earlier projection. Agreement with a default-capacity
    // implementation alone would not detect a shared wrong-field mistake.
    let mut expected = vec![
        Expr::prop(),
        projections[0].clone(),
        Expr::pi(
            BinderInfo::Default,
            projections[0].clone(),
            projections[0].clone(),
        ),
    ];
    expected.resize(field_count, const_expr("Nat"));
    let baseline_tc = TypeChecker::new(&env);
    for (projection, ty) in projections.iter().zip(&expected) {
        assert_eq!(
            baseline_tc
                .infer_type(projection)
                .expect("the default-capacity dependent projection must succeed"),
            *ty
        );
    }

    // Start from each dependent target in a fresh checker, so prior projection
    // or infer-type cache hits cannot hide eviction during its first walk.
    for target in 0..3 {
        let mut public_tc = TypeChecker::new(&env);
        let mut cert_tc = TypeChecker::new(&env);
        public_tc.set_max_cache_entries(capacity);
        cert_tc.set_max_cache_entries(capacity);
        let order = std::iter::once(target)
            .chain(0..field_count)
            .chain((0..field_count).rev())
            .chain(std::iter::once(target));
        for index in order {
            assert_eq!(
                public_tc
                    .infer_type(&projections[index])
                    .unwrap_or_else(|error| {
                        panic!("dependent capacity {capacity}, index {index}: {error:?}")
                    }),
                expected[index]
            );
            let (ty, cert) = cert_tc
                .infer_type_with_cert(&projections[index])
                .expect("dependent certificate generation must survive eviction");
            assert_eq!(ty, expected[index]);
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(&cert, &projections[index])
                    .expect("independently derive the selected dependent field type"),
                expected[index]
            );
        }
    }
}

#[test]
fn dependent_projection_types_survive_zero_capacity_eviction() {
    assert_dependent_capacity_invariant(0);
}

#[test]
fn dependent_projection_types_survive_one_capacity_eviction() {
    assert_dependent_capacity_invariant(1);
}
