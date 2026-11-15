// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rebinding must preserve DAG sharing without reusing a different binder's result.
//! Structural fixtures below test the transformation, not certificate validity.
//! The inference/replay controls use closed terms in an empty environment.

use super::{convert_fvar_cert_to_bvar, RebindContext};
use crate::cert::{CertVerifier, DefEqStep, ProofCert, ZFCSetCertKind};
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, FVarId, Literal, MDataValue};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::collections::HashSet;
use std::sync::Arc;

fn fvar_cert(id: FVarId, ty: Expr) -> Arc<ProofCert> {
    Arc::new(ProofCert::FVar {
        id,
        type_: Box::new(ty),
    })
}

fn bvar_cert(idx: u32, ty: Expr) -> Arc<ProofCert> {
    Arc::new(ProofCert::BVar {
        idx,
        expected_type: Box::new(ty),
    })
}

fn app_cert(left: Arc<ProofCert>, right: Arc<ProofCert>, ty: Expr) -> ProofCert {
    ProofCert::App {
        fn_cert: left,
        fn_type: Box::new(ty.clone()),
        arg_cert: right,
        result_type: Box::new(ty),
    }
}

// No structural hashing, equality, serialization or expanded-tree traversal.
// This helper deliberately refuses variants outside these growth fixtures.
pub(super) fn core_allocations(root: &ProofCert) -> usize {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    while let Some(cert) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(cert)) {
            continue;
        }
        match cert {
            ProofCert::App {
                fn_cert, arg_cert, ..
            } => {
                pending.extend([fn_cert.as_ref(), arg_cert.as_ref()]);
            }
            ProofCert::Lam {
                arg_type_cert,
                body_cert,
                ..
            } => {
                pending.extend([arg_type_cert.as_ref(), body_cert.as_ref()]);
            }
            ProofCert::Pi {
                arg_type_cert,
                body_type_cert,
                ..
            } => {
                pending.extend([arg_type_cert.as_ref(), body_type_cert.as_ref()]);
            }
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                ..
            } => {
                pending.extend([type_cert.as_ref(), value_cert.as_ref(), body_cert.as_ref()]);
            }
            ProofCert::Sort { .. } | ProofCert::FVar { .. } | ProofCert::BVar { .. } => {}
            other => panic!("unexpected growth-fixture certificate {other:?}"),
        }
    }
    seen.len()
}

#[test]
fn rebind_shared_certificate_depth_24_stays_a_dag() {
    let id = FVarId(53);
    let mut input = fvar_cert(id, Expr::fvar(id));
    for _ in 0..24 {
        input = Arc::new(app_cert(input.clone(), input.clone(), Expr::fvar(id)));
    }
    assert_eq!(core_allocations(&input), 25);
    let output = convert_fvar_cert_to_bvar(input.as_ref().clone(), id, 0);
    assert_eq!(core_allocations(&output), 25);
    let mut node = &output;
    for _ in 0..24 {
        let ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } = node
        else {
            panic!("missing shared application");
        };
        assert!(Arc::ptr_eq(fn_cert, arg_cert));
        assert_eq!(fn_type.as_ref(), &Expr::bvar(0));
        assert_eq!(result_type.as_ref(), &Expr::bvar(0));
        node = fn_cert;
    }
    assert_eq!(node, bvar_cert(0, Expr::bvar(0)).as_ref());
    // The conversion borrows the input graph; it must not mutate its leaves.
    let mut original = input.as_ref();
    for _ in 0..24 {
        let ProofCert::App { fn_cert, .. } = original else {
            panic!("input changed")
        };
        original = fn_cert;
    }
    assert_eq!(original, fvar_cert(id, Expr::fvar(id)).as_ref());
}

#[test]
fn rebind_shared_node_separates_binder_depths_and_shares_equal_depths() {
    let id = FVarId(53);
    let shared = fvar_cert(id, Expr::fvar(id));
    let binder = Arc::new(ProofCert::Lam {
        binder_info: BinderInfo::Implicit,
        arg_type_cert: shared.clone(),
        body_cert: shared.clone(),
        result_type: Box::new(Expr::fvar(id)),
    });
    let input = app_cert(shared, binder, Expr::fvar(id));
    let output = convert_fvar_cert_to_bvar(input, id, 0);
    let ProofCert::App {
        fn_cert, arg_cert, ..
    } = &output
    else {
        panic!("App")
    };
    let ProofCert::Lam {
        binder_info,
        arg_type_cert,
        body_cert,
        result_type,
    } = arg_cert.as_ref()
    else {
        panic!("Lam")
    };
    assert_eq!(*binder_info, BinderInfo::Implicit);
    assert!(Arc::ptr_eq(fn_cert, arg_type_cert));
    assert!(!Arc::ptr_eq(fn_cert, body_cert));
    assert_eq!(fn_cert.as_ref(), bvar_cert(0, Expr::bvar(0)).as_ref());
    assert_eq!(body_cert.as_ref(), bvar_cert(1, Expr::bvar(1)).as_ref());
    assert_eq!(result_type.as_ref(), &Expr::bvar(0));
}

#[test]
fn rebind_absent_fvar_still_shifts_bvars_and_all_leaf_type_fields() {
    let id = FVarId(53);
    let ty = Expr::app(Expr::bvar(0), Expr::bvar(2));
    let expected = Expr::app(Expr::bvar(0), Expr::bvar(3));
    for idx in 0..=3 {
        let input = bvar_cert(idx, ty.clone());
        let output = convert_fvar_cert_to_bvar(input.as_ref().clone(), id, 1);
        assert_eq!(
            output,
            *bvar_cert(if idx >= 1 { idx + 1 } else { idx }, expected.clone())
        );
    }
    let other = FVarId(54);
    let input = ProofCert::FVar {
        id: other,
        type_: Box::new(ty.clone()),
    };
    let output = convert_fvar_cert_to_bvar(input, id, 1);
    assert_eq!(
        output,
        ProofCert::FVar {
            id: other,
            type_: Box::new(expected.clone())
        }
    );
    let name = Name::from_string("structuralType");
    let levels = vec![Level::succ(Level::zero())];
    let input = ProofCert::Const {
        name: name.clone(),
        levels: levels.clone(),
        type_: Box::new(ty.clone()),
    };
    let output = convert_fvar_cert_to_bvar(input, id, 1);
    assert_eq!(
        output,
        ProofCert::Const {
            name,
            levels,
            type_: Box::new(expected.clone())
        }
    );
    let input = ProofCert::Lit {
        lit: Literal::nat(17),
        type_: Box::new(ty),
    };
    let output = convert_fvar_cert_to_bvar(input, id, 1);
    assert_eq!(
        output,
        ProofCert::Lit {
            lit: Literal::nat(17),
            type_: Box::new(expected)
        }
    );
}

#[test]
fn rebind_memo_is_local_to_the_target_fvar() {
    let first = FVarId(53);
    let second = FVarId(54);
    let leaf = fvar_cert(first, Expr::fvar(second));
    let input = app_cert(leaf.clone(), leaf, Expr::fvar(first));
    let a = convert_fvar_cert_to_bvar(input.clone(), first, 0);
    let b = convert_fvar_cert_to_bvar(input.clone(), second, 0);
    let c = convert_fvar_cert_to_bvar(input, first, 0);
    assert_eq!(a, c);
    let ProofCert::App {
        fn_cert: a_leaf, ..
    } = &a
    else {
        panic!("App")
    };
    let ProofCert::App {
        fn_cert: b_leaf, ..
    } = &b
    else {
        panic!("App")
    };
    assert_eq!(a_leaf.as_ref(), bvar_cert(0, Expr::fvar(second)).as_ref());
    assert_eq!(b_leaf.as_ref(), fvar_cert(first, Expr::bvar(0)).as_ref());
}

// Each immediate child appears at its rule's original depth, or under exactly
// one binder. Supplying independent expected leaves/type expressions tests the
// full rule matrix without calling the production abstraction to build targets.
fn shallow_rule_matrix(zero: Arc<ProofCert>, one: Arc<ProofCert>, ty: Expr) -> Vec<ProofCert> {
    let t = || Box::new(ty.clone());
    let level = Level::succ(Level::zero());
    let mut cases = vec![
        ProofCert::Sort {
            level: level.clone(),
        },
        ProofCert::CubicalInterval,
        ProofCert::CubicalEndpoint { is_one: true },
        ProofCert::SProp,
        ProofCert::Lam {
            binder_info: BinderInfo::Implicit,
            arg_type_cert: zero.clone(),
            body_cert: one.clone(),
            result_type: t(),
        },
        ProofCert::Pi {
            binder_info: BinderInfo::Default,
            arg_type_cert: zero.clone(),
            arg_level: level.clone(),
            body_type_cert: one.clone(),
            body_level: Level::zero(),
        },
        ProofCert::Let {
            type_cert: zero.clone(),
            value_cert: zero.clone(),
            body_cert: one.clone(),
            result_type: t(),
        },
        app_cert(zero.clone(), zero.clone(), ty.clone()),
        ProofCert::DefEq {
            inner: zero.clone(),
            expected_type: t(),
            actual_type: t(),
            eq_steps: vec![DefEqStep::Symm(Box::new(DefEqStep::Beta))],
        },
        ProofCert::MData {
            metadata: vec![(Name::from_string("retainedMetadata"), MDataValue::Nat(17))],
            inner_cert: zero.clone(),
            result_type: t(),
        },
        ProofCert::Proj {
            struct_name: Name::from_string("structuralProjection"),
            idx: 7,
            expr_cert: zero.clone(),
            expr_type: t(),
            field_type: t(),
        },
        ProofCert::CubicalPath {
            ty_cert: zero.clone(),
            ty_level: level,
            left_cert: zero.clone(),
            right_cert: zero.clone(),
        },
        ProofCert::CubicalPathLam {
            body_cert: one.clone(),
            body_type: t(),
            result_type: t(),
        },
        ProofCert::CubicalPathApp {
            path_cert: zero.clone(),
            arg_cert: zero.clone(),
            path_type: t(),
            result_type: t(),
        },
        ProofCert::CubicalHComp {
            ty_cert: zero.clone(),
            phi_cert: zero.clone(),
            u_cert: zero.clone(),
            base_cert: zero.clone(),
            result_type: t(),
        },
        ProofCert::CubicalTransp {
            ty_cert: zero.clone(),
            phi_cert: zero.clone(),
            base_cert: zero.clone(),
            result_type: t(),
        },
        ProofCert::CubicalCoe {
            ty_cert: zero.clone(),
            r_cert: zero.clone(),
            s_cert: zero.clone(),
            base_cert: zero.clone(),
            result_type: t(),
        },
        ProofCert::ZFCMem {
            elem_cert: zero.clone(),
            set_cert: zero.clone(),
        },
        ProofCert::ZFCComprehension {
            var_ty_cert: zero.clone(),
            pred_cert: one.clone(),
            result_type: t(),
        },
        ProofCert::Squash {
            inner_cert: zero.clone(),
        },
    ];
    for kind in [
        ZFCSetCertKind::Empty,
        ZFCSetCertKind::Infinity,
        ZFCSetCertKind::Singleton(zero.clone()),
        ZFCSetCertKind::Pair(zero.clone(), zero.clone()),
        ZFCSetCertKind::Union(zero.clone()),
        ZFCSetCertKind::PowerSet(zero.clone()),
        ZFCSetCertKind::Choice(zero.clone()),
        ZFCSetCertKind::Separation {
            set_cert: zero.clone(),
            pred_cert: one.clone(),
        },
        ZFCSetCertKind::Replacement {
            set_cert: zero.clone(),
            func_cert: one.clone(),
        },
    ] {
        cases.push(ProofCert::ZFCSet {
            kind,
            result_type: t(),
        });
    }
    cases
}

#[test]
fn rebind_preserves_core_cubical_zfc_and_impredicative_rule_fields() {
    let id = FVarId(53);
    let shared = fvar_cert(id, Expr::fvar(id));
    let inputs = shallow_rule_matrix(shared.clone(), shared, Expr::fvar(id));
    let expected = shallow_rule_matrix(
        bvar_cert(0, Expr::bvar(0)),
        bvar_cert(1, Expr::bvar(1)),
        Expr::bvar(0),
    );
    assert_eq!(inputs.len(), 29);
    assert_eq!(inputs.len(), expected.len());
    for (input, expected) in inputs.into_iter().zip(expected) {
        let actual = convert_fvar_cert_to_bvar(input, id, 0);
        assert_eq!(actual, expected);
        if let ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            ..
        } = &actual
        {
            assert!(Arc::ptr_eq(ty_cert, phi_cert));
            assert!(Arc::ptr_eq(ty_cert, u_cert));
            assert!(Arc::ptr_eq(ty_cert, base_cert));
        }
        if let ProofCert::ZFCSet {
            kind: ZFCSetCertKind::Pair(left, right),
            ..
        } = &actual
        {
            assert!(Arc::ptr_eq(left, right));
        }
    }
}

// Independent test inventories of the fields the original rebinder transforms.
// Mutate ONE at a time: a second affected field must not hide a missing summary edge.
fn support_type_fields(cert: &mut ProofCert) -> Vec<&mut Expr> {
    match cert {
        ProofCert::FVar { type_, .. }
        | ProofCert::Const { type_, .. }
        | ProofCert::Lit { type_, .. } => vec![type_],
        ProofCert::BVar { expected_type, .. } => vec![expected_type],
        ProofCert::App {
            fn_type,
            result_type,
            ..
        } => vec![fn_type, result_type],
        ProofCert::Lam { result_type, .. }
        | ProofCert::Let { result_type, .. }
        | ProofCert::MData { result_type, .. }
        | ProofCert::CubicalHComp { result_type, .. }
        | ProofCert::CubicalTransp { result_type, .. }
        | ProofCert::CubicalCoe { result_type, .. }
        | ProofCert::ZFCSet { result_type, .. }
        | ProofCert::ZFCComprehension { result_type, .. } => vec![result_type],
        ProofCert::DefEq {
            expected_type,
            actual_type,
            ..
        } => vec![expected_type, actual_type],
        ProofCert::Proj {
            expr_type,
            field_type,
            ..
        } => vec![expr_type, field_type],
        ProofCert::CubicalPathLam {
            body_type,
            result_type,
            ..
        } => vec![body_type, result_type],
        ProofCert::CubicalPathApp {
            path_type,
            result_type,
            ..
        } => vec![path_type, result_type],
        ProofCert::Sort { .. }
        | ProofCert::Pi { .. }
        | ProofCert::CubicalInterval
        | ProofCert::CubicalEndpoint { .. }
        | ProofCert::CubicalPath { .. }
        | ProofCert::ZFCMem { .. }
        | ProofCert::SProp
        | ProofCert::Squash { .. } => vec![],
    }
}

fn support_children(cert: &mut ProofCert) -> Vec<(&mut Arc<ProofCert>, u32)> {
    match cert {
        ProofCert::App {
            fn_cert, arg_cert, ..
        } => vec![(fn_cert, 0), (arg_cert, 0)],
        ProofCert::Lam {
            arg_type_cert,
            body_cert,
            ..
        } => vec![(arg_type_cert, 0), (body_cert, 1)],
        ProofCert::Pi {
            arg_type_cert,
            body_type_cert,
            ..
        } => vec![(arg_type_cert, 0), (body_type_cert, 1)],
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            ..
        } => vec![(type_cert, 0), (value_cert, 0), (body_cert, 1)],
        ProofCert::DefEq { inner, .. } => vec![(inner, 0)],
        ProofCert::MData { inner_cert, .. } | ProofCert::Squash { inner_cert } => {
            vec![(inner_cert, 0)]
        }
        ProofCert::Proj { expr_cert, .. } => vec![(expr_cert, 0)],
        ProofCert::CubicalPath {
            ty_cert,
            left_cert,
            right_cert,
            ..
        } => vec![(ty_cert, 0), (left_cert, 0), (right_cert, 0)],
        ProofCert::CubicalPathLam { body_cert, .. } => vec![(body_cert, 1)],
        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            ..
        } => vec![(path_cert, 0), (arg_cert, 0)],
        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            ..
        } => vec![(ty_cert, 0), (phi_cert, 0), (u_cert, 0), (base_cert, 0)],
        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            ..
        } => vec![(ty_cert, 0), (phi_cert, 0), (base_cert, 0)],
        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            ..
        } => vec![(ty_cert, 0), (r_cert, 0), (s_cert, 0), (base_cert, 0)],
        ProofCert::ZFCSet { kind, .. } => match kind {
            ZFCSetCertKind::Empty | ZFCSetCertKind::Infinity => vec![],
            ZFCSetCertKind::Singleton(c)
            | ZFCSetCertKind::Union(c)
            | ZFCSetCertKind::PowerSet(c)
            | ZFCSetCertKind::Choice(c) => vec![(c, 0)],
            ZFCSetCertKind::Pair(a, b) => vec![(a, 0), (b, 0)],
            ZFCSetCertKind::Separation {
                set_cert,
                pred_cert,
            }
            | ZFCSetCertKind::Replacement {
                set_cert,
                func_cert: pred_cert,
            } => vec![(set_cert, 0), (pred_cert, 1)],
        },
        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => vec![(elem_cert, 0), (set_cert, 0)],
        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            ..
        } => vec![(var_ty_cert, 0), (pred_cert, 1)],
        ProofCert::Sort { .. }
        | ProofCert::BVar { .. }
        | ProofCert::FVar { .. }
        | ProofCert::Const { .. }
        | ProofCert::Lit { .. }
        | ProofCert::CubicalInterval
        | ProofCert::CubicalEndpoint { .. }
        | ProofCert::SProp => vec![],
    }
}

fn closed_support_rules() -> Vec<ProofCert> {
    let leaf = Arc::new(ProofCert::Sort {
        level: Level::zero(),
    });
    let mut rules = shallow_rule_matrix(leaf.clone(), leaf, Expr::prop());
    rules.extend([
        ProofCert::FVar {
            id: FVarId(999),
            type_: Box::new(Expr::prop()),
        },
        ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(Expr::prop()),
        },
        ProofCert::Const {
            name: Name::from_string("metadataOnly"),
            levels: vec![],
            type_: Box::new(Expr::prop()),
        },
        ProofCert::Lit {
            lit: Literal::nat(17),
            type_: Box::new(Expr::prop()),
        },
    ]);
    rules
}

#[test]
fn rebind_support_closed_dag_across_binder_depths_stays_linear() {
    let target = FVarId(53);
    let mut shared = Arc::new(ProofCert::Sort {
        level: Level::zero(),
    });
    for _ in 0..24 {
        shared = Arc::new(app_cert(shared.clone(), shared.clone(), Expr::prop()));
    }
    for depth in [8, 24, 48] {
        let mut root = fvar_cert(target, Expr::prop());
        for _ in 0..depth {
            root = Arc::new(ProofCert::Lam {
                binder_info: BinderInfo::Default,
                arg_type_cert: shared.clone(),
                body_cert: root,
                result_type: Box::new(Expr::prop()),
            });
        }
        let before = core_allocations(&root);
        assert_eq!(before, 25 + depth + 1);
        let output = convert_fvar_cert_to_bvar(root.as_ref().clone(), target, 0);
        assert_eq!(core_allocations(&output), before, "O(N+d), not O(N*d)");
        let mut node = &output;
        for _ in 0..depth {
            let ProofCert::Lam {
                arg_type_cert,
                body_cert,
                ..
            } = node
            else {
                panic!("Lam")
            };
            assert!(
                Arc::ptr_eq(arg_type_cert, &shared),
                "keep the actual input allocation at every depth"
            );
            node = body_cert;
        }
        assert_eq!(node, bvar_cert(depth as u32, Expr::prop()).as_ref());
    }
}

#[test]
fn rebind_support_each_rule_and_metadata_field_preserves_identity_or_effect() {
    let target = FVarId(53);
    let rules = closed_support_rules();
    assert_eq!(rules.len(), 33);
    for rule in rules {
        let original = Arc::new(rule.clone());
        let mut context = RebindContext::new(target);
        assert!(Arc::ptr_eq(&context.convert_arc(&original, 1), &original));
        assert!(
            context.memo.is_empty(),
            "unchanged rules never enter the conversion memo"
        );
        let count = support_type_fields(&mut rule.clone()).len();
        for index in 0..count {
            for (input_type, output_type) in [
                (Expr::fvar(target), Expr::bvar(1)),
                (Expr::bvar(1), Expr::bvar(2)),
            ] {
                let mut input = rule.clone();
                *support_type_fields(&mut input)[index] = input_type;
                let input = Arc::new(input);
                let mut expected = rule.clone();
                *support_type_fields(&mut expected)[index] = output_type;
                let mut context = RebindContext::new(target);
                let actual = context.convert_arc(&input, 1);
                assert!(!Arc::ptr_eq(&actual, &input));
                assert_eq!(actual.as_ref(), &expected);
            }
        }
    }
}

#[test]
fn rebind_support_each_child_edge_tracks_its_original_binder_depth() {
    let target = FVarId(53);
    let mut tested = 0;
    for rule in closed_support_rules() {
        let count = support_children(&mut rule.clone()).len();
        for index in 0..count {
            let mut input = rule.clone();
            let (child, delta) = support_children(&mut input).remove(index);
            *child = fvar_cert(target, Expr::prop());
            let input = Arc::new(input);
            let mut expected = rule.clone();
            *support_children(&mut expected).remove(index).0 = bvar_cert(1 + delta, Expr::prop());
            let actual = RebindContext::new(target).convert_arc(&input, 1);
            assert!(!Arc::ptr_eq(&actual, &input));
            assert_eq!(actual.as_ref(), &expected);
            for (before, after, unchanged) in [(1 + delta, 2 + delta, false), (delta, delta, true)]
            {
                let mut input = rule.clone();
                *support_children(&mut input).remove(index).0 = bvar_cert(before, Expr::prop());
                let input = Arc::new(input);
                let mut expected = rule.clone();
                *support_children(&mut expected).remove(index).0 = bvar_cert(after, Expr::prop());
                let actual = RebindContext::new(target).convert_arc(&input, 1);
                assert_eq!(Arc::ptr_eq(&actual, &input), unchanged);
                assert_eq!(actual.as_ref(), &expected);
            }
            tested += 1;
        }
    }
    assert_eq!(tested, 44, "every original recursive certificate edge");
}

#[test]
fn rebind_support_positive_prefix_preserves_all_later_fields_and_edges() {
    let target = FVarId(53);
    let rules = closed_support_rules();
    assert_eq!(rules.len(), 33);
    let mut edges = 0;
    for rule in rules {
        let mut input = rule.clone();
        let mut expected = rule;
        let fields = support_type_fields(&mut input).len();
        for field in support_type_fields(&mut input) {
            *field = Expr::fvar(target);
        }
        for field in support_type_fields(&mut expected) {
            *field = Expr::bvar(1);
        }
        let children = support_children(&mut input).len();
        for (child, _) in support_children(&mut input) {
            *child = fvar_cert(target, Expr::prop());
        }
        for (child, delta) in support_children(&mut expected) {
            *child = bvar_cert(1 + delta, Expr::prop());
        }
        edges += children;
        let input = Arc::new(input);
        // All transformed fields/children are affected simultaneously. The
        // first positive support edge cannot hide conversion of later ones.
        // These shallow fixtures also compare the original wire format; never
        // serialize the exponentially shared growth fixture above.
        let original_bytes = serde_json::to_vec(input.as_ref()).unwrap();
        let actual = RebindContext::new(target).convert_arc(&input, 1);
        assert_eq!(Arc::ptr_eq(&actual, &input), fields + children == 0);
        assert_eq!(actual.as_ref(), &expected);
        assert_eq!(
            serde_json::to_vec(actual.as_ref()).unwrap(),
            serde_json::to_vec(&expected).unwrap()
        );
        assert_eq!(serde_json::to_vec(input.as_ref()).unwrap(), original_bytes);
    }
    assert_eq!(edges, 44, "every original recursive certificate edge");
}

#[test]
fn rebind_support_keeps_depth_freevar_and_context_distinctions() {
    let first = FVarId(53);
    let second = FVarId(54);
    let shared = bvar_cert(0, Expr::prop());
    let mut context = RebindContext::new(first);
    let shifted = context.convert_arc(&shared, 0);
    let unchanged = context.convert_arc(&shared, 1);
    assert_eq!(shifted.as_ref(), bvar_cert(1, Expr::prop()).as_ref());
    assert!(!Arc::ptr_eq(&shifted, &shared));
    assert!(Arc::ptr_eq(&unchanged, &shared));
    assert!(Arc::ptr_eq(&context.convert_arc(&shared, 0), &shifted));

    let leaf = fvar_cert(first, Expr::prop());
    assert!(Arc::ptr_eq(
        &RebindContext::new(second).convert_arc(&leaf, 0),
        &leaf
    ));
    assert_eq!(
        RebindContext::new(first).convert_arc(&leaf, 0).as_ref(),
        bvar_cert(0, Expr::prop()).as_ref()
    );
    let metadata = fvar_cert(second, Expr::fvar(second));
    let result = RebindContext::new(first).convert_arc(&metadata, 0);
    assert_eq!(result.as_ref(), metadata.as_ref());
    assert!(
        Arc::ptr_eq(&result, &metadata),
        "unrelated-FVar metadata is exactly unchanged"
    );
}

#[test]
fn rebind_support_preserves_saturating_index_and_depth_boundaries() {
    let target = FVarId(53);
    let leaf = Arc::new(ProofCert::Sort {
        level: Level::zero(),
    });
    let binder = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: leaf.clone(),
        body_cert: leaf,
        result_type: Box::new(Expr::prop()),
    };
    for (input, retained) in [
        (bvar_cert(u32::MAX, Expr::prop()).as_ref().clone(), false),
        (binder, false),
        (
            ProofCert::Const {
                name: Name::from_string("metadataOnly"),
                levels: vec![],
                type_: Box::new(Expr::lam(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::fvar(FVarId(54)),
                )),
            },
            true,
        ),
    ] {
        let input = Arc::new(input);
        let actual = RebindContext::new(target).convert_arc(&input, u32::MAX);
        assert_eq!(actual.as_ref(), input.as_ref());
        assert!(
            Arc::ptr_eq(&actual, &input) == retained,
            "certificate saturation guards stay conservative; unrelated Expr FVars are unchanged"
        );
        assert_eq!(
            convert_fvar_cert_to_bvar(input.as_ref().clone(), target, u32::MAX),
            *input
        );
    }
    let input = Arc::new(ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Arc::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: fvar_cert(target, Expr::prop()),
        result_type: Box::new(Expr::prop()),
    });
    let actual = RebindContext::new(target).convert_arc(&input, u32::MAX);
    let ProofCert::Lam { body_cert, .. } = actual.as_ref() else {
        panic!("Lam")
    };
    assert_eq!(
        body_cert.as_ref(),
        bvar_cert(u32::MAX, Expr::prop()).as_ref()
    );
}

#[test]
fn rebind_support_actual_closed_nested_binders_infer_and_replay() {
    let env = Environment::new();
    let mut expr = Expr::prop();
    let mut expected = Expr::type_();
    for _ in 0..8 {
        expr = Expr::lam(BinderInfo::Default, Expr::prop(), expr);
        expected = Expr::pi(BinderInfo::Default, Expr::prop(), expected);
    }
    let (ty, cert) = TypeChecker::new(&env)
        .infer_type_with_cert(&expr)
        .expect("actual closed lambda telescope");
    assert_eq!(ty, expected);
    let actual = CertVerifier::new(&env)
        .verify(&cert, &expr)
        .expect("unchanged independent certificate verification");
    assert_eq!(actual, expected);
}
