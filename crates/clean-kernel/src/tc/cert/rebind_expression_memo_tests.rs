// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared expression fields retain exact binder semantics and avoid repeat walks.

use super::{convert_fvar_cert_to_bvar, RebindContext};
use crate::cert::ProofCert;
use crate::expr::{Expr, ExprKind, FVarId};
use std::collections::HashSet;
use std::sync::Arc;

fn assert_abstracted_dag(root: &Expr, shared_child: &Arc<Expr>) {
    let ExprKind::App(child, _) = root.kind() else {
        panic!("metadata root must retain its application shape");
    };
    assert!(
        Arc::ptr_eq(child, shared_child),
        "all metadata fields must reuse the same transformed child"
    );
    let mut pending = vec![(root, 32)];
    let mut seen = HashSet::new();
    while let Some((node, depth)) = pending.pop() {
        if !seen.insert((std::ptr::from_ref(node), depth)) {
            continue;
        }
        assert!(seen.len() <= 65, "converted expression lost DAG sharing");
        match node.kind() {
            ExprKind::App(func, arg) if depth > 0 => {
                pending.push((func.as_ref(), depth - 1));
                pending.push((arg.as_ref(), depth - 1));
            }
            ExprKind::BVar(0) if depth == 0 => {}
            _ => panic!("converted expression changed shape or leaf value"),
        }
    }
}

#[test]
fn shared_metadata_is_abstracted_once_across_certificate_fields() {
    let target = FVarId(173);
    let mut expression = Expr::fvar(target);
    for _ in 0..32 {
        expression = Expr::app(expression.clone(), expression);
    }
    let leaf = Arc::new(ProofCert::FVar {
        id: target,
        type_: Box::new(expression.clone()),
    });
    let mut certificate = Arc::clone(&leaf);
    for _ in 0..24 {
        certificate = Arc::new(ProofCert::App {
            fn_cert: certificate,
            fn_type: Box::new(expression.clone()),
            arg_cert: Arc::clone(&leaf),
            result_type: Box::new(expression.clone()),
        });
    }

    // The former rebinder started a fresh expression fold for each of these
    // 49 fields. This is a measured lower bound on that former path's work,
    // excluding its certificate/support walks, not a timing-based threshold.
    let _ = crate::work_meter::stats::take();
    for _ in 0..49 {
        drop(expression.abstract_fvar_at(target, 0));
    }
    let independent = crate::work_meter::stats::take().fold_nodes;
    let output = convert_fvar_cert_to_bvar(certificate.as_ref().clone(), target, 0);
    let shared = crate::work_meter::stats::take().fold_nodes;
    assert!(
        shared < independent,
        "shared conversion {shared} must cost less than independent fields {independent}"
    );
    eprintln!("rebind expression folds: independent={independent}, shared={shared}");

    let ProofCert::App { fn_type, .. } = &output else {
        panic!("expected converted application");
    };
    let ExprKind::App(shared_child, _) = fn_type.kind() else {
        panic!("expected application type");
    };
    let shared_child = Arc::clone(shared_child);

    let mut node = &output;
    for _ in 0..24 {
        let ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } = node
        else {
            panic!("expected application in converted certificate");
        };
        assert_abstracted_dag(fn_type, &shared_child);
        assert_abstracted_dag(result_type, &shared_child);
        let ProofCert::BVar {
            idx: 0,
            expected_type,
        } = arg_cert.as_ref()
        else {
            panic!("shared argument must be the abstracted free variable");
        };
        assert_abstracted_dag(expected_type, &shared_child);
        node = fn_cert;
    }
    let ProofCert::BVar {
        idx: 0,
        expected_type,
    } = node
    else {
        panic!("chain must end at the abstracted free variable");
    };
    assert_abstracted_dag(expected_type, &shared_child);
    assert!(expression.has_fvar_quick(), "input was not mutated");
}

#[test]
fn shared_expression_memo_keeps_target_and_depth_separate() {
    let a = FVarId(173);
    let b = FVarId(174);
    let input = Expr::app(Expr::fvar(a), Expr::app(Expr::fvar(b), Expr::bvar(0)));
    let mut first = RebindContext::new(a);
    let mut second = RebindContext::new(b);
    for depth in [0, 1, 0, 2, 1] {
        let shifted = if depth == 0 { 1 } else { 0 };
        assert_eq!(
            first.abstract_expr(&input, depth),
            Expr::app(
                Expr::bvar(depth),
                Expr::app(Expr::fvar(b), Expr::bvar(shifted))
            )
        );
        assert_eq!(
            second.abstract_expr(&input, depth),
            Expr::app(
                Expr::fvar(a),
                Expr::app(Expr::bvar(depth), Expr::bvar(shifted))
            )
        );
    }
}
