// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Regression: a certificate must be no bigger than the DAG it certifies.
//!
//! Match lowering hands the kernel expression DAGs whose children are shared
//! `Arc<Expr>` nodes. `infer_arc_memo` already walks such a DAG once, but until
//! the certificate's own children became `Arc<ProofCert>` the MATERIALIZED
//! certificate still mirrored the *expanded* term: every memo hit deep-cloned
//! the memoized sub-certificate and every parent embedded its children by
//! value, so a spine of depth `d` with sharing factor 2 produced `2^(d+2) - 3`
//! certificate nodes. Measured on the pre-fix tree, allocated nodes were
//!
//! ```text
//!   depth   4      8       12      16
//!   nodes   61     1021    16381   262141        (2^(d+2) - 3, tree)
//!   micros  53     661     9825    164240
//! ```
//!
//! and after the `Arc` conversion, on the same probe,
//!
//! ```text
//!   depth   4      8       12      16      24
//!   nodes   17     33      49      65      97     (4d + 1, DAG)
//!   micros  21     39      57      66      94
//! ```
//!
//! This test pins the DAG bound. It is deliberately measured on ALLOCATED
//! nodes (pointer identity), because the logical *tree* size is still
//! exponential — sharing is what makes it representable at all.

use clean_kernel::cert::ProofCert;
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use std::sync::Arc;

fn cert_nodes(c: &ProofCert) -> u64 {
    match c {
        ProofCert::App {
            fn_cert, arg_cert, ..
        } => 1 + cert_nodes(fn_cert) + cert_nodes(arg_cert),
        ProofCert::Lam {
            arg_type_cert,
            body_cert,
            ..
        } => 1 + cert_nodes(arg_type_cert) + cert_nodes(body_cert),
        ProofCert::Pi {
            arg_type_cert,
            body_type_cert,
            ..
        } => 1 + cert_nodes(arg_type_cert) + cert_nodes(body_type_cert),
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            ..
        } => 1 + cert_nodes(type_cert) + cert_nodes(value_cert) + cert_nodes(body_cert),
        ProofCert::DefEq { inner, .. } => 1 + cert_nodes(inner),
        ProofCert::MData { inner_cert, .. } => 1 + cert_nodes(inner_cert),
        ProofCert::Proj { expr_cert, .. } => 1 + cert_nodes(expr_cert),
        _ => 1,
    }
}

/// ALLOCATED nodes: each cert address counted once (the materialized DAG size).
fn cert_distinct(c: &ProofCert, seen: &mut std::collections::HashSet<usize>) -> u64 {
    let p = std::ptr::from_ref::<ProofCert>(c) as usize;
    if !seen.insert(p) {
        return 0;
    }
    match c {
        ProofCert::App {
            fn_cert, arg_cert, ..
        } => 1 + cert_distinct(fn_cert, seen) + cert_distinct(arg_cert, seen),
        ProofCert::Lam {
            arg_type_cert,
            body_cert,
            ..
        } => 1 + cert_distinct(arg_type_cert, seen) + cert_distinct(body_cert, seen),
        ProofCert::Pi {
            arg_type_cert,
            body_type_cert,
            ..
        } => 1 + cert_distinct(arg_type_cert, seen) + cert_distinct(body_type_cert, seen),
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            ..
        } => {
            1 + cert_distinct(type_cert, seen)
                + cert_distinct(value_cert, seen)
                + cert_distinct(body_cert, seen)
        }
        ProofCert::DefEq { inner, .. } => 1 + cert_distinct(inner, seen),
        ProofCert::MData { inner_cert, .. } => 1 + cert_distinct(inner_cert, seen),
        ProofCert::Proj { expr_cert, .. } => 1 + cert_distinct(expr_cert, seen),
        _ => 1,
    }
}

fn env_with_f() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
    })
    .expect("Nat axiom");
    let nat = Expr::const_str("Nat");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        ),
    })
    .expect("f axiom");
    env
}

/// e_0 = 0 ; e_{k+1} = f e_k e_k  with BOTH argument positions the SAME `Arc`.
fn shared_dag(depth: u32) -> Arc<Expr> {
    let f = Arc::new(Expr::const_str("f"));
    let mut e = Arc::new(Expr::nat_lit(0));
    for _ in 0..depth {
        let inner = Arc::new(Expr::from_kind(ExprKind::App(f.clone(), e.clone())));
        e = Arc::new(Expr::from_kind(ExprKind::App(inner, e.clone())));
    }
    e
}

/// The certificate over a shared-`Arc` spine must stay linear in the depth.
///
/// REQUIRES: `f : Nat -> Nat -> Nat` and a spine whose two argument positions
/// at each level are the SAME `Arc<Expr>`.
/// ENSURES: allocated certificate nodes are `O(depth)`, not `O(2^depth)`.
#[test]
fn cert_over_shared_arc_dag_stays_linear() {
    let env = env_with_f();
    let max: u32 = std::env::var("CERT_PROBE_MAX")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(14);
    println!("depth\texpr_distinct\tcert_tree\tcert_alloc\tmicros");
    for d in 1..=max {
        let e = shared_dag(d);
        let tc = TypeChecker::new(&env);
        let t0 = std::time::Instant::now();
        let (_ty, cert) = tc
            .infer_type_with_cert(e.as_ref())
            .expect("shared DAG should type-check");
        let micros = t0.elapsed().as_micros();
        // `cert_nodes` is the LOGICAL tree size (walks shared nodes repeatedly),
        // so it is only computed where that walk is affordable.
        let n = if d <= 16 {
            cert_nodes(&cert).to_string()
        } else {
            "skipped".to_string()
        };
        let mut seen = std::collections::HashSet::new();
        let dn = cert_distinct(&cert, &mut seen);
        // distinct expression nodes: 2 per level + 1 leaf + 1 for `f`
        println!("{}\t{}\t{}\t{}\t{}", d, 2 * d + 2, n, dn, micros);
        // Linear bound with generous slack. Pre-fix this is 2^(d+2) - 3, so
        // the assertion trips from depth 4 on.
        let bound = u64::from(8 * d + 16);
        assert!(
            dn <= bound,
            "certificate over a shared-Arc DAG of depth {d} allocated {dn} nodes, \
             bound {bound} — certificate children are no longer shared"
        );
    }
}
