// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg(not(debug_assertions))]

//! Release-only parity tests for `TypeChecker::infer_type`.
//!
//! In release builds, `infer_type()` uses the fast path instead of the
//! certificate-generating debug path. These tests compare the release path
//! against `infer_type_with_cert()` on a representative corpus and verify
//! that the closed-term type cache records real hits.

#[path = "release_infer_parity/support.rs"]
mod release_infer_parity_support;

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, FVarId, ZFCSetExpr};
use clean_kernel::level::Level;
use clean_kernel::mode::CleanMode;
use clean_kernel::{LocalContext, Name, TypeChecker};
use release_infer_parity_support::{
    cubical_constant_interval_family, cubical_constant_prop_path, cubical_i0, cubical_i1,
    cubical_interval, release_infer_env, release_zfc_env, wave0_corpus, zfc_empty_set,
    zfc_set_identity, zfc_set_to_prop_pred,
};

fn infer_fast(tc: &TypeChecker<'_>, expr: &Expr) -> Result<Expr, String> {
    tc.infer_type(expr)
        .map_err(|err| strip_location(&format!("{err:?}")))
}

fn infer_cert(tc: &TypeChecker<'_>, expr: &Expr) -> Result<Expr, String> {
    tc.infer_type_with_cert(expr)
        .map(|(ty, _cert)| ty)
        .map_err(|err| strip_location(&format!("{err:?}")))
}

/// The certifying infer path records an `ExprLocation` (decl_name + traversal
/// steps) for error reporting; the fast path does not. That asymmetry is a
/// reporting feature, not a parity gap — the underlying error variant and
/// payload are the same. Strip the `location:` field from both Debug strings
/// so the parity assertion compares the kernel error shape, not the
/// location-tracking metadata.
fn strip_location(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        // Look for the start of a ", location: " segment.
        let rest = &s[i..];
        if let Some(label) = [", location: ", " location: "]
            .iter()
            .find(|lbl| rest.starts_with(*lbl))
        {
            let after_label = i + label.len();
            let after = &s[after_label..];
            // Determine the length of the value to drop: `None` or `Some(...)`.
            let drop_len = if after.starts_with("None") {
                4
            } else if after.starts_with("Some(") {
                let mut depth = 1u32;
                let mut consumed = "Some(".len();
                for c in after[consumed..].chars() {
                    consumed += c.len_utf8();
                    match c {
                        '(' => depth += 1,
                        ')' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                consumed
            } else {
                0
            };
            i = after_label + drop_len;
            continue;
        }
        let ch = s[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn assert_parity_in_mode(env: &Environment, mode: CleanMode, name: &str, expr: &Expr) {
    let fast = infer_fast(&TypeChecker::with_mode(env, mode), expr);
    let cert = infer_cert(&TypeChecker::with_mode(env, mode), expr);
    assert_parity(name, fast, cert);
}

fn assert_parity(name: &str, fast: Result<Expr, String>, cert: Result<Expr, String>) {
    assert_eq!(
        fast, cert,
        "release infer parity mismatch for {name}: fast={fast:?}, cert={cert:?}"
    );
}

fn certified_type(env: &Environment, name: &str, expr: &Expr) -> Expr {
    TypeChecker::new(env)
        .infer_type_with_cert(expr)
        .unwrap_or_else(|err| panic!("cert infer failed for {name}: {err:?}"))
        .0
}

#[test]
fn infer_parity_release_matches_certified_wave0_corpus() {
    let env = release_infer_env();

    for (name, expr) in wave0_corpus() {
        let fast = infer_fast(&TypeChecker::new(&env), &expr);
        let cert = infer_cert(&TypeChecker::new(&env), &expr);
        assert_parity(name, fast, cert);
    }
}

#[test]
fn infer_parity_release_matches_certified_local_context_paths() {
    let env = release_infer_env();

    let mut ctx = LocalContext::new();
    let x = ctx.push(Name::from_string("x"), Expr::prop(), BinderInfo::Default);
    let y = ctx.push_let(Name::from_string("y"), Expr::type_(), Expr::prop());

    let x_expr = Expr::fvar(x);
    let y_expr = Expr::fvar(y);

    assert_parity(
        "fvar_bound",
        infer_fast(&TypeChecker::with_context(&env, ctx.clone()), &x_expr),
        infer_cert(&TypeChecker::with_context(&env, ctx.clone()), &x_expr),
    );
    assert_parity(
        "fvar_let_bound",
        infer_fast(&TypeChecker::with_context(&env, ctx.clone()), &y_expr),
        infer_cert(&TypeChecker::with_context(&env, ctx), &y_expr),
    );
}

#[test]
fn infer_parity_release_matches_certified_error_paths() {
    let env = release_infer_env();

    let cases = [
        ("unbound_bvar", Expr::bvar(0)),
        ("unknown_fvar", Expr::fvar(FVarId::new(99_999))),
        (
            "not_a_function",
            Expr::app(Expr::sort(Level::zero()), Expr::sort(Level::zero())),
        ),
    ];

    for (name, expr) in cases {
        let fast = infer_fast(&TypeChecker::new(&env), &expr);
        let cert = infer_cert(&TypeChecker::new(&env), &expr);
        assert_parity(name, fast, cert);
    }
}

#[test]
fn infer_parity_release_matches_certified_cubical_mode_paths() {
    let env = release_infer_env();
    let path_lam = cubical_constant_prop_path();
    let cases = [
        ("cubical_interval", cubical_interval()),
        ("cubical_i0", cubical_i0()),
        ("cubical_i1", cubical_i1()),
        (
            "cubical_path",
            Expr::from_kind(ExprKind::CubicalPath {
                ty: cubical_constant_interval_family().into(),
                left: cubical_i0().into(),
                right: cubical_i1().into(),
            }),
        ),
        ("cubical_path_lam", path_lam.clone()),
        (
            "cubical_path_app",
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: path_lam.into(),
                arg: cubical_i1().into(),
            }),
        ),
        (
            "cubical_hcomp",
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: cubical_interval().into(),
                phi: cubical_i0().into(),
                u: Expr::lam(BinderInfo::Default, cubical_interval(), cubical_i0()).into(),
                base: cubical_i0().into(),
            }),
        ),
        (
            "cubical_transp",
            Expr::from_kind(ExprKind::CubicalTransp {
                ty: cubical_constant_interval_family().into(),
                phi: cubical_i0().into(),
                base: cubical_i0().into(),
            }),
        ),
    ];

    for (name, expr) in cases {
        assert_parity_in_mode(&env, CleanMode::Cubical, name, &expr);
    }
}

#[test]
fn infer_parity_release_matches_certified_set_theoretic_paths() {
    let env = release_zfc_env();
    let empty = zfc_empty_set();
    let pred = zfc_set_to_prop_pred();
    let func = zfc_set_identity();
    let cases = [
        ("zfc_empty", empty.clone()),
        (
            "zfc_singleton",
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(
                empty.clone().into(),
            ))),
        ),
        (
            "zfc_separation",
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
                set: empty.clone().into(),
                pred: pred.clone().into(),
            })),
        ),
        (
            "zfc_replacement",
            Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
                set: empty.clone().into(),
                func: func.clone().into(),
            })),
        ),
        (
            "zfc_mem",
            Expr::from_kind(ExprKind::ZFCMem {
                element: empty.clone().into(),
                set: empty.clone().into(),
            }),
        ),
        (
            "zfc_comprehension",
            Expr::from_kind(ExprKind::ZFCComprehension {
                domain: empty.into(),
                pred: pred.into(),
            }),
        ),
    ];

    for (name, expr) in cases {
        assert_parity_in_mode(&env, CleanMode::SetTheoretic, name, &expr);
    }
}

#[test]
fn infer_parity_release_matches_certified_impredicative_paths() {
    let env = release_infer_env();
    let cases = [
        ("sprop", Expr::from_kind(ExprKind::SProp)),
        (
            "squash_prop",
            Expr::from_kind(ExprKind::Squash(Expr::prop().into())),
        ),
        (
            "squash_type",
            Expr::from_kind(ExprKind::Squash(Expr::type_().into())),
        ),
    ];

    for (name, expr) in cases {
        assert_parity_in_mode(&env, CleanMode::Impredicative, name, &expr);
    }
}

#[test]
fn infer_parity_release_matches_certified_mode_error_paths() {
    let env = release_infer_env();
    let cases = [
        ("cubical_requires_mode", cubical_interval()),
        ("zfc_requires_mode", zfc_empty_set()),
        ("sprop_requires_mode", Expr::from_kind(ExprKind::SProp)),
        (
            "squash_requires_mode",
            Expr::from_kind(ExprKind::Squash(Expr::prop().into())),
        ),
    ];

    for (name, expr) in cases {
        let fast = infer_fast(&TypeChecker::new(&env), &expr);
        let cert = infer_cert(&TypeChecker::new(&env), &expr);
        assert_parity(name, fast, cert);
    }
}

#[test]
fn infer_parity_release_type_cache_hits_on_repeated_closed_terms() {
    let env = release_infer_env();
    let corpus = wave0_corpus();
    let mut tc = TypeChecker::new(&env);
    tc.enable_type_cache_pub();

    for (name, expr) in &corpus {
        let fast = tc
            .infer_type(expr)
            .unwrap_or_else(|err| panic!("first release infer failed for {name}: {err:?}"));
        let cert = certified_type(&env, name, expr);
        assert_eq!(
            fast, cert,
            "cached release infer should match cert for {name}"
        );
    }

    let first_pass = tc.type_cache_stats().expect("type cache should be enabled");
    assert_eq!(
        first_pass.misses,
        corpus.len() as u64,
        "first pass should miss once per closed expression"
    );
    assert_eq!(first_pass.hits, 0, "first pass should not record hits");
    assert_eq!(
        first_pass.entries,
        corpus.len(),
        "cache should store each closed expression after the first pass"
    );

    for (name, expr) in &corpus {
        let cached = tc
            .infer_type(expr)
            .unwrap_or_else(|err| panic!("cached release infer failed for {name}: {err:?}"));
        let cert = certified_type(&env, name, expr);
        assert_eq!(cached, cert, "cache hit should preserve parity for {name}");
    }

    let second_pass = tc
        .type_cache_stats()
        .expect("type cache should stay enabled");
    assert_eq!(
        second_pass.misses,
        corpus.len() as u64,
        "cache misses should not increase on the second pass"
    );
    assert_eq!(
        second_pass.hits,
        corpus.len() as u64,
        "second pass should hit once per closed expression"
    );
    assert_eq!(
        second_pass.entries,
        corpus.len(),
        "cache entry count should remain stable across hits"
    );
}
