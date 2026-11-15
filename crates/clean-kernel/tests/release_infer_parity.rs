// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg(not(debug_assertions))]

//! Release-only parity tests for `TypeChecker::infer_type`.
//!
//! In release builds, `infer_type()` uses the fast path instead of the
//! certificate-generating debug path. These tests compare the release path
//! against `infer_type_with_cert()` on a representative corpus, including the
//! `ExprLocation` every located error carries, and verify that the closed-term
//! type cache records real hits. In a debug build `infer_type()` IS the
//! certificate path, so there is nothing to compare and this file compiles to
//! no tests: run it with `--release`.

#[path = "release_infer_parity/support.rs"]
mod release_infer_parity_support;

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, FVarId, ZFCSetExpr};
use clean_kernel::level::Level;
use clean_kernel::mode::CleanMode;
use clean_kernel::{ExprPathStep, LocalContext, Name, TypeChecker, TypeError};
use release_infer_parity_support::{
    cubical_constant_interval_family, cubical_constant_prop_path, cubical_i0, cubical_i1,
    cubical_interval, release_infer_env, release_zfc_env, wave0_corpus, zfc_empty_set,
    zfc_set_identity, zfc_set_to_prop_pred,
};

fn infer_fast(tc: &TypeChecker<'_>, expr: &Expr) -> Result<Expr, String> {
    tc.infer_type(expr).map_err(|err| format!("{err:?}"))
}

fn infer_cert(tc: &TypeChecker<'_>, expr: &Expr) -> Result<Expr, String> {
    tc.infer_type_with_cert(expr)
        .map(|(ty, _cert)| ty)
        .map_err(|err| format!("{err:?}"))
}

// Errors are compared as their full `Debug` strings, `location:` included.
// Both bodies record an `ExprLocation` (decl_name + traversal steps), and the
// same ill-typed term must get the same one from either: Trust's UI tests read
// it, and a per-profile trail is a diagnostic that depends on the build. This
// file used to strip `location:` before comparing, which is how the release
// body naming the parent instead of the ill-typed child at seven error sites
// went unseen (#3425; `infer_parity_release_matches_certified_error_locations`).

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

/// `let v : ty := val; body`.
fn let_v(ty: Expr, val: Expr, body: Expr) -> Expr {
    Expr::let_named(Name::from_string("v"), ty, val, body, false)
}

/// One ill-typed term per error that names a child term, each checked through
/// both bodies with the `ExprLocation` compared.
struct LocationCase {
    name: &'static str,
    expr: Expr,
    /// `TypeError` variant the term must raise.
    variant: &'static str,
    /// The trail the certificate body records at top level: the one step to
    /// the child the error names (`wrapped` prepends a parent's step).
    steps: Vec<ExprPathStep>,
    /// The check also runs in infer-only mode (`infer_type`). App-argument,
    /// Lam-domain and Let checks run only in check mode (`infer_only = false`).
    in_infer_only: bool,
}

fn location_cases() -> Vec<LocationCase> {
    use ExprPathStep::{AppArg, AppFn, LamType, LetType, LetVal, PiBody, PiDom};
    let prop = Expr::prop;
    // `λ y : Prop, y : Prop → Prop`: a term whose type is a Pi, not a Sort.
    let not_a_type = || Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0));
    let case = |name, expr, variant, step, in_infer_only| LocationCase {
        name,
        expr,
        variant,
        steps: vec![step],
        in_infer_only,
    };
    vec![
        // `Prop Prop`: `Prop : Type` is not a function type.
        case(
            "not_a_function",
            Expr::app(prop(), prop()),
            "NotAFunction",
            AppFn,
            true,
        ),
        // `(λ x : Prop, x) Prop`: `Prop : Type`, the domain is `Prop`.
        case(
            "app_arg_mismatch",
            Expr::app(not_a_type(), prop()),
            "TypeMismatch",
            AppArg,
            false,
        ),
        // `λ x : (λ y : Prop, y), Prop`.
        case(
            "lam_domain_not_a_sort",
            Expr::lam(BinderInfo::Default, not_a_type(), prop()),
            "ExpectedSort",
            LamType,
            false,
        ),
        // `∀ x : (λ y : Prop, y), Prop`.
        case(
            "pi_domain_not_a_sort",
            Expr::pi(BinderInfo::Default, not_a_type(), prop()),
            "ExpectedSort",
            PiDom,
            true,
        ),
        // `∀ x : Prop, (λ y : Prop, y)`.
        case(
            "pi_body_not_a_sort",
            Expr::pi(BinderInfo::Default, prop(), not_a_type()),
            "ExpectedSort",
            PiBody,
            true,
        ),
        // `let v : (λ y : Prop, y) := Prop; Prop`.
        case(
            "let_type_not_a_sort",
            let_v(not_a_type(), prop(), prop()),
            "ExpectedSort",
            LetType,
            false,
        ),
        // `let v : Prop := Prop; Prop`: `Prop : Type`, annotated `Prop`.
        case(
            "let_value_mismatch",
            let_v(prop(), prop(), prop()),
            "TypeMismatch",
            LetVal,
            false,
        ),
    ]
}

/// Each case also runs one binder down, so the parent's steps are compared too.
fn wrapped(case: &LocationCase) -> Vec<(String, Expr, Vec<ExprPathStep>)> {
    let under = |step: ExprPathStep, label: &str, expr: Expr| {
        let mut steps = vec![step];
        steps.extend(case.steps.iter().cloned());
        (format!("{}_under_{label}", case.name), expr, steps)
    };
    let bad = || case.expr.clone();
    vec![
        (case.name.to_string(), bad(), case.steps.clone()),
        under(
            ExprPathStep::LamBody,
            "lam",
            Expr::lam(BinderInfo::Default, Expr::prop(), bad()),
        ),
        under(
            ExprPathStep::PiBody,
            "pi",
            Expr::pi(BinderInfo::Default, Expr::prop(), bad()),
        ),
        under(
            ExprPathStep::LetBody,
            "let",
            let_v(Expr::type_(), Expr::prop(), bad()),
        ),
    ]
}

/// Release `infer_type` and the certificate body agree on the error AND on the
/// `ExprLocation` at every error that names a child term: `NotAFunction`
/// (`AppFn`), App argument (`AppArg`), Lam domain (`LamType`), Pi domain
/// (`PiDom`), Pi body (`PiBody`), Let type (`LetType`) and Let value
/// (`LetVal`). The certificate body pushes the child step before its snapshot;
/// before #3425 the release body snapshotted at the parent. Each case is
/// checked in check mode and, where that check runs there, in infer-only mode.
/// The expected trail is asserted on the certificate error as well, so a case
/// that stops raising its error cannot pass as vacuous parity.
#[test]
fn infer_parity_release_matches_certified_error_locations() {
    let env = release_infer_env();
    // Every disagreement is collected and reported together, so one run names
    // every site whose trail differs rather than the first.
    let mut mismatches = Vec::new();

    for case in location_cases() {
        for (name, expr, steps) in wrapped(&case) {
            let expect = |mode: &str, cert: &Result<Expr, TypeError>| {
                let Err(err) = cert else {
                    panic!("{name} ({mode}): cert must reject, got {cert:?}");
                };
                assert!(
                    format!("{err:?}").starts_with(case.variant),
                    "{name} ({mode}): expected {}, got {err:?}",
                    case.variant
                );
                let location = err.location().map(|loc| loc.steps.clone());
                assert_eq!(location, Some(steps.clone()), "{name} ({mode}) trail");
            };
            let mut compare =
                |mode: &str, fast: Result<Expr, String>, cert: Result<Expr, String>| {
                    if fast != cert {
                        mismatches.push(format!(
                            "{name} ({mode}):\n  fast={fast:?}\n  cert={cert:?}"
                        ));
                    }
                };

            let fast = TypeChecker::new(&env).infer_type_full(&expr);
            let cert = TypeChecker::new(&env)
                .infer_type_with_cert_full(&expr)
                .map(|(ty, _cert)| ty);
            expect("check", &cert);
            compare(
                "check",
                fast.map_err(|err| format!("{err:?}")),
                cert.map_err(|err| format!("{err:?}")),
            );

            let fast = infer_fast(&TypeChecker::new(&env), &expr);
            let cert = TypeChecker::new(&env)
                .infer_type_with_cert(&expr)
                .map(|(ty, _cert)| ty);
            if case.in_infer_only {
                expect("infer-only", &cert);
            }
            compare("infer-only", fast, cert.map_err(|err| format!("{err:?}")));
        }
    }

    assert!(
        mismatches.is_empty(),
        "release infer parity: {} error location mismatch(es):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
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
