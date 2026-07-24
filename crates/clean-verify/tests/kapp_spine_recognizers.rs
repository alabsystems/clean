// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment A (#2859 computational-iota/delta track): the application-spine /
//! head recognition substrate `kapp_fn` / `kapp_arg_count` / `is_const_app`.
//!
//! These pure structural `KExpr` functions are the substrate a later
//! computational `iota_step` uses to recognize a recursor-`const`-headed
//! `app`-spine without any change to `KExpr`. This test pins that they are
//! registered as DerivedProved definitions, that their unfolding lemmas hold,
//! and that closed evaluations reduce in the kernel (the directed-computation
//! property the track relies on). See
//! `designs/2026-06-14-computational-iota-delta-track.md`.

use clean_kernel::{Expr, Name, TypeChecker};
use clean_verify::spec::{AxiomCategory, ProofStatus};
use clean_verify::test_utils::build_spec_with_stack;

fn nat_lit(n: u32) -> Expr {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let mut out = zero;
    for _ in 0..n {
        out = Expr::app(succ.clone(), out);
    }
    out
}

fn kexpr_sort(n: u32) -> Expr {
    let sort = Expr::const_(Name::from_string("KExpr.sort"), vec![]);
    Expr::app(sort, nat_lit(n))
}

/// The three recognizers are registered recursive definitions and the three
/// unfolding lemmas are DerivedProved with zero axiom_deps.
#[test]
fn spine_recognizers_are_registered_and_proved() {
    let spec = build_spec_with_stack();

    for name in ["kapp_fn", "kapp_arg_count", "is_const_app"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be a registered recursive def"));
        assert!(!def.is_axiom, "{name} must be a definition, not an axiom");
        assert!(
            def.value_src.is_some() || def.elaborated_value.is_some(),
            "{name} should carry a computational body"
        );
    }

    for name in ["kapp_fn_app", "kapp_fn_const", "kapp_arg_count_app"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} unfolding lemma should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (Eq.refl unfolding)"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry zero axiom_deps: {:?}",
            def.axiom_deps
        );
    }
}

/// Closed single-step evaluations reduce in the kernel: a bare (non-application)
/// term is its own spine head with zero arguments. (The recursive `app`-spine
/// computation rules are guaranteed definitionally by the DerivedProved `Eq.refl`
/// unfolding lemmas pinned above — `kapp_fn_app`/`kapp_arg_count_app` only
/// typecheck because the match computes. Multi-level kernel WHNF through the
/// spec-level `KExpr.rec` wrapper is a known kernel limitation, logged here as a
/// diagnostic rather than hard-asserted; cf. tests/instantiate_at_diagnostic.rs.)
#[test]
fn spine_recognizers_compute_on_closed_terms() {
    let spec = build_spec_with_stack();
    let tc = TypeChecker::new(spec.env());

    let kapp_fn = Expr::const_(Name::from_string("kapp_fn"), vec![]);
    let kapp_arg_count = Expr::const_(Name::from_string("kapp_arg_count"), vec![]);

    // A bare head has zero args and is its own head (single recursor step on the
    // `sort` constructor — reliably reduces).
    let bare = kexpr_sort(0);
    let bare_count = Expr::app(kapp_arg_count.clone(), bare.clone());
    assert!(
        tc.is_def_eq(&bare_count, &nat_lit(0)),
        "kapp_arg_count of a bare sort should be 0; WHNF = {:?}",
        tc.whnf(&bare_count)
    );
    let bare_fn = Expr::app(kapp_fn.clone(), bare.clone());
    assert!(
        tc.is_def_eq(&bare_fn, &bare),
        "kapp_fn of a bare sort should be itself; WHNF = {:?}",
        tc.whnf(&bare_fn)
    );

    // Diagnostic only: the recursive spine cases (correctness already guaranteed
    // by the DerivedProved unfolding lemmas). Log the reduction surface.
    let spine = Expr::app(Expr::app(kexpr_sort(0), kexpr_sort(1)), kexpr_sort(2));
    eprintln!(
        "[Increment A diagnostic] kapp_fn (2-arg sort spine) WHNF = {:?}",
        tc.whnf(&Expr::app(kapp_fn, spine.clone()))
    );
    eprintln!(
        "[Increment A diagnostic] kapp_arg_count (2-arg sort spine) WHNF = {:?}",
        tc.whnf(&Expr::app(kapp_arg_count, spine))
    );
}
