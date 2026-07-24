// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::DeclarationTrustSummary;
use clean_kernel::{BinderInfo, Expr, Name, SorrySummary};

fn explicit_sorry() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("sorryAx"), vec![]),
        [
            Expr::prop(),
            Expr::const_(Name::from_string("Bool.false"), vec![]),
        ],
    )
}

fn synthetic_sorry() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("sorryAx"), vec![]),
        [
            Expr::prop(),
            Expr::const_(Name::from_string("Bool.true"), vec![]),
        ],
    )
}

fn trusted_arith(goal: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedArith"), vec![]),
        Expr::const_(Name::from_string(goal), vec![]),
    )
}

fn trusted_ay(goal: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![]),
        Expr::const_(Name::from_string(goal), vec![]),
    )
}

#[test]
fn test_declaration_trust_summary_counts_multiple_terms_in_nested_expression() {
    let expr = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        trusted_ay("Issue2667.goal0"),
        Expr::lam(
            BinderInfo::Default,
            synthetic_sorry(),
            Expr::app(
                Expr::app(trusted_arith("Issue2667.goal1"), explicit_sorry()),
                trusted_ay("Issue2667.goal2"),
            ),
        ),
        false,
    );

    let summary = DeclarationTrustSummary::from_expr(&expr);
    assert!(
        summary.has_explicit_sorry,
        "nested explicit sorry should be tracked"
    );
    assert!(
        summary.has_synthetic_sorry,
        "binder types containing synthetic sorry should be tracked"
    );
    assert_eq!(
        summary.trusted_arith_count, 1,
        "the walker should count each trustedArith occurrence"
    );
    assert_eq!(
        summary.trusted_ay_count, 2,
        "the walker should count repeated trustedAy occurrences"
    );
    assert_eq!(summary.trusted_axiom_count(), 3);
    assert!(!summary.is_fully_verified());
    assert_eq!(
        summary.sorry_summary(),
        SorrySummary {
            has_sorry: true,
            has_explicit_sorry: true,
            has_synthetic_sorry: true,
        }
    );
}

#[test]
fn test_declaration_trust_summary_merge_and_projection_preserve_counts() {
    let mut merged = DeclarationTrustSummary::from_expr(&trusted_ay("Issue2667.left"));
    merged.merge(DeclarationTrustSummary::from_expr(&Expr::app(
        trusted_arith("Issue2667.right"),
        explicit_sorry(),
    )));

    assert!(merged.has_explicit_sorry);
    assert!(!merged.has_synthetic_sorry);
    assert_eq!(merged.trusted_arith_count, 1);
    assert_eq!(merged.trusted_ay_count, 1);
    assert_eq!(merged.trusted_axiom_count(), 2);
    assert!(!merged.is_fully_verified());
    assert_eq!(
        merged.sorry_summary(),
        SorrySummary {
            has_sorry: true,
            has_explicit_sorry: true,
            has_synthetic_sorry: false,
        }
    );

    let trust_only = DeclarationTrustSummary::from_expr(&Expr::app(
        trusted_arith("Issue2667.trust_only"),
        trusted_ay("Issue2667.trust_only_tail"),
    ));
    assert!(
        !trust_only.sorry_summary().has_sorry,
        "trusted-only debt must not be projected as sorry"
    );
    assert_eq!(trust_only.trusted_axiom_count(), 2);
    assert!(!trust_only.is_fully_verified());
}
