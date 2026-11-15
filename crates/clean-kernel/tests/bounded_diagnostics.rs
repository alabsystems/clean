// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::diagnostic::{MAX_DIAGNOSTIC_BYTES, MAX_DIAGNOSTIC_NODES};
use clean_kernel::expr::{BigNat, BinderData, ExprKind, Literal};
use clean_kernel::{Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use std::fmt::Write;
use std::sync::Arc;

fn record(case: &str, text: &str) {
    assert!(text.len() <= MAX_DIAGNOSTIC_BYTES);
    println!(
        "BOUNDED_DIAGNOSTIC={}",
        serde_json::json!({
            "case":case,"bytes":text.len(),"text":text
        })
    );
}

fn shared_pi(depth: usize) -> Arc<Expr> {
    let mut expression = Arc::new(Expr::prop());
    for _ in 0..depth {
        expression = Arc::new(Expr::from(ExprKind::Pi(
            BinderData::default(),
            expression.clone(),
            expression.clone(),
        )));
    }
    expression
}

#[test]
fn actual_shared_type_mismatch_keeps_the_verdict_and_both_roles() {
    let environment = Environment::new();
    let checker = TypeChecker::new(&environment);
    let expected = shared_pi(20);
    let error = checker.check_type(&Expr::prop(), &expected).unwrap_err();
    assert!(matches!(error, KernelTypeError::TypeMismatch { .. }));
    let before = expected.hash_cached();
    let rendered = format!("{}", error.diagnostic());
    record("actual-type-mismatch", &rendered);
    assert!(rendered.starts_with("TypeMismatch { expected: #0, inferred: #1 }"));
    assert!(rendered.contains("Pi(") && rendered.contains("Sort("));
    assert!(rendered.len() <= MAX_DIAGNOSTIC_BYTES);
    assert_eq!(expected.hash_cached(), before);
    assert_eq!(format!("{:?}", error.diagnostic()), rendered);
    assert!(matches!(
        checker.check_type(&Expr::prop(), &expected),
        Err(KernelTypeError::TypeMismatch { .. })
    ));
}

#[test]
fn sharing_is_printed_once_and_the_old_tree_expansion_is_not_used() {
    let expression = shared_pi(14);
    let bounded = expression.diagnostic().to_string();
    record("shared-dag", &bounded);
    assert_eq!(bounded.matches(" = Pi(").count(), 14);
    assert_eq!(bounded.matches(" = Sort(").count(), 1);
    assert_eq!(bounded.matches(" = Level::Zero").count(), 1);
    assert!(bounded.len() < 2048);
    // A capped writer establishes that the pre-existing Debug expands this
    // same small DAG past 64 KiB without allocating or recording a huge log.
    struct StopAt {
        bytes: usize,
    }
    impl Write for StopAt {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.bytes += text.len();
            if self.bytes > 65_536 {
                Err(std::fmt::Error)
            } else {
                Ok(())
            }
        }
    }
    let mut legacy = StopAt { bytes: 0 };
    assert!(write!(legacy, "{expression:?}").is_err());
    assert!(legacy.bytes > 65_536);
}

#[test]
fn deep_expression_and_universe_paths_do_not_use_recursive_formatting() {
    let mut deep = Arc::new(Expr::prop());
    let leaf = Arc::new(Expr::prop());
    for _ in 0..20_000 {
        deep = Arc::new(Expr::from(ExprKind::App(deep, leaf.clone())));
    }
    let expression = deep;
    // Borrowing into a small-stack thread isolates the formatter's stack use;
    // the deep input is constructed and destroyed on the caller's stack.
    let rendered = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn_scoped(scope, || expression.diagnostic().to_string())
            .unwrap()
            .join()
            .unwrap()
    });
    assert!(rendered.len() <= MAX_DIAGNOSTIC_BYTES);
    assert!(rendered.contains("<depth-limit>"));
    assert!(rendered.contains("depth=true"));
    record("deep-expression", &rendered);

    let mut level = Level::zero();
    for _ in 0..20_000 {
        level = Level::Succ(level.into());
    }
    let universe = Expr::from(ExprKind::Sort(level));
    let rendered = universe.diagnostic().to_string();
    assert!(rendered.len() <= MAX_DIAGNOSTIC_BYTES);
    assert!(rendered.contains("Level::Succ") && rendered.contains("depth=true"));
    record("deep-level", &rendered);
}

#[test]
fn huge_names_strings_naturals_and_locations_are_only_previewed() {
    let mut name = Name::anon();
    for _ in 0..20_000 {
        name = name.str("component");
    }
    name = name.str("💥\n".repeat(100_000));
    let unknown = KernelTypeError::UnknownConst(name);
    let rendered = unknown.diagnostic().to_string();
    assert!(rendered.starts_with("UnknownConst("));
    assert!(rendered.contains("<name-prefix>") && rendered.contains("text-preview"));
    assert!(rendered.len() < 1024);
    record("name-and-string-preview", &rendered);

    let string = Expr::from(ExprKind::Lit(Literal::String(Arc::from(
        "💥\n".repeat(100_000),
    ))));
    assert!(string.diagnostic().to_string().len() < 1024);
    let natural = Expr::from(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![
        u64::MAX;
        100_000
    ]))));
    let rendered = natural.diagnostic().to_string();
    assert!(rendered.contains("limbs=100000") && rendered.len() < 1024);
    record("large-natural", &rendered);

    let location = clean_kernel::tc::expr_location::ExprLocation {
        decl_name: Some(Name::from_string("ordinary.source")),
        steps: vec![clean_kernel::tc::expr_location::ExprPathStep::AppArg; 100_000],
    };
    let error = KernelTypeError::TypeMismatch {
        expected: Box::new(Expr::prop()),
        inferred: Box::new(Expr::type_()),
        location: Some(Box::new(location)),
    };
    let rendered = error.diagnostic().to_string();
    assert!(rendered.contains("steps: 100000") && rendered.len() < 2048);
    record("large-location", &rendered);
}

#[test]
fn breadth_and_output_limits_are_visible_and_do_not_hide_error_kinds() {
    let mut layer: Vec<_> = (0..256)
        .map(|i| Arc::new(Expr::const_str(&format!("{}_{i}", "x".repeat(64)))))
        .collect();
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|pair| Arc::new(Expr::from(ExprKind::App(pair[0].clone(), pair[1].clone()))))
            .collect();
    }
    let rendered = layer[0].diagnostic().to_string();
    assert!(rendered.len() <= MAX_DIAGNOSTIC_BYTES);
    assert!(rendered.contains("<node-limit>"));
    record("node-limit", &rendered);
    assert!(
        rendered
            .lines()
            .filter(|line| line.starts_with('#') && line.contains(" = "))
            .count()
            <= MAX_DIAGNOSTIC_NODES
    );

    let mut layer: Vec<_> = (0..64)
        .map(|i| Arc::new(Expr::const_str(&format!("{}_{i}", "x".repeat(128)))))
        .collect();
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|pair| Arc::new(Expr::from(ExprKind::App(pair[0].clone(), pair[1].clone()))))
            .collect();
    }
    let rendered = layer[0].diagnostic().to_string();
    assert!(rendered.len() <= MAX_DIAGNOSTIC_BYTES);
    assert!(rendered.contains("bytes=true"));
    record("byte-limit", &rendered);

    let error = KernelTypeError::DeclarationBudgetExhausted { limit: 123 };
    assert_eq!(
        error.diagnostic().to_string(),
        "DeclarationBudgetExhausted { limit: 123 }; no verdict"
    );
    assert_eq!(
        KernelTypeError::Interrupted.diagnostic().to_string(),
        "Interrupted"
    );
    let ordinary = Expr::prop();
    assert_eq!(format!("{ordinary:?}"), "Sort(Zero)");
    assert_eq!(ordinary.to_string(), "Prop");
}
