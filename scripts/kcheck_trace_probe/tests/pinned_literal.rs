// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, Literal};
use clean_kernel::kcheck_trace::core::{CoreTracer, Refusal};
use clean_kernel::kcheck_trace::term::{Label, Node, Term};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

fn reference_string(text: &str) -> Expr {
    let c = |name| Expr::const_(Name::from_string(name), vec![]);
    let mut list = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        c("Char"),
    );
    for scalar in text.chars().rev() {
        let value = Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(u32::from(scalar))));
        list = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [c("Char"), value, list],
        );
    }
    Expr::app(c("String.ofList"), list)
}

fn validate_labels(term: &Term, checker: &TypeChecker<'_>, count: &mut usize) {
    match term.0.as_ref() {
        Node::App(function, argument, label) => {
            let Label::Checked(domain) = label else {
                panic!("literal builder left an application unlabelled")
            };
            let function_type = checker
                .infer_type(&function.erase())
                .expect("function type");
            let function_type = checker.whnf(&function_type);
            let clean_kernel::expr::ExprKind::Pi(_, expected, _) = function_type.kind() else {
                panic!("function must have Pi type")
            };
            assert!(checker.is_def_eq(&domain.erase(), expected));
            let argument_type = checker
                .infer_type(&argument.erase())
                .expect("argument type");
            assert!(checker.is_def_eq(&argument_type, &domain.erase()));
            *count += 1;
            validate_labels(function, checker, count);
            validate_labels(argument, checker, count);
            validate_labels(domain, checker, count);
        }
        Node::Lam(_, domain, body) | Node::Pi(_, domain, body) => {
            validate_labels(domain, checker, count);
            validate_labels(body, checker, count);
        }
        Node::Let(_, ty, value, body) => {
            validate_labels(ty, checker, count);
            validate_labels(value, checker, count);
            validate_labels(body, checker, count);
        }
        Node::Proj(_, _, value) => validate_labels(value, checker, count),
        _ => {}
    }
}

#[test]
fn pinned_prelude_string_literal_labels_match_the_existing_kernel() {
    let lib = clean_olean::require_pinned_lean_lib_path().expect("exact pinned Lean required");
    let mut env = Environment::for_lean_replay();
    clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib])
        .expect("pinned Prelude import");
    let checker = TypeChecker::new(&env);
    for text in ["", "a", "λ", "aλ", "\0a"] {
        let literal = Literal::String(text.into());
        let raw = Expr::from_kind(clean_kernel::expr::ExprKind::Lit(literal.clone()));
        let reference = reference_string(text);
        let admitted = checker.is_def_eq(&raw, &reference);
        assert!(
            !checker.heartbeat_spent(),
            "an exhausted oracle is not a refusal verdict"
        );
        let mut tracer = CoreTracer::new(&env, 1000000);
        match tracer.expand_literal(&literal) {
            Ok(term) => {
                assert!(admitted, "producer expanded an unadmitted literal");
                assert!(
                    checker.is_def_eq(&raw, &term.erase()),
                    "wrong Unicode sequence"
                );
                let ty = tracer
                    .infer_ann(&term)
                    .expect("annotated literal construction");
                assert!(checker.is_def_eq(
                    &ty.erase(),
                    &Expr::const_(Name::from_string("String"), vec![])
                ));
                let mut count = 0;
                validate_labels(&term, &checker, &mut count);
                assert!(count >= 2 + 4 * text.chars().count());
                assert!(tracer.domain_problems.is_empty());
                eprintln!("pinned String literal {text:?}: admitted; {count} checked applications");
            }
            Err(Refusal::Coverage { source_name, .. }) => {
                assert!(
                    !admitted,
                    "tracer refused a literal the kernel expands: {source_name}"
                );
                assert!(matches!(
                    source_name.as_str(),
                    "String_literal_extension_not_canonical"
                        | "String_literal_ofList_missing_or_legacy_layout"
                ));
                eprintln!(
                    "pinned String literal {text:?}: explicit admission refusal {source_name}"
                );
            }
            Err(error) => panic!("literal construction failed: {error}"),
        }
    }
}

#[test]
fn pinned_nat_primitive_folds_preserve_labels_and_surplus_arguments() {
    let lib = clean_olean::require_pinned_lean_lib_path().expect("exact pin");
    let mut env = Environment::for_lean_replay();
    clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Prelude");
    let add = Name::from_string("Nat.add");
    assert!(env.native_fold_authorized(&add));
    let raw = Expr::apps(
        Expr::const_(add, vec![]),
        [Expr::nat_lit(1000000), Expr::nat_lit(2)],
    );
    let checker = TypeChecker::new(&env);
    let mut tracer = CoreTracer::new(&env, 10000);
    let (annotated, _) = tracer.check(&raw).expect("labelled arithmetic");
    let reduced = tracer.whnf(&annotated).expect("primitive Nat fold");
    assert_eq!(reduced.erase(), Expr::nat_lit(1000002));
    assert!(checker.is_def_eq(&raw, &reduced.erase()));
    assert!(!checker.heartbeat_spent());
    assert_eq!(tracer.native_nat_steps.get("Nat.add").copied(), Some(1));
    assert!(tracer
        .spine_comparisons
        .iter()
        .any(|event| event.entry == "Nat_native"));
    assert!(tracer.domain_problems.is_empty());
    // A surplus argument is invalid typing, but WHNF must preserve it exactly.
    let extra = Term::new(Node::Lit(Literal::Nat(4u64.into())));
    let nat = Term::new(Node::Const(Name::from_string("Nat"), vec![]));
    let over = Term::new(Node::App(annotated, extra.clone(), Label::Checked(nat)));
    let reduced = tracer.whnf(&over).expect("do not drop surplus application");
    assert_eq!(
        reduced.erase(),
        Expr::app(Expr::nat_lit(1000002), extra.erase())
    );
}

#[test]
fn pinned_int_constructor_comparison_records_the_coverage_gap() {
    let lib = clean_olean::require_pinned_lean_lib_path().expect("exact pin");
    let mut env = Environment::for_lean_replay();
    clean_olean::load_module_with_deps(&mut env, "Init.Data.Int.Basic", &[lib])
        .expect("pinned Int definitions");
    let c = |name| Expr::const_(Name::from_string(name), vec![]);
    let left = Expr::app(c("Int.ofNat"), Expr::app(c("Nat.succ"), Expr::nat_lit(0)));
    let right = Expr::app(c("Int.ofNat"), Expr::nat_lit(1));
    let checker = TypeChecker::new(&env);
    assert!(checker.is_def_eq(&left, &right));
    assert!(!checker.heartbeat_spent());
    let mut tracer = CoreTracer::new(&env, 1_000_000);
    let (left, _) = tracer.check(&left).expect("left annotation");
    let (right, _) = tracer.check(&right).expect("right annotation");
    let refusal = tracer
        .conv(&left, &right)
        .expect_err("recorded producer gap");
    assert!(
        matches!(refusal, Refusal::Coverage { source_name, .. } if source_name == "conversion_rule_gap")
    );
    assert!(
        tracer.domain_problems.is_empty(),
        "coverage is not a failed domain guard"
    );
}
