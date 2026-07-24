// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    import_article, parse_article, parse_article_with_context, translate_term_with_context,
    translate_type_with_context, OtName, OtTerm, OtTranslationContext, OtType, OtVariable,
};
use crate::{Declaration, ExprKind, Name as LeanName};

const REFL_ARTICLE: &str = r#"
6
version
"x"
"A"
varType
3
def
var
1
def
varTerm
2
def
refl
4
def
"bool"
typeOp
nil
opType
5
def
"->"
typeOp
3
ref
5
ref
nil
cons
cons
opType
6
def
"->"
typeOp
3
ref
6
ref
nil
cons
cons
opType
7
def
"="
const
7
ref
constTerm
2
ref
appTerm
2
ref
appTerm
8
def
4
ref
nil
8
ref
thm
"#;

#[test]
fn parses_version_only_article() {
    let article = parse_article("6\nversion\n").expect("version-only article should parse");
    assert_eq!(article.version, 6);
    assert!(article.assumptions.is_empty());
    assert!(article.theorems.is_empty());
}

#[test]
fn parses_minimal_exported_refl_article() {
    let article = parse_article(REFL_ARTICLE).expect("minimal theorem article should parse");
    assert_eq!(article.version, 6);
    assert!(article.assumptions.is_empty());
    assert_eq!(article.theorems.len(), 1);

    let theorem = &article.theorems[0];
    assert!(theorem.hypotheses.is_empty());
    let (lhs, rhs) = theorem
        .conclusion
        .dest_eq()
        .expect("exported theorem should be an equality");
    assert_eq!(lhs, rhs);
    match lhs {
        OtTerm::Var(variable) => {
            assert_eq!(variable.name, OtName::global("x"));
            assert_eq!(variable.ty, OtType::Var(OtName::global("A")));
        }
        other => panic!("expected variable equality, found {other:?}"),
    }
}

#[test]
fn translates_hol_function_type_into_prop_and_arrow() {
    let a = OtName::global("A");
    let ty = OtType::function(OtType::Var(a.clone()), OtType::bool());
    let expr = translate_type_with_context(&ty, &OtTranslationContext::with_type_vars([a]))
        .expect("translate type");
    let ExprKind::Pi(_, domain, codomain) = expr.kind() else {
        panic!("expected arrow/pi, got {:?}", expr.kind());
    };
    assert!(matches!(domain.kind(), ExprKind::BVar(0)));
    assert!(matches!(codomain.kind(), ExprKind::Sort(level) if level.is_zero()));
}

#[test]
fn translates_lambda_term_with_type_variable_context() {
    let a = OtName::global("A");
    let binder = OtVariable::new(OtName::global("x"), OtType::Var(a.clone()));
    let term = OtTerm::abs(binder.clone(), OtTerm::var(binder));
    let expr = translate_term_with_context(&term, &OtTranslationContext::with_type_vars([a]))
        .expect("translate lambda");
    let ExprKind::Lam(_, binder_ty, body) = expr.kind() else {
        panic!("expected lambda, got {:?}", expr.kind());
    };
    assert!(matches!(binder_ty.kind(), ExprKind::BVar(0)));
    assert!(matches!(body.kind(), ExprKind::BVar(0)));
}

#[test]
fn import_pipeline_registers_support_and_exported_axioms() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let imported = import_article(&article).expect("article should import");
    assert_eq!(imported.required_mode, crate::CleanMode::Classical);
    assert!(imported.support_declarations.is_empty());
    assert_eq!(imported.theorem_declarations.len(), 1);

    match &imported.theorem_declarations[0] {
        Declaration::Axiom { name, type_, .. } => {
            assert_eq!(
                name,
                &LeanName::from_string("OpenTheory.Imported.theorem.0")
            );
            assert!(matches!(type_.kind(), ExprKind::Pi(_, _, _)));
        }
        other => panic!("expected imported theorem axiom, found {other:?}"),
    }
}

/// Article B references the refl theorem (x = x) via the `axiom` command.
/// Without context, this creates an assumption. With context from article A,
/// the axiom resolves to the proved theorem.
const DEPENDENT_ARTICLE: &str = r#"
6
version
"x"
"A"
varType
3
def
var
1
def
varTerm
2
def
"bool"
typeOp
nil
opType
5
def
"->"
typeOp
3
ref
5
ref
nil
cons
cons
opType
6
def
"->"
typeOp
3
ref
6
ref
nil
cons
cons
opType
7
def
"="
const
7
ref
constTerm
2
ref
appTerm
2
ref
appTerm
8
def
nil
8
ref
axiom
9
def
9
ref
nil
8
ref
thm
"#;

#[test]
fn test_axiom_without_context_creates_assumption() {
    let article = parse_article(DEPENDENT_ARTICLE).expect("dependent article should parse");
    // Without context, the axiom creates an assumption.
    assert_eq!(
        article.assumptions.len(),
        1,
        "axiom should produce an assumption"
    );
    assert_eq!(article.theorems.len(), 1, "thm should export a theorem");
}

#[test]
fn test_axiom_with_context_resolves_to_proved_theorem() {
    // First parse article A to get its proved theorems.
    let article_a = parse_article(REFL_ARTICLE).expect("article A should parse");
    assert_eq!(article_a.theorems.len(), 1);
    assert!(article_a.assumptions.is_empty());

    // Build context from article A's proved theorems.
    let context = article_a.proved_theorems_as_context();
    assert_eq!(
        context.len(),
        1,
        "article A should contribute one proved theorem"
    );

    // Parse article B with context from article A.
    let article_b = parse_article_with_context(DEPENDENT_ARTICLE, context)
        .expect("dependent article should parse with context");

    // With context, the axiom resolves to the proved theorem — no assumptions.
    assert!(
        article_b.assumptions.is_empty(),
        "axiom should resolve against context, not create assumption; got {} assumptions",
        article_b.assumptions.len(),
    );
    assert_eq!(
        article_b.theorems.len(),
        1,
        "thm should still export a theorem"
    );
}

#[test]
fn test_vm_note_command_executed_saturates_at_usize_max() {
    // Trust ledger 2026-06-10: arithmetic overflow (Add) @ open_theory/vm.rs:245.
    // The counter now saturates instead of panicking; its only consumer is the
    // `executed_commands > 1` Version-position check, which saturation preserves.
    let mut vm = super::vm::OtVmState {
        executed_commands: usize::MAX,
        ..Default::default()
    };
    vm.note_command_executed();
    assert_eq!(vm.executed_commands, usize::MAX);
}
