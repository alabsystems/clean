// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Mizar importer: XML parsing, AST types, and translation.

use super::importer::{MizConstantKind, MizarImportConfig, MizarImporter};
use super::translate::{
    translate_formula, translate_formula_fresh, translate_term, translate_term_fresh,
    translate_type_fresh, MizTranslationContext,
};
use super::types::*;
use super::xml_parser::{parse_article, parse_formula_xml, parse_term_xml, parse_type_xml};
use crate::types::{AxiomProfile, SourceSystem, TrustLevel};
use clean_kernel::{Expr, ExprKind, Name};

// ════════════════════════════════════════════════════════════════════════════
// XML parsing: formulas
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_pred_formula() {
    let xml = r#"<Pred kind="R" nr="1"><Var nr="1"/><Var nr="2"/></Pred>"#;
    let f = parse_formula_xml(xml).expect("should parse predicate formula");
    match f {
        MizFormula::Pred { name, args } => {
            assert_eq!(name, "R1");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn test_parse_not_formula() {
    let xml = r#"<Not><Pred kind="R" nr="1"/></Not>"#;
    let f = parse_formula_xml(xml).expect("should parse negation");
    match f {
        MizFormula::Not(inner) => {
            assert!(matches!(*inner, MizFormula::Pred { .. }));
        }
        other => panic!("expected Not, got {other:?}"),
    }
}

#[test]
fn test_parse_and_formula() {
    let xml = r#"<And><Pred kind="R" nr="1"/><Pred kind="R" nr="2"/></And>"#;
    let f = parse_formula_xml(xml).expect("should parse conjunction");
    match f {
        MizFormula::And(conjuncts) => {
            assert_eq!(conjuncts.len(), 2);
        }
        other => panic!("expected And, got {other:?}"),
    }
}

#[test]
fn test_parse_or_formula() {
    let xml = r#"<Or><Pred kind="R" nr="1"/><Pred kind="R" nr="2"/></Or>"#;
    let f = parse_formula_xml(xml).expect("should parse disjunction");
    match f {
        MizFormula::Or(disjuncts) => {
            assert_eq!(disjuncts.len(), 2);
        }
        other => panic!("expected Or, got {other:?}"),
    }
}

#[test]
fn test_parse_implies_formula() {
    let xml = r#"<Implies><Pred kind="R" nr="1"/><Pred kind="R" nr="2"/></Implies>"#;
    let f = parse_formula_xml(xml).expect("should parse implication");
    assert!(matches!(f, MizFormula::Implies(_, _)));
}

#[test]
fn test_parse_iff_formula() {
    let xml = r#"<Iff><Pred kind="R" nr="1"/><Pred kind="R" nr="2"/></Iff>"#;
    let f = parse_formula_xml(xml).expect("should parse biconditional");
    assert!(matches!(f, MizFormula::Iff(_, _)));
}

#[test]
fn test_parse_forall_formula() {
    let xml =
        r#"<For vid="x1"><Typ kind="M" nr="1"/><Pred kind="R" nr="1"><Var nr="1"/></Pred></For>"#;
    let f = parse_formula_xml(xml).expect("should parse universal quantifier");
    match f {
        MizFormula::ForAll { var, ty, body } => {
            assert_eq!(var, "x1");
            assert!(matches!(ty, MizType::Mode { .. }));
            assert!(matches!(*body, MizFormula::Pred { .. }));
        }
        other => panic!("expected ForAll, got {other:?}"),
    }
}

#[test]
fn test_parse_exists_formula() {
    let xml =
        r#"<Ex vid="x1"><Typ kind="M" nr="1"/><Pred kind="R" nr="1"><Var nr="1"/></Pred></Ex>"#;
    let f = parse_formula_xml(xml).expect("should parse existential quantifier");
    match f {
        MizFormula::Exists { var, ty, body } => {
            assert_eq!(var, "x1");
            assert!(matches!(ty, MizType::Mode { .. }));
            assert!(matches!(*body, MizFormula::Pred { .. }));
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn test_parse_is_formula() {
    let xml = r#"<Is><Var nr="1"/><Typ kind="M" nr="1"/></Is>"#;
    let f = parse_formula_xml(xml).expect("should parse type judgment");
    match f {
        MizFormula::Is { term, ty } => {
            assert!(matches!(term, MizTerm::Var(_)));
            assert!(matches!(ty, MizType::Mode { .. }));
        }
        other => panic!("expected Is, got {other:?}"),
    }
}

#[test]
fn test_parse_contradiction() {
    let xml = r#"<Contradiction/>"#;
    let f = parse_formula_xml(xml).expect("should parse contradiction");
    assert!(matches!(f, MizFormula::Contradiction));
}

#[test]
fn test_parse_thesis() {
    let xml = r#"<Thesis/>"#;
    let f = parse_formula_xml(xml).expect("should parse thesis");
    assert!(matches!(f, MizFormula::Thesis));
}

// ════════════════════════════════════════════════════════════════════════════
// XML parsing: terms
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_var_term() {
    let xml = r#"<Var nr="3"/>"#;
    let t = parse_term_xml(xml).expect("should parse variable");
    match t {
        MizTerm::Var(name) => assert_eq!(name, "x3"),
        other => panic!("expected Var, got {other:?}"),
    }
}

#[test]
fn test_parse_numeral_term() {
    let xml = r#"<Num nr="42"/>"#;
    let t = parse_term_xml(xml).expect("should parse numeral");
    match t {
        MizTerm::Numeral(n) => assert_eq!(n, 42),
        other => panic!("expected Numeral, got {other:?}"),
    }
}

#[test]
fn test_parse_functor_term() {
    let xml = r#"<Func kind="K" nr="5"><Var nr="1"/><Var nr="2"/></Func>"#;
    let t = parse_term_xml(xml).expect("should parse functor");
    match t {
        MizTerm::Functor { name, args } => {
            assert_eq!(name, "K5");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected Functor, got {other:?}"),
    }
}

#[test]
fn test_parse_aggregate_term() {
    let xml = r#"<Aggregate nr="7"><Var nr="1"/><Num nr="0"/></Aggregate>"#;
    let t = parse_term_xml(xml).expect("should parse aggregate");
    match t {
        MizTerm::Aggregate {
            struct_name,
            fields,
        } => {
            assert_eq!(struct_name, "7");
            assert_eq!(fields.len(), 2);
        }
        other => panic!("expected Aggregate, got {other:?}"),
    }
}

#[test]
fn test_parse_selector_term() {
    let xml = r#"<Selector nr="3"><Var nr="1"/></Selector>"#;
    let t = parse_term_xml(xml).expect("should parse selector");
    match t {
        MizTerm::Selector { field, arg } => {
            assert_eq!(field, "3");
            assert!(matches!(*arg, MizTerm::Var(_)));
        }
        other => panic!("expected Selector, got {other:?}"),
    }
}

#[test]
fn test_parse_the_term() {
    let xml = r#"<The><Typ kind="M" nr="1"/></The>"#;
    let t = parse_term_xml(xml).expect("should parse definite description");
    match t {
        MizTerm::The { ty } => {
            assert!(matches!(ty, MizType::Mode { .. }));
        }
        other => panic!("expected The, got {other:?}"),
    }
}

#[test]
fn test_parse_fraenkel_term() {
    let xml = r#"<Fraenkel><Typ kind="M" nr="1" vid="x1"/><Var nr="1"/><Pred kind="R" nr="1"><Var nr="1"/></Pred></Fraenkel>"#;
    let t = parse_term_xml(xml).expect("should parse Fraenkel term");
    match t {
        MizTerm::Fraenkel {
            term,
            vars,
            formula,
        } => {
            assert_eq!(vars.len(), 1);
            assert!(matches!(*term, MizTerm::Var(_)));
            assert!(matches!(*formula, MizFormula::Pred { .. }));
        }
        other => panic!("expected Fraenkel, got {other:?}"),
    }
}

#[test]
fn test_parse_it_term() {
    let xml = r#"<It/>"#;
    let t = parse_term_xml(xml).expect("should parse It");
    assert!(matches!(t, MizTerm::It));
}

// ════════════════════════════════════════════════════════════════════════════
// XML parsing: types
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_mode_type() {
    let xml = r#"<Typ kind="M" nr="5"><Var nr="1"/></Typ>"#;
    let ty = parse_type_xml(xml).expect("should parse mode type");
    match ty {
        MizType::Mode { name, args } => {
            assert_eq!(name, "5");
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Mode, got {other:?}"),
    }
}

#[test]
fn test_parse_struct_type() {
    let xml = r#"<Typ kind="G" nr="3"/>"#;
    let ty = parse_type_xml(xml).expect("should parse struct type");
    match ty {
        MizType::Struct { name, args } => {
            assert_eq!(name, "3");
            assert!(args.is_empty());
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn test_parse_set_type() {
    let xml = r#"<Typ kind="set" nr=""/>"#;
    let ty = parse_type_xml(xml).expect("should parse set type");
    assert!(matches!(ty, MizType::Set));
}

#[test]
fn test_parse_clustered_type() {
    let xml =
        r#"<Typ kind="M" nr="1"><Cluster><Adjective nr="2"/><Adjective nr="3"/></Cluster></Typ>"#;
    let ty = parse_type_xml(xml).expect("should parse clustered type");
    match ty {
        MizType::Clustered { adjectives, base } => {
            assert_eq!(adjectives.len(), 2);
            assert!(matches!(*base, MizType::Mode { .. }));
        }
        other => panic!("expected Clustered, got {other:?}"),
    }
}

#[test]
fn test_parse_negated_adjective() {
    let xml = r#"<Typ kind="M" nr="1"><Cluster><Adjective nr="2" value="false"/></Cluster></Typ>"#;
    let ty = parse_type_xml(xml).expect("should parse negated adjective");
    match ty {
        MizType::Clustered { adjectives, .. } => {
            assert_eq!(adjectives.len(), 1);
            assert!(adjectives[0].negated);
        }
        other => panic!("expected Clustered, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// XML parsing: full article
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_empty_article() {
    let xml = r#"<Article aid="TEST"/>"#;
    let article = parse_article(xml).expect("should parse empty article");
    assert_eq!(article.name, "TEST");
    assert!(article.items.is_empty());
}

#[test]
fn test_parse_article_with_environ() {
    let xml = r#"<Article aid="XBOOLE_0">
  <Environ>
    <Vocabularies>
      <Directive name="XBOOLE_0"/>
      <Directive name="TARSKI"/>
    </Vocabularies>
    <Constructors>
      <Directive name="XBOOLE_0"/>
    </Constructors>
  </Environ>
</Article>"#;
    let article = parse_article(xml).expect("should parse article with environ");
    assert_eq!(article.name, "XBOOLE_0");
    assert_eq!(article.environ.vocabularies.len(), 2);
    assert_eq!(article.environ.vocabularies[0], "XBOOLE_0");
    assert_eq!(article.environ.vocabularies[1], "TARSKI");
    assert_eq!(article.environ.constructors.len(), 1);
}

#[test]
fn test_parse_article_with_theorem() {
    let xml = r#"<Article aid="TEST">
  <Theorem nr="1">
    <For vid="x1">
      <Typ kind="M" nr="1"/>
      <Pred kind="R" nr="1"><Var nr="1"/></Pred>
    </For>
  </Theorem>
</Article>"#;
    let article = parse_article(xml).expect("should parse article with theorem");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Theorem(thm) => {
            assert_eq!(thm.label, "1");
            assert!(matches!(thm.proposition, MizFormula::ForAll { .. }));
        }
        other => panic!("expected Theorem, got {other:?}"),
    }
}

#[test]
fn test_parse_article_with_xml_decl() {
    let xml = r#"<?xml version="1.0"?>
<Article aid="TEST"/>"#;
    let article = parse_article(xml).expect("should handle XML declaration");
    assert_eq!(article.name, "TEST");
}

// ════════════════════════════════════════════════════════════════════════════
// Nested formula parsing
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_nested_formulas() {
    let xml = r#"<Implies>
  <And>
    <Pred kind="R" nr="1"><Var nr="1"/></Pred>
    <Pred kind="R" nr="2"><Var nr="2"/></Pred>
  </And>
  <Or>
    <Pred kind="R" nr="3"/>
    <Not><Pred kind="R" nr="4"/></Not>
  </Or>
</Implies>"#;
    let f = parse_formula_xml(xml).expect("should parse nested formula");
    match f {
        MizFormula::Implies(lhs, rhs) => {
            assert!(matches!(*lhs, MizFormula::And(_)));
            match *rhs {
                MizFormula::Or(ref disj) => {
                    assert_eq!(disj.len(), 2);
                    assert!(matches!(disj[1], MizFormula::Not(_)));
                }
                _ => panic!("expected Or on RHS"),
            }
        }
        other => panic!("expected Implies, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Translation: formulas
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_forall() {
    let formula = MizFormula::ForAll {
        var: "x".to_owned(),
        ty: MizType::Set,
        body: Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![MizTerm::Var("x".to_owned())],
        }),
    };
    let expr = translate_formula_fresh(&formula).expect("should translate ForAll");
    // Should produce Pi(Default, Type, App(Const("Mizar.Pred.P"), BVar(0)))
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_translate_exists() {
    let formula = MizFormula::Exists {
        var: "x".to_owned(),
        ty: MizType::Set,
        body: Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![MizTerm::Var("x".to_owned())],
        }),
    };
    let expr = translate_formula_fresh(&formula).expect("should translate Exists");
    // Should produce App(Const("Exists"), Lam(Default, Type, App(Const("Mizar.Pred.P"), BVar(0))))
    match expr.kind() {
        ExprKind::App(func, _arg) => {
            assert!(
                matches!(func.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Exists"))
            );
        }
        other => panic!("expected App(Exists, ...), got {other:?}"),
    }
}

#[test]
fn test_translate_not() {
    let formula = MizFormula::Not(Box::new(MizFormula::Pred {
        name: "P".to_owned(),
        args: vec![],
    }));
    let expr = translate_formula_fresh(&formula).expect("should translate Not");
    // Not P = P -> False = Pi(Default, App(Const("Mizar.Pred.P")), Const("False"))
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_translate_and() {
    let formula = MizFormula::And(vec![
        MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![],
        },
        MizFormula::Pred {
            name: "Q".to_owned(),
            args: vec![],
        },
    ]);
    let expr = translate_formula_fresh(&formula).expect("should translate And");
    // And(P, Q) = App(App(Const("And"), P), Q)
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected */ }
        other => panic!("expected App for And, got {other:?}"),
    }
}

#[test]
fn test_translate_or() {
    let formula = MizFormula::Or(vec![
        MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![],
        },
        MizFormula::Pred {
            name: "Q".to_owned(),
            args: vec![],
        },
    ]);
    let expr = translate_formula_fresh(&formula).expect("should translate Or");
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected */ }
        other => panic!("expected App for Or, got {other:?}"),
    }
}

#[test]
fn test_translate_implies() {
    let formula = MizFormula::Implies(
        Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![],
        }),
        Box::new(MizFormula::Pred {
            name: "Q".to_owned(),
            args: vec![],
        }),
    );
    let expr = translate_formula_fresh(&formula).expect("should translate Implies");
    // P implies Q = Pi(Default, P, Q)
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_translate_contradiction() {
    let formula = MizFormula::Contradiction;
    let expr = translate_formula_fresh(&formula).expect("should translate Contradiction");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("False"));
        }
        other => panic!("expected Const(False), got {other:?}"),
    }
}

#[test]
fn test_translate_empty_and() {
    let formula = MizFormula::And(vec![]);
    let expr = translate_formula_fresh(&formula).expect("should translate empty And");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("True"));
        }
        other => panic!("expected Const(True), got {other:?}"),
    }
}

#[test]
fn test_translate_empty_or() {
    let formula = MizFormula::Or(vec![]);
    let expr = translate_formula_fresh(&formula).expect("should translate empty Or");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("False"));
        }
        other => panic!("expected Const(False), got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Translation: terms
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_bound_var() {
    let mut ctx = MizTranslationContext::new();
    ctx.add_predicate("P", Name::from_string("P"));

    // Simulate: for x being set holds P(x)
    // We need to translate the body after pushing x.
    let term = MizTerm::Var("x".to_owned());

    // Push a local to simulate being inside a binder.
    // Access internal push_local directly would need pub(crate).
    // Instead, test through translate_formula which manages the context.
    let formula = MizFormula::ForAll {
        var: "x".to_owned(),
        ty: MizType::Set,
        body: Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![term],
        }),
    };
    let expr = translate_formula(&mut ctx, &formula).expect("should translate with bound var");
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
}

#[test]
fn test_translate_free_var() {
    // A variable not in scope becomes a constant reference.
    let term = MizTerm::Var("y".to_owned());
    let expr = translate_term_fresh(&term).expect("should translate free var");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("y"));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_translate_numeral() {
    let term = MizTerm::Numeral(42);
    let expr = translate_term_fresh(&term).expect("should translate numeral");
    assert!(matches!(expr.kind(), ExprKind::Lit(_)));
}

#[test]
fn test_translate_functor() {
    let term = MizTerm::Functor {
        name: "add".to_owned(),
        args: vec![MizTerm::Numeral(1), MizTerm::Numeral(2)],
    };
    let expr = translate_term_fresh(&term).expect("should translate functor");
    // App(App(Const("Mizar.Func.add"), Lit(1)), Lit(2))
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected */ }
        other => panic!("expected App for functor, got {other:?}"),
    }
}

#[test]
fn test_translate_it() {
    let term = MizTerm::It;
    let expr = translate_term_fresh(&term).expect("should translate It");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Mizar.it"));
        }
        other => panic!("expected Const(Mizar.it), got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Translation: types
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_set_type() {
    let ty = MizType::Set;
    let expr = translate_type_fresh(&ty).expect("should translate Set");
    // Set -> Type (Sort 1)
    assert!(matches!(expr.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_translate_mode_type() {
    let ty = MizType::Mode {
        name: "Nat".to_owned(),
        args: vec![],
    };
    let expr = translate_type_fresh(&ty).expect("should translate Mode");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Mizar.Mode.Nat"));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_translate_mode_with_args() {
    let ty = MizType::Mode {
        name: "Element".to_owned(),
        args: vec![MizTerm::Var("NAT".to_owned())],
    };
    let expr = translate_type_fresh(&ty).expect("should translate Mode with args");
    // App(Const("Mizar.Mode.Element"), Const("NAT"))
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected */ }
        other => panic!("expected App for mode with args, got {other:?}"),
    }
}

#[test]
fn test_translate_struct_type() {
    let ty = MizType::Struct {
        name: "TopSpace".to_owned(),
        args: vec![],
    };
    let expr = translate_type_fresh(&ty).expect("should translate Struct");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Mizar.Struct.TopSpace"));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_translate_clustered_type() {
    let ty = MizType::Clustered {
        adjectives: vec![MizAdjective {
            name: "non-empty".to_owned(),
            negated: false,
            args: vec![],
        }],
        base: Box::new(MizType::Mode {
            name: "set".to_owned(),
            args: vec![],
        }),
    };
    let expr = translate_type_fresh(&ty).expect("should translate Clustered");
    // Mizar.Subtype(base, lam x : base => adj(x))
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected: App(App(Subtype, base), lam) */ }
        other => panic!("expected App for clustered type, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Round-trip: XML -> AST -> verify structure
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_roundtrip_forall_pred() {
    let xml = r#"<For vid="x">
  <Typ kind="M" nr="1"/>
  <Pred kind="R" nr="1"><Var nr="1"/></Pred>
</For>"#;
    let formula = parse_formula_xml(xml).expect("should parse");
    let expr = translate_formula_fresh(&formula).expect("should translate");

    // Verify structure: Pi(Default, Mode, App(Pred, BVar(0)))
    match expr.kind() {
        ExprKind::Pi(_, ty, body) => {
            // Type should be a mode constant
            assert!(matches!(ty.kind(), ExprKind::Const(_, _)));
            // Body should be an application
            assert!(matches!(body.kind(), ExprKind::App(_, _)));
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_roundtrip_nested_quantifiers() {
    let xml = r#"<For vid="x">
  <Typ kind="M" nr="1"/>
  <For vid="y">
    <Typ kind="M" nr="2"/>
    <Pred kind="R" nr="1"><Var nr="1"/><Var nr="2"/></Pred>
  </For>
</For>"#;
    let formula = parse_formula_xml(xml).expect("should parse nested quantifiers");
    let expr = translate_formula_fresh(&formula).expect("should translate nested quantifiers");

    // Should be Pi(_, _, Pi(_, _, App(App(Pred, _), _)))
    match expr.kind() {
        ExprKind::Pi(_, _, body) => {
            assert!(matches!(body.kind(), ExprKind::Pi(_, _, _)));
        }
        other => panic!("expected nested Pi, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Edge cases
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_xml_with_comments() {
    let xml = r#"<!-- A comment --><Pred kind="R" nr="1"/><!-- Another comment -->"#;
    let f = parse_formula_xml(xml).expect("should handle comments");
    assert!(matches!(f, MizFormula::Pred { .. }));
}

#[test]
fn test_parse_xml_entities() {
    // Test XML entity unescaping in attribute values.
    let xml = r#"<Pred kind="R" nr="1&amp;2"/>"#;
    let f = parse_formula_xml(xml).expect("should unescape entities");
    match f {
        MizFormula::Pred { name, .. } => {
            assert_eq!(name, "R1&2");
        }
        other => panic!("expected Pred, got {other:?}"),
    }
}

#[test]
fn test_parse_malformed_xml_error() {
    let xml = r#"<Not>"#; // Missing closing tag
    let result = parse_formula_xml(xml);
    assert!(result.is_err());
}

#[test]
fn test_parse_unknown_formula_tag_error() {
    let xml = r#"<Unknown/>"#;
    let result = parse_formula_xml(xml);
    assert!(result.is_err());
}

#[test]
fn test_translate_with_registered_predicate() {
    let mut ctx = MizTranslationContext::new();
    ctx.add_predicate("eq", Name::from_string("Eq"));

    let formula = MizFormula::Pred {
        name: "eq".to_owned(),
        args: vec![MizTerm::Numeral(1), MizTerm::Numeral(2)],
    };
    let expr = translate_formula(&mut ctx, &formula).expect("should use registered name");
    // Should use Const("Eq") not Const("Mizar.Pred.eq")
    fn find_head_const(e: &Expr) -> Option<&Name> {
        match e.kind() {
            ExprKind::App(f, _) => find_head_const(f),
            ExprKind::Const(name, _) => Some(name),
            _ => None,
        }
    }
    let head = find_head_const(&expr).expect("should have a head constant");
    assert_eq!(*head, Name::from_string("Eq"));
}

#[test]
fn test_translate_with_registered_functor() {
    let mut ctx = MizTranslationContext::new();
    ctx.add_functor("plus", Name::from_string("Nat.add"));

    let term = MizTerm::Functor {
        name: "plus".to_owned(),
        args: vec![MizTerm::Numeral(1), MizTerm::Numeral(2)],
    };
    let expr = translate_term(&mut ctx, &term).expect("should use registered name");
    fn find_head_const(e: &Expr) -> Option<&Name> {
        match e.kind() {
            ExprKind::App(f, _) => find_head_const(f),
            ExprKind::Const(name, _) => Some(name),
            _ => None,
        }
    }
    let head = find_head_const(&expr).expect("should have a head constant");
    assert_eq!(*head, Name::from_string("Nat.add"));
}

#[test]
fn test_translate_selector_term() {
    let term = MizTerm::Selector {
        field: "carrier".to_owned(),
        arg: Box::new(MizTerm::Var("T".to_owned())),
    };
    let expr = translate_term_fresh(&term).expect("should translate selector");
    match expr.kind() {
        ExprKind::App(func, _arg) => {
            assert!(
                matches!(func.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Mizar.Selector.carrier"))
            );
        }
        other => panic!("expected App for selector, got {other:?}"),
    }
}

#[test]
fn test_translate_aggregate_term() {
    let term = MizTerm::Aggregate {
        struct_name: "TopSpace".to_owned(),
        fields: vec![MizTerm::Numeral(1)],
    };
    let expr = translate_term_fresh(&term).expect("should translate aggregate");
    match expr.kind() {
        ExprKind::App(func, _) => {
            assert!(
                matches!(func.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Mizar.Struct.TopSpace.mk"))
            );
        }
        other => panic!("expected App for aggregate, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Serde round-trip for AST types
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_serde_roundtrip_formula() {
    let formula = MizFormula::ForAll {
        var: "x".to_owned(),
        ty: MizType::Set,
        body: Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![MizTerm::Var("x".to_owned())],
        }),
    };
    let json = serde_json::to_string(&formula).expect("should serialize");
    let deserialized: MizFormula = serde_json::from_str(&json).expect("should deserialize");
    assert_eq!(formula, deserialized);
}

#[test]
fn test_serde_roundtrip_article() {
    let article = MizArticle {
        name: "TEST".to_owned(),
        environ: MizEnviron {
            vocabularies: vec!["XBOOLE_0".to_owned()],
            ..MizEnviron::default()
        },
        items: vec![MizItem::Theorem(MizTheorem {
            label: "T1".to_owned(),
            proposition: MizFormula::Contradiction,
            proof: None,
        })],
    };
    let json = serde_json::to_string(&article).expect("should serialize");
    let deserialized: MizArticle = serde_json::from_str(&json).expect("should deserialize");
    assert_eq!(article, deserialized);
}

// ════════════════════════════════════════════════════════════════════════════
// Additional formula translation tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_iff() {
    let formula = MizFormula::Iff(
        Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![],
        }),
        Box::new(MizFormula::Pred {
            name: "Q".to_owned(),
            args: vec![],
        }),
    );
    let expr = translate_formula_fresh(&formula).expect("should translate Iff");
    fn find_head_const(e: &Expr) -> Option<&Name> {
        match e.kind() {
            ExprKind::App(f, _) => find_head_const(f),
            ExprKind::Const(name, _) => Some(name),
            _ => None,
        }
    }
    let head = find_head_const(&expr).expect("should have head constant");
    assert_eq!(*head, Name::from_string("Iff"));
}

#[test]
fn test_translate_is_formula() {
    let formula = MizFormula::Is {
        term: MizTerm::Var("x".to_owned()),
        ty: MizType::Mode {
            name: "Nat".to_owned(),
            args: vec![],
        },
    };
    let expr = translate_formula_fresh(&formula).expect("should translate Is");
    fn find_head_const(e: &Expr) -> Option<&Name> {
        match e.kind() {
            ExprKind::App(f, _) => find_head_const(f),
            ExprKind::Const(name, _) => Some(name),
            _ => None,
        }
    }
    let head = find_head_const(&expr).expect("should have head constant");
    assert_eq!(*head, Name::from_string("Mizar.Is"));
}

#[test]
fn test_translate_thesis() {
    let formula = MizFormula::Thesis;
    let expr = translate_formula_fresh(&formula).expect("should translate Thesis");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Mizar.Thesis"));
        }
        other => panic!("expected Const(Mizar.Thesis), got {other:?}"),
    }
}

#[test]
fn test_translate_triple_and() {
    let formula = MizFormula::And(vec![
        MizFormula::Pred {
            name: "A".to_owned(),
            args: vec![],
        },
        MizFormula::Pred {
            name: "B".to_owned(),
            args: vec![],
        },
        MizFormula::Pred {
            name: "C".to_owned(),
            args: vec![],
        },
    ]);
    let expr = translate_formula_fresh(&formula).expect("should translate triple And");
    // Nested And application: And(And(A, B), C)
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected */ }
        other => panic!("expected nested App for triple And, got {other:?}"),
    }
}

#[test]
fn test_translate_nested_forall_exists() {
    let formula = MizFormula::ForAll {
        var: "x".to_owned(),
        ty: MizType::Set,
        body: Box::new(MizFormula::Exists {
            var: "y".to_owned(),
            ty: MizType::Set,
            body: Box::new(MizFormula::Pred {
                name: "P".to_owned(),
                args: vec![MizTerm::Var("x".to_owned()), MizTerm::Var("y".to_owned())],
            }),
        }),
    };
    let expr = translate_formula_fresh(&formula).expect("should translate nested quantifiers");
    match expr.kind() {
        ExprKind::Pi(_, _, body) => {
            assert!(matches!(body.kind(), ExprKind::App(func, _) if {
                matches!(func.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Exists"))
            }));
        }
        other => panic!("expected Pi then Exists, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Additional term translation tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_numeral_zero() {
    let term = MizTerm::Numeral(0);
    let expr = translate_term_fresh(&term).expect("should translate zero");
    assert!(matches!(expr.kind(), ExprKind::Lit(_)));
}

#[test]
fn test_translate_negative_numeral() {
    let term = MizTerm::Numeral(-5);
    let expr = translate_term_fresh(&term).expect("should translate negative numeral");
    assert!(matches!(expr.kind(), ExprKind::Lit(_)));
}

#[test]
fn test_translate_functor_no_args() {
    let term = MizTerm::Functor {
        name: "empty_set".to_owned(),
        args: vec![],
    };
    let expr = translate_term_fresh(&term).expect("should translate nullary functor");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Mizar.Func.empty_set"));
        }
        other => panic!("expected Const for nullary functor, got {other:?}"),
    }
}

#[test]
fn test_translate_the_term() {
    let term = MizTerm::The {
        ty: MizType::Mode {
            name: "Element".to_owned(),
            args: vec![],
        },
    };
    let expr = translate_term_fresh(&term).expect("should translate The");
    match expr.kind() {
        ExprKind::App(func, _) => {
            assert!(matches!(
                func.kind(),
                ExprKind::Const(name, _) if *name == Name::from_string("Mizar.the")
            ));
        }
        other => panic!("expected App(Mizar.the, ...), got {other:?}"),
    }
}

#[test]
fn test_translate_fraenkel_term() {
    let term = MizTerm::Fraenkel {
        term: Box::new(MizTerm::Var("x".to_owned())),
        vars: vec![("x".to_owned(), MizType::Set)],
        formula: Box::new(MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![MizTerm::Var("x".to_owned())],
        }),
    };
    let expr = translate_term_fresh(&term).expect("should translate Fraenkel");
    match expr.kind() {
        ExprKind::App(func, _) => {
            assert!(matches!(
                func.kind(),
                ExprKind::Const(name, _) if *name == Name::from_string("Mizar.fraenkel")
            ));
        }
        other => panic!("expected App(Mizar.fraenkel, ...), got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Additional type translation tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_struct_type_with_args() {
    let ty = MizType::Struct {
        name: "TopSpace".to_owned(),
        args: vec![MizTerm::Var("X".to_owned())],
    };
    let expr = translate_type_fresh(&ty).expect("should translate Struct with args");
    match expr.kind() {
        ExprKind::App(func, _) => {
            assert!(matches!(
                func.kind(),
                ExprKind::Const(name, _) if *name == Name::from_string("Mizar.Struct.TopSpace")
            ));
        }
        other => panic!("expected App for struct with args, got {other:?}"),
    }
}

#[test]
fn test_translate_clustered_negated_adjective() {
    let ty = MizType::Clustered {
        adjectives: vec![MizAdjective {
            name: "empty".to_owned(),
            negated: true,
            args: vec![],
        }],
        base: Box::new(MizType::Set),
    };
    let expr = translate_type_fresh(&ty).expect("should translate negated adjective cluster");
    match expr.kind() {
        ExprKind::App(_, _) => { /* expected */ }
        other => panic!("expected App for negated clustered type, got {other:?}"),
    }
}

#[test]
fn test_translate_clustered_empty_adjectives() {
    let ty = MizType::Clustered {
        adjectives: vec![],
        base: Box::new(MizType::Set),
    };
    let expr = translate_type_fresh(&ty).expect("should translate empty cluster");
    assert!(matches!(expr.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_translate_with_registered_mode() {
    let mut ctx = MizTranslationContext::new();
    ctx.add_mode("Nat", Name::from_string("Lean.Nat"));

    let ty = MizType::Mode {
        name: "Nat".to_owned(),
        args: vec![],
    };
    let expr =
        super::translate::translate_type(&mut ctx, &ty).expect("should use registered mode name");
    match expr.kind() {
        ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Lean.Nat"));
        }
        other => panic!("expected Const(Lean.Nat), got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Import pipeline: MizarImporter
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_importer_empty_article() {
    let importer = MizarImporter::with_defaults("EMPTY");
    let xml = r#"<Article aid="EMPTY"/>"#;
    let result = importer
        .import_article_xml(xml)
        .expect("should import empty article");
    assert_eq!(result.article_name, "EMPTY");
    assert!(result.constants.is_empty());
    assert_eq!(result.theorem_count, 0);
    assert_eq!(result.definition_count, 0);
    assert_eq!(result.axiomatized_count, 0);
    assert_eq!(result.total_constants(), 0);
}

#[test]
fn test_importer_article_with_theorem() {
    let importer = MizarImporter::with_defaults("TEST");
    let xml = r#"<Article aid="TEST">
  <Theorem nr="1">
    <For vid="x1">
      <Typ kind="M" nr="1"/>
      <Pred kind="R" nr="1"><Var nr="1"/></Pred>
    </For>
  </Theorem>
</Article>"#;
    let result = importer
        .import_article_xml(xml)
        .expect("should import article with theorem");

    assert_eq!(result.theorem_count, 1);
    assert_eq!(result.total_constants(), 1);

    let c = &result.constants[0];
    assert_eq!(c.kind, MizConstantKind::Theorem);
    assert!(c.name.contains("TEST"));
    assert_eq!(c.provenance.source, SourceSystem::Mizar);
    assert_eq!(c.trust_level, TrustLevel::PartiallyAxiomatized);
    assert!(c.axiom_profile.contains(AxiomProfile::MIZAR_SOFT_TYPE));
}

#[test]
fn test_importer_axiomatized_theorem() {
    let config = MizarImportConfig {
        translate_proofs: false,
        axiomatize_unproved: true,
    };
    let importer = MizarImporter::new("AX", config);
    let xml = r#"<Article aid="AX">
  <Theorem nr="1">
    <Pred kind="R" nr="1"/>
  </Theorem>
</Article>"#;
    let result = importer.import_article_xml(xml).expect("should import");
    assert_eq!(result.axiomatized_count, 1);
    let c = &result.constants[0];
    assert_eq!(c.trust_level, TrustLevel::PartiallyAxiomatized);
    assert!(c.axiom_profile.contains(AxiomProfile::MIZAR_SOFT_TYPE));
}

#[test]
fn test_importer_article_name_from_xml() {
    let importer = MizarImporter::with_defaults("FALLBACK");
    let xml = r#"<Article aid="FROMXML"/>"#;
    let result = importer.import_article_xml(xml).expect("should import");
    // Article name should come from XML when present.
    assert_eq!(result.article_name, "FROMXML");
}

#[test]
fn test_importer_article_name_fallback() {
    let importer = MizarImporter::with_defaults("FALLBACK");
    let xml = r#"<Article aid=""/>"#;
    let result = importer.import_article_xml(xml).expect("should import");
    // Empty aid in XML => use importer's article_name.
    assert_eq!(result.article_name, "FALLBACK");
}

#[test]
fn test_importer_xml_parse_error() {
    let importer = MizarImporter::with_defaults("TEST");
    let result = importer.import_article_xml("<garbage");
    assert!(result.is_err());
}

#[test]
fn test_importer_config_defaults() {
    let config = MizarImportConfig::default();
    assert!(!config.translate_proofs);
    assert!(config.axiomatize_unproved);
}

#[test]
fn test_importer_result_diagnostics() {
    let importer = MizarImporter::with_defaults("TEST");
    let xml = r#"<Article aid="TEST"/>"#;
    let result = importer.import_article_xml(xml).expect("should import");
    assert!(!result.has_diagnostics());
}

#[test]
fn test_importer_result_kernel_verified_count() {
    let importer = MizarImporter::with_defaults("TEST");
    let xml = r#"<Article aid="TEST"/>"#;
    let result = importer.import_article_xml(xml).expect("should import");
    assert_eq!(result.kernel_verified_count(), 0);
}

#[test]
fn test_importer_result_partially_axiomatized_count() {
    let config = MizarImportConfig {
        translate_proofs: false,
        axiomatize_unproved: true,
    };
    let importer = MizarImporter::new("TEST", config);
    let xml = r#"<Article aid="TEST">
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
  <Theorem nr="2"><Pred kind="R" nr="2"/></Theorem>
</Article>"#;
    let result = importer.import_article_xml(xml).expect("should import");
    assert_eq!(result.partially_axiomatized_count(), 2);
}

#[test]
fn test_importer_constant_kinds() {
    assert_ne!(MizConstantKind::Theorem, MizConstantKind::Definition);
    assert_ne!(MizConstantKind::Scheme, MizConstantKind::Registration);
    assert_ne!(MizConstantKind::Notation, MizConstantKind::Theorem);
}

#[test]
fn test_translate_article_item_provenance() {
    use super::importer::MizarImportConfig;
    use super::translate::translate_article_item;
    let mut ctx = MizTranslationContext::new();
    let config = MizarImportConfig::default();
    let item = MizItem::Theorem(MizTheorem {
        label: "42".to_owned(),
        proposition: MizFormula::Pred {
            name: "P".to_owned(),
            args: vec![],
        },
        proof: None,
    });
    let result =
        translate_article_item(&mut ctx, &item, "META", &config).expect("should translate");
    let c = result.expect("should produce a constant");
    assert_eq!(c.name, "Mizar.META.T42");
    assert_eq!(c.provenance.source, SourceSystem::Mizar);
    assert_eq!(c.provenance.original_name, "Mizar.META.T42");
    assert!(c.provenance.source_file.as_deref() == Some("META.miz"));
    assert!(c.axiom_profile.contains(AxiomProfile::MIZAR_SOFT_TYPE));
    assert_eq!(c.trust_level, TrustLevel::PartiallyAxiomatized);
}

// ════════════════════════════════════════════════════════════════════════════
// Article-level parsing tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_article_with_environ_tarski() {
    let xml = r#"<Article aid="TARSKI">
  <Environ>
    <Vocabularies>
      <Directive name="TARSKI"/>
      <Directive name="XBOOLE_0"/>
    </Vocabularies>
    <Constructors>
      <Directive name="TARSKI"/>
    </Constructors>
  </Environ>
</Article>"#;
    let article = parse_article(xml).expect("should parse article with environ");
    assert_eq!(article.name, "TARSKI");
    assert_eq!(article.environ.vocabularies.len(), 2);
    assert_eq!(article.environ.vocabularies[0], "TARSKI");
    assert_eq!(article.environ.vocabularies[1], "XBOOLE_0");
    assert_eq!(article.environ.constructors.len(), 1);
    assert!(article.items.is_empty());
}

#[test]
fn test_parse_article_empty() {
    let xml = r#"<Article aid="EMPTY"/>"#;
    let article = parse_article(xml).expect("should parse empty article");
    assert_eq!(article.name, "EMPTY");
    assert!(article.items.is_empty());
    assert!(article.is_empty());
}

#[test]
fn test_parse_article_multiple_theorems() {
    let xml = r#"<Article aid="MULTI">
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
  <Theorem nr="2"><Pred kind="R" nr="2"/></Theorem>
  <Theorem nr="3"><Not><Pred kind="R" nr="3"/></Not></Theorem>
</Article>"#;
    let article = parse_article(xml).expect("should parse multiple theorems");
    assert_eq!(article.items.len(), 3);
    let counts = article.item_counts();
    assert_eq!(counts.theorems, 3);
    assert_eq!(counts.total(), 3);
}

#[test]
fn test_parse_article_item_counts() {
    let article = MizArticle {
        name: "COUNTS".to_owned(),
        environ: MizEnviron::default(),
        items: vec![
            MizItem::Theorem(MizTheorem {
                label: "T1".to_owned(),
                proposition: MizFormula::Contradiction,
                proof: None,
            }),
            MizItem::Definition(MizDefinition::ModeDef {
                name: "M".to_owned(),
                params: vec![],
                expansion: None,
            }),
            MizItem::Scheme(MizScheme {
                name: "S".to_owned(),
                premises: vec![],
                conclusion: MizFormula::Thesis,
            }),
            MizItem::Registration(MizRegistration::Existential {
                adjectives: vec![],
                ty: MizType::Set,
            }),
            MizItem::Notation(MizNotation::Synonym {
                new_name: "new".to_owned(),
                original: "old".to_owned(),
            }),
        ],
    };
    let counts = article.item_counts();
    assert_eq!(counts.theorems, 1);
    assert_eq!(counts.definitions, 1);
    assert_eq!(counts.schemes, 1);
    assert_eq!(counts.registrations, 1);
    assert_eq!(counts.notations, 1);
    assert_eq!(counts.total(), 5);
    assert!(!article.is_empty());
}

// ════════════════════════════════════════════════════════════════════════════
// Registration parsing tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_existential_registration() {
    let xml = r#"<Article aid="REG">
  <Registration>
    <ExistentialRegistration>
      <Adjective nr="empty"/>
      <Typ kind="M" nr="1"/>
    </ExistentialRegistration>
  </Registration>
</Article>"#;
    let article = parse_article(xml).expect("should parse existential registration");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Registration(MizRegistration::Existential { adjectives, ty }) => {
            assert_eq!(adjectives.len(), 1);
            assert_eq!(adjectives[0].name, "empty");
            assert!(matches!(ty, MizType::Mode { .. }));
        }
        other => panic!("expected Existential registration, got {other:?}"),
    }
}

#[test]
fn test_parse_conditional_registration() {
    let xml = r#"<Article aid="REG">
  <Registration>
    <ConditionalRegistration>
      <Cluster><Adjective nr="finite"/></Cluster>
      <Cluster><Adjective nr="non-empty"/></Cluster>
      <Typ kind="M" nr="1"/>
    </ConditionalRegistration>
  </Registration>
</Article>"#;
    let article = parse_article(xml).expect("should parse conditional registration");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Registration(MizRegistration::Conditional {
            antecedent,
            consequent,
            ty: _,
        }) => {
            assert_eq!(antecedent.len(), 1);
            assert_eq!(antecedent[0].name, "finite");
            assert_eq!(consequent.len(), 1);
            assert_eq!(consequent[0].name, "non-empty");
        }
        other => panic!("expected Conditional registration, got {other:?}"),
    }
}

#[test]
fn test_parse_functorial_registration() {
    let xml = r#"<Article aid="REG">
  <Registration>
    <FunctorialRegistration>
      <Func kind="K" nr="1"/>
      <Adjective nr="positive"/>
    </FunctorialRegistration>
  </Registration>
</Article>"#;
    let article = parse_article(xml).expect("should parse functorial registration");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Registration(MizRegistration::Functorial { term, adjectives }) => {
            assert!(matches!(term, MizTerm::Functor { .. }));
            assert_eq!(adjectives.len(), 1);
            assert_eq!(adjectives[0].name, "positive");
        }
        other => panic!("expected Functorial registration, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Notation parsing tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_synonym_notation() {
    let xml = r#"<Article aid="NOT">
  <Notation>
    <Synonym nr="is_subset_of" origin="c="/>
  </Notation>
</Article>"#;
    let article = parse_article(xml).expect("should parse synonym notation");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Notation(MizNotation::Synonym { new_name, original }) => {
            assert_eq!(new_name, "is_subset_of");
            assert_eq!(original, "c=");
        }
        other => panic!("expected Synonym notation, got {other:?}"),
    }
}

#[test]
fn test_parse_antonym_notation() {
    let xml = r#"<Article aid="NOT">
  <Notation>
    <Antonym nr="is_not_empty" origin="empty"/>
  </Notation>
</Article>"#;
    let article = parse_article(xml).expect("should parse antonym notation");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Notation(MizNotation::Antonym { new_name, original }) => {
            assert_eq!(new_name, "is_not_empty");
            assert_eq!(original, "empty");
        }
        other => panic!("expected Antonym notation, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Scheme parsing and translation tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_scheme_with_premises() {
    let xml = r#"<Article aid="SCH">
  <Scheme nr="1">
    <SchemePremises>
      <Pred kind="R" nr="1"/>
    </SchemePremises>
    <Pred kind="R" nr="2"/>
  </Scheme>
</Article>"#;
    let article = parse_article(xml).expect("should parse scheme");
    assert_eq!(article.items.len(), 1);
    match &article.items[0] {
        MizItem::Scheme(sch) => {
            assert_eq!(sch.name, "1");
            assert_eq!(sch.premises.len(), 1);
            assert!(matches!(&sch.conclusion, MizFormula::Pred { name, .. } if name == "R2"));
        }
        other => panic!("expected Scheme, got {other:?}"),
    }
}

#[test]
fn test_parse_scheme_no_premises() {
    let xml = r#"<Article aid="SCH">
  <Scheme nr="1">
    <Pred kind="R" nr="1"/>
  </Scheme>
</Article>"#;
    let article = parse_article(xml).expect("should parse scheme without premises");
    match &article.items[0] {
        MizItem::Scheme(sch) => {
            assert!(sch.premises.is_empty());
            assert!(matches!(&sch.conclusion, MizFormula::Pred { .. }));
        }
        other => panic!("expected Scheme, got {other:?}"),
    }
}

#[test]
fn test_scheme_translation() {
    let scheme = MizScheme {
        name: "Induction".to_owned(),
        premises: vec![MizFormula::Pred {
            name: "Base".to_owned(),
            args: vec![],
        }],
        conclusion: MizFormula::ForAll {
            var: "n".to_owned(),
            ty: MizType::Set,
            body: Box::new(MizFormula::Pred {
                name: "P".to_owned(),
                args: vec![MizTerm::Var("n".to_owned())],
            }),
        },
    };
    // Verify the scheme's premise and conclusion both translate.
    let premise_expr =
        translate_formula_fresh(&scheme.premises[0]).expect("scheme premise should translate");
    assert!(matches!(premise_expr.kind(), ExprKind::Const(_, _)));

    let conclusion_expr =
        translate_formula_fresh(&scheme.conclusion).expect("scheme conclusion should translate");
    assert!(matches!(conclusion_expr.kind(), ExprKind::Pi(_, _, _)));
}

// ════════════════════════════════════════════════════════════════════════════
// Error recovery parsing tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_parse_mizar_article_with_recovery() {
    use super::xml_parser::parse_mizar_article;

    let xml = r#"<Article aid="MIXED">
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
  <Theorem nr="2"><Pred kind="R" nr="2"/></Theorem>
</Article>"#;
    let result = parse_mizar_article(xml).expect("should parse with recovery");
    assert!(result.is_clean());
    assert_eq!(result.items_parsed, 2);
    assert_eq!(result.items_skipped, 0);
    assert_eq!(result.article.name, "MIXED");
}

#[test]
fn test_parse_mizar_article_empty() {
    use super::xml_parser::parse_mizar_article;

    let xml = r#"<Article aid="EMPTY"/>"#;
    let result = parse_mizar_article(xml).expect("should parse empty article");
    assert!(result.is_clean());
    assert_eq!(result.items_parsed, 0);
    assert!(!result.has_items());
}

// ════════════════════════════════════════════════════════════════════════════
// Batch import tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_import_report_summary() {
    use super::importer::MizarImportReport;

    let report = MizarImportReport {
        article_name: "TEST".to_owned(),
        total_items: 10,
        theorems_imported: 5,
        definitions_imported: 2,
        schemes_imported: 1,
        registrations_imported: 1,
        axiomatized: 3,
        skipped: 1,
        errors: 0,
        diagnostics: vec![],
    };
    assert_eq!(report.constants_produced(), 9);
    assert!(!report.is_complete()); // has skips
    assert!(report.summary().contains("TEST"));
}

#[test]
fn test_import_report_complete() {
    use super::importer::MizarImportReport;

    let report = MizarImportReport {
        article_name: "CLEAN".to_owned(),
        total_items: 3,
        theorems_imported: 3,
        errors: 0,
        skipped: 0,
        ..MizarImportReport::default()
    };
    assert!(report.is_complete());
}

#[test]
fn test_batch_import_report_clean() {
    use super::importer::MizarBatchImportReport;

    let batch = MizarBatchImportReport::default();
    assert!(batch.is_clean());
    assert_eq!(batch.articles_imported(), 0);
    assert_eq!(batch.articles_failed(), 0);
}

#[test]
fn test_batch_import_report_with_failures() {
    use super::importer::MizarBatchImportReport;

    let mut batch = MizarBatchImportReport::default();
    batch
        .failed_articles
        .push(("BAD".to_owned(), "parse error".to_owned()));
    batch.total_errors = 1;
    assert!(!batch.is_clean());
    assert_eq!(batch.articles_failed(), 1);
    assert!(batch.summary().contains("1 failed"));
}

// ════════════════════════════════════════════════════════════════════════════
// Edge cases
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_environ_all_dependencies() {
    let env = MizEnviron {
        vocabularies: vec!["A".to_owned(), "B".to_owned()],
        constructors: vec!["B".to_owned(), "C".to_owned()],
        theorems: vec!["A".to_owned(), "D".to_owned()],
        ..MizEnviron::default()
    };
    let deps = env.all_dependencies();
    assert!(deps.contains(&"A".to_owned()));
    assert!(deps.contains(&"B".to_owned()));
    assert!(deps.contains(&"C".to_owned()));
    assert!(deps.contains(&"D".to_owned()));
    // Uniqueness: "A" and "B" appear in multiple lists but should be unique.
    assert_eq!(deps.len(), 4);
}

#[test]
fn test_environ_is_empty() {
    let env = MizEnviron::default();
    assert!(env.is_empty());

    let env_with_vocab = MizEnviron {
        vocabularies: vec!["X".to_owned()],
        ..MizEnviron::default()
    };
    assert!(!env_with_vocab.is_empty());
}

#[test]
fn test_article_dependency_count() {
    let article = MizArticle {
        name: "DEP".to_owned(),
        environ: MizEnviron {
            vocabularies: vec!["A".to_owned()],
            constructors: vec!["A".to_owned(), "B".to_owned()],
            ..MizEnviron::default()
        },
        items: vec![],
    };
    assert_eq!(article.dependency_count(), 2);
}

#[test]
fn test_mizar_cluster_type_variants() {
    use super::types::MizClusterType;

    let types = [
        MizClusterType::Existential,
        MizClusterType::Conditional,
        MizClusterType::Functorial,
    ];
    // Verify all variants are distinct.
    for (i, a) in types.iter().enumerate() {
        for (j, b) in types.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

#[test]
fn test_mizar_notation_kind_variants() {
    use super::types::MizNotationKind;

    assert_ne!(MizNotationKind::Synonym, MizNotationKind::Antonym);
}

#[test]
fn test_annotated_notation() {
    use super::types::{MizAnnotatedNotation, MizNotationKind};

    let notation = MizAnnotatedNotation {
        kind: MizNotationKind::Synonym,
        pattern: "is_empty".to_owned(),
        origin: "empty".to_owned(),
        source_article: "XBOOLE_0".to_owned(),
    };
    assert_eq!(notation.kind, MizNotationKind::Synonym);
    assert_eq!(notation.pattern, "is_empty");
    assert_eq!(notation.origin, "empty");
    assert_eq!(notation.source_article, "XBOOLE_0");
}

#[test]
fn test_annotated_registration() {
    use super::types::{MizAnnotatedRegistration, MizClusterType};

    let reg = MizAnnotatedRegistration {
        cluster_type: MizClusterType::Existential,
        conditions: vec![MizAdjective {
            name: "empty".to_owned(),
            negated: false,
            args: vec![],
        }],
        registration: MizRegistration::Existential {
            adjectives: vec![MizAdjective {
                name: "empty".to_owned(),
                negated: false,
                args: vec![],
            }],
            ty: MizType::Set,
        },
    };
    assert_eq!(reg.cluster_type, MizClusterType::Existential);
    assert_eq!(reg.conditions.len(), 1);
}

#[test]
fn test_scheme_signature() {
    use super::types::{MizSchemeFuncArg, MizSchemePredArg, MizSchemeSignature};

    let sig = MizSchemeSignature {
        name: "Induction".to_owned(),
        func_args: vec![MizSchemeFuncArg {
            name: "F".to_owned(),
            arg_types: vec![MizType::Set],
            result_type: MizType::Set,
        }],
        pred_args: vec![MizSchemePredArg {
            name: "P".to_owned(),
            arg_types: vec![MizType::Set],
        }],
        premises: vec![MizFormula::Pred {
            name: "Base".to_owned(),
            args: vec![],
        }],
        conclusion: MizFormula::Thesis,
    };
    assert_eq!(sig.name, "Induction");
    assert_eq!(sig.func_args.len(), 1);
    assert_eq!(sig.pred_args.len(), 1);
    assert_eq!(sig.premises.len(), 1);
}

#[test]
fn test_xml_is_mizar_article() {
    use super::xml_parser::is_mizar_article_xml;

    assert!(is_mizar_article_xml(r#"<Article aid="TEST"/>"#));
    assert!(is_mizar_article_xml(
        r#"<?xml version="1.0"?><Article aid="TEST"/>"#
    ));
    assert!(!is_mizar_article_xml(r#"<Theorem nr="1"/>"#));
    assert!(!is_mizar_article_xml(r#"not xml at all"#));
    assert!(!is_mizar_article_xml(r#"<Article/>"#)); // no aid attribute
}

#[test]
fn test_xml_count_article_items_approx() {
    use super::xml_parser::count_article_items_approx;

    let xml = r#"<Article aid="TEST">
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
  <Definition kind="M"><ModeDef nr="1"/></Definition>
  <Scheme nr="1"><Pred kind="R" nr="1"/></Scheme>
</Article>"#;
    assert_eq!(count_article_items_approx(xml), 3);
}

#[test]
fn test_parse_environ_only() {
    use super::xml_parser::parse_environ_only;

    let xml = r#"<Article aid="TEST">
  <Environ>
    <Vocabularies>
      <Directive name="XBOOLE_0"/>
    </Vocabularies>
  </Environ>
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
</Article>"#;
    let env = parse_environ_only(xml).expect("should parse environ only");
    assert_eq!(env.vocabularies.len(), 1);
    assert_eq!(env.vocabularies[0], "XBOOLE_0");
}

#[test]
fn test_parse_registrations_from_xml() {
    use super::xml_parser::parse_registrations_from_xml;

    let xml = r#"<Article aid="REG">
  <Registration>
    <ExistentialRegistration>
      <Adjective nr="empty"/>
      <Typ kind="M" nr="1"/>
    </ExistentialRegistration>
  </Registration>
  <Registration>
    <FunctorialRegistration>
      <Func kind="K" nr="1"/>
      <Adjective nr="positive"/>
    </FunctorialRegistration>
  </Registration>
</Article>"#;
    let regs = parse_registrations_from_xml(xml).expect("should parse registrations");
    assert_eq!(regs.len(), 2);
    assert!(matches!(&regs[0], MizRegistration::Existential { .. }));
    assert!(matches!(&regs[1], MizRegistration::Functorial { .. }));
}

#[test]
fn test_parse_notations_from_xml() {
    use super::xml_parser::parse_notations_from_xml;

    let xml = r#"<Article aid="NOT">
  <Notation>
    <Synonym nr="foo" origin="bar"/>
  </Notation>
  <Notation>
    <Antonym nr="baz" origin="qux"/>
  </Notation>
</Article>"#;
    let notes = parse_notations_from_xml(xml).expect("should parse notations");
    assert_eq!(notes.len(), 2);
    assert!(matches!(&notes[0], MizNotation::Synonym { .. }));
    assert!(matches!(&notes[1], MizNotation::Antonym { .. }));
}

#[test]
fn test_parse_schemes_from_xml() {
    use super::xml_parser::parse_schemes_from_xml;

    let xml = r#"<Article aid="SCH">
  <Scheme nr="1">
    <Pred kind="R" nr="1"/>
  </Scheme>
  <Scheme nr="2">
    <SchemePremises>
      <Pred kind="R" nr="2"/>
    </SchemePremises>
    <Pred kind="R" nr="3"/>
  </Scheme>
</Article>"#;
    let schemes = parse_schemes_from_xml(xml).expect("should parse schemes");
    assert_eq!(schemes.len(), 2);
    assert_eq!(schemes[0].name, "1");
    assert_eq!(schemes[1].name, "2");
    assert_eq!(schemes[1].premises.len(), 1);
}

#[test]
fn test_mizar_import_error_display() {
    use super::importer::MizarImportError;
    use std::io;

    let io_err = MizarImportError::IoError(io::Error::new(io::ErrorKind::NotFound, "no file"));
    assert!(format!("{io_err}").contains("no file"));

    let fmt_err = MizarImportError::InvalidFormat {
        detail: "missing root".to_owned(),
    };
    assert!(format!("{fmt_err}").contains("missing root"));
}

#[test]
fn test_serde_roundtrip_annotated_notation() {
    use super::types::{MizAnnotatedNotation, MizNotationKind};

    let notation = MizAnnotatedNotation {
        kind: MizNotationKind::Antonym,
        pattern: "non_empty".to_owned(),
        origin: "empty".to_owned(),
        source_article: "XBOOLE_0".to_owned(),
    };
    let json = serde_json::to_string(&notation).expect("should serialize");
    let deserialized: MizAnnotatedNotation =
        serde_json::from_str(&json).expect("should deserialize");
    assert_eq!(notation, deserialized);
}

#[test]
fn test_serde_roundtrip_scheme_signature() {
    use super::types::{MizSchemePredArg, MizSchemeSignature};

    let sig = MizSchemeSignature {
        name: "Sch1".to_owned(),
        func_args: vec![],
        pred_args: vec![MizSchemePredArg {
            name: "P".to_owned(),
            arg_types: vec![MizType::Set],
        }],
        premises: vec![],
        conclusion: MizFormula::Thesis,
    };
    let json = serde_json::to_string(&sig).expect("should serialize");
    let deserialized: MizSchemeSignature = serde_json::from_str(&json).expect("should deserialize");
    assert_eq!(sig, deserialized);
}

#[test]
fn test_mizar_article_item_counts_default() {
    use super::types::MizArticleItemCounts;

    let counts = MizArticleItemCounts::default();
    assert_eq!(counts.total(), 0);
    assert_eq!(counts.theorems, 0);
    assert_eq!(counts.definitions, 0);
}

#[test]
fn test_article_stats() {
    use super::xml_parser::article_stats;

    let xml = r#"<Article aid="STATS">
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
  <Theorem nr="2"><Pred kind="R" nr="2"/></Theorem>
  <Scheme nr="1"><Pred kind="R" nr="1"/></Scheme>
</Article>"#;
    let stats = article_stats(xml).expect("should extract stats");
    assert_eq!(stats.name, "STATS");
    assert_eq!(stats.theorems, 2);
    assert_eq!(stats.schemes, 1);
    assert_eq!(stats.total_items(), 3);
}
