// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::path::{Path, PathBuf};

use super::importer::*;
use super::types::*;
use super::yxml_parser::*;
use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

// ===== YXML low-level parsing tests =====

#[test]
fn test_yxml_parse_empty_input() {
    let result = parse_yxml(b"");
    let nodes = result.expect("empty input should succeed");
    assert!(nodes.is_empty());
}

#[test]
fn test_yxml_parse_plain_text() {
    let result = parse_yxml(b"hello world").expect("plain text should parse");
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], YxmlTree::Text("hello world".to_owned()));
}

#[test]
fn test_yxml_parse_simple_element() {
    let input = yxml_elem("foo", &[], b"bar");
    let result = parse_yxml(&input).expect("simple element should parse");
    assert_eq!(result.len(), 1);
    match &result[0] {
        YxmlTree::Element {
            name,
            attrs,
            children,
        } => {
            assert_eq!(name, "foo");
            assert!(attrs.is_empty());
            assert_eq!(children.len(), 1);
            assert_eq!(children[0], YxmlTree::Text("bar".to_owned()));
        }
        other => panic!("expected Element, got {other:?}"),
    }
}

#[test]
fn test_yxml_parse_element_with_attrs() {
    let input = yxml_elem("node", &[("key", "val"), ("x", "42")], b"data");
    let result = parse_yxml(&input).expect("element with attrs should parse");
    assert_eq!(result.len(), 1);
    match &result[0] {
        YxmlTree::Element { name, attrs, .. } => {
            assert_eq!(name, "node");
            assert_eq!(attrs.len(), 2);
            assert_eq!(attrs[0], ("key".to_owned(), "val".to_owned()));
            assert_eq!(attrs[1], ("x".to_owned(), "42".to_owned()));
        }
        other => panic!("expected Element, got {other:?}"),
    }
}

#[test]
fn test_yxml_parse_nested_elements() {
    let inner = yxml_elem("inner", &[("a", "1")], b"text");
    let mut outer_content = Vec::new();
    outer_content.extend_from_slice(&inner);
    let outer = yxml_elem("outer", &[], &outer_content);

    let result = parse_yxml(&outer).expect("nested elements should parse");
    assert_eq!(result.len(), 1);

    let outer_tree = &result[0];
    assert_eq!(outer_tree.tag_name(), Some("outer"));
    assert_eq!(outer_tree.children().len(), 1);

    let inner_tree = &outer_tree.children()[0];
    assert_eq!(inner_tree.tag_name(), Some("inner"));
    assert_eq!(inner_tree.attr("a"), Some("1"));
    assert_eq!(inner_tree.text_content(), "text");
}

#[test]
fn test_yxml_parse_empty_element() {
    let input = yxml_leaf("empty", &[]);
    let result = parse_yxml(&input).expect("empty element should parse");
    assert_eq!(result.len(), 1);
    match &result[0] {
        YxmlTree::Element { name, children, .. } => {
            assert_eq!(name, "empty");
            assert!(children.is_empty());
        }
        other => panic!("expected Element, got {other:?}"),
    }
}

#[test]
fn test_yxml_parse_multiple_siblings() {
    let mut input = Vec::new();
    input.extend_from_slice(&yxml_leaf("a", &[]));
    input.extend_from_slice(&yxml_leaf("b", &[]));
    input.extend_from_slice(b"text between");
    input.extend_from_slice(&yxml_leaf("c", &[]));

    let result = parse_yxml(&input).expect("siblings should parse");
    assert_eq!(result.len(), 4);
    assert_eq!(result[0].tag_name(), Some("a"));
    assert_eq!(result[1].tag_name(), Some("b"));
    assert_eq!(result[2], YxmlTree::Text("text between".to_owned()));
    assert_eq!(result[3].tag_name(), Some("c"));
}

#[test]
fn test_yxml_tree_text_content_deep() {
    // Build: <a>hello<b>world</b>!</a>
    let b_elem = yxml_elem("b", &[], b"world");
    let mut content = Vec::new();
    content.extend_from_slice(b"hello");
    content.extend_from_slice(&b_elem);
    content.extend_from_slice(b"!");
    let a_elem = yxml_elem("a", &[], &content);

    let tree = parse_yxml_tree(&a_elem).expect("should parse");
    assert_eq!(tree.text_content(), "helloworld!");
}

#[test]
fn test_yxml_tree_find_child() {
    let child_a = yxml_leaf("alpha", &[("id", "1")]);
    let child_b = yxml_leaf("beta", &[("id", "2")]);
    let mut content = Vec::new();
    content.extend_from_slice(&child_a);
    content.extend_from_slice(&child_b);
    let root = yxml_elem("root", &[], &content);

    let tree = parse_yxml_tree(&root).expect("should parse");
    let found = tree.find_child("beta").expect("should find beta");
    assert_eq!(found.attr("id"), Some("2"));
    assert!(tree.find_child("gamma").is_none());
}

#[test]
fn test_yxml_tree_find_children() {
    let item1 = yxml_leaf("item", &[("n", "1")]);
    let item2 = yxml_leaf("item", &[("n", "2")]);
    let other = yxml_leaf("other", &[]);
    let item3 = yxml_leaf("item", &[("n", "3")]);
    let mut content = Vec::new();
    content.extend_from_slice(&item1);
    content.extend_from_slice(&item2);
    content.extend_from_slice(&other);
    content.extend_from_slice(&item3);
    let root = yxml_elem("root", &[], &content);

    let tree = parse_yxml_tree(&root).expect("should parse");
    let items = tree.find_children("item");
    assert_eq!(items.len(), 3);
    assert_eq!(items[0].attr("n"), Some("1"));
    assert_eq!(items[1].attr("n"), Some("2"));
    assert_eq!(items[2].attr("n"), Some("3"));
}

#[test]
fn test_yxml_parse_invalid_utf8() {
    // Invalid UTF-8 byte sequence in text
    let input: &[u8] = &[0xff, 0xfe];
    let result = parse_yxml(input);
    assert!(result.is_err());
    match result.unwrap_err() {
        YxmlError::InvalidUtf8 { .. } => {}
        other => panic!("expected InvalidUtf8, got {other:?}"),
    }
}

#[test]
fn test_yxml_parse_tree_single_element() {
    let input = yxml_leaf("single", &[("k", "v")]);
    let tree = parse_yxml_tree(&input).expect("should parse");
    assert_eq!(tree.tag_name(), Some("single"));
    assert_eq!(tree.attr("k"), Some("v"));
}

#[test]
fn test_yxml_parse_tree_wraps_multiple() {
    let mut input = Vec::new();
    input.extend_from_slice(&yxml_leaf("a", &[]));
    input.extend_from_slice(&yxml_leaf("b", &[]));

    let tree = parse_yxml_tree(&input).expect("should parse");
    assert_eq!(tree.tag_name(), Some("root"));
    assert_eq!(tree.children().len(), 2);
}

// ===== Isabelle type parsing tests =====

#[test]
fn test_parse_type_tfree() {
    let input = yxml_leaf("TFree", &[("name", "'a"), ("sort", "ord")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse TFree");
    assert_eq!(
        ty,
        IsaType::TFree {
            name: "'a".to_owned(),
            sort: vec!["ord".to_owned()],
        }
    );
}

#[test]
fn test_parse_type_tfree_empty_sort() {
    let input = yxml_leaf("TFree", &[("name", "'b"), ("sort", "")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse TFree");
    assert_eq!(
        ty,
        IsaType::TFree {
            name: "'b".to_owned(),
            sort: Vec::new(),
        }
    );
}

#[test]
fn test_parse_type_tfree_multiple_sort() {
    let input = yxml_leaf("TFree", &[("name", "'c"), ("sort", "ord,type")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse TFree");
    assert_eq!(
        ty,
        IsaType::TFree {
            name: "'c".to_owned(),
            sort: vec!["ord".to_owned(), "type".to_owned()],
        }
    );
}

#[test]
fn test_parse_type_tvar() {
    let input = yxml_leaf("TVar", &[("name", "'a"), ("index", "3"), ("sort", "ring")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse TVar");
    assert_eq!(
        ty,
        IsaType::TVar {
            name: "'a".to_owned(),
            index: 3,
            sort: vec!["ring".to_owned()],
        }
    );
}

#[test]
fn test_parse_type_nullary_constructor() {
    let input = yxml_leaf("Type", &[("name", "nat")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse nullary Type");
    assert_eq!(
        ty,
        IsaType::Type {
            name: "nat".to_owned(),
            args: vec![],
        }
    );
}

#[test]
fn test_parse_type_unary_constructor() {
    // list('a) — Type constructor with one argument
    let tfree = yxml_leaf("TFree", &[("name", "'a"), ("sort", "")]);
    let input = yxml_elem("Type", &[("name", "List.list")], &tfree);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse unary Type");
    assert_eq!(
        ty,
        IsaType::Type {
            name: "List.list".to_owned(),
            args: vec![IsaType::TFree {
                name: "'a".to_owned(),
                sort: vec![],
            }],
        }
    );
}

#[test]
fn test_parse_type_fun() {
    // 'a => 'b — fun('a, 'b)
    let ta = yxml_leaf("TFree", &[("name", "'a"), ("sort", "")]);
    let tb = yxml_leaf("TFree", &[("name", "'b"), ("sort", "")]);
    let mut args = Vec::new();
    args.extend_from_slice(&ta);
    args.extend_from_slice(&tb);
    let input = yxml_elem("Type", &[("name", "fun")], &args);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse fun type");

    let expected = IsaType::fun(
        IsaType::TFree {
            name: "'a".to_owned(),
            sort: vec![],
        },
        IsaType::TFree {
            name: "'b".to_owned(),
            sort: vec![],
        },
    );
    assert_eq!(ty, expected);
    assert!(ty.is_fun());
}

#[test]
fn test_parse_type_nested_constructors() {
    // nat list list — Type("List.list", [Type("List.list", [Type("nat", [])])])
    let nat = yxml_leaf("Type", &[("name", "nat")]);
    let inner_list = yxml_elem("Type", &[("name", "List.list")], &nat);
    let outer_list = yxml_elem("Type", &[("name", "List.list")], &inner_list);

    let tree = parse_yxml_tree(&outer_list).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse nested type");
    assert_eq!(
        ty,
        IsaType::Type {
            name: "List.list".to_owned(),
            args: vec![IsaType::Type {
                name: "List.list".to_owned(),
                args: vec![IsaType::Type {
                    name: "nat".to_owned(),
                    args: vec![],
                }],
            }],
        }
    );
}

#[test]
fn test_parse_type_unknown_tag() {
    let input = yxml_leaf("Unknown", &[("name", "x")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let result = parse_type(&tree);
    assert!(result.is_err());
    match result.unwrap_err() {
        YxmlError::UnknownConstructor { name } => {
            assert!(
                name.contains("Unknown"),
                "error should mention Unknown: {name}"
            );
        }
        other => panic!("expected UnknownConstructor, got {other:?}"),
    }
}

// ===== Isabelle term parsing tests =====

#[test]
fn test_parse_term_bound() {
    let input = yxml_leaf("Bound", &[("index", "0")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Bound");
    assert_eq!(term, IsaTerm::Bound(0));
}

#[test]
fn test_parse_term_bound_higher_index() {
    let input = yxml_leaf("Bound", &[("index", "42")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Bound");
    assert_eq!(term, IsaTerm::Bound(42));
}

#[test]
fn test_parse_term_free() {
    let ty = yxml_leaf("Type", &[("name", "nat")]);
    let input = yxml_elem("Free", &[("name", "x")], &ty);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Free");
    assert_eq!(
        term,
        IsaTerm::Free {
            name: "x".to_owned(),
            ty: IsaType::nullary("nat"),
        }
    );
}

#[test]
fn test_parse_term_var() {
    let ty = yxml_leaf("Type", &[("name", "bool")]);
    let input = yxml_elem("Var", &[("name", "P"), ("index", "1")], &ty);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Var");
    assert_eq!(
        term,
        IsaTerm::Var {
            name: "P".to_owned(),
            index: 1,
            ty: IsaType::nullary("bool"),
        }
    );
}

#[test]
fn test_parse_term_const() {
    let ty = yxml_leaf("Type", &[("name", "nat")]);
    let input = yxml_elem("Const", &[("name", "Nat.zero_class.zero")], &ty);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Const");
    assert_eq!(
        term,
        IsaTerm::Const {
            name: "Nat.zero_class.zero".to_owned(),
            ty: IsaType::nullary("nat"),
        }
    );
}

#[test]
fn test_parse_term_abs() {
    // \x::nat. Bound(0)
    let ty = yxml_leaf("Type", &[("name", "nat")]);
    let body = yxml_leaf("Bound", &[("index", "0")]);
    let mut content = Vec::new();
    content.extend_from_slice(&ty);
    content.extend_from_slice(&body);
    let input = yxml_elem("Abs", &[("name", "x")], &content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Abs");
    assert_eq!(
        term,
        IsaTerm::Abs {
            name: "x".to_owned(),
            ty: IsaType::nullary("nat"),
            body: Box::new(IsaTerm::Bound(0)),
        }
    );
    assert!(term.is_abs());
}

#[test]
fn test_parse_term_app() {
    // f $ x where f: Free("f", nat => nat), x: Free("x", nat)
    let f_ty_a = yxml_leaf("Type", &[("name", "nat")]);
    let f_ty_b = yxml_leaf("Type", &[("name", "nat")]);
    let mut f_ty_args = Vec::new();
    f_ty_args.extend_from_slice(&f_ty_a);
    f_ty_args.extend_from_slice(&f_ty_b);
    let f_ty = yxml_elem("Type", &[("name", "fun")], &f_ty_args);
    let f_term = yxml_elem("Free", &[("name", "f")], &f_ty);

    let x_ty = yxml_leaf("Type", &[("name", "nat")]);
    let x_term = yxml_elem("Free", &[("name", "x")], &x_ty);

    let mut app_content = Vec::new();
    app_content.extend_from_slice(&f_term);
    app_content.extend_from_slice(&x_term);
    let input = yxml_elem("App", &[], &app_content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse App");
    assert!(term.is_app());

    match &term {
        IsaTerm::App { fun, arg } => {
            match fun.as_ref() {
                IsaTerm::Free { name, ty } => {
                    assert_eq!(name, "f");
                    assert!(ty.is_fun());
                }
                other => panic!("expected Free, got {other:?}"),
            }
            match arg.as_ref() {
                IsaTerm::Free { name, ty } => {
                    assert_eq!(name, "x");
                    assert_eq!(ty, &IsaType::nullary("nat"));
                }
                other => panic!("expected Free, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_term_app_dollar_sign_tag() {
    // The `$` tag is an alternative for App in some Isabelle export formats
    let bound0 = yxml_leaf("Bound", &[("index", "0")]);
    let bound1 = yxml_leaf("Bound", &[("index", "1")]);
    let mut content = Vec::new();
    content.extend_from_slice(&bound0);
    content.extend_from_slice(&bound1);
    let input = yxml_elem("$", &[], &content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse $ as App");
    assert_eq!(
        term,
        IsaTerm::App {
            fun: Box::new(IsaTerm::Bound(0)),
            arg: Box::new(IsaTerm::Bound(1)),
        }
    );
}

#[test]
fn test_parse_term_nested_abs_app() {
    // \x::nat. \y::nat. App(Free("plus", nat => nat => nat), Bound(1), Bound(0))
    // which is plus(x, y) in de Bruijn notation
    let nat = || yxml_leaf("Type", &[("name", "nat")]);

    // Build fun type: nat => nat => nat
    let mut fun_inner_args = Vec::new();
    fun_inner_args.extend_from_slice(&nat());
    fun_inner_args.extend_from_slice(&nat());
    let fun_inner = yxml_elem("Type", &[("name", "fun")], &fun_inner_args);
    let mut fun_outer_args = Vec::new();
    fun_outer_args.extend_from_slice(&nat());
    fun_outer_args.extend_from_slice(&fun_inner);
    let plus_ty = yxml_elem("Type", &[("name", "fun")], &fun_outer_args);

    let plus = yxml_elem("Const", &[("name", "Groups.plus_class.plus")], &plus_ty);
    let b1 = yxml_leaf("Bound", &[("index", "1")]);
    let b0 = yxml_leaf("Bound", &[("index", "0")]);

    // App(plus, Bound(1))
    let mut app1_content = Vec::new();
    app1_content.extend_from_slice(&plus);
    app1_content.extend_from_slice(&b1);
    let app1 = yxml_elem("App", &[], &app1_content);

    // App(App(plus, Bound(1)), Bound(0))
    let mut app2_content = Vec::new();
    app2_content.extend_from_slice(&app1);
    app2_content.extend_from_slice(&b0);
    let app2 = yxml_elem("App", &[], &app2_content);

    // \y::nat. app2
    let mut abs_y_content = Vec::new();
    abs_y_content.extend_from_slice(&nat());
    abs_y_content.extend_from_slice(&app2);
    let abs_y = yxml_elem("Abs", &[("name", "y")], &abs_y_content);

    // \x::nat. abs_y
    let mut abs_x_content = Vec::new();
    abs_x_content.extend_from_slice(&nat());
    abs_x_content.extend_from_slice(&abs_y);
    let abs_x = yxml_elem("Abs", &[("name", "x")], &abs_x_content);

    let tree = parse_yxml_tree(&abs_x).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse nested abs+app");

    // Verify the outer structure
    match &term {
        IsaTerm::Abs { name, ty, body } => {
            assert_eq!(name, "x");
            assert_eq!(ty, &IsaType::nullary("nat"));
            match body.as_ref() {
                IsaTerm::Abs {
                    name: inner_name,
                    ty: inner_ty,
                    body: inner_body,
                } => {
                    assert_eq!(inner_name, "y");
                    assert_eq!(inner_ty, &IsaType::nullary("nat"));
                    assert!(inner_body.is_app());
                }
                other => panic!("expected inner Abs, got {other:?}"),
            }
        }
        other => panic!("expected outer Abs, got {other:?}"),
    }
}

#[test]
fn test_parse_term_unknown_tag() {
    let input = yxml_leaf("Bogus", &[("index", "0")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let result = parse_term(&tree);
    assert!(result.is_err());
    match result.unwrap_err() {
        YxmlError::UnknownConstructor { name } => {
            assert!(name.contains("Bogus"));
        }
        other => panic!("expected UnknownConstructor, got {other:?}"),
    }
}

#[test]
fn test_parse_term_missing_type_child() {
    // Free without a type child
    let input = yxml_leaf("Free", &[("name", "x")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let result = parse_term(&tree);
    assert!(result.is_err());
    match result.unwrap_err() {
        YxmlError::MissingChild { parent, .. } => {
            assert_eq!(parent, "Free");
        }
        other => panic!("expected MissingChild, got {other:?}"),
    }
}

#[test]
fn test_parse_term_abs_missing_body() {
    // Abs with type but no body
    let ty = yxml_leaf("Type", &[("name", "nat")]);
    let input = yxml_elem("Abs", &[("name", "x")], &ty);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let result = parse_term(&tree);
    assert!(result.is_err());
}

// ===== Theorem parsing tests =====

#[test]
fn test_parse_theorem_proved() {
    let proof = yxml_leaf("proof", &[("status", "proved")]);
    // proposition: True (as a Const)
    let true_ty = yxml_leaf("Type", &[("name", "prop")]);
    let true_const = yxml_elem("Const", &[("name", "HOL.True")], &true_ty);
    let prop = yxml_elem("prop", &[], &true_const);

    let mut content = Vec::new();
    content.extend_from_slice(&proof);
    content.extend_from_slice(&prop);
    let input = yxml_elem("theorem", &[("name", "HOL.TrueI")], &content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let thm = parse_theorem(&tree).expect("should parse theorem");

    assert_eq!(thm.name, "HOL.TrueI");
    assert_eq!(thm.proof_status, ProofStatus::Proved);
    assert_eq!(thm.props.len(), 1);
    match &thm.props[0] {
        IsaTerm::Const { name, .. } => assert_eq!(name, "HOL.True"),
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_parse_theorem_axiomatized() {
    let proof = yxml_leaf("proof", &[("status", "axiomatized")]);
    let ax_ty = yxml_leaf("Type", &[("name", "prop")]);
    let ax_const = yxml_elem("Const", &[("name", "HOL.iff_reflection")], &ax_ty);
    let prop = yxml_elem("prop", &[], &ax_const);

    let mut content = Vec::new();
    content.extend_from_slice(&proof);
    content.extend_from_slice(&prop);
    let input = yxml_elem("theorem", &[("name", "HOL.iff_reflection")], &content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let thm = parse_theorem(&tree).expect("should parse theorem");

    assert_eq!(thm.name, "HOL.iff_reflection");
    assert_eq!(thm.proof_status, ProofStatus::Axiomatized);
    assert_eq!(thm.props.len(), 1);
}

#[test]
fn test_parse_theorem_no_proof_element() {
    // Theorem without explicit proof element defaults to Axiomatized
    let ax_ty = yxml_leaf("Type", &[("name", "prop")]);
    let ax_const = yxml_elem("Const", &[("name", "Axiom.A")], &ax_ty);
    let prop = yxml_elem("prop", &[], &ax_const);

    let input = yxml_elem("theorem", &[("name", "Axiom.A")], &prop);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let thm = parse_theorem(&tree).expect("should parse theorem");

    assert_eq!(thm.proof_status, ProofStatus::Axiomatized);
}

#[test]
fn test_parse_theorem_multiple_props() {
    let proof = yxml_leaf("proof", &[("status", "proved")]);

    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let hyp = yxml_elem("Const", &[("name", "P")], &prop_ty.clone());
    let concl = yxml_elem("Const", &[("name", "Q")], &prop_ty);
    let prop1 = yxml_elem("prop", &[], &hyp);
    let prop2 = yxml_elem("prop", &[], &concl);

    let mut content = Vec::new();
    content.extend_from_slice(&proof);
    content.extend_from_slice(&prop1);
    content.extend_from_slice(&prop2);
    let input = yxml_elem("theorem", &[("name", "MyThm")], &content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let thm = parse_theorem(&tree).expect("should parse theorem");

    assert_eq!(thm.name, "MyThm");
    assert_eq!(thm.props.len(), 2);
}

#[test]
fn test_parse_theorem_wrong_tag() {
    let input = yxml_leaf("not_a_theorem", &[("name", "x")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let result = parse_theorem(&tree);
    assert!(result.is_err());
    match result.unwrap_err() {
        YxmlError::UnexpectedElement { expected, found } => {
            assert_eq!(expected, "theorem");
            assert_eq!(found, "not_a_theorem");
        }
        other => panic!("expected UnexpectedElement, got {other:?}"),
    }
}

// ===== Theory export parsing tests =====

#[test]
fn test_parse_theory_export_minimal() {
    let input = yxml_leaf("theory", &[("name", "Minimal")]);
    let export = parse_theory_export(&input).expect("should parse minimal theory");
    assert_eq!(export.theory_name, "Minimal");
    assert!(export.types.is_empty());
    assert!(export.consts.is_empty());
    assert!(export.theorems.is_empty());
    assert!(export.dependencies.is_empty());
}

#[test]
fn test_parse_theory_export_with_dependencies() {
    let dep1 = yxml_leaf("dep", &[("name", "Pure")]);
    let dep2 = yxml_leaf("dep", &[("name", "HOL.HOL")]);
    let mut imports_content = Vec::new();
    imports_content.extend_from_slice(&dep1);
    imports_content.extend_from_slice(&dep2);
    let imports = yxml_elem("imports", &[], &imports_content);

    let input = yxml_elem("theory", &[("name", "MyTheory")], &imports);

    let export = parse_theory_export(&input).expect("should parse theory with deps");
    assert_eq!(export.theory_name, "MyTheory");
    assert_eq!(export.dependencies, vec!["Pure", "HOL.HOL"]);
}

#[test]
fn test_parse_theory_export_with_types_and_consts() {
    let nat_ty = yxml_leaf("Type", &[("name", "nat")]);
    let td = yxml_elem("type_decl", &[("name", "nat")], &nat_ty);
    let types = yxml_elem("types", &[], &td);

    let bool_ty = yxml_leaf("Type", &[("name", "bool")]);
    let cd = yxml_elem("const_decl", &[("name", "True")], &bool_ty);
    let consts = yxml_elem("consts", &[], &cd);

    let mut content = Vec::new();
    content.extend_from_slice(&types);
    content.extend_from_slice(&consts);
    let input = yxml_elem("theory", &[("name", "HOL.HOL")], &content);

    let export = parse_theory_export(&input).expect("should parse theory with types+consts");
    assert_eq!(export.theory_name, "HOL.HOL");
    assert_eq!(export.types.len(), 1);
    assert_eq!(export.types[0].0, "nat");
    assert_eq!(export.consts.len(), 1);
    assert_eq!(export.consts[0].0, "True");
    assert_eq!(export.consts[0].1, IsaType::nullary("bool"));
}

#[test]
fn test_parse_theory_export_with_theorems() {
    let proof = yxml_leaf("proof", &[("status", "proved")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let true_const = yxml_elem("Const", &[("name", "HOL.True")], &prop_ty);
    let prop = yxml_elem("prop", &[], &true_const);

    let mut thm_content = Vec::new();
    thm_content.extend_from_slice(&proof);
    thm_content.extend_from_slice(&prop);
    let thm = yxml_elem("theorem", &[("name", "HOL.TrueI")], &thm_content);
    let theorems = yxml_elem("theorems", &[], &thm);

    let input = yxml_elem("theory", &[("name", "HOL.HOL")], &theorems);

    let export = parse_theory_export(&input).expect("should parse theory with theorems");
    assert_eq!(export.theorems.len(), 1);
    assert_eq!(export.theorems[0].name, "HOL.TrueI");
    assert_eq!(export.theorems[0].proof_status, ProofStatus::Proved);
}

#[test]
fn test_parse_theory_export_full() {
    // Build a complete theory export with deps, types, consts, and theorems
    let dep = yxml_leaf("dep", &[("name", "Pure")]);
    let imports = yxml_elem("imports", &[], &dep);

    let nat_type = yxml_leaf("Type", &[("name", "nat")]);
    let td = yxml_elem("type_decl", &[("name", "nat")], &nat_type);
    let types = yxml_elem("types", &[], &td);

    let zero_ty = yxml_leaf("Type", &[("name", "nat")]);
    let zero_cd = yxml_elem("const_decl", &[("name", "zero")], &zero_ty);
    let suc_dom = yxml_leaf("Type", &[("name", "nat")]);
    let suc_cod = yxml_leaf("Type", &[("name", "nat")]);
    let mut suc_fun_args = Vec::new();
    suc_fun_args.extend_from_slice(&suc_dom);
    suc_fun_args.extend_from_slice(&suc_cod);
    let suc_ty = yxml_elem("Type", &[("name", "fun")], &suc_fun_args);
    let suc_cd = yxml_elem("const_decl", &[("name", "Suc")], &suc_ty);
    let mut consts_content = Vec::new();
    consts_content.extend_from_slice(&zero_cd);
    consts_content.extend_from_slice(&suc_cd);
    let consts = yxml_elem("consts", &[], &consts_content);

    let proof = yxml_leaf("proof", &[("status", "proved")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let prop_const = yxml_elem("Const", &[("name", "Nat.Suc_not_Zero")], &prop_ty);
    let prop = yxml_elem("prop", &[], &prop_const);
    let mut thm_content = Vec::new();
    thm_content.extend_from_slice(&proof);
    thm_content.extend_from_slice(&prop);
    let thm = yxml_elem("theorem", &[("name", "Nat.Suc_not_Zero")], &thm_content);
    let theorems = yxml_elem("theorems", &[], &thm);

    let mut theory_content = Vec::new();
    theory_content.extend_from_slice(&imports);
    theory_content.extend_from_slice(&types);
    theory_content.extend_from_slice(&consts);
    theory_content.extend_from_slice(&theorems);
    let input = yxml_elem("theory", &[("name", "Nat.Nat")], &theory_content);

    let export = parse_theory_export(&input).expect("should parse full theory export");
    assert_eq!(export.theory_name, "Nat.Nat");
    assert_eq!(export.dependencies, vec!["Pure"]);
    assert_eq!(export.types.len(), 1);
    assert_eq!(export.types[0].0, "nat");
    assert_eq!(export.consts.len(), 2);
    assert_eq!(export.consts[0].0, "zero");
    assert_eq!(export.consts[1].0, "Suc");
    assert!(export.consts[1].1.is_fun());
    assert_eq!(export.theorems.len(), 1);
    assert_eq!(export.theorems[0].name, "Nat.Suc_not_Zero");
    assert_eq!(export.theorems[0].proof_status, ProofStatus::Proved);
}

// ===== Round-trip tests: build YXML manually, parse, verify AST =====

#[test]
fn test_roundtrip_identity_lambda() {
    // \x::'a. x  (identity function as Abs("x", TFree("'a"), Bound(0)))
    let ty = yxml_leaf("TFree", &[("name", "'a"), ("sort", "")]);
    let body = yxml_leaf("Bound", &[("index", "0")]);
    let mut abs_content = Vec::new();
    abs_content.extend_from_slice(&ty);
    abs_content.extend_from_slice(&body);
    let input = yxml_elem("Abs", &[("name", "x")], &abs_content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse identity");

    let expected = IsaTerm::abs(
        "x",
        IsaType::TFree {
            name: "'a".to_owned(),
            sort: vec![],
        },
        IsaTerm::Bound(0),
    );
    assert_eq!(term, expected);
}

#[test]
fn test_roundtrip_const_application() {
    // Suc(zero): App(Const("Suc", nat=>nat), Const("zero", nat))
    let nat = || yxml_leaf("Type", &[("name", "nat")]);

    // Suc type: nat => nat
    let mut suc_ty_args = Vec::new();
    suc_ty_args.extend_from_slice(&nat());
    suc_ty_args.extend_from_slice(&nat());
    let suc_ty = yxml_elem("Type", &[("name", "fun")], &suc_ty_args);
    let suc = yxml_elem("Const", &[("name", "Suc")], &suc_ty);

    let zero = yxml_elem("Const", &[("name", "zero")], &nat());

    let mut app_content = Vec::new();
    app_content.extend_from_slice(&suc);
    app_content.extend_from_slice(&zero);
    let input = yxml_elem("App", &[], &app_content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let term = parse_term(&tree).expect("should parse Suc(zero)");

    let nat_ty = IsaType::nullary("nat");
    let expected = IsaTerm::app(
        IsaTerm::const_of("Suc", IsaType::fun(nat_ty.clone(), nat_ty.clone())),
        IsaTerm::const_of("zero", nat_ty),
    );
    assert_eq!(term, expected);
}

// ===== Type helper method tests =====

#[test]
fn test_isa_type_nullary() {
    let ty = IsaType::nullary("bool");
    assert_eq!(
        ty,
        IsaType::Type {
            name: "bool".to_owned(),
            args: vec![],
        }
    );
    assert!(!ty.is_fun());
}

#[test]
fn test_isa_type_fun_helper() {
    let ty = IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("bool"));
    assert!(ty.is_fun());
    match &ty {
        IsaType::Type { name, args } => {
            assert_eq!(name, "fun");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected Type, got {other:?}"),
    }
}

#[test]
fn test_isa_type_tfree_helper() {
    let ty = IsaType::tfree("'a");
    assert_eq!(
        ty,
        IsaType::TFree {
            name: "'a".to_owned(),
            sort: vec![],
        }
    );
}

// ===== Term helper method tests =====

#[test]
fn test_isa_term_const_of() {
    let term = IsaTerm::const_of("True", IsaType::nullary("prop"));
    match &term {
        IsaTerm::Const { name, ty } => {
            assert_eq!(name, "True");
            assert_eq!(ty, &IsaType::nullary("prop"));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_isa_term_app_helper() {
    let term = IsaTerm::app(IsaTerm::Bound(0), IsaTerm::Bound(1));
    assert!(term.is_app());
}

#[test]
fn test_isa_term_abs_helper() {
    let term = IsaTerm::abs("x", IsaType::nullary("nat"), IsaTerm::Bound(0));
    assert!(term.is_abs());
}

// ===== Theory export helper tests =====

#[test]
fn test_isa_theory_export_new() {
    let export = IsaTheoryExport::new("Test.Test");
    assert_eq!(export.theory_name, "Test.Test");
    assert!(export.types.is_empty());
    assert!(export.consts.is_empty());
    assert!(export.theorems.is_empty());
    assert!(export.dependencies.is_empty());
}

// ===== Edge case tests =====

#[test]
fn test_yxml_deeply_nested_elements() {
    // 10 levels of nesting
    let mut current = yxml_leaf("leaf", &[("depth", "10")]);
    for i in (0..10).rev() {
        current = yxml_elem("level", &[("n", &i.to_string())], &current);
    }

    let tree = parse_yxml_tree(&current).expect("deep nesting should parse");
    assert_eq!(tree.tag_name(), Some("level"));
    assert_eq!(tree.attr("n"), Some("0"));

    // Walk down to the leaf
    let mut node = &tree;
    for _ in 0..10 {
        let children: Vec<&YxmlTree> = node
            .children()
            .iter()
            .filter(|c| c.tag_name().is_some())
            .collect();
        assert_eq!(children.len(), 1);
        node = children[0];
    }
    assert_eq!(node.tag_name(), Some("leaf"));
    assert_eq!(node.attr("depth"), Some("10"));
}

#[test]
fn test_yxml_text_with_special_chars() {
    // Text containing various special characters (but not \x05 or \x06)
    let text = b"hello <world> & \"quotes\" 'apos'";
    let input = yxml_elem("data", &[], text);
    let tree = parse_yxml_tree(&input).expect("should parse");
    assert_eq!(tree.text_content(), "hello <world> & \"quotes\" 'apos'");
}

#[test]
fn test_yxml_empty_text_not_emitted() {
    // Consecutive elements should not produce empty text nodes
    let a = yxml_leaf("a", &[]);
    let b = yxml_leaf("b", &[]);
    let mut content = Vec::new();
    content.extend_from_slice(&a);
    content.extend_from_slice(&b);
    let input = yxml_elem("root", &[], &content);

    let tree = parse_yxml_tree(&input).expect("should parse");
    // All children should be elements, no empty text nodes
    for child in tree.children() {
        assert!(
            child.tag_name().is_some(),
            "unexpected text node: {child:?}"
        );
    }
}

#[test]
fn test_parse_type_with_class_children_sort() {
    // Sort via <class> child elements instead of sort attribute
    let class1 = yxml_leaf("class", &[("name", "ord")]);
    let class2 = yxml_leaf("class", &[("name", "type")]);
    let mut content = Vec::new();
    content.extend_from_slice(&class1);
    content.extend_from_slice(&class2);
    let input = yxml_elem("TFree", &[("name", "'a")], &content);

    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse TFree with class children");
    assert_eq!(
        ty,
        IsaType::TFree {
            name: "'a".to_owned(),
            sort: vec!["ord".to_owned(), "type".to_owned()],
        }
    );
}

#[test]
fn test_parse_type_tvar_index_zero() {
    let input = yxml_leaf("TVar", &[("name", "'a"), ("index", "0"), ("sort", "")]);
    let tree = parse_yxml_tree(&input).expect("should parse yxml");
    let ty = parse_type(&tree).expect("should parse TVar with index 0");
    assert_eq!(
        ty,
        IsaType::TVar {
            name: "'a".to_owned(),
            index: 0,
            sort: vec![],
        }
    );
}

#[test]
fn test_yxml_error_display() {
    // Verify error messages are informative
    let err = YxmlError::UnexpectedEof { offset: 42 };
    assert_eq!(err.to_string(), "unexpected end of input at byte offset 42");

    let err = YxmlError::MissingAttribute {
        element: "Const".to_owned(),
        attr: "name".to_owned(),
    };
    assert_eq!(
        err.to_string(),
        "missing attribute 'name' on element <Const>"
    );
}

#[test]
fn test_proof_status_equality() {
    assert_eq!(ProofStatus::Proved, ProofStatus::Proved);
    assert_eq!(ProofStatus::Axiomatized, ProofStatus::Axiomatized);
    assert_ne!(ProofStatus::Proved, ProofStatus::Axiomatized);
}

// ===================================================================
// ===== Importer tests ==============================================
// ===================================================================

// -- Helper: build a minimal IsaTheoryExport for testing --

fn make_theory(name: &str, theorems: Vec<IsaTheorem>) -> IsaTheoryExport {
    IsaTheoryExport {
        theory_name: name.to_owned(),
        types: vec![("nat".to_owned(), IsaType::nullary("nat"))],
        consts: vec![
            ("zero".to_owned(), IsaType::nullary("nat")),
            (
                "Suc".to_owned(),
                IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
            ),
        ],
        theorems,
        dependencies: vec!["Pure".to_owned()],
    }
}

fn make_proved_theorem(name: &str) -> IsaTheorem {
    IsaTheorem {
        name: name.to_owned(),
        props: vec![IsaTerm::const_of("HOL.True", IsaType::nullary("HOL.bool"))],
        proof_status: ProofStatus::Proved,
    }
}

fn make_axiomatized_theorem(name: &str) -> IsaTheorem {
    IsaTheorem {
        name: name.to_owned(),
        props: vec![IsaTerm::const_of("HOL.True", IsaType::nullary("HOL.bool"))],
        proof_status: ProofStatus::Axiomatized,
    }
}

fn make_implication_theorem(name: &str) -> IsaTheorem {
    IsaTheorem {
        name: name.to_owned(),
        props: vec![
            IsaTerm::const_of("P", IsaType::nullary("HOL.bool")),
            IsaTerm::const_of("Q", IsaType::nullary("HOL.bool")),
        ],
        proof_status: ProofStatus::Proved,
    }
}

fn default_importer() -> IsabelleImporter {
    IsabelleImporter::with_defaults()
}

// ===== test_importer_single_theory =====

#[test]
fn test_importer_single_theory_basic() {
    let theory = make_theory("HOL.HOL", vec![make_proved_theorem("HOL.TrueI")]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.constants.len(), 1);
    assert_eq!(result.constants[0].name, "HOL.TrueI");
    assert_eq!(
        result.constants[0].trust_level,
        TrustLevel::CertificateReplayed
    );
    assert_eq!(
        result.constants[0].provenance.source,
        SourceSystem::Isabelle
    );
    assert_eq!(
        result.constants[0].provenance.source_file,
        Some("HOL.HOL.thy".to_owned())
    );
    assert!(!result.has_errors());
}

#[test]
fn test_importer_single_theory_axiomatized() {
    let theory = make_theory("HOL.Axioms", vec![make_axiomatized_theorem("HOL.ext")]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.constants.len(), 1);
    assert_eq!(
        result.constants[0].trust_level,
        TrustLevel::PartiallyAxiomatized
    );
    assert!(result.constants[0]
        .axiom_profile
        .contains(AxiomProfile::ISABELLE_LCF_ERASED));
}

#[test]
fn test_importer_single_theory_empty_theorems() {
    let theory = make_theory("Empty.Theory", vec![]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert!(result.constants.is_empty());
    assert_eq!(result.statistics.theories_processed, 1);
    assert_eq!(result.statistics.theorems_imported, 0);
    assert!(!result.has_constants());
}

#[test]
fn test_importer_single_theory_metadata_recorded() {
    let theory = make_theory("Nat.Nat", vec![make_proved_theorem("Nat.Suc_not_Zero")]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.statistics.theories_processed, 1);
    assert_eq!(result.statistics.types_declared, 1); // nat
    assert_eq!(result.statistics.consts_declared, 2); // zero, Suc
    assert_eq!(result.statistics.dependencies_count, 1); // Pure
    assert_eq!(result.statistics.theory_names, vec!["Nat.Nat"]);
}

// ===== test_importer_multiple_theories =====

#[test]
fn test_importer_multiple_theories_merged() {
    let theory1 = make_theory(
        "HOL.HOL",
        vec![
            make_proved_theorem("HOL.TrueI"),
            make_proved_theorem("HOL.refl"),
        ],
    );
    let theory2 = make_theory(
        "Nat.Nat",
        vec![
            make_proved_theorem("Nat.Suc_not_Zero"),
            make_axiomatized_theorem("Nat.induct"),
        ],
    );

    let importer = default_importer();
    let mut combined = importer
        .import_theory(&theory1)
        .expect("theory1 should import");
    let result2 = importer
        .import_theory(&theory2)
        .expect("theory2 should import");
    combined.merge(result2);

    assert_eq!(combined.constants.len(), 4);
    assert_eq!(combined.statistics.theories_processed, 2);
    assert_eq!(combined.statistics.theorems_imported, 4);
    assert_eq!(combined.statistics.theory_names, vec!["HOL.HOL", "Nat.Nat"]);
}

#[test]
fn test_importer_multiple_theories_mixed_proof_status() {
    let theory = make_theory(
        "Mixed.Theory",
        vec![
            make_proved_theorem("thm_proved"),
            make_axiomatized_theorem("thm_axiomatized"),
            make_proved_theorem("thm_proved2"),
        ],
    );

    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.statistics.theorems_imported, 3);

    // Check trust level summary.
    let cert_count = result
        .statistics
        .trust_level_summary
        .get(&TrustLevel::CertificateReplayed)
        .copied()
        .unwrap_or(0);
    let axiom_count = result
        .statistics
        .trust_level_summary
        .get(&TrustLevel::PartiallyAxiomatized)
        .copied()
        .unwrap_or(0);
    assert_eq!(cert_count, 2);
    assert_eq!(axiom_count, 1);
}

// ===== test_importer_error_handling =====

#[test]
fn test_importer_error_handling_empty_props_continue() {
    let bad_thm = IsaTheorem {
        name: "bad_theorem".to_owned(),
        props: vec![], // Empty props → translation error
        proof_status: ProofStatus::Proved,
    };
    let good_thm = make_proved_theorem("good_theorem");

    let theory = make_theory("Error.Theory", vec![bad_thm, good_thm]);
    let importer = default_importer(); // continue_on_error = true

    let result = importer
        .import_theory(&theory)
        .expect("should succeed with errors");

    assert_eq!(result.constants.len(), 1);
    assert_eq!(result.constants[0].name, "good_theorem");
    assert_eq!(result.statistics.translation_errors, 1);
    assert_eq!(result.statistics.theorems_imported, 1);
    assert!(result.has_errors());
    assert_eq!(result.errors.len(), 1);
}

#[test]
fn test_importer_error_handling_abort_on_error() {
    let bad_thm = IsaTheorem {
        name: "bad_theorem".to_owned(),
        props: vec![],
        proof_status: ProofStatus::Proved,
    };
    let good_thm = make_proved_theorem("good_theorem");

    let theory = make_theory("Abort.Theory", vec![bad_thm, good_thm]);
    let config = IsabelleImportConfig::builder()
        .continue_on_error(false)
        .build();
    let importer = IsabelleImporter::new(config);

    let result = importer.import_theory(&theory);
    assert!(result.is_err(), "should abort on first error");
}

#[test]
fn test_importer_error_handling_all_bad() {
    let bad1 = IsaTheorem {
        name: "bad1".to_owned(),
        props: vec![],
        proof_status: ProofStatus::Proved,
    };
    let bad2 = IsaTheorem {
        name: "bad2".to_owned(),
        props: vec![],
        proof_status: ProofStatus::Proved,
    };

    let theory = make_theory("AllBad.Theory", vec![bad1, bad2]);
    let importer = default_importer();

    let result = importer
        .import_theory(&theory)
        .expect("should succeed with errors collected");
    assert!(result.constants.is_empty());
    assert_eq!(result.statistics.translation_errors, 2);
    assert_eq!(result.errors.len(), 2);
}

#[test]
fn test_importer_error_is_display() {
    let err = IsabelleImportError::MissingTheoryName;
    let msg = err.to_string();
    assert_eq!(msg, "theory export missing name");

    let err = IsabelleImportError::NoYxmlFiles(PathBuf::from("/tmp/empty"));
    let msg = err.to_string();
    assert!(msg.contains("/tmp/empty"));
}

#[test]
fn test_importer_error_trust_level_mismatch_display() {
    let err = IsabelleImportError::TrustLevelMismatch {
        name: "thm1".to_owned(),
        status: ProofStatus::Axiomatized,
        required: TrustLevel::CertificateReplayed,
    };
    let msg = err.to_string();
    assert!(msg.contains("thm1"));
    assert!(msg.contains("Axiomatized"));
}

#[test]
fn test_importer_error_batch_display() {
    let err = IsabelleImportError::Batch {
        count: 3,
        first: "first error".to_owned(),
        errors: vec![],
    };
    let msg = err.to_string();
    assert!(msg.contains("3 errors"));
    assert!(msg.contains("first error"));
}

// ===== test_importer_statistics_tracking =====

#[test]
fn test_importer_statistics_tracking_basic() {
    let theory = make_theory(
        "Stats.Theory",
        vec![
            make_proved_theorem("thm1"),
            make_proved_theorem("thm2"),
            make_axiomatized_theorem("thm3"),
        ],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.statistics.theories_processed, 1);
    assert_eq!(result.statistics.theorems_imported, 3);
    assert_eq!(result.statistics.theorems_skipped, 0);
    assert_eq!(result.statistics.translation_errors, 0);
    assert_eq!(result.total_theorems_processed(), 3);
}

#[test]
fn test_importer_statistics_tracking_with_errors() {
    let bad = IsaTheorem {
        name: "bad".to_owned(),
        props: vec![],
        proof_status: ProofStatus::Proved,
    };
    let theory = make_theory("Stats.Errors", vec![make_proved_theorem("good"), bad]);
    let importer = default_importer();
    let result = importer.import_theory(&theory).expect("should succeed");

    assert_eq!(result.statistics.theorems_imported, 1);
    assert_eq!(result.statistics.translation_errors, 1);
    assert_eq!(result.total_theorems_processed(), 2);
}

#[test]
fn test_importer_statistics_merge() {
    let theory1 = make_theory("T1", vec![make_proved_theorem("a")]);
    let theory2 = make_theory(
        "T2",
        vec![make_proved_theorem("b"), make_axiomatized_theorem("c")],
    );

    let importer = default_importer();
    let mut r1 = importer.import_theory(&theory1).expect("t1 ok");
    let r2 = importer.import_theory(&theory2).expect("t2 ok");
    r1.merge(r2);

    assert_eq!(r1.statistics.theories_processed, 2);
    assert_eq!(r1.statistics.theorems_imported, 3);
    assert_eq!(r1.statistics.types_declared, 2); // nat in each
    assert_eq!(r1.statistics.consts_declared, 4); // zero + Suc in each
    assert_eq!(r1.statistics.dependencies_count, 2); // Pure in each
}

#[test]
fn test_importer_statistics_axiom_profile_summary() {
    let theory = make_theory(
        "Profile.Theory",
        vec![
            make_proved_theorem("proved1"),
            make_proved_theorem("proved2"),
            make_axiomatized_theorem("axiom1"),
        ],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    // All constants should have at least the base Isabelle profile.
    assert!(!result.statistics.axiom_profile_summary.is_empty());

    // Sum of all profile counts should equal theorems_imported.
    let total: usize = result.statistics.axiom_profile_summary.values().sum();
    assert_eq!(total, result.statistics.theorems_imported);
}

// ===== test_importer_axiom_profile_propagation =====

#[test]
fn test_importer_axiom_profile_propagation_proved() {
    let theory = make_theory("Profile.Proved", vec![make_proved_theorem("proved_thm")]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    let constant = &result.constants[0];
    assert!(constant.axiom_profile.contains(AxiomProfile::CLASSICAL));
    assert!(constant
        .axiom_profile
        .contains(AxiomProfile::EXTENSIONALITY));
    assert!(constant
        .axiom_profile
        .contains(AxiomProfile::ISABELLE_LCF_ERASED));
}

#[test]
fn test_importer_axiom_profile_propagation_axiomatized() {
    let theory = make_theory(
        "Profile.Axiomatized",
        vec![make_axiomatized_theorem("axiom_thm")],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    let constant = &result.constants[0];
    assert!(constant
        .axiom_profile
        .contains(AxiomProfile::ISABELLE_LCF_ERASED));
    assert_eq!(constant.trust_level, TrustLevel::PartiallyAxiomatized);
}

#[test]
fn test_importer_axiom_profile_in_provenance() {
    let theory = make_theory("Prov.Test", vec![make_proved_theorem("prov_thm")]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    let constant = &result.constants[0];
    // Provenance axiom_profile should match the constant's profile.
    assert_eq!(constant.provenance.axiom_profile, constant.axiom_profile);
}

#[test]
fn test_importer_axiom_profile_consistency_across_theory() {
    let theory = make_theory(
        "Consistent.Theory",
        vec![make_proved_theorem("p1"), make_proved_theorem("p2")],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    // All proved theorems from the same Isabelle theory should have the same
    // base axiom profile.
    let profile0 = result.constants[0].axiom_profile;
    let profile1 = result.constants[1].axiom_profile;
    assert_eq!(profile0, profile1);
}

// ===== test_importer_yxml_roundtrip =====

#[test]
fn test_importer_yxml_roundtrip_simple() {
    // Build YXML for a minimal theory with one theorem.
    let proof = yxml_leaf("proof", &[("status", "proved")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let true_const = yxml_elem("Const", &[("name", "HOL.True")], &prop_ty);
    let prop = yxml_elem("prop", &[], &true_const);

    let mut thm_content = Vec::new();
    thm_content.extend_from_slice(&proof);
    thm_content.extend_from_slice(&prop);
    let thm = yxml_elem("theorem", &[("name", "HOL.TrueI")], &thm_content);
    let theorems = yxml_elem("theorems", &[], &thm);
    let input = yxml_elem("theory", &[("name", "HOL.HOL")], &theorems);

    let yxml_str = std::str::from_utf8(&input).expect("should be valid UTF-8");
    let importer = default_importer();
    let result = importer
        .import_yxml(yxml_str)
        .expect("yxml import should succeed");

    assert_eq!(result.constants.len(), 1);
    assert_eq!(result.constants[0].name, "HOL.TrueI");
    assert_eq!(result.statistics.theories_processed, 1);
    assert_eq!(result.statistics.theorems_imported, 1);
}

#[test]
fn test_importer_yxml_roundtrip_bytes() {
    // Same as above but using import_yxml_bytes.
    let proof = yxml_leaf("proof", &[("status", "axiomatized")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let ax_const = yxml_elem("Const", &[("name", "HOL.ext")], &prop_ty);
    let prop = yxml_elem("prop", &[], &ax_const);

    let mut thm_content = Vec::new();
    thm_content.extend_from_slice(&proof);
    thm_content.extend_from_slice(&prop);
    let thm = yxml_elem("theorem", &[("name", "HOL.ext")], &thm_content);
    let theorems = yxml_elem("theorems", &[], &thm);
    let input = yxml_elem("theory", &[("name", "HOL.Ext")], &theorems);

    let importer = default_importer();
    let result = importer
        .import_yxml_bytes(&input)
        .expect("bytes import should succeed");

    assert_eq!(result.constants.len(), 1);
    assert_eq!(result.constants[0].name, "HOL.ext");
    assert_eq!(
        result.constants[0].trust_level,
        TrustLevel::PartiallyAxiomatized
    );
}

#[test]
fn test_importer_yxml_roundtrip_full_theory() {
    // Build a complete theory with deps, types, consts, and theorems.
    let dep = yxml_leaf("dep", &[("name", "Pure")]);
    let imports = yxml_elem("imports", &[], &dep);

    let nat_type = yxml_leaf("Type", &[("name", "nat")]);
    let td = yxml_elem("type_decl", &[("name", "nat")], &nat_type);
    let types = yxml_elem("types", &[], &td);

    let zero_ty = yxml_leaf("Type", &[("name", "nat")]);
    let zero_cd = yxml_elem("const_decl", &[("name", "zero")], &zero_ty);
    let consts = yxml_elem("consts", &[], &zero_cd);

    let proof = yxml_leaf("proof", &[("status", "proved")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let prop_const = yxml_elem("Const", &[("name", "Nat.Suc_not_Zero")], &prop_ty);
    let prop = yxml_elem("prop", &[], &prop_const);
    let mut thm_content = Vec::new();
    thm_content.extend_from_slice(&proof);
    thm_content.extend_from_slice(&prop);
    let thm = yxml_elem("theorem", &[("name", "Nat.Suc_not_Zero")], &thm_content);
    let theorems = yxml_elem("theorems", &[], &thm);

    let mut theory_content = Vec::new();
    theory_content.extend_from_slice(&imports);
    theory_content.extend_from_slice(&types);
    theory_content.extend_from_slice(&consts);
    theory_content.extend_from_slice(&theorems);
    let input = yxml_elem("theory", &[("name", "Nat.Nat")], &theory_content);

    let importer = default_importer();
    let result = importer
        .import_yxml_bytes(&input)
        .expect("full theory import should succeed");

    assert_eq!(result.constants.len(), 1);
    assert_eq!(result.constants[0].name, "Nat.Suc_not_Zero");
    assert_eq!(result.statistics.theories_processed, 1);
    assert_eq!(result.statistics.types_declared, 1);
    assert_eq!(result.statistics.consts_declared, 1);
    assert_eq!(result.statistics.dependencies_count, 1);
}

#[test]
fn test_importer_yxml_roundtrip_invalid() {
    let importer = default_importer();
    // Invalid YXML: not valid UTF-8 inside theory context won't cause parse
    // issues at the string level, so let's test with a valid string that's
    // not a theory.
    let input = yxml_leaf("not_a_theory", &[("name", "X")]);
    let result = importer.import_yxml_bytes(&input);
    assert!(result.is_err(), "non-theory YXML should fail");
}

#[test]
fn test_importer_yxml_roundtrip_multiple_theorems() {
    let proof = yxml_leaf("proof", &[("status", "proved")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);

    let mut theorems_content = Vec::new();
    for name in &["thm_a", "thm_b", "thm_c"] {
        let const_elem = yxml_elem("Const", &[("name", name)], &prop_ty);
        let prop = yxml_elem("prop", &[], &const_elem);
        let mut tc = Vec::new();
        tc.extend_from_slice(&proof);
        tc.extend_from_slice(&prop);
        let thm = yxml_elem("theorem", &[("name", name)], &tc);
        theorems_content.extend_from_slice(&thm);
    }
    let theorems = yxml_elem("theorems", &[], &theorems_content);
    let input = yxml_elem("theory", &[("name", "Multi.Thm")], &theorems);

    let importer = default_importer();
    let result = importer
        .import_yxml_bytes(&input)
        .expect("multi-theorem import should succeed");

    assert_eq!(result.constants.len(), 3);
    let names: Vec<&str> = result.constants.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(names, vec!["thm_a", "thm_b", "thm_c"]);
}

// ===== test_importer_config_builder =====

#[test]
fn test_importer_config_builder_defaults() {
    let config = IsabelleImportConfig::default();
    assert!(config.theory_search_paths.is_empty());
    assert!(!config.include_proofs);
    assert_eq!(config.trust_level, TrustLevel::PartiallyAxiomatized);
    assert!(config.continue_on_error);
    assert!(config.name_filter.is_none());
    assert_eq!(config.max_theorems_per_theory, 0);
}

#[test]
fn test_importer_config_builder_full() {
    let config = IsabelleImportConfig::builder()
        .theory_search_path("/tmp/theories")
        .theory_search_path("/opt/isabelle/export")
        .include_proofs(true)
        .trust_level(TrustLevel::CertificateReplayed)
        .continue_on_error(false)
        .name_filter("HOL.")
        .max_theorems_per_theory(100)
        .build();

    assert_eq!(config.theory_search_paths.len(), 2);
    assert_eq!(
        config.theory_search_paths[0],
        PathBuf::from("/tmp/theories")
    );
    assert_eq!(
        config.theory_search_paths[1],
        PathBuf::from("/opt/isabelle/export")
    );
    assert!(config.include_proofs);
    assert_eq!(config.trust_level, TrustLevel::CertificateReplayed);
    assert!(!config.continue_on_error);
    assert_eq!(config.name_filter, Some("HOL.".to_owned()));
    assert_eq!(config.max_theorems_per_theory, 100);
}

#[test]
fn test_importer_config_builder_name_filter_applied() {
    let theory = make_theory(
        "Filter.Theory",
        vec![
            make_proved_theorem("HOL.TrueI"),
            make_proved_theorem("HOL.FalseE"),
            make_proved_theorem("Nat.Suc_not_Zero"),
        ],
    );
    let config = IsabelleImportConfig::builder().name_filter("HOL.").build();
    let importer = IsabelleImporter::new(config);
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.constants.len(), 2);
    assert!(result.constants.iter().all(|c| c.name.contains("HOL.")));
    // The filtered theorem counts as skipped.
    assert_eq!(result.statistics.theorems_skipped, 1);
}

#[test]
fn test_importer_config_builder_max_theorems() {
    let theory = make_theory(
        "Max.Theory",
        vec![
            make_proved_theorem("thm1"),
            make_proved_theorem("thm2"),
            make_proved_theorem("thm3"),
            make_proved_theorem("thm4"),
            make_proved_theorem("thm5"),
        ],
    );
    let config = IsabelleImportConfig::builder()
        .max_theorems_per_theory(2)
        .build();
    let importer = IsabelleImporter::new(config);
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert_eq!(result.constants.len(), 2);
    assert_eq!(result.constants[0].name, "thm1");
    assert_eq!(result.constants[1].name, "thm2");
    // Remaining 3 are skipped.
    assert_eq!(result.statistics.theorems_skipped, 3);
}

#[test]
fn test_importer_config_builder_name_filter_no_match() {
    let theory = make_theory(
        "NoMatch.Theory",
        vec![
            make_proved_theorem("Nat.add"),
            make_proved_theorem("Nat.mul"),
        ],
    );
    let config = IsabelleImportConfig::builder().name_filter("HOL.").build();
    let importer = IsabelleImporter::new(config);
    let result = importer
        .import_theory(&theory)
        .expect("import should succeed");

    assert!(result.constants.is_empty());
    assert_eq!(result.statistics.theorems_skipped, 2);
}

// ===== test_translator_edge_cases =====

#[test]
fn test_translator_edge_case_nested_fun_types() {
    // nat => (nat => bool) — curried function type
    let theory = make_theory(
        "Nested.Fun",
        vec![IsaTheorem {
            name: "nested_fun_thm".to_owned(),
            props: vec![IsaTerm::const_of(
                "f",
                IsaType::fun(
                    IsaType::nullary("nat"),
                    IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("HOL.bool")),
                ),
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import nested fun");

    assert_eq!(result.constants.len(), 1);
    // The type should contain nested Pi types.
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("Pi") || type_debug.contains("Const"),
        "should translate nested function type: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_polymorphic_type() {
    // 'a list — polymorphic list type
    let theory = make_theory(
        "Poly.List",
        vec![IsaTheorem {
            name: "poly_thm".to_owned(),
            props: vec![IsaTerm::const_of(
                "nil",
                IsaType::Type {
                    name: "List.list".to_owned(),
                    args: vec![IsaType::tfree("'a")],
                },
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import polymorphic type");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    // The translated expr is the term (e.g., Const("nil", [])), not the type constructor.
    assert!(
        type_debug.contains("nil"),
        "should contain translated term reference: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_set_type() {
    // 'a set
    let theory = make_theory(
        "Poly.Set",
        vec![IsaTheorem {
            name: "set_thm".to_owned(),
            props: vec![IsaTerm::const_of(
                "empty_set",
                IsaType::Type {
                    name: "Set.set".to_owned(),
                    args: vec![IsaType::nullary("nat")],
                },
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import set type");

    assert_eq!(result.constants.len(), 1);
}

#[test]
fn test_translator_edge_case_prod_type() {
    // nat * bool — product type
    let theory = make_theory(
        "Prod.Type",
        vec![IsaTheorem {
            name: "prod_thm".to_owned(),
            props: vec![IsaTerm::const_of(
                "pair",
                IsaType::Type {
                    name: "Product_Type.prod".to_owned(),
                    args: vec![IsaType::nullary("nat"), IsaType::nullary("HOL.bool")],
                },
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import product type");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("pair"),
        "should contain pair term: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_class_constraint_type() {
    // 'a::linorder — type variable with class constraint
    let theory = make_theory(
        "Class.Constraint",
        vec![IsaTheorem {
            name: "class_thm".to_owned(),
            props: vec![IsaTerm::const_of(
                "sorted",
                IsaType::fun(
                    IsaType::Type {
                        name: "List.list".to_owned(),
                        args: vec![IsaType::TFree {
                            name: "'a".to_owned(),
                            sort: vec!["linorder".to_owned()],
                        }],
                    },
                    IsaType::nullary("HOL.bool"),
                ),
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import class constraint");

    assert_eq!(result.constants.len(), 1);
}

#[test]
fn test_translator_edge_case_schematic_var_in_term() {
    // Term with schematic variable ?P.0
    let theory = make_theory(
        "Schematic.Var",
        vec![IsaTheorem {
            name: "schematic_thm".to_owned(),
            props: vec![IsaTerm::Var {
                name: "P".to_owned(),
                index: 0,
                ty: IsaType::nullary("HOL.bool"),
            }],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import schematic var");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("?P"),
        "should reference ?P: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_schematic_var_nonzero_index() {
    let theory = make_theory(
        "Schematic.Index",
        vec![IsaTheorem {
            name: "schematic_idx_thm".to_owned(),
            props: vec![IsaTerm::Var {
                name: "x".to_owned(),
                index: 5,
                ty: IsaType::nullary("nat"),
            }],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import schematic var with index");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("?x") && type_debug.contains("5"),
        "should reference ?x with index 5: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_lambda_abstraction() {
    // \x::nat. x (identity function)
    let theory = make_theory(
        "Lambda.Test",
        vec![IsaTheorem {
            name: "id_thm".to_owned(),
            props: vec![IsaTerm::abs(
                "x",
                IsaType::nullary("nat"),
                IsaTerm::Bound(0),
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import lambda");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("Lam"),
        "should contain Lam: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_nested_application() {
    // f(g(x)) — nested application
    let nat_ty = IsaType::nullary("nat");
    let fun_ty = IsaType::fun(nat_ty.clone(), nat_ty.clone());

    let theory = make_theory(
        "Nested.App",
        vec![IsaTheorem {
            name: "nested_app_thm".to_owned(),
            props: vec![IsaTerm::app(
                IsaTerm::const_of("f", fun_ty.clone()),
                IsaTerm::app(
                    IsaTerm::const_of("g", fun_ty),
                    IsaTerm::const_of("x", nat_ty),
                ),
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import nested app");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("App"),
        "should contain App: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_implication_theorem() {
    // [| P |] ==> Q has props [P, Q] → translates to P → Q
    let theory = make_theory("Impl.Theory", vec![make_implication_theorem("impl_thm")]);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import implication");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    // Should have Pi (arrow) for the implication.
    assert!(
        type_debug.contains("Pi"),
        "implication should translate to Pi: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_multi_hypothesis_theorem() {
    // [| P; Q; R |] ==> S — three hypotheses
    let theory = make_theory(
        "MultiHyp.Theory",
        vec![IsaTheorem {
            name: "multi_hyp_thm".to_owned(),
            props: vec![
                IsaTerm::const_of("P", IsaType::nullary("HOL.bool")),
                IsaTerm::const_of("Q", IsaType::nullary("HOL.bool")),
                IsaTerm::const_of("R", IsaType::nullary("HOL.bool")),
                IsaTerm::const_of("S", IsaType::nullary("HOL.bool")),
            ],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import multi-hypothesis");

    assert_eq!(result.constants.len(), 1);
    // Count Pi nodes — should have at least 3 for P → Q → R → S.
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    let pi_count = type_debug.matches("Pi").count();
    assert!(
        pi_count >= 3,
        "should have >= 3 Pi for 3 hypotheses, got {pi_count}: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_custom_type_constructor() {
    // MyTheory.mytype(nat) — custom unary type constructor
    let theory = make_theory(
        "Custom.TypeCons",
        vec![IsaTheorem {
            name: "custom_type_thm".to_owned(),
            props: vec![IsaTerm::const_of(
                "mk",
                IsaType::Type {
                    name: "MyTheory.mytype".to_owned(),
                    args: vec![IsaType::nullary("nat")],
                },
            )],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import custom type constructor");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("mk"),
        "should reference mk term: {type_debug}"
    );
}

#[test]
fn test_translator_edge_case_int_type() {
    // Int.int — integer type
    let theory = make_theory(
        "Int.Theory",
        vec![IsaTheorem {
            name: "int_thm".to_owned(),
            props: vec![IsaTerm::const_of("zero", IsaType::nullary("Int.int"))],
            proof_status: ProofStatus::Proved,
        }],
    );
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import int type");

    assert_eq!(result.constants.len(), 1);
    let type_debug = format!("{:?}", result.constants[0].translated.type_expr);
    assert!(
        type_debug.contains("zero"),
        "should reference zero term: {type_debug}"
    );
}

// ===== Importer result API tests =====

#[test]
fn test_import_result_has_constants() {
    let theory = make_theory("API.Test", vec![make_proved_theorem("thm")]);
    let importer = default_importer();
    let result = importer.import_theory(&theory).expect("should succeed");
    assert!(result.has_constants());
}

#[test]
fn test_import_result_total_processed() {
    let bad_thm = IsaTheorem {
        name: "bad".to_owned(),
        props: vec![],
        proof_status: ProofStatus::Proved,
    };
    let theory = make_theory(
        "Total.Test",
        vec![
            make_proved_theorem("good1"),
            bad_thm,
            make_proved_theorem("good2"),
        ],
    );
    let importer = default_importer();
    let result = importer.import_theory(&theory).expect("should succeed");

    assert_eq!(result.total_theorems_processed(), 3);
}

// ===== Convenience function tests =====

#[test]
fn test_import_theory_default_function() {
    use super::importer::import_theory_default;

    let theory = make_theory("Convenience.Test", vec![make_proved_theorem("conv_thm")]);
    let result = import_theory_default(&theory).expect("should succeed");
    assert_eq!(result.constants.len(), 1);
}

#[test]
fn test_import_yxml_default_function() {
    use super::importer::import_yxml_default;

    let proof = yxml_leaf("proof", &[("status", "proved")]);
    let prop_ty = yxml_leaf("Type", &[("name", "prop")]);
    let true_const = yxml_elem("Const", &[("name", "HOL.True")], &prop_ty);
    let prop = yxml_elem("prop", &[], &true_const);

    let mut thm_content = Vec::new();
    thm_content.extend_from_slice(&proof);
    thm_content.extend_from_slice(&prop);
    let thm = yxml_elem("theorem", &[("name", "HOL.TrueI")], &thm_content);
    let theorems = yxml_elem("theorems", &[], &thm);
    let input = yxml_elem("theory", &[("name", "HOL.HOL")], &theorems);

    let yxml_str = std::str::from_utf8(&input).expect("valid UTF-8");
    let result = import_yxml_default(yxml_str).expect("should succeed");
    assert_eq!(result.constants.len(), 1);
}

// ===== Importer with_defaults test =====

#[test]
fn test_importer_with_defaults_creates_valid_importer() {
    let importer = IsabelleImporter::with_defaults();
    let config = importer.config();
    assert!(config.theory_search_paths.is_empty());
    assert!(!config.include_proofs);
    assert_eq!(config.trust_level, TrustLevel::PartiallyAxiomatized);
    assert!(config.continue_on_error);
}

// ===== Directory import error test =====

#[test]
fn test_importer_directory_nonexistent() {
    let importer = default_importer();
    let result = importer.import_directory(Path::new("/nonexistent/path/to/theories"));
    assert!(result.is_err());
}

#[test]
fn test_importer_file_nonexistent() {
    let importer = default_importer();
    let result = importer.import_file(Path::new("/nonexistent/file.yxml"));
    assert!(result.is_err());
}

// ===== Search path import test =====

#[test]
fn test_importer_all_search_paths_empty() {
    let config = IsabelleImportConfig::default(); // no search paths
    let importer = IsabelleImporter::new(config);
    let result = importer
        .import_all_search_paths()
        .expect("empty paths should succeed");
    assert!(result.constants.is_empty());
    assert_eq!(result.statistics.theories_processed, 0);
}

// ===== Large theory import test =====

#[test]
fn test_importer_large_theory() {
    let mut theorems = Vec::new();
    for i in 0..100 {
        theorems.push(make_proved_theorem(&format!("thm_{i}")));
    }
    let theory = make_theory("Large.Theory", theorems);
    let importer = default_importer();
    let result = importer
        .import_theory(&theory)
        .expect("should import 100 theorems");

    assert_eq!(result.constants.len(), 100);
    assert_eq!(result.statistics.theorems_imported, 100);
    assert!(!result.has_errors());
}

// ===== Provenance completeness test =====

#[test]
fn test_importer_provenance_fields_complete() {
    let theory = make_theory("Prov.Complete", vec![make_proved_theorem("Nat.add_comm")]);
    let importer = default_importer();
    let result = importer.import_theory(&theory).expect("should succeed");

    let c = &result.constants[0];
    assert_eq!(c.provenance.source, SourceSystem::Isabelle);
    assert_eq!(c.provenance.original_name, "Nat.add_comm");
    assert_eq!(
        c.provenance.source_file,
        Some("Prov.Complete.thy".to_owned())
    );
    assert_eq!(c.provenance.axiom_profile, c.axiom_profile);
}
