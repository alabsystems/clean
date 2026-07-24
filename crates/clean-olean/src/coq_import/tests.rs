// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    parse_vo, translate_term, Binder, CastKind, Constr, CoqName, CoqSort, UniverseInstance,
    UniverseLevel, OCAML_MARSHAL_MAGIC,
};
use clean_kernel::{BinderInfo, ExprKind, Level, Name};

#[test]
fn coq_translate_prop_sort() {
    let expr = translate_term(&Constr::prop()).expect("translate Prop");
    assert!(matches!(expr.kind(), ExprKind::Sort(level) if level.is_zero()));
}

#[test]
fn coq_translate_type_product() {
    let term = Constr::Prod {
        binder: Binder::explicit("A", Constr::type0()),
        body: Box::new(Constr::type0()),
    };
    let expr = translate_term(&term).expect("translate product");
    let ExprKind::Pi(binder, domain, body) = expr.kind() else {
        panic!("expected Pi, got {:?}", expr.kind());
    };
    assert_eq!(binder.info, BinderInfo::Default);
    assert!(matches!(domain.kind(), ExprKind::Sort(level) if *level == Level::succ(Level::zero())));
    assert!(matches!(body.kind(), ExprKind::Sort(level) if *level == Level::succ(Level::zero())));
}

#[test]
fn coq_translate_lambda_rel() {
    let term = Constr::Lambda {
        binder: Binder::explicit("p", Constr::prop()),
        body: Box::new(Constr::rel(1)),
    };
    let expr = translate_term(&term).expect("translate lambda");
    let ExprKind::Lam(_, domain, body) = expr.kind() else {
        panic!("expected lambda, got {:?}", expr.kind());
    };
    assert!(matches!(domain.kind(), ExprKind::Sort(level) if level.is_zero()));
    assert!(matches!(body.kind(), ExprKind::BVar(0)));
}

#[test]
fn coq_translate_let_and_cast() {
    let term = Constr::LetIn {
        name: Some("x".to_string()),
        type_: Box::new(Constr::Sort(CoqSort::Set)),
        value: Box::new(Constr::Cast {
            term: Box::new(Constr::Sort(CoqSort::Set)),
            kind: CastKind::Default,
            ty: Box::new(Constr::type0()),
        }),
        body: Box::new(Constr::rel(1)),
    };
    let expr = translate_term(&term).expect("translate let");
    let ExprKind::Let(name, ty, value, body, non_dep) = expr.kind() else {
        panic!("expected let, got {:?}", expr.kind());
    };
    assert_eq!(name.to_string(), "x");
    assert!(!non_dep);
    assert!(matches!(ty.kind(), ExprKind::Sort(level) if *level == Level::succ(Level::zero())));
    assert!(matches!(value.kind(), ExprKind::Sort(level) if *level == Level::succ(Level::zero())));
    assert!(matches!(body.kind(), ExprKind::BVar(0)));
}

#[test]
fn coq_translate_const_universe_params() {
    let term = Constr::Const {
        name: CoqName::from_dotted("Coq.Init.Logic.eq"),
        universes: UniverseInstance {
            levels: vec![UniverseLevel::Param("u".to_string())],
        },
    };
    let expr = translate_term(&term).expect("translate const");
    let ExprKind::Const(name, levels) = expr.kind() else {
        panic!("expected const, got {:?}", expr.kind());
    };
    assert_eq!(name.to_string(), "Coq.Init.Logic.eq");
    assert_eq!(levels.len(), 1);
    assert_eq!(levels[0], Level::param(Name::from_string("u")));
}

#[test]
fn coq_parse_vo_scaffold_preserves_payload_and_trailer() {
    let payload = [0xAA, 0xBB, 0xCC];
    let trailer = [0xDD, 0xEE];
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&OCAML_MARSHAL_MAGIC.to_be_bytes());
    bytes.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    bytes.extend_from_slice(&1u32.to_be_bytes());
    bytes.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    bytes.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    bytes.extend_from_slice(&payload);
    bytes.extend_from_slice(&trailer);

    let parsed = parse_vo(&bytes).expect("parse vo scaffold");
    assert_eq!(parsed.header.data_len, 3);
    assert_eq!(parsed.sections.len(), 2);
    assert_eq!(parsed.sections[0].bytes, payload);
    assert_eq!(parsed.sections[1].bytes, trailer);
}
