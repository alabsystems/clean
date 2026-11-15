// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::{Environment, ExprKind};
use std::sync::Arc;

fn candidate(value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string("transport").num(7),
        level_params: vec![Name::from_string("u").num(3)],
        type_: Expr::prop(),
        value,
    }
}

#[test]
fn theorem_carrier_preserves_structural_names_and_supplied_unchecked_witness() {
    let original = candidate(Expr::bvar(0));
    let bytes = encode_theorem_dag(&original).unwrap();
    let restored = decode_theorem_dag(&bytes).unwrap();
    let (
        Declaration::Theorem {
            name: a,
            level_params: b,
            type_: c,
            value: d,
        },
        Declaration::Theorem {
            name: e,
            level_params: f,
            type_: g,
            value: h,
        },
    ) = (&original, &restored)
    else {
        panic!("theorem fields");
    };
    assert_eq!((a, b, c, d), (e, f, g, h));
    // Decode success must not turn an ill-scoped witness into kernel evidence.
    let environment = Environment::new();
    let checker = crate::tc::TypeChecker::new(&environment);
    assert!(checker.check_type(h, g).is_err());
}

#[test]
fn theorem_carrier_preserves_shared_graph_without_tree_expansion() {
    let mut shared = Arc::new(Expr::bvar(0));
    for _ in 0..32 {
        shared = Arc::new(Expr::app_arc(Arc::clone(&shared), shared));
    }
    let bytes = encode_theorem_dag(&candidate((*shared).clone())).unwrap();
    assert!(
        bytes.len() < 4096,
        "a 33-node DAG expanded: {} bytes",
        bytes.len()
    );
    let Declaration::Theorem { value, .. } = decode_theorem_dag(&bytes).unwrap() else {
        panic!("theorem");
    };
    let mut current = &value;
    for _ in 0..32 {
        let ExprKind::App(left, right) = current.kind() else {
            panic!("shared application")
        };
        assert!(Arc::ptr_eq(left, right));
        current = left;
    }
    assert!(matches!(current.kind(), ExprKind::BVar(0)));
}

#[test]
fn theorem_carrier_refuses_other_domains_flags_trailing_and_every_truncation() {
    let original = encode_theorem_dag(&candidate(Expr::bvar(0))).unwrap();
    for end in 0..original.len() {
        assert!(
            decode_theorem_dag(&original[..end]).is_err(),
            "prefix {end}"
        );
    }
    for offset in [0, 7, 8, 12] {
        let mut bytes = original.clone();
        bytes[offset] ^= 1;
        assert!(decode_theorem_dag(&bytes).is_err(), "header byte {offset}");
    }
    let mut trailing = original;
    trailing.push(0);
    assert!(decode_theorem_dag(&trailing).is_err());
    let environment_bytes = Environment::new().to_dag_bincode().unwrap();
    assert!(decode_theorem_dag(&environment_bytes).is_err());
    let axiom = Declaration::Axiom {
        name: Name::from_string("not_a_theorem"),
        level_params: vec![],
        type_: Expr::prop(),
    };
    assert!(encode_theorem_dag(&axiom).is_err());
}

#[test]
fn theorem_carrier_refuses_dangling_expression_roots() {
    // A well-framed theorem payload with no graph cannot satisfy either root.
    let mut payload = Encoder::new(Encoding::V2);
    let mut projection = Projection::default();
    Name::from_string("missing")
        .to_wire(&mut projection)
        .unwrap()
        .write(&mut payload)
        .unwrap();
    Vec::<WName>::new().write(&mut payload).unwrap();
    Ref(0).write(&mut payload).unwrap();
    Ref(0).write(&mut payload).unwrap();
    let mut out = Encoder::new(Encoding::V2);
    out.raw(MAGIC).unwrap();
    out.u32(1).unwrap();
    out.u32(0).unwrap();
    out.bytes(&payload.finish()).unwrap();
    out.len(0).unwrap();
    assert!(decode_theorem_dag(&out.finish()).is_err());
}
