// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{FVarId, Name};

fn payload(name: &str) -> proof_state::ObligationLocalHypothesis {
    proof_state::ObligationLocalHypothesis {
        name: name.to_owned(),
        type_expr: Some(Expr::type_()),
        type_pp: "Type".to_owned(),
        value_expr: Some(Expr::prop()),
        value_pp: Some("Prop".to_owned()),
    }
}

#[test]
fn obligation_ingress_preserves_source_identity_and_original_typed_payloads() {
    let input = [payload("h.dot"), payload("«h.dot»"), payload("«_»")];
    let locals = open_obligation_local_context(&input).unwrap();
    assert_eq!(locals.len(), input.len());
    assert_eq!(locals[0].name.name(), &Name::anon().str("h").str("dot"));
    assert_eq!(locals[1].name.name(), &Name::anon().str("h.dot"));
    assert_ne!(locals[0].name, locals[1].name);
    assert!(!locals[2].name.is_unescaped_component("_"));
    for (index, (local, wire)) in locals.iter().zip(&input).enumerate() {
        assert_eq!(local.fvar, FVarId::new(index as u64));
        assert_eq!(Some(&local.ty), wire.type_expr.as_ref());
        assert_eq!(local.value, wire.value_expr);
    }
}

#[test]
fn obligation_ingress_refuses_non_source_selectors_and_pretty_only_types() {
    for text in ["", "_", ".h", "_root_.h", "x + y", "<non-source local>"] {
        let error = open_obligation_local_context(&[payload(text)]).unwrap_err();
        assert_eq!(error.code, crate::rpc::error_codes::INVALID_PARAMS);
        assert_eq!(
            error.data.as_ref().unwrap()["code"],
            "INVALID_LOCAL_CONTEXT"
        );
    }
    let mut pretty_only = payload("«h.dot»");
    pretty_only.type_expr = None;
    let error = open_obligation_local_context(&[pretty_only]).unwrap_err();
    assert_eq!(
        error.data.as_ref().unwrap()["code"],
        "PRETTY_ONLY_LOCAL_CONTEXT"
    );
}
