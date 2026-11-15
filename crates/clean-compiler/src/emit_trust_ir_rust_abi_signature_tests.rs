// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the Rust-ABI signatures and Rust-callee declarations.

use crate::ir::IRType;
use crate::lcnf::{Decl, DeclValue, ExternEntry, Param};
use crate::rust_abi::*;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Name};

fn arrow(params: &[&str], result: &str) -> Expr {
    params.iter().rev().fold(Expr::const_str(result), |acc, p| {
        Expr::arrow(Expr::const_str(p), acc)
    })
}

/// The prelude plus `inc : UInt64 → UInt64` declared exactly as Trust's
/// `declare_rust_callees` declares a Rust `fn` (an `Opaque` with the hidden
/// inhabitant `fun _ => UInt64.ofNat 0`), plus a Lean definition `leanInc`.
fn env() -> Environment {
    let mut env = Environment::with_prelude();
    let hidden = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt64"),
        Expr::app(Expr::const_str("UInt64.ofNat"), Expr::nat_lit(0)),
    );
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("inc"),
        level_params: vec![],
        type_: arrow(&["UInt64"], "UInt64"),
        value: hidden.clone(),
    })
    .expect("declare the Rust callee");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("leanInc"),
        level_params: vec![],
        type_: arrow(&["UInt64"], "UInt64"),
        value: hidden,
        is_reducible: true,
    })
    .expect("declare the Lean definition");
    let nat_hidden = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::nat_lit(0),
    );
    env.add_decl(Declaration::Opaque {
        name: Name::from_string("natCallee"),
        level_params: vec![],
        type_: arrow(&["Nat"], "Nat"),
        value: nat_hidden,
    })
    .expect("declare a Nat-typed opaque");
    env
}

#[test]
fn carrier_signature_reads_every_pi_binder_and_the_codomain() {
    let env = env();
    assert_eq!(
        carrier_signature(&env, &Name::from_string("inc")),
        Ok(CarrierSignature {
            params: vec![Carrier::UInt64],
            result: Carrier::UInt64,
        })
    );
    assert_eq!(
        carrier_signature(&env, &Name::from_string("Nat.add")),
        Ok(CarrierSignature {
            params: vec![Carrier::Nat, Carrier::Nat],
            result: Carrier::Nat,
        })
    );
    assert_eq!(
        carrier_signature(&env, &Name::from_string("Bool.not")),
        Ok(CarrierSignature {
            params: vec![Carrier::Bool],
            result: Carrier::Bool,
        })
    );
}

#[test]
fn carrier_signature_refuses_a_non_carrier_position_by_name() {
    let env = env();
    // `String.length : String → Nat` — the parameter is not a carrier.
    let err = carrier_signature(&env, &Name::from_string("String.length"))
        .expect_err("String is not a carrier");
    assert!(
        matches!(&err, RustAbiError::NotACarrier { name, position, .. }
            if name == "String.length" && position == "parameter 0"),
        "{err}"
    );
    // `Char` is no carrier either (its result position here).
    let err = carrier_signature(&env, &Name::from_string("Char.ofNat"))
        .expect_err("Char is not a carrier");
    assert!(
        matches!(&err, RustAbiError::NotACarrier { position, .. } if position == "result"),
        "{err}"
    );
    let err = carrier_signature(&env, &Name::from_string("noSuchDecl")).expect_err("unknown");
    assert!(matches!(err, RustAbiError::UnknownConstant { .. }), "{err}");
}

#[test]
fn rust_callee_decl_is_an_extern_at_the_carrier_signature() {
    let env = env();
    let callee = RustCallee {
        constant: Name::from_string("inc"),
        symbol: "_ZN4demo3inc17h0123456789abcdefE".to_string(),
    };
    let decl = rust_callee_decl(&env, &callee).expect("the Trust-declared opaque is a callee");
    assert!(decl.is_extern(), "a Rust callee has no code body");
    assert_eq!(decl.params.len(), 1);
    let sig = RustExternSig::of_decl(&decl).expect("a rust-backend extern");
    assert_eq!(sig.symbol, callee.symbol);
    assert_eq!(sig.params, vec![IRType::UInt64]);
    assert_eq!(sig.ret, IRType::UInt64);
    // The hidden inhabitant is NOT what a call compiles to: the extern has
    // no value at all.
    assert!(matches!(decl.body, DeclValue::Extern(_)));
}

#[test]
fn rust_callee_decl_refuses_a_lean_definition_and_nat() {
    let env = env();
    let err = rust_callee_decl(
        &env,
        &RustCallee {
            constant: Name::from_string("leanInc"),
            symbol: "leanInc".to_string(),
        },
    )
    .expect_err("a definition's value would be compiled instead of calling Rust");
    assert!(
        matches!(err, RustAbiError::RustCalleeNotOpaque { .. }),
        "{err}"
    );
    let err = rust_callee_decl(
        &env,
        &RustCallee {
            constant: Name::from_string("natCallee"),
            symbol: "nat_callee".to_string(),
        },
    )
    .expect_err("Nat has no Rust carrier ABI");
    assert!(matches!(err, RustAbiError::RustCalleeNat { .. }), "{err}");
}

#[test]
fn a_c_extern_is_not_a_rust_callee() {
    let decl = Decl::extern_decl(
        Name::from_string("cfun"),
        vec![],
        Expr::const_str("UInt64"),
        vec![Param::new(
            FVarId::new(0),
            Name::anon(),
            Expr::const_str("UInt64"),
        )],
        vec![ExternEntry {
            backend: "c".to_string(),
            name: "cfun".to_string(),
        }],
    );
    assert_eq!(RustExternSig::of_decl(&decl), None);
}
