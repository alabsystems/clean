// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the FFI bridge module.

use super::*;
use crate::lcnf::ExternEntry;
use clean_kernel::{Expr, FVarId};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ════════════════════════════════════════════════════════════════════
// ImplementedByMap tests
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_implemented_by_map_empty() {
    let map = ImplementedByMap::new();
    assert!(map.is_empty());
    assert_eq!(map.len(), 0);
    assert!(!map.has_binding(&name("foo")));
    assert!(map.resolve(&name("foo")).is_none());
}

#[test]
fn test_implemented_by_map_register_and_resolve() {
    let mut map = ImplementedByMap::new();
    map.register(name("List.mapImpl"), name("List.mapFast"));

    assert!(!map.is_empty());
    assert_eq!(map.len(), 1);
    assert!(map.has_binding(&name("List.mapImpl")));
    assert_eq!(
        map.resolve(&name("List.mapImpl")),
        Some(&name("List.mapFast"))
    );
    assert!(!map.has_binding(&name("List.filter")));
}

#[test]
fn test_implemented_by_map_overwrite() {
    let mut map = ImplementedByMap::new();
    map.register(name("f"), name("g"));
    map.register(name("f"), name("h"));

    assert_eq!(map.len(), 1);
    assert_eq!(map.resolve(&name("f")), Some(&name("h")));
}

#[test]
fn test_implemented_by_map_from_env() {
    let mut env = Environment::new();
    // Must add a constant declaration so from_env can find it when iterating
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: name("List.map"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add axiom");
    env.register_implemented_by(name("List.map"), name("List.mapTR"));

    let map = ImplementedByMap::from_env(&env);
    assert_eq!(map.resolve(&name("List.map")), Some(&name("List.mapTR")));
}

// ════════════════════════════════════════════════════════════════════
// FfiBridge tests
// ════════════════════════════════════════════════════════════════════

#[test]
fn test_ffi_bridge_from_env_externs() {
    let mut env = Environment::new();
    let decl_name = name("IO.Handle.mk");
    // Use Prop as the type -- it's valid in any empty environment
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: decl_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add axiom");
    env.register_extern(decl_name.clone(), "clean_io_handle_mk".to_owned());

    let bridge = FfiBridge::from_env(&env);
    assert_eq!(bridge.num_externs(), 1);
    assert!(bridge.is_extern(&decl_name));

    let ext = bridge.get_extern(&decl_name).expect("should find extern");
    assert_eq!(ext.c_name, "clean_io_handle_mk");
    assert_eq!(ext.lean_name, decl_name);
}

#[test]
fn test_ffi_bridge_from_env_implemented_by() {
    let mut env = Environment::new();
    // Must add a constant so from_env finds the implemented_by binding
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: name("Array.map"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add axiom");
    env.register_implemented_by(name("Array.map"), name("Array.mapFast"));

    let bridge = FfiBridge::from_env(&env);
    assert_eq!(bridge.num_implemented_by(), 1);
    assert_eq!(
        bridge.resolve_implemented_by(&name("Array.map")),
        Some(&name("Array.mapFast"))
    );
}

#[test]
fn test_ffi_bridge_resolve_call_direct() {
    let env = Environment::new();
    let bridge = FfiBridge::from_env(&env);

    match bridge.resolve_call(&name("myFunc")) {
        CallTarget::Direct(n) => assert_eq!(*n, name("myFunc")),
        other => panic!("expected Direct, got {:?}", other),
    }
}

#[test]
fn test_ffi_bridge_resolve_call_redirect() {
    let mut env = Environment::new();
    // Add constant declaration so from_env finds the binding
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: name("List.map"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add axiom");
    env.register_implemented_by(name("List.map"), name("List.mapTR"));

    let bridge = FfiBridge::from_env(&env);
    match bridge.resolve_call(&name("List.map")) {
        CallTarget::Redirect(n) => assert_eq!(*n, name("List.mapTR")),
        other => panic!("expected Redirect, got {:?}", other),
    }
}

#[test]
fn test_ffi_bridge_resolve_call_extern() {
    let mut env = Environment::new();
    let decl_name = name("lean_io_prim_handle_mk");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: decl_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add axiom");
    env.register_extern(decl_name.clone(), "clean_io_handle_mk".to_owned());

    let bridge = FfiBridge::from_env(&env);
    match bridge.resolve_call(&decl_name) {
        CallTarget::Extern(ext) => {
            assert_eq!(ext.c_name, "clean_io_handle_mk");
        }
        other => panic!("expected Extern, got {:?}", other),
    }
}

#[test]
fn test_ffi_bridge_resolve_call_implemented_by_to_extern() {
    let mut env = Environment::new();
    let axiom = name("IO.println");
    let impl_name = name("IO.println.impl");

    // Add both the axiom and the implementation as declarations
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: axiom.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add axiom");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: impl_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("should add impl axiom");
    env.register_extern(impl_name.clone(), "clean_io_println".to_owned());
    env.register_implemented_by(axiom.clone(), impl_name.clone());

    let bridge = FfiBridge::from_env(&env);

    // Resolving the axiom should chain through implementedBy to the extern
    match bridge.resolve_call(&axiom) {
        CallTarget::Extern(ext) => {
            assert_eq!(ext.c_name, "clean_io_println");
        }
        other => panic!("expected Extern (via implementedBy), got {:?}", other),
    }
}

#[test]
fn test_ffi_bridge_from_lcnf_externs() {
    let decl_name = name("clean_box");
    let param = Param::new(FVarId::new(0), name("x"), Expr::const_str("USize"));
    let return_ty = Expr::const_str("Nat");
    let attr = ExternAttr {
        entries: vec![ExternEntry {
            backend: "c".to_owned(),
            name: "clean_box".to_owned(),
        }],
    };

    let bridge =
        FfiBridge::from_lcnf_externs(&[(decl_name.clone(), &[param][..], &return_ty, &attr)]);

    assert_eq!(bridge.num_externs(), 1);
    let ext = bridge.get_extern(&decl_name).expect("should find extern");
    assert_eq!(ext.c_name, "clean_box");
}

#[test]
fn test_ffi_bridge_skips_non_c_backends() {
    let decl_name = name("llvm_only_fn");
    let return_ty = Expr::const_str("Nat");
    let attr = ExternAttr {
        entries: vec![ExternEntry {
            backend: "llvm".to_owned(),
            name: "llvm_fn".to_owned(),
        }],
    };

    let bridge = FfiBridge::from_lcnf_externs(&[(decl_name.clone(), &[][..], &return_ty, &attr)]);

    assert_eq!(bridge.num_externs(), 0);
    assert!(!bridge.is_extern(&decl_name));
}

#[test]
fn test_implemented_by_map_iter() {
    let mut map = ImplementedByMap::new();
    map.register(name("a"), name("b"));
    map.register(name("c"), name("d"));

    let entries: Vec<_> = map.iter().collect();
    assert_eq!(entries.len(), 2);
}
