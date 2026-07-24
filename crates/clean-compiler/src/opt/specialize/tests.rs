// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for function specialization pass.

use super::*;
use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use clean_kernel::{Expr, FVarId, Name};
use std::collections::HashMap;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Helper to extract the first Const call name from code.
fn extract_first_const_call(code: &Code) -> Option<String> {
    match code {
        Code::Let(decl, body) => {
            if let LetValue::Const { name, .. } = &decl.value {
                Some(name.to_string())
            } else {
                extract_first_const_call(body)
            }
        }
        Code::Fun(_, body) | Code::JoinPoint(_, body) => extract_first_const_call(body),
        Code::Cases(cases) => {
            for alt in &cases.alts {
                let alt_body = alt.body();
                if let Some(name) = extract_first_const_call(alt_body) {
                    return Some(name);
                }
            }
            None
        }
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => None,
    }
}

/// Helper to extract the first FVar call from code.
fn extract_first_fvar_call(code: &Code) -> Option<(FVarId, Vec<Arg>)> {
    match code {
        Code::Let(decl, body) => {
            if let LetValue::FVar { fvar, args } = &decl.value {
                Some((*fvar, args.clone()))
            } else {
                extract_first_fvar_call(body)
            }
        }
        Code::Fun(_, body) | Code::JoinPoint(_, body) => extract_first_fvar_call(body),
        _ => None,
    }
}

#[test]
fn test_ground_tracking_literals() {
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );

    let mut ctx = SpecContext::new(name("test"));
    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let _ = specialize_code(&mut ctx, &mut state, &code, &config);

    assert!(
        ctx.ground.contains(&fvar(1)),
        "Literal binding should be ground"
    );
}

#[test]
fn test_ground_tracking_propagates() {
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_2"),
                nat_type(),
                LetValue::Const {
                    name: name("Nat.succ"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let mut ctx = SpecContext::new(name("test"));
    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let _ = specialize_code(&mut ctx, &mut state, &code, &config);

    assert!(ctx.ground.contains(&fvar(1)));
    assert!(ctx.ground.contains(&fvar(2)));
}

#[test]
fn test_non_ground_params() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: name("Nat.succ"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::ret(fvar(2)),
    );

    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));

    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let _ = specialize_code(&mut ctx, &mut state, &code, &config);

    assert!(
        !ctx.ground.contains(&fvar(2)),
        "Binding depending on param should not be ground"
    );
}

#[test]
fn test_spec_context_creation() {
    let ctx = SpecContext::new(name("test_fn"));
    assert!(ctx.scope.is_empty());
    assert!(ctx.ground.is_empty());
    assert_eq!(ctx.decl_name, name("test_fn"));
}

#[test]
fn test_spec_config_default() {
    let config = SpecConfig::default();
    assert!(config.specialize_instances);
    assert!(!config.specialize_higher_order);
    assert_eq!(config.max_depth, 5);
}

#[test]
fn test_spec_param_info_causes_specialization() {
    assert!(SpecParamInfo::FixedInst.causes_specialization());
    assert!(SpecParamInfo::FixedHO.causes_specialization());
    assert!(SpecParamInfo::User.causes_specialization());
    assert!(!SpecParamInfo::FixedNeutral.causes_specialization());
    assert!(!SpecParamInfo::Other.causes_specialization());
}

#[test]
fn test_specialize_returns_same_structure() {
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );

    let config = SpecConfig {
        specialize_instances: false,
        ..Default::default()
    };
    let result = specialize_in_code(&code, &config);

    assert!(
        matches!(&result, Code::Let(decl, body) if decl.fvar_id == fvar(1) && matches!(**body, Code::Return(_))),
        "Expected let binding with return body"
    );
}

#[test]
fn test_is_code_ground_return() {
    let ctx = SpecContext::new(name("test"));
    assert!(is_code_ground(&ctx, &Code::ret(fvar(1))));
}

#[test]
fn test_is_code_ground_return_non_ground() {
    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));
    assert!(!is_code_ground(&ctx, &Code::ret(fvar(1))));
}

#[test]
fn test_is_code_ground_let_chain() {
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );
    let ctx = SpecContext::new(name("test"));
    assert!(is_code_ground(&ctx, &code));
}

#[test]
fn test_is_code_ground_unreachable() {
    let ctx = SpecContext::new(name("test"));
    assert!(is_code_ground(&ctx, &Code::Unreachable(nat_type())));
}

#[test]
fn test_specialize_declaration() {
    use crate::lcnf::Param;

    let decl = Decl::new(
        name("test_fn"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("n"), nat_type())],
        Code::let_bind(
            LetDecl::new(fvar(2), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let config = SpecConfig::default();
    let (result, generated) = specialize(&decl, &config);

    assert_eq!(result.name, name("test_fn"));
    assert_eq!(result.params.len(), 1);
    assert!(generated.is_empty());
}

#[test]
fn test_specialize_cases() {
    use crate::lcnf::Param;

    let code = Code::Cases(Cases {
        type_name: name("TestType"),
        scrutinee: fvar(1),
        result_type: nat_type(),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("Ctor1"),
                params: vec![Param::new(fvar(10), name("x"), nat_type())],
                body: Box::new(Code::let_bind(
                    LetDecl::new(fvar(11), name("_1"), nat_type(), LetValue::nat(1)),
                    Code::ret(fvar(11)),
                )),
            },
            Alt::Default(Box::new(Code::let_bind(
                LetDecl::new(fvar(12), name("_2"), nat_type(), LetValue::nat(2)),
                Code::ret(fvar(12)),
            ))),
        ],
    });

    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));
    ctx.ground.insert(fvar(1));

    let mut state = SpecState::new();
    let config = SpecConfig::default();

    let result = specialize_code(&mut ctx, &mut state, &code, &config);

    assert!(
        matches!(&result, Code::Cases(cases) if cases.alts.len() == 2),
        "Expected Cases with 2 alts"
    );
}

#[test]
fn test_spec_entry_creation() {
    let entry = SpecEntry {
        decl_name: name("foo"),
        params_info: vec![SpecParamInfo::FixedInst, SpecParamInfo::Other],
        already_specialized: false,
    };

    assert_eq!(entry.decl_name, name("foo"));
    assert_eq!(entry.params_info.len(), 2);
    assert!(!entry.already_specialized);
}

#[test]
fn test_spec_registry() {
    let mut registry = SpecRegistry::new();
    let entry = SpecEntry {
        decl_name: name("foo"),
        params_info: vec![SpecParamInfo::FixedInst],
        already_specialized: false,
    };
    registry.register(entry);
    let entry = registry
        .get(&name("foo"))
        .expect("registered entry should be found");
    assert_eq!(
        entry.decl_name,
        name("foo"),
        "entry decl_name should match registered name"
    );
    assert!(
        registry.get(&name("bar")).is_none(),
        "unregistered name should not be found"
    );
}

#[test]
fn test_spec_state_name_generation() {
    let mut state = SpecState::new();
    let name1 = state.gen_spec_name(&name("List.map"), &name("main"));
    let name2 = state.gen_spec_name(&name("List.map"), &name("main"));
    assert_ne!(name1, name2);
    assert!(name1.to_string().contains("List.map"));
}

#[test]
fn test_spec_cache_lookup() {
    let mut state = SpecState::new();
    let key = SpecCacheKey {
        original: name("foo"),
        ground_args: vec![SpecKey::Ground(GroundValue::Lit(42)), SpecKey::Erased],
    };
    assert_eq!(state.lookup_cache(&key), None);
    state.cache_spec(key.clone(), name("foo_spec_0"));
    assert_eq!(state.lookup_cache(&key), Some(&name("foo_spec_0")));
}

#[test]
fn test_ground_value_from_literal() {
    let bindings: HashMap<FVarId, &LetValue> = HashMap::new();
    let lit_value = LetValue::nat(42);
    let result = let_value_to_ground(&lit_value, &bindings);
    assert_eq!(result, Some(GroundValue::Lit(42)));
}

#[test]
fn test_ground_value_from_const() {
    let bindings: HashMap<FVarId, &LetValue> = HashMap::new();
    let const_value = LetValue::Const {
        name: name("Nat.zero"),
        levels: vec![],
        args: vec![],
    };
    let result = let_value_to_ground(&const_value, &bindings);
    assert_eq!(result, Some(GroundValue::Const(name("Nat.zero"))));
}

#[test]
fn test_spec_key_from_ground_arg() {
    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));
    ctx.ground.insert(fvar(1));
    ctx.bindings.insert(fvar(1), LetValue::nat(42));
    let bindings_ref: HashMap<FVarId, &LetValue> =
        ctx.bindings.iter().map(|(k, v)| (*k, v)).collect();
    let key = arg_to_spec_key(&ctx, &Arg::FVar(fvar(1)), &bindings_ref);
    assert!(matches!(key, SpecKey::Ground(GroundValue::Lit(42))));
}

#[test]
fn test_spec_key_from_non_ground_arg() {
    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));
    let bindings_ref: HashMap<FVarId, &LetValue> = HashMap::new();
    let key = arg_to_spec_key(&ctx, &Arg::FVar(fvar(1)), &bindings_ref);
    assert!(matches!(key, SpecKey::Erased));
}

#[test]
fn test_has_specializable_ground_args() {
    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));
    ctx.ground.insert(fvar(1));
    let args_with_ground = vec![Arg::FVar(fvar(1)), Arg::Erased];
    assert!(has_specializable_ground_args(&ctx, &args_with_ground));
    let args_without_ground = vec![Arg::Erased, Arg::Type(nat_type())];
    assert!(!has_specializable_ground_args(&ctx, &args_without_ground));
}

#[test]
fn test_build_spec_key() {
    let mut ctx = SpecContext::new(name("test"));
    ctx.scope.insert(fvar(1));
    ctx.ground.insert(fvar(1));
    ctx.bindings.insert(fvar(1), LetValue::nat(100));
    let bindings_ref: HashMap<FVarId, &LetValue> =
        ctx.bindings.iter().map(|(k, v)| (*k, v)).collect();
    let args = vec![Arg::FVar(fvar(1)), Arg::Erased];
    let key = build_spec_key(&ctx, &name("foo"), &args, &bindings_ref);
    assert_eq!(key.original, name("foo"));
    assert_eq!(key.ground_args.len(), 2);
    assert!(matches!(
        &key.ground_args[0],
        SpecKey::Ground(GroundValue::Lit(100))
    ));
    assert!(matches!(&key.ground_args[1], SpecKey::Erased));
}

// Regression: specialize_code_with_index JoinPoint handler must save/restore
// scope and ground sets. specialize_code (line 484) does this correctly;
// specialize_code_with_index (line 956) was missing it after W3-717 fixed
// Code::Fun but missed Code::JoinPoint (same bug class).
#[test]
fn test_batch_joinpoint_scope_restore() {
    use crate::lcnf::Param;

    // Build: jp j (p : Nat) := return p; let x := 42; return x
    // JP param fvar(200) should NOT leak into scope after JP is processed.
    let jp_code = Code::JoinPoint(
        FunDecl::new(
            fvar(300),
            name("j"),
            vec![Param::new(fvar(200), name("p"), nat_type())],
            nat_type(),
            Code::ret(fvar(200)),
        ),
        Box::new(Code::let_bind(
            LetDecl::new(fvar(1), name("_x"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(1)),
        )),
    );

    let mut ctx = SpecContext::new(name("test"));

    let mut state = SpecState::new();
    let config = SpecConfig::default();
    let decl_index = DeclIndex::default();

    let _ = specialize_code_with_index(&mut ctx, &mut state, &jp_code, &config, &decl_index);

    // JP param fvar(200) must NOT be in scope after processing
    assert!(
        !ctx.scope.contains(&fvar(200)),
        "JoinPoint param fvar(200) leaked into continuation scope — \
         specialize_code_with_index must save/restore scope like specialize_code does"
    );

    // JP itself fvar(300) SHOULD be in scope (added after restore, like specialize_code)
    assert!(
        ctx.scope.contains(&fvar(300)),
        "JoinPoint fvar(300) should be added to scope after processing"
    );
}

mod batch;

mod local;

mod dce_interaction_tests;
