// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for expand_reset fast/slow path semantic equivalence (#1112).
//!
//! Verifies that for any valid reset/reuse pattern, `make_fast_path` and
//! `make_slow_path` produce semantically equivalent transformations:
//! - Both eliminate all `_reuse` operations
//! - Fast path uses `_set` (mutate in place), slow path uses `Ctor` (allocate new)
//! - Both reference the same constructor field arguments
//! - Full expansion is idempotent

use super::rewrite::make_slow_path;
use super::*;
use crate::rc::pseudo_op;
use crate::rc::FVarIdAllocator;
use clean_kernel::{Expr, FVarId, Name};
use proptest::prelude::*;

// ═══════════════════════════════════════════════════════════════════════════
// Generic Code tree walkers
// ═══════════════════════════════════════════════════════════════════════════

/// Check if any let-value in the code tree satisfies the predicate.
fn any_let_value(code: &Code, pred: &dyn Fn(&LetValue) -> bool) -> bool {
    match code {
        Code::Let(decl, body) => pred(&decl.value) || any_let_value(body, pred),
        Code::Fun(f, body) => any_let_value(&f.body, pred) || any_let_value(body, pred),
        Code::JoinPoint(j, body) => any_let_value(&j.body, pred) || any_let_value(body, pred),
        Code::Cases(cases) => cases.alts.iter().any(|alt| match alt {
            Alt::Ctor { body, .. } => any_let_value(body, pred),
            Alt::Default(body) => any_let_value(body, pred),
        }),
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => false,
    }
}

/// Check if any let-decl in the code tree satisfies the predicate.
fn any_let_decl(code: &Code, pred: &dyn Fn(&LetDecl) -> bool) -> bool {
    match code {
        Code::Let(decl, body) => pred(decl) || any_let_decl(body, pred),
        Code::Fun(f, body) => any_let_decl(&f.body, pred) || any_let_decl(body, pred),
        Code::JoinPoint(j, body) => any_let_decl(&j.body, pred) || any_let_decl(body, pred),
        Code::Cases(cases) => cases.alts.iter().any(|alt| match alt {
            Alt::Ctor { body, .. } => any_let_decl(body, pred),
            Alt::Default(body) => any_let_decl(body, pred),
        }),
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => false,
    }
}

/// Collect FVarIds from let-decls using an extractor function.
fn collect_from_lets(code: &Code, extract: &dyn Fn(&LetDecl) -> Vec<FVarId>) -> Vec<FVarId> {
    let mut result = Vec::new();
    collect_from_lets_impl(code, extract, &mut result);
    result
}

fn collect_from_lets_impl(
    code: &Code,
    extract: &dyn Fn(&LetDecl) -> Vec<FVarId>,
    out: &mut Vec<FVarId>,
) {
    match code {
        Code::Let(decl, body) => {
            out.extend(extract(decl));
            collect_from_lets_impl(body, extract, out);
        }
        Code::Fun(f, body) => {
            collect_from_lets_impl(&f.body, extract, out);
            collect_from_lets_impl(body, extract, out);
        }
        Code::JoinPoint(j, body) => {
            collect_from_lets_impl(&j.body, extract, out);
            collect_from_lets_impl(body, extract, out);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_from_lets_impl(body, extract, out),
                    Alt::Default(body) => collect_from_lets_impl(body, extract, out),
                }
            }
        }
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => {}
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Code inspection helpers built on generic walkers
// ═══════════════════════════════════════════════════════════════════════════

fn contains_reuse(code: &Code) -> bool {
    any_let_value(code, &|v| is_reuse_op(v))
}

fn contains_ctor(code: &Code) -> bool {
    any_let_value(code, &|v| matches!(v, LetValue::Ctor { .. }))
}

fn contains_dec(code: &Code) -> bool {
    any_let_value(
        code,
        &|v| matches!(v, LetValue::Const { name, .. } if name.to_string() == pseudo_op::DEC),
    )
}

fn count_in_lets(code: &Code, pred: &dyn Fn(&LetDecl) -> bool) -> usize {
    match code {
        Code::Let(decl, body) => (if pred(decl) { 1 } else { 0 }) + count_in_lets(body, pred),
        Code::Fun(f, body) => count_in_lets(&f.body, pred) + count_in_lets(body, pred),
        Code::JoinPoint(j, body) => count_in_lets(&j.body, pred) + count_in_lets(body, pred),
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_in_lets(body, pred),
                Alt::Default(body) => count_in_lets(body, pred),
            })
            .sum(),
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => 0,
    }
}

fn count_set_ops(code: &Code) -> usize {
    count_in_lets(
        code,
        &|decl| matches!(&decl.value, LetValue::Const { name, .. } if name.to_string() == pseudo_op::SET),
    )
}

fn collect_set_field_args(code: &Code) -> Vec<FVarId> {
    collect_from_lets(code, &|decl| {
        if let LetValue::Const { name, args, .. } = &decl.value {
            if name.to_string() == pseudo_op::SET {
                // _set args: [obj_fvar, Index(n), value_fvar]
                if let Some(Arg::FVar(v)) = args.get(2) {
                    return vec![*v];
                }
            }
        }
        vec![]
    })
}

fn collect_ctor_field_args(code: &Code) -> Vec<FVarId> {
    collect_from_lets(code, &|decl| {
        if let LetValue::Ctor { args, .. } = &decl.value {
            args.iter().filter_map(|a| a.as_fvar()).collect()
        } else {
            vec![]
        }
    })
}

// ═══════════════════════════════════════════════════════════════════════════
// Proptest strategies for generating valid LCNF with reuse patterns
// ═══════════════════════════════════════════════════════════════════════════

// FVarId constants — low IDs avoid collision with allocator range (20M+).
const OBJ_FVAR: u64 = 1;
const RESET_VAR: u64 = 2;
const RESULT_FVAR: u64 = 3;
const FIELD_START: u64 = 100;
const EXTRA_START: u64 = 200;
const SCRUTINEE: u64 = 300;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Configuration for a generated reuse body.
#[derive(Clone, Debug)]
struct ReuseConfig {
    num_fields: usize,        // 1..=5 field arguments
    use_native: bool,         // native LetValue::Reuse vs legacy Const
    with_cases: bool,         // wrap reuse in Cases (both branches)
    extra_lets_before: usize, // 0..=2 lets before reuse
    extra_lets_after: usize,  // 0..=2 lets after reuse
}

fn arb_reuse_config() -> impl Strategy<Value = ReuseConfig> {
    (
        1..=5usize,
        proptest::bool::ANY,
        proptest::bool::ANY,
        0..=2usize,
        0..=2usize,
    )
        .prop_map(
            |(num_fields, use_native, with_cases, extra_lets_before, extra_lets_after)| {
                ReuseConfig {
                    num_fields,
                    use_native,
                    with_cases,
                    extra_lets_before,
                    extra_lets_after,
                }
            },
        )
}

/// Build a Code body with a reuse operation and optional surrounding structure.
fn build_reuse_body(config: &ReuseConfig) -> Code {
    let reset_var = fvar(RESET_VAR);
    let result_fvar = fvar(RESULT_FVAR);

    let field_args: Vec<Arg> = (0..config.num_fields)
        .map(|i| Arg::FVar(fvar(FIELD_START + i as u64)))
        .collect();

    let reuse_value = if config.use_native {
        LetValue::Reuse {
            slot: reset_var,
            ctor_name: name("T.mk"),
            levels: vec![],
            args: field_args,
        }
    } else {
        let mut args = vec![Arg::FVar(reset_var)];
        args.extend(field_args);
        LetValue::Const {
            name: name(pseudo_op::REUSE),
            levels: vec![],
            args,
        }
    };

    // Build inside-out: return -> extra_after -> reuse -> extra_before
    let mut inner = Code::ret(result_fvar);

    for i in 0..config.extra_lets_after {
        let extra_fvar = fvar(EXTRA_START + 50 + i as u64);
        inner = Code::let_bind(
            LetDecl::new(
                extra_fvar,
                name("_extra_after"),
                nat_type(),
                LetValue::nat(0),
            ),
            inner,
        );
    }

    inner = Code::let_bind(
        LetDecl::new(result_fvar, name("result"), nat_type(), reuse_value),
        inner,
    );

    for i in (0..config.extra_lets_before).rev() {
        let extra_fvar = fvar(EXTRA_START + i as u64);
        inner = Code::let_bind(
            LetDecl::new(
                extra_fvar,
                name("_extra_before"),
                nat_type(),
                LetValue::nat(0),
            ),
            inner,
        );
    }

    if config.with_cases {
        Code::Cases(Cases {
            type_name: name("T"),
            result_type: Expr::const_str("_"),
            scrutinee: fvar(SCRUTINEE),
            alts: vec![
                Alt::Ctor {
                    ctor_name: name("T.mk"),
                    params: vec![],
                    body: Box::new(inner.clone()),
                },
                Alt::Default(Box::new(inner)),
            ],
        })
    } else {
        inner
    }
}

/// Build `let w := reset x; <reuse_body>` for full expand_reset_reuse testing.
fn build_reset_reuse_code(config: &ReuseConfig) -> Code {
    Code::let_bind(
        LetDecl::new(
            fvar(RESET_VAR),
            name("w"),
            nat_type(),
            LetValue::Const {
                name: name(pseudo_op::RESET),
                levels: vec![],
                args: vec![Arg::FVar(fvar(OBJ_FVAR))],
            },
        ),
        build_reuse_body(config),
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// Property tests
// ═══════════════════════════════════════════════════════════════════════════

// Property 1: Fast path eliminates all _reuse operations.
proptest! {
    #[test]
    fn prop_fast_path_eliminates_reuse(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let fast = make_fast_path(fvar(RESET_VAR), fvar(OBJ_FVAR), &body, &mut alloc);
        prop_assert!(!contains_reuse(&fast),
            "Fast path should not contain _reuse.\nConfig: {:?}\nOutput:\n{}", config, fast);
    }
}

// Property 2: Slow path eliminates all _reuse operations.
proptest! {
    #[test]
    fn prop_slow_path_eliminates_reuse(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let slow = make_slow_path(fvar(OBJ_FVAR), &body, &mut alloc);
        prop_assert!(!contains_reuse(&slow),
            "Slow path should not contain _reuse.\nConfig: {:?}\nOutput:\n{}", config, slow);
    }
}

// Property 3: Fast path generates one _set per FVar field argument.
proptest! {
    #[test]
    fn prop_fast_path_set_count_matches_fields(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let fast = make_fast_path(fvar(RESET_VAR), fvar(OBJ_FVAR), &body, &mut alloc);
        let set_count = count_set_ops(&fast);
        // When with_cases, reuse appears in both branches
        let expected = if config.with_cases { config.num_fields * 2 } else { config.num_fields };
        prop_assert_eq!(set_count, expected,
            "Expected {} _set ops, got {}.\nConfig: {:?}\nOutput:\n{}",
            expected, set_count, config, fast);
    }
}

// Property 4: Slow path generates Ctor for each reuse site.
proptest! {
    #[test]
    fn prop_slow_path_has_ctor(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let slow = make_slow_path(fvar(OBJ_FVAR), &body, &mut alloc);
        prop_assert!(contains_ctor(&slow),
            "Slow path should contain Ctor.\nConfig: {:?}\nOutput:\n{}", config, slow);
    }
}

// Property 5: Fast and slow paths reference the same field arguments.
// Core semantic equivalence: both paths write the same values, just differently.
proptest! {
    #[test]
    fn prop_same_field_args(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc_fast = FVarIdAllocator::for_expand_reset();
        let mut alloc_slow = FVarIdAllocator::for_expand_reset();
        let fast = make_fast_path(fvar(RESET_VAR), fvar(OBJ_FVAR), &body, &mut alloc_fast);
        let slow = make_slow_path(fvar(OBJ_FVAR), &body, &mut alloc_slow);
        let mut fast_args: Vec<u64> = collect_set_field_args(&fast).iter().map(|f| f.as_u64()).collect();
        let mut slow_args: Vec<u64> = collect_ctor_field_args(&slow).iter().map(|f| f.as_u64()).collect();
        fast_args.sort();
        slow_args.sort();
        prop_assert_eq!(fast_args, slow_args,
            "Field args should match.\nConfig: {:?}\nFast:\n{}\nSlow:\n{}", config, fast, slow);
    }
}

// Property 6: Slow path decs the original object.
proptest! {
    #[test]
    fn prop_slow_path_decs_original(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let slow = make_slow_path(fvar(OBJ_FVAR), &body, &mut alloc);
        prop_assert!(contains_dec(&slow),
            "Slow path should dec original.\nConfig: {:?}\nOutput:\n{}", config, slow);
    }
}

// Property 7: Fast path does NOT dec the original (it reuses the memory).
proptest! {
    #[test]
    fn prop_fast_path_no_dec(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let fast = make_fast_path(fvar(RESET_VAR), fvar(OBJ_FVAR), &body, &mut alloc);
        prop_assert!(!contains_dec(&fast),
            "Fast path should NOT dec original.\nConfig: {:?}\nOutput:\n{}", config, fast);
    }
}

// Property 8: Fast path binds reset_var via `_reuse_slot`.
proptest! {
    #[test]
    fn prop_fast_path_binds_reset_var(config in arb_reuse_config()) {
        let body = build_reuse_body(&config);
        let mut alloc = FVarIdAllocator::for_expand_reset();
        let fast = make_fast_path(fvar(RESET_VAR), fvar(OBJ_FVAR), &body, &mut alloc);
        prop_assert!(
            any_let_decl(&fast, &|decl| decl.name.to_string() == pseudo_op::REUSE_SLOT),
            "Fast path should bind via _reuse_slot.\nConfig: {:?}\nOutput:\n{}", config, fast);
    }
}

// Property 9: Full expand_reset_reuse leaves no _reuse remaining.
proptest! {
    #[test]
    fn prop_full_expansion_no_reuse_remaining(config in arb_reuse_config()) {
        let code = build_reset_reuse_code(&config);
        let result = expand_reset_reuse_in_code(&code);
        prop_assert!(!contains_reuse(&result),
            "Full expansion should leave no _reuse.\nConfig: {:?}\nOutput:\n{}", config, result);
    }
}

// Property 10: Full expand_reset_reuse is idempotent (no _reset after first pass).
proptest! {
    #[test]
    fn prop_full_expansion_idempotent(config in arb_reuse_config()) {
        let code = build_reset_reuse_code(&config);
        let once = expand_reset_reuse_in_code(&code);
        let twice = expand_reset_reuse_in_code(&once);
        let once_str = format!("{once}");
        let twice_str = format!("{twice}");
        prop_assert_eq!(once_str, twice_str,
            "Expanding twice should equal once.\nConfig: {:?}", config);
    }
}
