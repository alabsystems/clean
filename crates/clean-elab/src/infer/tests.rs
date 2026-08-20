// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for type elaboration
//!
//! Test modules are split by category for maintainability.
//! Submodules are under tests/ directory.
use super::*;

use clean_kernel::env::Declaration;
use clean_parser::{parse_decl_with_tactics, parse_expr, SurfaceDecl};

// ==== Test submodules (extracted from this file) ====
#[path = "tests/action_lifting.rs"]
mod action_lifting;
#[path = "tests/aesop_proof_chain.rs"]
mod aesop_proof_chain;
#[path = "tests/alias_patterns.rs"]
mod alias_patterns;
#[path = "tests/basic.rs"]
mod basic;
#[path = "tests/by_ascription.rs"]
mod by_ascription;
#[path = "tests/by_cases_dispatch.rs"]
mod by_cases_dispatch;
#[path = "tests/cache_reuse.rs"]
mod cache_reuse;
#[path = "tests/calc.rs"]
mod calc;
#[path = "tests/calc_multistep.rs"]
mod calc_multistep;
#[path = "tests/conv_proof_chain.rs"]
mod conv_proof_chain;
#[path = "tests/ctor_pattern_arity.rs"]
mod ctor_pattern_arity;
#[path = "tests/curried_pattern_lambda.rs"]
mod curried_pattern_lambda;
#[path = "tests/do_compat.rs"]
mod do_compat;
#[path = "tests/do_control_flow.rs"]
mod do_control_flow;
#[path = "tests/do_for_handlers.rs"]
mod do_for_handlers;
#[path = "tests/do_handlers.rs"]
mod do_handlers;
#[path = "tests/do_if_let_patterns.rs"]
mod do_if_let_patterns;
#[path = "tests/do_match_dispatch.rs"]
mod do_match_dispatch;
#[path = "tests/do_match_patterns.rs"]
mod do_match_patterns;
#[path = "tests/do_match_q_patterns.rs"]
mod do_match_q_patterns;
#[path = "tests/do_match_return_bodies.rs"]
mod do_match_return_bodies;
#[path = "tests/congr_arg_flex_head.rs"]
mod congr_arg_flex_head;
#[path = "tests/do_notation.rs"]
mod do_notation;
#[path = "tests/do_notation_state.rs"]
mod do_notation_state;
#[path = "tests/do_try_catch.rs"]
mod do_try_catch;
#[path = "tests/elab_rules.rs"]
mod elab_rules;
#[path = "tests/exact_universe_poly.rs"]
mod exact_universe_poly;
#[path = "tests/if_expr.rs"]
mod if_expr;
#[path = "tests/if_let_complex_patterns.rs"]
mod if_let_complex_patterns;
#[path = "tests/if_let_patterns.rs"]
mod if_let_patterns;
#[path = "tests/implicit.rs"]
mod implicit;
#[path = "tests/inductive.rs"]
mod inductive;
#[path = "tests/inductive_deriving_3431.rs"]
mod inductive_deriving_3431;
#[path = "tests/inductive_deriving_3432.rs"]
mod inductive_deriving_3432;
#[path = "tests/inductive_deriving_3434.rs"]
mod inductive_deriving_3434;
#[path = "tests/inductive_deriving_trk_e.rs"]
mod inductive_deriving_trk_e;
#[path = "tests/instance.rs"]
mod instance;
#[path = "tests/instance_elab_regressions.rs"]
mod instance_elab_regressions;
#[path = "tests/let_binding.rs"]
mod let_binding;
#[path = "tests/match_ctor_namespace.rs"]
mod match_ctor_namespace;
#[path = "tests/match_expr.rs"]
mod match_expr;
#[path = "tests/match_expr_nat_rec.rs"]
mod match_expr_nat_rec;
#[path = "tests/modifiers.rs"]
mod modifiers;
#[path = "tests/nat_literal_pattern_typecheck.rs"]
mod nat_literal_pattern_typecheck;
#[path = "tests/nested_ctor_patterns.rs"]
mod nested_ctor_patterns;
#[path = "tests/nested_inductive_match.rs"]
mod nested_inductive_match;
#[path = "tests/projection.rs"]
mod projection;
#[path = "tests/property_tests.rs"]
mod property_tests;
#[path = "tests/proptest_roundtrip.rs"]
mod proptest_roundtrip;
#[path = "tests/quotation.rs"]
mod quotation;
#[path = "tests/recursor_universe_params.rs"]
mod recursor_universe_params;
#[path = "tests/regression.rs"]
mod regression;
#[path = "tests/rw_proof_chain.rs"]
mod rw_proof_chain;
#[path = "tests/simp_chain_proof.rs"]
mod simp_chain_proof;
#[path = "tests/simp_namespace_proof.rs"]
mod simp_namespace_proof;
#[path = "tests/sorry.rs"]
mod sorry;
#[path = "tests/structural_recursion.rs"]
mod structural_recursion;
#[path = "tests/structure.rs"]
mod structure_tests;
#[path = "tests/suffices_tactic.rs"]
mod suffices_tactic;
#[path = "tests/tactic_error_boundary.rs"]
mod tactic_error_boundary;
#[path = "tests/trans_class.rs"]
mod trans_class;
#[path = "tests/traversal_regressions.rs"]
mod traversal_regressions;
#[path = "tests/universe_inst.rs"]
mod universe_inst;
#[path = "tests/user_tactic_exec.rs"]
mod user_tactic_exec;
#[path = "tests/verification/mod.rs"]
mod verification;

fn elab(input: &str) -> Result<Expr, ElabError> {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr(input).map_err(|e| ElabError::ParseError(e.to_string()))?;
    ctx.elaborate(&surface)
}

fn elab_with_env(env: &Environment, input: &str) -> Result<Expr, ElabError> {
    let mut ctx = ElabCtx::new(env);
    let surface = parse_expr(input).map_err(|e| ElabError::ParseError(e.to_string()))?;
    ctx.elaborate(&surface)
}

#[test]
fn test_elab_char_literal_lowers_to_char_of_nat() {
    // `'a'` (codepoint 97) elaborates to the canonical `Char.ofNat 97`.
    let expected = Expr::app(
        Expr::const_(Name::from_string("Char.ofNat"), vec![]),
        Expr::nat_lit(97),
    );
    assert_eq!(
        elab("'a'").expect("char literal should elaborate"),
        expected
    );
}

#[test]
fn test_elab_char_unicode_literal_uses_scalar_value() {
    // `'🙂'` written via a `\u{...}` escape (U+1F642 = 128578).
    let expected = Expr::app(
        Expr::const_(Name::from_string("Char.ofNat"), vec![]),
        Expr::nat_lit(128_578),
    );
    assert_eq!(
        elab(r"'\u{1F642}'").expect("unicode char literal should elaborate"),
        expected
    );
}

/// Build the canonical lowering of a float literal absent any `OfScientific`
/// instance: `Float.ofScientific <mantissa> <Bool sign> <decExp>`.
fn float_of_scientific(mantissa: u64, exp_sign: bool, dec_exp: u64) -> Expr {
    let sign = Expr::const_(
        Name::from_string(if exp_sign { "Bool.true" } else { "Bool.false" }),
        vec![],
    );
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Float.ofScientific"), vec![]),
                Expr::nat_lit(mantissa),
            ),
            sign,
        ),
        Expr::nat_lit(dec_exp),
    )
}

#[test]
fn test_elab_float_literal_decimal_lowers_to_of_scientific() {
    // `3.14` denotes `314 * 10^-2`, i.e. mantissa 314, negative exponent 2.
    // With no `OfScientific` instance in scope it defaults to the native
    // `Float.ofScientific` form that the kernel reducer understands.
    assert_eq!(
        elab("3.14").expect("float literal should elaborate"),
        float_of_scientific(314, true, 2)
    );
}

#[test]
fn test_elab_float_literal_negative_exponent_lowers_to_of_scientific() {
    // `1e-5` denotes `1 * 10^-5`.
    assert_eq!(
        elab("1e-5").expect("float literal should elaborate"),
        float_of_scientific(1, true, 5)
    );
}

#[test]
fn test_elab_float_literal_zero_lowers_to_of_scientific() {
    // `0.0` denotes `0 * 10^-1` (digits preserved verbatim, not normalized).
    assert_eq!(
        elab("0.0").expect("float literal should elaborate"),
        float_of_scientific(0, true, 1)
    );
}

fn pair_env() -> Environment {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let pair = Name::from_string("Pair");

    // Pair : Type
    let pair_type = Expr::type_();

    // mk : Prop → Prop → Pair
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::const_(pair.clone(), vec![]),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: mk_type,
            }],
        }],
    };

    env.add_inductive(decl).unwrap();
    env.register_structure_fields(
        pair,
        vec![Name::from_string("fst"), Name::from_string("snd")],
    )
    .unwrap();

    env
}

fn namespace_env() -> Environment {
    let mut env = Environment::new();
    let base_name = Name::from_string("whnf_to");
    let namespaced = Name::from_string("whnf_to.refl");

    env.add_decl(Declaration::Axiom {
        name: base_name,
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: namespaced,
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    env
}

fn pair_env_with_namespaced_const() -> Environment {
    let mut env = pair_env();
    let pair = Name::from_string("Pair");
    let pair_val = Name::from_string("pairVal");

    env.add_decl(Declaration::Axiom {
        name: pair_val,
        level_params: vec![],
        type_: Expr::const_(pair, vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pairVal.snd"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    env
}

/// Test namespace-only prefix case (#497, #501):
/// When `Foo` is not a constant but `Foo.bar` is, the elaborator should
/// resolve `Foo.bar` as the constant rather than failing with UnknownIdent("Foo").
fn namespace_only_env() -> Environment {
    let mut env = Environment::new();
    // Only add Foo.bar, NOT Foo itself
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo.bar"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env
}

fn parse_decl_for_elab(input: &str) -> Result<SurfaceDecl, ElabError> {
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    parse_decl_with_tactics(input, &patterns).map_err(|e| ElabError::ParseError(e.to_string()))
}

fn elab_decl(input: &str) -> Result<ElabResult, ElabError> {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_decl_for_elab(input)?;
    ctx.elab_decl(&surface)
}

/// Elaborate a declaration with a full prelude environment.
///
/// Unlike [`elab_decl`], this initializes the environment with all prelude
/// constants (DecidableEq, BEq, Nat, etc.), which is required for tests that
/// exercise derive handlers for universe-polymorphic typeclasses.
/// Fixes #3408: derive tests using `elab_decl` silently produced 0 instances
/// because the typeclass constants weren't in the environment.
fn elab_decl_with_prelude(input: &str) -> Result<ElabResult, ElabError> {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_decl_for_elab(input)?;
    ctx.elab_decl(&surface)
}
