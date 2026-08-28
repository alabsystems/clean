// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the stratified Hurkens block (parse/paren/order/reverify).
//! Split out of the parent module for file size; declared from `mod.rs`
//! behind `#[cfg(test)]`.

use super::*;
use crate::test_utils::parse_check;

/// Every plain-def source in registration order.
const DEF_SOURCES: [&str; 13] = [
    SRC_POWR,
    SRC_POWR2,
    SRC_U0_ARROW,
    SRC_U0_BODY,
    SRC_U0,
    SRC_POWR_LEVEL,
    SRC_POWR2_LEVEL,
    SRC_U0_ARROW_LEVEL,
    SRC_U0_LEVEL,
    SRC_HK_MAX_NAT,
    SRC_HK_LEVEL_VAL,
    SRC_HK_LEVEL_ZERO_FLAG,
    SRC_HK_NONPI_FLAG,
];

/// Every (name, type, value) triple registered via `add_definition`, in
/// registration order.
const THEOREM_SOURCES: [(&str, &str, &str); 16] = [
    (
        "powr_level_val_one",
        TY_POWR_LEVEL_VAL_ONE,
        VAL_POWR_LEVEL_VAL_ONE,
    ),
    (
        "powr2_level_val_one",
        TY_POWR2_LEVEL_VAL_ONE,
        VAL_POWR2_LEVEL_VAL_ONE,
    ),
    (
        "U0_arrow_level_val_zero",
        TY_U0_ARROW_LEVEL_VAL_ZERO,
        VAL_U0_ARROW_LEVEL_VAL_ZERO,
    ),
    (
        "U0_level_val_one",
        TY_U0_LEVEL_VAL_ONE,
        VAL_U0_LEVEL_VAL_ONE,
    ),
    (
        "level_succ_ne_zero",
        TY_LEVEL_SUCC_NE_ZERO,
        VAL_LEVEL_SUCC_NE_ZERO,
    ),
    (
        "level_imax_ne_zero",
        TY_LEVEL_IMAX_NE_ZERO,
        VAL_LEVEL_IMAX_NE_ZERO,
    ),
    ("hk_kill_nonpi", TY_HK_KILL_NONPI, VAL_HK_KILL_NONPI),
    (
        "hk_nonpi_flag_witness",
        TY_HK_NONPI_FLAG_WITNESS,
        VAL_HK_NONPI_FLAG_WITNESS,
    ),
    (
        "typingctx_powr_ty",
        TY_TYPINGCTX_POWR_TY,
        VAL_TYPINGCTX_POWR_TY,
    ),
    (
        "typingctx_powr2_ty",
        TY_TYPINGCTX_POWR2_TY,
        VAL_TYPINGCTX_POWR2_TY,
    ),
    (
        "typingctx_U0_formable",
        TY_TYPINGCTX_U0_FORMABLE,
        VAL_TYPINGCTX_U0_FORMABLE,
    ),
    (
        "typingctx_pi_not_small",
        TY_TYPINGCTX_PI_NOT_SMALL,
        VAL_TYPINGCTX_PI_NOT_SMALL,
    ),
    (
        "typingctx_powr2_not_small",
        TY_TYPINGCTX_POWR2_NOT_SMALL,
        VAL_TYPINGCTX_POWR2_NOT_SMALL,
    ),
    (
        "typingctx_U0_not_small",
        TY_TYPINGCTX_U0_NOT_SMALL,
        VAL_TYPINGCTX_U0_NOT_SMALL,
    ),
    (
        "typingctx_powr2_never_small",
        TY_TYPINGCTX_POWR2_NEVER_SMALL,
        VAL_TYPINGCTX_POWR2_NEVER_SMALL,
    ),
    (
        "typingctx_U0_never_small",
        TY_TYPINGCTX_U0_NEVER_SMALL,
        VAL_TYPINGCTX_U0_NEVER_SMALL,
    ),
];

/// Parse-check every generated source — the fast guard for the commonest
/// failure class (syntax-level assembly mistakes invisible to cargo check).
#[test]
fn test_hurkens_block_sources_parse() {
    for src in DEF_SOURCES {
        parse_check(src).unwrap_or_else(|e| panic!("def source should parse: {e}\n{src}"));
    }
    parse_check(SRC_TYPINGCTX_PI_SMALL_INV)
        .unwrap_or_else(|e| panic!("typingctx_pi_small_inv should parse: {e}"));
    for (name, ty, val) in THEOREM_SOURCES {
        let assembled = format!("def {name} : {ty} := {val}");
        parse_check(&assembled)
            .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
    }
    for (_, ty, val) in [
        (
            "typingctx_powr_witness",
            TY_TYPINGCTX_POWR_WITNESS,
            VAL_TYPINGCTX_POWR_WITNESS,
        ),
        (
            "typingctx_U0_witness",
            TY_TYPINGCTX_U0_WITNESS,
            VAL_TYPINGCTX_U0_WITNESS,
        ),
    ] {
        let assembled = format!("def hk_parse_probe : {ty} := {val}");
        parse_check(&assembled)
            .unwrap_or_else(|e| panic!("witness should parse as a def: {e}\n{assembled}"));
    }
}

/// Paren balance on every source (a cheap structural guard for the long
/// single-line proof terms).
#[test]
fn test_hurkens_block_sources_paren_balanced() {
    let mut all: Vec<String> = DEF_SOURCES.iter().map(|s| (*s).to_string()).collect();
    all.push(SRC_TYPINGCTX_PI_SMALL_INV.to_string());
    for (_, ty, val) in THEOREM_SOURCES {
        all.push(ty.to_string());
        all.push(val.to_string());
    }
    all.push(TY_TYPINGCTX_POWR_WITNESS.to_string());
    all.push(VAL_TYPINGCTX_POWR_WITNESS.to_string());
    all.push(TY_TYPINGCTX_U0_WITNESS.to_string());
    all.push(VAL_TYPINGCTX_U0_WITNESS.to_string());
    for src in &all {
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open in: {src}");
        }
        assert_eq!(depth, 0, "unbalanced parens in: {src}");
    }
}

/// THE ORDER GUARD for the inversion recursor: minor premises must follow
/// TypingCtx's constructor declaration order (var sort pi lam app const
/// let_ — dependent_sn_richmodel.rs:109-115). The arm count alone cannot
/// catch a transposition.
#[test]
fn test_hurkens_inversion_minor_order() {
    let landmarks = [
        "(he : Eq KExpr (KExpr.bvar i) (KExpr.pi PA PB))", // var
        "(he : Eq KExpr (KExpr.sort n) (KExpr.pi PA PB))", // sort
        "level_imax_ne_zero n m",                          // pi
        "(he : Eq KExpr (KExpr.lam A b) (KExpr.pi PA PB))", // lam
        "(he : Eq KExpr (KExpr.app f a) (KExpr.pi PA PB))", // app
        "(he : Eq KExpr (KExpr.const cn us) (KExpr.pi PA PB))", // const
        "(he : Eq KExpr (KExpr.let_ lty lv lb) (KExpr.pi PA PB))", // let_
    ];
    let src = SRC_TYPINGCTX_PI_SMALL_INV;
    let mut cursor = 0usize;
    for (position, mark) in landmarks.iter().enumerate() {
        let found = src[cursor..]
            .find(mark)
            .unwrap_or_else(|| panic!("minor premise {position} ({mark}) missing or out of order"));
        cursor += found + mark.len();
    }
}

/// Registration + kernel re-verification against the substitution bundle:
/// the stage registers every constant, and the ground witnesses plus both
/// halves of the block re-typecheck in the live kernel environment.
#[test]
fn test_hurkens_block_registered_and_reverifies() {
    let spec = crate::test_utils::build_substitution_spec_with_stack();
    for name in [
        "powr",
        "powr2",
        "U0_arrow",
        "U0_body",
        "U0",
        "powr_level",
        "powr2_level",
        "U0_arrow_level",
        "U0_level",
        "hk_max_nat",
        "hk_level_val",
        "powr_level_val_one",
        "powr2_level_val_one",
        "U0_arrow_level_val_zero",
        "U0_level_val_one",
        "hk_level_zero_flag",
        "level_succ_ne_zero",
        "level_imax_ne_zero",
        "hk_nonpi_flag",
        "hk_kill_nonpi",
        "hk_nonpi_flag_witness",
        "typingctx_powr_ty",
        "typingctx_powr2_ty",
        "typingctx_U0_formable",
        "typingctx_pi_small_inv",
        "typingctx_pi_not_small",
        "typingctx_powr2_not_small",
        "typingctx_U0_not_small",
        "typingctx_powr2_never_small",
        "typingctx_U0_never_small",
        "typingctx_powr_witness",
        "typingctx_U0_witness",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the stratified_hurkens_block stage"
        );
    }
    for name in [
        "typingctx_U0_formable",
        "typingctx_U0_not_small",
        "typingctx_powr2_not_small",
        "typingctx_powr_witness",
        "typingctx_U0_witness",
        "hk_nonpi_flag_witness",
    ] {
        spec.verify_definition(name).unwrap_or_else(|e| {
            panic!("{name} should re-typecheck in the spec environment: {e:?}")
        });
    }
}
