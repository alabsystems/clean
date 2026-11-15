// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Refutations of satisfiable problems that read a user symbol as the built-in operator it is
//! spelled like, through `clean cert verify-external`'s adapter (`verify_alethe_proof`).
//!
//! Each `soundness/bs_u_*.{smt2,alethe}` pair comes from AY's r18 cross-review of its
//! consumer-certificate mirror (2026-10-07). The problem names a symbol with a built-in's
//! spelling: a `declare-fun`, `define-fun`, `define-fun-rec`, datatype constructor or selector,
//! `:named` label or sort (`c00`..`c06`, `c09`..`c17`, `d20`, `d21`, `d24`..`d31`), a quoted
//! numeral (`c07`, `c08`), a local `|false|` (`d22`, `d32`), or the global `|false|` (`e01`,
//! `(declare-const |false| Bool) (assert |false|)`). The proof refutes it with `evaluate`, which
//! is sound only if the symbol is the built-in: `(+ 1 1)` folds to `2`, `(and true true)` to
//! `true`, `|false|` to `false`.
//!
//! Under SMT-LIB 2.6 every problem is satisfiable or ill-formed: a theory symbol may not be
//! redeclared, and `|false|` is the symbol `false`. AY answered `sat` for each one it parses
//! (r18 verifier). Clean 6a916983, the commit Trust pinned, fully verified the same-arity cases
//! `c05`, `c14`..`c16`, `d20`, `d21`, `d24`..`d31` and `e01`; the declaration was accepted,
//! and the parser then read every use of the name as the built-in. Fix 38
//! (third-party/carcara/DOWNSTREAM.md) refuses such a declaration while parsing the problem, and a
//! local binding shadows the built-in, so each pair must be refused for the reason named here: at
//! parse time for a declaration, at step `t1` for the rest.

use super::verify_alethe_proof;

macro_rules! pair {
    ($name:literal) => {
        (
            $name,
            include_str!(concat!("soundness/", $name, ".smt2")),
            include_str!(concat!("soundness/", $name, ".alethe")),
        )
    };
}

const fn with_reason(
    (name, problem, proof): (&'static str, &'static str, &'static str),
    reason: &'static str,
) -> (&'static str, &'static str, &'static str, &'static str) {
    (name, problem, proof, reason)
}

/// (fixture, the refusal the diagnostic must name)
const BUILTIN_SPELLINGS: [(&str, &str, &str, &str); 31] = [
    with_reason(
        pair!("bs_u_c00_control_decl_ite"),
        "'ite' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c01_definefun_ite"),
        "'ite' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c02_definefun_not"),
        "'not' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c03_definefun_eq"),
        "'=' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c04_dt_ctor_ite"),
        "'ite' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c05_dt_ctor_and"),
        "'and' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c06_dt_sel_not"),
        "'not' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c07_quoted_numeral"),
        "step 't1' with rule 'evaluate'",
    ),
    with_reason(
        pair!("bs_u_c08_quoted_numeral_b"),
        "step 't1' with rule 'evaluate'",
    ),
    with_reason(
        pair!("bs_u_c09_dt_ctor_distinct"),
        "'distinct' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c10_definesort_int"),
        "'Int' is a built-in sort and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c11_declare_sort_bool"),
        "'Bool' is a built-in sort and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c12_definefunrec_ite"),
        "'define-fun-rec' is not supported",
    ),
    with_reason(
        pair!("bs_u_c13_named_ite"),
        "'ite' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c14_dt_ctor_plus"),
        "'+' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c15_definefun_plus"),
        "'+' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c16_dt_ctor_bvadd"),
        "'bvadd' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_c17_dt_ctor_eq"),
        "'=' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d20_declfun_plus"),
        "'+' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d21_declfun_and2"),
        "'and' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d22_let_quoted_false"),
        "step 't1' with rule 'evaluate'",
    ),
    with_reason(
        pair!("bs_u_d24_definefun_minus"),
        "'-' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d25_declfun_le"),
        "'<=' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d26_definefun_or"),
        "'or' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d27_dtctor_or"),
        "'or' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d28_definefun_xor"),
        "'xor' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d29_definefun_ite3"),
        "'ite' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d30_declfun_ite3"),
        "'ite' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d31_definefun_eq2"),
        "'=' is a built-in operator and cannot be declared or defined",
    ),
    with_reason(
        pair!("bs_u_d32_exists_quoted_false"),
        "step 't1' with rule 'evaluate'",
    ),
    with_reason(
        pair!("bs_u_e01_declconst_quoted_false"),
        "'false' is a built-in operator and cannot be declared or defined",
    ),
];

#[test]
fn refutations_through_a_builtin_spelling_are_refused() {
    for (name, problem, proof, reason) in BUILTIN_SPELLINGS {
        let diagnostic = match verify_alethe_proof(problem, proof) {
            Err(error) => error.to_string(),
            Ok(valid) => {
                panic!("{name}: a refutation of a satisfiable problem returned Ok({valid})")
            }
        };
        assert!(
            diagnostic.contains(reason),
            "{name}: expected {reason:?}, got: {diagnostic}"
        );
    }
}
