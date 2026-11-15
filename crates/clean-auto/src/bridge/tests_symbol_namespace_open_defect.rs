// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OPEN DEFECT, pinned so it fails loudly the day it is fixed:
//! `docs/issues/2026-09-28-smt-bridge-translation-defects.md` §1.
//!
//! The bridge names solver constants by strings in ONE namespace: a constant
//! by its Lean name (`term_lowering.rs`, `Const` arm), a string literal `s` as
//! `str_{s}`, a free variable as `fvar_{id}`. `Name`'s `Display` escapes
//! nothing, so a constant can be NAMED like a literal's or a local's symbol
//! and the two become one solver term. Measured consequence: after
//! `def str_a : String := "b"`, the FALSE goal `"a" = str_a` is UNSAT to the
//! bridge, which reconstructs `Eq.refl "a"`; only the kernel check stops it
//! (`tactic/tests/decide_finite_forall.rs`,
//! `test_decide_kernel_gate_refuses_smt_name_collision`).
//!
//! When the namespaces are separated, these assertions flip: update the issue
//! file and turn each into the positive statement.

use super::super::*;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, FVarId};

#[test]
fn open_defect_a_string_literal_and_a_constant_share_a_solver_symbol() {
    let env = Environment::with_prelude();
    let mut bridge = SmtBridge::new(&env);
    let literal = Expr::str_lit("a");
    let constant = Expr::const_(Name::from_string("str_a"), vec![]);
    let lit_term = bridge.translate_term(&literal).expect("literal translates");
    let const_term = bridge
        .translate_term(&constant)
        .expect("constant translates");
    assert_eq!(
        lit_term, const_term,
        "the collision is FIXED — update docs/issues/2026-09-28-smt-bridge-translation-defects.md §1"
    );
}

#[test]
fn open_defect_a_free_variable_and_a_constant_share_a_solver_symbol() {
    let env = Environment::with_prelude();
    let mut bridge = SmtBridge::new(&env);
    let fvar = Expr::fvar(FVarId::new(7));
    let constant = Expr::const_(Name::from_string("fvar_7"), vec![]);
    let fvar_term = bridge.translate_term(&fvar).expect("fvar translates");
    let const_term = bridge
        .translate_term(&constant)
        .expect("constant translates");
    assert_eq!(
        fvar_term, const_term,
        "the collision is FIXED — update docs/issues/2026-09-28-smt-bridge-translation-defects.md §1"
    );
}
