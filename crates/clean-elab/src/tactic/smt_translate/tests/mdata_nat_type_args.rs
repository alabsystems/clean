// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metadata-wrapped Nat type-argument regressions for SMT-LIB translation (#2808).

use super::*;
use clean_kernel::MDataValue;

fn make_mdata_nat_type() -> Expr {
    Expr::mdata(
        vec![(Name::from_string("pp.universes"), MDataValue::Bool(true))],
        Expr::const_(Name::from_string("Nat"), vec![]),
    )
}

#[test]
fn test_hsub_mdata_nat_type_arg_uses_monus() {
    let mut t = SmtLibTranslator::new();
    let expr = make_hsub(make_mdata_nat_type(), Expr::nat_lit(3), Expr::nat_lit(5));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(ite (>= 3 5) (- 3 5) 0)");
}

#[test]
fn test_hdiv_mdata_nat_type_arg_uses_total_div() {
    let mut t = SmtLibTranslator::new();
    let expr = make_hdiv(make_mdata_nat_type(), Expr::nat_lit(5), Expr::nat_lit(0));
    assert_eq!(
        t.translate_expr(&expr).unwrap(),
        "(ite (> 0 0) (div 5 0) 0)"
    );
}

#[test]
fn test_hmod_mdata_nat_type_arg_uses_total_mod() {
    let mut t = SmtLibTranslator::new();
    let expr = make_hmod(make_mdata_nat_type(), Expr::nat_lit(5), Expr::nat_lit(0));
    assert_eq!(
        t.translate_expr(&expr).unwrap(),
        "(ite (> 0 0) (mod 5 0) 5)"
    );
}
