// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel terms of the `eqsat_rules` gate: names, the rule literals as
//! trust-cg's generator will build them (constructors and raw `Nat` literals, no
//! binder and no universe level), the two statements, and the entry's verdict
//! on a closed term.

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::{ReferenceKernel, ReferenceRefusal};

pub(super) fn n(s: &str) -> Name {
    Name::from_string(s)
}

pub(super) fn c(name: &str) -> Expr {
    Expr::const_(n(name), vec![])
}

pub(super) fn app(head: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(head), args)
}

pub(super) fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

pub(super) fn boolean(b: bool) -> Expr {
    c(if b { "Bool.true" } else { "Bool.false" })
}

pub(super) fn sorts(vars: &[(&str, bool)]) -> Expr {
    vars.iter()
        .rev()
        .fold(c("EqsatRule.Sorts.nil"), |rest, (sort, constant)| {
            app(
                "EqsatRule.Sorts.cons",
                [
                    c(&format!("EqsatRule.Srt.{sort}")),
                    boolean(*constant),
                    rest,
                ],
            )
        })
}

pub(super) fn conds(items: Vec<Expr>) -> Expr {
    items
        .into_iter()
        .rev()
        .fold(c("EqsatRule.Conds.nil"), |rest, cond| {
            app("EqsatRule.Conds.cons", [cond, rest])
        })
}

pub(super) fn var(i: u64) -> Expr {
    app("EqsatRule.Pat.var", [nat(i)])
}

pub(super) fn cvar(i: u64) -> Expr {
    app("EqsatRule.Pat.cvar", [nat(i)])
}

pub(super) fn lit(neg: bool, mag: u64) -> Expr {
    app("EqsatRule.Pat.lit", [boolean(neg), nat(mag)])
}

pub(super) fn bin(op: &str, a: Expr, b: Expr) -> Expr {
    app("EqsatRule.Pat.bin", [c(&format!("SemR.BinOp.{op}")), a, b])
}

pub(super) fn un(op: &str, a: Expr) -> Expr {
    app("EqsatRule.Pat.un", [c(&format!("SemR.UnOp.{op}")), a])
}

pub(super) fn rule(dir: &str, vars: Expr, lhs: Expr, rhs: Expr, conds: Expr) -> Expr {
    app(
        "EqsatRule.Rule.mk",
        [c(&format!("EqsatRule.Dir.{dir}")), vars, lhs, rhs, conds],
    )
}

pub(super) fn int_ty(t: &str) -> Expr {
    app("EqsatRule.STy.int", [c(&format!("SemR.IntTy.{t}"))])
}

pub(super) fn sound(rule: Expr, ty: Expr) -> Expr {
    app("EqsatRule.Sound", [rule, ty])
}

pub(super) fn satisfiable(rule: Expr, ty: Expr) -> Expr {
    app("EqsatRule.Satisfiable", [rule, ty])
}

pub(super) fn not(p: Expr) -> Expr {
    app("Not", [p])
}

/// `EqsatInt.<lemma> SemR.IntTy.<t>`: an all-width lemma at one type.
pub(super) fn at(lemma: &str, t: &str) -> Expr {
    app(lemma, [c(&format!("SemR.IntTy.{t}"))])
}

pub(super) fn add_zero_literal(zero: u64) -> Expr {
    rule(
        "equiv",
        sorts(&[("t", false)]),
        bin("add", var(0), lit(false, zero)),
        var(0),
        conds(vec![]),
    )
}

pub(super) fn rotl_full_literal(with_condition: bool) -> Expr {
    rule(
        "equiv",
        sorts(&[("t", true), ("t", false)]),
        bin("rotl", var(1), cvar(0)),
        var(1),
        conds(if with_condition {
            vec![app("EqsatRule.Cond.zeroModWidth", [nat(0)])]
        } else {
            vec![]
        }),
    )
}

/// `band_false`, registered `refines`, under the direction given.
pub(super) fn band_false_literal(dir: &str) -> Expr {
    rule(
        dir,
        sorts(&[("bool", false)]),
        bin("bAnd", var(0), c("EqsatRule.Pat.ff")),
        c("EqsatRule.Pat.ff"),
        conds(vec![]),
    )
}

/// `mul_mul_const` as the checker's parser reads the rule written with term
/// variables and no `eval`: every `const` flag false, `Pat.var` throughout.
pub(super) fn mul_assoc_terms_literal() -> Expr {
    rule(
        "equiv",
        sorts(&[("t", false), ("t", false), ("t", false)]),
        bin("mul", bin("mul", var(2), var(0)), var(1)),
        bin("mul", var(2), bin("mul", var(0), var(1))),
        conds(vec![]),
    )
}

/// `(mul ?x (const INT)) = (neg ?x)`: `mul_neg_one` with `-1`, and
/// `mul_255_neg_i8` (the wrong-rule set's `wrong_width`) with `255`.
pub(super) fn mul_const_neg_literal(neg: bool, mag: u64) -> Expr {
    rule(
        "equiv",
        sorts(&[("t", false)]),
        bin("mul", var(0), lit(neg, mag)),
        un("neg", var(0)),
        conds(vec![]),
    )
}

pub(super) fn udiv_self_literal(dir: &str) -> Expr {
    rule(
        dir,
        sorts(&[("t", false)]),
        bin("udiv", var(0), var(0)),
        lit(false, 1),
        conds(vec![]),
    )
}

pub(super) fn accepted(k: &ReferenceKernel, ty: &Expr, val: &Expr, what: &str) {
    k.check_closed_term(ty, val)
        .unwrap_or_else(|e| panic!("{what} must be accepted: {e:?}"));
}

pub(super) fn refused(k: &ReferenceKernel, ty: &Expr, val: &Expr, what: &str) {
    let e = k
        .check_closed_term(ty, val)
        .expect_err(&format!("{what} must be refused"));
    assert!(
        matches!(e, ReferenceRefusal::Kernel(_)),
        "{what}: got {e:?}"
    );
}
