// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The operator controls of the `eqsat_decide` gate: one closed outcome of
//! `Pat.evalR` per operator, accepted by `Eq.refl` on Clean's reference entry
//! beside a forged outcome the entry refuses.
//!
//! `evalR_agrees` proves the evaluator against SemR for every operator, and a
//! wrong operator arm has no such proof. What that proof does not show is that
//! Clean's kernel evaluates each operator on closed residues to the value
//! Lean's does. Each row here is that, for one operator: the outcome is the
//! one the pinned Lean accepts by `rfl`, and the forged outcome is what a
//! neighbouring operator, the other signedness, the unreduced result or a
//! lost refusal would give.

use clean_kernel::expr::Expr;
use clean_kernel::ReferenceKernel;

use super::procedure::refused_for_the_claim;
use super::terms::{accepted, app, bin, boolean, c, lit, nat, un, var};
use super::{assignment, eq, refl, res};

/// The rows of [`operator_controls`].
pub(super) const CASES: usize = 39;

/// An outcome of the residue evaluator.
#[derive(Clone, Copy)]
enum Out {
    Res(u64),
    Bit(bool),
    Ub,
    Bad,
}

impl Out {
    fn term(self) -> Expr {
        match self {
            Out::Res(r) => app("EqsatDecide.RR.ok", [res(r)]),
            Out::Bit(v) => app("EqsatDecide.RR.ok", [bit(v)]),
            Out::Ub => c("EqsatDecide.RR.ub"),
            Out::Bad => c("EqsatDecide.RR.bad"),
        }
    }
}

fn bit(v: bool) -> Expr {
    app("EqsatDecide.RV.bit", [boolean(v)])
}

fn cmp(op: &str, a: Expr, b: Expr) -> Expr {
    app("EqsatRule.Pat.cmp", [c(&format!("SemR.ICmpOp.{op}")), a, b])
}

/// One row: the pattern evaluated at an integer type (`int`) of `width` bits
/// on `env`, the outcome, and the forged outcome.
struct Case {
    what: &'static str,
    int: bool,
    width: u32,
    env: Vec<Expr>,
    pat: Expr,
    is: Out,
    forged: Out,
}

/// A binary operator on two residues at eight bits.
fn bin8(what: &'static str, op: &str, a: u64, b: u64, is: Out, forged: Out) -> Case {
    Case {
        what,
        int: true,
        width: 8,
        env: vec![res(a), res(b)],
        pat: bin(op, var(0), var(1)),
        is,
        forged,
    }
}

/// A unary operator on a residue at eight bits.
fn un8(what: &'static str, op: &str, a: u64, is: u64, forged: u64) -> Case {
    Case {
        what,
        int: true,
        width: 8,
        env: vec![res(a)],
        pat: un(op, var(0)),
        is: Out::Res(is),
        forged: Out::Res(forged),
    }
}

/// A comparison of two residues at eight bits.
fn cmp8(what: &'static str, op: &str, a: u64, b: u64, is: bool) -> Case {
    Case {
        what,
        int: true,
        width: 8,
        env: vec![res(a), res(b)],
        pat: cmp(op, var(0), var(1)),
        is: Out::Bit(is),
        forged: Out::Bit(!is),
    }
}

fn cases() -> Vec<Case> {
    use Out::{Bad, Bit, Res, Ub};
    let sel = |cnd: Expr, a: Expr, b: Expr| app("EqsatRule.Pat.sel", [cnd, a, b]);
    // An assignment, a pattern and its outcome where the row is of no common
    // shape.
    let other = |what, int, width, env, pat, is, forged| Case {
        what,
        int,
        width,
        env,
        pat,
        is,
        forged,
    };
    vec![
        // ── Binary operators on residues: the forged outcome is the
        //    unreduced result or a neighbouring operator's. ──
        bin8("mul 200 3", "mul", 200, 3, Res(88), Res(600)),
        bin8("sub 3 5", "sub", 3, 5, Res(254), Res(2)),
        bin8("or 0xf0 0x0f", "or", 0xf0, 0x0f, Res(0xff), Res(0)),
        bin8("xor 0xff 0x0f", "xor", 0xff, 0x0f, Res(0xf0), Res(0xff)),
        bin8("shl 0x81 1", "shl", 0x81, 1, Res(2), Res(0x102)),
        bin8("lshr 0x81 1", "lshr", 0x81, 1, Res(0x40), Res(0xc0)),
        bin8("ashr 0x81 1", "ashr", 0x81, 1, Res(0xc0), Res(0x40)),
        bin8("sdiv -8 2", "sdiv", 248, 2, Res(252), Res(124)),
        bin8("urem 200 7", "urem", 200, 7, Res(4), Res(28)),
        bin8("srem -8 3", "srem", 248, 3, Res(254), Res(2)),
        bin8("rotl 0x81 1", "rotl", 0x81, 1, Res(3), Res(0xc0)),
        bin8("rotr 0x81 1", "rotr", 0x81, 1, Res(0xc0), Res(3)),
        // ── Undefined behaviour is `ub`, never a value. ──
        bin8("shl 1 8, the width", "shl", 1, 8, Ub, Res(0)),
        bin8("sdiv -128 -1", "sdiv", 128, 255, Ub, Res(128)),
        // ── Unary operators. ──
        un8("neg 1", "neg", 1, 255, 1),
        un8("not 0x0f", "not", 0x0f, 0xf0, 0x0f),
        un8("ctpop 0xf1", "ctpop", 0xf1, 5, 6),
        un8("ctlz 0x10", "ctlz", 0x10, 3, 4),
        un8("cttz 0x10", "cttz", 0x10, 4, 3),
        un8("bitreverse 1", "bitreverse", 1, 0x80, 1),
        un8("bswap 0x12 at eight bits", "bswap", 0x12, 0x12, 0x21),
        other(
            "bswap 0x1234 at sixteen bits",
            true,
            16,
            vec![res(0x1234)],
            un("bswap", var(0)),
            Res(0x3412),
            Res(0x1234),
        ),
        // ── Comparisons with distinct operands: signed against unsigned,
        //    and the operand order. ──
        cmp8("icmp.slt 0x80 1", "slt", 0x80, 1, true),
        cmp8("icmp.ult 0x80 1", "ult", 0x80, 1, false),
        cmp8("icmp.sge 0x80 1", "sge", 0x80, 1, false),
        cmp8("icmp.ule 1 0x80", "ule", 1, 0x80, true),
        cmp8("icmp.ne 1 0x80", "ne", 1, 0x80, true),
        // ── Literals are read modulo the type. ──
        other(
            "(const -1) at eight bits",
            true,
            8,
            vec![],
            lit(true, 1),
            Res(255),
            Res(1),
        ),
        other(
            "(const 300) at eight bits",
            true,
            8,
            vec![],
            lit(false, 300),
            Res(44),
            Res(300),
        ),
        // ── Sorts: a residue beside a Boolean is refused; Booleans take
        //    `band bor bxor` at an integer type and `and or xor` at `bool`. ──
        other(
            "add of a residue and a Boolean",
            true,
            8,
            vec![res(1), bit(true)],
            bin("add", var(0), var(1)),
            Bad,
            Res(2),
        ),
        other(
            "bxor true false at an integer type",
            true,
            8,
            vec![bit(true), bit(false)],
            bin("bXor", var(0), var(1)),
            Bit(true),
            Bit(false),
        ),
        other(
            "xor true true at bool",
            false,
            8,
            vec![bit(true), bit(true)],
            bin("xor", var(0), var(1)),
            Bit(false),
            Bit(true),
        ),
        other(
            "icmp.ult false true at bool",
            false,
            8,
            vec![bit(true), bit(false)],
            cmp("ult", var(1), var(0)),
            Bit(true),
            Bit(false),
        ),
        // ── `select` takes the second arm on `false`, and the first
        //    operand's undefined behaviour is the outcome whatever follows. ──
        other(
            "select false 7 9",
            true,
            8,
            vec![bit(false), res(7), res(9)],
            sel(var(0), var(1), var(2)),
            Res(9),
            Res(7),
        ),
        other(
            "add of (udiv 5 0) and an unbound variable",
            true,
            8,
            vec![res(0), res(5)],
            bin("add", bin("udiv", var(1), var(0)), var(7)),
            Ub,
            Bad,
        ),
        // ── A residue where the instance type is `bool`: `bad` under every
        //    operator form (`EqsatDecideControls.res_at_bool_*`). ──
        other(
            "add of two residues at bool",
            false,
            8,
            vec![res(1), res(2)],
            bin("add", var(0), var(1)),
            Bad,
            Res(0),
        ),
        other(
            "neg of a residue at bool",
            false,
            8,
            vec![res(1)],
            un("neg", var(0)),
            Bad,
            Res(255),
        ),
        other(
            "icmp.eq of two residues at bool",
            false,
            8,
            vec![res(1), res(1)],
            cmp("eq", var(0), var(1)),
            Bad,
            Bit(true),
        ),
        other(
            "select of two residues at bool",
            false,
            8,
            vec![bit(true), res(1), res(2)],
            sel(var(0), var(1), var(2)),
            Bad,
            Res(1),
        ),
    ]
}

/// Have the entry accept each row's outcome by `Eq.refl` and refuse the forged
/// one, offered with its own `Eq.refl`. Returns the number of rows.
pub(super) fn operator_controls(k: &ReferenceKernel) -> usize {
    let cases = cases();
    for case in &cases {
        let value = || {
            app(
                "EqsatRule.Pat.evalR",
                [
                    boolean(case.int),
                    nat(u64::from(case.width)),
                    nat(1u64 << case.width),
                    assignment(case.env.clone()),
                    case.pat.clone(),
                ],
            )
        };
        let claim = |outcome: Out| eq("EqsatDecide.RR", value(), outcome.term());
        let by_refl = |outcome: Out| refl("EqsatDecide.RR", outcome.term());
        accepted(k, &claim(case.is), &by_refl(case.is), case.what);
        refused_for_the_claim(
            k,
            &claim(case.forged),
            &by_refl(case.forged),
            &format!("{}, forged", case.what),
        );
        // The accepted outcome's proof is not a proof of the forged one.
        refused_for_the_claim(
            k,
            &claim(case.forged),
            &by_refl(case.is),
            &format!("{}, forged with the true outcome's proof", case.what),
        );
    }
    assert_eq!(cases.len(), CASES, "the rows of the operator controls");
    cases.len()
}
