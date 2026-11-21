// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The controls of the three procedures of PKG-U6b on Clean's reference
//! entry, under the budget, on a kernel that replayed the family:
//!
//! * `exhaust8p` (`EqsatPacked`): rules with up to two variables of the
//!   instance type at `i8` and `u8`, over `add sub and or xor neg not`;
//! * `bitwiseAll` (`EqsatBitwise`): rules over `and or xor not`, `(const 0)`
//!   and `(const -1)`, at each of the twelve integer types from one truth
//!   table;
//! * `ringAll` (`EqsatRing`): rules over `add sub mul neg not` and integer
//!   literals, at each of the twelve integer types from one polynomial normal
//!   form.
//!
//! As in `procedure.rs`, a rule literal is built here as trust-cg's generator
//! will build it, the kernel is asked to accept it as the rule the procedure's
//! controls module defines under the same name, and the term offered for a
//! rule is the term a discharge record carries:
//! `EqsatDecide.<procedure>_sound <literal> <type> EqsatDecide.rflTrue`. For
//! each procedure the gate has the entry accept that term for a list of rule
//! and type pairs (the tracker's subject at every type the procedure covers
//! among them) and prints the smallest heartbeat limit each passes under; and
//! it has the entry refuse it, for the claim (`TypeMismatch`), for false
//! rules, for rules outside the procedure's fragment, at a type the procedure
//! does not cover, and where the term of one rule or type is offered for
//! another. `(and ?x (const 255)) = ?x`, which is true at eight bits only, is
//! refused at `u16` under each of the three.

use std::time::Instant;

use clean_kernel::expr::Expr;
use clean_kernel::ReferenceKernel;

use super::procedure::{refused_for_the_claim, smallest_passing_limit};
use super::terms::{
    accepted, app, bin, boolean, c, conds, cvar, int_ty, lit, nat, not, rule, satisfiable, sorts,
    sound, un, var,
};
use super::{eq, refl, BUDGET};

/// SemR's twelve integer types, in the order of `SemR.IntTy`.
pub(super) const INT_TYPES: [&str; 12] = [
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
];

/// The integer types `exhaust8p` does not cover.
const WIDER: [&str; 10] = [
    "i16", "i32", "i64", "i128", "isize", "u16", "u32", "u64", "u128", "usize",
];

/// An instance type by name: an integer type of SemR, or `bool`.
fn sty(name: &str) -> Expr {
    if name == "bool" {
        c("EqsatRule.STy.bool")
    } else {
        int_ty(name)
    }
}

fn none() -> Expr {
    conds(vec![])
}

/// `n` variables of the instance type, none a constant variable.
fn ts(n: usize) -> Expr {
    sorts(&vec![("t", false); n])
}

fn v(i: u64) -> Expr {
    var(i)
}

/// `(const n)` for a natural `n`.
fn k(n: u64) -> Expr {
    lit(false, n)
}

/// `(const -1)`.
fn minus_one() -> Expr {
    lit(true, 1)
}

fn equiv(vars: Expr, lhs: Expr, rhs: Expr) -> Expr {
    rule("equiv", vars, lhs, rhs, none())
}

fn cmp_eq(a: Expr, b: Expr) -> Expr {
    app("EqsatRule.Pat.cmp", [c("SemR.ICmpOp.eq"), a, b])
}

fn sel(condition: Expr, a: Expr, b: Expr) -> Expr {
    app("EqsatRule.Pat.sel", [condition, a, b])
}

fn is(value: Expr, answer: bool) -> Expr {
    eq("Bool", value, boolean(answer))
}

fn by_refl(answer: bool) -> Expr {
    refl("Bool", boolean(answer))
}

// ── Rules more than one procedure is asked about ──

/// `(and ?x (or ?x ?y)) = ?x`: the tracker's subject for `exhaust8p`.
fn absorb() -> Expr {
    equiv(ts(2), bin("and", v(0), bin("or", v(0), v(1))), v(0))
}

/// `(and ?x (not ?x)) = (const 0)`: the tracker's subject for `bitwiseAll`.
fn and_not() -> Expr {
    equiv(ts(1), bin("and", v(0), un("not", v(0))), k(0))
}

/// `(sub (add ?x ?y) ?y) = ?x`: the tracker's subject for `ringAll`.
fn sub_add() -> Expr {
    equiv(ts(2), bin("sub", bin("add", v(0), v(1)), v(1)), v(0))
}

/// `(and ?x (const 255)) = ?x`: true at eight bits only.
fn and255() -> Expr {
    equiv(ts(1), bin("and", v(0), k(255)), v(0))
}

/// `(add ?x (neg ?y)) = (sub ?y ?x)`: trust-cg's `wrong_operand_order`.
fn wrong_operand_order() -> Expr {
    equiv(
        ts(2),
        bin("add", v(0), un("neg", v(1))),
        bin("sub", v(1), v(0)),
    )
}

/// `(mul ?x ?y) = (mul ?y ?x)`.
fn mul_comm() -> Expr {
    equiv(ts(2), bin("mul", v(0), v(1)), bin("mul", v(1), v(0)))
}

/// One procedure: its name in `EqsatDecide`, and the module of its controls.
#[derive(Clone, Copy)]
struct Procedure {
    name: &'static str,
    controls: &'static str,
}

const PACKED: Procedure = Procedure {
    name: "exhaust8p",
    controls: "EqsatPackedControls",
};
const BITWISE: Procedure = Procedure {
    name: "bitwiseAll",
    controls: "EqsatBitwiseControls",
};
const RING: Procedure = Procedure {
    name: "ringAll",
    controls: "EqsatRingControls",
};

impl Procedure {
    /// `EqsatDecide.<procedure> rule ty`.
    fn answer(self, rule: Expr, ty: Expr) -> Expr {
        app(&format!("EqsatDecide.{}", self.name), [rule, ty])
    }

    /// The term a discharge record carries for `Sound rule ty`.
    fn record(self, rule: Expr, ty: Expr) -> Expr {
        self.term_by("sound", rule, ty)
    }

    /// `EqsatDecide.<procedure>_<what> rule ty rflTrue`.
    fn term_by(self, what: &str, rule: Expr, ty: Expr) -> Expr {
        app(
            &format!("EqsatDecide.{}_{what}", self.name),
            [rule, ty, c("EqsatDecide.rflTrue")],
        )
    }

    /// A constant of the procedure's controls module.
    fn control(self, name: &str) -> Expr {
        c(&format!("{}.{name}", self.controls))
    }
}

/// `EqsatDecide.Defined rule ty`.
fn defined(rule: Expr, ty: Expr) -> Expr {
    app("EqsatDecide.Defined", [rule, ty])
}

/// What the controls of one procedure counted.
pub(super) struct Counted {
    /// The procedure's name in `EqsatDecide`.
    pub(super) name: &'static str,
    /// Rules proved by the record term, each at one type.
    pub(super) proved: usize,
    /// The dearest of them, in heartbeats.
    pub(super) dearest: u32,
    /// The sum of their costs, in heartbeats.
    pub(super) total: u64,
    /// Terms the entry refused for the claim.
    pub(super) refused: usize,
}

/// The controls of one procedure on one kernel, and their counts.
struct Controls<'k> {
    k: &'k ReferenceKernel,
    procedure: Procedure,
    counted: Counted,
}

impl<'k> Controls<'k> {
    fn new(k: &'k ReferenceKernel, procedure: Procedure) -> Self {
        Controls {
            k,
            procedure,
            counted: Counted {
                name: procedure.name,
                proved: 0,
                dearest: 0,
                total: 0,
                refused: 0,
            },
        }
    }

    /// The literal built here is the rule the controls module defines under
    /// `name`.
    fn literal(&self, name: &str, literal: &Expr) {
        accepted(
            self.k,
            &eq(
                "EqsatRule.Rule",
                self.procedure.control(name),
                literal.clone(),
            ),
            &refl("EqsatRule.Rule", literal.clone()),
            &format!(
                "the literal built here is {}.{name}",
                self.procedure.controls
            ),
        );
    }

    /// The entry accepts `proof : goal`.
    fn accept(&self, goal: &Expr, proof: &Expr, what: &str) {
        accepted(self.k, goal, proof, what);
    }

    /// The record term proves `Sound literal ty` under the budget; `theorem`
    /// is the controls module's theorem of the same statement. Prints the
    /// time of the check and the smallest heartbeat limit it passes under.
    fn prove(&mut self, theorem: &str, text: &str, literal: &Expr, ty: &str) {
        let procedure = self.procedure;
        self.accept(
            &sound(literal.clone(), sty(ty)),
            &procedure.control(theorem),
            &format!(
                "{}.{theorem} for the literal built here",
                procedure.controls
            ),
        );
        self.prove_as(theorem, text, literal, ty);
    }

    /// [`Controls::prove`] for a rule the controls module has no theorem of;
    /// `label` names the check in the gate's output.
    fn prove_as(&mut self, label: &str, text: &str, literal: &Expr, ty: &str) {
        let procedure = self.procedure;
        let goal = sound(literal.clone(), sty(ty));
        let term = procedure.record(literal.clone(), sty(ty));
        let started = Instant::now();
        self.accept(&goal, &term, &format!("{label} by the record term"));
        let micros = started.elapsed().as_micros();
        let cost = smallest_passing_limit(self.k, &goal, &term, label);
        self.counted.proved += 1;
        self.counted.dearest = self.counted.dearest.max(cost);
        self.counted.total += u64::from(cost);
        eprintln!(
            "eqsat_decide: {}: {label}: `{text}` at {ty}: accepted under {BUDGET} in {micros} \
             us; smallest passing limit {cost} heartbeats",
            procedure.name
        );
    }

    /// A term the entry refuses for the claim.
    fn forged(&mut self, goal: &Expr, proof: &Expr, what: &str) {
        refused_for_the_claim(self.k, goal, proof, what);
        self.counted.refused += 1;
    }

    /// The procedure answers `false` on `literal` at `ty` (accepted by
    /// `Eq.refl false`), `true` is refused, and so is the record term for
    /// `Sound literal ty`: two refusals.
    fn not_admitted(&mut self, literal: &Expr, ty: &str, what: &str) {
        let procedure = self.procedure;
        let answer = procedure.answer(literal.clone(), sty(ty));
        self.accept(
            &is(answer.clone(), false),
            &by_refl(false),
            &format!("{} = false for {what}", procedure.name),
        );
        self.forged(
            &is(answer, true),
            &by_refl(true),
            &format!("{} = true for {what}", procedure.name),
        );
        self.forged(
            &sound(literal.clone(), sty(ty)),
            &procedure.record(literal.clone(), sty(ty)),
            &format!("the {} record term for {what}", procedure.name),
        );
    }

    /// The same `true` gives `Defined` and `Satisfiable` for a rule the
    /// procedure proves, and neither for one it does not (two refusals).
    /// `Satisfiable` of a rule with no side condition holds whatever the rule
    /// is; its term is refused all the same, because the procedure did not
    /// answer `true`.
    fn says_something(&mut self, proved: &Expr, refused: &Expr, ty: &str) {
        let procedure = self.procedure;
        for (literal, admitted) in [(proved, true), (refused, false)] {
            let pairs = [
                (
                    defined(literal.clone(), sty(ty)),
                    procedure.term_by("defined", literal.clone(), sty(ty)),
                    "Defined",
                ),
                (
                    satisfiable(literal.clone(), sty(ty)),
                    procedure.term_by("satisfiable", literal.clone(), sty(ty)),
                    "Satisfiable",
                ),
            ];
            for (goal, proof, what) in pairs {
                let what = format!("{what} by {} at {ty}", procedure.name);
                if admitted {
                    self.accept(&goal, &proof, &what);
                } else {
                    self.forged(&goal, &proof, &what);
                }
            }
        }
    }
}

// ── exhaust8p ──

/// `(and (or Z (neg Z)) (const 128)) = (const 128)`: true exactly where `Z`
/// is not 0.
fn non_zero(z: Expr) -> Expr {
    equiv(
        ts(2),
        bin("and", bin("or", z.clone(), un("neg", z)), k(128)),
        k(128),
    )
}

/// `?v + 1`: 0 at 255 only.
fn succ_p(i: u64) -> Expr {
    bin("add", v(i), k(1))
}

#[allow(clippy::too_many_lines)]
fn packed_controls(kernel: &ReferenceKernel) -> Counted {
    let mut t = Controls::new(kernel, PACKED);

    let xor_xor = equiv(ts(2), bin("xor", bin("xor", v(0), v(1)), v(1)), v(0));
    let add_carry = equiv(
        ts(2),
        bin("add", bin("and", v(0), v(1)), bin("or", v(0), v(1))),
        bin("add", v(0), v(1)),
    );
    let de_morgan = equiv(
        ts(2),
        un("not", bin("and", un("not", v(0)), un("not", v(1)))),
        bin("or", v(0), v(1)),
    );
    let add_comm = rule(
        "refines",
        ts(2),
        bin("add", v(0), v(1)),
        bin("add", v(1), v(0)),
        none(),
    );
    let sub_all_ones = equiv(ts(1), bin("sub", minus_one(), v(0)), un("not", v(0)));
    let const_fold = equiv(ts(0), bin("add", k(1), k(255)), k(0));
    let sub_add_wrong = equiv(ts(2), bin("sub", bin("add", v(0), v(1)), v(0)), v(0));
    let add_is_or = equiv(ts(2), bin("add", v(0), v(1)), bin("or", v(0), v(1)));
    let corner_top_top = non_zero(bin("or", succ_p(0), succ_p(1)));
    let corner_zero_zero = non_zero(bin("or", v(0), v(1)));
    let corner_top_zero = non_zero(bin("or", succ_p(0), v(1)));
    let corner_zero_top = non_zero(bin("or", v(0), succ_p(1)));
    let rot_round = equiv(ts(2), bin("rotl", bin("rotr", v(0), v(1)), v(1)), v(0));
    let select_eq = equiv(ts(2), sel(cmp_eq(v(0), v(1)), v(0), v(1)), v(1));
    let bool_beside = equiv(sorts(&[("t", false), ("bool", false)]), v(0), v(0));
    let cond_all_ones = rule(
        "equiv",
        sorts(&[("t", true), ("t", false)]),
        bin("and", v(1), cvar(0)),
        v(1),
        conds(vec![app(
            "EqsatRule.Cond.eq",
            [nat(0), boolean(true), nat(1)],
        )]),
    );
    let three_vars = equiv(ts(3), v(0), v(0));
    let unbound_side = equiv(ts(2), v(2), v(2));
    let tt_side = equiv(ts(2), v(0), c("EqsatRule.Pat.tt"));

    for (name, literal) in [
        ("absorb", absorb()),
        ("subAdd", sub_add()),
        ("xorXor", xor_xor.clone()),
        ("addCarry", add_carry.clone()),
        ("deMorgan", de_morgan.clone()),
        ("addComm", add_comm.clone()),
        ("subAllOnes", sub_all_ones.clone()),
        ("constFold", const_fold.clone()),
        ("subAddWrong", sub_add_wrong.clone()),
        ("wrongOperandOrder", wrong_operand_order()),
        ("addIsOr", add_is_or.clone()),
        ("cornerTopTop", corner_top_top.clone()),
        ("cornerZeroZero", corner_zero_zero.clone()),
        ("cornerTopZero", corner_top_zero.clone()),
        ("cornerZeroTop", corner_zero_top.clone()),
        ("mulComm", mul_comm()),
        ("rotRound", rot_round.clone()),
        ("selectEq", select_eq.clone()),
        ("boolBeside", bool_beside.clone()),
        ("condAllOnes", cond_all_ones.clone()),
        ("threeVars", three_vars.clone()),
        ("unboundSide", unbound_side.clone()),
        ("ttSide", tt_side.clone()),
    ] {
        t.literal(name, &literal);
    }

    // ── Rules the record term proves, each under the budget. The first two
    //    are the tracker's subject. ──
    for ty in ["i8", "u8"] {
        t.prove(
            &format!("absorb_{ty}"),
            "(and ?x (or ?x ?y)) = ?x",
            &absorb(),
            ty,
        );
    }
    for ty in ["i8", "u8"] {
        t.prove(
            &format!("sub_add_{ty}"),
            "(sub (add ?x ?y) ?y) = ?x",
            &sub_add(),
            ty,
        );
        t.prove(
            &format!("xor_xor_{ty}"),
            "(xor (xor ?x ?y) ?y) = ?x",
            &xor_xor,
            ty,
        );
    }
    t.prove(
        "add_carry_u8",
        "(add (and ?x ?y) (or ?x ?y)) = (add ?x ?y)",
        &add_carry,
        "u8",
    );
    t.prove(
        "de_morgan_u8",
        "(not (and (not ?x) (not ?y))) = (or ?x ?y)",
        &de_morgan,
        "u8",
    );
    t.prove(
        "add_comm_refines_u8",
        "(add ?x ?y) refines to (add ?y ?x)",
        &add_comm,
        "u8",
    );
    t.prove(
        "sub_all_ones_i8",
        "(sub (const -1) ?x) = (not ?x)",
        &sub_all_ones,
        "i8",
    );
    t.prove(
        "const_fold_u8",
        "(add (const 1) (const 255)) = (const 0)",
        &const_fold,
        "u8",
    );
    t.says_something(&absorb(), &sub_add_wrong, "u8");

    // ── False rules: some assignment fails. Each corner rule fails on one
    //    assignment of the 65,536. ──
    for ty in ["u8", "i8"] {
        t.not_admitted(
            &sub_add_wrong,
            ty,
            &format!("(sub (add ?x ?y) ?x) = ?x at {ty}"),
        );
    }
    for (literal, what) in [
        (wrong_operand_order(), "wrong_operand_order"),
        (add_is_or, "(add ?x ?y) = (or ?x ?y)"),
        (corner_top_top, "a rule false at ?x = ?y = 255 only"),
        (corner_zero_zero, "a rule false at ?x = ?y = 0 only"),
        (corner_top_zero, "a rule false at ?x = 255, ?y = 0 only"),
        (corner_zero_top, "a rule false at ?x = 0, ?y = 255 only"),
    ] {
        t.not_admitted(&literal, "u8", what);
    }

    // ── Outside the fragment: an operator, a comparison and a select, a
    //    Boolean variable, a side condition, a third variable, a side that
    //    is not a term, a Boolean literal. Two of them are `Sound`. ──
    for (literal, what) in [
        (mul_comm(), "(mul ?x ?y) = (mul ?y ?x)"),
        (rot_round, "(rotl (rotr ?x ?y) ?y) = ?x"),
        (select_eq, "(select (icmp.eq ?x ?y) ?x ?y) = ?y"),
        (bool_beside.clone(), "?x = ?x beside a Boolean variable"),
        (cond_all_ones, "a rule with a side condition"),
        (three_vars.clone(), "?x = ?x beside two more variables"),
        (unbound_side, "a side that is not a term"),
        (tt_side, "?x = true"),
    ] {
        t.not_admitted(&literal, "u8", what);
    }
    t.accept(
        &sound(bool_beside, sty("u8")),
        &PACKED.control("bool_beside_sound_u8"),
        "the hand proof of ?x = ?x beside a Boolean variable",
    );
    t.accept(
        &sound(three_vars, sty("u8")),
        &PACKED.control("three_vars_sound_u8"),
        "the hand proof of ?x = ?x beside two more variables",
    );

    // ── Another type: the procedure answers `false` at every type but `i8`
    //    and `u8`, and the `u8` term proves nothing there. ──
    for wide in WIDER {
        t.not_admitted(&absorb(), wide, &format!("absorb at {wide}"));
        t.forged(
            &sound(absorb(), sty(wide)),
            &PACKED.record(absorb(), sty("u8")),
            &format!("the u8 term of absorb offered at {wide}"),
        );
    }
    t.not_admitted(&absorb(), "bool", "absorb at bool");
    // `(and ?x (const 255)) = ?x` is in the fragment and true at eight bits;
    // at `u16` it is false, and not this procedure's.
    t.prove_as("and255_u8", "(and ?x (const 255)) = ?x", &and255(), "u8");
    t.not_admitted(&and255(), "u16", "(and ?x (const 255)) = ?x at u16");

    // ── Another rule: the term of a true rule offered for a false one. ──
    t.forged(
        &sound(sub_add_wrong, sty("u8")),
        &PACKED.record(sub_add(), sty("u8")),
        "the term of sub_add offered for (sub (add ?x ?y) ?x) = ?x",
    );
    t.counted
}

// ── bitwiseAll ──

#[allow(clippy::too_many_lines)]
fn bitwise_controls(kernel: &ReferenceKernel) -> Counted {
    let mut t = Controls::new(kernel, BITWISE);

    let or_absorb = equiv(ts(2), bin("or", v(0), bin("and", v(0), v(1))), v(0));
    let or_not = equiv(ts(1), bin("or", v(0), un("not", v(0))), minus_one());
    let de_morgan3 = rule(
        "refines",
        sorts(&[("t", false), ("t", false), ("t", true)]),
        un("not", bin("and", v(0), bin("and", v(1), cvar(2)))),
        bin(
            "or",
            un("not", v(0)),
            bin("or", un("not", v(1)), un("not", cvar(2))),
        ),
        none(),
    );
    // The `xor` of eight variables nested to the right in rank order, against
    // the same nested to the left in the reverse order: 256 rows.
    let eight_vars = equiv(
        ts(8),
        (0..7).rev().fold(v(7), |rest, i| bin("xor", v(i), rest)),
        (0..7).rev().fold(v(7), |rest, i| bin("xor", rest, v(i))),
    );
    let nine_vars = equiv(ts(9), v(0), v(0));
    let and_one = equiv(ts(1), bin("and", v(0), k(1)), v(0));
    let or_neg_zero = equiv(ts(1), bin("or", v(0), lit(true, 0)), v(0));
    let or_drop = equiv(ts(2), bin("or", v(0), v(1)), v(0));
    let xor_self_wrong = equiv(ts(1), bin("xor", v(0), v(0)), v(0));
    let and_is_or = equiv(ts(2), bin("and", v(0), v(1)), bin("or", v(0), v(1)));
    let zero_is_ones = equiv(ts(0), k(0), minus_one());
    let add_zero = equiv(ts(1), bin("add", v(0), k(0)), v(0));
    let neg_neg = equiv(ts(1), un("neg", un("neg", v(0))), v(0));
    let band_self = equiv(ts(1), bin("bAnd", v(0), v(0)), v(0));
    let sel_same = equiv(ts(1), sel(c("EqsatRule.Pat.tt"), v(0), v(0)), v(0));
    let cmp_side = equiv(ts(1), cmp_eq(v(0), v(0)), cmp_eq(v(0), v(0)));
    let unbound = equiv(ts(1), v(1), v(1));
    let bool_var = equiv(sorts(&[("t", false), ("bool", false)]), v(0), v(0));
    let with_cond = rule(
        "equiv",
        sorts(&[("t", true)]),
        v(0),
        v(0),
        conds(vec![app(
            "EqsatRule.Cond.ne",
            [nat(0), boolean(false), nat(0)],
        )]),
    );

    for (name, literal) in [
        ("andNot", and_not()),
        ("orAbsorb", or_absorb.clone()),
        ("orNot", or_not.clone()),
        ("deMorgan3", de_morgan3.clone()),
        ("eightVars", eight_vars.clone()),
        ("nineVars", nine_vars.clone()),
        ("and255", and255()),
        ("andOne", and_one.clone()),
        ("orNegZero", or_neg_zero.clone()),
        ("orDrop", or_drop.clone()),
        ("xorSelfWrong", xor_self_wrong.clone()),
        ("andIsOr", and_is_or.clone()),
        ("zeroIsOnes", zero_is_ones.clone()),
        ("addZero", add_zero.clone()),
        ("negNeg", neg_neg.clone()),
        ("bandSelf", band_self.clone()),
        ("selSame", sel_same.clone()),
        ("cmpSide", cmp_side.clone()),
        ("unbound", unbound.clone()),
        ("boolVar", bool_var.clone()),
        ("withCond", with_cond.clone()),
    ] {
        t.literal(name, &literal);
    }

    // ── Rules the record term proves, each under the budget. The first
    //    twelve are the tracker's subject, at every integer type. ──
    for ty in INT_TYPES {
        t.prove(
            &format!("and_not_{ty}"),
            "(and ?x (not ?x)) = (const 0)",
            &and_not(),
            ty,
        );
    }
    for ty in ["u8", "u64"] {
        t.prove(
            &format!("or_absorb_{ty}"),
            "(or ?x (and ?x ?y)) = ?x",
            &or_absorb,
            ty,
        );
    }
    t.prove(
        "or_not_u128",
        "(or ?x (not ?x)) = (const -1)",
        &or_not,
        "u128",
    );
    t.prove(
        "de_morgan3_i64",
        "(not (and ?x (and ?y ?z))) refines to (or (not ?x) (or (not ?y) (not ?z)))",
        &de_morgan3,
        "i64",
    );
    t.prove(
        "eight_vars_u64",
        "the xor of eight variables = the same in the reverse order (256 rows)",
        &eight_vars,
        "u64",
    );
    t.says_something(&and_not(), &or_drop, "u64");

    // ── `(and ?x (const 255)) = ?x`: true at eight bits only, and the
    //    literal is outside the fragment, so it is refused at every type. It
    //    is false at `u16`. ──
    for ty in ["u16", "u8", "i8", "u64"] {
        t.not_admitted(&and255(), ty, &format!("(and ?x (const 255)) = ?x at {ty}"));
    }
    t.accept(
        &not(sound(and255(), sty("u16"))),
        &BITWISE.control("and255_not_sound_u16"),
        "the proof that (and ?x (const 255)) = ?x is not Sound at u16",
    );

    // ── False rules: a row differs. ──
    t.not_admitted(&or_drop, "u8", "(or ?x ?y) = ?x");
    t.accept(
        &not(sound(or_drop.clone(), sty("u8"))),
        &BITWISE.control("or_drop_not_sound_u8"),
        "the proof that (or ?x ?y) = ?x is not Sound at u8",
    );
    t.not_admitted(&xor_self_wrong, "u8", "(xor ?x ?x) = ?x");
    t.not_admitted(&and_is_or, "u64", "(and ?x ?y) = (or ?x ?y)");
    t.not_admitted(&zero_is_ones, "u8", "(const 0) = (const -1)");

    // ── Outside the fragment: a literal that is neither 0 nor -1, an
    //    arithmetic operator, the Boolean operator, a select, a comparison,
    //    a side that is not a term, a Boolean variable, a side condition, a
    //    ninth variable. Four of them are `Sound`. ──
    for (literal, ty, what) in [
        (and_one, "u8", "(and ?x (const 1)) = ?x"),
        (or_neg_zero.clone(), "u8", "(or ?x (const -0)) = ?x"),
        (add_zero.clone(), "u8", "(add ?x (const 0)) = ?x"),
        (neg_neg, "u8", "(neg (neg ?x)) = ?x"),
        (band_self, "u8", "(band ?x ?x) = ?x"),
        (sel_same, "u8", "(select true ?x ?x) = ?x"),
        (cmp_side, "u8", "(icmp.eq ?x ?x) = (icmp.eq ?x ?x)"),
        (unbound, "u8", "a side that is not a term"),
        (bool_var, "u8", "?x = ?x beside a Boolean variable"),
        (with_cond.clone(), "u8", "a rule with a side condition"),
        (nine_vars, "u64", "?a = ?a beside eight more variables"),
        (sub_add(), "u64", "(sub (add ?x ?y) ?y) = ?x, ringAll's"),
        (mul_comm(), "u64", "(mul ?x ?y) = (mul ?y ?x)"),
    ] {
        t.not_admitted(&literal, ty, what);
    }
    for (literal, theorem, what) in [
        (
            or_neg_zero,
            "or_neg_zero_sound_u8",
            "(or ?x (const -0)) = ?x",
        ),
        (add_zero, "add_zero_sound_u8", "(add ?x (const 0)) = ?x"),
        (with_cond, "with_cond_sound_u8", "?x = ?x where (ne ?x 0)"),
    ] {
        t.accept(
            &sound(literal, sty("u8")),
            &BITWISE.control(theorem),
            &format!("the exhaust8 proof of {what}"),
        );
    }

    // ── Another type: `false` at `bool`; and a term names its type, so the
    //    term of one type is not a term of another, also where the rule
    //    holds at both. ──
    t.not_admitted(&and_not(), "bool", "and_not at bool");
    t.forged(
        &sound(and_not(), sty("bool")),
        &BITWISE.record(and_not(), sty("u64")),
        "the u64 term of and_not offered at bool",
    );
    t.forged(
        &sound(and_not(), sty("u16")),
        &BITWISE.record(and_not(), sty("u8")),
        "the u8 term of and_not offered at u16",
    );
    // ── Another rule: the term of a true rule offered for a false one. ──
    t.forged(
        &sound(or_drop, sty("u8")),
        &BITWISE.record(or_absorb, sty("u8")),
        "the term of or_absorb offered for (or ?x ?y) = ?x",
    );
    t.counted
}

// ── ringAll ──

#[allow(clippy::too_many_lines)]
fn ring_controls(kernel: &ReferenceKernel) -> Counted {
    let mut t = Controls::new(kernel, RING);

    let sub_add_refines = rule(
        "refines",
        ts(2),
        bin("sub", bin("add", v(0), v(1)), v(1)),
        v(0),
        none(),
    );
    let add_self = equiv(ts(1), bin("add", v(0), v(0)), bin("mul", v(0), k(2)));
    let neg_not = equiv(ts(1), un("neg", un("not", v(0))), bin("add", v(0), k(1)));
    let distrib = equiv(
        ts(3),
        bin("mul", v(0), bin("add", v(1), v(2))),
        bin("add", bin("mul", v(0), v(1)), bin("mul", v(0), v(2))),
    );
    let square = equiv(
        ts(2),
        bin("mul", bin("add", v(0), v(1)), bin("add", v(0), v(1))),
        bin(
            "add",
            bin(
                "add",
                bin("mul", v(0), v(0)),
                bin("mul", k(2), bin("mul", v(0), v(1))),
            ),
            bin("mul", v(1), v(1)),
        ),
    );
    let diff_squares = equiv(
        ts(2),
        bin("mul", bin("sub", v(0), v(1)), bin("add", v(0), v(1))),
        bin("sub", bin("mul", v(0), v(0)), bin("mul", v(1), v(1))),
    );
    let add_one = equiv(ts(1), bin("add", v(0), k(1)), v(0));
    let wrong_constant = equiv(ts(1), bin("mul", v(0), k(2)), v(0));
    let wrong_not = equiv(ts(1), un("neg", un("not", v(0))), bin("sub", v(0), k(1)));
    let mul256 = equiv(ts(1), bin("mul", v(0), k(256)), k(0));
    let and_self = equiv(ts(1), bin("and", v(0), v(0)), v(0));
    let udiv_one = equiv(ts(1), bin("udiv", v(0), k(1)), v(0));
    let select_same = equiv(
        sorts(&[("bool", false), ("t", false)]),
        sel(v(0), v(1), v(1)),
        v(1),
    );
    let cmp_self = equiv(ts(1), cmp_eq(v(0), v(0)), c("EqsatRule.Pat.tt"));
    let cond_zero = rule(
        "equiv",
        sorts(&[("t", true)]),
        bin("add", cvar(0), k(0)),
        cvar(0),
        conds(vec![app(
            "EqsatRule.Cond.eq",
            [nat(0), boolean(false), nat(0)],
        )]),
    );
    let unbound_side = equiv(ts(1), v(1), v(1));
    let bool_var = equiv(
        sorts(&[("bool", false)]),
        bin("add", v(0), v(0)),
        bin("mul", v(0), k(2)),
    );

    for (name, literal) in [
        ("subAdd", sub_add()),
        ("subAddRefines", sub_add_refines.clone()),
        ("addSelf", add_self.clone()),
        ("negNot", neg_not.clone()),
        ("distrib", distrib.clone()),
        ("square", square.clone()),
        ("diffSquares", diff_squares.clone()),
        ("mulComm", mul_comm()),
        ("addOne", add_one.clone()),
        ("wrongConstant", wrong_constant.clone()),
        ("wrongOperandOrder", wrong_operand_order()),
        ("wrongNot", wrong_not.clone()),
        ("mul256", mul256.clone()),
        ("and255", and255()),
        ("andSelf", and_self.clone()),
        ("udivOne", udiv_one.clone()),
        ("selectSame", select_same.clone()),
        ("cmpSelf", cmp_self.clone()),
        ("condZero", cond_zero.clone()),
        ("unboundSide", unbound_side.clone()),
        ("boolVar", bool_var.clone()),
    ] {
        t.literal(name, &literal);
    }

    // ── Rules the record term proves, each under the budget. The first
    //    twelve are the tracker's subject, at every integer type. ──
    for ty in INT_TYPES {
        t.prove(
            &format!("sub_add_{ty}"),
            "(sub (add ?x ?y) ?y) = ?x",
            &sub_add(),
            ty,
        );
    }
    t.prove(
        "sub_add_refines_u64",
        "(sub (add ?x ?y) ?y) refines to ?x",
        &sub_add_refines,
        "u64",
    );
    t.prove(
        "add_self_u8",
        "(add ?x ?x) = (mul ?x (const 2))",
        &add_self,
        "u8",
    );
    t.prove(
        "neg_not_isize",
        "(neg (not ?x)) = (add ?x (const 1))",
        &neg_not,
        "isize",
    );
    t.prove(
        "distrib_u16",
        "(mul ?x (add ?y ?z)) = (add (mul ?x ?y) (mul ?x ?z))",
        &distrib,
        "u16",
    );
    t.prove(
        "mul_comm_u8",
        "(mul ?x ?y) = (mul ?y ?x)",
        &mul_comm(),
        "u8",
    );
    t.prove(
        "square_i128",
        "(mul (add ?x ?y) (add ?x ?y)) = (add (add (mul ?x ?x) (mul (const 2) (mul ?x ?y))) (mul \
         ?y ?y))",
        &square,
        "i128",
    );
    t.prove(
        "diff_squares_i64",
        "(mul (sub ?x ?y) (add ?x ?y)) = (sub (mul ?x ?x) (mul ?y ?y))",
        &diff_squares,
        "i64",
    );
    t.says_something(&sub_add(), &add_one, "u64");

    // ── `(and ?x (const 255)) = ?x`: `and` is outside the fragment, so it
    //    is refused at every type; it is false at `u16`. ──
    for ty in ["u16", "u8"] {
        t.not_admitted(&and255(), ty, &format!("(and ?x (const 255)) = ?x at {ty}"));
    }

    // ── False rules: the two sides are two polynomials. ──
    for ty in ["u8", "u64"] {
        t.not_admitted(&add_one, ty, &format!("(add ?x (const 1)) = ?x at {ty}"));
    }
    t.accept(
        &not(sound(add_one.clone(), sty("u8"))),
        &RING.control("add_one_not_sound_u8"),
        "the proof that (add ?x (const 1)) = ?x is not Sound at u8",
    );
    t.not_admitted(&wrong_constant, "u8", "wrong_constant");
    t.not_admitted(&wrong_operand_order(), "u8", "wrong_operand_order");
    t.not_admitted(&wrong_not, "u8", "(neg (not ?x)) = (sub ?x (const 1))");

    // ── True at the type, and not an identity of polynomials over the
    //    integers or not in the fragment: `Sound` (by `exhaust8`), and not
    //    admitted. ──
    for (literal, theorem, what) in [
        (
            mul256,
            "mul256_sound_u8",
            "(mul ?x (const 256)) = (const 0)",
        ),
        (and_self, "and_self_sound_u8", "(and ?x ?x) = ?x"),
    ] {
        t.not_admitted(&literal, "u8", what);
        t.accept(
            &sound(literal, sty("u8")),
            &RING.control(theorem),
            &format!("the exhaust8 proof of {what}"),
        );
    }

    // ── Outside the fragment: an operator, a select, a comparison, a side
    //    condition, a side that is not a term, a Boolean variable, and the
    //    subjects of the other two procedures. ──
    for (literal, ty, what) in [
        (udiv_one, "u8", "(udiv ?x (const 1)) = ?x"),
        (select_same, "u8", "(select ?c ?x ?x) = ?x"),
        (cmp_self, "u8", "(icmp.eq ?x ?x) = true"),
        (cond_zero, "u8", "a rule with a side condition"),
        (unbound_side, "u8", "a side that is not a term"),
        (bool_var, "u8", "a variable of sort bool"),
        (
            and_not(),
            "u64",
            "(and ?x (not ?x)) = (const 0), bitwiseAll's",
        ),
        (absorb(), "u8", "(and ?x (or ?x ?y)) = ?x, exhaust8p's"),
    ] {
        t.not_admitted(&literal, ty, what);
    }

    // ── Another type: `false` at `bool`; and a term names its type. ──
    t.not_admitted(&sub_add(), "bool", "sub_add at bool");
    t.forged(
        &sound(sub_add(), sty("bool")),
        &RING.record(sub_add(), sty("u64")),
        "the u64 term of sub_add offered at bool",
    );
    t.forged(
        &sound(sub_add(), sty("u16")),
        &RING.record(sub_add(), sty("u8")),
        "the u8 term of sub_add offered at u16",
    );
    // ── Another rule: the term of a true rule offered for a false one. ──
    t.forged(
        &sound(add_one, sty("u8")),
        &RING.record(sub_add(), sty("u8")),
        "the term of sub_add offered for (add ?x (const 1)) = ?x",
    );
    t.counted
}

/// Run the controls of the three procedures on the entry of a kernel that
/// replayed the family under the budget: `exhaust8p`, `bitwiseAll`,
/// `ringAll`, in that order.
pub(super) fn three_procedures(k: &ReferenceKernel) -> [Counted; 3] {
    [packed_controls(k), bitwise_controls(k), ring_controls(k)]
}
