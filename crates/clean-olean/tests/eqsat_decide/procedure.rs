// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The procedure controls of the `eqsat_decide` gate: what Clean's reference
//! entry accepts and refuses for `exhaust8` under the budget, on a kernel that
//! replayed the family (the gate's module documentation lists them).
//!
//! A rule literal is built here as trust-cg's generator will build it
//! (constructors and raw `Nat` literals), the kernel is asked to accept it as
//! the rule `EqsatDecideControls.lean` defines under the same name, and the
//! term offered for a rule is the term a discharge record carries:
//! `EqsatDecide.exhaust8_sound <literal> <type> EqsatDecide.rflTrue`.

use std::cell::Cell;
use std::time::Instant;

use clean_kernel::env::{Declaration, EnvError};
use clean_kernel::expr::Expr;
use clean_kernel::tc::TypeError;
use clean_kernel::{ReferenceKernel, ReferenceRefusal};

use super::terms::{
    accepted, app, bin, boolean, c, conds, cvar, int_ty, lit, n, nat, rule, satisfiable, sorts,
    sound, un, var,
};
use super::{eq, refl, BUDGET};

/// The integer types `exhaust8` does not cover.
const WIDER: [&str; 10] = [
    "i16", "i32", "i64", "i128", "isize", "u16", "u32", "u64", "u128", "usize",
];

fn none() -> Expr {
    conds(vec![])
}

fn one() -> Expr {
    sorts(&[("t", false)])
}

fn two() -> Expr {
    sorts(&[("t", false), ("t", false)])
}

fn sel(condition: Expr, a: Expr, b: Expr) -> Expr {
    app("EqsatRule.Pat.sel", [condition, a, b])
}

fn bool_ty() -> Expr {
    c("EqsatRule.STy.bool")
}

/// `(and ?x (const 255)) = ?x`: true at eight bits only.
fn and255() -> Expr {
    rule(
        "equiv",
        one(),
        bin("and", var(0), lit(false, 255)),
        var(0),
        none(),
    )
}

fn and_not() -> Expr {
    rule(
        "equiv",
        one(),
        bin("and", var(0), un("not", var(0))),
        lit(false, 0),
        none(),
    )
}

fn band_absorb() -> Expr {
    rule(
        "equiv",
        sorts(&[("bool", false), ("bool", false)]),
        bin("bAnd", var(0), bin("bOr", var(0), var(1))),
        var(0),
        none(),
    )
}

fn select_same() -> Expr {
    rule(
        "equiv",
        sorts(&[("bool", false), ("t", false)]),
        sel(var(0), var(1), var(1)),
        var(1),
        none(),
    )
}

fn select_nested_sides(vars: Expr) -> Expr {
    rule(
        "equiv",
        vars,
        sel(var(0), sel(var(1), var(2), var(2)), var(2)),
        var(2),
        none(),
    )
}

/// 1,024 assignments: the most `exhaust8` enumerates.
fn select_nested() -> Expr {
    select_nested_sides(sorts(&[("bool", false), ("bool", false), ("t", false)]))
}

/// 2,048 assignments.
fn select_three() -> Expr {
    select_nested_sides(sorts(&[
        ("bool", false),
        ("bool", false),
        ("t", false),
        ("bool", false),
    ]))
}

fn bits_heavy() -> Expr {
    rule(
        "equiv",
        one(),
        un("ctpop", un("bitreverse", un("bswap", var(0)))),
        un("ctpop", var(0)),
        none(),
    )
}

fn heavy(x: u64) -> Expr {
    un("ctpop", un("bitreverse", un("bswap", var(x))))
}

/// The three bit operators of `bits_heavy` in each arm of two selects that
/// read two Booleans: 1,024 assignments.
fn bits_heavy_nested() -> Expr {
    rule(
        "equiv",
        sorts(&[("bool", false), ("bool", false), ("t", false)]),
        sel(var(0), sel(var(1), heavy(2), heavy(2)), heavy(2)),
        un("ctpop", var(2)),
        none(),
    )
}

/// `(udiv ?x (const 0))` refines to `rhs`: the left side is undefined
/// behaviour on every assignment, so the rule is `Sound` whatever `rhs` is.
fn udiv_zero_refines(rhs: Expr) -> Expr {
    rule(
        "refines",
        one(),
        bin("udiv", var(0), lit(false, 0)),
        rhs,
        none(),
    )
}

fn udiv_self(dir: &str) -> Expr {
    rule(
        dir,
        one(),
        bin("udiv", var(0), var(0)),
        lit(false, 1),
        none(),
    )
}

fn pow2_clear(with_condition: bool) -> Expr {
    rule(
        "equiv",
        sorts(&[("t", true)]),
        bin("and", cvar(0), bin("sub", cvar(0), lit(false, 1))),
        lit(false, 0),
        conds(if with_condition {
            vec![app("EqsatRule.Cond.pow2", [nat(0)])]
        } else {
            vec![]
        }),
    )
}

fn rotl_self_full() -> Expr {
    rule(
        "equiv",
        sorts(&[("t", true)]),
        bin("rotl", cvar(0), cvar(0)),
        cvar(0),
        conds(vec![app("EqsatRule.Cond.zeroModWidth", [nat(0)])]),
    )
}

/// `(add ?c 1) = ?c where (eq ?c 0) (ne ?c 0)`: `Sound` for want of an
/// assignment.
fn contradictory() -> Expr {
    let on_zero = |cond: &str| {
        app(
            &format!("EqsatRule.Cond.{cond}"),
            [nat(0), boolean(false), nat(0)],
        )
    };
    rule(
        "equiv",
        sorts(&[("t", true)]),
        bin("add", cvar(0), lit(false, 1)),
        cvar(0),
        conds(vec![on_zero("eq"), on_zero("ne")]),
    )
}

fn wrong_constant() -> Expr {
    rule(
        "equiv",
        one(),
        bin("mul", var(0), lit(false, 2)),
        var(0),
        none(),
    )
}

fn wrong_boolean_constant() -> Expr {
    rule(
        "equiv",
        one(),
        app("EqsatRule.Pat.cmp", [c("SemR.ICmpOp.ult"), var(0), var(0)]),
        c("EqsatRule.Pat.tt"),
        none(),
    )
}

fn wrong_select_arm() -> Expr {
    rule(
        "equiv",
        two(),
        sel(c("EqsatRule.Pat.tt"), var(0), var(1)),
        var(1),
        none(),
    )
}

fn wrong_operand_order() -> Expr {
    rule(
        "equiv",
        two(),
        bin("add", var(0), un("neg", var(1))),
        bin("sub", var(1), var(0)),
        none(),
    )
}

fn missing_side_condition() -> Expr {
    rule(
        "equiv",
        sorts(&[("t", true), ("t", false)]),
        bin("rotl", var(1), cvar(0)),
        var(1),
        none(),
    )
}

/// `?x = ?x` beside a second 8-bit variable: `Sound`, and 65,536 assignments.
fn two_vars() -> Expr {
    rule("equiv", two(), var(0), var(0), none())
}

fn unbound_side() -> Expr {
    rule("equiv", one(), var(1), var(1), none())
}

fn zero_at_bool() -> Expr {
    rule("equiv", sorts(&[]), lit(false, 0), lit(false, 0), none())
}

/// `(and ?x (or ?x ?y)) = ?x`: a true rule with two 8-bit variables, the one
/// step 0 measured at about 1.57 million heartbeats.
fn absorb2() -> Expr {
    rule(
        "equiv",
        two(),
        bin("and", var(0), bin("or", var(0), var(1))),
        var(0),
        none(),
    )
}

fn exhaust8(rule: Expr, ty: Expr) -> Expr {
    app("EqsatDecide.exhaust8", [rule, ty])
}

/// The term a discharge record carries for `Sound rule ty`.
fn by_exhaust8(rule: Expr, ty: Expr) -> Expr {
    app(
        "EqsatDecide.exhaust8_sound",
        [rule, ty, c("EqsatDecide.rflTrue")],
    )
}

/// `EqsatDecide.Defined rule ty`: some assignment meets the side conditions
/// and both sides are one common value there.
fn defined(rule: Expr, ty: Expr) -> Expr {
    app("EqsatDecide.Defined", [rule, ty])
}

/// The same `true` offered for `Defined rule ty`.
fn defined_by_exhaust8(rule: Expr, ty: Expr) -> Expr {
    app(
        "EqsatDecide.exhaust8_defined",
        [rule, ty, c("EqsatDecide.rflTrue")],
    )
}

/// The same `true` offered for `Satisfiable rule ty`.
fn satisfiable_by_exhaust8(rule: Expr, ty: Expr) -> Expr {
    app(
        "EqsatDecide.exhaust8_satisfiable",
        [rule, ty, c("EqsatDecide.rflTrue")],
    )
}

/// `sweep rule true 8 256`: the enumeration alone, without the size limit.
fn sweep8(rule: Expr) -> Expr {
    app("EqsatDecide.sweep", [rule, boolean(true), nat(8), nat(256)])
}

fn is(value: Expr, answer: bool) -> Expr {
    eq("Bool", value, boolean(answer))
}

fn by_refl(answer: bool) -> Expr {
    refl("Bool", boolean(answer))
}

/// The limit of the budget refusal `e` is, when it is one.
fn out_of_budget(e: &ReferenceRefusal) -> Option<u32> {
    match e {
        ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
            source: TypeError::HeartbeatExceeded { limit, .. },
            ..
        }) => Some(*limit),
        _ => None,
    }
}

/// The entry refuses `val : ty`, and for the claim: the kernel found that the
/// term does not have the type (`TypeMismatch`). A refusal for lack of budget,
/// depth, memory or a declaration count, or an interruption, would say nothing
/// of the term and fails here.
pub(super) fn refused_for_the_claim(k: &ReferenceKernel, ty: &Expr, val: &Expr, what: &str) {
    let e = k
        .check_closed_term(ty, val)
        .expect_err(&format!("{what} must be refused"));
    assert!(
        matches!(
            e,
            ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
                source: TypeError::TypeMismatch { .. },
                ..
            })
        ),
        "{what}: refused, but not as a term that does not have the type, so the refusal says \
         nothing of the claim: {e:?}"
    );
}

/// The smallest heartbeat limit under which the kernel accepts `val : ty`, by
/// bisection below the budget with a limit of the check's own
/// (`Environment::check_decl_readonly_with_heartbeat`, the check
/// `check_closed_term` runs). Every refusal below that limit must name
/// heartbeats: a caller tells `timed-out` from `kernel-refused` by it.
pub(super) fn smallest_passing_limit(
    k: &ReferenceKernel,
    ty: &Expr,
    val: &Expr,
    what: &str,
) -> u32 {
    let decl = Declaration::Definition {
        name: n("eqsat_decide.cost"),
        level_params: vec![],
        type_: ty.clone(),
        value: val.clone(),
        is_reducible: false,
    };
    let passes = |limit: u32| -> bool {
        match k
            .environment()
            .check_decl_readonly_with_heartbeat(&decl, Some(limit))
        {
            Ok(()) => true,
            Err(EnvError::TypeCheckFailed {
                source: TypeError::HeartbeatExceeded { .. },
                ..
            }) => false,
            Err(other) => panic!(
                "{what}: a check refused below its cost must name heartbeats; at {limit}: \
                 {other:?}"
            ),
        }
    };
    assert!(passes(BUDGET), "{what}: passes at the budget");
    // `fails` is a limit the check is refused at (0 stands for "no limit
    // below 1" and is never offered: a limit of 0 is unlimited).
    let (mut fails, mut passing) = (0u32, BUDGET);
    while passing - fails > 1 {
        let mid = fails + (passing - fails) / 2;
        if passes(mid) {
            passing = mid;
        } else {
            fails = mid;
        }
    }
    passing
}

/// What the procedure controls counted.
pub(super) struct ProcedureControls {
    /// Rules proved by the record term, each at one type.
    pub(super) proved: usize,
    /// The dearest of them, in heartbeats.
    pub(super) dearest: u32,
    /// The sum of their costs, in heartbeats.
    pub(super) total: u64,
    /// Terms the entry refused for the claim.
    pub(super) refused: usize,
}

/// Run every procedure control on the entry of a kernel that replayed the
/// family under the budget.
#[allow(clippy::too_many_lines)]
pub(super) fn procedure_controls(k: &ReferenceKernel) -> ProcedureControls {
    let u8_ = || int_ty("u8");
    let i8_ = || int_ty("i8");

    // ── The literals built here are the rules the controls module defines. ──
    let literals: [(&str, Expr); 25] = [
        ("and255", and255()),
        ("andNot", and_not()),
        ("bandAbsorb", band_absorb()),
        ("selectSame", select_same()),
        ("selectNested", select_nested()),
        ("selectThree", select_three()),
        ("bitsHeavy", bits_heavy()),
        ("bitsHeavyNested", bits_heavy_nested()),
        ("udivZeroRefines", udiv_zero_refines(lit(false, 7))),
        (
            "udivZeroRefinesTt",
            udiv_zero_refines(c("EqsatRule.Pat.tt")),
        ),
        ("udivZeroRefinesUnbound", udiv_zero_refines(var(1))),
        ("udivSelfRefines", udiv_self("refines")),
        ("udivSelfEquiv", udiv_self("equiv")),
        ("pow2Clear", pow2_clear(true)),
        ("pow2ClearNoCond", pow2_clear(false)),
        ("rotlSelfFull", rotl_self_full()),
        ("contradictory", contradictory()),
        ("wrongConstant", wrong_constant()),
        ("wrongBooleanConstant", wrong_boolean_constant()),
        ("wrongSelectArm", wrong_select_arm()),
        ("wrongOperandOrder", wrong_operand_order()),
        ("missingSideCondition", missing_side_condition()),
        ("twoVars", two_vars()),
        ("unboundSide", unbound_side()),
        ("zeroAtBool", zero_at_bool()),
    ];
    for (name, literal) in &literals {
        accepted(
            k,
            &eq(
                "EqsatRule.Rule",
                c(&format!("EqsatDecideControls.{name}")),
                literal.clone(),
            ),
            &refl("EqsatRule.Rule", literal.clone()),
            &format!("the literal built here is EqsatDecideControls.{name}"),
        );
    }
    // The comparison tells two rules apart.
    refused_for_the_claim(
        k,
        &eq("EqsatRule.Rule", c("EqsatDecideControls.and255"), and_not()),
        &refl("EqsatRule.Rule", and_not()),
        "another rule's literal offered as EqsatDecideControls.and255",
    );

    // ── Rules the record term proves, each under the budget. ──
    let proved: [(&str, &str, Expr, Expr, u32); 16] = [
        (
            "and255_u8",
            "(and ?x (const 255)) = ?x",
            and255(),
            u8_(),
            256,
        ),
        (
            "and255_i8",
            "(and ?x (const 255)) = ?x",
            and255(),
            i8_(),
            256,
        ),
        (
            "and_not_u8",
            "(and ?x (not ?x)) = (const 0)",
            and_not(),
            u8_(),
            256,
        ),
        (
            "and_not_i8",
            "(and ?x (not ?x)) = (const 0)",
            and_not(),
            i8_(),
            256,
        ),
        (
            "band_absorb_bool",
            "(band ?p (bor ?p ?q)) = ?p",
            band_absorb(),
            bool_ty(),
            4,
        ),
        (
            "select_same_u8",
            "(select ?c ?x ?x) = ?x",
            select_same(),
            u8_(),
            512,
        ),
        (
            "select_same_i8",
            "(select ?c ?x ?x) = ?x",
            select_same(),
            i8_(),
            512,
        ),
        (
            "select_same_bool",
            "(select ?c ?x ?x) = ?x",
            select_same(),
            bool_ty(),
            4,
        ),
        (
            "select_nested_u8",
            "(select ?p (select ?q ?x ?x) ?x) = ?x",
            select_nested(),
            u8_(),
            1024,
        ),
        (
            "bits_heavy_u8",
            "(ctpop (bitreverse (bswap ?x))) = (ctpop ?x)",
            bits_heavy(),
            u8_(),
            256,
        ),
        (
            "bits_heavy_nested_u8",
            "(select ?p (select ?q H H) H) = (ctpop ?x), H = (ctpop (bitreverse (bswap ?x)))",
            bits_heavy_nested(),
            u8_(),
            1024,
        ),
        (
            "udiv_self_refines_u8",
            "(udiv ?x ?x) refines to (const 1)",
            udiv_self("refines"),
            u8_(),
            256,
        ),
        (
            "udiv_self_refines_i8",
            "(udiv ?x ?x) refines to (const 1)",
            udiv_self("refines"),
            i8_(),
            256,
        ),
        (
            "pow2_clear_u8",
            "(and ?c (sub ?c 1)) = 0 where (pow2 ?c)",
            pow2_clear(true),
            u8_(),
            256,
        ),
        (
            "rotl_self_full_u8",
            "(rotl ?n ?n) = ?n where ?n == 0 mod width",
            rotl_self_full(),
            u8_(),
            256,
        ),
        ("zero_u8", "(const 0) = (const 0)", zero_at_bool(), u8_(), 1),
    ];
    let (mut dearest, mut total) = (0u32, 0u64);
    for (theorem, text, literal, ty, assignments) in &proved {
        let goal = sound(literal.clone(), ty.clone());
        // The controls module's theorem states the literal built here.
        accepted(
            k,
            &goal,
            &c(&format!("EqsatDecideControls.{theorem}")),
            &format!("EqsatDecideControls.{theorem} for the literal built here"),
        );
        let term = by_exhaust8(literal.clone(), ty.clone());
        let started = Instant::now();
        accepted(k, &goal, &term, &format!("{theorem} by the record term"));
        let micros = started.elapsed().as_micros();
        let cost = smallest_passing_limit(k, &goal, &term, theorem);
        dearest = dearest.max(cost);
        total += u64::from(cost);
        eprintln!(
            "eqsat_decide: {theorem}: `{text}`, {assignments} assignment(s): accepted under \
             {BUDGET} in {micros} us; smallest passing limit {cost} heartbeats"
        );
    }

    let refusals = Cell::new(0usize);
    // A term the entry refuses for the claim.
    let forged = |goal: &Expr, proof: &Expr, what: &str| {
        refused_for_the_claim(k, goal, proof, what);
        refusals.set(refusals.get() + 1);
    };
    // `exhaust8 rule ty` is `false` (accepted by `Eq.refl false`), `true` is
    // refused, and so is the record term for `Sound rule ty`.
    let not_admitted = |literal: &Expr, ty: &Expr, what: &str| {
        let answer = exhaust8(literal.clone(), ty.clone());
        accepted(
            k,
            &is(answer.clone(), false),
            &by_refl(false),
            &format!("exhaust8 = false for {what}"),
        );
        forged(
            &is(answer, true),
            &by_refl(true),
            &format!("exhaust8 = true for {what}"),
        );
        forged(
            &sound(literal.clone(), ty.clone()),
            &by_exhaust8(literal.clone(), ty.clone()),
            &format!("the record term for {what}"),
        );
    };

    // ── False rules: an assignment fails. ──
    not_admitted(&wrong_constant(), &u8_(), "wrong_constant at u8");
    not_admitted(
        &wrong_boolean_constant(),
        &u8_(),
        "wrong_boolean_constant at u8",
    );
    not_admitted(&wrong_select_arm(), &bool_ty(), "wrong_select_arm at bool");
    not_admitted(
        &pow2_clear(false),
        &u8_(),
        "pow2_clear without its side condition at u8",
    );
    // ── A side that is not a term. ──
    not_admitted(&unbound_side(), &u8_(), "an unbound side at u8");
    not_admitted(&zero_at_bool(), &bool_ty(), "(const 0) at bool");
    // ── Direction: a refines-only rule offered as equiv. ──
    not_admitted(
        &udiv_self("equiv"),
        &u8_(),
        "(udiv ?x ?x) = 1 as equiv at u8",
    );
    forged(
        &sound(udiv_self("equiv"), u8_()),
        &by_exhaust8(udiv_self("refines"), u8_()),
        "the refines rule's term offered for the equiv statement",
    );

    // ── Width: the term of a true 8-bit rule proves nothing at another
    //    type, whichever type the term names. ──
    for wide in WIDER {
        not_admitted(&and255(), &int_ty(wide), &format!("and255 at {wide}"));
        forged(
            &sound(and255(), int_ty(wide)),
            &by_exhaust8(and255(), u8_()),
            &format!("the u8 term of and255 offered at {wide}"),
        );
    }

    // ── Size: over 1,024 assignments the answer is `false` before any
    //    assignment is tested, for a false rule, a true one and a `Sound`
    //    one alike. ──
    let started = Instant::now();
    for (literal, what) in [
        (wrong_select_arm(), "wrong_select_arm at u8"),
        (wrong_operand_order(), "wrong_operand_order at u8"),
        (missing_side_condition(), "missing_side_condition at u8"),
        (two_vars(), "?x = ?x beside a second 8-bit variable"),
        (absorb2(), "(and ?x (or ?x ?y)) = ?x at u8"),
        (select_three(), "one 8-bit variable and three Booleans"),
    ] {
        not_admitted(&literal, &u8_(), what);
    }
    eprintln!(
        "eqsat_decide: six rules over the size limit: 18 checks in {} us",
        started.elapsed().as_micros()
    );
    // The three wrong ones are false, not only large: the enumeration alone
    // finds a failing assignment.
    for (literal, what) in [
        (wrong_select_arm(), "wrong_select_arm"),
        (wrong_operand_order(), "wrong_operand_order"),
        (missing_side_condition(), "missing_side_condition"),
    ] {
        accepted(
            k,
            &is(sweep8(literal.clone()), false),
            &by_refl(false),
            &format!("sweep = false for {what}"),
        );
        forged(
            &is(sweep8(literal), true),
            &by_refl(true),
            &format!("sweep = true for {what}"),
        );
    }
    // And the `Sound` one is `Sound`: the hand proof is accepted where the
    // record term is refused.
    accepted(
        k,
        &sound(two_vars(), u8_()),
        &c("EqsatDecideControls.two_vars_sound_u8"),
        "the hand proof of ?x = ?x beside a second variable",
    );

    // ── Side conditions no assignment satisfies: `Sound`, and not admitted. ──
    accepted(
        k,
        &sound(contradictory(), u8_()),
        &c("EqsatDecideControls.contradictory_is_sound_u8"),
        "the hand proof that the contradictory rule is Sound",
    );
    not_admitted(&contradictory(), &u8_(), "the contradictory rule at u8");
    accepted(
        k,
        &is(sweep8(contradictory()), true),
        &by_refl(true),
        "sweep = true for the contradictory rule",
    );
    forged(
        &satisfiable(contradictory(), u8_()),
        &satisfiable_by_exhaust8(contradictory(), u8_()),
        "Satisfiable of the contradictory rule by exhaust8",
    );
    accepted(
        k,
        &satisfiable(pow2_clear(true), u8_()),
        &satisfiable_by_exhaust8(pow2_clear(true), u8_()),
        "Satisfiable of pow2_clear by exhaust8",
    );
    forged(
        &defined(contradictory(), u8_()),
        &defined_by_exhaust8(contradictory(), u8_()),
        "Defined of the contradictory rule by exhaust8",
    );
    accepted(
        k,
        &defined(pow2_clear(true), u8_()),
        &defined_by_exhaust8(pow2_clear(true), u8_()),
        "Defined of pow2_clear by exhaust8",
    );
    // A refines rule whose left side is undefined at 0 has an assignment on
    // which both sides are one value.
    accepted(
        k,
        &defined(udiv_self("refines"), u8_()),
        &defined_by_exhaust8(udiv_self("refines"), u8_()),
        "Defined of (udiv ?x ?x) refines to 1 by exhaust8",
    );

    // ── A left side that is undefined behaviour on every assignment: the
    //    `refines` rule is `Sound` whatever its right side is, and is not
    //    admitted, whether that right side is a value, a Boolean where a
    //    value of the type belongs, or not a term. ──
    let never_defined = udiv_zero_refines(lit(false, 7));
    accepted(
        k,
        &sound(never_defined.clone(), u8_()),
        &c("EqsatDecideControls.udiv_zero_refines_is_sound_u8"),
        "the proof that (udiv ?x 0) refines to 7 is Sound",
    );
    for (rhs, what) in [
        (lit(false, 7), "(udiv ?x 0) refines to 7 at u8"),
        (
            c("EqsatRule.Pat.tt"),
            "(udiv ?x 0) refines to true at u8 (a Boolean at an integer type)",
        ),
        (var(1), "(udiv ?x 0) refines to an unbound ?y at u8"),
    ] {
        not_admitted(&udiv_zero_refines(rhs), &u8_(), what);
    }
    forged(
        &defined(never_defined.clone(), u8_()),
        &defined_by_exhaust8(never_defined, u8_()),
        "Defined of (udiv ?x 0) refines to 7 by exhaust8",
    );
    // The enumeration alone lets the first two stand, as `Sound` does, and
    // refuses the third: a right side that is not a term stands nowhere.
    for rhs in [lit(false, 7), c("EqsatRule.Pat.tt")] {
        accepted(
            k,
            &is(sweep8(udiv_zero_refines(rhs)), true),
            &by_refl(true),
            "sweep = true for a refines rule whose left side is never defined",
        );
    }
    accepted(
        k,
        &is(sweep8(udiv_zero_refines(var(1))), false),
        &by_refl(false),
        "sweep = false for (udiv ?x 0) refines to an unbound ?y",
    );
    forged(
        &is(sweep8(udiv_zero_refines(var(1))), true),
        &by_refl(true),
        "sweep = true for (udiv ?x 0) refines to an unbound ?y",
    );

    // ── The budget is in force on this entry: the enumeration of a true
    //    rule with two 8-bit variables, asked for without the size limit,
    //    runs out, and the refusal names the budget. ──
    let started = Instant::now();
    let ran_out = k
        .check_closed_term(&is(sweep8(absorb2()), true), &by_refl(true))
        .expect_err("65,536 assignments do not fit the budget");
    assert_eq!(
        out_of_budget(&ran_out),
        Some(BUDGET),
        "the two-variable enumeration is refused for the budget: {ran_out:?}"
    );
    eprintln!(
        "eqsat_decide: sweep of `(and ?x (or ?x ?y)) = ?x` (65,536 assignments): refused with \
         HeartbeatExceeded at {BUDGET} in {} ms",
        started.elapsed().as_millis()
    );

    ProcedureControls {
        proved: proved.len(),
        dearest,
        total,
        refused: refusals.get(),
    }
}
