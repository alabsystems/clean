// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Component controls for the original-source ordering transport. These definitions
//! retain the actual source predicate, decision, and UInt arms. Ordinary Lean
//! elaboration/compiler/IR controls exercise the production caller separately.

use super::*;
use crate::source_equation::check_uint_source_equation;
use crate::TvDenotation;
use clean_kernel::{ConstantKind, Declaration, DeclarationVerification};

fn operands(width: u32, form: &str, model: bool) -> (Expr, Expr) {
    let (a, b, z) = if model {
        (Expr::bvar(2), Expr::bvar(1), Expr::bvar(0))
    } else {
        (v(0), v(1), v(2))
    };
    let operation = |op: &str, x: Expr, y: Expr| {
        if !model {
            return Expr::apps(c(&format!("UInt{width}.{op}")), [x, y]);
        }
        if op == "sub" {
            let m = crate::modulus(width);
            Expr::apps(
                c("Nat.mod"),
                [
                    Expr::apps(c("Nat.sub"), [Expr::apps(c("Nat.add"), [x, m.clone()]), y]),
                    m,
                ],
            )
        } else {
            Expr::apps(c(&format!("Nat.{op}")), [x, y])
        }
    };
    match form {
        "plain" => (a, b),
        "sub_left" => (operation("sub", a, b), z),
        "sub_right" => (a, operation("sub", b, z)),
        "land_left" => (operation("land", a, b), z),
        "lor_right" => (a, operation("lor", b, z)),
        "both" => (operation("sub", a, b.clone()), operation("lor", b, z)),
        _ => panic!("component fixture form"),
    }
}

fn register_source(
    env: &mut Environment,
    width: u32,
    label: &str,
    predicate: Expr,
    decision: Expr,
) -> Name {
    let uint = c(&format!("UInt{width}"));
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [uint.clone(), predicate, decision, v(0), v(1)],
    );
    let name = Name::from_string(label).num(u64::from(width));
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(
            uint.clone(),
            Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        ),
        value: lam(0, uint.clone(), lam(1, uint.clone(), lam(2, uint, body))),
        is_reducible: true,
    })
    .expect("the actual source predicate and its actual decision type-check");
    name
}

fn source(
    env: &mut Environment,
    width: u32,
    label: &str,
    form: &str,
    strict: bool,
    direct: bool,
    flipped_dictionary: bool,
) -> Name {
    let uint = c(&format!("UInt{width}"));
    let relation = if strict { "lt" } else { "le" };
    let (a, b) = operands(width, form, false);
    let predicate = if direct {
        assert!(!flipped_dictionary);
        Expr::apps(
            c(&format!("UInt{width}.{relation}")),
            [a.clone(), b.clone()],
        )
    } else {
        let class = if strict { "LT" } else { "LE" };
        let dictionary = if flipped_dictionary {
            // A VALID dictionary whose field computes b < a (or b <= a).
            // Its decision below is reversed too, so rejection cannot be
            // attributed to an ill-typed source Decidable instance.
            let field = lam(
                20,
                uint.clone(),
                lam(
                    21,
                    uint.clone(),
                    Expr::apps(c(&format!("UInt{width}.{relation}")), [v(21), v(20)]),
                ),
            );
            Expr::apps(
                Expr::const_(
                    Name::from_string(&format!("{class}.mk")),
                    vec![Level::zero()],
                ),
                [uint.clone(), field],
            )
        } else {
            c(&format!("inst{class}UInt{width}"))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string(&format!("{class}.{relation}")),
                vec![Level::zero()],
            ),
            [uint, dictionary, a.clone(), b.clone()],
        )
    };
    let dec_name = if strict { "decLt" } else { "decLe" };
    let decision = Expr::apps(
        c(&format!("UInt{width}.{dec_name}")),
        if flipped_dictionary { [b, a] } else { [a, b] },
    );
    register_source(env, width, label, predicate, decision)
}

fn denotation(
    width: u32,
    form: &str,
    strict: bool,
    swap_operands: bool,
    swap_arms: bool,
) -> TvDenotation {
    let (a, b) = operands(width, form, true);
    let condition = Expr::apps(
        c(if strict { "Nat.blt" } else { "Nat.ble" }),
        if swap_operands { [b, a] } else { [a, b] },
    );
    let (no, yes) = if swap_arms {
        (Expr::bvar(2), Expr::bvar(1))
    } else {
        (Expr::bvar(1), Expr::bvar(2))
    };
    TvDenotation {
        body: choice(c("Nat"), no, yes, condition),
        arity: 3,
        width,
        callees: vec![],
    }
}

fn require_original_judgment(env: &Environment, source: &Name, den: &TvDenotation, label: &str) {
    let before = env.closure_digest(source).unwrap();
    let checked = check_uint_source_equation(env, source, den, Name::from_string(label))
        .expect("computed-operand transport proves the full ORIGINAL source judgment");
    assert_eq!(*checked.source_closure_digest(), before);
    assert_eq!(env.closure_digest(source), Ok(before));
    let Declaration::Theorem {
        name, type_, value, ..
    } = checked.declaration()
    else {
        panic!("theorem");
    };
    assert!(!type_.has_fvar_quick() && !value.has_fvar_quick());
    assert!(env.audit_certification(type_, value).is_certified());
    let mut replay = env.clone();
    replay
        .add_decl(checked.declaration().clone())
        .expect("exact full theorem admission");
    let admitted = replay.get_const(name).unwrap();
    assert_eq!(admitted.kind, ConstantKind::Theorem);
    assert_eq!(admitted.type_, *type_);
    assert_eq!(admitted.value.as_ref(), Some(value));
    assert_eq!(
        replay.declaration_verification(name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    assert!(replay.axiom_deps(name).unwrap().is_empty());
    assert_eq!(
        replay.closure_digest(name).unwrap(),
        *checked.equation_closure_digest()
    );
}

#[test]
fn source_equation_computed_order_operands_all_uint_widths() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for (form, strict, direct) in [
            ("sub_left", true, false),
            ("sub_right", false, true),
            ("land_left", false, false),
            ("lor_right", true, true),
            ("both", true, false),
        ] {
            let label = format!("SourceEquation.computedOrder.{form}.{strict}.{direct}");
            let original = source(&mut env, width, &label, form, strict, direct, false);
            require_original_judgment(
                &env,
                &original,
                &denotation(width, form, strict, false, false),
                &format!("{label}.checked{width}"),
            );
        }
    }
}

#[test]
fn source_equation_computed_order_reads_actual_cross_class_relation() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let uint = c(&format!("UInt{width}"));
        let (a, b) = operands(width, "sub_left", false);
        // LT's field type is UInt -> UInt -> Prop; storing LE is valid.
        let dictionary = Expr::apps(
            Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
            [uint.clone(), c(&format!("UInt{width}.le"))],
        );
        let predicate = Expr::apps(
            Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            [uint, dictionary, a.clone(), b.clone()],
        );
        let decision = Expr::apps(c(&format!("UInt{width}.decLe")), [a, b]);
        let original = register_source(
            &mut env,
            width,
            "SourceEquation.actualCrossClassOrder",
            predicate,
            decision,
        );
        require_original_judgment(
            &env,
            &original,
            &denotation(width, "sub_left", false, false, false),
            &format!("SourceEquation.checkedCrossClassOrder{width}"),
        );
        check_uint_source_equation(
            &env,
            &original,
            &denotation(width, "sub_left", true, false, false),
            Name::from_string("SourceEquation.wrongCrossClassOrder").num(u64::from(width)),
        )
        .expect_err("the class name never substitutes the wrong actual relation");
    }
}

#[test]
fn source_equation_computed_order_refuses_wrong_model_and_actual_dictionary() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let original = source(
            &mut env,
            width,
            "SourceEquation.orderControls",
            "sub_left",
            true,
            false,
            false,
        );
        for (label, den) in [
            (
                "operand_order",
                denotation(width, "sub_left", true, true, false),
            ),
            (
                "comparison",
                denotation(width, "sub_left", false, false, false),
            ),
            (
                "computed_operand",
                denotation(width, "land_left", true, false, false),
            ),
            ("branches", denotation(width, "sub_left", true, false, true)),
        ] {
            check_uint_source_equation(
                &env,
                &original,
                &den,
                Name::from_string("SourceEquation.wrongComputedOrder")
                    .str(label)
                    .num(u64::from(width)),
            )
            .expect_err("wrong emitted predicate/operand/branch never proves the source judgment");
        }
        for strict in [false, true] {
            let changed = source(
                &mut env,
                width,
                &format!("SourceEquation.flippedOrderDictionary.{strict}"),
                "sub_left",
                strict,
                false,
                true,
            );
            check_uint_source_equation(
                &env,
                &changed,
                &denotation(width, "sub_left", strict, false, false),
                Name::from_string("SourceEquation.wrongActualOrderDictionary")
                    .str(if strict { "lt" } else { "le" })
                    .num(u64::from(width)),
            )
            .expect_err("typed LT/LE syntax alone does not establish a dictionary's meaning");
        }
    }
}

#[test]
fn source_equation_nat_predicate_conversion_keeps_actual_source_decision() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let to_nat = c(&format!("UInt{width}.toNat"));
        let a = Expr::app(to_nat.clone(), v(0));
        let b = Expr::app(to_nat, v(1));
        let original = register_source(
            &mut env,
            width,
            "SourceEquation.actualNatOrder",
            Expr::apps(c("Nat.le"), [a.clone(), b.clone()]),
            Expr::apps(c("Nat.decLe"), [a, b]),
        );
        require_original_judgment(
            &env,
            &original,
            &denotation(width, "plain", false, false, false),
            &format!("SourceEquation.checkedActualNatOrder{width}"),
        );
    }
}
