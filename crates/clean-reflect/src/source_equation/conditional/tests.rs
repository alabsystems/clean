// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Component controls use actual kernel-checked UInt definitions and supplied
//! Nat denotations. Actual source-text/compiler/IR pipeline replay is a separate
//! qualification owned by the compiler integration tests.

use super::*;
use crate::source_equation::check_uint_source_equation;
use crate::TvDenotation;
use clean_kernel::{ConstantKind, Declaration, DeclarationVerification, Environment};

#[test]
fn source_equation_conditional_false_comparison_bridge_is_cic() {
    let env = Environment::with_prelude();
    let (a, b, hn) = (v(0), v(1), v(2));
    let p = Expr::apps(c("Nat.le"), [a.clone(), b.clone()]);
    let not_p = Expr::arrow(p.clone(), c("False"));
    let cond = Expr::apps(c("Nat.ble"), [a.clone(), b.clone()]);
    let mut proof = Search {
        environment: &env,
        width: 32,
        result: ScalarSort::UInt(32),
        params: &[],
        next: 300,
    }
    .false_comparison(p, cond.clone(), a, b, hn);
    let mut statement = eq(c("Bool"), cond, c("Bool.false"));
    for (id, ty) in [(2, not_p), (1, c("Nat")), (0, c("Nat"))] {
        proof = lam(id, ty.clone(), proof);
        statement = Expr::pi(
            BinderInfo::Default,
            ty,
            statement.abstract_fvar(FVarId::new(id)),
        );
    }
    let audit = env.audit_certification(&statement, &proof);
    assert!(
        audit.is_certified(),
        "constructive Bool elimination: {:?}",
        audit.issues
    );
}

fn source(env: &mut Environment, width: u32, label: &str, flipped: bool, arm: &str) -> Name {
    let uint = c(&format!("UInt{width}"));
    let (a, b) = (v(0), v(1));
    let predicate = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            uint.clone(),
            c(&format!("instLTUInt{width}")),
            if flipped { b.clone() } else { a.clone() },
            if flipped { a.clone() } else { b.clone() },
        ],
    );
    let decision = Expr::apps(
        c(&format!("UInt{width}.decLt")),
        if flipped {
            [b.clone(), a.clone()]
        } else {
            [a.clone(), b.clone()]
        },
    );
    let yes = match arm {
        "add" => Expr::apps(
            c(&format!("UInt{width}.add")),
            [
                a.clone(),
                Expr::app(c(&format!("UInt{width}.ofNat")), Expr::nat_lit(1u64)),
            ],
        ),
        "sub" => Expr::apps(c(&format!("UInt{width}.sub")), [a.clone(), b.clone()]),
        "land" => Expr::apps(c(&format!("UInt{width}.land")), [a.clone(), b.clone()]),
        _ => panic!("fixture arm"),
    };
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [uint.clone(), predicate, decision, yes, b],
    );
    let name = Name::from_string(label).num(u64::from(width));
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        value: lam(0, uint.clone(), lam(1, uint, body)),
        is_reducible: true,
    })
    .expect("the actual original UInt conditional definition kernel-checks");
    name
}

fn denotation(width: u32, flipped: bool, swap_arms: bool, arm: &str) -> TvDenotation {
    let (a, b) = (Expr::bvar(1), Expr::bvar(0));
    let cond = Expr::apps(
        c("Nat.blt"),
        if flipped {
            [b.clone(), a.clone()]
        } else {
            [a.clone(), b.clone()]
        },
    );
    let modulus = crate::modulus(width);
    let yes = match arm {
        "add" | "add2" => Expr::apps(
            c("Nat.mod"),
            [
                Expr::apps(
                    c("Nat.add"),
                    [a, Expr::nat_lit(if arm == "add2" { 2u64 } else { 1u64 })],
                ),
                modulus,
            ],
        ),
        "sub" => Expr::apps(
            c("Nat.mod"),
            [
                Expr::apps(
                    c("Nat.sub"),
                    [Expr::apps(c("Nat.add"), [a, modulus.clone()]), b.clone()],
                ),
                modulus,
            ],
        ),
        "land" => Expr::apps(c("Nat.land"), [a, b.clone()]),
        _ => panic!("fixture arm"),
    };
    TvDenotation {
        body: if swap_arms {
            choice(c("Nat"), yes, b, cond)
        } else {
            choice(c("Nat"), b, yes, cond)
        },
        arity: 2,
        width,
        callees: vec![],
    }
}

#[test]
fn source_equation_conditional_actual_original_definition_all_uint_widths() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let source = source(
            &mut env,
            width,
            "SourceEquation.actualConditional",
            false,
            "add",
        );
        let before = env.closure_digest(&source).unwrap();
        let checked = check_uint_source_equation(
            &env,
            &source,
            &denotation(width, false, false, "add"),
            Name::from_string("SourceEquation.checkedConditional").num(u64::from(width)),
        )
        .expect("the full ORIGINAL source call, not a reconstructed UInt choice, is proved");
        assert_eq!(*checked.source_closure_digest(), before);
        assert_eq!(env.closure_digest(&source), Ok(before));
        let Declaration::Theorem {
            name, type_, value, ..
        } = checked.declaration()
        else {
            panic!("a theorem")
        };
        assert!(!type_.has_fvar_quick() && !value.has_fvar_quick());
        assert!(env.audit_certification(type_, value).is_certified());
        let mut replay = env.clone();
        replay
            .add_decl(checked.declaration().clone())
            .expect("independent full theorem admission");
        assert_eq!(replay.get_const(name).unwrap().kind, ConstantKind::Theorem);
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
}

#[test]
fn source_equation_conditional_comparison_and_arms_are_not_assumed() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        let original = source(
            &mut env,
            width,
            "SourceEquation.conditionalControls",
            false,
            "add",
        );
        for (label, den) in [
            ("comparison", denotation(width, true, false, "add")),
            ("arms", denotation(width, false, true, "add")),
            ("operation", denotation(width, false, false, "sub")),
            ("literal", denotation(width, false, false, "add2")),
        ] {
            check_uint_source_equation(
                &env,
                &original,
                &den,
                Name::from_string("SourceEquation.wrongConditional")
                    .str(label)
                    .num(u64::from(width)),
            )
            .expect_err(
                "a changed predicate, operand order or branch cannot prove the actual source call",
            );
        }
        let changed = source(
            &mut env,
            width,
            "SourceEquation.changedConditional",
            true,
            "add",
        );
        check_uint_source_equation(
            &env,
            &changed,
            &denotation(width, false, false, "add"),
            Name::from_string("SourceEquation.wrongOriginal").num(u64::from(width)),
        )
        .expect_err("the actual source predicate must kernel-match the reflected comparison");
    }
}

#[test]
fn source_equation_conditional_reuses_actual_subtraction_and_bitwise_leaf_proofs() {
    let mut env = Environment::with_prelude();
    for width in [8, 16, 32, 64] {
        for arm in ["sub", "land"] {
            let original = source(
                &mut env,
                width,
                &format!("SourceEquation.conditional{arm}"),
                false,
                arm,
            );
            check_uint_source_equation(
                &env,
                &original,
                &denotation(width, false, false, arm),
                Name::from_string("SourceEquation.checkedConditionalLeaf")
                    .str(arm)
                    .num(u64::from(width)),
            )
            .expect("the actual source arm needs its genuine arithmetic proof");
        }
    }
}

#[test]
fn source_equation_conditional_refuses_a_forged_bool_rec_motive() {
    let mut env = Environment::with_prelude();
    let original = source(
        &mut env,
        32,
        "SourceEquation.conditionalMotive",
        false,
        "add",
    );
    let mut den = denotation(32, false, false, "add");
    let args: Vec<_> = den.body.get_app_args().into_iter().cloned().collect();
    den.body = bool_rec(
        Level::succ(Level::zero()),
        Expr::lam(BinderInfo::Default, c("Bool"), c("UInt32")),
        args[1].clone(),
        args[2].clone(),
        args[3].clone(),
    );
    check_uint_source_equation(
        &env,
        &original,
        &den,
        Name::from_string("SourceEquation.wrongMotive"),
    )
    .expect_err("the Nat-valued constant motive is required, not guessed from argument count");
}

#[test]
fn source_equation_conditional_nested_actual_arms_keep_binders_disjoint() {
    let mut env = Environment::with_prelude();
    let base = source(
        &mut env,
        32,
        "SourceEquation.innerConditional",
        false,
        "add",
    );
    let mut inner = env.get_const(&base).unwrap().value.clone().unwrap();
    for arg in [v(0), v(1)] {
        let ExprKind::Lam(_, _, body) = inner.kind() else {
            panic!("actual source lambda")
        };
        inner = body.instantiate(&arg);
    }
    let args = inner.get_app_args();
    let uint = c("UInt32");
    let outer = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            uint.clone(),
            args[1].clone(),
            args[2].clone(),
            inner.clone(),
            v(1),
        ],
    );
    let original = Name::from_string("SourceEquation.nestedConditional");
    env.add_decl(Declaration::Definition {
        name: original.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        value: lam(0, uint.clone(), lam(1, uint, outer)),
        is_reducible: true,
    })
    .expect("actual nested original source");
    for swapped in [false, true] {
        let inner_den = denotation(32, swapped, false, "add");
        let flat = denotation(32, false, false, "add");
        let cond = flat.body.get_app_args()[3].clone();
        let den = TvDenotation {
            body: choice(c("Nat"), Expr::bvar(0), inner_den.body, cond),
            ..flat
        };
        let result = check_uint_source_equation(
            &env,
            &original,
            &den,
            Name::from_string("SourceEquation.checkedNested").num(u64::from(swapped)),
        );
        if swapped {
            result.expect_err("the inner source predicate is checked too");
        } else {
            result
                .expect("nested original conditional equations preserve input and scratch binders");
        }
    }
}

#[test]
fn source_equation_conditional_leaf_search_checks_its_actual_source_endpoint() {
    let mut env = Environment::with_prelude();
    let base = source(&mut env, 32, "SourceEquation.leafSearchBase", false, "add");
    let mut body = env.get_const(&base).unwrap().value.clone().unwrap();
    for arg in [v(0), v(1)] {
        let ExprKind::Lam(_, _, result) = body.kind() else {
            panic!("source lambda")
        };
        body = result.instantiate(&arg);
    }
    let args = body.get_app_args();
    let uint = c("UInt32");
    // This original source writes the IR's Nat subtraction spelling itself.
    // Conversion proves this arm; a candidate about UInt.sub has a different
    // left endpoint and must not suppress that valid conversion proof.
    let nat_arm = Expr::apps(
        c("Nat.sub"),
        [
            Expr::apps(
                c("Nat.add"),
                [Expr::app(c("UInt32.toNat"), v(0)), crate::modulus(32)],
            ),
            Expr::app(c("UInt32.toNat"), v(1)),
        ],
    );
    let actual = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            uint.clone(),
            args[1].clone(),
            args[2].clone(),
            Expr::app(c("UInt32.ofNat"), nat_arm),
            v(1),
        ],
    );
    let original = Name::from_string("SourceEquation.actualNatSubConditional");
    env.add_decl(Declaration::Definition {
        name: original.clone(),
        level_params: vec![],
        type_: Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone())),
        value: lam(0, uint.clone(), lam(1, uint, actual)),
        is_reducible: true,
    })
    .expect("actual source with a convertible Nat arithmetic arm");
    check_uint_source_equation(
        &env,
        &original,
        &denotation(32, false, false, "sub"),
        Name::from_string("SourceEquation.checkedActualNatSubConditional"),
    )
    .expect(
        "search checks the actual source leaf rather than assuming a reified UInt.sub endpoint",
    );
}
