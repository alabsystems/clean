// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Original boundary goals through the consumer's canonical typed proof carrier.
use crate::spec::Specification;
use clean_kernel::{BinderInfo, Declaration, Expr, Level, Name, TypeChecker};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn eq_primitive(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())]),
        args,
    )
}
fn value(n: Expr) -> Expr {
    app("IRStepResult.value", [app("IRScalar.int_", [n])])
}
fn wrap(width: u64, n: Expr) -> Expr {
    app("ir_wrap", [Expr::nat_lit(width), n])
}
fn actual(width: u64, word: u64, amount: u64) -> Expr {
    app(
        "ir_binop_eval",
        [
            c("IRBinOp.shl"),
            app("IRTy.uint_", [Expr::nat_lit(width)]),
            app("IRScalar.int_", [Expr::nat_lit(word)]),
            app("IRScalar.int_", [Expr::nat_lit(amount)]),
        ],
    )
}
fn trans(a: Expr, b: Expr, end: Expr, first: Expr, second: Expr) -> Expr {
    eq_primitive("Eq.trans", [c("IRStepResult"), a, b, end, first, second])
}
fn bound(n: u64, gap: u64) -> Expr {
    app(
        "Nat.le_add_right",
        [app("Nat.succ", [Expr::nat_lit(n)]), Expr::nat_lit(gap)],
    )
}

fn replay(
    spec: &Specification,
    name: String,
    actual: Expr,
    answer: Expr,
    proof: Expr,
    required: Option<&str>,
) {
    let goal = eq_primitive("Eq", [c("IRStepResult"), actual, answer]);
    let goal_bytes = trust_ir::proof::encode_clean_expr_v1(&goal).unwrap();
    let proof_bytes = trust_ir::proof::encode_clean_expr_v1(&proof).unwrap();
    let decoded_goal = trust_ir::proof::decode_clean_expr_v1(&goal_bytes).unwrap();
    let decoded_proof = trust_ir::proof::decode_clean_expr_v1(&proof_bytes).unwrap();
    assert_eq!(decoded_goal, goal);
    assert_eq!(decoded_proof, proof);
    for (claim, body) in [(&goal, &proof), (&decoded_goal, &decoded_proof)] {
        assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
        assert!(!body.has_fvar_quick() && !body.has_loose_bvars());
        let mut checker = TypeChecker::new(spec.env());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker
            .check_type(body, claim)
            .expect("complete actual boundary proof");
        assert!(!checker.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        spec.env()
            .check_decl_readonly_strict(&Declaration::Definition {
                name: Name::from_string(&name),
                level_params: vec![],
                type_: claim.clone(),
                value: body.clone(),
                is_reducible: true,
            })
            .expect("strict complete closed boundary declaration");
        let audit = spec.env().audit_certification(claim, body);
        assert!(audit.is_certified(), "{name}: {audit:#?}");
        if let Some(root) = required {
            assert!(audit.dependencies.contains(&Name::from_string(root)));
        }
        for dependency in &audit.dependencies {
            assert!(spec.env().axiom_deps(dependency).unwrap().is_empty());
            assert!(spec.env().trust_marker_deps(dependency).unwrap().is_empty());
        }
    }
}

pub(super) fn check() {
    let spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack().unwrap();
    for width in [32_u64, 64] {
        let limit = 1_u128 << width;
        let maximum = (limit - 1) as u64;
        for (index, (word, amount)) in [
            (0, 0),
            (maximum, 0),
            (maximum, width - 1),
            (1_u64 << (width - 1), width - 1),
            (maximum, 31),
            (maximum, 24),
        ]
        .into_iter()
        .enumerate()
        {
            let answer = ((u128::from(word) << amount) & (limit - 1)) as u64;
            let power = app("ir_nat_pow2", [Expr::nat_lit(amount)]);
            let raw_product = app("ir_nat_mul", [Expr::nat_lit(word), power.clone()]);
            let product = app("Nat.mul", [Expr::nat_lit(word), power.clone()]);
            let raw = value(wrap(width, raw_product.clone()));
            let multiplied = value(wrap(width, product.clone()));
            let residue = app(
                "Nat.mod",
                [product.clone(), app("Nat.succ", [Expr::nat_lit(maximum)])],
            );
            let normalized = value(residue.clone());
            let expected = value(Expr::nat_lit(answer));
            let product_agreement = app(
                "ir_eq_cong",
                [
                    c("Nat"),
                    c("IRStepResult"),
                    Expr::lam(
                        BinderInfo::Default,
                        c("Nat"),
                        value(wrap(width, Expr::bvar(0))),
                    ),
                    raw_product,
                    product.clone(),
                    app(
                        "ir_nat_mul_canonical_agrees_v1",
                        [Expr::nat_lit(word), power],
                    ),
                ],
            );
            let remainder_agreement = app(
                "ir_eq_cong",
                [
                    c("Nat"),
                    c("IRStepResult"),
                    Expr::lam(BinderInfo::Default, c("Nat"), value(Expr::bvar(0))),
                    wrap(width, product.clone()),
                    residue,
                    app(
                        "ir_nat_rem_canonical_positive_v1",
                        [product, Expr::nat_lit(maximum)],
                    ),
                ],
            );
            let closed = trans(
                raw.clone(),
                multiplied.clone(),
                expected.clone(),
                product_agreement,
                trans(
                    multiplied,
                    normalized,
                    expected.clone(),
                    remainder_agreement,
                    eq_primitive("Eq.refl", [c("IRStepResult"), expected.clone()]),
                ),
            );
            let operation = app(
                "ir_byte_shl_uint_canonical_v1",
                [
                    Expr::nat_lit(width),
                    Expr::nat_lit(word),
                    Expr::nat_lit(amount),
                    bound(word, u64::try_from(limit - u128::from(word) - 1).unwrap()),
                    bound(
                        amount,
                        u64::try_from(limit - u128::from(amount) - 1).unwrap(),
                    ),
                    bound(amount, width - amount - 1),
                ],
            );
            let actual = actual(width, word, amount);
            let proof = trans(actual.clone(), raw, expected.clone(), operation, closed);
            replay(
                &spec,
                format!("canonical_shl_ground_{width}_{index}"),
                actual,
                expected,
                proof,
                Some("ir_byte_shl_uint_canonical_v1"),
            );
        }
        let expected = app(
            "IRStepResult.fault",
            [app("IROutcome.ub", [c("IRFault.shift_oob")])],
        );
        let proof = eq_primitive("Eq.refl", [c("IRStepResult"), expected.clone()]);
        replay(
            &spec,
            format!("canonical_shl_range_fault_{width}"),
            actual(width, 7, width),
            expected,
            proof,
            None,
        );
    }
}
