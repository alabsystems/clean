// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Case builders for the heads whose telescope carries instances or universe
//! levels (`native_fold_review.rs`): the heterogeneous arithmetic short-cuts,
//! `HAppend`, `BEq.beq`, `Ord.compare`, `decide`, `ite`/`dite`, the
//! propositional `Decidable` combinators, `List.length` and `Array.size`.
//!
//! Every instance is one the ENVIRONMENT declares, spelled the way Clean's
//! prelude or Lean's `Init` spells it, and kept only when it has the class
//! type the head expects (checked in `LeanReference`); a head for which no
//! instance survives gets no case and stays unreviewed.

use super::cases::levels;
use super::reference::reference;
use super::{def_eq, fresh, Case, Val};
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

const SMALL: [u128; 6] = [0, 1, 2, 3, 7, 10];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn cl(s: &str, levels: &[Level]) -> Expr {
    Expr::const_(n(s), levels.to_vec())
}

fn one() -> Level {
    Level::succ(Level::zero())
}

/// Candidate instance terms, each `(term, …)` kept when every constant it
/// names is declared and its type is `class`.
fn instances(
    env: &Environment,
    tc: &TypeChecker<'_>,
    class: &Expr,
    candidates: Vec<(Vec<&str>, Expr)>,
) -> Vec<Expr> {
    candidates
        .into_iter()
        .filter(|(names, _)| names.iter().all(|s| env.get_const(&n(s)).is_some()))
        .filter_map(|(_, term)| {
            fresh(tc);
            let ty = tc.infer_type(&term).ok()?;
            def_eq(tc, &ty, class).then_some(term)
        })
        .collect()
}

/// `(proposition, a Decidable instance for it, its truth)`.
fn decided(env: &Environment) -> Vec<(Expr, Expr, bool)> {
    let mut out = vec![
        (
            c("True"),
            Expr::apps(c("Decidable.isTrue"), [c("True"), c("True.intro")]),
            true,
        ),
        (
            c("False"),
            Expr::apps(
                c("Decidable.isFalse"),
                [
                    c("False"),
                    Expr::lam(BinderInfo::Default, c("False"), Expr::bvar(0)),
                ],
            ),
            false,
        ),
    ];
    if env.get_const(&n("Nat.decEq")).is_some() {
        for (a, b) in [(3u64, 3u64), (3, 4)] {
            let prop = Expr::apps(
                cl("Eq", &[one()]),
                [c("Nat"), Expr::nat_lit(a), Expr::nat_lit(b)],
            );
            let inst = Expr::apps(c("Nat.decEq"), [Expr::nat_lit(a), Expr::nat_lit(b)]);
            out.push((prop, inst, a == b));
        }
    }
    out
}

fn case(head: &(Expr, Expr), args: Vec<Expr>, answer: Val) -> Case {
    Case {
        head: head.0.clone(),
        value: head.1.clone(),
        args,
        answer,
        deep: false,
    }
}

/// `Some(cases)` for a head built here, `None` for the generic walk.
pub(super) fn special_cases(
    env: &Environment,
    name: &Name,
    tc: &TypeChecker<'_>,
) -> Option<Result<Vec<Case>, String>> {
    let spelled = name.to_string();
    let nat = c("Nat");
    let hetero = |op: &str| -> Option<(&'static str, Vec<(Vec<&'static str>, Expr)>)> {
        Some(match op {
            "HAdd.hAdd" => (
                "Nat.add",
                vec![
                    (vec!["instHAddNatNatNat"], c("instHAddNatNatNat")),
                    (vec!["instHAddNat"], c("instHAddNat")),
                    (
                        vec!["instHAdd", "instAddNat"],
                        Expr::apps(
                            cl("instHAdd", &[Level::zero()]),
                            [c("Nat"), c("instAddNat")],
                        ),
                    ),
                ],
            ),
            "HSub.hSub" => (
                "Nat.sub",
                vec![
                    (vec!["instHSubNatNatNat"], c("instHSubNatNatNat")),
                    (
                        vec!["instHSub", "instSubNat"],
                        Expr::apps(
                            cl("instHSub", &[Level::zero()]),
                            [c("Nat"), c("instSubNat")],
                        ),
                    ),
                ],
            ),
            "HMul.hMul" => (
                "Nat.mul",
                vec![
                    (vec!["instHMulNatNatNat"], c("instHMulNatNatNat")),
                    (
                        vec!["instHMul", "instMulNat"],
                        Expr::apps(
                            cl("instHMul", &[Level::zero()]),
                            [c("Nat"), c("instMulNat")],
                        ),
                    ),
                ],
            ),
            "HDiv.hDiv" => (
                "Nat.div",
                vec![
                    (vec!["instHDivNatNatNat"], c("instHDivNatNatNat")),
                    (vec!["instHDivNat"], c("instHDivNat")),
                    (
                        vec!["instHDiv", "Nat.instDiv"],
                        Expr::apps(
                            cl("instHDiv", &[Level::zero()]),
                            [c("Nat"), c("Nat.instDiv")],
                        ),
                    ),
                ],
            ),
            "HMod.hMod" => (
                "Nat.mod",
                vec![
                    (vec!["instHModNatNatNat"], c("instHModNatNatNat")),
                    (vec!["instHModNat"], c("instHModNat")),
                    (
                        vec!["instHMod", "Nat.instMod"],
                        Expr::apps(
                            cl("instHMod", &[Level::zero()]),
                            [c("Nat"), c("Nat.instMod")],
                        ),
                    ),
                ],
            ),
            "HPow.hPow" => (
                "Nat.pow",
                vec![
                    (vec!["instHPowNatNatNat"], c("instHPowNatNatNat")),
                    (
                        vec!["instHPow", "instPowNat"],
                        Expr::apps(
                            cl("instHPow", &[Level::zero(), Level::zero()]),
                            [c("Nat"), c("Nat"), c("instPowNat")],
                        ),
                    ),
                ],
            ),
            _ => return None,
        })
    };
    if let Some((op, candidates)) = hetero(&spelled) {
        let head = levels(env, &spelled, Level::zero())?;
        let class_name = spelled.split('.').next().unwrap_or_default();
        let class = Expr::apps(
            cl(class_name, &[Level::zero(), Level::zero(), Level::zero()]),
            [nat.clone(), nat.clone(), nat.clone()],
        );
        let insts = instances(env, tc, &class, candidates);
        let mut out = Vec::new();
        for inst in &insts {
            for a in SMALL {
                for b in SMALL {
                    let Some(answer) = reference(op, &[Val::Nat(a), Val::Nat(b)]) else {
                        continue;
                    };
                    let args = vec![
                        nat.clone(),
                        nat.clone(),
                        nat.clone(),
                        inst.clone(),
                        Expr::nat_lit_u128(a),
                        Expr::nat_lit_u128(b),
                    ];
                    out.push(case(&head, args, answer));
                }
            }
        }
        return Some(Ok(out));
    }
    let head = |level: Level| levels(env, &spelled, level);
    Some(Ok(match spelled.as_str() {
        "HAppend.hAppend" => {
            let head = head(Level::zero())?;
            let s = c("String");
            let class = Expr::apps(
                cl("HAppend", &[Level::zero(), Level::zero(), Level::zero()]),
                [s.clone(), s.clone(), s.clone()],
            );
            let insts = instances(
                env,
                tc,
                &class,
                vec![
                    (vec!["instHAppendString"], c("instHAppendString")),
                    (
                        vec!["instHAppendStringStringString"],
                        c("instHAppendStringStringString"),
                    ),
                    (
                        vec!["instHAppendOfAppend", "instAppendString"],
                        Expr::apps(
                            cl("instHAppendOfAppend", &[Level::zero()]),
                            [s.clone(), c("instAppendString")],
                        ),
                    ),
                ],
            );
            let words = ["", "a", "bc", "héllo"];
            let mut out = Vec::new();
            for inst in &insts {
                for x in words {
                    for y in words {
                        let args = vec![
                            s.clone(),
                            s.clone(),
                            s.clone(),
                            inst.clone(),
                            Expr::str_lit(x),
                            Expr::str_lit(y),
                        ];
                        out.push(case(&head, args, Val::Str(format!("{x}{y}"))));
                    }
                }
            }
            out
        }
        "BEq.beq" => {
            let head = head(Level::zero())?;
            let mut out = Vec::new();
            for (ty, inst_name, vals) in [
                (
                    "Nat",
                    "instBEqNat",
                    vec![(Expr::nat_lit(3), 3u32), (Expr::nat_lit(4), 4)],
                ),
                (
                    "Bool",
                    "instBEqBool",
                    vec![(c("Bool.true"), 1), (c("Bool.false"), 0)],
                ),
                (
                    "Char",
                    "instBEqChar",
                    vec![
                        (Expr::app(c("Char.ofNat"), Expr::nat_lit(65)), 65),
                        (Expr::app(c("Char.ofNat"), Expr::nat_lit(97)), 97),
                    ],
                ),
                (
                    "String",
                    "instBEqString",
                    vec![(Expr::str_lit("ab"), 1), (Expr::str_lit("abc"), 2)],
                ),
                (
                    "Int",
                    "instBEqInt",
                    vec![
                        (Expr::app(c("Int.ofNat"), Expr::nat_lit(2)), 2),
                        (Expr::app(c("Int.negSucc"), Expr::nat_lit(1)), 3),
                    ],
                ),
            ] {
                let class = Expr::app(cl("BEq", &[Level::zero()]), c(ty));
                let mut candidates = vec![(vec![inst_name], c(inst_name))];
                let deq = format!("instDecidableEq{ty}");
                if env.get_const(&n(&deq)).is_some() {
                    candidates.push((
                        vec!["instBEqOfDecidableEq"],
                        Expr::apps(
                            cl("instBEqOfDecidableEq", &[Level::zero()]),
                            [c(ty), c(&deq)],
                        ),
                    ));
                }
                for inst in instances(env, tc, &class, candidates) {
                    for (x, xv) in &vals {
                        for (y, yv) in &vals {
                            let args = vec![c(ty), inst.clone(), x.clone(), y.clone()];
                            out.push(case(&head, args, Val::Bool(xv == yv)));
                        }
                    }
                }
            }
            out
        }
        "Ord.compare" => {
            let head = head(Level::zero())?;
            let class = Expr::app(cl("Ord", &[Level::zero()]), nat.clone());
            let insts = instances(env, tc, &class, vec![(vec!["instOrdNat"], c("instOrdNat"))]);
            let mut out = Vec::new();
            for inst in &insts {
                for a in SMALL {
                    for b in SMALL {
                        let args = vec![
                            nat.clone(),
                            inst.clone(),
                            Expr::nat_lit_u128(a),
                            Expr::nat_lit_u128(b),
                        ];
                        out.push(case(&head, args, Val::Ordering(a.cmp(&b))));
                    }
                }
            }
            out
        }
        "Decidable.decide" | "decide" => {
            let head = head(Level::zero())?;
            decided(env)
                .into_iter()
                .map(|(p, inst, truth)| case(&head, vec![p, inst], Val::Bool(truth)))
                .collect()
        }
        "ite" | "dite" => {
            let head = head(one())?;
            let dependent = spelled == "dite";
            decided(env)
                .into_iter()
                .map(|(p, inst, truth)| {
                    let branch = |v: u64, dom: Expr| {
                        if dependent {
                            Expr::lam(BinderInfo::Default, dom, Expr::nat_lit(v))
                        } else {
                            Expr::nat_lit(v)
                        }
                    };
                    let not_p = Expr::app(c("Not"), p.clone());
                    let args = vec![nat.clone(), p.clone(), inst, branch(1, p), branch(2, not_p)];
                    case(&head, args, Val::Nat(if truth { 1 } else { 2 }))
                })
                .collect()
        }
        "instDecidableAnd" | "instDecidableOr" => {
            let head = head(Level::zero())?;
            let props = decided(env);
            let mut out = Vec::new();
            for (p, dp, tp) in props.iter().take(2) {
                for (q, dq, tq) in props.iter().take(2) {
                    let truth = if spelled == "instDecidableAnd" {
                        *tp && *tq
                    } else {
                        *tp || *tq
                    };
                    let args = vec![p.clone(), q.clone(), dp.clone(), dq.clone()];
                    out.push(case(&head, args, Val::Decided(truth)));
                }
            }
            out
        }
        "instDecidableNot" => {
            let head = head(Level::zero())?;
            decided(env)
                .into_iter()
                .map(|(p, dp, tp)| case(&head, vec![p, dp], Val::Decided(!tp)))
                .collect()
        }
        "List.length" | "Array.size" => {
            let head = head(Level::zero())?;
            let array = spelled == "Array.size";
            let mut out = Vec::new();
            for len in [0u64, 1, 3, 7] {
                let mut list = Expr::app(cl("List.nil", &[Level::zero()]), nat.clone());
                for i in 0..len {
                    list = Expr::apps(
                        cl("List.cons", &[Level::zero()]),
                        [nat.clone(), Expr::nat_lit(i), list],
                    );
                }
                let arg = if array {
                    Expr::apps(cl("Array.mk", &[Level::zero()]), [nat.clone(), list])
                } else {
                    list
                };
                out.push(case(
                    &head,
                    vec![nat.clone(), arg],
                    Val::Nat(u128::from(len)),
                ));
            }
            out
        }
        _ => return None,
    }))
}
