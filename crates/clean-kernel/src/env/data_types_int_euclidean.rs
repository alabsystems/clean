// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked Euclidean and floor integer division, as used by Lean's `/` and `%`
//! notation (`ediv`/`emod`) and Lean's `Int.fdiv`/`Int.fmod`.
//!
//! These constructor equations mirror Lean v4.30.0-rc2,
//! `Init/Data/Int/DivMod/Basic.lean`, whose `ediv`, `emod`, `fdiv` and `fmod`
//! bodies are Lean 4.8.0's (`Init/Data/Int/DivMod.lean`) case for case. The
//! legacy explicit `Int.div` and `Int.mod` heads retain their separate
//! truncating semantics. There is no native reducer here: ordinary delta/iota
//! reduction checks the definitions, including negative and zero divisors.
//!
//! `subNatNat` inside `emod`/`fmod` is spelled as Lean's own one-step body,
//! `match n - m with | 0 => ofNat (m - n) | succ k => -[k+1]`, not as a call
//! of the prelude's `Int.subNatNat`, which recurses on its second argument one
//! decrement at a time: `(-2^63 : Int) % 2^64` took `2^63` unfoldings through
//! it (R168).

use super::data_types_arithmetic::int_binop_by_sign_cases;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn succ(value: Expr) -> Expr {
    Expr::app(constant("Nat.succ"), value)
}

fn of_nat(value: Expr) -> Expr {
    Expr::app(constant("Int.ofNat"), value)
}

/// The negative-dividend, nonnegative-divisor branch: zero is separate,
/// while division by `succ k` returns `negSucc (m / succ k)`.
fn negative_ediv_of_nat(b: &mut EnvDeclBuilder, m: Expr, n: Expr) -> Expr {
    let nat = constant("Nat");
    let int = constant("Int");
    let (k_id, k) = b.fresh_local(nat.clone());
    let (ih_id, _) = b.fresh_local(int.clone());
    let quotient = Expr::apps(constant("Nat.div"), [m, succ(k)]);
    let negative = Expr::app(constant("Int.negSucc"), quotient);
    let step = b.mk_lam(ih_id, BinderInfo::Default, int.clone(), negative);
    let step = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), step);
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, nat, int),
            of_nat(constant("Nat.zero")),
            step,
            n,
        ],
    )
}

/// `Nat.rec (λ _ => Int) zero (λ k _ => succ_case k) scrutinee`: a
/// zero/successor split of a `Nat`, one ι step on a literal.
fn nat_cases(
    b: &mut EnvDeclBuilder,
    scrutinee: Expr,
    zero: Expr,
    succ_case: impl FnOnce(&mut EnvDeclBuilder, Expr) -> Expr,
) -> Expr {
    let nat = constant("Nat");
    let int = constant("Int");
    let (k_id, k) = b.fresh_local(nat.clone());
    let (ih_id, _) = b.fresh_local(int.clone());
    let body = succ_case(b, k);
    let step = b.mk_lam(ih_id, BinderInfo::Default, int.clone(), body);
    let step = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), step);
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, nat, int),
            zero,
            step,
            scrutinee,
        ],
    )
}

/// Lean's `Int.subNatNat m n`: `match n - m with | 0 => ofNat (m - n) |
/// succ k => -[k+1]`.
fn sub_nat_nat(b: &mut EnvDeclBuilder, m: Expr, n: Expr) -> Expr {
    let sub = |x, y| Expr::apps(constant("Nat.sub"), [x, y]);
    nat_cases(b, sub(n.clone(), m.clone()), of_nat(sub(m, n)), |_, k| {
        Expr::app(constant("Int.negSucc"), k)
    })
}

fn neg_of_nat(value: Expr) -> Expr {
    Expr::app(constant("Int.neg"), of_nat(value))
}

impl Environment {
    /// Called after `init_int_arith` has checked Int/Nat arithmetic. Import
    /// mode skips that entire cluster, leaving genuine imported definitions
    /// untouched. Every declaration here passes normal `add_decl` checking.
    pub(super) fn init_int_euclidean(&mut self) -> Result<(), EnvError> {
        let ediv = int_binop_by_sign_cases(|b, case, m, n| {
            let div = |a, b| Expr::apps(constant("Nat.div"), [a, b]);
            match case {
                0 => of_nat(div(m, n)),
                1 => Expr::app(constant("Int.neg"), of_nat(div(m, succ(n)))),
                2 => negative_ediv_of_nat(b, m, n),
                _ => of_nat(succ(div(m, succ(n)))),
            }
        });
        let emod = int_binop_by_sign_cases(|b, case, m, n| {
            let divisor = if case % 2 == 0 { n } else { succ(n) };
            let remainder = Expr::apps(constant("Nat.mod"), [m, divisor.clone()]);
            if case < 2 {
                of_nat(remainder)
            } else {
                sub_nat_nat(b, divisor, succ(remainder))
            }
        });
        // def fdiv : Int → Int → Int
        //   | 0,       _       => 0
        //   | ofNat m, ofNat n => ofNat (m / n)
        //   | ofNat (succ m), -[n+1] => -[m / succ n +1]
        //   | -[_+1],  0       => 0
        //   | -[m+1],  succ n  => -[m / succ n +1]
        //   | -[m+1],  -[n+1]  => ofNat (succ m / succ n)
        let div = |a, b| Expr::apps(constant("Nat.div"), [a, b]);
        let rem = |a, b| Expr::apps(constant("Nat.mod"), [a, b]);
        let zero = || of_nat(constant("Nat.zero"));
        let fdiv = int_binop_by_sign_cases(|b, case, m, n| match case {
            0 => of_nat(div(m, n)),
            1 => nat_cases(b, m, zero(), |_, k| {
                Expr::app(constant("Int.negSucc"), div(k, succ(n)))
            }),
            2 => nat_cases(b, n, zero(), |_, k| {
                Expr::app(constant("Int.negSucc"), div(m, succ(k)))
            }),
            _ => of_nat(div(succ(m), succ(n))),
        });
        // def fmod : Int → Int → Int
        //   | 0,       _       => 0
        //   | ofNat m, ofNat n => ofNat (m % n)
        //   | ofNat (succ m),  -[n+1]  => subNatNat (m % succ n) n
        //   | -[m+1],  ofNat n => subNatNat n (succ (m % n))
        //   | -[m+1],  -[n+1]  => -ofNat (succ m % succ n)
        let fmod = int_binop_by_sign_cases(|b, case, m, n| match case {
            0 => of_nat(rem(m, n)),
            1 => nat_cases(b, m, zero(), |b, k| {
                sub_nat_nat(b, rem(k, succ(n.clone())), n)
            }),
            2 => sub_nat_nat(b, n.clone(), succ(rem(m, n))),
            _ => neg_of_nat(rem(succ(m), succ(n))),
        });
        let int = constant("Int");
        // Pinned Lean writes both domains as `@& Int`; preserve that borrowed
        // metadata as well as the logical type in these checked declarations.
        let borrowed_int = super::lean_nat_spelling::LeanNat::borrowed(int.clone());
        let type_ = Expr::pi(
            BinderInfo::Default,
            borrowed_int.clone(),
            Expr::pi(BinderInfo::Default, borrowed_int, int),
        );
        for (head, value) in [("Int.ediv", ediv), ("Int.emod", emod)] {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(head),
                level_params: vec![],
                type_: type_.clone(),
                value,
                is_reducible: true,
            })?;
        }
        // Lean writes `fdiv`/`fmod` over plain `Int` (no `@&`, no extern).
        let plain_type = Expr::pi(
            BinderInfo::Default,
            constant("Int"),
            Expr::pi(BinderInfo::Default, constant("Int"), constant("Int")),
        );
        for (head, value) in [("Int.fdiv", fdiv), ("Int.fmod", fmod)] {
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(head),
                level_params: vec![],
                type_: plain_type.clone(),
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConstantKind, ExprKind, MDataValue, TypeChecker};

    fn int(value: i64) -> Expr {
        if value < 0 {
            Expr::app(
                constant("Int.negSucc"),
                Expr::nat_lit(value.unsigned_abs() - 1),
            )
        } else {
            of_nat(Expr::nat_lit(value as u64))
        }
    }

    /// Lean's `Int.fdiv`/`Int.fmod` on machine integers: floor rounding,
    /// `fdiv a 0 = 0`, `fmod a 0 = a`.
    fn floor_div_mod(a: i64, b: i64) -> (i64, i64) {
        if b == 0 {
            return (0, a);
        }
        let mut q = a / b;
        if a % b != 0 && ((a < 0) != (b < 0)) {
            q -= 1;
        }
        (q, a - b * q)
    }

    #[test]
    fn checked_floor_definitions_match_lean_on_every_sign_pair() {
        // A zero dividend over a negative divisor takes Lean's `0, _ => 0`
        // case: a body without the zero/successor split on the dividend
        // gives `fdiv 0 (-2) = -1`, and one returning the divisor's payload
        // from that zero branch gives `fmod 0 (-2) = 1` (R168's review
        // mutants K7, K8).
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        for head in ["Int.fdiv", "Int.fmod"] {
            let name = Name::from_string(head);
            let info = env.get_const(&name).expect("checked definition exists");
            assert_eq!(info.kind, ConstantKind::Definition);
            assert!(env.native_fold_verdict(&name).is_err(), "no trusted fold");
            assert!(env
                .axiom_deps(&name)
                .expect("definition closure")
                .is_empty());
            tc.check_type(info.value.as_ref().unwrap(), &info.type_)
                .unwrap();
        }
        let mut wrong = Vec::new();
        for a in [-7_i64, -6, -2, -1, 0, 1, 2, 6, 7] {
            for b in [-3_i64, -2, -1, 0, 1, 2, 3, 256] {
                let (q, r) = floor_div_mod(a, b);
                for (head, expected) in [("Int.fdiv", q), ("Int.fmod", r)] {
                    let expression = Expr::apps(constant(head), [int(a), int(b)]);
                    if !tc.is_def_eq(&expression, &int(expected)) {
                        wrong.push(format!("{head} {a} {b} is not {expected}"));
                    }
                    for off in [-1, 1] {
                        if tc.is_def_eq(&expression, &int(expected + off)) {
                            wrong.push(format!("{head} {a} {b} = {}", expected + off));
                        }
                    }
                }
            }
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    }

    #[test]
    fn checked_euclidean_definitions_compute_without_a_native_fold_or_axioms() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        for head in ["Int.ediv", "Int.emod"] {
            let name = Name::from_string(head);
            let info = env.get_const(&name).expect("checked definition exists");
            assert_eq!(info.kind, ConstantKind::Definition);
            let mut result = &info.type_;
            for argument in 0..2 {
                let ExprKind::Pi(binder, domain, body) = result.kind() else {
                    panic!("{head}: missing argument {argument}");
                };
                assert_eq!(binder.info, BinderInfo::Default);
                assert_eq!(binder.mult, crate::Multiplicity::Many);
                let ExprKind::MData(metadata, ty) = domain.kind() else {
                    panic!("{head}: argument {argument} lost Lean's @& annotation");
                };
                assert_eq!(
                    metadata.as_slice(),
                    &[(Name::from_string("borrowed"), MDataValue::Bool(true))]
                );
                assert_eq!(ty.as_ref(), &constant("Int"));
                result = body;
            }
            assert_eq!(result, &constant("Int"), "{head}: unannotated Int result");
            assert!(
                env.native_fold_verdict(&name).is_err(),
                "no new trusted fold"
            );
            assert!(env
                .axiom_deps(&name)
                .expect("definition closure")
                .is_empty());
            tc.check_type(info.value.as_ref().unwrap(), &info.type_)
                .unwrap();
            let application = Expr::apps(constant(head), [int(-7), int(2)]);
            tc.check_type(&application, &constant("Int")).unwrap();
            assert!(tc.check_type(&application, &constant("Nat")).is_err());
        }
        for a in [-7_i64, -6, -1, 0, 6, 7] {
            for b in [-3_i64, -2, 0, 2, 3, 256] {
                let q = if b == 0 { 0 } else { a.div_euclid(b) };
                let r = if b == 0 { a } else { a.rem_euclid(b) };
                for (head, expected) in [("Int.ediv", q), ("Int.emod", r)] {
                    let expression = Expr::apps(constant(head), [int(a), int(b)]);
                    assert!(tc.is_def_eq(&expression, &int(expected)), "{head} {a} {b}");
                    assert!(
                        !tc.is_def_eq(&expression, &int(expected + 1)),
                        "wrong answer for {head} {a} {b}"
                    );
                }
            }
        }
        // The same inputs distinguish the preserved direct T-rounding heads.
        for (head, expected) in [("Int.div", -3), ("Int.mod", -1)] {
            assert!(tc.is_def_eq(
                &Expr::apps(constant(head), [int(-7), int(2)]),
                &int(expected),
            ));
        }
    }
}
