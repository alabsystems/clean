// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The REVIEW behind every `fold` row of `native_fold_canon.tsv`
//! (`docs/issues/2026-09-26-kernel-native-fold-by-name.md`, section
//! "2026-09-28 — every world pins only reviewed folds"). Test builds only:
//! this crate's unit tests, and downstream test builds through the
//! `test-fixtures` feature their `[dev-dependencies]` enable.
//!
//! A pinned digest used to switch on every rule keyed on its name. Over Lean
//! 4.30's `Init` that turned on `String.drop`'s reducer, which returns a
//! `String` where Lean's definition returns a `String.Slice` that remembers the
//! string it was cut from, so `String.drop "abc" 1 = String.drop "xbc" 1`
//! checked by `rfl` in the default theory. A pin now carries a ROLE
//! (`native_fold_authority::FoldRole`): `definition` says only that the closure
//! is a known definition (it may be a boundary of another closure, or a
//! literal carrier a reviewed reducer reads), and `fold` additionally lets the
//! name's own rules fire. A row is `fold` only when [`review`] passes it.
//!
//! The review is the Lean 4.8.0 battery's three-way check, generalized to
//! every head a world pins. On literal inputs that include edge cases
//! (`native_fold_review_cases.rs`), for every case the fold fires on:
//!
//! - **T** the fold's result has the head application's type, in
//!   `KernelTheory::LeanReference` (Lean's kernel exactly);
//! - **I** the fold's result equals the INDEPENDENT answer
//!   (`native_fold_review_reference.rs`, plain Rust), definitionally in
//!   `LeanReference`;
//! - **D** the head's own DEFINITION, applied to the same arguments with the
//!   fold bypassed (the head replaced by its δ-unfolding; `LeanReference`
//!   runs no Clean reducer), reaches the same answer — skipped only on `deep`
//!   inputs δι cannot reach within the budget;
//! - **A** for a `Decidable` result, the fold's term and the definition's are
//!   definitionally equal (the witness proves the right proposition);
//! - **K** for a kernel fold (`reduce_nat`, `reduce_int`), the kernel's own
//!   whnf of the head application reaches the answer. One of the fourteen
//!   heads Lean's `reduce_nat` has is folded and compared in `LeanReference`.
//!   A fold Lean's kernel lacks (`Nat.pred`, the `Int` heads) does not fire
//!   there (`tc/fold_admission.rs`), so it is folded by a whnf in
//!   `KernelTheory::Extended` and that result is compared with the answer in
//!   `LeanReference`;
//! - **P** (ordinary runs only) the production checker (`TypeChecker::new`,
//!   the environment's own theory, the compiled table) proves
//!   `head args = answer`.
//!
//! A head passes when the fold fired at least once and no leg failed. A head
//! the battery cannot exercise (no case generator, no fold of its own) is not
//! reviewed, and is never `fold`.

use crate::env::{Environment, KernelTheory};
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

#[path = "native_fold_review_cases.rs"]
mod cases;
#[path = "native_fold_review_literal.rs"]
mod literal;
#[path = "native_fold_review_reference.rs"]
mod reference;
#[path = "native_fold_review_roles.rs"]
mod roles;
#[path = "native_fold_review_special.rs"]
mod special;

pub use roles::{review_world, RowReview};

/// Per-check heartbeat budget of every reference-theory leg.
pub const REVIEW_HEARTBEATS: u32 = 2_000_000;

/// The kernel's own name-keyed folds outside the native-reducer registry that
/// the K leg exercises (`tc/reduction/nat.rs`, `tc/reduction/int.rs`).
const KERNEL_FOLD_HEADS: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.pow",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Nat.pred",
    "Int.add",
    "Int.sub",
    "Int.mul",
];

/// One component of a `Lean.Name` value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameComp {
    /// `Lean.Name.str`.
    Str(String),
    /// `Lean.Name.num`.
    Num(u64),
}

/// A value the independent reference computes and the review can spell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Val {
    /// A natural number.
    Nat(u128),
    /// A boolean.
    Bool(bool),
    /// An integer.
    Int(i128),
    /// `UIntN` (width, value).
    UInt(u64, u128),
    /// `IntN` (width, value).
    SInt(u64, i128),
    /// `BitVec w` (width, value).
    BitVec(u64, u128),
    /// A Unicode scalar value.
    Char(u32),
    /// A string.
    Str(String),
    /// A `Decidable p` whose proposition has this truth value.
    Decided(bool),
    /// A `Lean.Name`.
    Name(Vec<NameComp>),
    /// An `Ordering`.
    Ordering(std::cmp::Ordering),
    /// A proposition (`True`/`False`), used as an argument only.
    Prop(bool),
    /// An argument whose value no reference reads (a type, an instance).
    Opaque,
}

/// One input of a head: the head (with its universe levels), its δ-unfolding
/// at those levels, the arguments and the independent answer.
#[derive(Debug, Clone)]
pub(crate) struct Case {
    pub(crate) head: Expr,
    pub(crate) value: Expr,
    pub(crate) args: Vec<Expr>,
    pub(crate) answer: Val,
    /// δι of the definition cannot reach this input within the budget.
    pub(crate) deep: bool,
}

/// What the review found for one head.
#[derive(Debug, Clone, Default)]
pub struct Review {
    /// Cases built.
    pub cases: usize,
    /// Cases on which the fold fired (reducer or kernel fold).
    pub fired: usize,
    /// Legs that failed, each with the input and the reason.
    pub failures: Vec<String>,
    /// Cases with no independent answer (they run leg T only).
    pub unanswered: usize,
    /// Why the head could not be reviewed at all.
    pub unreviewable: Option<String>,
}

impl Review {
    /// Reviewed: the fold fired at least once and every leg held.
    #[must_use]
    pub fn passed(&self) -> bool {
        self.unreviewable.is_none() && self.fired > 0 && self.failures.is_empty()
    }

    fn unreviewable(why: impl Into<String>) -> Self {
        Self {
            unreviewable: Some(why.into()),
            ..Self::default()
        }
    }
}

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

/// Spell `val` as a closed term of its type in `env`; `None` when the carrier
/// it needs is absent or the value has no spelling (`Decided`, `Opaque`).
pub(crate) fn spell(env: &Environment, val: &Val) -> Option<Expr> {
    let has = |s: &str| env.get_const(&Name::from_string(s)).is_some();
    let int = |i: i128| -> Option<Expr> {
        Some(if i >= 0 {
            Expr::app(c("Int.ofNat"), Expr::nat_lit_u128(u128::try_from(i).ok()?))
        } else {
            Expr::app(
                c("Int.negSucc"),
                Expr::nat_lit_u128(u128::try_from(-(i + 1)).ok()?),
            )
        })
    };
    Some(match val {
        Val::Nat(n) => Expr::nat_lit_u128(*n),
        Val::Bool(b) => c(if *b { "Bool.true" } else { "Bool.false" }),
        Val::Int(i) => int(*i)?,
        Val::UInt(bits, v) => {
            let of_nat = format!("UInt{bits}.ofNat");
            has(&of_nat).then(|| Expr::app(c(&of_nat), Expr::nat_lit_u128(*v)))?
        }
        Val::SInt(bits, v) => {
            let of_int = format!("Int{bits}.ofInt");
            has(&of_int).then_some(())?;
            Expr::app(c(&of_int), int(*v)?)
        }
        Val::BitVec(w, v) => Expr::apps(
            c("BitVec.ofNat"),
            [Expr::nat_lit(*w), Expr::nat_lit_u128(*v)],
        ),
        Val::Char(ch) => Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(*ch))),
        Val::Str(s) => Expr::str_lit(s),
        Val::Ordering(o) => c(match o {
            std::cmp::Ordering::Less => "Ordering.lt",
            std::cmp::Ordering::Equal => "Ordering.eq",
            std::cmp::Ordering::Greater => "Ordering.gt",
        }),
        Val::Name(comps) => {
            let mut out = c("Lean.Name.anonymous");
            for comp in comps {
                out = match comp {
                    NameComp::Str(s) => Expr::apps(c("Lean.Name.str"), [out, Expr::str_lit(s)]),
                    NameComp::Num(n) => Expr::apps(c("Lean.Name.num"), [out, Expr::nat_lit(*n)]),
                };
            }
            out
        }
        Val::Prop(b) => c(if *b { "True" } else { "False" }),
        Val::Decided(_) | Val::Opaque => return None,
    })
}

/// A checker in `theory` with the review's budget.
fn checker(env: &Environment, theory: Option<KernelTheory>) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(env);
    if let Some(theory) = theory {
        tc.set_kernel_theory(theory);
    }
    tc.set_heartbeat_limit(REVIEW_HEARTBEATS);
    tc
}

fn fresh(tc: &TypeChecker<'_>) {
    tc.reset_local_context();
    tc.reset_heartbeat();
}

fn def_eq(tc: &TypeChecker<'_>, a: &Expr, b: &Expr) -> bool {
    fresh(tc);
    tc.is_def_eq(a, b)
}

/// `e` reduces (whnf in `tc`) to `Decidable.isTrue …` when `truth`, else to
/// `Decidable.isFalse …`.
fn decides(tc: &TypeChecker<'_>, e: &Expr, truth: bool) -> bool {
    fresh(tc);
    let whnf = tc.whnf(e);
    let want = if truth {
        "Decidable.isTrue"
    } else {
        "Decidable.isFalse"
    };
    matches!(whnf.get_app_fn().kind(), ExprKind::Const(k, _) if k.to_string() == want)
}

/// `e` equals the answer in `tc`: its spelling definitionally, or for a
/// `Decidable` answer, the constructor the truth demands.
fn reaches(env: &Environment, tc: &TypeChecker<'_>, e: &Expr, answer: &Val) -> Result<(), String> {
    match answer {
        Val::Decided(truth) => decides(tc, e, *truth)
            .then_some(())
            .ok_or_else(|| format!("does not decide {truth}")),
        other => {
            let spelled = spell(env, other).ok_or_else(|| format!("no spelling for {other:?}"))?;
            def_eq(tc, e, &spelled)
                .then_some(())
                .ok_or_else(|| format!("is not {other:?}"))
        }
    }
}

/// In an ordinary (non-re-pin) run, a `fold` row must actually fire under the
/// compiled table: its fold verdict is `Ok` (its closure and every boundary
/// admitted), and, when it has a registered reducer, every constant that
/// reducer recognizes in its arguments is a known definition. `Err` names what
/// blocks it.
pub fn fold_row_fires(env: &Environment, name: &Name) -> Result<(), String> {
    env.native_fold_verdict(name)
        .map_err(|e| format!("fold verdict {e:?}"))?;
    if env.get_native_reducer(name).is_some() {
        for r in crate::env::recognized_argument_names(name) {
            if env.get_const(r).is_some() && !env.native_fold_definition_admitted(r) {
                return Err(format!(
                    "recognized argument `{r}` is not a known definition: {:?}",
                    env.native_fold_definition_verdict(r)
                ));
            }
        }
    }
    Ok(())
}

/// The actual argument-name dependencies of a registered reducer. Canonical
/// batteries use this same registry mapping to retain definition-only rows;
/// callers must include only names present in their measured environment.
/// This exposes metadata to test builds; it grants no fold permission.
#[must_use]
pub fn recognized_arguments(env: &Environment, name: &Name) -> &'static [Name] {
    if env.get_native_reducer(name).is_some() {
        crate::env::recognized_argument_names(name)
    } else {
        &[]
    }
}

/// Whether the reference theory reads `arg` as the value the independent
/// reference gives it: a `Nat` literal; a string literal whose expansion is
/// admitted (it is definitionally `String.ofList` of its characters); a type,
/// a proposition or a proof; otherwise a term whose whnf is a constructor
/// application or a λ.
fn interpretable(env: &Environment, tc: &TypeChecker<'_>, arg: &Expr) -> bool {
    use crate::expr::Literal;
    match arg.kind() {
        ExprKind::Lit(Literal::Nat(_)) => return true,
        ExprKind::Lit(Literal::String(s)) => {
            return literal::expansion_admitted(env, tc, s);
        }
        _ => {}
    }
    fresh(tc);
    let Ok(ty) = tc.infer_type(arg) else {
        return false;
    };
    fresh(tc);
    let ty_whnf = tc.whnf(&ty);
    if matches!(ty_whnf.kind(), ExprKind::Sort(_)) {
        return true;
    }
    fresh(tc);
    if let Ok(sort) = tc.infer_type(&ty) {
        fresh(tc);
        if matches!(tc.whnf(&sort).kind(), ExprKind::Sort(l) if l.is_zero()) {
            return true;
        }
    }
    fresh(tc);
    let whnf = tc.whnf(arg);
    if matches!(whnf.kind(), ExprKind::Lam(..) | ExprKind::Lit(_)) {
        return true;
    }
    matches!(whnf.get_app_fn().kind(), ExprKind::Const(k, _) if env.get_constructor(k).is_some())
}

/// Review the fold keyed on `name` in `env` (module docs). `production`
/// adds the P leg; a re-pin passes `false`, since the compiled table is the
/// one being replaced.
#[must_use]
pub fn review(env: &Environment, name: &Name, production: bool) -> Review {
    let spelled = name.to_string();
    if literal::is_literal_key(&spelled) {
        return literal::review_literal(env);
    }
    let reducer = env.get_native_reducer(name);
    let kernel = KERNEL_FOLD_HEADS.contains(&spelled.as_str());
    if reducer.is_none() && !kernel {
        return Review::unreviewable("no fold of its own (a carrier or an instance)");
    }
    let reference = checker(env, Some(KernelTheory::LeanReference));
    let cases = match cases::cases_for(env, name, &reference) {
        Ok(cases) if !cases.is_empty() => cases,
        Ok(_) => return Review::unreviewable("no case could be built"),
        Err(why) => return Review::unreviewable(why),
    };
    // The theory a Clean-only kernel fold fires in (the K leg).
    let folding = (kernel && !Environment::is_lean_kernel_nat_extension(name))
        .then(|| checker(env, Some(KernelTheory::Extended)));
    let prod = production.then(|| checker(env, None));
    let mut out = Review {
        cases: cases.len(),
        ..Review::default()
    };
    for case in &cases {
        let term = Expr::apps(case.head.clone(), case.args.iter().cloned());
        // An input the environment cannot type, or cannot INTERPRET (a
        // carrier that does not reduce to a constructor here, a string literal
        // whose expansion is not admitted here), is the builder's problem, not
        // the fold's: it carries no evidence either way. Measured: the
        // specification declares no reducible `Char.ofNat`, so a `Char` input
        // there is stuck and every definition leg over it failed.
        fresh(&reference);
        if reference.infer_type(&term).is_err()
            || !case.args.iter().all(|a| interpretable(env, &reference, a))
        {
            continue;
        }
        let mut fired = false;
        let mut failures: Vec<(&str, String)> = Vec::new();
        let answered = !matches!(case.answer, Val::Opaque);
        if let Some(reducer) = reducer {
            let raw: Vec<&Expr> = case.args.iter().collect();
            let result = reducer(&raw).or_else(|| {
                fresh(&reference);
                let whnf: Vec<Expr> = case.args.iter().map(|a| reference.whnf(a)).collect();
                reducer(&whnf.iter().collect::<Vec<_>>())
            });
            if let Some(result) = result {
                fired = true;
                // T: the result has the head application's type.
                fresh(&reference);
                let head_ty = reference.infer_type(&term);
                fresh(&reference);
                let result_ty = reference.infer_type(&result);
                match (head_ty, result_ty) {
                    (Ok(t), Ok(r)) if def_eq(&reference, &t, &r) => {}
                    (Ok(t), Ok(r)) => {
                        failures.push(("T", format!("result type {r:?}, head type {t:?}")));
                    }
                    (t, r) => failures.push(("T", format!("ill-typed: head {t:?}, result {r:?}"))),
                }
                // I: the result is the independent answer.
                if !answered {
                    // Leg T alone: see `native_fold_review_cases.rs`.
                } else if let Err(why) = reaches(env, &reference, &result, &case.answer) {
                    failures.push(("I", format!("the fold's {result:?} {why}")));
                }
                // A: a Decidable result is the definition's own term.
                if matches!(case.answer, Val::Decided(_)) && !case.deep {
                    let unfolded = Expr::apps(case.value.clone(), case.args.iter().cloned());
                    if !def_eq(&reference, &unfolded, &result) {
                        failures.push((
                            "A",
                            format!("the fold's witness {result:?} is not the definition's"),
                        ));
                    }
                }
            }
        }
        if !answered {
            out.unanswered += 1;
            for (leg, why) in failures {
                let args: String = format!("{:?}", case.args).chars().take(240).collect();
                out.failures.push(format!(
                    "{leg} {spelled} {args}: {}",
                    why.chars().take(400).collect::<String>()
                ));
            }
            continue;
        }
        if kernel {
            // K: the kernel's own fold reaches the answer, judged in Lean's
            // theory. A fold Lean's kernel lacks is first run where it fires.
            fired = true;
            let folded = folding.as_ref().map(|extended| {
                fresh(extended);
                extended.whnf(&term)
            });
            if let Err(why) = reaches(
                env,
                &reference,
                folded.as_ref().unwrap_or(&term),
                &case.answer,
            ) {
                failures.push(("K", format!("the kernel fold {why}")));
            }
        }
        if !fired {
            continue;
        }
        out.fired += 1;
        // D: the definition, fold bypassed, reaches the same answer.
        if !case.deep {
            let unfolded = Expr::apps(case.value.clone(), case.args.iter().cloned());
            if let Err(why) = reaches(env, &reference, &unfolded, &case.answer) {
                failures.push(("D", format!("the definition {why}")));
            }
        }
        // P: the production checker proves `head args = answer` (not on a
        // deep input, where a fold the table keeps off leaves δι the work).
        if let (Some(prod), false) = (&prod, case.deep) {
            if let Err(why) = reaches(env, prod, &term, &case.answer) {
                failures.push(("P", format!("production {why}")));
            }
        }
        for (leg, why) in failures {
            let args: String = format!("{:?}", case.args).chars().take(240).collect();
            let why: String = why.chars().take(400).collect();
            out.failures.push(format!("{leg} {spelled} {args}: {why}"));
        }
    }
    out
}
