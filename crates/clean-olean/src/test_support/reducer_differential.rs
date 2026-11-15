// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The differential battery behind rule 0 of the Lean kernel-theory profile
//! (`clean_kernel::env::kernel_theory`, `LEAN_PROFILE_DIFFERENTIAL_REDUCERS`).
//!
//! A native reducer may fire in [`KernelTheory::Lean`] only when it computes
//! what Lean's kernel computes by δι from the head's own definition. For a
//! head `h` and a battery of literal argument lists `a`, this fires the
//! registered reducer on `h a` and requires, in [`KernelTheory::LeanReference`]
//! (Lean's kernel exactly: its `Nat` literal extensions and no Clean reducer):
//!
//! 1. `h a` to be well typed, and the result `r` to be well typed at a type
//!    definitionally equal to it — `String.drop` returns a `String` literal
//!    where Lean 4.30's returns a `String.Slice`, and fails here;
//! 2. `h a` and `r` to be definitionally equal, by δι from `h`'s definition.
//!
//! A reducer is COVERED when it fired on at least one battery input and every
//! result it produced passed both checks. A heartbeat budget bounds each check:
//! a result the reference theory cannot establish within it counts against the
//! reducer, never for it. The battery generates arguments only for binders
//! whose type it knows how to populate (the literal carriers below); a head
//! with any other binder is `unsupported`, which is not covered.

use clean_kernel::env::{Environment, KernelTheory};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

/// Per-check heartbeat budget of the reference theory.
pub const DIFFERENTIAL_HEARTBEATS: u32 = 2_000_000;

/// What the battery found for one reducer.
#[derive(Debug, Clone, Default)]
pub struct ReducerDifferential {
    /// Battery inputs the reducer produced a result for.
    pub fired: usize,
    /// Results that passed both checks.
    pub agreed: usize,
    /// Results that did not, each with the input and the reason.
    pub disagreements: Vec<String>,
    /// Why no battery could be built, when none could.
    pub unsupported: Option<String>,
}

impl ReducerDifferential {
    /// Covered: fired at least once, and every result agreed.
    #[must_use]
    pub fn covered(&self) -> bool {
        self.unsupported.is_none() && self.fired > 0 && self.disagreements.is_empty()
    }
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

const NATS: [u64; 9] = [0, 1, 2, 3, 7, 8, 255, 256, 1000];
const WIDTHS: [u64; 3] = [1, 4, 8];
const CHARS: [u32; 9] = [0x41, 0x61, 0x20, 0x30, 0x7A, 0x0A, 0xC4, 0xDF, 0x3000];
const STRINGS: [&str; 8] = ["", "a", "abc", " x", "\u{3000}x", "Ä", "ß", "a b\n"];

/// Literal inputs for a binder of type `ty`, or `None` for a type the battery
/// does not populate. `ref_tc` puts fixed-width values in constructor form
/// too, since some reducers recognise only that form.
fn values_for(ty: &Expr, ref_tc: &TypeChecker<'_>) -> Option<Vec<Expr>> {
    // A binder type can arrive wrapped in (empty) metadata from the `.olean`.
    let mut ty = ty;
    while let ExprKind::MData(_, inner) = ty.kind() {
        ty = inner;
    }
    let head = ty.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let args = ty.get_app_args();
    let s = name.to_string();
    let nat = |n: u64| Expr::nat_lit(n);
    let out: Vec<Expr> = match (s.as_str(), args.len()) {
        ("Nat", 0) => NATS.iter().map(|&n| nat(n)).collect(),
        ("Bool", 0) => vec![c("Bool.true"), c("Bool.false")],
        ("Char", 0) => CHARS
            .iter()
            .map(|&n| Expr::app(c("Char.ofNat"), nat(u64::from(n))))
            .collect(),
        ("String", 0) => STRINGS.iter().map(Expr::str_lit).collect(),
        ("Int", 0) => [0u64, 1, 5, 255]
            .iter()
            .map(|&n| Expr::app(c("Int.ofNat"), nat(n)))
            .chain(
                [0u64, 4]
                    .iter()
                    .map(|&n| Expr::app(c("Int.negSucc"), nat(n))),
            )
            .collect(),
        ("UInt8" | "UInt16" | "UInt32" | "UInt64", 0) => {
            let of_nat = c(&format!("{s}.ofNat"));
            let raw: Vec<Expr> = [0u64, 1, 2, 3, 100, 200, 255, 256]
                .iter()
                .map(|&n| Expr::app(of_nat.clone(), nat(n)))
                .collect();
            let whnf: Vec<Expr> = raw.iter().map(|e| ref_tc.whnf(e)).collect();
            raw.into_iter().chain(whnf).collect()
        }
        ("Int8" | "Int16" | "Int32" | "Int64", 0) => {
            let of_int = c(&format!("{s}.ofInt"));
            [0u64, 1, 2, 100]
                .iter()
                .map(|&n| Expr::app(of_int.clone(), Expr::app(c("Int.ofNat"), nat(n))))
                .chain(
                    [0u64, 4]
                        .iter()
                        .map(|&n| Expr::app(of_int.clone(), Expr::app(c("Int.negSucc"), nat(n)))),
                )
                .collect()
        }
        ("Lean.Name", 0) => {
            let anon = c("Lean.Name.anonymous");
            let str_ = |p: Expr, s: &str| Expr::apps(c("Lean.Name.str"), [p, Expr::str_lit(s)]);
            let a = str_(anon.clone(), "a");
            vec![
                anon.clone(),
                a.clone(),
                str_(a.clone(), "b"),
                Expr::apps(c("Lean.Name.num"), [a, nat(1)]),
            ]
        }
        ("BitVec", 1) => {
            let w = args[0].clone();
            [0u64, 1, 3, 5, 255]
                .iter()
                .map(|&n| Expr::apps(c("BitVec.ofNat"), [w.clone(), nat(n)]))
                .collect()
        }
        _ => return None,
    };
    Some(out)
}

/// Every argument list the battery builds for `head`, with the head's own
/// binders instantiated left to right (a later binder's type may mention an
/// earlier argument, as `BitVec n` does). Implicit `Nat` binders take small
/// widths; any other implicit or instance binder makes the head unsupported.
fn battery(
    env: &Environment,
    head: &Name,
    ref_tc: &TypeChecker<'_>,
) -> Result<Vec<Vec<Expr>>, String> {
    let ci = env
        .get_const(head)
        .ok_or_else(|| format!("`{head}` is not a constant of this environment"))?;
    if !ci.level_params.is_empty() {
        return Err(format!("`{head}` is universe-polymorphic"));
    }
    let mut lists: Vec<(Vec<Expr>, Expr)> = vec![(Vec::new(), ci.type_.clone())];
    while let Some((_, ty)) = lists.first() {
        let implicit = match ty.kind() {
            ExprKind::Pi(bd, _, _) => bd.info != clean_kernel::expr::BinderInfo::Default,
            _ => break,
        };
        let mut next = Vec::new();
        for (args, ty) in lists {
            let ExprKind::Pi(_, dom, body) = ty.kind() else {
                return Err("uneven telescope".to_owned());
            };
            let mut dom: &Expr = dom;
            while let ExprKind::MData(_, inner) = dom.kind() {
                dom = inner;
            }
            let values = if implicit {
                match dom.kind() {
                    ExprKind::Const(n, _) if n.to_string() == "Nat" => {
                        WIDTHS.iter().map(|&w| Expr::nat_lit(w)).collect()
                    }
                    _ => return Err(format!("`{head}` has a non-`Nat` implicit binder")),
                }
            } else {
                values_for(dom, ref_tc)
                    .ok_or_else(|| format!("`{head}` has a binder of type {dom:?}"))?
            };
            for v in values {
                let mut a = args.clone();
                a.push(v.clone());
                next.push((a, body.instantiate(&v)));
            }
        }
        // Keep the product bounded: every value of a unary head, a spread of
        // pairs for wider ones.
        next.truncate(96);
        lists = next;
    }
    Ok(lists.into_iter().map(|(args, _)| args).collect())
}

/// Run the battery for the reducer registered for `head` in `env` (which must
/// hold `head`'s definition and its δ-closure, as the `.olean` stores them).
#[must_use]
pub fn differential(env: &Environment, head: &Name) -> ReducerDifferential {
    let mut out = ReducerDifferential::default();
    let Some(reducer) = env.get_native_reducer(head) else {
        out.unsupported = Some(format!("no reducer is registered for `{head}`"));
        return out;
    };
    let mut ref_tc = TypeChecker::new(env);
    ref_tc.set_kernel_theory(KernelTheory::LeanReference);
    ref_tc.set_heartbeat_limit(DIFFERENTIAL_HEARTBEATS);
    let inputs = match battery(env, head, &ref_tc) {
        Ok(inputs) => inputs,
        Err(why) => {
            out.unsupported = Some(why);
            return out;
        }
    };
    for args in inputs {
        let term = Expr::apps(Expr::const_(head.clone(), vec![]), args.iter().cloned());
        let refs: Vec<&Expr> = args.iter().collect();
        let Some(result) = reducer(&refs) else {
            continue;
        };
        out.fired += 1;
        ref_tc.reset_local_context();
        ref_tc.reset_heartbeat();
        let verdict = (|| -> Result<(), String> {
            let t_ty = ref_tc
                .infer_type(&term)
                .map_err(|e| format!("the input is ill-typed: {e:?}"))?;
            ref_tc.reset_heartbeat();
            let r_ty = ref_tc
                .infer_type(&result)
                .map_err(|e| format!("the result is ill-typed: {e:?}"))?;
            ref_tc.reset_heartbeat();
            if !ref_tc.is_def_eq(&t_ty, &r_ty) {
                return Err(format!(
                    "the result has type {r_ty:?}, the head's value {t_ty:?}"
                ));
            }
            ref_tc.reset_heartbeat();
            if !ref_tc.is_def_eq(&term, &result) {
                return Err(format!("δι does not reach {result:?}"));
            }
            Ok(())
        })();
        match verdict {
            Ok(()) => out.agreed += 1,
            Err(why) => out.disagreements.push(format!("{term:?}: {why}")),
        }
    }
    out
}
