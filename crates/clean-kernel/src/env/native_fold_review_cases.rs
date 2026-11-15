// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The INPUTS of the native-fold review (`native_fold_review.rs`): literal
//! arguments for every binder a head's type telescope has, each paired with
//! the value the independent reference reads, and the answer that reference
//! gives. Edge cases are deliberate: zero, one, the width boundaries of every
//! fixed-width type, values past `2^64`, invalid code points, multi-byte and
//! astral characters. Heads whose telescope carries instances or universe
//! levels (`HAdd.hAdd`, `ite`, `BEq.beq`, …) are built by
//! [`special_cases`] from the instances the environment itself declares.

use super::reference::reference;
use super::{fresh, Case, NameComp, Val};
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Most cases per head (the product of the per-binder inputs is cut here).
const CASE_CAP: usize = 169;

/// An input holding a `Nat` literal above this anywhere is `deep`: δι of a
/// definition that recurses on it (a `Nat` recursion, a `Fin`/`UInt` carrier
/// compared by structural descent) does not finish within the review's budget,
/// and a heartbeat budget does not bound the memory such a descent takes
/// (measured: `UInt32.decEq` on `2^32 + 5` over the prelude passed 6 GB).
const DEEP_NAT: u64 = 1000;

/// Whether `e` holds a `Nat` literal above [`DEEP_NAT`].
pub(super) fn holds_deep_literal(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::Lit(crate::expr::Literal::Nat(v)) => v.to_u64().is_none_or(|v| v > DEEP_NAT),
        ExprKind::App(f, a) => holds_deep_literal(f) || holds_deep_literal(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            holds_deep_literal(t) || holds_deep_literal(b)
        }
        ExprKind::MData(_, inner) => holds_deep_literal(inner),
        _ => false,
    }
}

const NATS: [u128; 13] = [
    0,
    1,
    2,
    3,
    6,
    10,
    13,
    255,
    256,
    1 << 32,
    (1 << 64) - 1,
    (1 << 64) + 1,
    1 << 100,
];
const WIDTHS: [u128; 6] = [0, 1, 4, 8, 16, 64];
const CHARS: [u32; 15] = [
    0x41, 0x61, 0x5A, 0x7A, 0x30, 0x39, 0x20, 0x09, 0x0A, 0x0D, 0xC4, 0xDF, 0x3000, 0x10FFFF,
    0xD800,
];
const STRINGS: [&str; 11] = [
    "",
    "a",
    "ab",
    "abc",
    " x",
    "\u{3000}x",
    "Ä",
    "ß",
    "a b\n",
    "héllo",
    "😀z",
];
const INTS: [i128; 10] = [
    0,
    1,
    5,
    255,
    -1,
    -5,
    1 << 63,
    -(1 << 63),
    1 << 70,
    -(1 << 70),
];
const UINT_RAW: [u128; 10] = [0, 1, 2, 3, 100, 200, 255, 256, 65_535, 65_536];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn lit(v: u128) -> Expr {
    Expr::nat_lit_u128(v)
}

fn mask(bits: u64) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

fn int_expr(i: i128) -> Option<Expr> {
    Some(if i >= 0 {
        Expr::app(c("Int.ofNat"), lit(u128::try_from(i).ok()?))
    } else {
        Expr::app(c("Int.negSucc"), lit(u128::try_from(-(i + 1)).ok()?))
    })
}

fn signed(v: u128, bits: u64) -> i128 {
    let v = v & mask(bits);
    if bits == 0 {
        0
    } else if v >> (bits - 1) == 1 {
        (v as i128) - (1i128 << bits)
    } else {
        v as i128
    }
}

fn name_val(comps: &[NameComp]) -> Expr {
    let mut out = c("Lean.Name.anonymous");
    for comp in comps {
        out = match comp {
            NameComp::Str(s) => Expr::apps(c("Lean.Name.str"), [out, Expr::str_lit(s)]),
            NameComp::Num(k) => Expr::apps(c("Lean.Name.num"), [out, Expr::nat_lit(*k)]),
        };
    }
    out
}

/// Inputs for an explicit binder of type `ty`, or `None` for a type the
/// review does not populate.
fn values_for(env: &Environment, ty: &Expr) -> Option<Vec<(Expr, Val)>> {
    let ty = ty.strip_mdata();
    let ExprKind::Const(head, _) = ty.get_app_fn().kind() else {
        return None;
    };
    let args = ty.get_app_args();
    let head = head.to_string();
    let has = |s: &str| env.get_const(&n(s)).is_some();
    Some(match (head.as_str(), args.len()) {
        ("Nat", 0) => NATS.iter().map(|&v| (lit(v), Val::Nat(v))).collect(),
        ("Bool", 0) => vec![
            (c("Bool.true"), Val::Bool(true)),
            (c("Bool.false"), Val::Bool(false)),
        ],
        ("Char", 0) => CHARS
            .iter()
            .map(|&cp| {
                let valid = cp < 0xD800 || (0xDFFF < cp && cp < 0x11_0000);
                (
                    Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(cp))),
                    Val::Char(if valid { cp } else { 0 }),
                )
            })
            .collect(),
        ("String", 0) => STRINGS
            .iter()
            .map(|s| (Expr::str_lit(s), Val::Str((*s).to_string())))
            .collect(),
        ("Int", 0) => INTS
            .iter()
            .filter_map(|&i| Some((int_expr(i)?, Val::Int(i))))
            .collect(),
        ("UInt8" | "UInt16" | "UInt32" | "UInt64", 0) => {
            let bits: u64 = head.trim_start_matches("UInt").parse().ok()?;
            let of_nat = format!("{head}.ofNat");
            has(&of_nat).then_some(())?;
            let edges = [mask(bits), mask(bits) + 1, mask(bits) + 6];
            UINT_RAW
                .iter()
                .chain(edges.iter())
                .map(|&v| {
                    (
                        Expr::app(c(&of_nat), lit(v)),
                        Val::UInt(bits, v & mask(bits)),
                    )
                })
                .collect()
        }
        ("Int8" | "Int16" | "Int32" | "Int64", 0) => {
            let bits: u64 = head.trim_start_matches("Int").parse().ok()?;
            let of_int = format!("{head}.ofInt");
            has(&of_int).then_some(())?;
            let max = (1i128 << (bits - 1)) - 1;
            [0, 1, 2, 100, -1, -5, max, -max - 1, max + 1]
                .iter()
                .filter_map(|&i| {
                    let v = signed((i as u128) & mask(bits), bits);
                    Some((Expr::app(c(&of_int), int_expr(i)?), Val::SInt(bits, v)))
                })
                .collect()
        }
        ("BitVec", 1) => {
            let ExprKind::Lit(crate::expr::Literal::Nat(w)) = args[0].kind() else {
                return None;
            };
            let w = w.to_u64().filter(|w| *w <= 128)?;
            let m = mask(w);
            [0u128, 1, 3, 5, 255, m, m.wrapping_add(1), m.wrapping_add(4)]
                .iter()
                .map(|&v| {
                    (
                        Expr::apps(c("BitVec.ofNat"), [Expr::nat_lit(w), lit(v)]),
                        Val::BitVec(w, v & m),
                    )
                })
                .collect()
        }
        ("Lean.Name", 0) => {
            let a = NameComp::Str("a".into());
            let b = NameComp::Str("b".into());
            let shapes: Vec<Vec<NameComp>> = vec![
                vec![],
                vec![a.clone()],
                vec![a.clone(), b.clone()],
                vec![a.clone(), NameComp::Num(1)],
                vec![b],
            ];
            shapes
                .into_iter()
                .map(|s| (name_val(&s), Val::Name(s)))
                .collect()
        }
        _ => return None,
    })
}

/// The cases of `name`: the generic telescope walk for a monomorphic head, or
/// the hand-built instances of [`special_cases`].
pub(super) fn cases_for(
    env: &Environment,
    name: &Name,
    tc: &TypeChecker<'_>,
) -> Result<Vec<Case>, String> {
    let ci = env
        .get_const(name)
        .ok_or_else(|| format!("`{name}` is not declared"))?;
    let value = ci
        .value
        .clone()
        .ok_or_else(|| format!("`{name}` has no value"))?;
    if let Some(special) = super::special::special_cases(env, name, tc) {
        return special;
    }
    if !ci.level_params.is_empty() {
        return Err(format!(
            "`{name}` is universe-polymorphic and has no case builder"
        ));
    }
    let spelled = name.to_string();
    let mut lists: Vec<(Vec<Expr>, Vec<Val>, Expr)> =
        vec![(Vec::new(), Vec::new(), ci.type_.clone())];
    loop {
        let ty = lists[0].2.clone();
        let ty = if matches!(ty.strip_mdata().kind(), ExprKind::Pi(..)) {
            ty
        } else {
            fresh(tc);
            let w = tc.whnf(&ty);
            if !matches!(w.kind(), ExprKind::Pi(..)) {
                break;
            }
            for entry in &mut lists {
                fresh(tc);
                entry.2 = tc.whnf(&entry.2);
            }
            w
        };
        let ExprKind::Pi(bd, _, _) = ty.strip_mdata().kind() else {
            break;
        };
        let implicit = bd.info != BinderInfo::Default;
        let mut next = Vec::new();
        for (args, vals, ty) in lists {
            let ExprKind::Pi(_, dom, body) = ty.strip_mdata().kind() else {
                return Err("uneven telescope".into());
            };
            let inputs: Vec<(Expr, Val)> = if implicit {
                match dom.strip_mdata().kind() {
                    ExprKind::Const(k, _) if k.to_string() == "Nat" => {
                        WIDTHS.iter().map(|&w| (lit(w), Val::Nat(w))).collect()
                    }
                    _ => return Err(format!("`{name}` has a non-`Nat` implicit binder")),
                }
            } else {
                values_for(env, dom)
                    .ok_or_else(|| format!("`{name}` has a binder of type {dom:?}"))?
            };
            for (e, v) in inputs {
                let (mut a, mut vs) = (args.clone(), vals.clone());
                a.push(e.clone());
                vs.push(v);
                next.push((a, vs, body.instantiate(&e)));
            }
        }
        if next.is_empty() {
            return Err("an empty input list".into());
        }
        next.truncate(CASE_CAP);
        lists = next;
    }
    let head = Expr::const_(name.clone(), vec![]);
    Ok(lists
        .into_iter()
        .map(|(args, vals, _)| {
            // No reference: the case still runs leg T (a fold whose result
            // has the wrong type is a disagreement whatever its value), but
            // it can never make the head reviewed.
            let answer = reference(&spelled, &vals).unwrap_or(Val::Opaque);
            let deep = args.iter().any(holds_deep_literal);
            Case {
                head: head.clone(),
                value: value.clone(),
                args,
                answer,
                deep,
            }
        })
        .collect())
}

/// `u` for every universe parameter of `name` (all heads the special builders
/// take are instantiated at `Nat`, `String`, … in `Type`, or `Sort 1`).
pub(super) fn levels(env: &Environment, name: &str, level: Level) -> Option<(Expr, Expr)> {
    let ci = env.get_const(&n(name))?;
    let levels = vec![level; ci.level_params.len()];
    let value = ci
        .value
        .as_ref()?
        .instantiate_level_params_direct(&ci.level_params, &levels);
    Some((Expr::const_(n(name), levels), value))
}
