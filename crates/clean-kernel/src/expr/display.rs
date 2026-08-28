// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pretty-printing for Expr.
//!
//! Contains Display impl and all display helper functions.

use super::*;
use crate::level::Level;
use crate::name::Name;

// ── Display (pretty-printing) ───────────────────────────────────────────────

fn display_level_as_nat(level: &Level) -> Option<u32> {
    // Iterative with checked_add: total on all inputs. The previous recursive
    // `.map(|n| n + 1)` carried a panicking add (Trust ledger 2026-06-10,
    // assertion: arithmetic overflow (Add) @ expr/display.rs:17) and was not
    // stack-safe on deep Succ chains.
    let mut n: u32 = 0;
    let mut current = level;
    loop {
        match current {
            Level::Zero => return Some(n),
            Level::Succ(inner) => {
                n = n.checked_add(1)?;
                current = inner;
            }
            _ => return None,
        }
    }
}

fn display_level(level: &Level) -> String {
    if let Some(n) = display_level_as_nat(level) {
        return n.to_string();
    }
    level.to_string()
}

fn display_sort(level: &Level) -> String {
    match display_level_as_nat(level) {
        Some(0) => "Prop".to_string(),
        Some(1) => "Type".to_string(),
        Some(n) => format!("Type {}", n - 1),
        None => format!("Sort {}", display_level(level)),
    }
}

/// Check whether the expression uses the bound variable at `param_depth`.
/// Stack-safe to prevent overflow on deeply nested expressions.
fn display_uses_param(kind: &ExprKind, param_depth: u32) -> bool {
    stack_safe(|| display_uses_param_impl(kind, param_depth))
}

fn display_uses_param_impl(kind: &ExprKind, param_depth: u32) -> bool {
    match kind {
        ExprKind::BVar(idx) => *idx == param_depth,
        ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => false,
        ExprKind::App(f, a) => {
            display_uses_param(&f.kind, param_depth) || display_uses_param(&a.kind, param_depth)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&body.kind, param_depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&val.kind, param_depth)
                || display_uses_param(&body.kind, param_depth + 1)
        }
        ExprKind::Proj(_, _, e) => display_uses_param(&e.kind, param_depth),
        ExprKind::MData(_, inner) => display_uses_param(&inner.kind, param_depth),
        ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => false,
        ExprKind::CubicalPath { ty, left, right } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&left.kind, param_depth)
                || display_uses_param(&right.kind, param_depth)
        }
        ExprKind::CubicalPathLam { body } => display_uses_param(&body.kind, param_depth + 1),
        ExprKind::CubicalPathApp { path, arg } => {
            display_uses_param(&path.kind, param_depth)
                || display_uses_param(&arg.kind, param_depth)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&phi.kind, param_depth)
                || display_uses_param(&u.kind, param_depth)
                || display_uses_param(&base.kind, param_depth)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&phi.kind, param_depth)
                || display_uses_param(&base.kind, param_depth)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&r.kind, param_depth)
                || display_uses_param(&s.kind, param_depth)
                || display_uses_param(&base.kind, param_depth)
        }
        ExprKind::ZFCSet(_) => false,
        ExprKind::ZFCMem { element, set } => {
            display_uses_param(&element.kind, param_depth)
                || display_uses_param(&set.kind, param_depth)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            display_uses_param(&domain.kind, param_depth)
                || display_uses_param(&pred.kind, param_depth + 1)
        }
        ExprKind::SProp => false,
        ExprKind::Squash(inner) => display_uses_param(&inner.kind, param_depth),
    }
}

/// Generate a binder name based on the domain type.
fn display_binder_name(kind: &ExprKind, used: &[String]) -> String {
    let base: String = match kind {
        ExprKind::Sort(level) => match display_level_as_nat(level) {
            Some(0) => "P".to_string(),
            Some(1) => "A".to_string(),
            _ => "u".to_string(),
        },
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if let Some(c) = s.chars().next() {
                if c.is_alphabetic() {
                    c.to_string()
                } else {
                    "x".to_string()
                }
            } else {
                "x".to_string()
            }
        }
        ExprKind::Pi(_, _, _) => "f".to_string(),
        _ => "x".to_string(),
    };
    let base = base.to_lowercase();
    if !used.contains(&base) {
        return base;
    }
    for i in 1..100 {
        let name = format!("{base}{i}");
        if !used.contains(&name) {
            return name;
        }
    }
    format!("{}_{}", base, used.len())
}

// ── Precedence, on Lean's own scale ─────────────────────────────────────────
//
// `prec` is the precedence the *enclosing* context demands: a term renders
// parenthesised exactly when its own level is lower. Using Lean's numbers
// (rather than an ad-hoc 0..3 ladder) is what lets `Nat.myTriple n = n + n + n`
// print without spurious parentheses around either side — an application binds
// tighter than `=`, and `+` binds tighter still.

/// The loosest context: nothing is parenthesised here.
const PREC_BOTTOM: u32 = 0;
/// `↔`.
const PREC_IFF: u32 = 20;
/// `→` (Lean's `arrow`), and the level `∀`/`fun` bodies extend through.
const PREC_ARROW: u32 = 25;
/// `∨`.
const PREC_OR: u32 = 30;
/// `∧`.
const PREC_AND: u32 = 35;
/// `¬`.
const PREC_NOT: u32 = 40;
/// Comparisons and `=`.
const PREC_REL: u32 = 50;
/// `+`, `-`, `++`.
const PREC_ADD: u32 = 65;
/// `*`, `/`, `%`.
const PREC_MUL: u32 = 70;
/// `^` and prefix `-`.
const PREC_POW: u32 = 75;
/// A function application, `f a b` (Lean's `lead`).
const PREC_APP: u32 = 1022;
/// An application's *argument* position (Lean's `max`): every compound term
/// standing here needs parentheses.
const PREC_MAX: u32 = 1024;

/// Associativity of an infix notation, which fixes where parentheses may be
/// dropped in a chain: `a - b - c` is `(a - b) - c`, `a ^ b ^ c` is
/// `a ^ (b ^ c)`, and `a = b = c` is not a chain at all.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Assoc {
    Left,
    Right,
    None,
}

/// An infix notation: the symbol, its level, and its associativity.
struct InfixNotation {
    symbol: &'static str,
    prec: u32,
    assoc: Assoc,
}

/// Infix notation for a fully-applied head constant.
///
/// `argc` is the number of arguments actually applied, and it must match
/// exactly: a partially-applied `HAdd.hAdd` is a function, not a sum, and
/// printing it as `a + b` would be a lie. The two operands are always the
/// last two arguments — everything before them is the implicit type and
/// instance telescope, which is exactly what Lean hides.
fn infix_notation(head: &str, argc: usize) -> Option<InfixNotation> {
    let (symbol, prec, assoc, arity) = match head {
        // Core logic and equality.
        "Eq" => ("=", PREC_REL, Assoc::None, 3),
        "Ne" => ("≠", PREC_REL, Assoc::None, 3),
        "Iff" => ("↔", PREC_IFF, Assoc::None, 2),
        "And" => ("∧", PREC_AND, Assoc::Right, 2),
        "Or" => ("∨", PREC_OR, Assoc::Right, 2),
        // Heterogeneous arithmetic: `α β γ inst lhs rhs`.
        "HAdd.hAdd" => ("+", PREC_ADD, Assoc::Left, 6),
        "HSub.hSub" => ("-", PREC_ADD, Assoc::Left, 6),
        "HMul.hMul" => ("*", PREC_MUL, Assoc::Left, 6),
        "HDiv.hDiv" => ("/", PREC_MUL, Assoc::Left, 6),
        "HMod.hMod" => ("%", PREC_MUL, Assoc::Left, 6),
        "HPow.hPow" => ("^", PREC_POW, Assoc::Right, 6),
        "HAppend.hAppend" => ("++", PREC_ADD, Assoc::Right, 6),
        // Homogeneous relations and operations: `α inst lhs rhs`.
        "LE.le" => ("≤", PREC_REL, Assoc::None, 4),
        "LT.lt" => ("<", PREC_REL, Assoc::None, 4),
        "GE.ge" => ("≥", PREC_REL, Assoc::None, 4),
        "GT.gt" => (">", PREC_REL, Assoc::None, 4),
        "BEq.beq" => ("==", PREC_REL, Assoc::None, 4),
        _ => return None,
    };
    (argc == arity).then_some(InfixNotation {
        symbol,
        prec,
        assoc,
    })
}

/// Wrap `body` in parentheses when the enclosing context binds tighter than
/// the term's own level.
fn parenthesise(body: String, own_prec: u32, ambient: u32) -> String {
    if ambient > own_prec {
        format!("({body})")
    } else {
        body
    }
}

/// Render a fully-applied constant through Lean notation, or `None` when no
/// notation applies and the caller should fall back to `f a b` juxtaposition.
///
/// The head name is materialised as a `String` for matching. `Display` is a
/// cold path — it runs when a message is built for a human, never inside
/// conversion or unification — so the allocation is not on any hot loop.
fn display_notation(name: &Name, args: &[&Expr], prec: u32, binders: &[String]) -> Option<String> {
    let head = name.to_string();
    match (head.as_str(), args.len()) {
        // `@OfNat.ofNat α n inst` IS the numeral `n`. Without this every
        // literal in a goal reads `OfNat.ofNat Nat 1 (instOfNatNat 1)`.
        ("OfNat.ofNat", 3) => Some(display_expr_to_string(&args[1].kind, prec, binders)),
        ("Not", 1) => {
            let inner = display_expr_to_string(&args[0].kind, PREC_NOT + 1, binders);
            Some(parenthesise(format!("¬{inner}"), PREC_NOT, prec))
        }
        // `@Neg.neg α inst a`.
        ("Neg.neg", 3) => {
            let inner = display_expr_to_string(&args[2].kind, PREC_POW + 1, binders);
            Some(parenthesise(format!("-{inner}"), PREC_POW, prec))
        }
        // `@Exists α (fun x => p)` — bind the predicate's own binder so the
        // body prints with a name rather than a de Bruijn index.
        ("Exists", 2) => {
            let ExprKind::Lam(_, ty, body) = &args[1].kind else {
                return None;
            };
            let binder = display_binder_name(&ty.kind, binders);
            let mut inner_binders = binders.to_vec();
            inner_binders.push(binder.clone());
            let body_str = display_expr_to_string(&body.kind, PREC_BOTTOM, &inner_binders);
            Some(parenthesise(
                format!("∃ {binder}, {body_str}"),
                PREC_BOTTOM,
                prec,
            ))
        }
        (head, argc) => {
            let notation = infix_notation(head, argc)?;
            // Operands are the last two arguments; `argc >= 2` holds because
            // every arity in the table is at least 2.
            let (lhs, rhs) = (args[argc - 2], args[argc - 1]);
            let (lhs_prec, rhs_prec) = match notation.assoc {
                Assoc::Left => (notation.prec, notation.prec + 1),
                Assoc::Right => (notation.prec + 1, notation.prec),
                Assoc::None => (notation.prec + 1, notation.prec + 1),
            };
            let lhs_str = display_expr_to_string(&lhs.kind, lhs_prec, binders);
            let rhs_str = display_expr_to_string(&rhs.kind, rhs_prec, binders);
            Some(parenthesise(
                format!("{lhs_str} {} {rhs_str}", notation.symbol),
                notation.prec,
                prec,
            ))
        }
    }
}

/// Split a curried application into its head and argument spine.
///
/// Iterative: an application spine of thousands of arguments is ordinary in
/// generated code, and this runs inside `Display`.
fn collect_app_spine(kind: &ExprKind) -> (&ExprKind, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = kind;
    while let ExprKind::App(func, arg) = current {
        args.push(arg.as_ref());
        current = &func.kind;
    }
    args.reverse();
    (current, args)
}

/// Helper: format an ExprKind to a String (used for recursive sub-expressions).
/// Stack-safe to prevent overflow on deeply nested expressions during Display.
fn display_expr_to_string(kind: &ExprKind, prec: u32, binders: &[String]) -> String {
    stack_safe(|| display_expr_to_string_impl(kind, prec, binders))
}

fn display_expr_to_string_impl(kind: &ExprKind, prec: u32, binders: &[String]) -> String {
    struct Helper<'a> {
        kind: &'a ExprKind,
        prec: u32,
        binders: &'a [String],
    }
    impl std::fmt::Display for Helper<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            display_expr_ctx(self.kind, self.prec, self.binders, f)
        }
    }
    Helper {
        kind,
        prec,
        binders,
    }
    .to_string()
}

/// Stack-safe wrapper for display_expr_ctx_impl.
/// Prevents stack overflow on deeply nested expressions during Display::fmt.
fn display_expr_ctx(
    kind: &ExprKind,
    prec: u32,
    binders: &[String],
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    stack_safe(|| display_expr_ctx_impl(kind, prec, binders, f))
}

fn display_expr_ctx_impl(
    kind: &ExprKind,
    prec: u32,
    binders: &[String],
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    match kind {
        ExprKind::Sort(level) => write!(f, "{}", display_sort(level)),
        // Universe levels are suppressed, matching Lean's default
        // (`pp.universes false`): `List.{0} Nat` reads `List Nat`. They are
        // structurally invisible in source and are noise in a goal window;
        // `{:?}` still shows them for debugging.
        ExprKind::Const(name, _) => write!(f, "{name}"),
        ExprKind::Pi(bd, dom, body)
            if bd.info == BinderInfo::Default && !display_uses_param(&body.kind, 0) =>
        {
            // `→` is right-associative: `A -> B -> C` needs no parentheses on
            // the right, but a nested arrow on the left does.
            let left = display_expr_to_string(&dom.kind, PREC_ARROW + 1, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push("_".to_string());
            let right = display_expr_to_string(&body.kind, PREC_ARROW, &new_binders);
            if prec > PREC_ARROW {
                write!(f, "({left} -> {right})")
            } else {
                write!(f, "{left} -> {right}")
            }
        }
        ExprKind::Pi(_, dom, body) => {
            let name = display_binder_name(&dom.kind, binders);
            let dom_str = display_expr_to_string(&dom.kind, PREC_BOTTOM, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, PREC_BOTTOM, &new_binders);
            if prec > PREC_BOTTOM {
                write!(f, "(({name} : {dom_str}) -> {body_str})")
            } else {
                write!(f, "({name} : {dom_str}) -> {body_str}")
            }
        }
        ExprKind::Lam(_, ty, body) => {
            let name = display_binder_name(&ty.kind, binders);
            let ty_str = display_expr_to_string(&ty.kind, PREC_BOTTOM, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, PREC_BOTTOM, &new_binders);
            if prec > PREC_BOTTOM {
                write!(f, "(fun ({name} : {ty_str}) => {body_str})")
            } else {
                write!(f, "fun ({name} : {ty_str}) => {body_str}")
            }
        }
        ExprKind::App(_, _) => {
            let (head, args) = collect_app_spine(kind);
            // Notation first: a fully-applied `HAdd.hAdd`/`Eq`/`OfNat.ofNat`
            // spine prints as `a + b` / `a = b` / `1`, which also drops the
            // leading implicit-type and instance arguments Lean hides.
            if let ExprKind::Const(name, _) = head {
                if let Some(rendered) = display_notation(name, &args, prec, binders) {
                    return f.write_str(&rendered);
                }
            }
            // Plain juxtaposition. The head sits in function position (nested
            // spines do not re-parenthesise); every argument sits at `max`.
            let mut out = display_expr_to_string(head, PREC_APP, binders);
            for arg in args {
                out.push(' ');
                out.push_str(&display_expr_to_string(&arg.kind, PREC_MAX, binders));
            }
            if prec > PREC_APP {
                write!(f, "({out})")
            } else {
                f.write_str(&out)
            }
        }
        ExprKind::Let(_, ty, val, body, _) => {
            let name = display_binder_name(&ty.kind, binders);
            let ty_str = display_expr_to_string(&ty.kind, PREC_BOTTOM, binders);
            let val_str = display_expr_to_string(&val.kind, PREC_BOTTOM, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, PREC_BOTTOM, &new_binders);
            let out = format!("let ({name} : {ty_str}) := {val_str} in {body_str}");
            if prec > PREC_BOTTOM {
                write!(f, "({out})")
            } else {
                f.write_str(&out)
            }
        }
        // Through `Display for Literal`: the derived `Debug` would render
        // `Nat(Small(1))`, a Rust variant name, into a user's goal window.
        ExprKind::Lit(lit) => write!(f, "{lit}"),
        ExprKind::Proj(name, idx, e) => {
            let e_str = display_expr_to_string(&e.kind, PREC_MAX, binders);
            write!(f, "{name}.{idx}.{e_str}")
        }
        // `FVarId`'s derived `Debug` renders `FVarId(0)`; print the raw id so
        // the rendering carries no Rust type name.
        ExprKind::FVar(id) => write!(f, "fvar#{}", id.as_u64()),
        ExprKind::BVar(idx) => {
            let idx = *idx as usize;
            if idx < binders.len() {
                write!(f, "{}", binders[binders.len() - 1 - idx])
            } else {
                write!(f, "bvar#{idx}")
            }
        }
        ExprKind::MData(_, inner) => {
            write!(f, "@[mdata] ")?;
            display_expr_ctx(&inner.kind, prec, binders, f)
        }
        ExprKind::CubicalInterval => write!(f, "\u{1d540}"),
        ExprKind::CubicalI0 => write!(f, "i0"),
        ExprKind::CubicalI1 => write!(f, "i1"),
        ExprKind::CubicalPath { ty, left, right } => {
            let ty_s = display_expr_to_string(&ty.kind, PREC_MAX, binders);
            let l_s = display_expr_to_string(&left.kind, PREC_MAX, binders);
            let r_s = display_expr_to_string(&right.kind, PREC_MAX, binders);
            write!(f, "Path {ty_s} {l_s} {r_s}")
        }
        ExprKind::CubicalPathLam { body } => {
            let name = "i".to_string();
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, PREC_BOTTOM, &new_binders);
            write!(f, "pathLam ({name} : \u{1d540}) => {body_str}")
        }
        ExprKind::CubicalPathApp { path, arg } => {
            let p_s = display_expr_to_string(&path.kind, PREC_APP, binders);
            let a_s = display_expr_to_string(&arg.kind, PREC_MAX, binders);
            write!(f, "{p_s} @ {a_s}")
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            let ty_s = display_expr_to_string(&ty.kind, PREC_MAX, binders);
            let phi_s = display_expr_to_string(&phi.kind, PREC_MAX, binders);
            let u_s = display_expr_to_string(&u.kind, PREC_MAX, binders);
            let b_s = display_expr_to_string(&base.kind, PREC_MAX, binders);
            write!(f, "hcomp {ty_s} {phi_s} {u_s} {b_s}")
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            let ty_s = display_expr_to_string(&ty.kind, PREC_MAX, binders);
            let phi_s = display_expr_to_string(&phi.kind, PREC_MAX, binders);
            let b_s = display_expr_to_string(&base.kind, PREC_MAX, binders);
            write!(f, "transp {ty_s} {phi_s} {b_s}")
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            let ty_s = display_expr_to_string(&ty.kind, PREC_MAX, binders);
            let r_s = display_expr_to_string(&r.kind, PREC_MAX, binders);
            let s_s = display_expr_to_string(&s.kind, PREC_MAX, binders);
            let b_s = display_expr_to_string(&base.kind, PREC_MAX, binders);
            write!(f, "coe {ty_s} {r_s} {s_s} {b_s}")
        }
        ExprKind::ZFCSet(set_expr) => write!(f, "{set_expr:?}"),
        ExprKind::ZFCMem { element, set } => {
            let el_s = display_expr_to_string(&element.kind, PREC_MAX, binders);
            let s_s = display_expr_to_string(&set.kind, PREC_MAX, binders);
            write!(f, "{el_s} \u{2208} {s_s}")
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            let name = "x".to_string();
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let dom_s = display_expr_to_string(&domain.kind, PREC_BOTTOM, binders);
            let pred_s = display_expr_to_string(&pred.kind, PREC_BOTTOM, &new_binders);
            write!(f, "{{ {name} \u{2208} {dom_s} | {pred_s} }}")
        }
        ExprKind::SProp => write!(f, "SProp"),
        ExprKind::Squash(inner) => {
            let inner_s = display_expr_to_string(&inner.kind, PREC_BOTTOM, binders);
            write!(f, "\u{2308}{inner_s}\u{2309}")
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_expr_ctx(&self.kind, 0, &[], f)
    }
}
