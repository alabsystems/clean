// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`LeanTerm`] → Lean surface text with context-driven parenthesization.
//!
//! The single rule reproduces the batch-3 hand translations exactly: an infix
//! operand is wrapped iff its own precedence is `<=` the parent's (so every
//! binary operator fully parenthesizes an operand of equal-or-looser binding,
//! matching Isabelle's explicit tree — e.g. `(xs ++ ys) ++ zs` *and*
//! `xs ++ (ys ++ zs)` under a looser `=`). Method/application nodes bind tighter
//! than any infix; they are wrapped only as a *receiver* or *function argument*
//! when they carry arguments (so `xs.reverse.reverse` chains but
//! `(xs.map g).map f` and `.drop (n - xs.length)` parenthesize).

use super::types::LeanTerm;

/// The syntactic position a [`LeanTerm`] is being rendered into — the sole input
/// to the wrap decision.
#[derive(Debug, Clone, Copy)]
pub enum Ctx {
    /// The statement root (or an `=`-operand rendered at sentence level): never
    /// wrapped by the outer context.
    Top,
    /// An operand of an infix operator of the given precedence.
    Operand(u8),
    /// A receiver of a dot-notation method (`recv.method`).
    Recv,
    /// An argument in a function/method application (`f arg`).
    Arg,
}

/// Render `t` at the statement root (no outer parentheses).
#[must_use]
pub fn render_top(t: &LeanTerm) -> String {
    render(t, Ctx::Top)
}

/// Render `t` in context `ctx`, adding parentheses when the context requires.
#[must_use]
pub fn render(t: &LeanTerm, ctx: Ctx) -> String {
    match t {
        LeanTerm::Atom(s) => s.clone(),
        LeanTerm::Infix {
            op, prec, lhs, rhs, ..
        } => {
            let inner = format!(
                "{} {op} {}",
                render(lhs, Ctx::Operand(*prec)),
                render(rhs, Ctx::Operand(*prec))
            );
            wrap(inner, wrap_infix(*prec, ctx))
        }
        LeanTerm::Prefix { op, arg } => {
            // A prefix operator binds loosely; parenthesize an infix operand and
            // wrap the whole node in any nested (non-Top) context.
            let inner = format!(
                "{op} {}",
                render(arg, Ctx::Operand(super::types::prec::LATTICE))
            );
            wrap(inner, !matches!(ctx, Ctx::Top))
        }
        LeanTerm::Method { recv, name, args } => {
            let mut s = format!("{}.{name}", render(recv, Ctx::Recv));
            for a in args {
                s.push(' ');
                s.push_str(&render(a, Ctx::Arg));
            }
            wrap(s, wrap_application(!args.is_empty(), ctx))
        }
        LeanTerm::App { head, args } => {
            let mut s = head.clone();
            for a in args {
                s.push(' ');
                s.push_str(&render(a, Ctx::Arg));
            }
            wrap(s, wrap_application(!args.is_empty(), ctx))
        }
    }
}

/// Whether an infix node of precedence `prec` needs parentheses in `ctx`.
fn wrap_infix(prec: u8, ctx: Ctx) -> bool {
    match ctx {
        Ctx::Top => false,
        Ctx::Operand(parent) => prec <= parent,
        Ctx::Recv | Ctx::Arg => true,
    }
}

/// Whether an application/method node needs parentheses in `ctx`. Applications
/// bind tighter than any infix (never wrapped as an operand); as a receiver or a
/// function argument they are wrapped only when they carry arguments (a nullary
/// projection like `.reverse` chains bare).
fn wrap_application(has_args: bool, ctx: Ctx) -> bool {
    match ctx {
        Ctx::Top | Ctx::Operand(_) => false,
        Ctx::Recv | Ctx::Arg => has_args,
    }
}

fn wrap(s: String, do_wrap: bool) -> String {
    if do_wrap {
        format!("({s})")
    } else {
        s
    }
}

#[cfg(test)]
mod tests {
    use super::super::types::{prec, LeanTerm};
    use super::*;

    fn a(s: &str) -> LeanTerm {
        LeanTerm::atom(s)
    }

    #[test]
    fn fully_parenthesizes_append_tree_under_eq() {
        // eq( ++(++(xs,ys), zs), ++(xs, ++(ys,zs)) )
        let lhs = LeanTerm::infix(
            "++",
            prec::ADD,
            LeanTerm::infix("++", prec::ADD, a("xs"), a("ys")),
            a("zs"),
        );
        let rhs = LeanTerm::infix(
            "++",
            prec::ADD,
            a("xs"),
            LeanTerm::infix("++", prec::ADD, a("ys"), a("zs")),
        );
        let eq = LeanTerm::infix("=", prec::EQ, lhs, rhs);
        assert_eq!(render_top(&eq), "(xs ++ ys) ++ zs = xs ++ (ys ++ zs)");
    }

    #[test]
    fn method_receiver_and_arg_parens() {
        // (xs ++ ys).length  — infix receiver wraps
        let len = LeanTerm::method(
            LeanTerm::infix("++", prec::ADD, a("xs"), a("ys")),
            "length",
            vec![],
        );
        assert_eq!(render_top(&len), "(xs ++ ys).length");
        // xs.reverse.reverse — nullary chains bare
        let rr = LeanTerm::method(
            LeanTerm::method(a("xs"), "reverse", vec![]),
            "reverse",
            vec![],
        );
        assert_eq!(render_top(&rr), "xs.reverse.reverse");
        // (xs.map g).map f — arg-bearing method receiver wraps
        let mm = LeanTerm::method(
            LeanTerm::method(a("xs"), "map", vec![a("g")]),
            "map",
            vec![a("f")],
        );
        assert_eq!(render_top(&mm), "(xs.map g).map f");
        // ys.drop (n - xs.length) — infix method arg wraps
        let d = LeanTerm::method(
            a("ys"),
            "drop",
            vec![LeanTerm::infix(
                "-",
                prec::ADD,
                a("n"),
                LeanTerm::method(a("xs"), "length", vec![]),
            )],
        );
        assert_eq!(render_top(&d), "ys.drop (n - xs.length)");
    }

    #[test]
    fn nested_eq_wraps_both_operands() {
        // (ys = zs) as an operand of another eq → parenthesized
        let inner = LeanTerm::infix("=", prec::EQ, a("ys"), a("zs"));
        let outer = LeanTerm::infix("=", prec::EQ, inner.clone(), inner);
        assert_eq!(render_top(&outer), "(ys = zs) = (ys = zs)");
    }
}
