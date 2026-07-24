// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel `Expr`/`Level` -> Lean 4 surface syntax.
//!
//! Fidelity rules:
//! - Prints the elaborated kernel term structure verbatim: every binder is
//!   printed EXPLICIT (kernel terms carry all arguments positionally; binder
//!   info is elaboration sugar), every application is positional.
//! - Constant references are printed `@CleanVerify.<name>` (fully explicit),
//!   with universe instantiations left for Lean to re-infer (Lean's own
//!   auto-generated recursors may order universe params differently; values
//!   are pinned by the fully-explicit arguments).
//! - Binder names are fresh `x_N` (Clean's kernel binders are nameless de
//!   Bruijn); `x_N` never collides with exported constants (asserted upstream).
//! - Kernel projections `Proj(S, i, e)` print as Lean structure field access
//!   `(e).pf<i>` — valid only for inductives the emitter declared as Lean
//!   `structure`s (the `structs` set), whose auto-generated accessors are the
//!   same primitive projections. Nat literals print in constructor normal
//!   form (`Nat.succ^n Nat.zero` over the mirror `Nat`), the form Clean's
//!   kernel treats the literal as definitionally equal to; capped so a huge
//!   literal is SKIPPED rather than emitted as a megabyte tower.
//! - Remaining unprintable forms (string literals, free variables, mode
//!   extensions) return an error so the caller can SKIP honestly.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use clean_kernel::{Expr, ExprKind, Level, Literal, Name};

pub const NAMESPACE: &str = "CleanVerify";

/// Largest Nat literal printed in constructor normal form. Above this, the
/// succ-tower is unreasonably large and the item is skipped honestly.
const MAX_NAT_LITERAL: u64 = 4096;

pub struct Printer<'a> {
    /// Clean-name -> Lean-name remaps (reserved-name collisions).
    pub renames: &'a HashMap<String, String>,
    /// Inductives emitted as Lean `structure`s (field access is printable).
    pub structs: &'a HashSet<String>,
    /// Fresh binder counter (per emitted declaration).
    pub next_var: usize,
}

impl<'a> Printer<'a> {
    pub fn new(renames: &'a HashMap<String, String>, structs: &'a HashSet<String>) -> Self {
        Printer {
            renames,
            structs,
            next_var: 0,
        }
    }

    fn fresh(&mut self) -> String {
        let v = format!("x_{}", self.next_var);
        self.next_var += 1;
        v
    }

    /// Print a constant reference (without `@`), namespaced and renamed.
    pub fn const_ref(&self, n: &Name) -> String {
        let s = n.to_string();
        let mapped = self.renames.get(&s).cloned().unwrap_or(s);
        format!("{NAMESPACE}.{}", escape_name(&mapped))
    }

    /// Print an expression. `ctx` maps de Bruijn depth to binder names
    /// (innermost last).
    pub fn expr(&mut self, e: &Expr, ctx: &mut Vec<String>) -> Result<String, String> {
        match e.kind() {
            ExprKind::BVar(i) => {
                let i = *i as usize;
                if i >= ctx.len() {
                    return Err(format!("loose bvar #{i} (ctx depth {})", ctx.len()));
                }
                Ok(ctx[ctx.len() - 1 - i].clone())
            }
            // Always parenthesized: `Sort u` in argument position must group.
            ExprKind::Sort(l) => Ok(format!("(Sort {})", level_atom(l))),
            ExprKind::Const(n, _levels) => Ok(format!("@{}", self.const_ref(n))),
            ExprKind::App(_, _) => {
                // Collect the application spine iteratively.
                let mut args = Vec::new();
                let mut head = e;
                while let ExprKind::App(f, a) = head.kind() {
                    args.push(a.as_ref());
                    head = f;
                }
                args.reverse();
                let mut s = String::from("(");
                s.push_str(&self.expr(head, ctx)?);
                for a in args {
                    s.push(' ');
                    s.push_str(&self.expr(a, ctx)?);
                }
                s.push(')');
                Ok(s)
            }
            ExprKind::Lam(_, ty, body) => {
                let t = self.expr(ty, ctx)?;
                let v = self.fresh();
                ctx.push(v.clone());
                let b = self.expr(body, ctx);
                ctx.pop();
                Ok(format!("(fun ({v} : {t}) => {})", b?))
            }
            ExprKind::Pi(_, ty, body) => {
                let t = self.expr(ty, ctx)?;
                let v = self.fresh();
                ctx.push(v.clone());
                let b = self.expr(body, ctx);
                ctx.pop();
                Ok(format!("(({v} : {t}) -> {})", b?))
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let t = self.expr(ty, ctx)?;
                let vv = self.expr(val, ctx)?;
                let v = self.fresh();
                ctx.push(v.clone());
                let b = self.expr(body, ctx);
                ctx.pop();
                Ok(format!("(let {v} : {t} := {vv}; {})", b?))
            }
            ExprKind::MData(_, inner) => self.expr(inner, ctx),
            ExprKind::Lit(Literal::Nat(n)) => match n.to_u64() {
                Some(v) if v <= MAX_NAT_LITERAL => {
                    // Constructor normal form over the mirror Nat — the form
                    // Clean's kernel holds the literal definitionally equal to.
                    let zero = format!("@{}", self.const_ref(&Name::from_string("Nat.zero")));
                    let succ = format!("@{}", self.const_ref(&Name::from_string("Nat.succ")));
                    let mut s = zero;
                    for _ in 0..v {
                        s = format!("({succ} {s})");
                    }
                    Ok(s)
                }
                _ => Err(format!(
                    "literal Nat({n:?}) exceeds ctor-normal-form cap {MAX_NAT_LITERAL}"
                )),
            },
            ExprKind::Lit(l) => Err(format!("literal {l:?} not exportable")),
            ExprKind::Proj(n, i, inner) => {
                if self.structs.contains(&n.to_string()) {
                    // Field access on an inductive emitted as a Lean
                    // `structure`; Lean's auto-generated `pf<i>` accessor is
                    // the same primitive projection.
                    let e = self.expr(inner, ctx)?;
                    Ok(format!("(({e}).pf{i})"))
                } else {
                    Err(format!("kernel projection {n}.{i} not exportable"))
                }
            }
            ExprKind::FVar(_) => Err("free variable in exported term".to_string()),
            other => Err(format!("non-core expression form {other:?}")),
        }
    }

    /// Print a Pi telescope's first `n` binders as Lean binder groups,
    /// returning (binder_string, remainder_expr, binder_names_pushed).
    /// Used for inductive headers and constructor parameter stripping.
    pub fn telescope<'e>(
        &mut self,
        e: &'e Expr,
        n: usize,
        ctx: &mut Vec<String>,
        prefix: &str,
    ) -> Result<(String, &'e Expr), String> {
        let mut binders = String::new();
        let mut cur = e;
        for k in 0..n {
            match cur.kind() {
                ExprKind::Pi(_, ty, body) => {
                    let t = self.expr(ty, ctx)?;
                    let v = format!("{prefix}{k}");
                    let _ = write!(binders, " ({v} : {t})");
                    ctx.push(v);
                    cur = body;
                }
                _ => {
                    return Err(format!(
                        "expected {n} leading Pi binders, found non-Pi at {k}"
                    ))
                }
            }
        }
        Ok((binders, cur))
    }
}

/// Lean 4 keywords that cannot appear bare as a name component.
const LEAN_KEYWORDS: [&str; 30] = [
    "theorem",
    "def",
    "axiom",
    "inductive",
    "structure",
    "class",
    "instance",
    "fun",
    "match",
    "with",
    "let",
    "have",
    "show",
    "from",
    "by",
    "at",
    "in",
    "do",
    "then",
    "else",
    "if",
    "end",
    "open",
    "mutual",
    "where",
    "deriving",
    "variable",
    "universe",
    "section",
    "namespace",
];

/// Escape each dot-component of a name that is not a plain Lean identifier.
pub fn escape_name(s: &str) -> String {
    s.split('.')
        .map(|c| {
            let ok = !c.is_empty()
                && !LEAN_KEYWORDS.contains(&c)
                && c.chars()
                    .next()
                    .is_some_and(|f| f.is_alphabetic() || f == '_')
                && c.chars()
                    .all(|ch| ch.is_alphanumeric() || ch == '_' || ch == '\'');
            if ok {
                c.to_string()
            } else {
                format!("\u{ab}{c}\u{bb}") // «c»
            }
        })
        .collect::<Vec<_>>()
        .join(".")
}

/// Print a universe level as a Lean level ATOM (parenthesized if compound).
pub fn level_atom(l: &Level) -> String {
    let s = level_str(l);
    if s.chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
    {
        s
    } else {
        format!("({s})")
    }
}

fn level_str(l: &Level) -> String {
    // Peel successor applications onto a numeric offset.
    let mut offset = 0u64;
    let mut cur = l;
    while let Level::Succ(inner) = cur {
        offset += 1;
        cur = inner;
    }
    match cur {
        Level::Zero => format!("{offset}"),
        Level::Param(n) => {
            if offset == 0 {
                escape_name(&n.to_string())
            } else {
                format!("{}+{offset}", escape_name(&n.to_string()))
            }
        }
        Level::Max(a, b) => {
            let base = format!("max {} {}", level_atom(a), level_atom(b));
            if offset == 0 {
                base
            } else {
                format!("({base})+{offset}")
            }
        }
        Level::IMax(a, b) => {
            let base = format!("imax {} {}", level_atom(a), level_atom(b));
            if offset == 0 {
                base
            } else {
                format!("({base})+{offset}")
            }
        }
        Level::Succ(_) => unreachable!("successors peeled above"),
    }
}

/// Print a `.{u, v}` universe-parameter binder suffix (empty if none).
pub fn level_params_suffix(params: &[Name]) -> String {
    if params.is_empty() {
        String::new()
    } else {
        let names: Vec<String> = params.iter().map(|n| escape_name(&n.to_string())).collect();
        format!(".{{{}}}", names.join(", "))
    }
}
