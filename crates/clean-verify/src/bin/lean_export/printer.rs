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
//!   same primitive projections. Nat literals print as NUMERALS over the
//!   bridged carrier (`CleanVerify.Nat` is a reducible alias of Lean's `Nat`;
//!   see `emit.rs::emit_nat_carrier`), which is what Clean's kernel actually
//!   does with them — its Nat reduction is native on `BigNat` and name-keyed,
//!   so a succ-tower over a MIRROR Nat demanded a computation Clean never
//!   performs. See the `Lit(Nat(_))` arm for the measurement that settles it.
//! - Remaining unprintable forms (string literals, free variables, mode
//!   extensions) return an error so the caller can SKIP honestly.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use clean_kernel::{Expr, ExprKind, Level, Literal, Name};

pub const NAMESPACE: &str = "CleanVerify";

pub(crate) struct Printer<'a> {
    /// Clean-name -> Lean-name remaps (reserved-name collisions).
    pub renames: &'a HashMap<String, String>,
    /// Inductives emitted as Lean `structure`s (field access is printable).
    pub structs: &'a HashSet<String>,
    /// Fresh binder counter (per emitted declaration).
    pub next_var: usize,
}

impl<'a> Printer<'a> {
    pub(crate) fn new(renames: &'a HashMap<String, String>, structs: &'a HashSet<String>) -> Self {
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
    pub(crate) fn const_ref(&self, n: &Name) -> String {
        let s = n.to_string();
        let mapped = self.renames.get(&s).cloned().unwrap_or(s);
        format!("{NAMESPACE}.{}", escape_name(&mapped))
    }

    /// Print an expression. `ctx` maps de Bruijn depth to binder names
    /// (innermost last).
    pub(crate) fn expr(&mut self, e: &Expr, ctx: &mut Vec<String>) -> Result<String, String> {
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
            // A Nat literal prints as a NUMERAL, over the bridged carrier
            // (`CleanVerify.Nat` is a reducible alias of Lean's `Nat`, see
            // emit.rs `emit_nat_carrier`). It used to print as a succ-tower
            // over a MIRROR Nat, capped at 4096, and that was wrong in a way
            // the cap concealed rather than caused.
            //
            // Clean's kernel never walks these unary. Its Nat acceleration is
            // NAME-KEYED — `names::NAT_ADD`/`NAT_SUB`/`NAT_PRED` in
            // `clean-kernel/src/tc/reduction/mod.rs`, dispatched from `nat.rs`,
            // and `whnf` runs `reduce_nat` BEFORE delta — so a closed literal
            // folds natively on BigNat. The spec says so about itself:
            // `core_spec/eval_ir_float.rs:174-177` writes 2^63 as a literal
            // "so the kernel folds it natively on BigNat; a unary numeral of
            // this magnitude does not exist."
            //
            // Prefixing `CleanVerify.` switched that acceleration off, so the
            // export was not replaying what Clean's kernel did — it was
            // demanding something strictly harder. MEASURED on the mirror with
            // the best possible encoding (so it is a floor no encoding beats):
            // 2.75e-5 s and ~6.3 KB RSS per unit of VALUE, exactly 2x per
            // doubling over 4096..65536. Extrapolated, 4294967295 costs 33 h
            // and 27 TB; 2^63 costs 7.9 million years. Raising the cap, a
            // logarithmic encoding and an `OfNat` instance are all dead on that
            // measurement, and a half-bridge (Lean's carrier, the spec's unary
            // bodies) blows `maxRecDepth` on every blocked obligation: the axis
            // is the OPERATION NAME, not the numeral.
            //
            // `BigNat`'s own `Display` (`clean-kernel/src/expr/types.rs:421`)
            // is already a valid Lean numeral in both arms — decimal for
            // `Small`, `0x`-prefixed big-endian limbs for `Big`. Verified
            // against Lean rather than assumed, including that the limb order
            // and the leading zeros are right: 2^64, [1,0,1] and 2^128-1 all
            // check by `rfl` against independently computed decimals. This also
            // reaches values `to_u64()` cannot (`expr/types.rs` returns `None`
            // for `Big`), which no cap could ever have admitted.
            ExprKind::Lit(Literal::Nat(n)) => Ok(n.to_string()),
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
    pub(crate) fn telescope<'e>(
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
pub(crate) fn escape_name(s: &str) -> String {
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
pub(crate) fn level_atom(l: &Level) -> String {
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
pub(crate) fn level_params_suffix(params: &[Name]) -> String {
    if params.is_empty() {
        String::new()
    } else {
        let names: Vec<String> = params.iter().map(|n| escape_name(&n.to_string())).collect();
        format!(".{{{}}}", names.join(", "))
    }
}
