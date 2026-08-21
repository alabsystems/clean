// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Reader C**: the ELABORATED KERNEL TERM read back into a core module.
//!
//! This is the reader that keeps the minter out of the trusted base. It does
//! not look at the minted text, the fixture, or anything the minter produced;
//! it looks at the `Expr` that `Specification::new()` actually registered under
//! `<prefix>_module` — the object every downstream theorem is about — and
//! reconstructs the core module from it. If the minter wrote `IRBinOp.or_`
//! where the artifact had `and`, this reader reads `or` back and the two core
//! modules differ.
//!
//! Fail-closed with NO default arm: a term that is not exactly the constructor
//! application the shape table declares is a [`DecodeError`], never a guess.
//!
//! Reduction here is deliberately a 30-line delta+beta unfolder rather than the
//! kernel's `whnf`: the decoder is meant to be an independent reader, and one
//! that borrowed the kernel's reducer could share a defect with the semantics
//! it is checking against.

use clean_kernel::{Environment, Expr, ExprKind, Literal, Name};

use super::core::Sx;
use super::error::DecodeError;
use super::shape::{self, Arg};
use super::tags::Tags;

/// Decode the registered `<prefix>_module` back into a core module.
///
/// `tags` maps the crate-level interning ids the registered term carries back
/// to the canonical first-use indices the core module uses. An id the table
/// does not list is a hard refusal: either the artifact was re-interned and the
/// table needs a reviewed update, or the term is about a different type.
///
/// # Errors
/// Returns [`DecodeError`] when the constant is absent, has no value, its
/// delta-normalized term is not a core module, or it names an aggregate the tag
/// table does not list.
pub fn decode(env: &Environment, module_const: &str, tags: &Tags) -> Result<Sx, DecodeError> {
    let ci = env
        .get_const(&Name::from_string(module_const))
        .ok_or_else(|| DecodeError::Missing(module_const.to_string()))?;
    let value = ci
        .value
        .clone()
        .ok_or_else(|| DecodeError::NoValue(module_const.to_string()))?;
    let d = Decoder { env, tags };
    let (funcs, globals) = d.ctor2(&value, "IRModule.mk", "the module")?;
    let fs = d.list(&funcs, "IRFunc", "the function list")?;
    let gs = d.list(&globals, "IRGlobal", "the global list")?;
    if !gs.is_empty() {
        return Err(DecodeError::Shape {
            at: "the global list".into(),
            msg: format!("expected no globals, found {}", gs.len()),
        });
    }
    let mut out = Vec::new();
    for f in &fs {
        out.push(d.func(f)?);
    }
    Ok(Sx::tag(
        "module",
        vec![Sx::tag("funcs", out), Sx::tag("globals", vec![])],
    ))
}

struct Decoder<'a> {
    env: &'a Environment,
    tags: &'a Tags,
}

impl Decoder<'_> {
    /// Delta-unfold the head constant and beta-reduce until the head is a
    /// constructor (a constant with no value) or nothing more can be done.
    fn whnf(&self, e: &Expr) -> Expr {
        let mut cur = e.clone();
        for _ in 0..10_000 {
            let (head, args) = spine(&cur);
            match head.kind() {
                ExprKind::Const(n, _) => {
                    let Some(ci) = self.env.get_const(n) else {
                        return cur;
                    };
                    let Some(v) = ci.value.clone() else {
                        return cur;
                    };
                    cur = apply(v, args);
                }
                ExprKind::Lam(_, _, body) if !args.is_empty() => {
                    let rest = args[1..].to_vec();
                    cur = apply((**body).instantiate(&args[0]), rest);
                }
                ExprKind::MData(_, inner) => cur = apply((**inner).clone(), args),
                _ => return cur,
            }
        }
        cur
    }

    /// The head constructor name and its explicit arguments.
    fn head(&self, e: &Expr, at: &str) -> Result<(String, Vec<Expr>), DecodeError> {
        let w = self.whnf(e);
        let (h, args) = spine(&w);
        match h.kind() {
            ExprKind::Const(n, _) => Ok((n.to_string(), args)),
            other => Err(DecodeError::Shape {
                at: at.to_string(),
                msg: format!("expected a constructor application, found {other:?}"),
            }),
        }
    }

    fn ctor(&self, e: &Expr, name: &str, at: &str, arity: usize) -> Result<Vec<Expr>, DecodeError> {
        let (h, args) = self.head(e, at)?;
        if h != name {
            return Err(DecodeError::Shape {
                at: at.to_string(),
                msg: format!("expected `{name}`, found `{h}`"),
            });
        }
        if args.len() != arity {
            return Err(DecodeError::Shape {
                at: at.to_string(),
                msg: format!("`{name}` takes {arity} argument(s), found {}", args.len()),
            });
        }
        Ok(args)
    }

    fn ctor2(&self, e: &Expr, name: &str, at: &str) -> Result<(Expr, Expr), DecodeError> {
        let a = self.ctor(e, name, at, 2)?;
        Ok((a[0].clone(), a[1].clone()))
    }

    /// `IRList α` — `IRList.nil α` / `IRList.cons α x rest`.
    fn list(&self, e: &Expr, elem: &str, at: &str) -> Result<Vec<Expr>, DecodeError> {
        let mut out = Vec::new();
        let mut cur = e.clone();
        loop {
            let (h, args) = self.head(&cur, at)?;
            match h.as_str() {
                "IRList.nil" => return Ok(out),
                "IRList.cons" => {
                    if args.len() != 3 {
                        return Err(DecodeError::Shape {
                            at: at.to_string(),
                            msg: format!("IRList.cons takes 3 arguments, found {}", args.len()),
                        });
                    }
                    out.push(args[1].clone());
                    cur = args[2].clone();
                }
                other => {
                    return Err(DecodeError::Shape {
                        at: at.to_string(),
                        msg: format!("expected an `IRList {elem}`, found `{other}`"),
                    })
                }
            }
        }
    }

    fn nat(&self, e: &Expr, at: &str) -> Result<u128, DecodeError> {
        let mut n = 0u128;
        let mut cur = e.clone();
        loop {
            // A `Nat` LITERAL is a `Nat`. Clean's parser elaborates `1000` to
            // `ExprKind::Lit(Literal::Nat(..))` rather than to a
            // thousand-deep `Nat.succ` tower, and the minter emits a literal
            // for every machine DATUM outside the `ir_d0..ir_d16` atom pool
            // (`shape::Arg::Data`). Reading it here is what keeps this reader
            // independent of the minter's numeral policy rather than blind to
            // it: a decoder that refused a literal would report "not a Nat" for
            // a term that is one, and the gate would read as a mint defect.
            //
            // Exact, and fail-closed above `u128`: `to_u64` returning `None`
            // means the literal has more than one limb, and no width or
            // constant in the fragment does.
            let w = self.whnf(&cur);
            if let Some(v) = nat_literal(&w) {
                return Ok(n + u128::from(v));
            }
            let (h, args) = self.head(&cur, at)?;
            match h.as_str() {
                "Nat.zero" => return Ok(n),
                "Nat.succ" if args.len() == 1 => {
                    n += 1;
                    cur = args[0].clone();
                }
                other => {
                    return Err(DecodeError::Shape {
                        at: at.to_string(),
                        msg: format!("expected a `Nat`, found `{other}`"),
                    })
                }
            }
        }
    }

    fn flag(&self, e: &Expr, at: &str) -> Result<&'static str, DecodeError> {
        let (h, _) = self.head(e, at)?;
        match h.as_str() {
            "Bool.true" => Ok("true"),
            "Bool.false" => Ok("false"),
            other => Err(DecodeError::Shape {
                at: at.to_string(),
                msg: format!("expected a `Bool`, found `{other}`"),
            }),
        }
    }

    fn nat_list(&self, e: &Expr, at: &str) -> Result<Vec<Sx>, DecodeError> {
        self.list(e, "Nat", at)?
            .iter()
            .map(|x| Ok(Sx::a(self.nat(x, at)?.to_string())))
            .collect()
    }

    fn func(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let a = self.ctor(e, "IRFunc.mk", "the function", 4)?;
        let blocks = self.list(&a[3], "IRBlock", "the block list")?;
        let mut bs = Vec::new();
        for b in &blocks {
            bs.push(self.block(b)?);
        }
        Ok(Sx::tag(
            "func",
            vec![
                Sx::a(self.nat(&a[0], "the function id")?.to_string()),
                Sx::tag("params", self.nat_list(&a[1], "the function parameters")?),
                Sx::tag(
                    "entry",
                    vec![Sx::a(self.nat(&a[2], "the entry block")?.to_string())],
                ),
                Sx::tag("blocks", bs),
            ],
        ))
    }

    fn block(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let a = self.ctor(e, "IRBlock.mk", "a block", 3)?;
        let nodes = self.list(&a[2], "IRNode", "a block body")?;
        let mut ns = Vec::new();
        for n in &nodes {
            let na = self.ctor(n, "IRNode.mk", "a node", 2)?;
            ns.push(Sx::tag(
                "node",
                vec![
                    Sx::tag("results", self.nat_list(&na[1], "a node's results")?),
                    self.inst(&na[0])?,
                ],
            ));
        }
        Ok(Sx::tag(
            "block",
            vec![
                Sx::a(self.nat(&a[0], "a block id")?.to_string()),
                Sx::tag("params", self.nat_list(&a[1], "a block's parameters")?),
                Sx::tag("nodes", ns),
            ],
        ))
    }

    fn inst(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let (h, args) = self.head(e, "an instruction")?;
        let sh = shape::INSTS
            .iter()
            .find(|s| s.clean == h)
            .ok_or_else(|| DecodeError::Shape {
                at: "an instruction".into(),
                msg: format!("`{h}` is not one of the 28 declared IRInst constructors"),
            })?;
        if args.len() != sh.args.len() {
            return Err(DecodeError::Shape {
                at: sh.core.to_string(),
                msg: format!("takes {} argument(s), found {}", sh.args.len(), args.len()),
            });
        }
        let mut out = Vec::new();
        for (kind, a) in sh.args.iter().zip(&args) {
            out.push(self.arg(*kind, a, sh.core)?);
        }
        Ok(Sx::tag(sh.core, out))
    }

    fn arg(&self, kind: Arg, e: &Expr, at: &str) -> Result<Sx, DecodeError> {
        Ok(match kind {
            Arg::Ty => self.ty(e)?,
            Arg::Val | Arg::Blk | Arg::Nat | Arg::Data => Sx::a(self.nat(e, at)?.to_string()),
            Arg::Flag => Sx::a(self.flag(e, at)?),
            Arg::Vals(head) => Sx::tag(head, self.nat_list(e, at)?),
            Arg::Cases => {
                let cs = self.list(e, "IRSwitchCase", "the switch arms")?;
                let mut out = Vec::new();
                for c in &cs {
                    let ca = self.ctor(c, "IRSwitchCase.mk", "a switch arm", 3)?;
                    out.push(Sx::tag(
                        "case",
                        vec![
                            Sx::a(self.nat(&ca[0], "a switch case value")?.to_string()),
                            Sx::a(self.nat(&ca[1], "a switch case target")?.to_string()),
                            Sx::tag("args", self.nat_list(&ca[2], "a switch case's arguments")?),
                        ],
                    ));
                }
                Sx::tag("cases", out)
            }
            Arg::Const => self.cst(e)?,
            Arg::OptVal => {
                let (h, a) = self.head(e, at)?;
                match h.as_str() {
                    "IROption.none" => Sx::tag("none", vec![]),
                    "IROption.some" if a.len() == 2 => {
                        Sx::tag("some", vec![Sx::a(self.nat(&a[1], at)?.to_string())])
                    }
                    other => {
                        return Err(DecodeError::Shape {
                            at: at.to_string(),
                            msg: format!("expected an `IROption Nat`, found `{other}`"),
                        })
                    }
                }
            }
            Arg::Op(alpha) => {
                let (h, _) = self.head(e, at)?;
                shape::alphabet(alpha)
                    .iter()
                    .find(|(_, k)| *k == h)
                    .map(|(c, _)| Sx::a(*c))
                    .ok_or_else(|| DecodeError::Shape {
                        at: at.to_string(),
                        msg: format!("`{h}` is not a declared {alpha} operator"),
                    })?
            }
        })
    }

    fn ty(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let (h, args) = self.head(e, "a type")?;
        // Aggregates come back through the tag table, so the core module the
        // decoder produces speaks canonical first-use indices exactly as reader
        // A's does — and an id the table does not list refuses rather than
        // silently becoming a canonical index of its own.
        if h == "IRTy.enum_" || h == "IRTy.struct_" {
            if args.len() != 1 {
                return Err(DecodeError::Shape {
                    at: "an aggregate type".into(),
                    msg: format!("`{h}` takes 1 argument, found {}", args.len()),
                });
            }
            let raw = u32::try_from(self.nat(&args[0], "an aggregate id")?).map_err(|_| {
                DecodeError::Shape {
                    at: "an aggregate type".into(),
                    msg: "the aggregate id does not fit u32".into(),
                }
            })?;
            let (core, canonical) = if h == "IRTy.enum_" {
                ("enum", self.tags.enum_canonical(raw)?)
            } else {
                ("struct", self.tags.struct_canonical(raw)?)
            };
            return Ok(Sx::tag(core, vec![Sx::a(canonical.to_string())]));
        }
        let sh = shape::TYS
            .iter()
            .find(|s| s.clean == h)
            .ok_or_else(|| DecodeError::Shape {
                at: "a type".into(),
                msg: format!("`{h}` is not one of the 18 declared IRTy constructors"),
            })?;
        if args.len() != sh.args.len() {
            return Err(DecodeError::Shape {
                at: sh.core.to_string(),
                msg: format!("takes {} argument(s), found {}", sh.args.len(), args.len()),
            });
        }
        let mut out = Vec::new();
        for (kind, a) in sh.args.iter().zip(&args) {
            out.push(self.arg(*kind, a, sh.core)?);
        }
        Ok(Sx::tag(sh.core, out))
    }

    fn cst(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let (h, args) = self.head(e, "a constant")?;
        if h == "IRConst.aggv" {
            if args.len() != 1 {
                return Err(DecodeError::Shape {
                    at: "agg".into(),
                    msg: format!("IRConst.aggv takes 1 argument, found {}", args.len()),
                });
            }
            let mut elems = Vec::new();
            let mut cur = args[0].clone();
            loop {
                let (sh, sa) = self.head(&cur, "a constant element spine")?;
                match sh.as_str() {
                    "IRConst.vnil" => break,
                    "IRConst.vcons" if sa.len() == 2 => {
                        elems.push(self.cst(&sa[0])?);
                        cur = sa[1].clone();
                    }
                    other => {
                        return Err(DecodeError::Shape {
                            at: "agg".into(),
                            msg: format!("expected a vnil/vcons element spine, found `{other}`"),
                        })
                    }
                }
            }
            return Ok(Sx::tag("agg", elems));
        }
        let sh = shape::CONSTS
            .iter()
            .find(|s| s.clean == h)
            .ok_or_else(|| DecodeError::Shape {
                at: "a constant".into(),
                msg: format!("`{h}` is not a declared IRConst constructor"),
            })?;
        if args.len() != sh.args.len() {
            return Err(DecodeError::Shape {
                at: sh.core.to_string(),
                msg: format!("takes {} argument(s), found {}", sh.args.len(), args.len()),
            });
        }
        let mut out = Vec::new();
        for (kind, a) in sh.args.iter().zip(&args) {
            out.push(self.arg(*kind, a, sh.core)?);
        }
        Ok(Sx::tag(sh.core, out))
    }
}

/// Split an application into its head and its arguments, left to right.
/// The value of a `Nat` NUMERAL, in either shape Clean's elaborator produces.
///
/// A numeral in registered source does NOT arrive as a bare `ExprKind::Lit`: it
/// is elaborated through the `OfNat` class, so `127` becomes
/// `Proj(OfNat, 0, instOfNatNat 127)` — the projection of the instance
/// structure's field. The bare literal shape occurs too, so both are read and
/// **nothing else is**: this is a two-case reader, not a search for any `Lit`
/// buried in a term, because a looser rule would happily read the wrong number
/// out of a term that merely mentions one.
///
/// Added 2026-08-20 with the eleventh chain, which is the first whose module
/// names a numeral outside the `ir_d0..ir_d16` atom pool (`IRTy.enum_ 127`,
/// `IRTy.uint_ 32`, `IRConst.int_ 1000`). Before it, every numeral in every
/// registered module was an `ir_dN` constant that delta-unfolds to a
/// `Nat.succ` tower, which is why this reader only knew that shape.
fn nat_literal(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(b)) => b.to_u64(),
        ExprKind::Proj(name, 0, inner) if name.to_string() == "OfNat" => {
            let (head, args) = spine(inner);
            match head.kind() {
                ExprKind::Const(n, _) if n.to_string() == "instOfNatNat" && args.len() == 1 => {
                    match args[0].kind() {
                        ExprKind::Lit(Literal::Nat(b)) => b.to_u64(),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    loop {
        match cur.kind().clone() {
            ExprKind::App(f, a) => {
                args.push((*a).clone());
                cur = (*f).clone();
            }
            ExprKind::MData(_, inner) => cur = (*inner).clone(),
            _ => {
                args.reverse();
                return (cur, args);
            }
        }
    }
}

/// Apply `f` to `args`, beta-reducing where the function is already a lambda.
fn apply(f: Expr, args: Vec<Expr>) -> Expr {
    let mut cur = f;
    for a in args {
        cur = match cur.kind().clone() {
            ExprKind::Lam(_, _, body) => (*body).instantiate(&a),
            _ => Expr::app(cur, a),
        };
    }
    cur
}
