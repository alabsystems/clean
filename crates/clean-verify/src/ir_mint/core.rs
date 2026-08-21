// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The CORE MODULE: the object all three readers of the A2 gate produce.
//!
//! A core module is exactly the fragment of `trust_ir::Module` that Clean's
//! `IRModule` can encode, written in one canonical text form. It is carried as
//! a generic S-expression rather than as a bespoke enum on purpose: the SHAPE
//! of every instruction is declared once, in [`super::shape`], and that one
//! table drives the reader, the printer, the minter and the decoder. Two
//! readers therefore cannot disagree about an instruction's arity or field
//! order — only about its content, which is what the gate is for.
//!
//! ## The canonical form, and what it normalizes
//!
//! Normalized (declared, and each one measured — see the module docs of
//! [`super`]):
//!
//! * **Crate-level interning ids** — `enum.N`, `struct.N`, `func.N`,
//!   `global.N` — are renumbered densely by FIRST USE in canonical traversal
//!   order. These are the ids that move under a producer change with zero
//!   instructions changed.
//! * **SSA value ids** are the producer's OWN canonical dense renumbering
//!   (`trust_ir::format::canonicalize`: block parameters in block-id order,
//!   then instruction results in program order). Not a rule invented here.
//! * **The function id** of the projected body is 0.
//!
//! Erased (declared): spans, value names, producer tags, proof annotations,
//! scopes, `align`, the function-type id, parameter TYPES, block-parameter
//! TYPES, calling convention, linkage, attrs, summary. Clean's `IRModule`
//! encodes none of them, so a gate over this form cannot see them; that is a
//! statement about the fragment, not a silent drop.
//!
//! `?` is a legal atom in one position only: a flag a reader could not
//! witness. It never survives into a minted module — [`super::mint`] refuses
//! it.

use std::fmt::Write as _;

use super::error::CoreError;

/// A parsed core-module S-expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sx {
    /// A bare token.
    Atom(String),
    /// A parenthesised list.
    List(Vec<Sx>),
}

impl Sx {
    /// The atom's text, or an error naming what was found instead.
    ///
    /// # Errors
    /// Returns [`CoreError::Shape`] when this node is a list.
    pub(crate) fn atom(&self) -> Result<&str, CoreError> {
        match self {
            Self::Atom(a) => Ok(a),
            Self::List(_) => Err(CoreError::Shape("expected an atom, found a list".into())),
        }
    }

    /// The list's elements, or an error naming what was found instead.
    ///
    /// # Errors
    /// Returns [`CoreError::Shape`] when this node is an atom.
    pub(crate) fn list(&self) -> Result<&[Sx], CoreError> {
        match self {
            Self::List(l) => Ok(l),
            Self::Atom(a) => Err(CoreError::Shape(format!(
                "expected a list, found atom `{a}`"
            ))),
        }
    }

    /// A `(head ...)` list whose head atom is `head`, returning the tail.
    ///
    /// # Errors
    /// Returns [`CoreError::Shape`] when the node is not such a list.
    pub fn tagged(&self, head: &str) -> Result<&[Sx], CoreError> {
        let l = self.list()?;
        let Some(first) = l.first() else {
            return Err(CoreError::Shape(format!("expected ({head} ...), found ()")));
        };
        if first.atom()? != head {
            return Err(CoreError::Shape(format!(
                "expected ({head} ...), found ({} ...)",
                first.atom()?
            )));
        }
        Ok(&l[1..])
    }

    /// A `u128` atom.
    ///
    /// # Errors
    /// Returns [`CoreError::Shape`] when the atom is not a canonical decimal.
    pub fn num(&self) -> Result<u128, CoreError> {
        let a = self.atom()?;
        a.parse::<u128>()
            .map_err(|_| CoreError::Shape(format!("expected a decimal number, found `{a}`")))
    }

    /// Build `(head a b ...)`.
    #[must_use]
    pub(crate) fn tag(head: &str, rest: Vec<Sx>) -> Self {
        let mut v = vec![Sx::Atom(head.to_string())];
        v.extend(rest);
        Sx::List(v)
    }

    /// Build a bare atom.
    #[must_use]
    pub(crate) fn a(s: impl Into<String>) -> Self {
        Sx::Atom(s.into())
    }
}

/// Tokenize and parse a core-module text into one S-expression.
///
/// Fail-closed: unbalanced parens, trailing text after the top-level form and
/// an empty input are all errors. There is no recovery mode.
///
/// # Errors
/// Returns [`CoreError::Shape`] on any malformed input.
pub fn parse(text: &str) -> Result<Sx, CoreError> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        match ch {
            '(' | ')' => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
                toks.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    let mut pos = 0usize;
    let sx = parse_at(&toks, &mut pos)?;
    if pos != toks.len() {
        return Err(CoreError::Shape(format!(
            "trailing text after the top-level form ({} token(s) left)",
            toks.len() - pos
        )));
    }
    Ok(sx)
}

fn parse_at(toks: &[String], pos: &mut usize) -> Result<Sx, CoreError> {
    let Some(t) = toks.get(*pos) else {
        return Err(CoreError::Shape("unexpected end of input".into()));
    };
    *pos += 1;
    match t.as_str() {
        "(" => {
            let mut items = Vec::new();
            loop {
                let Some(nxt) = toks.get(*pos) else {
                    return Err(CoreError::Shape("unclosed `(`".into()));
                };
                if nxt == ")" {
                    *pos += 1;
                    return Ok(Sx::List(items));
                }
                items.push(parse_at(toks, pos)?);
            }
        }
        ")" => Err(CoreError::Shape("unexpected `)`".into())),
        other => Ok(Sx::Atom(other.to_string())),
    }
}

/// Render an S-expression on one line, with single spaces.
#[must_use]
pub(crate) fn flat(sx: &Sx) -> String {
    match sx {
        Sx::Atom(a) => a.clone(),
        Sx::List(l) => {
            let parts: Vec<String> = l.iter().map(flat).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// Print a core module in the ONE canonical layout.
///
/// Byte-for-byte round-tripping (`print(parse(t)) == t`) is what makes the
/// reader a checked component rather than a trusted one: a reader that dropped
/// a field could not print it back.
///
/// # Errors
/// Returns [`CoreError::Shape`] when `sx` is not a well-formed core module.
pub fn print(sx: &Sx) -> Result<String, CoreError> {
    let body = sx.tagged("module")?;
    if body.len() != 2 {
        return Err(CoreError::Shape(format!(
            "(module ...) takes exactly (funcs ...) and (globals ...), found {} item(s)",
            body.len()
        )));
    }
    let funcs = body[0].tagged("funcs")?;
    let globals = body[1].tagged("globals")?;
    let mut out = String::from("(module\n  (funcs\n");
    for f in funcs {
        print_func(&mut out, f)?;
    }
    out.push_str("  )\n");
    if globals.is_empty() {
        out.push_str("  (globals)\n");
    } else {
        out.push_str("  (globals");
        for g in globals {
            let _ = write!(out, " {}", flat(g));
        }
        out.push_str(")\n");
    }
    out.push_str(")\n");
    Ok(out)
}

fn print_func(out: &mut String, f: &Sx) -> Result<(), CoreError> {
    let items = f.tagged("func")?;
    if items.len() != 4 {
        return Err(CoreError::Shape(format!(
            "(func id (params ..) (entry n) (blocks ..)) takes 4 items, found {}",
            items.len()
        )));
    }
    let _ = writeln!(out, "    (func {}", items[0].atom()?);
    let _ = writeln!(out, "      {}", flat(&items[1]));
    let _ = writeln!(out, "      {}", flat(&items[2]));
    out.push_str("      (blocks\n");
    for b in items[3].tagged("blocks")? {
        print_block(out, b)?;
    }
    out.push_str("      ))\n");
    Ok(())
}

fn print_block(out: &mut String, b: &Sx) -> Result<(), CoreError> {
    let items = b.tagged("block")?;
    if items.len() != 3 {
        return Err(CoreError::Shape(format!(
            "(block id (params ..) (nodes ..)) takes 3 items, found {}",
            items.len()
        )));
    }
    let _ = writeln!(out, "        (block {}", items[0].atom()?);
    let _ = writeln!(out, "          {}", flat(&items[1]));
    out.push_str("          (nodes\n");
    for n in items[2].tagged("nodes")? {
        let ni = n.tagged("node")?;
        if ni.len() != 2 {
            return Err(CoreError::Shape(format!(
                "(node (results ..) INST) takes 2 items, found {}",
                ni.len()
            )));
        }
        let _ = writeln!(out, "            (node {} {})", flat(&ni[0]), flat(&ni[1]));
    }
    out.push_str("          ))\n");
    Ok(())
}

/// The canonical content digest of a core module: BLAKE3 over the canonical
/// text under a versioned domain tag.
#[must_use]
pub fn digest(canonical_text: &str) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"clean.ir_mint.core.v1\0");
    h.update(canonical_text.as_bytes());
    h.finalize().to_hex().to_string()
}

/// Walk every node of a core module in canonical order, calling `f` with each
/// `(block_id, node_index, inst)`.
///
/// # Errors
/// Returns [`CoreError::Shape`] when the module is malformed.
pub fn for_each_inst<F>(sx: &Sx, mut f: F) -> Result<(), CoreError>
where
    F: FnMut(&str, usize, &Sx) -> Result<(), CoreError>,
{
    for func in sx.tagged("module")?[0].tagged("funcs")? {
        let items = func.tagged("func")?;
        for b in items[3].tagged("blocks")? {
            let bi = b.tagged("block")?;
            let bid = bi[0].atom()?;
            for (i, n) in bi[2].tagged("nodes")?.iter().enumerate() {
                let ni = n.tagged("node")?;
                f(bid, i, &ni[1])?;
            }
        }
    }
    Ok(())
}
