// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Reader B's MODULE-TABLE PREAMBLE**: the `type ty.N = …` and `global …`
//! rows trust-ir's `Display for Module` prints BEFORE the first function, read
//! into the `(global k <agg>)` entries `project` splices into the core module.
//! This file is the READER of that grammar only; the comparison of what it read
//! against the tag table's `globals` lane is `interface_globals::check_globals`.
//!
//! Until 2026-09-09 no chained body addressed a global, reader B refused a
//! `global_addr` outright, and the emitted fixtures carried function bodies
//! only. `ir_lzc` projects `<LevelArc as Deref>::deref`, whose `expect`
//! message the producer promotes to a module-table global
//! (`@__trust_promoted_4557`, 34 bytes of `[ty.0 x 34]` where
//! `type ty.0 = u8`). The two module-table rows that global needs are cut from
//! the dump into a `.trust-ir-rows.txt` fixture, and this module is the reader
//! for exactly that grammar — nothing wider.
//!
//! # What is read, and what is refused by name
//!
//! * `type ty.N = <tok>` — `tok` must be one of the SCALAR tokens reader B's
//!   `ty()` accepts: `bool`, `ptr`, `iN`, `uN`, `fN`. A `struct.N`, `enum.N`,
//!   `usize` (target-dependent) or anything else is refused: the table row is
//!   only ever consulted to resolve an array's element, and an element the
//!   reader has no scalar image for has no `(int a)` image either.
//! * `global [<linkage>] @<name> <ty> = <init>` — the linkage keyword is read
//!   from [`LINKAGES`](super::LINKAGES) with the printer's suppressed default
//!   `external` on absence (the same absence-is-a-value rule the function
//!   header follows). The three other fields `Display for Module` can print
//!   between `global` and `@name` — ` tls(N)`, ` mut`, ` align(N)` — are
//!   REFUSED BY NAME, because Clean's `IRGlobal.mk : Nat → IRConst → IRGlobal`
//!   carries an id and an initializer and nothing else, so none of the three
//!   has a slot to land in and none may be erased in silence. Reader A refuses
//!   the same three in its globals WALK (`scripts/crystal_a2_project/src/main.rs`,
//!   the `module.globals.get(raw)` loop that returns on `mutable` / `tls` /
//!   `align` before it reads the initializer; `global_init` there reads the
//!   initializer only), so a `mut` global cannot reach a core module through
//!   either reader.
//! * `<ty>` must be `[ty.N x LEN]` with `ty.N` a row of the type table, and is
//!   RESOLVED to `[u8 x LEN]` — the form the tag table's `globals` lane pins
//!   as `ty`, because `ty.N` is a whole-crate type-table index and renumbers
//!   like every other crate-level id.
//! * `<init>` must be `array[ a, b, … ]` with EXACTLY `LEN` digit-only
//!   elements, each below `2^width` of the resolved integer element, and reads
//!   as `(agg (int a) (int b) …)`. The list is read as the printer writes it
//!   and nothing looser: an EMPTY element (`array[ 1,, 2 ]`, a trailing comma)
//!   and a NON-CANONICAL numeral (`007`, which would image to the atom
//!   `(int 007)` beside `(int 7)`) are each refused as not the printer's
//!   output. Only `array[ ]` with `LEN` 0 has no element.
//!
//! # Line numbers in refusals
//!
//! A preamble refusal names its FILE line. So does `split_bodies`, which is
//! handed the preamble's line count as a base. The per-body reader that
//! consumes each chunk numbers from the chunk's first line, as it has for
//! every body after the first of a multi-body chain since `has_loose_bvars`;
//! a refusal it raises on a preamble-bearing fixture is therefore
//! BODY-RELATIVE, offset by the preamble and by every earlier body.
//!
//! # The Aggregate/Array rule is a POSITION rule
//!
//! trust-ir has two printed aggregate constants: `{ a, b }` (`Constant::Aggregate`)
//! and `array[ a, b ]` (`Constant::Array`). Clean's `IRConst` has ONE, `aggv`.
//! The image would not be injective if both spellings were accepted in the
//! same position — so they are not. `array[…]` reads ONLY here, as a global
//! initializer, and `{…}` reads ONLY in an instruction constant (`Reader::cst`,
//! which refuses `array[`). A `{…}` initializer on a `global` row is refused
//! by this module for the same reason. No accepted pair collapses, because no
//! position accepts both.

use std::collections::BTreeMap;

use super::core::Sx;
use super::error::{CoreError, EmittedError};
use super::{DEFAULT_LINKAGE, LINKAGES};

/// One `global …` row of the preamble, resolved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct GlobalDecl {
    /// The name after `@`, as the module table spells it.
    pub(super) name: String,
    /// The linkage keyword, `external` when the row prints none.
    pub(super) linkage: String,
    /// The RESOLVED array type, `[u8 x 34]`.
    pub(super) ty: String,
    /// The initializer as `(agg (int a) …)`.
    pub(super) init: Sx,
}

/// The parsed preamble: the type-table rows and the global rows.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Preamble {
    /// `ty.N` -> the scalar token it aliases.
    pub(super) types: BTreeMap<u32, String>,
    /// Every `global …` row, in printed order.
    pub(super) globals: Vec<GlobalDecl>,
}

/// Split the leading module-table rows off an emitted text.
///
/// The preamble is the maximal leading run of lines that are blank or start
/// with `type ty.` or `global `; the rest is returned UNTOUCHED, starting at
/// the first line that is neither, so `split_bodies` sees exactly what it saw
/// before this module existed. A `type`/`global` row that appears AFTER a body
/// is not a preamble and stays refused there as trailing content.
pub(super) fn split_preamble(text: &str) -> (Vec<&str>, &str) {
    let mut lines = Vec::new();
    let mut consumed = 0usize;
    for raw in text.split_inclusive('\n') {
        let line = raw.strip_suffix('\n').unwrap_or(raw);
        let line = line.strip_suffix('\r').unwrap_or(line);
        if !(line.trim().is_empty() || line.starts_with("type ty.") || line.starts_with("global "))
        {
            break;
        }
        lines.push(line);
        consumed += raw.len();
    }
    (lines, &text[consumed..])
}

/// The scalar type tokens a `type ty.N = …` row may alias, with the element
/// width an ARRAY over that scalar checks its digit-only elements against.
/// `None` is a scalar reader B images but this preamble refuses as an array
/// element: `bool`, `ptr` and the floats print no digit-only literal that
/// `(int a)` is the image of.
fn scalar_width(tok: &str) -> Option<Option<u32>> {
    match tok {
        "bool" | "ptr" | "f32" | "f64" => Some(None),
        "i8" | "u8" => Some(Some(8)),
        "i16" | "u16" => Some(Some(16)),
        "i32" | "u32" => Some(Some(32)),
        "i64" | "u64" => Some(Some(64)),
        "i128" | "u128" => Some(Some(128)),
        _ => None,
    }
}

fn syn(line: usize, msg: impl Into<String>) -> EmittedError {
    EmittedError::Syntax {
        line,
        msg: msg.into(),
    }
}

fn no_image(line: usize, msg: impl Into<String>) -> EmittedError {
    EmittedError::Core {
        line,
        source: CoreError::NoImage(msg.into()),
    }
}

/// Parse the preamble lines [`split_preamble`] returned.
///
/// `lines[i]` is line `i + 1` of the emitted text, and every refusal names it.
///
/// # Errors
/// Returns [`EmittedError`] on any row outside the grammar stated in the
/// module docs, and on any construct with no image — a non-scalar type alias,
/// a `tls(`/`mut`/`align(` global, a `{…}` initializer, an element out of
/// range, or a length that disagrees with its element count.
pub(super) fn parse(lines: &[&str]) -> Result<Preamble, EmittedError> {
    let mut pre = Preamble::default();
    for (i, raw) in lines.iter().enumerate() {
        let n = i + 1;
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(rest) = line.strip_prefix("type ty.") {
            let (idx, tok) = rest
                .split_once(" = ")
                .ok_or_else(|| syn(n, "a `type ty.N = <ty>` row needs ` = `"))?;
            let idx: u32 = idx
                .trim()
                .parse()
                .map_err(|_| syn(n, format!("type-table index `ty.{idx}` is not a number")))?;
            let tok = tok.trim();
            if scalar_width(tok).is_none() {
                return Err(no_image(
                    n,
                    format!(
                        "type-table row `ty.{idx} = {tok}`: only a SCALAR alias (bool, ptr, iN, \
                         uN, fN) is read here, because the row is consulted only to resolve an \
                         array's element; a `struct.N`, `enum.N`, `usize` or any other token \
                         has no element image and is refused rather than aliased"
                    ),
                ));
            }
            if pre.types.insert(idx, tok.to_string()).is_some() {
                return Err(syn(n, format!("type-table row `ty.{idx}` appears twice")));
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("global ") {
            let decl = global_row(n, rest, &pre.types)?;
            if pre.globals.iter().any(|g| g.name == decl.name) {
                return Err(syn(n, format!("global `@{}` is declared twice", decl.name)));
            }
            pre.globals.push(decl);
            continue;
        }
        return Err(syn(
            n,
            format!("`{line}` is neither a `type ty.N = …` row nor a `global …` row"),
        ));
    }
    Ok(pre)
}

/// `[<linkage>] [tls(N)] [mut] [align(N)] @<name> [ty.N x LEN] = array[ … ]`,
/// everything after the `global ` keyword.
fn global_row(
    n: usize,
    rest: &str,
    types: &BTreeMap<u32, String>,
) -> Result<GlobalDecl, EmittedError> {
    let (head, init) = rest.split_once(" = ").ok_or_else(|| {
        syn(
            n,
            "a `global` row without ` = <init>` declares no bytes; refused",
        )
    })?;
    let mut linkage = DEFAULT_LINKAGE.to_string();
    let mut toks = head.split_whitespace().peekable();
    if let Some(tok) = toks.peek() {
        if let Some(found) = LINKAGES.iter().find(|k| *k == tok) {
            linkage = (*found).to_string();
            toks.next();
        }
    }
    // The three fields `IRGlobal.mk` has no slot for, refused BY NAME so that
    // a global carrying one can never be read as the same module as one
    // without it. The printer emits them in this order, between the linkage
    // and the name.
    let mut name: Option<&str> = None;
    if let Some(tok) = toks.next() {
        if tok.starts_with("tls(") || tok == "mut" || tok.starts_with("align(") {
            return Err(no_image(
                n,
                format!(
                    "global row carries `{tok}`: `IRGlobal.mk : Nat -> IRConst -> IRGlobal` has \
                     no slot for thread-local storage, mutability or alignment, so a `tls(`, \
                     `mut` or `align(` global is REFUSED by name in both readers rather than \
                     read as the immutable, non-TLS, unaligned global it is not"
                ),
            ));
        }
        if let Some(nm) = tok.strip_prefix('@') {
            name = Some(nm);
        } else {
            return Err(syn(
                n,
                format!(
                    "global row token `{tok}` is not a linkage ({LINKAGES:?}) and not the \
                     `@<name>`"
                ),
            ));
        }
    }
    let name = name.ok_or_else(|| syn(n, "a `global` row names no `@<name>`"))?;
    if name.is_empty() {
        return Err(syn(n, "a `global` row names an empty `@`"));
    }
    let ty_tok: Vec<&str> = toks.collect();
    let ty_tok = ty_tok.join(" ");
    let (ty, width) = array_ty(n, &ty_tok, types)?;
    let (resolved, len) = ty;
    let init = array_init(n, init.trim(), len, width)?;
    Ok(GlobalDecl {
        name: name.to_string(),
        linkage,
        ty: resolved,
        init,
    })
}

/// `[ty.N x LEN]` -> (`[u8 x LEN]`, LEN) plus the element width.
fn array_ty(
    n: usize,
    tok: &str,
    types: &BTreeMap<u32, String>,
) -> Result<((String, usize), Option<u32>), EmittedError> {
    let inner = tok
        .strip_prefix('[')
        .and_then(|x| x.strip_suffix(']'))
        .ok_or_else(|| {
            no_image(
                n,
                format!(
                    "global type `{tok}`: only an ARRAY `[ty.N x LEN]` global has an image (a \
                     `(agg …)` of its elements); a scalar or aggregate-typed global is refused"
                ),
            )
        })?;
    let (elem, len) = inner
        .split_once(" x ")
        .ok_or_else(|| syn(n, format!("array type `{tok}` is not `[ty.N x LEN]`")))?;
    let len: usize = len
        .trim()
        .parse()
        .map_err(|_| syn(n, format!("array length `{len}` is not a number")))?;
    let idx: u32 = elem
        .trim()
        .strip_prefix("ty.")
        .and_then(|k| k.parse().ok())
        .ok_or_else(|| {
            no_image(
                n,
                format!(
                    "array element `{elem}` is not a `ty.N` type-table index; the printer always \
                     routes an array element through the table, so anything else is not the \
                     printer's output"
                ),
            )
        })?;
    let scalar = types.get(&idx).ok_or_else(|| {
        syn(
            n,
            format!(
                "array element `ty.{idx}` has no `type ty.{idx} = …` row in the preamble; the \
                 fixture must carry the row the global names"
            ),
        )
    })?;
    let width = scalar_width(scalar).flatten();
    Ok(((format!("[{scalar} x {len}]"), len), width))
}

/// `array[ a, b, … ]` -> `(agg (int a) (int b) …)`, exactly `len` digit-only
/// elements each below `2^width`.
fn array_init(n: usize, init: &str, len: usize, width: Option<u32>) -> Result<Sx, EmittedError> {
    if init.starts_with('{') {
        return Err(no_image(
            n,
            format!(
                "global initializer `{init}`: a `{{…}}` aggregate is an INSTRUCTION constant and \
                 reads only there; a global initializer reads only as `array[ … ]`. The two \
                 spellings share one Clean image (`aggv`), so each is accepted in exactly one \
                 position and never both — the position rule, not a constructor"
            ),
        ));
    }
    let inner = init
        .strip_prefix("array[")
        .and_then(|x| x.strip_suffix(']'))
        .ok_or_else(|| {
            no_image(
                n,
                format!("global initializer `{init}` is not `array[ a, b, … ]`"),
            )
        })?;
    let Some(width) = width else {
        return Err(no_image(
            n,
            "an array over `bool`, `ptr` or a float has no digit-only element literal that \
             `(int a)` is the image of; refused",
        ));
    };
    // `array[ ]` is the ONE element-less spelling; every other list is read
    // element by element, and an empty element is refused below rather than
    // skipped, so `array[ 1,, 2 ]` and a trailing comma are not two elements.
    let elems: Vec<&str> = if inner.trim().is_empty() {
        Vec::new()
    } else {
        inner.split(',').map(str::trim).collect()
    };
    // An empty element is named BEFORE the count is compared, so `array[ 1,, 2 ]`
    // is refused for the doubled comma it carries and not for the count it
    // happens to reach.
    if elems.iter().any(|e| e.is_empty()) {
        return Err(syn(
            n,
            format!(
                "array initializer `{init}` carries an EMPTY element (a doubled or trailing \
                 comma); the printer separates elements with `, ` and never writes one, so \
                 this is not the printer's output"
            ),
        ));
    }
    if elems.len() != len {
        return Err(syn(
            n,
            format!(
                "array type declares {len} element(s) and the initializer carries {}; a global \
                 whose length and bytes disagree is not the printer's output",
                elems.len()
            ),
        ));
    }
    let mut out = Vec::with_capacity(len);
    for e in elems {
        if !e.chars().all(|c| c.is_ascii_digit()) {
            return Err(no_image(
                n,
                format!("array element `{e}` is not a digit-only literal"),
            ));
        }
        let v: u128 = e
            .parse()
            .map_err(|_| syn(n, format!("array element `{e}` does not fit u128")))?;
        if e != v.to_string() {
            return Err(syn(
                n,
                format!(
                    "array element `{e}` is not the canonical decimal `{v}`; the printer writes \
                     each element as `{{}}` of its value, so a leading zero is not the printer's \
                     output and would image to a second atom for one value"
                ),
            ));
        }
        if width < 128 && v >= (1u128 << width) {
            return Err(no_image(
                n,
                format!(
                    "array element {v} does not fit the {width}-bit element type; a byte above \
                     255 in a `[u8 x N]` is not the printer's output"
                ),
            ));
        }
        out.push(Sx::tag("int", vec![Sx::a(e.to_string())]));
    }
    Ok(Sx::tag("agg", out))
}
