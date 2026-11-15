// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// B3 schema-parity gate.
//
// The Rust IR is the canonical surface; the Lean operational semantics must
// keep up with it, or any module using an un-modelled construct falls outside
// the proven core. There is no Lean toolchain in CI here to *prove* parity, but
// we CAN mechanically detect *drift*: every Rust `Inst` / `CastOp` / `Ty` /
// `FatPtrKind` / `Constant` variant must either have a Lean constructor of the
// same name, or be on an explicit, documented allowlist of known-not-yet-
// modelled constructs. Those established axes have empty allowlists. The
// BinOp/UnOp axes below also record two remaining float operators. Since WS2.18 the `Inst`
// axis is also checked at FIELD level: each Rust variant's named fields must
// equal the Lean constructor's binder list (in order, through an explicit
// snake_case -> camelCase name map), so a field such as
// `Switch.exhaustive_enum_unreachable` can no longer be dropped silently.
//
// This makes the coordinated-triple rule enforceable: adding a new Rust variant
// without Lean semantics fails this test unless you also record it as known
// debt here (which docs/roadmap/B3-lean-ir-parity.md tracks). Removing the debt
// (adding the Lean constructor) requires deleting the allowlist entry, so the
// allowlist can never silently over-claim either.
//
// When a Lean toolchain is available, the real fix is to add the Lean
// constructors + semantics and shrink these allowlists to empty.
//
// Since RM4 the `Inst`, `Ty` and `Constant` axes are SPLIT: a variant a SemR
// ledger lists (`lean/semr/FRAGMENT.tsv`, `TY_FRAGMENT.tsv`,
// `CONSTANT_FRAGMENT.tsv`) is judged against SemR (`lean/semr/SemR.lean`), and
// every other variant keeps the old gate against lean/trust_ir-semantics. The
// two halves partition the Rust variants.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_required(path: PathBuf) -> String {
    std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "required checked-in Lean model {} could not be read: {error}",
            path.display()
        )
    })
}

/// Leading PascalCase identifier of a trimmed line, if it is a variant head
/// (`Name`, `Name {`, `Name(`, `Name,`) rather than a comment/attribute/field.
fn pascal_head(trimmed: &str) -> Option<String> {
    let mut chars = trimmed.char_indices();
    let (_, first) = chars.next()?;
    if !first.is_ascii_uppercase() {
        return None;
    }
    let end = trimmed
        .char_indices()
        .find(|(_, c)| !(c.is_ascii_alphanumeric() || *c == '_'))
        .map(|(i, _)| i)
        .unwrap_or(trimmed.len());
    let name = &trimmed[..end];
    // Must be followed by a variant delimiter (or end-of-line for the last one).
    let rest = trimmed[end..].trim_start();
    // Rust: `Name {` / `Name(` / `Name,`. Lean no-arg ctor: `Name : Inst`.
    if rest.is_empty()
        || rest.starts_with('{')
        || rest.starts_with('(')
        || rest.starts_with(',')
        || rest.starts_with(':')
    {
        Some(name.to_string())
    } else {
        None
    }
}

/// The declaration head of `enum_name` in `src`: `pub enum NAME {`, or, for a
/// level-generic carrier (amendment S, `src/level.rs`), `pub enum NAMEG<X> {`,
/// of which `NAME` is the level-R alias.
fn enum_head(src: &str, enum_name: &str) -> Option<(usize, String)> {
    for needle in [
        format!("pub enum {enum_name} {{"),
        format!("pub enum {enum_name}G<X> {{"),
    ] {
        if let Some(start) = src.find(&needle) {
            return Some((start, needle));
        }
    }
    None
}

/// The level-R extension, `pub enum NoExt {}` in `src/level.rs`, has no
/// variant. Only while that holds may a level-generic carrier's `Ext` variant
/// be left out of a level-R axis: it is then uninhabited at level R, so no
/// level-R value reaches it and the Lean model has nothing to mirror
/// (amendment S, `docs/SPEC_RATIFICATIONS.md` §1).
fn noext_is_empty(level_rs: &str) -> bool {
    let needle = "pub enum NoExt {";
    let Some(start) = level_rs.find(needle) else {
        return false;
    };
    level_rs[start + needle.len()..]
        .trim_start()
        .starts_with('}')
}

/// Top-level variant names of a Rust `pub enum NAME { ... }`. For a
/// level-generic carrier the `Ext` variant is excluded BY RULE, and only while
/// `NoExt` is empty ([`noext_is_empty`]); otherwise it stays and the axis
/// fails for want of a Lean constructor.
fn rust_enum_variants(src: &str, enum_name: &str) -> BTreeSet<String> {
    rust_enum_variants_at_level(src, enum_name, &read_level_rs())
}

fn read_level_rs() -> String {
    std::fs::read_to_string(manifest().join("src/level.rs")).expect("level.rs")
}

fn rust_enum_variants_at_level(src: &str, enum_name: &str, level_rs: &str) -> BTreeSet<String> {
    let mut out = rust_enum_variants_raw(src, enum_name);
    let generic = src.contains(&format!("pub enum {enum_name}G<X> {{"));
    if generic && noext_is_empty(level_rs) {
        out.remove("Ext");
    }
    out
}

fn rust_enum_variants_raw(src: &str, enum_name: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let Some((start, needle)) = enum_head(src, enum_name) else {
        return out;
    };
    let body = &src[start + needle.len()..];
    let mut depth: i32 = 0;
    for line in body.lines() {
        let trimmed = line.trim_start();
        if depth == 0
            && !trimmed.starts_with("///")
            && !trimmed.starts_with("//")
            && !trimmed.starts_with("#[")
            && let Some(name) = pascal_head(trimmed)
        {
            out.insert(name);
        }
        depth += line.matches('{').count() as i32;
        depth -= line.matches('}').count() as i32;
        if depth < 0 {
            break; // closed the enum itself
        }
    }
    out
}

/// Constructor names of a Lean `inductive NAME where | A ... | B ... deriving`.
fn lean_constructors(src: &str, inductive_name: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let needle = format!("inductive {inductive_name} where");
    let Some(start) = src.find(&needle) else {
        return out;
    };
    for line in src[start + needle.len()..].lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("deriving") || trimmed.starts_with("inductive ") {
            break;
        }
        if let Some(rest) = trimmed.strip_prefix("| ")
            && let Some(name) = pascal_head(rest.trim_start())
        {
            out.insert(name);
        }
    }
    out
}

fn lean_dir() -> PathBuf {
    manifest().join("../../lean/trust_ir-semantics/TrustIr")
}

/// (Rust variants − Lean constructors) == the documented allowlist, or the
/// reason it is not. Split from [`assert_parity`] so the mutation controls
/// below can assert that a specific drift is CAUGHT, by name.
fn parity_drift(
    axis: &str,
    rust: &BTreeSet<String>,
    lean: &BTreeSet<String>,
    allowlist: &[&str],
) -> Result<(), String> {
    if rust.is_empty() {
        return Err(format!("{axis}: failed to parse any Rust variants"));
    }
    if lean.is_empty() {
        return Err(format!("{axis}: failed to parse any Lean constructors"));
    }
    let allow: BTreeSet<String> = allowlist.iter().map(|s| s.to_string()).collect();
    let drift: BTreeSet<String> = rust.difference(lean).cloned().collect();

    let new_drift: Vec<&String> = drift.difference(&allow).collect();
    if !new_drift.is_empty() {
        return Err(format!(
            "{axis}: these Rust variants have NO Lean constructor and are NOT on the \
             B3 allowlist — add Lean semantics (coordinated-triple) or record them in \
             the allowlist in this test + docs/roadmap/B3-lean-ir-parity.md: {new_drift:?}"
        ));
    }
    let stale_allow: Vec<&String> = allow.difference(&drift).collect();
    if !stale_allow.is_empty() {
        return Err(format!(
            "{axis}: these allowlist entries are no longer drifting (Lean now has them, \
             or they were renamed/removed) — delete them from the allowlist so the gate \
             keeps enforcing parity: {stale_allow:?}"
        ));
    }
    Ok(())
}

/// Assert: (Rust variants − Lean constructors) == the documented allowlist.
fn assert_parity(axis: &str, rust: &BTreeSet<String>, lean: &BTreeSet<String>, allowlist: &[&str]) {
    if let Err(reason) = parity_drift(axis, rust, lean, allowlist) {
        panic!("{reason}");
    }
}

/// Operator enums are independent schema axes, not implied by Inst parity.
#[test]
fn arithmetic_operators_track_the_lean_model() {
    let rust = read_required(manifest().join("src/inst.rs"));
    let lean = read_required(lean_dir().join("BinOp.lean"));
    assert_parity(
        "UnOp",
        &rust_enum_variants(&rust, "UnOp"),
        &lean_constructors_any_case(&lean, "UnOp"),
        &[],
    );
    assert_parity(
        "BinOp",
        &rust_enum_variants(&rust, "BinOp"),
        &lean_constructors_any_case(&lean, "BinOp"),
        &[],
    );
}

// ---------------------------------------------------------------------------
// The `Constant` axis (WS2.18).
//
// Lean spells `Constant` constructors in lowerCamelCase (`int`, `u128`,
// `fnDef`, `symbolAddr`) where Rust uses PascalCase, so the axis compares the
// Rust names through `lower_first` — an explicit, total name map (the whole
// map is "lowercase the first character"), not a fuzzy match.
// ---------------------------------------------------------------------------

/// Rust PascalCase variant name -> the Lean lowerCamelCase constructor name.
fn lower_first(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_ascii_lowercase().to_string() + chars.as_str(),
        None => String::new(),
    }
}

/// Leading identifier of a Lean constructor line (`int : Int → Constant`,
/// `phantomData : Constant`), any case. `None` unless the name is followed by
/// a binder, a type ascription, or the end of the line.
fn lean_ident_head(trimmed: &str) -> Option<String> {
    let first = trimmed.chars().next()?;
    if !first.is_ascii_alphabetic() {
        return None;
    }
    let end = trimmed
        .char_indices()
        .find(|(_, c)| !(c.is_ascii_alphanumeric() || *c == '_'))
        .map(|(i, _)| i)
        .unwrap_or(trimmed.len());
    let rest = trimmed[end..].trim_start();
    if rest.is_empty() || rest.starts_with(':') || rest.starts_with('(') {
        Some(trimmed[..end].to_string())
    } else {
        None
    }
}

/// Constructor names (any case) of a Lean `inductive NAME where`.
fn lean_constructors_any_case(src: &str, inductive_name: &str) -> BTreeSet<String> {
    lean_inductive_ctor_texts(src, inductive_name)
        .unwrap_or_default()
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}

// ---------------------------------------------------------------------------
// The FIELD-level `Inst` axis (WS2.18).
//
// Name-level parity cannot see a field: `Switch` existed on both sides while
// the Lean one had no `exhaustive_enum_unreachable`, and `CallIndirect` no
// calling convention. This axis parses each Rust variant's named fields and
// each Lean constructor's binder names and compares them IN ORDER, through
// `rust_field_to_lean`. Both parsers FAIL LOUDLY (an `Err` naming the
// variant) on any line they cannot classify, so a shape they were not written
// for is a gate failure, never a silently-empty field list.
// ---------------------------------------------------------------------------

/// Explicit exceptions to the snake_case -> camelCase field-name map: the
/// Lean binder had to be renamed because the Rust name is a Lean keyword, or
/// the Rust variant is a tuple variant with positional fields.
const FIELD_NAME_EXCEPTIONS: &[(&str, &str, &str)] = &[
    // `default` is a Lean keyword.
    ("Switch", "default", "default_"),
    // `def` is a Lean keyword.
    ("OpenFrame", "def", "def_"),
    // Tuple variant `DialectOp(Box<DialectInst>)`: positional field 0.
    ("DialectOp", "0", "op"),
];

/// Known field-level gaps: `(variant, lean-binder)` pairs that exist in Rust
/// but not in Lean. EMPTY — the four gaps recorded at WS2.18 (`Alloca.align`,
/// `HeapAlloc.align`, `Switch.exhaustive_enum_unreachable`,
/// `CallIndirect.calling_conv`) were burned down in the same change by adding
/// the Lean binders (TrustIr/Inst.lean). Keep it empty.
const INST_FIELD_ALLOWLIST: &[(&str, &str)] = &[];

/// Map one Rust field name of `variant` to its Lean binder name.
fn rust_field_to_lean(variant: &str, field: &str) -> String {
    if let Some((_, _, lean)) = FIELD_NAME_EXCEPTIONS
        .iter()
        .find(|(v, f, _)| *v == variant && *f == field)
    {
        return (*lean).to_string();
    }
    let mut out = String::new();
    let mut upper_next = false;
    for c in field.chars() {
        if c == '_' {
            upper_next = true;
        } else if upper_next {
            out.push(c.to_ascii_uppercase());
            upper_next = false;
        } else {
            out.push(c);
        }
    }
    out
}

/// Strip a trailing `//` comment (Rust) — no field type in `inst.rs` contains
/// `//`, and a line that did would fail the field-shape check below loudly.
fn strip_rust_line_comment(line: &str) -> &str {
    match line.find("//") {
        Some(i) => &line[..i],
        None => line,
    }
}

/// Split `a, b<c, d>, e` on commas at bracket depth 0.
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '<' | '(' | '[' | '{' => {
                depth += 1;
                cur.push(c);
            }
            '>' | ')' | ']' | '}' => {
                depth -= 1;
                cur.push(c);
            }
            ',' if depth == 0 => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out.into_iter()
        .map(|p| p.trim().to_string())
        .filter(|p| !p.is_empty())
        .collect()
}

/// A named field line, shared by expanded and rustfmt-compact variants.
fn rust_named_field(enum_name: &str, variant: &str, line: &str) -> Result<String, String> {
    let malformed = || {
        format!("{enum_name}::{variant}: unparseable field line `{line}` (expected `name: Type,`)")
    };
    let Some((name, ty)) = line.split_once(':') else {
        return Err(malformed());
    };
    let name = name.trim().trim_start_matches("pub ").trim();
    if name.is_empty()
        || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        || name.starts_with(|c: char| c.is_ascii_digit())
        || !line.ends_with(',')
        || split_top_level_commas(ty.trim().trim_end_matches(',')).len() != 1
    {
        return Err(malformed());
    }
    Ok(name.to_string())
}

/// Split one COMPLETE compact named-field body. Delimiters and empty field
/// fragments are checked, rather than flattening nested type commas or silently
/// discarding an empty fragment. Expanded variants retain their line grammar.
fn rust_compact_named_fields(
    enum_name: &str,
    variant: &str,
    body: &str,
) -> Result<Vec<String>, String> {
    let malformed = || format!("{enum_name}::{variant}: unparseable compact named fields `{body}`");
    if body.trim().is_empty() {
        return Ok(Vec::new());
    }
    let mut delimiters = Vec::new();
    let mut fields = Vec::new();
    let mut start = 0;
    let mut previous = None;
    let mut push = |fragment: &str| -> Result<(), String> {
        if fragment.trim().is_empty() {
            return Err(malformed());
        }
        let field = rust_named_field(enum_name, variant, &format!("{},", fragment.trim()))?;
        if fields.contains(&field) {
            return Err(malformed());
        }
        fields.push(field);
        Ok(())
    };
    for (at, ch) in body.char_indices() {
        match ch {
            '<' | '(' | '[' | '{' => delimiters.push(ch),
            '>' if previous == Some('-') => {} // function return arrow
            '>' | ')' | ']' | '}' => {
                let wanted = match ch {
                    '>' => '<',
                    ')' => '(',
                    ']' => '[',
                    _ => '{',
                };
                if delimiters.pop() != Some(wanted) {
                    return Err(malformed());
                }
            }
            ',' if delimiters.is_empty() => {
                push(&body[start..at])?;
                start = at + 1;
            }
            _ => {}
        }
        previous = Some(ch);
    }
    if !delimiters.is_empty() {
        return Err(malformed());
    }
    if !body[start..].trim().is_empty() {
        push(&body[start..])?;
    }
    Ok(fields)
}

/// Every top-level variant of the Rust `pub enum NAME { ... }` with its field
/// names in declaration order: named fields for `V { a: T, .. }`, `"0"`,
/// `"1"`, .. for a tuple variant `V(T, ..)`, none for a unit variant.
fn rust_enum_variant_fields(
    src: &str,
    enum_name: &str,
) -> Result<Vec<(String, Vec<String>)>, String> {
    let (start, needle) = enum_head(src, enum_name)
        .ok_or_else(|| format!("{enum_name}: `pub enum {enum_name} {{` not found"))?;
    let body = &src[start + needle.len()..];
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    // `Some(name)` while inside a struct-like variant's `{ .. }`.
    let mut open: Option<String> = None;
    for raw in body.lines() {
        let trimmed = raw.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("#[") {
            continue;
        }
        let line = strip_rust_line_comment(trimmed).trim();
        if let Some(variant) = open.clone() {
            if line == "}," || line == "}" {
                open = None;
                continue;
            }
            // Expanded variants retain exactly one complete named field per line.
            let name = rust_named_field(enum_name, &variant, line)?;
            out.last_mut().expect("variant opened").1.push(name);
            continue;
        }
        if line == "}" {
            // Closed the enum itself.
            return Ok(out);
        }
        let Some(name) = pascal_head(line) else {
            return Err(format!("{enum_name}: unparseable variant line `{line}`"));
        };
        let rest = line[name.len()..].trim_start();
        if rest.is_empty() || rest == "," {
            out.push((name, Vec::new()));
        } else if rest == "{" {
            out.push((name.clone(), Vec::new()));
            open = Some(name);
        } else if let Some(inner) = rest.strip_prefix('{') {
            let Some(inner) = inner.strip_suffix("},").or_else(|| inner.strip_suffix('}')) else {
                return Err(format!(
                    "{enum_name}::{name}: compact named variant must close on its own line: `{line}`"
                ));
            };
            let fields = rust_compact_named_fields(enum_name, &name, inner)?;
            out.push((name, fields));
        } else if let Some(inner) = rest.strip_prefix('(') {
            let Some(inner) = inner.strip_suffix("),").or_else(|| inner.strip_suffix(')')) else {
                return Err(format!(
                    "{enum_name}::{name}: tuple variant must close on its own line: `{line}`"
                ));
            };
            let fields = split_top_level_commas(inner)
                .into_iter()
                .enumerate()
                .map(|(i, _)| i.to_string())
                .collect();
            out.push((name, fields));
        } else {
            return Err(format!(
                "{enum_name}::{name}: unparseable variant line `{line}`"
            ));
        }
    }
    Err(format!("{enum_name}: enum body never closed"))
}

/// Remove every `/- .. -/` block comment (doc comments included, nesting
/// honoured) and every `--` line comment from Lean source.
fn strip_lean_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    let mut depth = 0u32;
    while i < bytes.len() {
        if bytes[i..].starts_with(b"/-") {
            depth += 1;
            i += 2;
            continue;
        }
        if depth > 0 {
            if bytes[i..].starts_with(b"-/") {
                depth -= 1;
                i += 2;
            } else {
                if bytes[i] == b'\n' {
                    out.push('\n');
                }
                i += 1;
            }
            continue;
        }
        if bytes[i..].starts_with(b"--") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let ch = src[i..].chars().next().expect("in bounds");
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// `(name, text-after-name)` for every constructor of a Lean
/// `inductive NAME where`, comments stripped and continuation lines joined.
fn lean_inductive_ctor_texts(
    src: &str,
    inductive_name: &str,
) -> Result<Vec<(String, String)>, String> {
    let src = strip_lean_comments(src);
    let needle = format!("inductive {inductive_name} where");
    let start = src
        .find(&needle)
        .ok_or_else(|| format!("{inductive_name}: `{needle}` not found in the Lean model"))?;
    let mut out: Vec<(String, String)> = Vec::new();
    for line in src[start + needle.len()..].lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with("deriving") || trimmed.starts_with("inductive ") {
            break;
        }
        if let Some(rest) = trimmed.strip_prefix('|') {
            let rest = rest.trim_start();
            let Some(name) = lean_ident_head(rest) else {
                return Err(format!(
                    "{inductive_name}: unparseable constructor line `{trimmed}`"
                ));
            };
            out.push((name.clone(), rest[name.len()..].to_string()));
        } else if let Some(last) = out.last_mut() {
            last.1.push(' ');
            last.1.push_str(trimmed);
        } else {
            // Anything else ends the inductive (a following `def`, `end`, ..).
            break;
        }
    }
    Ok(out)
}

/// The binder names of one Lean constructor signature, in order:
/// `(ty : Ty) (lhs rhs : ValueId) : Inst` -> `[ty, lhs, rhs]`. Only explicit
/// named binders followed by `: <inductive>` are understood; an arrow-typed
/// (unnamed) parameter or anything else is an `Err`, never skipped.
fn lean_ctor_binders(ctor: &str, sig: &str, inductive_name: &str) -> Result<Vec<String>, String> {
    let mut names = Vec::new();
    let mut rest = sig.trim();
    loop {
        if let Some(tail) = rest.strip_prefix(':') {
            if tail.trim() == inductive_name {
                return Ok(names);
            }
            return Err(format!(
                "{inductive_name}.{ctor}: unnamed (arrow-typed) parameters `{}` — the field \
                 axis needs named binders `(name : Ty)`",
                tail.trim()
            ));
        }
        let Some(after_paren) = rest.strip_prefix('(') else {
            return Err(format!(
                "{inductive_name}.{ctor}: unparseable signature `{sig}`"
            ));
        };
        let mut depth = 1i32;
        let mut close = None;
        for (i, c) in after_paren.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(close) = close else {
            return Err(format!(
                "{inductive_name}.{ctor}: unbalanced binder in `{sig}`"
            ));
        };
        let group = &after_paren[..close];
        let Some((binder_names, _ty)) = group.split_once(" : ") else {
            return Err(format!(
                "{inductive_name}.{ctor}: binder group without a type `({group})`"
            ));
        };
        for name in binder_names.split_whitespace() {
            names.push(name.to_string());
        }
        rest = after_paren[close + 1..].trim_start();
    }
}

/// Field-level drift of the `Inst` axis, or `Ok` when every Rust variant's
/// mapped field list equals its Lean constructor's binder list modulo exactly
/// the `(variant, lean-binder)` pairs on `allowlist`.
fn inst_field_drift(
    inst_rs: &str,
    lean_inst: &str,
    allowlist: &[(&str, &str)],
) -> Result<(), String> {
    let rust = rust_enum_variant_fields(inst_rs, "Inst")?;
    let lean: BTreeMap<String, Vec<String>> = lean_inductive_ctor_texts(lean_inst, "Inst")?
        .into_iter()
        .map(|(name, sig)| lean_ctor_binders(&name, &sig, "Inst").map(|b| (name, b)))
        .collect::<Result<_, _>>()?;
    if rust.is_empty() || lean.is_empty() {
        return Err("Inst fields: failed to parse either side".to_string());
    }
    let allow: BTreeSet<(String, String)> = allowlist
        .iter()
        .map(|(v, f)| (v.to_string(), f.to_string()))
        .collect();
    let mut used_allow = BTreeSet::new();
    let mut drift = Vec::new();
    for (variant, fields) in &rust {
        let Some(binders) = lean.get(variant) else {
            // Name-level drift is the `Inst` name axis' verdict, not this one.
            continue;
        };
        let expected: Vec<String> = fields
            .iter()
            .map(|f| rust_field_to_lean(variant, f))
            .filter(|f| {
                let key = (variant.clone(), f.clone());
                if allow.contains(&key) && !binders.contains(f) {
                    used_allow.insert(key);
                    false
                } else {
                    true
                }
            })
            .collect();
        if &expected != binders {
            drift.push(format!(
                "{variant}: Rust fields (as Lean binders) {expected:?} != Lean binders {binders:?}"
            ));
        }
    }
    if !drift.is_empty() {
        return Err(format!(
            "Inst fields: Rust variants whose fields do not match their Lean binders — add \
             the Lean binder (and semantics) or record the gap in INST_FIELD_ALLOWLIST + \
             docs/roadmap/B3-lean-ir-parity.md: {drift:#?}"
        ));
    }
    let stale: Vec<_> = allow.difference(&used_allow).collect();
    if !stale.is_empty() {
        return Err(format!(
            "Inst fields: these allowlist entries are no longer gaps — delete them: {stale:?}"
        ));
    }
    Ok(())
}

#[test]
fn inst_and_castop_track_the_lean_model() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let lean_inst = read_required(lean_dir().join("Inst.lean"));
    let lean_castop = read_required(lean_dir().join("CastOp.lean"));

    // --- Inst ---
    let rust_inst = rust_enum_variants(&inst_rs, "Inst");
    let lean_inst_ctors = lean_constructors(&lean_inst, "Inst");
    // Known debt: Rust Inst variants not yet in the Lean operational model.
    // Shrink to empty as Lean semantics are added (needs a Lean toolchain).
    // GlobalAddr: Lean semGlobalAddr landed (cached, aliasing-faithful partial;
    // size/contents need module context — documented follow-up).
    // HeapAlloc / PtrData / PtrMetadata / PtrFromParts: landed earlier.
    // EMPTY — every Rust Inst variant now has a Lean constructor + semantics.
    // The 2026-07-01 drift was discharged 2026-07-02:
    //  * SeqMapAddK / SeqMapNot — semSeqMapAddK / semSeqMapNot
    //    (Semantics/Aggregate.lean) with the operational round-trip laws
    //    seqMapAddKList_roundTrip / seqMapNotList_involutive
    //    (Proofs/AggregateProps.lean); element op definitionally `BinOp Add` /
    //    `Bool.not` (seqElemAddK_eq_semIntBinOp_add).
    //  * CoroSuspend — semCoroSuspend (Semantics/Coroutine.lean), defined as
    //    the documented GEP+Store+Return macro-expansion
    //    (semCoroSuspend_is_macro_expansion).
    //  * Invoke / LandingPad / Resume — the NON-THROWING executable model
    //    mirroring interpret.rs (panic=abort): StepResult.InvokeReq runs the
    //    call and takes the normal edge binding the invoke's results
    //    (Eval.lean); a directly-executed LandingPad fails closed with
    //    `unsupported.host_unwind`, like interpret.rs (WS2.5/WS2.24); Resume
    //    is a structured `unsupported.host_unwind`. Full host-unwinding
    //    (taken unwind edges) remains a documented model refinement — see
    //    docs/roadmap/B3-lean-ir-parity.md "Depth gaps".
    // All six carry native_decide interpreter-agreement fixtures
    // (Semantics/ExecutableFixtures.lean).
    //
    // Since RM4 (Trust proven-core; `lean/semr/FRAGMENT.tsv`) the variants in
    // SemR's fragment are judged by SemR (`inst_parity_reads_semr_for_its_fragment`
    // below, and the SemR differential's parity gate), so this axis is the old
    // gate for the REST: every Rust variant outside SemR's fragment must have a
    // constructor in lean/trust_ir-semantics. (The legacy model keeps its
    // constructors for the fragment too; this axis no longer requires them.)
    const INST_ALLOWLIST: &[&str] = &[];
    let fragment = semr_fragment().unwrap_or_else(|e| panic!("{e}"));
    let rest = outside_semr_fragment(&rust_inst, &fragment);
    assert_parity(
        "Inst (outside SemR's fragment)",
        &rest,
        &lean_inst_ctors,
        INST_ALLOWLIST,
    );

    // --- CastOp ---
    let rust_castop = rust_enum_variants(&inst_rs, "CastOp");
    let lean_castop_ctors = lean_constructors(&lean_castop, "CastOp");
    // EMPTY — every Rust CastOp variant now has a Lean constructor + semCast
    // case. Transmute (scalar-only partial) and ReifyFnPointer (fn-item
    // partial) landed earlier; the saturating float→int drift (FPToSISat /
    // FPToUISat — Rust `f as iN`/`uN`, LLVM fptosi.sat/fptoui.sat) was
    // discharged 2026-07-10: EXACT saturating semantics mirroring the
    // reference interpreter (interpret.rs) — NaN → 0, out-of-range clamps to
    // MIN/MAX, in-range truncates toward zero via the exact frExp mantissa
    // decomposition (Semantics/Cast.lean fpToSISatRaw / fpToUISatRaw) — with
    // interpreter-agreement native_decide fixtures at two widths per op
    // (Semantics/ExecutableFixtures.lean fptosisat_* / fptouisat_*).
    // Note: cast_op_excluded (bridge.rs) excludes the pair from the
    // lowering-target subset (no proven bridge/ay lowering yet), exactly as
    // the ratified subset does (lowering-target-subset.md; the conformance
    // crate's bridge_subset_agreement gate pins the two spellings
    // identical). Subset membership is a separate decision from the
    // name+semantics parity this test enforces.
    const CASTOP_ALLOWLIST: &[&str] = &[];
    assert_parity("CastOp", &rust_castop, &lean_castop_ctors, CASTOP_ALLOWLIST);

    // --- Ty ---
    // The Rust `Ty` enum is the canonical type surface; the Lean `Ty`
    // (TrustIr/Basic.lean) must track it or record the gap. This axis closes
    // the audit finding that `Ty::F16` existed in Rust with no Lean semantics
    // and *nothing watching the drift*: now a new Rust `Ty` variant without a
    // Lean constructor fails this test unless it is recorded below.
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let rust_ty = rust_enum_variants(&ty_rs, "Ty");
    let lean_ty_ctors = lean_constructors(&lean_basic, "Ty");
    // EMPTY — every Rust `Ty` variant now has a Lean constructor. F16 and the
    // FatPtr/FatPtrKind were added to TrustIr/Basic.lean (F16 remains a
    // type-level float; FatPtr now has first-class value, trio, and 16-byte
    // memory semantics on the pinned 64-bit executable target). v30's
    // `Refine` landed as a coordinated triple: `Ty.Refine : TyId -> PredId ->
    // Ty` plus `Ty.isRefine`/`refineBase`/`refinePred` in Basic.lean. It needs
    // no new operational rule because it is REPRESENTATION-PRESERVING — its
    // meaning is definitionally its base type's, so every existing semantic
    // rule already covers it through the base.
    //
    // Since the v67 tensor region (PKG-U13a) the variants in SemR's type
    // fragment (`lean/semr/TY_FRAGMENT.tsv`) are judged by SemR
    // (`ty_parity_reads_semr_for_its_type_fragment` below holds each row to a
    // SemR `Ty` constructor, and the SemR differential judges the
    // instructions over them), so this axis is the old gate for the REST, the
    // same split the Inst axis made at RM4.
    const TY_ALLOWLIST: &[&str] = &[];
    let ty_fragment = semr_ty_fragment().unwrap_or_else(|e| panic!("{e}"));
    let rest_ty = outside_semr_fragment(&rust_ty, &ty_fragment);
    assert_parity(
        "Ty (outside SemR's type fragment)",
        &rest_ty,
        &lean_ty_ctors,
        TY_ALLOWLIST,
    );

    // --- FatPtrKind ---
    // `Ty::FatPtr` carries a sub-enum, and the `Ty` axis above sees only the
    // outer constructor name: a new `FatPtrKind` variant was invisible to this
    // gate. v38's `ContainerLen` landed that way unrecorded, and v40's
    // `ContainerVtable` widened the gap; both were then recorded here as debt.
    // EMPTY since WS2.18 — the Lean `FatPtrKind` (Basic.lean) has both, and
    // `FatPtrKind.metadataTy` / `metadataTyMatches` / `decodeValue`
    // (Semantics/Memory.lean) classify them by what their METADATA means,
    // mirroring Rust `PointerMetadataShape::metadata_ty`: `ContainerLen` on
    // the `U64` length lane with Slice/Str, `ContainerVtable` on the `Ptr`
    // vtable lane with TraitObject. The lane agreement itself is pinned by
    // `fat_ptr_kind_metadata_lanes_agree_with_rust` below (WS3.19), since a
    // name match alone would accept swapped lanes.
    let rust_fat_ptr_kind = rust_enum_variants(&ty_rs, "FatPtrKind");
    let lean_fat_ptr_kind_ctors = lean_constructors(&lean_basic, "FatPtrKind");
    const FAT_PTR_KIND_ALLOWLIST: &[&str] = &[];
    assert_parity(
        "FatPtrKind",
        &rust_fat_ptr_kind,
        &lean_fat_ptr_kind_ctors,
        FAT_PTR_KIND_ALLOWLIST,
    );

    // --- EnumTagRepr (WS3.14(b)) ---
    // An enum's tag lane is a LAYOUT fact the Lean model mirrors
    // (`EnumTagRepr` in Basic.lean, reached through `EnumDef.tagRepr` and
    // `EnumTagEncoding.niche`), and nothing watched it: the v45 128-bit lanes
    // could have landed in Rust with the Lean image still capped at 64 bits,
    // which is exactly the drift this gate exists to catch. Lean spells the
    // constructors in lower case, so the Rust names are lowered first.
    let rust_tag_repr: BTreeSet<String> = rust_enum_variants(&ty_rs, "EnumTagRepr")
        .iter()
        .map(|name| name.to_lowercase())
        .collect();
    let lean_tag_repr = lean_constructors_any_case(&lean_basic, "EnumTagRepr");
    const ENUM_TAG_REPR_ALLOWLIST: &[&str] = &[];
    assert_parity(
        "EnumTagRepr",
        &rust_tag_repr,
        &lean_tag_repr,
        ENUM_TAG_REPR_ALLOWLIST,
    );
}

/// The no-tag inhabited selector is distinct from v37's one-declared-variant
/// Untagged encoding. No constructor or selector field can disappear silently.
#[test]
fn enum_tag_encoding_tracks_the_complete_lean_model() {
    let rust = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean = read_required(lean_dir().join("Basic.lean"));
    let names = rust_enum_variants(&rust, "EnumTagEncoding")
        .iter()
        .map(|name| lower_first(name))
        .collect();
    assert_parity(
        "EnumTagEncoding",
        &names,
        &lean_constructors_any_case(&lean, "EnumTagEncoding"),
        &[],
    );
    let fields = rust_enum_variant_fields(&rust, "EnumTagEncoding").expect("enum fields");
    let fields = &fields
        .iter()
        .find(|(name, _)| name == "SingleInhabited")
        .expect("actual Rust single-inhabited constructor")
        .1;
    let constructors = lean_inductive_ctor_texts(&lean, "EnumTagEncoding").expect("Lean enum");
    let signature = &constructors
        .iter()
        .find(|(name, _)| name == "singleInhabited")
        .expect("actual Lean single-inhabited constructor")
        .1;
    assert_eq!(
        lean_ctor_binders("singleInhabited", signature, "EnumTagEncoding").expect("named selector"),
        *fields
    );
    assert_eq!(fields, &["variant".to_string()]);
}

#[test]
fn mutation_removing_lean_single_inhabited_fails_enum_encoding_parity() {
    let rust = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean = read_required(lean_dir().join("Basic.lean"));
    let constructor = "  | singleInhabited (variant : Nat) : EnumTagEncoding\n";
    assert_eq!(lean.matches(constructor).count(), 1);
    let names = rust_enum_variants(&rust, "EnumTagEncoding")
        .iter()
        .map(|name| lower_first(name))
        .collect();
    let error = parity_drift(
        "EnumTagEncoding",
        &names,
        &lean_constructors_any_case(&lean.replacen(constructor, "", 1), "EnumTagEncoding"),
        &[],
    )
    .expect_err("missing no-tag selector must refuse parity");
    assert!(error.contains("singleInhabited"), "{error}");
}

/// Mutation control for the `EnumTagRepr` axis (WS3.14(b)): dropping the
/// 128-bit lanes from the Lean mirror fails it by name.
#[test]
fn mutation_removing_the_lean_128_bit_tag_reprs_fails_the_enum_tag_repr_axis() {
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let wide = "  | u128 : EnumTagRepr\n";
    assert_eq!(lean_basic.matches(wide).count(), 1, "unique 128-bit lanes");
    let rust: BTreeSet<String> = rust_enum_variants(&ty_rs, "EnumTagRepr")
        .iter()
        .map(|name| name.to_lowercase())
        .collect();
    let reason = parity_drift(
        "EnumTagRepr",
        &rust,
        &lean_constructors_any_case(&lean_basic.replacen(wide, "", 1), "EnumTagRepr"),
        &[],
    )
    .expect_err("a Lean EnumTagRepr without the 128-bit lanes must fail");
    assert!(reason.contains("\"u128\""), "{reason}");
}

/// The `Constant` axis (WS2.18). Before it there was no `Constant` parity at
/// all: the Lean model silently lacked `U128`, `Bytes`, `Array`, `FnDef`,
/// `SymbolAddr` and `PhantomData`, so no Lean statement about a string
/// literal, a vtable or a function-pointer table was even expressible.
#[test]
fn constant_tracks_the_lean_model() {
    let constant_rs =
        std::fs::read_to_string(manifest().join("src/constant.rs")).expect("constant.rs");
    let lean_constant = read_required(lean_dir().join("Constant.lean"));
    // Since PKG-U13e the axis is split like `Inst` and `Ty`: a variant
    // `CONSTANT_FRAGMENT.tsv` lists is judged against SemR's `Const`
    // (`constant_parity_reads_semr_for_its_constant_fragment`), and only the
    // remainder against TrustIr/Constant.lean.
    let all = rust_enum_variants(&constant_rs, "Constant");
    let fragment = semr_constant_fragment().unwrap_or_else(|e| panic!("{e}"));
    let rust = old_gate_constants(&all, &fragment);
    let lean = lean_constructors_any_case(&lean_constant, "Constant");
    // EMPTY — every Rust `Constant` variant has a Lean constructor, and
    // `Value.ofConstant` (Semantics/Aggregate.lean) gives each the reference
    // interpreter's denotation; `symbolAddr` (a link-time address) is refused
    // fail-closed by every constant entry point instead (the `Const` step, a
    // global initializer, and a `Switch` case the in-order scan reaches).
    const CONSTANT_ALLOWLIST: &[&str] = &[];
    assert_parity(
        "Constant (outside SemR's constant fragment)",
        &rust,
        &lean,
        CONSTANT_ALLOWLIST,
    );
    // 18 since v70 added `Constant::TensorBlob` (SemR `Const.tensorBlob`)
    // after v50's `Splat` (Lean `Constant.splat`) and v49's `Uninit`.
    assert_eq!(
        all.len(),
        18,
        "Constant: the Rust enum no longer has 18 variants (15 + the crystal lane's `Uninit` \
         + v50's `Splat` + v70's `TensorBlob`) — re-check this axis parses it"
    );
    assert_eq!(rust.len() + fragment.len(), all.len());

    // Presence, not correctness (only the Lean build gives correctness): the
    // fail-closed refusal of a link-time address must not vanish silently.
    let lean_step = read_required(lean_dir().join("Semantics/Step.lean"));
    let lean_eval = read_required(lean_dir().join("Semantics/Eval.lean"));
    let lean_call = read_required(lean_dir().join("Semantics/Call.lean"));
    assert!(
        lean_constant.contains("def Constant.hasSymbolAddr"),
        "Constant: `Constant.hasSymbolAddr` vanished from TrustIr/Constant.lean"
    );
    for (name, src) in [
        ("Semantics/Step.lean", &lean_step),
        ("Semantics/Eval.lean", &lean_eval),
        ("Semantics/Call.lean", &lean_call),
    ] {
        assert!(
            src.contains("hasSymbolAddr") && src.contains(".linkTimeAddress"),
            "Constant: {name} no longer refuses a link-time `symbolAddr` \
             (`unsupported.link_time_address`) — a constant with no compile-time value \
             would reach `Value.ofConstant`'s placeholder arm"
        );
    }
}

/// The FIELD-level `Inst` axis (WS2.18): every Rust `Inst` variant's fields,
/// mapped through `rust_field_to_lean`, equal its Lean constructor's binders.
#[test]
fn inst_fields_track_the_lean_model() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let lean_inst = read_required(lean_dir().join("Inst.lean"));
    if let Err(reason) = inst_field_drift(&inst_rs, &lean_inst, INST_FIELD_ALLOWLIST) {
        panic!("{reason}");
    }
    // The parsers really saw the enum, not an empty prefix of it.
    let rust = rust_enum_variant_fields(&inst_rs, "Inst").expect("inst.rs parses");
    let names: BTreeSet<String> = rust.iter().map(|(n, _)| n.clone()).collect();
    assert_eq!(
        names,
        rust_enum_variants(&inst_rs, "Inst"),
        "Inst fields: the field parser and the name parser disagree on the variant set"
    );
    let total_fields: usize = rust.iter().map(|(_, f)| f.len()).sum();
    assert!(
        total_fields > 150,
        "Inst fields: only {total_fields} fields parsed — the parser lost part of the enum"
    );
}

// ---------------------------------------------------------------------------
// Mutation controls: each axis added by WS2.18 REFUSES the drift it exists to
// catch, by name — and is green on the unmutated sources (the tests above).
// ---------------------------------------------------------------------------

/// Removing `Constant.bytes` from the Lean model fails the `Constant` axis,
/// naming the missing constructor.
#[test]
fn mutation_removing_lean_constant_bytes_fails_the_constant_axis() {
    let constant_rs =
        std::fs::read_to_string(manifest().join("src/constant.rs")).expect("constant.rs");
    let lean_constant = read_required(lean_dir().join("Constant.lean"));
    let mutated: String = lean_constant
        .lines()
        .filter(|line| !line.trim_start().starts_with("| bytes "))
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(
        mutated.lines().count(),
        lean_constant.lines().count(),
        "mutation applied"
    );
    let fragment = semr_constant_fragment().expect("constant ledger");
    let rust = old_gate_constants(&rust_enum_variants(&constant_rs, "Constant"), &fragment);
    let reason = parity_drift(
        "Constant",
        &rust,
        &lean_constructors_any_case(&mutated, "Constant"),
        &[],
    )
    .expect_err("a Lean model without `bytes` must fail the Constant axis");
    assert!(
        reason.contains("NO Lean constructor") && reason.contains("\"bytes\""),
        "{reason}"
    );
    // Control: the unmutated model passes (the refusal is the mutation's).
    parity_drift(
        "Constant",
        &rust,
        &lean_constructors_any_case(&lean_constant, "Constant"),
        &[],
    )
    .expect("unmutated Constant axis is green");
}

/// Removing `ContainerVtable` from the Lean `FatPtrKind` fails that axis.
#[test]
fn mutation_removing_lean_container_vtable_fails_the_fat_ptr_kind_axis() {
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let mutated: String = lean_basic
        .lines()
        .filter(|line| !line.trim_start().starts_with("| ContainerVtable"))
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(
        mutated.lines().count(),
        lean_basic.lines().count(),
        "mutation applied"
    );
    let reason = parity_drift(
        "FatPtrKind",
        &rust_enum_variants(&ty_rs, "FatPtrKind"),
        &lean_constructors(&mutated, "FatPtrKind"),
        &[],
    )
    .expect_err("a Lean FatPtrKind without ContainerVtable must fail");
    assert!(reason.contains("\"ContainerVtable\""), "{reason}");
}

/// Adding a Rust `Inst` field with no Lean binder fails the field axis,
/// naming the variant and the missing binder.
#[test]
fn mutation_adding_a_rust_inst_field_without_a_lean_binder_fails_the_field_axis() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let lean_inst = read_required(lean_dir().join("Inst.lean"));
    let anchor = "        exhaustive_enum_unreachable: bool,\n";
    assert_eq!(inst_rs.matches(anchor).count(), 1, "unique Switch anchor");
    let mutated = inst_rs.replacen(anchor, &format!("{anchor}        likely_case: u32,\n"), 1);
    let reason = inst_field_drift(&mutated, &lean_inst, INST_FIELD_ALLOWLIST)
        .expect_err("a Rust Switch field with no Lean binder must fail the field axis");
    assert!(
        reason.contains("Switch:") && reason.contains("likelyCase"),
        "{reason}"
    );
    // Control: a REORDER is drift too (the axis compares in order) ...
    let reordered = inst_rs.replacen(
        "        then_val: ValueId,\n        else_val: ValueId,\n",
        "        else_val: ValueId,\n        then_val: ValueId,\n",
        1,
    );
    assert_ne!(reordered, inst_rs, "reorder mutation applied");
    let reason = inst_field_drift(&reordered, &lean_inst, INST_FIELD_ALLOWLIST)
        .expect_err("reordered Select fields must fail");
    assert!(reason.contains("Select:"), "{reason}");
    // ... and the unmutated sources are green (no over-refusal).
    inst_field_drift(&inst_rs, &lean_inst, INST_FIELD_ALLOWLIST)
        .expect("unmutated field axis is green");
}

/// Dropping a Lean binder (the pre-WS2.18 shape of `Switch`) fails the axis,
/// and allowlisting exactly that gap is the only way to accept it.
#[test]
fn mutation_dropping_the_lean_switch_exhaustive_binder_fails_unless_allowlisted() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let lean_inst = read_required(lean_dir().join("Inst.lean"));
    let binder = " (exhaustiveEnumUnreachable : Bool)";
    assert_eq!(
        lean_inst.matches(binder).count(),
        1,
        "unique Lean Switch binder"
    );
    let mutated = lean_inst.replacen(binder, "", 1);
    let reason = inst_field_drift(&inst_rs, &mutated, &[])
        .expect_err("a Lean Switch without the exhaustive binder must fail");
    assert!(reason.contains("exhaustiveEnumUnreachable"), "{reason}");
    inst_field_drift(
        &inst_rs,
        &mutated,
        &[("Switch", "exhaustiveEnumUnreachable")],
    )
    .expect("an allowlisted gap is accepted");
    // A stale allowlist entry (the gap is closed) is itself a failure.
    let reason = inst_field_drift(
        &inst_rs,
        &lean_inst,
        &[("Switch", "exhaustiveEnumUnreachable")],
    )
    .expect_err("a stale field allowlist entry must fail");
    assert!(reason.contains("no longer gaps"), "{reason}");
}

/// Review of WS2.18 — three drifts the implementer's controls did not write,
/// each of which must be CAUGHT by name: a renamed Lean binder (same arity,
/// so an arity-only check would pass), a second positional field on the tuple
/// variant `DialectOp` (the exception-table path), and a Rust `Constant`
/// variant with no Lean constructor (the implementer's control only REMOVED a
/// Lean constructor).
#[test]
fn review_mutations_renamed_binder_tuple_arity_and_new_rust_constant_are_caught() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let lean_inst = read_required(lean_dir().join("Inst.lean"));

    // (1) Rename the Lean `CallIndirect` convention binder: arity unchanged.
    let binder = "(callingConv : CallingConv)";
    let constructor = concat!(
        "  | CallIndirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId)\n",
        "                 (callingConv : CallingConv) : Inst",
    );
    assert_eq!(
        lean_inst.matches(constructor).count(),
        1,
        "unique ordinary Lean CallIndirect constructor"
    );
    let renamed = lean_inst.replacen(
        constructor,
        &constructor.replace(binder, "(conv : CallingConv)"),
        1,
    );
    let reason = inst_field_drift(&inst_rs, &renamed, INST_FIELD_ALLOWLIST)
        .expect_err("a renamed Lean binder is field drift");
    assert!(
        reason.contains("CallIndirect:") && reason.contains("callingConv"),
        "{reason}"
    );

    // (2) Give the tuple variant `DialectOp` a second positional field.
    let tuple = "    DialectOp(Box<crate::dialect::DialectInst>),\n";
    assert_eq!(inst_rs.matches(tuple).count(), 1, "unique DialectOp anchor");
    let widened = inst_rs.replacen(
        tuple,
        "    DialectOp(Box<crate::dialect::DialectInst>, u32),\n",
        1,
    );
    let reason = inst_field_drift(&widened, &lean_inst, INST_FIELD_ALLOWLIST)
        .expect_err("a second positional DialectOp field has no Lean binder");
    assert!(reason.contains("DialectOp:"), "{reason}");

    // (3) A new Rust `Constant` variant with no Lean constructor.
    let constant_rs =
        std::fs::read_to_string(manifest().join("src/constant.rs")).expect("constant.rs");
    let lean_constant = read_required(lean_dir().join("Constant.lean"));
    let unit = "    PhantomData,\n";
    assert_eq!(
        constant_rs.matches(unit).count(),
        1,
        "unique PhantomData anchor"
    );
    let grown = constant_rs.replacen(unit, "    PhantomData,\n    Poison,\n", 1);
    let rust = old_gate_constants(
        &rust_enum_variants(&grown, "Constant"),
        &semr_constant_fragment().expect("constant ledger"),
    );
    let reason = parity_drift(
        "Constant",
        &rust,
        &lean_constructors_any_case(&lean_constant, "Constant"),
        &[],
    )
    .expect_err("a Rust Constant variant with no Lean constructor must fail");
    assert!(reason.contains("\"poison\""), "{reason}");
    assert!(!reason.contains("tensorBlob"), "{reason}");

    // (4) Drop a Lean calling convention: the `CallingConv` mirror axis fails.
    let lib_rs = std::fs::read_to_string(manifest().join("src/lib.rs")).expect("lib.rs");
    // The mirror lives in Basic.lean (moved there with wire v60).
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let swift = "  | Swift : CallingConv\n";
    assert_eq!(
        lean_basic.matches(swift).count(),
        1,
        "unique Lean Swift ctor"
    );
    let reason = parity_drift(
        "CallingConv",
        &rust_enum_variants(&lib_rs, "CallingConv"),
        &lean_constructors(&lean_basic.replacen(swift, "", 1), "CallingConv"),
        &[],
    )
    .expect_err("a Lean CallingConv without Swift must fail");
    assert!(reason.contains("\"Swift\""), "{reason}");
}

/// Canonical compact variants keep actual field names and nested type commas.
#[test]
fn compact_named_variant_fields_keep_order_and_nested_type_commas() {
    let rust = "pub enum Inst {\nOne { variant: u32 },\nTwo { first: Vec<(Ty, ValueId)>, second: fn(Ty) -> ValueId },\nEmpty {},\n}\n";
    assert_eq!(
        rust_enum_variant_fields(rust, "Inst").unwrap(),
        vec![
            ("One".to_string(), vec!["variant".to_string()]),
            (
                "Two".to_string(),
                vec!["first".to_string(), "second".to_string()]
            ),
            ("Empty".to_string(), vec![]),
        ]
    );
}

#[test]
fn compact_named_variant_fields_refuse_malformed_and_wrong_field_shapes() {
    for variant in [
        "Broken { field: },",
        "Broken { field: Ty,, },",
        "Broken { field: Vec<Ty },",
        "Broken { field: Ty] },",
        "Broken { field: Ty } trailing,",
        "Broken { field: Ty, field: Ty },",
        "Broken { 0field: Ty },",
    ] {
        let rust = format!("pub enum Inst {{\n{variant}\n}}\n");
        let error = rust_enum_variant_fields(&rust, "Inst").expect_err("malformed compact body");
        assert!(error.contains("Broken"), "{error}");
    }
    let lean = "inductive Inst where\n  | Foo (variant : Ty) : Inst\n";
    let good = "pub enum Inst {\nFoo { variant: Ty },\n}\n";
    inst_field_drift(good, lean, &[]).expect("known complete field shape");
    for wrong in [
        "pub enum Inst {\nFoo { other: Ty },\n}\n",
        "pub enum Inst {\nFoo { variant: Ty, extra: Ty },\n}\n",
    ] {
        let error =
            inst_field_drift(wrong, lean, &[]).expect_err("wrong named fields must fail axis");
        assert!(error.contains("Foo"), "{error}");
    }
}

/// The parsers fail LOUDLY on a shape they were not written for (the
/// increment's named risk): never a silently-empty field list.
#[test]
fn field_parsers_refuse_unparseable_shapes_by_name() {
    let arrow = "inductive Inst where\n  | Weird : ValueId → Inst\n  deriving Repr\n";
    let reason = lean_inductive_ctor_texts(arrow, "Inst")
        .and_then(|ctors| {
            ctors
                .into_iter()
                .map(|(n, sig)| lean_ctor_binders(&n, &sig, "Inst"))
                .collect::<Result<Vec<_>, _>>()
        })
        .expect_err("an arrow-typed constructor has no binder names");
    assert!(
        reason.contains("Inst.Weird") && reason.contains("unnamed"),
        "{reason}"
    );

    let rust = "pub enum Inst {\n    Odd {\n        a: u32, b: u32,\n    },\n}\n";
    let reason = rust_enum_variant_fields(rust, "Inst").expect_err("two fields on one line");
    assert!(reason.contains("Inst::Odd"), "{reason}");

    let rust = "pub enum Inst {\n    Split(\n        u32,\n    ),\n}\n";
    let reason = rust_enum_variant_fields(rust, "Inst").expect_err("multi-line tuple variant");
    assert!(reason.contains("Inst::Split"), "{reason}");
}

// ---------------------------------------------------------------------------
// Proof-program ratchet rows (roadmap WS2.18 "Ratchets"), each named after
// its row in reports/2026-09-17-two-language-proof-program.
// ---------------------------------------------------------------------------

/// Row `trust-ir-self-declared/lean-mirror-name-debt`: "name-level Rust<->Lean
/// parity closed with ALL allowlists empty" was true of three axes while the
/// `FatPtrKind` axis carried two entries and `Constant` had no axis. Now every
/// name axis is gated with an empty allowlist, and the constructs the row
/// named (`Arc<str>` = ContainerLen, `Arc<dyn Any>` = ContainerVtable, string
/// literal = Bytes, fn-pointer table = FnDef / SymbolAddr) are expressible.
#[test]
fn trust_ir_self_declared_lean_mirror_name_debt() {
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let lean_constant = read_required(lean_dir().join("Constant.lean"));
    let kinds = lean_constructors(&lean_basic, "FatPtrKind");
    for kind in ["ContainerLen", "ContainerVtable"] {
        assert!(kinds.contains(kind), "Lean FatPtrKind lacks {kind}");
    }
    let consts = lean_constructors_any_case(&lean_constant, "Constant");
    for c in [
        "u128",
        "bytes",
        "array",
        "fnDef",
        "symbolAddr",
        "phantomData",
        "splat",
    ] {
        assert!(consts.contains(c), "Lean Constant lacks {c}");
    }
    // This file carries no non-empty name allowlist: every `const
    // *_ALLOWLIST: &[..] = &[..]` literal is the empty slice.
    let this = std::fs::read_to_string(manifest().join("tests/lean_schema_parity.rs"))
        .expect("this test file");
    for line in this.lines().map(str::trim) {
        if line.starts_with("const ") && line.contains("_ALLOWLIST:") {
            assert!(
                line.ends_with("= &[];"),
                "a non-empty parity allowlist is back: `{line}`"
            );
        }
    }
}

/// Row `small-designs/OMET-13-lean-schema-parity-and-extern-semantics`,
/// field-parity half: "Switch with exhaustive_enum_unreachable=true vs false
/// must be distinguishable in the Lean Inst mirror (fails today)", and the
/// indirect-call calling convention likewise. The row's EXTERN-semantics half
/// (no referee executes a bodyless callee) is out of this increment's scope.
#[test]
fn small_designs_omet_13_lean_schema_parity_field_half() {
    let lean_inst = read_required(lean_dir().join("Inst.lean"));
    let ctors: BTreeMap<String, Vec<String>> = lean_inductive_ctor_texts(&lean_inst, "Inst")
        .expect("Inst.lean parses")
        .into_iter()
        .map(|(n, sig)| {
            let binders = lean_ctor_binders(&n, &sig, "Inst").expect("binders parse");
            (n, binders)
        })
        .collect();
    assert!(
        ctors["Switch"]
            .iter()
            .any(|b| b == "exhaustiveEnumUnreachable"),
        "Lean Switch cannot distinguish exhaustive_enum_unreachable true/false: {:?}",
        ctors["Switch"]
    );
    assert!(
        ctors["CallIndirect"].iter().any(|b| b == "callingConv"),
        "Lean CallIndirect has no calling convention: {:?}",
        ctors["CallIndirect"]
    );
    // The mirror lives in Basic.lean (moved there with wire v60).
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    assert!(
        lean_basic.contains("inductive CallingConv where"),
        "Lean CallingConv mirror is missing"
    );
    // The Lean CallingConv mirrors every Rust convention.
    let lib_rs = std::fs::read_to_string(manifest().join("src/lib.rs")).expect("lib.rs");
    assert_parity(
        "CallingConv",
        &rust_enum_variants(&lib_rs, "CallingConv"),
        &lean_constructors(&lean_basic, "CallingConv"),
        &[],
    );
}

/// The arms of a Lean definition by pattern matching (`def NAME : A → B`):
/// every `| <lhs> => <rhs>` line after the `def NAME` head, up to the first
/// blank line. Returned as `(lhs, rhs)` with whitespace collapsed.
fn lean_match_arms(src: &str, def_head: &str) -> Vec<(String, String)> {
    let start = src
        .find(def_head)
        .unwrap_or_else(|| panic!("`{def_head}` vanished from the Lean model"));
    let mut arms = Vec::new();
    for line in src[start + def_head.len()..].lines().skip(1) {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            break;
        }
        if let Some(arm) = trimmed.strip_prefix("| ")
            && let Some((lhs, rhs)) = arm.split_once("=>")
        {
            let collapse = |s: &str| s.split_whitespace().collect::<Vec<_>>().join(" ");
            arms.push((collapse(lhs), collapse(rhs)));
        }
    }
    arms
}

/// The Lean constructor name a `FatPtrKind` pattern like `.Slice _` names.
fn lean_kind_pattern_name(pattern: &str) -> Option<String> {
    let name = pattern.trim().strip_prefix('.')?;
    let end = name
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(name.len());
    Some(name[..end].to_string())
}

/// WS3.19: the `FatPtrKind` name-parity axis is empty, but a NAME match would
/// also accept a Lean model that put `ContainerLen` on the vtable lane and
/// `ContainerVtable` on the length lane — exactly the type confusion the Rust
/// `PointerMetadataShape::metadata_ty` comment forbids. This pins, per kind,
/// that the Lean `FatPtrKind.metadataTy` lane and the single lane
/// `metadataTyMatches` accepts both equal Rust's `metadata_ty(64)` (the Lean
/// executable model is the fixed 64-bit target). The Lean build's executable
/// fixtures (`ptr_metadata_container_len_yields_u64_stable` and its
/// lane-swapped twins in `Semantics/ExecutableFixtures.lean`) check the same
/// thing semantically; this is the half that runs without a Lean toolchain.
#[test]
fn fat_ptr_kind_metadata_lanes_agree_with_rust() {
    use trust_ir::{FatPtrKind, Ty, TyId};

    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let rust_names = rust_enum_variants(&ty_rs, "FatPtrKind");
    // One representative per Rust variant. Exhaustive by construction: the
    // `match` below stops compiling when a variant is added.
    let kinds = [
        FatPtrKind::Slice(TyId::new(0)),
        FatPtrKind::Str,
        FatPtrKind::TraitObject { trait_id: 7 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ];
    let name_of = |kind: &FatPtrKind| -> &'static str {
        match kind {
            FatPtrKind::Slice(_) => "Slice",
            FatPtrKind::Str => "Str",
            FatPtrKind::TraitObject { .. } => "TraitObject",
            FatPtrKind::ContainerLen => "ContainerLen",
            FatPtrKind::ContainerVtable => "ContainerVtable",
        }
    };
    let covered: BTreeSet<String> = kinds.iter().map(|k| name_of(k).to_string()).collect();
    assert_eq!(
        covered, rust_names,
        "every Rust FatPtrKind variant needs a representative here"
    );

    let lean_memory = read_required(lean_dir().join("Semantics/Memory.lean"));
    let lean_lane = |ty: &Ty| -> &'static str {
        match ty {
            Ty::U64 => "U64",
            Ty::Ptr => "Ptr",
            other => panic!("Rust metadata_ty(64) left the two-lane model: {other:?}"),
        }
    };

    // `FatPtrKind.metadataTy`: `| .Kind .. => .Lane`.
    let metadata_ty: Vec<(String, String)> =
        lean_match_arms(&lean_memory, "def FatPtrKind.metadataTy : FatPtrKind → Ty")
            .into_iter()
            .map(|(lhs, rhs)| {
                let kind = lean_kind_pattern_name(&lhs)
                    .unwrap_or_else(|| panic!("unparsed metadataTy arm `{lhs}`"));
                let lane = rhs.trim_start_matches('.').to_string();
                (kind, lane)
            })
            .collect();
    // `metadataTyMatches`: `| .Lane, .Kind .. => true`; the catch-all
    // `| _, _ => false` must be the only other arm.
    let mut matches: Vec<(String, String)> = Vec::new();
    for (lhs, rhs) in lean_match_arms(
        &lean_memory,
        "def metadataTyMatches : Ty → FatPtrKind → Bool",
    ) {
        let (lane, kind) = lhs
            .split_once(',')
            .unwrap_or_else(|| panic!("unparsed metadataTyMatches arm `{lhs}`"));
        if rhs == "true" {
            let kind = lean_kind_pattern_name(kind)
                .unwrap_or_else(|| panic!("unparsed metadataTyMatches kind `{kind}`"));
            matches.push((kind, lane.trim().trim_start_matches('.').to_string()));
        } else {
            assert_eq!(
                (lane.trim(), kind.trim(), rhs.as_str()),
                ("_", "_", "false"),
                "metadataTyMatches may only have `true` arms plus the catch-all refusal"
            );
        }
    }

    for kind in &kinds {
        let name = name_of(kind);
        let rust_ty = kind
            .metadata_ty(64)
            .unwrap_or_else(|| panic!("{name}: Rust has no 64-bit metadata type"));
        let want = lean_lane(&rust_ty);
        let lean_ty: Vec<&String> = metadata_ty
            .iter()
            .filter(|(k, _)| k == name)
            .map(|(_, lane)| lane)
            .collect();
        assert_eq!(
            lean_ty,
            vec![want],
            "{name}: Lean `FatPtrKind.metadataTy` must put it on exactly the `{want}` lane \
             (Rust `metadata_ty(64)` = {rust_ty:?})"
        );
        let accepted: Vec<&String> = matches
            .iter()
            .filter(|(k, _)| k == name)
            .map(|(_, lane)| lane)
            .collect();
        assert_eq!(
            accepted,
            vec![want],
            "{name}: Lean `metadataTyMatches` must accept exactly the `{want}` lane"
        );
    }
    assert_eq!(
        metadata_ty.len(),
        kinds.len(),
        "Lean `FatPtrKind.metadataTy` has an arm for a kind Rust does not have"
    );
    assert_eq!(
        matches.len(),
        kinds.len(),
        "Lean `metadataTyMatches` accepts a (lane, kind) pair beyond one per Rust kind"
    );
}

/// The v30 PREDICATE LATTICE axis: `Pred` / `Space` / `Universe`.
///
/// `Ty::Refine` landed with a Lean constructor, but the lattice it points at
/// (`crates/trust-ir/src/pred.rs`) was unmodelled — so the consumption rule in
/// `trust-ir-build/src/validate.rs` rested on an unverified claim about
/// `implies`. `lean/trust_ir-semantics/TrustIr/Pred.lean` now models it and
/// `TrustIr/Proofs/PredLatticeProps.lean` proves `implies` sound against a
/// denotation. This gate is what keeps the two from drifting: a new Rust
/// predicate shape with no Lean constructor fails here, and so does a stale
/// allowlist entry.
///
/// Same limitation as the axis above, stated plainly: this matches
/// constructor NAMES mechanically (there is no Lean toolchain in CI, or on the
/// authoring box). It cannot see whether the Lean semantics is *right*; the
/// denotation and the proofs are what carry that, and the last block below at
/// least keeps them from being deleted silently.
#[test]
fn pred_lattice_tracks_the_lean_model() {
    let pred_rs = std::fs::read_to_string(manifest().join("src/pred.rs")).expect("pred.rs");
    let lean_pred = read_required(lean_dir().join("Pred.lean"));

    // --- Pred ---
    // The Lean `Pred` is the TREE form (children inline) and `PredEntry` is
    // the id-spelled table form Rust stores; both carry these same nine
    // constructor names, and `PredTable.resolve` unfolds one into the other.
    let rust_pred = rust_enum_variants(&pred_rs, "Pred");
    let lean_pred_ctors = lean_constructors(&lean_pred, "Pred");
    // EMPTY — every Rust `Pred` variant has a Lean constructor, a denotation
    // arm (`Pred.denote`) and an `implies` arm. Keep it empty: a predicate
    // shape with no Lean meaning is a hole in exactly the mechanism the typed
    // value model exists to close.
    const PRED_ALLOWLIST: &[&str] = &[];
    assert_parity("Pred", &rust_pred, &lean_pred_ctors, PRED_ALLOWLIST);

    // --- Space ---
    // The index-vs-member distinction IS the miscompile class. If a third
    // convention is ever added to Rust without a Lean constructor, the
    // soundness proof stops covering it — fail here instead.
    let rust_space = rust_enum_variants(&pred_rs, "Space");
    let lean_space_ctors = lean_constructors(&lean_pred, "Space");
    const SPACE_ALLOWLIST: &[&str] = &[];
    assert_parity("Space", &rust_space, &lean_space_ctors, SPACE_ALLOWLIST);

    // --- Universe ---
    let rust_universe = rust_enum_variants(&pred_rs, "Universe");
    let lean_universe_ctors = lean_constructors(&lean_pred, "Universe");
    const UNIVERSE_ALLOWLIST: &[&str] = &[];
    assert_parity(
        "Universe",
        &rust_universe,
        &lean_universe_ctors,
        UNIVERSE_ALLOWLIST,
    );

    // --- The model is more than a name list ---
    // Names alone would pass on a file that declared the constructors and
    // nothing else. These check that the pieces the soundness argument needs
    // are still present: a denotation, the decision procedure, the join, and
    // the theorems stated against them. (Presence, not correctness — only a
    // Lean toolchain can give correctness, and there is none here.)
    for needle in [
        "def Pred.denote",
        "def Pred.impliesFuel",
        "def Pred.join",
        "def constDenote",
        "def Universe.contains",
    ] {
        assert!(
            lean_pred.contains(needle),
            "Pred lattice: `{needle}` vanished from TrustIr/Pred.lean — the parity gate \
             cannot certify constructor names against a model that no longer has a \
             denotation or a decision procedure"
        );
    }
    let lean_props = read_required(lean_dir().join("Proofs/PredLatticeProps.lean"));
    for needle in [
        "theorem impliesFuel_sound",
        "theorem implies_sound",
        "theorem join_upper_bound_left",
        "theorem join_upper_bound_right",
        "theorem denote_Top",
        "theorem index_never_implies_member",
    ] {
        assert!(
            lean_props.contains(needle),
            "Pred lattice: `{needle}` is missing from \
             TrustIr/Proofs/PredLatticeProps.lean — the consumption rule's soundness \
             claim has no statement backing it"
        );
    }
    // No `sorry` may creep into the lattice proofs: a `sorry` would satisfy
    // every `contains` check above while proving nothing, and would surface in
    // the Lean build only as a `sorryAx` in the axiom audit.
    for (name, src) in [
        ("Pred.lean", &lean_pred),
        ("PredLatticeProps.lean", &lean_props),
    ] {
        assert!(
            !src.contains("sorry"),
            "{name} contains `sorry` — the lattice soundness proof must not be stubbed"
        );
    }
}

/// Amendment S: the `Ext` variant leaves a level-R axis only because `NoExt`
/// is uninhabited. Give `NoExt` a variant and the `Ty` axis must fail, naming
/// `Ext` — the exclusion is a rule about the level-R type, not an allowlist.
#[test]
fn giving_noext_a_variant_fails_the_ty_axis() {
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let level_rs = read_level_rs();
    assert!(
        noext_is_empty(&level_rs),
        "NoExt has no variant on the tree"
    );
    let lean = lean_constructors(&lean_basic, "Ty");
    let ty_fragment = semr_ty_fragment().expect("TY_FRAGMENT.tsv");
    let rust = outside_semr_fragment(
        &rust_enum_variants_at_level(&ty_rs, "Ty", &level_rs),
        &ty_fragment,
    );
    assert!(
        !rust.contains("Ext"),
        "Ext is excluded while NoExt is empty"
    );
    parity_drift("Ty", &rust, &lean, &[]).expect("the tree's Ty axis is in parity");

    let anchor = "pub enum NoExt {}";
    assert_eq!(level_rs.matches(anchor).count(), 1, "unique NoExt anchor");
    let inhabited = level_rs.replacen(anchor, "pub enum NoExt {\n    Param(u32),\n}", 1);
    assert!(!noext_is_empty(&inhabited));
    let rust = outside_semr_fragment(
        &rust_enum_variants_at_level(&ty_rs, "Ty", &inhabited),
        &ty_fragment,
    );
    assert!(
        rust.contains("Ext"),
        "an inhabited NoExt keeps Ext on the axis"
    );
    let reason = parity_drift("Ty", &rust, &lean, &[]).expect_err("the axis must fail");
    assert!(reason.contains("Ext"), "the drift names Ext: {reason}");
}

/// The `TemplateTy` axis of amendment S, as (Rust, Lean) constructor sets: a
/// level-S type is every `TyG` variant but `Ext`, whose payload at level S is
/// a `TemplateRef`, plus one constructor per `TemplateRef` variant
/// (`Param` -> `param`, `Hole` -> `hole`, through `lower_first`). A type
/// former of SemR's type fragment (`TY_FRAGMENT.tsv`) is not a level-S type:
/// `trust_ir::template` refuses every occurrence of one in a template (T8;
/// `template_refuses_every_semr_fragment_type` in trust-ir-build's
/// `tests/template_validation.rs`), so it has no
/// `TemplateTy` constructor.
fn template_ty_axis(
    ty_rs: &str,
    level_rs: &str,
    lean_template: &str,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut rust = rust_enum_variants_raw(ty_rs, "Ty");
    assert!(rust.remove("Ext"), "TyG carries its Ext variant");
    for (variant, _) in semr_ty_fragment().unwrap_or_else(|e| panic!("{e}")) {
        assert!(
            rust.remove(&variant),
            "TY_FRAGMENT.tsv row `{variant}` is a TyG variant"
        );
    }
    let refs = rust_enum_variants_raw(level_rs, "TemplateRef");
    assert!(refs.len() >= 2, "TemplateRef parsed: {refs:?}");
    rust.extend(refs.iter().map(|name| lower_first(name)));
    (
        rust,
        lean_constructors_any_case(lean_template, "TemplateTy"),
    )
}

/// Exact, both ways: Lean may neither lack a level-S constructor nor carry
/// one Rust does not.
fn template_ty_drift(rust: &BTreeSet<String>, lean: &BTreeSet<String>) -> Result<(), String> {
    parity_drift("TemplateTy", rust, lean, &[])?;
    let extra: Vec<&String> = lean.difference(rust).collect();
    if extra.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "TemplateTy: Lean constructors with no Rust counterpart: {extra:?}"
        ))
    }
}

/// Amendment S: Lean's `TemplateTy` (`TrustIr/Template.lean`) mirrors Rust's
/// `TyG<TemplateRef>` exactly, and its ground constructors are Lean's `Ty`
/// constructors, so `substTy` and `embed` range over every level-R type.
#[test]
fn template_ty_axis_tracks_the_lean_model() {
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let level_rs = read_level_rs();
    let lean_template = read_required(lean_dir().join("Template.lean"));
    let (rust, lean) = template_ty_axis(&ty_rs, &level_rs, &lean_template);
    template_ty_drift(&rust, &lean).unwrap_or_else(|reason| panic!("{reason}"));

    // The ground half is exactly Lean's level-R `Ty`.
    let lean_ty = lean_constructors(&read_required(lean_dir().join("Basic.lean")), "Ty");
    let ground: BTreeSet<String> = lean
        .iter()
        .filter(|name| name.starts_with(|c: char| c.is_ascii_uppercase()))
        .cloned()
        .collect();
    assert_eq!(
        ground, lean_ty,
        "TemplateTy's ground constructors are Lean's Ty"
    );

    // Mutation controls: a Lean model without `hole`, or a Rust `TyG` with a
    // variant Lean lacks, fails the axis by name.
    let without_hole = lean_template.replacen("  | hole : Nat -> TemplateTy\n", "", 1);
    assert_ne!(without_hole, lean_template, "the hole constructor anchor");
    let (rust, lean) = template_ty_axis(&ty_rs, &level_rs, &without_hole);
    let reason = template_ty_drift(&rust, &lean).expect_err("a missing hole fails");
    assert!(reason.contains("hole"), "{reason}");

    let anchor = "pub enum TyG<X> {";
    assert_eq!(ty_rs.matches(anchor).count(), 1, "unique TyG anchor");
    let grown = ty_rs.replacen(anchor, "pub enum TyG<X> {\n    Opaque,", 1);
    let (rust, lean) = template_ty_axis(&grown, &level_rs, &lean_template);
    let reason = template_ty_drift(&rust, &lean).expect_err("a new TyG variant fails");
    assert!(reason.contains("Opaque"), "{reason}");
}

// ---------------------------------------------------------------------------
// The SemR axis (Trust proven-core RM4; RM0 decision 4: "From RM4 the parity
// gate is SemR").
//
// `lean/semr/FRAGMENT.tsv` names the Rust `Inst` variants whose semantics is
// SemR's, each beside the SemR `Inst` constructor that runs it. This axis holds
// the ledger to both sides: every row names a Rust variant and a SemR
// constructor, no name is listed twice, and every SemR constructor belongs to
// exactly one of FRAGMENT.tsv (wire decoded) or QUOTED_MODEL.tsv (quoted-only,
// never produced by the decoder; no runtime parity credit). The SEMANTIC half of
// the gate, that SemR and the reference interpreter agree on every variant of
// the fragment, is the SemR differential's (`semr_parity_gate_*` in
// crates/trust-ir-conformance/tests/lean_exec_differential.rs), which needs
// `lake`; this half is toolchain-free.
// ---------------------------------------------------------------------------

fn semr_source() -> PathBuf {
    manifest().join("../../lean/semr/SemR.lean")
}

fn semr_fragment_ledger() -> PathBuf {
    manifest().join("../../lean/semr/FRAGMENT.tsv")
}

fn semr_quoted_ledger() -> PathBuf {
    manifest().join("../../lean/semr/QUOTED_MODEL.tsv")
}

fn semr_ty_fragment_ledger() -> PathBuf {
    manifest().join("../../lean/semr/TY_FRAGMENT.tsv")
}

fn semr_constant_fragment_ledger() -> PathBuf {
    manifest().join("../../lean/semr/CONSTANT_FRAGMENT.tsv")
}

/// Constructor, canonical boundary control, decoder boundary, model scope.
/// Private typed cells are explicitly not canonical byte-memory semantics.
fn parse_semr_quoted(text: &str) -> Result<Vec<(String, String, String, String)>, String> {
    let mut rows = Vec::new();
    let mut seen = BTreeSet::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim_end();
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let fields: Vec<_> = line.split('\t').collect();
        let ident =
            |s: &str| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        let boundary_matches_scope = match fields.as_slice() {
            [_, _, boundary, "quoted-op"] => boundary.strip_prefix("inst.").is_some_and(ident),
            [_, _, "decoded.memory", "abstract-cell"] => true,
            [
                "makeClosure",
                "MakeClosure",
                "closure_types",
                "quoted-closure",
            ] => true,
            _ => false,
        };
        if fields.len() != 4 || !ident(fields[0]) || !ident(fields[1]) || !boundary_matches_scope {
            return Err(format!(
                "QUOTED_MODEL.tsv line {}: malformed row `{line}`",
                i + 1
            ));
        }
        if !seen.insert(fields[0].to_string()) {
            return Err(format!(
                "QUOTED_MODEL.tsv: constructor `{}` listed twice",
                fields[0]
            ));
        }
        rows.push((
            fields[0].into(),
            fields[1].into(),
            fields[2].into(),
            fields[3].into(),
        ));
    }
    if rows.is_empty() {
        return Err("QUOTED_MODEL.tsv: no rows".into());
    }
    Ok(rows)
}

/// The `(rust variant, SemR constructor)` rows of a fragment ledger, or why
/// the text is malformed: a row is two tab-separated names; `#` lines and blank
/// lines are comments; a name listed twice is an error.
fn parse_semr_fragment(text: &str) -> Result<Vec<(String, String)>, String> {
    parse_semr_ledger("FRAGMENT.tsv", text)
}

/// [`parse_semr_fragment`]'s rules for the ledger named `ledger`
/// (`FRAGMENT.tsv` for `Inst`, `TY_FRAGMENT.tsv` for `Ty`).
fn parse_semr_ledger(ledger: &str, text: &str) -> Result<Vec<(String, String)>, String> {
    let mut rows: Vec<(String, String)> = Vec::new();
    let mut rust_seen = BTreeSet::new();
    let mut semr_seen = BTreeSet::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim_end();
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let ident =
            |s: &str| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        if fields.len() != 2 || !ident(fields[0]) || !ident(fields[1]) {
            return Err(format!(
                "{ledger} line {}: expected `<RustVariant>\\t<semrConstructor>`, got `{line}`",
                i + 1
            ));
        }
        if !rust_seen.insert(fields[0].to_string()) {
            return Err(format!(
                "{ledger}: Rust variant `{}` listed twice",
                fields[0]
            ));
        }
        if !semr_seen.insert(fields[1].to_string()) {
            return Err(format!(
                "{ledger}: SemR constructor `{}` listed twice",
                fields[1]
            ));
        }
        rows.push((fields[0].to_string(), fields[1].to_string()));
    }
    if rows.is_empty() {
        return Err(format!("{ledger}: no rows"));
    }
    Ok(rows)
}

fn semr_ty_fragment() -> Result<Vec<(String, String)>, String> {
    parse_semr_ledger("TY_FRAGMENT.tsv", &read_required(semr_ty_fragment_ledger()))
}

fn semr_constant_fragment() -> Result<Vec<(String, String)>, String> {
    parse_semr_ledger(
        "CONSTANT_FRAGMENT.tsv",
        &read_required(semr_constant_fragment_ledger()),
    )
}

/// The `Constant` variants the old gate judges, in the Lean model's case:
/// every Rust variant `CONSTANT_FRAGMENT.tsv` does not list (filtered by its
/// Rust name before [`lower_first`]).
fn old_gate_constants(all: &BTreeSet<String>, fragment: &[(String, String)]) -> BTreeSet<String> {
    outside_semr_fragment(all, fragment)
        .iter()
        .map(|name| lower_first(name))
        .collect()
}

fn semr_fragment() -> Result<Vec<(String, String)>, String> {
    parse_semr_fragment(&read_required(semr_fragment_ledger()))
}

/// The Rust variants outside SemR's fragment: the old gate's remainder.
fn outside_semr_fragment(
    rust: &BTreeSet<String>,
    fragment: &[(String, String)],
) -> BTreeSet<String> {
    let inside: BTreeSet<&String> = fragment.iter().map(|(r, _)| r).collect();
    rust.iter()
        .filter(|v| !inside.contains(v))
        .cloned()
        .collect()
}

/// Constructors of SemR's `inductive Inst where`, including documented,
/// multiline binder lists. Unrecognized indented declarations fail closed.
fn semr_inst_constructors(src: &str) -> Result<BTreeSet<String>, String> {
    semr_inductive_constructors(src, "Inst")
}

/// Constructors of SemR's `inductive <name> where`, by
/// [`semr_inst_constructors`]'s rules.
fn semr_inductive_constructors(src: &str, name: &str) -> Result<BTreeSet<String>, String> {
    let src = strip_lean_comments(src);
    let needle = format!("inductive {name} where");
    let start = src
        .find(&needle)
        .ok_or_else(|| format!("SemR.lean: `{needle}` not found"))?;
    let mut out = BTreeSet::new();
    for line in src[start + needle.len()..].lines().skip(1) {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if !line.starts_with(char::is_whitespace) {
            break;
        }
        if line.starts_with("    ")
            && trimmed.starts_with('(')
            && trimmed.ends_with(')')
            && trimmed.contains(':')
            && !out.is_empty()
        {
            continue;
        }
        let Some(rest) = trimmed.strip_prefix('|') else {
            return Err(format!(
                "SemR.lean: unparseable line `{trimmed}` in `inductive {name}`"
            ));
        };
        let Some(ctor) = lean_ident_head(rest.trim_start()) else {
            return Err(format!(
                "SemR.lean: unparseable constructor line `{trimmed}`"
            ));
        };
        if !out.insert(ctor.clone()) {
            return Err(format!("SemR.lean: constructor `{ctor}` declared twice"));
        }
    }
    if out.is_empty() {
        return Err(format!("SemR.lean: `inductive {name}` has no constructors"));
    }
    Ok(out)
}

/// `TY_FRAGMENT.tsv` agrees with the Rust `Ty` and SemR's `Ty`, or the
/// reason: every row names a Rust variant that exists and a SemR constructor
/// SemR.lean declares. (SemR's other `Ty` constructors carry level-R types the
/// old gate already judges, `int` for twelve Rust variants among them, so the
/// map is not onto.)
fn semr_ty_fragment_drift(
    rust: &BTreeSet<String>,
    semr: &BTreeSet<String>,
    fragment: &[(String, String)],
) -> Result<(), String> {
    let no_rust: Vec<&String> = fragment
        .iter()
        .map(|(r, _)| r)
        .filter(|r| !rust.contains(*r))
        .collect();
    if !no_rust.is_empty() {
        return Err(format!(
            "SemR type fragment: TY_FRAGMENT.tsv names Rust Ty variants that do not exist: \
             {no_rust:?}"
        ));
    }
    let no_semr: Vec<&String> = fragment
        .iter()
        .map(|(_, s)| s)
        .filter(|s| !semr.contains(*s))
        .collect();
    if !no_semr.is_empty() {
        return Err(format!(
            "SemR type fragment: TY_FRAGMENT.tsv names SemR Ty constructors SemR.lean does \
             not declare (the type has no SemR semantics; drop the row, which returns the \
             variant to the old gate, or add the constructor): {no_semr:?}"
        ));
    }
    Ok(())
}

/// `CONSTANT_FRAGMENT.tsv` agrees with the Rust `Constant` and SemR's `Const`,
/// or the reason: every row names a Rust variant that exists and a SemR
/// constructor SemR.lean declares, and every SemR `Const` constructor is a
/// row's or names an old-gate variant (`int`, `bool`, `aggregate`, `uninit`:
/// constants the old gate already judges), so SemR declares no constant no
/// gate accounts for.
fn semr_constant_fragment_drift(
    rust: &BTreeSet<String>,
    semr: &BTreeSet<String>,
    fragment: &[(String, String)],
) -> Result<(), String> {
    let no_rust: Vec<&String> = fragment
        .iter()
        .map(|(r, _)| r)
        .filter(|r| !rust.contains(*r))
        .collect();
    if !no_rust.is_empty() {
        return Err(format!(
            "SemR constant fragment: CONSTANT_FRAGMENT.tsv names Rust Constant variants that \
             do not exist: {no_rust:?}"
        ));
    }
    let no_semr: Vec<&String> = fragment
        .iter()
        .map(|(_, s)| s)
        .filter(|s| !semr.contains(*s))
        .collect();
    if !no_semr.is_empty() {
        return Err(format!(
            "SemR constant fragment: CONSTANT_FRAGMENT.tsv names SemR Const constructors \
             SemR.lean does not declare (the constant has no SemR semantics; drop the row, \
             which returns the variant to the old gate, or add the constructor): {no_semr:?}"
        ));
    }
    let mut accounted = old_gate_constants(rust, fragment);
    accounted.extend(fragment.iter().map(|(_, s)| s.clone()));
    let unaccounted: Vec<&String> = semr.iter().filter(|s| !accounted.contains(*s)).collect();
    if !unaccounted.is_empty() {
        return Err(format!(
            "SemR constant fragment: SemR.lean declares Const constructors that are neither \
             a CONSTANT_FRAGMENT.tsv row nor an old-gate Constant variant: {unaccounted:?}"
        ));
    }
    Ok(())
}

/// The ledger agrees with the Rust `Inst` and SemR's `Inst`, or the reason.
fn semr_fragment_drift(
    rust: &BTreeSet<String>,
    semr: &BTreeSet<String>,
    fragment: &[(String, String)],
    quoted: &[(String, String, String, String)],
) -> Result<(), String> {
    let no_rust: Vec<&String> = fragment
        .iter()
        .map(|(r, _)| r)
        .filter(|r| !rust.contains(*r))
        .collect();
    if !no_rust.is_empty() {
        return Err(format!(
            "SemR fragment: FRAGMENT.tsv names Rust Inst variants that do not exist: {no_rust:?}"
        ));
    }
    let no_semr: Vec<&String> = fragment
        .iter()
        .map(|(_, s)| s)
        .filter(|s| !semr.contains(*s))
        .collect();
    if !no_semr.is_empty() {
        return Err(format!(
            "SemR fragment: FRAGMENT.tsv names SemR constructors SemR.lean does not declare \
             (the variant has no SemR semantics; drop the row or add the constructor and its \
             step rule): {no_semr:?}"
        ));
    }
    let mut listed: BTreeSet<&String> = fragment.iter().map(|(_, s)| s).collect();
    for (constructor, wire, _, _) in quoted {
        if !rust.contains(wire) || !semr.contains(constructor) {
            return Err(format!(
                "SemR quoted model: unknown constructor or canonical variant `{constructor}` / `{wire}`"
            ));
        }
        if !listed.insert(constructor) {
            return Err(format!(
                "SemR constructor `{constructor}` belongs to both ledgers or is repeated"
            ));
        }
    }
    let unlisted: Vec<&String> = semr.iter().filter(|s| !listed.contains(s)).collect();
    if !unlisted.is_empty() {
        return Err(format!(
            "SemR fragment: SemR.lean declares Inst constructors no ledger row names \
             (classify decoded or explicitly quoted-only): {unlisted:?}"
        ));
    }
    Ok(())
}

#[test]
fn inst_parity_reads_semr_for_its_fragment() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let rust_inst = rust_enum_variants(&inst_rs, "Inst");
    let semr =
        semr_inst_constructors(&read_required(semr_source())).unwrap_or_else(|e| panic!("{e}"));
    let fragment = semr_fragment().unwrap_or_else(|e| panic!("{e}"));
    let quoted = parse_semr_quoted(&read_required(semr_quoted_ledger())).expect("quoted ledger");
    semr_fragment_drift(&rust_inst, &semr, &fragment, &quoted).unwrap_or_else(|e| panic!("{e}"));
    // The two halves of the gate partition the Rust variants.
    let rest = outside_semr_fragment(&rust_inst, &fragment);
    assert_eq!(rest.len() + fragment.len(), rust_inst.len());
}

/// The `Ty` half of the SemR axis (v67 tensor region): every
/// `TY_FRAGMENT.tsv` row is a Rust `Ty` variant and a SemR `Ty` constructor,
/// and the rows and the old gate's remainder partition the Rust variants.
#[test]
fn ty_parity_reads_semr_for_its_type_fragment() {
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let rust_ty = rust_enum_variants(&ty_rs, "Ty");
    let semr_ty = semr_inductive_constructors(&read_required(semr_source()), "Ty")
        .unwrap_or_else(|e| panic!("{e}"));
    let fragment = semr_ty_fragment().unwrap_or_else(|e| panic!("{e}"));
    semr_ty_fragment_drift(&rust_ty, &semr_ty, &fragment).unwrap_or_else(|e| panic!("{e}"));
    let rest = outside_semr_fragment(&rust_ty, &fragment);
    assert_eq!(rest.len() + fragment.len(), rust_ty.len());
    // The type former is judged in SemR, and its instruction is in FRAGMENT.tsv.
    assert!(fragment.iter().any(|(r, s)| r == "Tensor" && s == "tensor"));
    let inst_fragment = semr_fragment().unwrap_or_else(|e| panic!("{e}"));
    assert!(inst_fragment.iter().any(|(r, _)| r == "TensorContract"));
}

/// The `Constant` half of the SemR axis (PKG-U13e, content-addressed weight
/// blobs): every `CONSTANT_FRAGMENT.tsv` row is a Rust `Constant` variant and
/// a SemR `Const` constructor, every SemR `Const` constructor is accounted
/// for, and the rows and the old gate's remainder partition the Rust
/// variants.
#[test]
fn constant_parity_reads_semr_for_its_constant_fragment() {
    let constant_rs =
        std::fs::read_to_string(manifest().join("src/constant.rs")).expect("constant.rs");
    let rust = rust_enum_variants(&constant_rs, "Constant");
    let semr = semr_inductive_constructors(&read_required(semr_source()), "Const")
        .unwrap_or_else(|e| panic!("{e}"));
    let fragment = semr_constant_fragment().unwrap_or_else(|e| panic!("{e}"));
    semr_constant_fragment_drift(&rust, &semr, &fragment).unwrap_or_else(|e| panic!("{e}"));
    let rest = outside_semr_fragment(&rust, &fragment);
    assert_eq!(rest.len() + fragment.len(), rust.len());
    // The blob is judged in SemR, over SemR's tensor type.
    assert!(
        fragment
            .iter()
            .any(|(r, s)| r == "TensorBlob" && s == "tensorBlob")
    );
    let ty_fragment = semr_ty_fragment().unwrap_or_else(|e| panic!("{e}"));
    assert!(ty_fragment.iter().any(|(r, _)| r == "Tensor"));
    assert!(
        semr.contains("int") && semr.contains("aggregate"),
        "the SemR Const parser saw the whole inductive: {semr:?}"
    );
}

/// Mutation controls for the `Constant` half of the SemR axis: each drift is
/// caught by name, and the unmutated ledger is the positive control.
#[test]
fn semr_constant_axis_mutations_are_caught() {
    let constant_rs =
        std::fs::read_to_string(manifest().join("src/constant.rs")).expect("constant.rs");
    let rust = rust_enum_variants(&constant_rs, "Constant");
    let semr_src = read_required(semr_source());
    let semr = semr_inductive_constructors(&semr_src, "Const").expect("SemR Const");
    let fragment = semr_constant_fragment().expect("ledger");
    assert_eq!(
        semr_constant_fragment_drift(&rust, &semr, &fragment),
        Ok(())
    );

    // SemR loses its blob constructor: the row is caught.
    let anchor = "  | tensorBlob (digest : List Nat) (dims : List Nat)\n";
    assert_eq!(
        semr_src.matches(anchor).count(),
        1,
        "unique SemR tensorBlob anchor"
    );
    let without = semr_inductive_constructors(&semr_src.replacen(anchor, "", 1), "Const")
        .expect("SemR Const without tensorBlob");
    let e = semr_constant_fragment_drift(&rust, &without, &fragment).unwrap_err();
    assert!(e.contains("\"tensorBlob\""), "{e}");

    // A row naming a Rust variant that does not exist (a rename).
    let mut renamed = fragment.clone();
    renamed[0].0 = "WeightBlob".into();
    let e = semr_constant_fragment_drift(&rust, &semr, &renamed).unwrap_err();
    assert!(e.contains("\"WeightBlob\""), "{e}");

    // Dropping the row returns the variant to the old gate, which fails by
    // name: the legacy Lean model has no blob; and SemR's constructor is then
    // unaccounted for.
    let lean_constant =
        lean_constructors_any_case(&read_required(lean_dir().join("Constant.lean")), "Constant");
    let dropped: Vec<(String, String)> = fragment
        .iter()
        .filter(|(r, _)| r != "TensorBlob")
        .cloned()
        .collect();
    let reason = parity_drift(
        "Constant",
        &old_gate_constants(&rust, &dropped),
        &lean_constant,
        &[],
    )
    .expect_err("an unlisted TensorBlob fails the old gate");
    assert!(reason.contains("\"tensorBlob\""), "{reason}");

    // A SemR constant neither a row nor an old-gate variant is unaccounted.
    let grown_semr = semr_src.replacen(anchor, &format!("{anchor}  | poison\n"), 1);
    let grown = semr_inductive_constructors(&grown_semr, "Const").expect("grown SemR Const");
    let e = semr_constant_fragment_drift(&rust, &grown, &fragment).unwrap_err();
    assert!(e.contains("\"poison\""), "{e}");

    // A new Rust Constant variant in neither half fails the old gate by name.
    let unit = "    PhantomData,\n";
    assert_eq!(
        constant_rs.matches(unit).count(),
        1,
        "unique PhantomData anchor"
    );
    let grown = rust_enum_variants(
        &constant_rs.replacen(unit, "    PhantomData,\n    Opaque,\n", 1),
        "Constant",
    );
    let reason = parity_drift(
        "Constant",
        &old_gate_constants(&grown, &fragment),
        &lean_constant,
        &[],
    )
    .expect_err("an unjudged variant fails");
    assert!(reason.contains("\"opaque\""), "{reason}");

    // Malformed ledgers and SemR sources fail closed.
    assert!(parse_semr_ledger("CONSTANT_FRAGMENT.tsv", "TensorBlob tensorBlob\n").is_err());
    assert!(
        parse_semr_ledger(
            "CONSTANT_FRAGMENT.tsv",
            "TensorBlob\ttensorBlob\nTensorBlob\tint\n"
        )
        .is_err()
    );
    assert!(
        parse_semr_ledger("CONSTANT_FRAGMENT.tsv", "# only a comment\n")
            .unwrap_err()
            .contains("CONSTANT_FRAGMENT.tsv")
    );
    assert!(semr_inductive_constructors("inductive Ty where\n  | int\n", "Const").is_err());
    assert!(semr_inductive_constructors("inductive Const where\n  ?? bad\n", "Const").is_err());
}

/// Mutation controls for the `Ty` half of the SemR axis: each drift is caught
/// by name, and the unmutated ledger is the positive control.
#[test]
fn semr_ty_axis_mutations_are_caught() {
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let rust_ty = rust_enum_variants(&ty_rs, "Ty");
    let semr_src = read_required(semr_source());
    let semr_ty = semr_inductive_constructors(&semr_src, "Ty").expect("SemR Ty");
    assert!(
        semr_ty.contains("tensor") && semr_ty.contains("int"),
        "{semr_ty:?}"
    );
    let fragment = semr_ty_fragment().expect("ledger");
    assert_eq!(
        semr_ty_fragment_drift(&rust_ty, &semr_ty, &fragment),
        Ok(())
    );

    // SemR loses its tensor constructor: the row is caught.
    let anchor = "  | tensor (elem : IntTy) (rank : Nat)\n";
    assert_eq!(
        semr_src.matches(anchor).count(),
        1,
        "unique SemR tensor anchor"
    );
    let without = semr_inductive_constructors(&semr_src.replacen(anchor, "", 1), "Ty")
        .expect("SemR Ty without tensor");
    let e = semr_ty_fragment_drift(&rust_ty, &without, &fragment).unwrap_err();
    assert!(e.contains("\"tensor\""), "{e}");

    // A row naming a Rust variant that does not exist (a rename).
    let mut renamed = fragment.clone();
    renamed[0].0 = "NdArray".into();
    let e = semr_ty_fragment_drift(&rust_ty, &semr_ty, &renamed).unwrap_err();
    assert!(e.contains("\"NdArray\""), "{e}");

    // Dropping the row returns the variant to the old gate, which fails by
    // name: the legacy Lean model has no tensor.
    let lean_ty = lean_constructors(&read_required(lean_dir().join("Basic.lean")), "Ty");
    let dropped: Vec<(String, String)> = fragment
        .iter()
        .filter(|(r, _)| r != "Tensor")
        .cloned()
        .collect();
    let reason = parity_drift(
        "Ty",
        &outside_semr_fragment(&rust_ty, &dropped),
        &lean_ty,
        &[],
    )
    .expect_err("an unlisted Tensor fails the old gate");
    assert!(reason.contains("Tensor"), "{reason}");

    // A new Rust Ty variant in neither half fails the old gate by name.
    let anchor = "pub enum TyG<X> {";
    assert_eq!(ty_rs.matches(anchor).count(), 1, "unique TyG anchor");
    let grown = rust_enum_variants(
        &ty_rs.replacen(anchor, "pub enum TyG<X> {\n    Opaque,", 1),
        "Ty",
    );
    let reason = parity_drift(
        "Ty",
        &outside_semr_fragment(&grown, &fragment),
        &lean_ty,
        &[],
    )
    .expect_err("an unjudged variant fails");
    assert!(reason.contains("Opaque"), "{reason}");

    // Malformed ledgers and SemR sources fail closed.
    assert!(parse_semr_ledger("TY_FRAGMENT.tsv", "Tensor tensor\n").is_err());
    assert!(parse_semr_ledger("TY_FRAGMENT.tsv", "Tensor\ttensor\nTensor\tint\n").is_err());
    assert!(parse_semr_ledger("TY_FRAGMENT.tsv", "Tensor\ttensor\nVector\ttensor\n").is_err());
    assert!(
        parse_semr_ledger("TY_FRAGMENT.tsv", "# only a comment\n")
            .unwrap_err()
            .contains("TY_FRAGMENT.tsv")
    );
    assert!(semr_inductive_constructors("inductive Inst where\n  | nop\n", "Ty").is_err());
    assert!(semr_inductive_constructors("inductive Ty where\n  ?? bad\n", "Ty").is_err());
}

/// Mutation controls for the SemR axis: each drift is caught by name, and the
/// unmutated ledger is the positive control.
#[test]
fn semr_axis_mutations_are_caught() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let rust_inst = rust_enum_variants(&inst_rs, "Inst");
    let semr_src = read_required(semr_source());
    let semr = semr_inst_constructors(&semr_src).expect("SemR Inst");
    let fragment = semr_fragment().expect("ledger");
    let quoted = parse_semr_quoted(&read_required(semr_quoted_ledger())).expect("quoted ledger");
    assert_eq!(
        semr_fragment_drift(&rust_inst, &semr, &fragment, &quoted),
        Ok(())
    );

    // A SemR constructor dropped from SemR.lean (the semantics is gone).
    let mut no_select = semr.clone();
    assert!(no_select.remove("select"));
    let e = semr_fragment_drift(&rust_inst, &no_select, &fragment, &quoted).unwrap_err();
    assert!(e.contains("\"select\""), "{e}");

    // A new SemR constructor nobody mapped.
    let mut extra = semr.clone();
    assert!(extra.insert("unclassifiedOperation".into()));
    let e = semr_fragment_drift(&rust_inst, &extra, &fragment, &quoted).unwrap_err();
    assert!(
        e.contains("\"unclassifiedOperation\"") && e.contains("no ledger row"),
        "{e}"
    );

    let mut extra = semr.clone();
    // (`fence`: a Rust variant SemR does not run; `switch` was this control's
    // name until VF5 put `Switch` in the fragment.)
    assert!(!semr.contains("fence"));
    extra.insert("fence".into());
    let e = semr_fragment_drift(&rust_inst, &extra, &fragment, &quoted).unwrap_err();
    assert!(
        e.contains("\"fence\"") && e.contains("no ledger row"),
        "{e}"
    );

    // A ledger row naming a Rust variant that does not exist (a rename).
    let mut renamed = fragment.clone();
    renamed[0].0 = "BinaryOp".into();
    let e = semr_fragment_drift(&rust_inst, &semr, &renamed, &quoted).unwrap_err();
    assert!(e.contains("\"BinaryOp\""), "{e}");

    // A row dropped from the ledger: its variant falls back to the old gate,
    // and its SemR constructor is unlisted.
    let dropped: Vec<_> = fragment
        .iter()
        .filter(|(r, _)| r != "Select")
        .cloned()
        .collect();
    let e = semr_fragment_drift(&rust_inst, &semr, &dropped, &quoted).unwrap_err();
    assert!(e.contains("\"select\""), "{e}");
    assert!(outside_semr_fragment(&rust_inst, &dropped).contains("Select"));

    // A quoted-only constructor cannot disappear, cross into runtime credit,
    // or name a nonexistent canonical boundary control.
    let mut no_quoted = quoted.clone();
    let absent = no_quoted.pop().unwrap();
    assert!(
        semr_fragment_drift(&rust_inst, &semr, &fragment, &no_quoted)
            .unwrap_err()
            .contains(&absent.0)
    );
    let mut overlapping = quoted.clone();
    overlapping[0].0 = "select".into();
    assert!(
        semr_fragment_drift(&rust_inst, &semr, &fragment, &overlapping)
            .unwrap_err()
            .contains("both ledgers")
    );
    let mut unknown = quoted.clone();
    unknown[0].1 = "InventedInstruction".into();
    assert!(
        semr_fragment_drift(&rust_inst, &semr, &fragment, &unknown)
            .unwrap_err()
            .contains("InventedInstruction")
    );
    assert!(parse_semr_quoted("undef\tUndef\tinst.undef\tdecoded\n").is_err());
    assert!(parse_semr_quoted("undef\tUndef\tdecoded.memory\tquoted-op\n").is_err());
    assert!(parse_semr_quoted("allocaCell\tAlloca\tinst.memory\tabstract-cell\n").is_err());
    assert!(parse_semr_quoted("allocaCell\tAlloca\tdecoded.memory\tabstract-cell\n").is_ok());
    assert!(
        parse_semr_quoted(
            "undef\tUndef\tinst.undef\tquoted-op\nundef\tUndef\tinst.undef\tquoted-op\n"
        )
        .is_err()
    );
    // The constructor's canonical image is v63, still refused at the wire
    // version boundary. No other constructor/scope pair may use this row.
    assert!(parse_semr_quoted("makeClosure\tMakeClosure\tclosure_types\tquoted-closure\n").is_ok());
    for row in [
        "makeClosure\tMakeClosure\tinst.make_closure\tquoted-closure\n",
        "makeClosure\tMakeClosure\twire_version\tquoted-closure\n",
        "makeClosure\tMakeClosure\twire_version\tquoted-op\n",
        "other\tMakeClosure\twire_version\tquoted-closure\n",
        "makeClosure\tOther\twire_version\tquoted-closure\n",
        "makeClosure\tMakeClosure\twire_version\tabstract-cell\n",
    ] {
        assert!(parse_semr_quoted(row).is_err(), "{row}");
    }
    assert!(parse_semr_quoted("# empty\n").is_err());

    // Malformed ledgers and SemR sources fail closed.
    assert!(parse_semr_fragment("BinOp binop\n").is_err());
    assert!(parse_semr_fragment("BinOp\tbinop\nBinOp\tunop\n").is_err());
    assert!(parse_semr_fragment("BinOp\tbinop\nUnOp\tbinop\n").is_err());
    assert!(parse_semr_fragment("# only a comment\n").is_err());
    assert!(semr_inst_constructors("inductive Inst where\n  | a\n  def x := 1\n").is_err());
    assert!(semr_inst_constructors("inductive Inst where\n\n").is_err());
    assert_eq!(semr_inst_constructors("inductive Inst where\n  /-- docs -/\n  | a (x : Nat)\n      (ys : List Nat)\n\nstructure Next where\n  | notAnInst\n").unwrap(), BTreeSet::from(["a".into()]));
}
