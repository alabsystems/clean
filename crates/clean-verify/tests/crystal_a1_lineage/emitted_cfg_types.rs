// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The type vocabulary both sides of the A1 gate are compared in.**
//!
//! Split out of `emitted_cfg.rs` on 2026-08-15, when the eighth chain's
//! `binop_tys` / `icmp_tys` / `rets` lanes took that file from 577 to 872 lines
//! — the same 500-line convention it was already split once for, at 945.
//!
//! An emitted operand type is a token in trust-ir's printed vocabulary (`u8`,
//! `f64`, `enum.13`); a Clean-side one is either an inline `IRTy` term or the
//! NAME of a registered alias (`ir_tU8`, `ir_vc_tu64`, `ir_fd_tf64`). This
//! module maps both onto one string so the lane comparator can use `assert_eq!`.
//!
//! **Two failure modes it is built to refuse.** An unrecognised token is
//! returned with a `?` prefix rather than dropped, so an unhandled type FAILS
//! the lane loudly instead of comparing equal to another unhandled one. And an
//! alias declared twice with different meanings is an assertion rather than a
//! last-writer-wins map entry — measured, not hypothetical: a chain's own unit
//! test quotes its type declaration verbatim, and the first version of the
//! scanner read the assertion's trailing `")` as part of the width.

use std::collections::BTreeMap;
use std::path::PathBuf;

/// Normalize a trust-ir type token to the vocabulary both sides are compared in.
///
/// `u8` -> `uint8`, `f64` -> `float64`, `enum.13` -> `enum13`. An unrecognised
/// token is returned with a `?` prefix rather than dropped, so an unhandled type
/// FAILS the lane loudly instead of comparing equal to another unhandled one.
pub(crate) fn norm_emitted_ty(tok: &str) -> String {
    let t = tok.trim_end_matches(',');
    let widthy = |p: &str, name: &str| -> Option<String> {
        t.strip_prefix(p)
            .filter(|w| !w.is_empty() && w.chars().all(|c| c.is_ascii_digit()))
            .map(|w| format!("{name}{w}"))
    };
    if let Some(s) = widthy("u", "uint") {
        return s;
    }
    if let Some(s) = widthy("i", "int") {
        return s;
    }
    if let Some(s) = widthy("f", "float") {
        return s;
    }
    for (p, name) in [
        ("enum.", "enum"),
        ("struct.", "struct"),
        ("tuple.", "tuple"),
        ("array.", "array"),
        ("functy.", "func"),
    ] {
        if let Some(w) = t.strip_prefix(p) {
            if !w.is_empty() && w.chars().all(|c| c.is_ascii_digit()) {
                return format!("{name}{w}");
            }
        }
    }
    match t {
        "bool" => "bool".to_string(),
        "ptr" => "ptr".to_string(),
        "unit" => "unit".to_string(),
        other => format!("?{other}"),
    }
}

/// `ir_d64` -> 64. The numeral convention is NAME-CARRIES-VALUE, and
/// `numeral_names_carry_their_values` in `crystal_a1_lineage.rs` proves it by
/// reading the registered `def ir_dK` chain rather than trusting it.
pub(crate) fn numeral_of(tok: &str) -> Option<u32> {
    tok.trim().strip_prefix("ir_d")?.parse::<u32>().ok()
}

/// Every `def <name> : IRTy := IRTy.<ctor> <arg>` registered anywhere in
/// `core_spec`, as `name -> normalized type`.
///
/// Scanned across the whole directory rather than one file because the type
/// aliases a chain uses are not all declared beside it: `ir_tU8` and `ir_tBool`
/// live in `eval_ir_crystal.rs` and are used by `eval_ir_contains.rs`.
pub(crate) fn clean_ty_aliases() -> BTreeMap<String, String> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec");
    let mut out = BTreeMap::new();
    // The `.rs` stages AND the GENERATED definition scripts. As of 2026-08-20
    // `has_cubical_layer`'s module is minted (crystal A2, `src/ir_mint`), so
    // `ir_h2_tmode` is a line in `generated/ir_h2.defs.txt` rather than a Rust
    // string literal. Missing it would leave the `load_tys` lane comparing
    // `?unresolved:ir_h2_tmode` — a token that equals nothing, which is a lane
    // that has stopped comparing.
    let mut files: Vec<PathBuf> = Vec::new();
    let entries = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{} must be readable ({e})", dir.display()));
    files.extend(entries.flatten().map(|e| e.path()));
    let generated_dir = dir.join("generated");
    if let Ok(generated) = std::fs::read_dir(&generated_dir) {
        files.extend(generated.flatten().map(|e| e.path()));
    }
    for p in files {
        let ext = p.extension().and_then(|e| e.to_str());
        let is_defs = ext == Some("txt")
            && p.file_name()
                .and_then(|f| f.to_str())
                .is_some_and(|f| f.ends_with(".defs.txt"));
        if ext != Some("rs") && !is_defs {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(&p) else {
            continue;
        };
        for line in src.lines() {
            let Some((_, rest)) = line.split_once("def ") else {
                continue;
            };
            let Some((name, body)) = rest.split_once(" : IRTy := ") else {
                continue;
            };
            if name.contains(' ') || name.contains('(') {
                continue; // a FUNCTION returning IRTy, not an alias
            }
            // These lines are Rust string literals, so the spec source ends at
            // the first closing quote. Trimming punctuation instead was WRONG
            // and measured wrong: the assertion `assert_eq!(SRC, "def … 64")`
            // in a chain's own test module also matches `def … : IRTy := `, and
            // its trailing `")` left the width as `64")`, which normalized to an
            // unresolved token and silently became the map entry.
            let body = body.split('"').next().unwrap_or(body).trim();
            if !body.starts_with("IRTy.") {
                continue; // a partial quotation, not a declaration
            }
            let norm = norm_clean_ty_ctor(body);
            if let Some(prev) = out.insert(name.to_string(), norm.clone()) {
                assert_eq!(
                    prev, norm,
                    "the IRTy alias {name} is declared twice with different meanings ({prev} vs \
                     {norm}); one of them is what the CFG type lane would compare against, and \
                     which one is an accident of directory order"
                );
            }
        }
    }
    out
}

/// `IRTy.uint_ ir_d8` -> `uint8`, `IRTy.float_ 64` -> `float64`,
/// `IRTy.bool_` -> `bool`.
pub(crate) fn norm_clean_ty_ctor(text: &str) -> String {
    let toks: Vec<&str> = text
        .trim()
        .trim_matches(['(', ')'])
        .split_whitespace()
        .collect();
    let Some(head) = toks.first() else {
        return "?empty".to_string();
    };
    let ctor = head.strip_prefix("IRTy.").unwrap_or(head);
    let arg = toks.get(1).map(|a| {
        numeral_of(a)
            .or_else(|| a.trim_end_matches(')').parse::<u32>().ok())
            .map_or_else(|| format!("?{a}"), |v| v.to_string())
    });
    match (ctor, arg) {
        ("bool_", _) => "bool".to_string(),
        ("ptr_", _) => "ptr".to_string(),
        ("unit_", _) => "unit".to_string(),
        ("never_", _) => "never".to_string(),
        ("int_", Some(w)) => format!("int{w}"),
        ("uint_", Some(w)) => format!("uint{w}"),
        ("float_", Some(w)) => format!("float{w}"),
        ("enum_", Some(w)) => format!("enum{w}"),
        ("struct_", Some(w)) => format!("struct{w}"),
        ("tuple_", Some(w)) => format!("tuple{w}"),
        ("func_", Some(w)) => format!("func{w}"),
        (c, a) => format!("?{c}:{}", a.unwrap_or_default()),
    }
}

/// The Clean-side type of an instruction operand slot: either an inline
/// `(IRTy.…)` term or the name of a registered alias.
pub(crate) fn norm_clean_ty(tok: &str, aliases: &BTreeMap<String, String>) -> String {
    let t = tok.trim();
    if t.starts_with("(IRTy.") || t.starts_with("IRTy.") {
        return norm_clean_ty_ctor(t);
    }
    aliases
        .get(t.trim_matches(['(', ')']))
        .cloned()
        .unwrap_or_else(|| format!("?unresolved:{t}"))
}

/// Every `ir_dK` numeral appearing in a term, in order.
pub(crate) fn numerals_in(text: &str) -> Vec<u32> {
    let mut out = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        if text[i..].starts_with("ir_d") {
            let mut j = i + 4;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 4 {
                if let Ok(v) = text[i + 4..j].parse::<u32>() {
                    out.push(v);
                }
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}
