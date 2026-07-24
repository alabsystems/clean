// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Documented arithmetic / float / cast policy for the frozen seed, plus a
//! programmatic grep helper that CI and the in-crate tests use to enforce it.
//!
//! See the crate-level docs and design §3.2 / §4.3 (Incident #2). The policy is:
//!
//! * **No `f64`/`f32` anywhere in `ck0`.** There is no float to overflow, to
//!   saturate from, or to carry a `NaN`. The cert boundary (M5) maps only exact
//!   rationals; `ck0` cannot even *receive* a float.
//! * **No fixed-width integer arithmetic that can overflow, and no `as` casts,
//!   outside the audited [`crate::bignat`] module.** Numeric *values* are
//!   arbitrary-precision `BigNat`. The only fixed-width quantities elsewhere are
//!   de Bruijn indices and level-param indices (`u32`), which are *compared*,
//!   not arithmetic'd into a numeric value (and the few additions on them are
//!   `checked_add`, surfacing as a typed error rather than a wrap).

/// The audited module name. Every `as` cast and every fixed-width arithmetic
/// site that genuinely needs to exist lives in this file and is annotated with
/// an `// AUDIT:` comment explaining why it is sound.
pub const AUDITED_ARITH_MODULE: &str = "bignat.rs";

/// Human-readable statement of the policy, mirrored into CI logs.
pub const POLICY: &str = "\
ck0 seed numeric policy (design §3.2 / §4.3 Incident #2):\n\
  - no f64/f32 anywhere in the crate;\n\
  - no `as` casts and no overflow-capable fixed-width arithmetic outside bignat.rs;\n\
  - numeric values are arbitrary-precision BigNat;\n\
  - de Bruijn / level-param u32 indices are compared, and only ever combined via\n\
    checked_add (typed error on overflow), never wrapping arithmetic.";

/// Source-grep gate used by `tests/no_float_no_unaudited_cast.rs` and CI.
///
/// Given the crate `src/` directory, returns a list of `(file, line_no, line)`
/// violations: any occurrence of `f64`/`f32`, or an ` as ` cast, in a file
/// other than the audited [`AUDITED_ARITH_MODULE`]. Comment lines (those whose
/// trimmed text starts with `//`) are ignored so that prose like this very
/// sentence does not self-trip.
///
/// This is a *defense-in-depth* check layered on top of the crate-level clippy
/// `deny`s in `lib.rs`; the clippy lints are the primary enforcement, this grep
/// catches anything a future clippy version might stop flagging.
#[must_use]
pub fn scan_violations(src_dir: &std::path::Path) -> Vec<Violation> {
    let mut out = Vec::new();
    scan_dir(src_dir, &mut out);
    out
}

/// A single policy violation found by [`scan_violations`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    /// File the violation was found in (relative to the scanned root if possible).
    pub file: std::path::PathBuf,
    /// 1-based line number.
    pub line_no: usize,
    /// The offending source line, trimmed.
    pub line: String,
    /// Why it is a violation.
    pub kind: ViolationKind,
}

/// The category of a policy [`Violation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ViolationKind {
    /// A bare `f64`/`f32` token appeared.
    Float,
    /// An ` as ` cast appeared outside the audited module.
    UnauditedCast,
}

fn scan_dir(dir: &std::path::Path, out: &mut Vec<Violation>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            scan_dir(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            scan_file(&path, out);
        }
    }
}

fn scan_file(path: &std::path::Path, out: &mut Vec<Violation>) {
    let is_audited = path
        .file_name()
        .and_then(|n| n.to_str())
        .is_some_and(|n| n == AUDITED_ARITH_MODULE);
    // `policy.rs` itself names `f64`/`f32`/`as` in prose and string literals;
    // exempt it so the documentation does not self-trip the gate.
    let is_self = path
        .file_name()
        .and_then(|n| n.to_str())
        .is_some_and(|n| n == "policy.rs");
    let Ok(contents) = std::fs::read_to_string(path) else {
        return;
    };
    for (idx, raw) in contents.lines().enumerate() {
        let line = raw.trim();
        if line.starts_with("//") || line.starts_with("#!") || line.starts_with("#[") {
            continue;
        }
        if !is_self && (contains_token(line, "f64") || contains_token(line, "f32")) {
            out.push(Violation {
                file: path.to_path_buf(),
                line_no: idx.saturating_add(1),
                line: line.to_string(),
                kind: ViolationKind::Float,
            });
        }
        if !is_audited && !is_self && line.contains(" as ") {
            out.push(Violation {
                file: path.to_path_buf(),
                line_no: idx.saturating_add(1),
                line: line.to_string(),
                kind: ViolationKind::UnauditedCast,
            });
        }
    }
}

/// True if `needle` appears in `hay` not adjacent to an identifier character on
/// either side (so `f64` matches but `xf64y` / `Inf64` do not).
fn contains_token(hay: &str, needle: &str) -> bool {
    let bytes = hay.as_bytes();
    let nlen = needle.len();
    let mut start = 0usize;
    while let Some(pos) = hay[start..].find(needle) {
        let abs = start.saturating_add(pos);
        let before_ok = abs == 0 || !is_ident_byte(bytes[abs.saturating_sub(1)]);
        let after_idx = abs.saturating_add(nlen);
        let after_ok = after_idx >= bytes.len() || !is_ident_byte(bytes[after_idx]);
        if before_ok && after_ok {
            return true;
        }
        start = abs.saturating_add(1);
        if start >= hay.len() {
            break;
        }
    }
    false
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}
