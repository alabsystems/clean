// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ACSL/spec comment extraction and parsing.

use super::CParser;
use crate::expr::{BinOp, UnaryOp};
use crate::spec::{FuncSpec, Location, Spec};
use crate::types::{CType, IntKind, Signedness};
use tree_sitter::Node;

impl CParser {
    /// Extract ACSL spec attached to a function (block or line comment)
    pub(super) fn extract_func_spec(&self, node: Node<'_>, source: &str) -> Option<FuncSpec> {
        let start_byte = node.start_byte();
        let nearest_comment = find_nearest_acsl_comment(source, start_byte)?;
        parse_acsl_spec(&nearest_comment)
    }
}

/// Parse ACSL-style specification comments
pub fn parse_acsl_spec(comment: &str) -> Option<FuncSpec> {
    // Look for /*@ ... */ or //@ ...
    let content = if let Some(inner) = comment
        .strip_prefix("/*@")
        .and_then(|s| s.strip_suffix("*/"))
    {
        inner
    } else {
        comment.strip_prefix("//@")?
    };

    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut assigns: Vec<Location> = Vec::new();
    let mut reads: Vec<Location> = Vec::new();
    let mut terminates: Option<Spec> = None;

    for line in content.lines() {
        let mut line = line.trim();
        if let Some(rest) = line.strip_prefix("//@") {
            line = rest.trim();
        }
        let line = line.trim_start_matches('@').trim();
        if let Some(rest) = line.strip_prefix("requires") {
            requires.push(parse_spec_expr(rest.trim().trim_end_matches(';')));
        } else if let Some(rest) = line.strip_prefix("ensures") {
            ensures.push(parse_spec_expr(rest.trim().trim_end_matches(';')));
        } else if let Some(rest) = line.strip_prefix("terminates") {
            // ACSL `terminates <pred>;` is a single function-contract clause:
            // the predicate under which the function is guaranteed to
            // terminate. Per ACSL there is at most one terminates clause per
            // contract, so a later clause replaces an earlier one.
            terminates = Some(parse_spec_expr(rest.trim().trim_end_matches(';')));
        } else if let Some(rest) = line.strip_prefix("assigns") {
            let text = rest.trim().trim_end_matches(';');
            if text == "\\nothing" {
                assigns.push(Location::Nothing);
            } else {
                // Parse each assigned location
                let parts: Vec<&str> = text.split(',').collect();
                for part in parts {
                    let part = part.trim();
                    if part == "\\nothing" {
                        assigns.push(Location::Nothing);
                    } else {
                        // Treat as a dereference of the variable
                        assigns.push(Location::Deref(parse_spec_expr(part)));
                    }
                }
            }
        } else if let Some(rest) = line.strip_prefix("reads") {
            // ACSL `reads <locations>;` declares the read footprint: the set of
            // memory locations the function may read. Mirrors the `assigns`
            // clause exactly (comma-separated list, `\nothing` keyword), but
            // populates `FuncSpec::reads` rather than `assigns`.
            let text = rest.trim().trim_end_matches(';');
            if text == "\\nothing" {
                reads.push(Location::Nothing);
            } else {
                // Parse each read location
                let parts: Vec<&str> = text.split(',').collect();
                for part in parts {
                    let part = part.trim();
                    if part == "\\nothing" {
                        reads.push(Location::Nothing);
                    } else {
                        // Treat as a dereference of the variable
                        reads.push(Location::Deref(parse_spec_expr(part)));
                    }
                }
            }
        }
    }

    Some(FuncSpec {
        requires,
        ensures,
        assigns,
        reads,
        terminates,
        ..Default::default()
    })
}

/// Find the ACSL comment nearest to the given byte offset
fn find_nearest_acsl_comment(source: &str, start_byte: usize) -> Option<String> {
    let block = find_block_acsl_comment_before(source, start_byte);
    let line = find_line_acsl_comment_before(source, start_byte);

    match (block, line) {
        (Some((text, end)), Some((line_text, line_end))) => {
            if line_end > end {
                Some(line_text)
            } else {
                Some(text)
            }
        }
        (Some((text, _)), None) | (None, Some((text, _))) => Some(text),
        (None, None) => None,
    }
}

/// Find the last block ACSL comment (/*@ ... */) before the given byte offset
fn find_block_acsl_comment_before(source: &str, start_byte: usize) -> Option<(String, usize)> {
    if start_byte > source.len() {
        return None;
    }

    let prefix = &source[..start_byte];
    let start_idx = prefix.rfind("/*@")?;
    let remainder = &source[start_idx..start_byte];
    let end_rel = remainder.find("*/")?;
    let end_idx = start_idx + end_rel + 2;

    // Ensure only whitespace between comment end and the target offset
    if source[end_idx..start_byte].trim().is_empty() {
        Some((source[start_idx..end_idx].to_string(), end_idx))
    } else {
        None
    }
}

/// Find the trailing block of line ACSL comments (//@ ...) before the offset
fn find_line_acsl_comment_before(source: &str, start_byte: usize) -> Option<(String, usize)> {
    let prefix = &source[..start_byte];
    let trimmed = prefix.trim_end_matches(|c: char| c.is_whitespace());
    let trimmed_len = trimmed.len();

    if trimmed_len == 0 {
        return None;
    }

    let mut collected = Vec::new();
    for line in trimmed.rsplit('\n') {
        let trimmed_line = line.trim_start();
        if trimmed_line.starts_with("//@") {
            collected.push(trimmed_line.to_string());
        } else if trimmed_line.is_empty() {
            if collected.is_empty() {
                continue;
            }
            break;
        } else {
            break;
        }
    }

    if collected.is_empty() {
        return None;
    }

    collected.reverse();
    Some((collected.join("\n"), trimmed_len))
}

/// Parse a specification expression.
///
/// This is a small precedence-respecting, parenthesis-aware recursive-descent
/// parser for the fragment of ACSL terms/predicates we model. It is careful to
/// only split on *top-level* operators (those outside any parentheses), so that
/// nested forms such as `\valid(p) && x >= 0` or `f(a, b) == 0` are parsed
/// correctly rather than being mis-split by a naive `str::split_once`.
///
/// Precedence (lowest binds last, evaluated left-to-right within a level):
///   1. `==>` / `<==>` (implication / equivalence)
///   2. `||`
///   3. `&&`
///   4. comparisons (`==`, `!=`, `<=`, `>=`, `<`, `>`)
///   5. `+` / `-`
///   6. `*` / `/` / `%`
///   7. unary `!` / `-`
///   8. primary (literals, ACSL builtins, parenthesised terms, variables)
fn parse_spec_expr(s: &str) -> Spec {
    parse_implies(s.trim())
}

/// Find the byte index of the first top-level (paren-depth 0) occurrence of any
/// of `ops`, scanning left-to-right. Returns `(index, matched_operator)`.
///
/// Operators are matched as substrings; callers must order `ops` so that longer
/// operators that share a prefix are listed first when relevant (e.g. `<==>`
/// before `<`). The matched op is mapped to a `'static` spelling so the returned
/// lifetime is independent of `s`.
fn find_top_level(s: &str, ops: &[&str]) -> Option<(usize, &'static str)> {
    let bytes = s.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            // Guard the slice: `i` may land on a UTF-8 continuation byte for
            // multibyte input (attacker-controlled ACSL comment text). Slicing
            // `&s[i..]` at a non-boundary would panic. All matched operators are
            // ASCII, so a non-boundary index can never begin an operator match;
            // skipping it preserves correct-path behaviour exactly.
            _ if depth == 0 && s.is_char_boundary(i) => {
                if let Some(matched) = match_op_at(&s[i..], ops) {
                    return Some((i, matched));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Like [`find_top_level`] but returns the *last* (rightmost) top-level match,
/// used for left-associative arithmetic reduction.
fn find_top_level_last(s: &str, ops: &[&str]) -> Option<(usize, &'static str)> {
    let bytes = s.as_bytes();
    let mut depth: i32 = 0;
    let mut found: Option<(usize, &'static str)> = None;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            // See `find_top_level`: guard against slicing at a non-char-boundary
            // for multibyte (attacker-controlled) input. Operators are ASCII, so
            // skipping continuation bytes cannot miss a match.
            _ if depth == 0 && s.is_char_boundary(i) => {
                if let Some(matched) = match_op_at(&s[i..], ops) {
                    found = Some((i, matched));
                }
            }
            _ => {}
        }
        i += 1;
    }
    found
}

/// If `prefix` begins with one of `ops`, return its `'static` spelling.
fn match_op_at(prefix: &str, ops: &[&str]) -> Option<&'static str> {
    for &op in ops {
        if prefix.starts_with(op) {
            return Some(match op {
                "<==>" => "<==>",
                "==>" => "==>",
                "||" => "||",
                "&&" => "&&",
                "==" => "==",
                "!=" => "!=",
                "<=" => "<=",
                ">=" => ">=",
                "<" => "<",
                ">" => ">",
                "+" => "+",
                "-" => "-",
                "*" => "*",
                "/" => "/",
                "%" => "%",
                _ => continue,
            });
        }
    }
    None
}

/// Strip one or more layers of fully-enclosing parentheses, if present.
/// `(a + b)` -> `a + b`; `(a) + (b)` is returned unchanged.
fn strip_outer_parens(s: &str) -> &str {
    let s = s.trim();
    if !s.starts_with('(') || !s.ends_with(')') {
        return s;
    }
    // Verify the leading '(' matches the trailing ')'.
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    // The opening paren only encloses the whole string if its
                    // match is the final character.
                    return if i == bytes.len() - 1 {
                        strip_outer_parens(&s[1..bytes.len() - 1])
                    } else {
                        s
                    };
                }
            }
            _ => {}
        }
    }
    s
}

/// Level 1: implication (`==>`) and equivalence (`<==>`), right-associative.
fn parse_implies(s: &str) -> Spec {
    let s = s.trim();
    if let Some((idx, op)) = find_top_level(s, &["<==>", "==>"]) {
        let left = parse_or(&s[..idx]);
        let right = parse_implies(&s[idx + op.len()..]);
        return match op {
            "<==>" => Spec::iff(left, right),
            _ => Spec::implies(left, right),
        };
    }
    parse_or(s)
}

/// Level 2: logical or (`||`), left-associative.
fn parse_or(s: &str) -> Spec {
    let s = s.trim();
    let mut operands = Vec::new();
    let mut rest = s;
    while let Some((idx, _)) = find_top_level(rest, &["||"]) {
        operands.push(parse_and(&rest[..idx]));
        rest = &rest[idx + 2..];
    }
    operands.push(parse_and(rest));
    Spec::or(operands)
}

/// Level 3: logical and (`&&`), left-associative.
fn parse_and(s: &str) -> Spec {
    let s = s.trim();
    let mut operands = Vec::new();
    let mut rest = s;
    while let Some((idx, _)) = find_top_level(rest, &["&&"]) {
        operands.push(parse_cmp(&rest[..idx]));
        rest = &rest[idx + 2..];
    }
    operands.push(parse_cmp(rest));
    Spec::and(operands)
}

/// Level 4: comparisons. We parse a single top-level comparison (the leftmost),
/// matching the leniency of ACSL surface usage. Longer operators are tried
/// before their prefixes (`<=` before `<`).
fn parse_cmp(s: &str) -> Spec {
    let s = s.trim();
    if let Some((idx, op)) = find_top_level(s, &["==", "!=", "<=", ">=", "<", ">"]) {
        let left = parse_add(&s[..idx]);
        let right = parse_add(&s[idx + op.len()..]);
        let bin = match op {
            "==" => BinOp::Eq,
            "!=" => BinOp::Ne,
            "<=" => BinOp::Le,
            ">=" => BinOp::Ge,
            "<" => BinOp::Lt,
            _ => BinOp::Gt,
        };
        return Spec::binop(bin, left, right);
    }
    parse_add(s)
}

/// Level 5: additive (`+`, `-`), left-associative.
fn parse_add(s: &str) -> Spec {
    let s = s.trim();
    // Reduce on the rightmost top-level +/- so the recursion accumulates the
    // higher-up additions on the left (left-associative reduction).
    if let Some((idx, op)) = find_top_level_last(s, &["+", "-"]) {
        // A leading '-' (or '+') is unary, not a binary operator.
        if idx == 0 {
            return parse_mul(s);
        }
        let left = parse_add(&s[..idx]);
        let right = parse_mul(&s[idx + op.len()..]);
        let bin = if op == "+" { BinOp::Add } else { BinOp::Sub };
        return Spec::binop(bin, left, right);
    }
    parse_mul(s)
}

/// Level 6: multiplicative (`*`, `/`, `%`), left-associative.
fn parse_mul(s: &str) -> Spec {
    let s = s.trim();
    if let Some((idx, op)) = find_top_level_last(s, &["*", "/", "%"]) {
        let left = parse_mul(&s[..idx]);
        let right = parse_unary(&s[idx + op.len()..]);
        let bin = match op {
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            _ => BinOp::Mod,
        };
        return Spec::binop(bin, left, right);
    }
    parse_unary(s)
}

/// Level 7: unary `!` (logical not) and `-` (negation).
fn parse_unary(s: &str) -> Spec {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix('!') {
        return Spec::not(parse_unary(rest));
    }
    if let Some(rest) = s.strip_prefix('-') {
        return Spec::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(parse_unary(rest)),
        };
    }
    parse_primary(s)
}

/// Level 8: primary terms — literals, ACSL builtins, parenthesised terms,
/// logic-function calls, and bare variables.
fn parse_primary(s: &str) -> Spec {
    let s = s.trim();

    // Parenthesised sub-expression.
    let unwrapped = strip_outer_parens(s);
    if unwrapped != s {
        return parse_spec_expr(unwrapped);
    }

    // ACSL builtin keywords without arguments.
    match s {
        "\\result" => return Spec::Result,
        "\\true" => return Spec::True,
        "\\false" => return Spec::False,
        "\\null" => return Spec::Null,
        _ => {}
    }

    // ACSL quantifiers: \forall T x; P  and  \exists T x; P.
    // The inner argument text is split on the *first* top-level ';' into a
    // binder declarator (`T x`) and the predicate body. The binder declarator
    // is a logic type followed by a single variable name.
    for (kw, is_forall) in [("\\forall", true), ("\\exists", false)] {
        if let Some(args) = strip_call(s, kw) {
            if let Some((binder, body)) = split_first_top_level_semicolon(&args) {
                if let Some((ty, var)) = parse_binder(&binder) {
                    let body = Box::new(parse_spec_expr(&body));
                    return if is_forall {
                        Spec::Forall { var, ty, body }
                    } else {
                        Spec::Exists { var, ty, body }
                    };
                }
            }
        }
    }

    // ACSL bounded aggregations: \sum(lo, hi, var; body) and friends. The head
    // (before ';') is `lo, hi, var`; the tail (after ';') is the lambda body
    // evaluated for each `var` in `[lo, hi]`.
    for kw in ["\\sum", "\\product", "\\min", "\\max", "\\numof"] {
        if let Some(args) = strip_call(s, kw) {
            if let Some((head, body)) = split_first_top_level_semicolon(&args) {
                let head_parts = split_top_level_commas(&head);
                if head_parts.len() == 3 {
                    if let Some(var) = parse_label(&head_parts[2]) {
                        let lo = Box::new(parse_spec_expr(&head_parts[0]));
                        let hi = Box::new(parse_spec_expr(&head_parts[1]));
                        let body = Box::new(parse_spec_expr(&body));
                        return match kw {
                            "\\sum" => Spec::Sum { lo, hi, var, body },
                            "\\product" => Spec::Product { lo, hi, var, body },
                            "\\min" => Spec::Min { lo, hi, var, body },
                            "\\max" => Spec::Max { lo, hi, var, body },
                            _ => Spec::NumOf { lo, hi, var, body },
                        };
                    }
                }
            }
        }
    }

    // ACSL builtins with a parenthesised argument list.
    if let Some(args) = strip_call(s, "\\at") {
        // \at(e, Label): value of `e` evaluated at program point `Label`.
        // The first argument is a spec expression; the second is a label
        // (a standard ACSL label such as Pre/Post/Here/Old/Init or a named
        // C label). Exactly two arguments are required; a malformed form
        // (missing label or extra arguments) is not a valid \at and degrades
        // to the bare-variable fallback below rather than mis-constructing.
        let parts = split_top_level_commas(&args);
        if parts.len() == 2 {
            if let Some(label) = parse_label(&parts[1]) {
                return Spec::At {
                    expr: Box::new(parse_spec_expr(&parts[0])),
                    label,
                };
            }
        }
    }
    if let Some(args) = strip_call(s, "\\old") {
        return Spec::Old(Box::new(parse_spec_expr(&args)));
    }
    if let Some(args) = strip_call(s, "\\valid_read") {
        return Spec::ValidRead(Box::new(parse_spec_expr(&args)));
    }
    if let Some(args) = strip_call(s, "\\valid") {
        return Spec::Valid(Box::new(parse_spec_expr(&args)));
    }
    if let Some(args) = strip_call(s, "\\separated") {
        return Spec::Separated(
            split_top_level_commas(&args)
                .iter()
                .map(|p| parse_spec_expr(p))
                .collect(),
        );
    }
    if let Some(args) = strip_call(s, "\\fresh") {
        return Spec::Fresh(Box::new(parse_spec_expr(&args)));
    }
    if let Some(args) = strip_call(s, "\\freeable") {
        return Spec::Freeable(Box::new(parse_spec_expr(&args)));
    }

    // Integer literal.
    if let Ok(n) = s.parse::<i64>() {
        return Spec::Int(n);
    }

    // Logic-function call: name(arg, ...) where name is an ordinary identifier
    // (not an ACSL `\builtin`).
    if let Some((head, rest)) = s.split_once('(') {
        let head = head.trim();
        if !head.is_empty()
            && !head.starts_with('\\')
            && head.chars().all(|c| c.is_alphanumeric() || c == '_')
            && rest.ends_with(')')
        {
            let inner = &rest[..rest.len() - 1];
            let args = if inner.trim().is_empty() {
                Vec::new()
            } else {
                split_top_level_commas(inner)
                    .iter()
                    .map(|p| parse_spec_expr(p))
                    .collect()
            };
            return Spec::Call {
                func: head.to_string(),
                args,
            };
        }
    }

    // Default: treat as a (possibly compound) variable reference.
    Spec::Var(s.to_string())
}

/// If `s` is exactly `keyword(...)` with balanced parentheses enclosing the
/// whole tail, return the inner argument text; otherwise `None`.
fn strip_call(s: &str, keyword: &str) -> Option<String> {
    let rest = s.strip_prefix(keyword)?;
    let rest = rest.trim_start();
    let inner = rest.strip_prefix('(')?.strip_suffix(')')?;
    Some(inner.trim().to_string())
}

/// Validate and normalise an ACSL `\at` label.
///
/// A label is either a standard ACSL logic label (`Pre`, `Post`, `Here`,
/// `Old`, `Init`, `LoopEntry`, `LoopCurrent`, `LoopExit`) or a user-defined C
/// label name. In both cases the surface form must be a single C identifier
/// (`[A-Za-z_][A-Za-z0-9_]*`); anything else (empty, whitespace-broken, or
/// containing operators/parentheses) is not a valid label and yields `None`.
fn parse_label(s: &str) -> Option<String> {
    let s = s.trim();
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return None,
    }
    if chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
        Some(s.to_string())
    } else {
        None
    }
}

/// Split an argument list on top-level commas (those at paren depth 0).
fn split_top_level_commas(s: &str) -> Vec<String> {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut parts = Vec::new();
    let mut start = 0;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b',' if depth == 0 => {
                parts.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(s[start..].trim().to_string());
    parts
}

/// Split `s` on the first top-level (paren/bracket depth 0) `;` into
/// `(before, after)`. Returns `None` if there is no top-level `;`.
fn split_first_top_level_semicolon(s: &str) -> Option<(String, String)> {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b';' if depth == 0 => {
                return Some((s[..i].trim().to_string(), s[i + 1..].trim().to_string()));
            }
            _ => {}
        }
    }
    None
}

/// Parse a quantifier binder declarator `T x` into `(type, variable name)`.
///
/// ACSL allows a comma-separated list of variables sharing a type (`int i, j`),
/// but we model a single binder per quantifier node, so only the first variable
/// is taken. The type is everything up to the last whitespace-separated token,
/// which is the variable name. Returns `None` for a malformed binder (no
/// variable name or an unrecognised type).
fn parse_binder(s: &str) -> Option<(CType, String)> {
    let s = s.trim();
    // The variable name is the last identifier; the type is everything before.
    let (ty_part, var_part) = s.rsplit_once(char::is_whitespace)?;
    let var = var_part.split(',').next()?.trim();
    if var.is_empty() || !is_identifier(var) {
        return None;
    }
    let ty = acsl_type_from_name(ty_part.trim())?;
    Some((ty, var.to_string()))
}

/// Whether `s` is a single C identifier (`[A-Za-z_][A-Za-z0-9_]*`).
fn is_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Map an ACSL/C logic type name to a [`CType`].
///
/// Handles the common scalar spellings used in quantifier binders. ACSL's
/// unbounded mathematical `integer` and `real` are modelled with their nearest
/// C counterparts (`int`/`double`) since the spec AST has no dedicated
/// logic-number variant. A trailing `*` denotes a pointer.
fn acsl_type_from_name(name: &str) -> Option<CType> {
    let name = name.trim();
    if let Some(base) = name.strip_suffix('*') {
        return Some(CType::ptr(acsl_type_from_name(base)?));
    }
    let ty = match name {
        "int" | "signed int" | "signed" | "integer" => CType::Int(IntKind::Int, Signedness::Signed),
        "unsigned" | "unsigned int" => CType::Int(IntKind::Int, Signedness::Unsigned),
        "char" => CType::Int(IntKind::Char, Signedness::Signed),
        "unsigned char" => CType::Int(IntKind::Char, Signedness::Unsigned),
        "short" | "short int" => CType::Int(IntKind::Short, Signedness::Signed),
        "unsigned short" => CType::Int(IntKind::Short, Signedness::Unsigned),
        "long" | "long int" => CType::Int(IntKind::Long, Signedness::Signed),
        "unsigned long" => CType::Int(IntKind::Long, Signedness::Unsigned),
        "long long" | "long long int" => CType::Int(IntKind::LongLong, Signedness::Signed),
        "size_t" => CType::size_t(),
        "_Bool" | "bool" | "boolean" => CType::Int(IntKind::Bool, Signedness::Unsigned),
        "float" => CType::Float(crate::types::FloatKind::Float),
        "double" | "real" => CType::Float(crate::types::FloatKind::Double),
        _ => return None,
    };
    Some(ty)
}
