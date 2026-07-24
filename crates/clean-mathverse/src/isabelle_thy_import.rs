// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Isabelle `.thy` files.

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind as ShardDeclKind, ImportConfidence,
    MathverseConstantHeader, SourceSystem, NO_VALUE,
};

/// Declaration kind extracted from source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclKind {
    Theorem,
    Lemma,
    Definition,
    Fun,
    Primrec,
    Inductive,
    Datatype,
    Locale,
    Class,
    Instance,
}

impl DeclKind {
    /// Map Isabelle surface-syntax kind to the shard-level [`ShardDeclKind`].
    /// Theorem/Lemma → Theorem; Definition/Fun/Primrec/Instance → Definition;
    /// Inductive/Datatype → Inductive; Locale/Class → Axiom (opaque containers).
    fn to_shard(self) -> ShardDeclKind {
        match self {
            Self::Theorem | Self::Lemma => ShardDeclKind::Theorem,
            Self::Definition | Self::Fun | Self::Primrec | Self::Instance => {
                ShardDeclKind::Definition
            }
            Self::Inductive | Self::Datatype => ShardDeclKind::Inductive,
            Self::Locale | Self::Class => ShardDeclKind::Axiom,
        }
    }
}

const DECL_STARTS: [(&str, DeclKind); 10] = [
    ("definition", DeclKind::Definition),
    ("inductive", DeclKind::Inductive),
    ("datatype", DeclKind::Datatype),
    ("primrec", DeclKind::Primrec),
    ("instance", DeclKind::Instance),
    ("theorem", DeclKind::Theorem),
    ("locale", DeclKind::Locale),
    ("class", DeclKind::Class),
    ("lemma", DeclKind::Lemma),
    ("fun", DeclKind::Fun),
];

/// A single declaration extracted from a source file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IsabelleDeclaration {
    pub name: String,
    pub kind: DeclKind,
    pub type_sig: Option<String>,
    /// The quoted Isar proposition of a `theorem`/`lemma` (the term inside
    /// `"..."`), without the surrounding quotes. `None` for non-statement
    /// declarations or when no quoted term is present.
    pub proposition: Option<String>,
    pub source_file: String,
}

struct PendingDecl {
    name: String,
    kind: DeclKind,
    text: String,
}

/// Parse source file content, extracting structured declarations.
pub(crate) fn parse_isabelle_file(content: &str, filename: &str) -> Vec<IsabelleDeclaration> {
    let cleaned = strip_comments(content);
    let mut decls = Vec::new();
    let mut pending: Option<PendingDecl> = None;
    let mut proof_depth = 0usize;

    for raw_line in cleaned.lines() {
        let line = raw_line.trim();
        if proof_depth > 0 {
            proof_depth = advance_proof_depth(line, proof_depth);
            continue;
        }

        if let Some(mut cur) = pending.take() {
            if line.is_empty() {
                decls.push(build_decl(cur, None, filename));
                continue;
            }
            if !cur.text.is_empty() {
                cur.text.push('\n');
            }
            cur.text.push_str(line);
            if let Some((cut, next_depth)) = boundary(cur.kind, &cur.text) {
                decls.push(build_decl(cur, Some(cut), filename));
                proof_depth = next_depth;
            } else {
                pending = Some(cur);
            }
            continue;
        }

        if should_ignore(line) {
            continue;
        }
        if let Some((kind, rest)) = decl_start(line) {
            if let Some(name) = parse_name(rest) {
                let cur = PendingDecl {
                    name,
                    kind,
                    text: line.to_owned(),
                };
                if let Some((cut, next_depth)) = boundary(kind, &cur.text) {
                    decls.push(build_decl(cur, Some(cut), filename));
                    proof_depth = next_depth;
                } else {
                    pending = Some(cur);
                }
            }
        }
    }

    if proof_depth == 0 {
        if let Some(cur) = pending {
            decls.push(build_decl(cur, None, filename));
        }
    }
    decls
}

/// Write parsed declarations to a shard.
///
/// For each `theorem`/`lemma`, the quoted Isar proposition is translated
/// into a real `FlatExpr` tree via [`crate::isabelle_term_parser`]. A
/// declaration whose proposition is absent or fails to parse is
/// **skipped** — never replaced with a `sort(0)` placeholder. Non-statement
/// declarations (`definition`, `datatype`, …) carry HOL *type* signatures
/// rather than propositions; a faithful HOL-type translator is out of
/// scope here, so those are skipped too rather than faked.
///
/// This guarantees the emitted shard has `expr_count > constant_count`
/// (real term trees) for every constant it does write. Returns the number
/// of declarations actually written.
pub(crate) fn write_isabelle_shard(
    decls: &[IsabelleDeclaration],
    writer: &mut ShardWriter,
) -> MathverseResult<usize> {
    let mut written = 0usize;
    for decl in decls {
        // Only `theorem`/`lemma` carry a quoted proposition we can faithfully
        // translate into a term tree. Everything else is skipped.
        let Some(prop) = decl.proposition.as_deref() else {
            continue;
        };
        let Some(type_idx) = crate::isabelle_term_parser::parse_isabelle_term(prop, writer) else {
            // Unsupported/exotic term: skip rather than emit a placeholder.
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        // Theorems have no value term in this Level-0/1 import.
        let value_idx = NO_VALUE;
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Isabelle as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl.kind.to_shard() as u8,
            axiom_profile: AxiomProfile::AXIOMATIZED,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        written += 1;
    }
    Ok(written)
}

fn build_decl(p: PendingDecl, cut: Option<usize>, filename: &str) -> IsabelleDeclaration {
    let header = cut.map(|i| &p.text[..i]).unwrap_or(&p.text).trim_end();
    let proposition = matches!(p.kind, DeclKind::Theorem | DeclKind::Lemma)
        .then(|| extract_proposition(header))
        .flatten();
    IsabelleDeclaration {
        name: p.name,
        kind: p.kind,
        type_sig: extract_type_sig(header),
        proposition,
        source_file: filename.to_owned(),
    }
}

/// Extract the quoted proposition from a `theorem`/`lemma` header. The
/// statement appears as the first quoted string in the header that follows
/// the name — either `theorem foo: "PROP"` (bare colon) or
/// `theorem foo :: "PROP"` (double colon). We scan for the first top-level
/// `"..."` quotation and return its contents without the quotes.
fn extract_proposition(header: &str) -> Option<String> {
    let quote_at = header.find('"')?;
    let quoted = read_quoted(&header[quote_at..])?;
    let inner = &quoted[1..quoted.len() - 1];
    (!inner.trim().is_empty()).then(|| inner.to_owned())
}

fn boundary(kind: DeclKind, text: &str) -> Option<(usize, usize)> {
    let mut best: Option<(usize, usize)> = None;
    for word in ["proof", "by"] {
        if let Some(idx) = find_token(text, word, true) {
            let depth = if word == "proof" {
                advance_proof_depth(&text[idx..], 0)
            } else {
                0
            };
            best = earlier(best, (idx, depth));
        }
    }
    if matches!(
        kind,
        DeclKind::Definition | DeclKind::Fun | DeclKind::Primrec | DeclKind::Inductive
    ) {
        if let Some(idx) = find_token(text, "where", true) {
            best = earlier(best, (idx, 0));
        }
    }
    if kind == DeclKind::Datatype {
        if let Some(idx) = find_token(text, "=", false) {
            best = earlier(best, (idx, 0));
        }
    }
    if matches!(
        kind,
        DeclKind::Locale | DeclKind::Class | DeclKind::Instance
    ) {
        if let Some(idx) = find_token(text, "begin", true) {
            best = earlier(best, (idx, 0));
        }
    }
    best
}

fn earlier(current: Option<(usize, usize)>, next: (usize, usize)) -> Option<(usize, usize)> {
    match current {
        Some(prev) if prev.0 <= next.0 => Some(prev),
        _ => Some(next),
    }
}

fn decl_start(line: &str) -> Option<(DeclKind, &str)> {
    for (keyword, kind) in DECL_STARTS {
        if let Some(rest) = line.strip_prefix(keyword) {
            if rest.is_empty() || rest.starts_with(char::is_whitespace) || rest.starts_with('"') {
                return Some((kind, rest));
            }
        }
    }
    None
}

fn should_ignore(line: &str) -> bool {
    line.is_empty()
        || matches!(line, "begin" | "end")
        || [
            "theory ",
            "imports ",
            "context ",
            "text ",
            "chapter ",
            "section ",
            "subsection ",
        ]
        .iter()
        .any(|p| line.starts_with(p))
}

fn parse_name(rest: &str) -> Option<String> {
    let s = rest.trim_start();
    if s.starts_with('"') {
        return read_quoted(s).map(|q| q[1..q.len() - 1].to_owned());
    }
    let end = s.find(|c: char| !is_name_char(c)).unwrap_or(s.len());
    (end > 0).then(|| s[..end].to_owned())
}

fn extract_type_sig(text: &str) -> Option<String> {
    let idx = find_token(text, "::", false)?;
    let rest = text[idx + 2..].trim_start();
    if rest.is_empty() {
        return None;
    }
    if rest.starts_with('"') {
        return read_quoted(rest).map(ToOwned::to_owned);
    }
    let mut end = rest.len();
    for marker in ["where", "proof", "by", "qed", "begin"] {
        if let Some(idx) = find_token(rest, marker, true) {
            end = end.min(idx);
        }
    }
    let sig = rest[..end].trim().trim_end_matches([':', '=', ';']).trim();
    (!sig.is_empty()).then(|| sig.to_owned())
}

fn strip_comments(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let mut out = String::with_capacity(content.len());
    let mut i = 0usize;
    let mut depth = 0usize;
    while i < chars.len() {
        if depth == 0 && chars[i] == '"' {
            out.push('"');
            i += 1;
            while i < chars.len() {
                let ch = chars[i];
                out.push(ch);
                i += 1;
                if ch == '\\' && i < chars.len() {
                    out.push(chars[i]);
                    i += 1;
                } else if ch == '"' {
                    break;
                }
            }
            continue;
        }
        if i + 1 < chars.len() && chars[i] == '(' && chars[i + 1] == '*' {
            depth += 1;
            out.push(' ');
            out.push(' ');
            i += 2;
            continue;
        }
        if depth > 0 {
            if i + 1 < chars.len() && chars[i] == '(' && chars[i + 1] == '*' {
                depth += 1;
                i += 2;
            } else if i + 1 < chars.len() && chars[i] == '*' && chars[i + 1] == ')' {
                depth = depth.saturating_sub(1);
                i += 2;
            } else {
                out.push(if chars[i] == '\n' { '\n' } else { ' ' });
                i += 1;
            }
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn advance_proof_depth(text: &str, depth: usize) -> usize {
    depth
        .saturating_add(count_token(text, "proof"))
        .saturating_sub(count_token(text, "qed"))
}

fn count_token(text: &str, token: &str) -> usize {
    let mut count = 0usize;
    let mut offset = 0usize;
    while offset < text.len() {
        if let Some(idx) = find_token(&text[offset..], token, true) {
            count += 1;
            offset += idx + token.len();
        } else {
            break;
        }
    }
    count
}

fn find_token(text: &str, token: &str, word_boundary: bool) -> Option<usize> {
    let mut in_quote = false;
    let mut escaped = false;
    for (idx, ch) in text.char_indices() {
        if in_quote {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_quote = false;
            }
            continue;
        }
        if ch == '"' {
            in_quote = true;
            continue;
        }
        if text[idx..].starts_with(token) {
            let before = text[..idx].chars().next_back();
            let after = text[idx + token.len()..].chars().next();
            if !word_boundary || (is_boundary(before) && is_boundary(after)) {
                return Some(idx);
            }
        }
    }
    None
}

fn read_quoted(text: &str) -> Option<&str> {
    let mut chars = text.char_indices();
    if chars.next()?.1 != '"' {
        return None;
    }
    let mut escaped = false;
    for (idx, ch) in chars {
        if escaped {
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else if ch == '"' {
            return Some(&text[..idx + 1]);
        }
    }
    None
}

fn is_name_char(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '.' | '\'' | '?' | '!' | '-')
}

fn is_boundary(ch: Option<char>) -> bool {
    ch.map(|c| !is_name_char(c)).unwrap_or(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_isabelle_file_with_blocks_and_proofs() {
        let text = r#"
theory Synthetic
imports Main
begin
definition add1 :: "nat => nat" where "add1 n = n + 1"
fun twice :: "nat => nat" where "twice n = n + n"
primrec fact :: "nat => nat" where "fact 0 = 1"
inductive even :: "nat => bool" where zero: "even 0"
datatype color = Red | Blue
locale semigroup =
  fixes mult :: "'a => 'a => 'a"
begin
lemma local_closed :: "True" by simp
end
class carrier_class =
  fixes carrier :: "'a => bool"
begin
end
instance nat :: carrier_class by standard
theorem add1_ok :: "add1 0 = 1"
proof
  theorem hidden_in_proof :: "False" by simp
qed
lemma "quoted theorem" :: "True" by simp
end
"#;
        let decls = parse_isabelle_file(text, "Synthetic.thy");
        let names: Vec<_> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "add1",
                "twice",
                "fact",
                "even",
                "color",
                "semigroup",
                "local_closed",
                "carrier_class",
                "nat",
                "add1_ok",
                "quoted theorem",
            ]
        );
        assert_eq!(decls[0].type_sig.as_deref(), Some("\"nat => nat\""));
        assert_eq!(decls[5].kind, DeclKind::Locale);
        assert_eq!(decls[5].type_sig.as_deref(), Some("\"'a => 'a => 'a\""));
        assert_eq!(decls[8].type_sig.as_deref(), Some("carrier_class"));
        assert!(decls.iter().all(|d| d.name != "hidden_in_proof"));
    }

    #[test]
    fn test_extract_proposition_bare_colon_theorem() {
        // `theorem foo: "PROP"` — the proposition follows a bare colon.
        let decls = parse_isabelle_file(
            "theory T imports Main begin\ntheorem foo: \"x + 0 = x\" by simp\nend\n",
            "T.thy",
        );
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, DeclKind::Theorem);
        assert_eq!(decls[0].proposition.as_deref(), Some("x + 0 = x"));
    }

    #[test]
    fn test_write_isabelle_thy_shard_emits_real_types() {
        // The importer now translates the quoted Isar proposition into a
        // real FlatExpr tree. A successfully-written shard must have strictly
        // more exprs than constants (no shared placeholder per constant).
        let decls = parse_isabelle_file(
            r#"
theory Mini
imports Main
begin
(* lemma ignored :: "False" *)
theorem id_nat_ok: "x + 0 = x" by simp
lemma both_ways: "a = b & b = a" by auto
end
"#,
            "Mini.thy",
        );
        assert!(!decls.is_empty());
        let mut writer = ShardWriter::new();
        let written = write_isabelle_shard(&decls, &mut writer).expect("real importer must emit");
        assert!(written >= 1, "expected at least one statement written");
        assert_eq!(writer.constant_count(), written);
        assert!(
            writer.expr_count() > writer.constant_count(),
            "stub signature: expr_count {} !> constant_count {}",
            writer.expr_count(),
            writer.constant_count()
        );
    }

    #[test]
    fn test_write_isabelle_shard_skips_unparseable_proposition() {
        // A lemma whose proposition we cannot translate is skipped, never
        // emitted as a placeholder. `%x. x` (lambda) is out of scope.
        let decls = parse_isabelle_file(
            "theory T imports Main begin\nlemma weird: \"%x. x\" by simp\nend\n",
            "T.thy",
        );
        assert_eq!(decls.len(), 1);
        let mut writer = ShardWriter::new();
        let written = write_isabelle_shard(&decls, &mut writer).expect("ok");
        assert_eq!(written, 0, "unparseable proposition must be skipped");
        assert_eq!(writer.constant_count(), 0);
    }
}
