// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Lean 3 `.lean` files.

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
    Axiom,
    Constant,
    Inductive,
    Structure,
    Class,
}
impl DeclKind {
    fn body_block(self) -> bool {
        matches!(self, Self::Inductive | Self::Structure | Self::Class)
    }

    /// Map Lean 3 surface-syntax kind to the shard-level [`ShardDeclKind`].
    /// Theorem/Lemma → Theorem; Axiom/Constant → Axiom;
    /// Inductive/Structure/Class → Inductive; Definition → Definition.
    fn to_shard(self) -> ShardDeclKind {
        match self {
            Self::Theorem | Self::Lemma => ShardDeclKind::Theorem,
            Self::Axiom | Self::Constant => ShardDeclKind::Axiom,
            Self::Inductive | Self::Structure | Self::Class => ShardDeclKind::Inductive,
            Self::Definition => ShardDeclKind::Definition,
        }
    }
}

/// A single declaration extracted from a source file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Lean3Declaration {
    pub name: String,
    pub kind: DeclKind,
    /// Raw binder-prefix text between the declaration name and the
    /// first top-level `:` (e.g. `(n : Nat) (h : n > 0)`). Empty when
    /// the declaration has no binders before the colon. Each binder
    /// becomes a Pi node in the FlatExpr tree at shard-emit time.
    pub binders: Option<String>,
    pub type_sig: Option<String>,
    pub source_file: String,
}

#[derive(Clone, Debug)]
struct PendingDecl {
    name: String,
    kind: DeclKind,
    text: String,
}
#[derive(Clone, Debug)]
struct Block {
    is_namespace: bool,
    name: Option<String>,
}

const DECL_STARTS: [(&str, DeclKind); 12] = [
    ("definition", DeclKind::Definition),
    ("inductive", DeclKind::Inductive),
    ("structure", DeclKind::Structure),
    ("constant", DeclKind::Constant),
    ("theorem", DeclKind::Theorem),
    ("axiom", DeclKind::Axiom),
    ("class", DeclKind::Class),
    ("lemma", DeclKind::Lemma),
    ("def", DeclKind::Definition),
    // Lean 3 mathlib uses these heavily and the prior table dropped them.
    ("instance", DeclKind::Definition),
    ("example", DeclKind::Theorem),
    ("abbreviation", DeclKind::Definition),
];
const MODIFIERS: [&str; 4] = ["private", "protected", "noncomputable", "meta"];
const VARIABLE_HEADS: [&str; 4] = ["variables", "variable", "parameters", "parameter"];

/// Parse source file content, extracting structured declarations.
pub(crate) fn parse_lean3_file(content: &str, filename: &str) -> Vec<Lean3Declaration> {
    let cleaned = strip_comments(content);
    let lines: Vec<&str> = cleaned.lines().collect();
    let mut decls = Vec::new();
    let mut blocks = Vec::<Block>::new();
    let mut pending: Option<PendingDecl> = None;
    let mut skipping_body = false;
    let mut i = 0usize;
    while i < lines.len() {
        let raw = lines[i];
        let line = raw.trim();
        let top = is_top_level(raw);
        if let Some(cur) = pending.take() {
            if starts_body_line(&cur, raw, line) {
                decls.push(build_decl(cur, None, filename));
                skipping_body = true;
                i += 1;
                continue;
            }
            if top && is_control_or_decl(line) {
                decls.push(build_decl(cur, None, filename));
                continue;
            }
            let mut cur = cur;
            append_line(&mut cur.text, line);
            if let Some(cut) = find_top_level_token(&cur.text, ":=") {
                decls.push(build_decl(cur, Some(cut), filename));
                skipping_body = true;
            } else {
                pending = Some(cur);
            }
            i += 1;
            continue;
        }
        if skipping_body {
            if top && is_control_or_decl(line) {
                skipping_body = false;
                continue;
            }
            i += 1;
            continue;
        }
        if line.is_empty() || !top {
            i += 1;
            continue;
        }
        if handle_block_line(line, &mut blocks) || is_variable_decl(line) {
            i += 1;
            continue;
        }
        if let Some((kind, rest)) = decl_start(line) {
            if let Some(name) = parse_name(rest) {
                let cur = PendingDecl {
                    name: qualify_name(&blocks, &name),
                    kind,
                    text: line.to_owned(),
                };
                if let Some(cut) = find_top_level_token(&cur.text, ":=") {
                    decls.push(build_decl(cur, Some(cut), filename));
                    skipping_body = true;
                } else {
                    pending = Some(cur);
                }
            }
        }
        i += 1;
    }
    if let Some(cur) = pending {
        decls.push(build_decl(cur, None, filename));
    }
    decls
}

/// Write parsed declarations to a shard.
///
/// For each declaration, the surface-syntax `type_sig` string is parsed
/// into a real `FlatExpr` tree via [`crate::lean3_type_parser`]. A
/// declaration whose type signature is absent or fails to parse is
/// **skipped** — never replaced with a `sort(0)` placeholder. This is
/// the import-time guarantee that the resulting shard's
/// `expr_count > constant_count` and that
/// `mathverse_fidelity_check` classifies it above `SurfaceNamesOnly`.
///
/// Returns the number of declarations actually written.
pub(crate) fn write_lean3_shard(
    decls: &[Lean3Declaration],
    writer: &mut ShardWriter,
) -> MathverseResult<usize> {
    let mut written = 0usize;
    for decl in decls {
        let Some(sig) = decl.type_sig.as_deref() else {
            // No declared type — would have to emit a placeholder.
            // Skip rather than fake.
            continue;
        };
        // Synthesize `∀ <binders>, <type>` so the parser wraps the body
        // in real Pi nodes and resolves binder-name references inside
        // the body as BVars rather than free Consts.
        let synthesized = match decl.binders.as_deref() {
            Some(binders) => format!("\u{2200} {binders}, {sig}"),
            None => sig.to_owned(),
        };
        let Some(type_idx) = crate::lean3_type_parser::parse_lean3_type(&synthesized, writer)
        else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        // For def-shaped decls we still don't have a real value term;
        // a real proof/body translator is out of scope. Mark axiomatized.
        let value_idx = NO_VALUE;
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8, // Lean 3 shares the nearest current tag.
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

fn build_decl(p: PendingDecl, cut: Option<usize>, filename: &str) -> Lean3Declaration {
    let header = cut.map(|i| &p.text[..i]).unwrap_or(&p.text).trim_end();
    let (binders, type_sig) = extract_binders_and_type(header, &p.name);
    Lean3Declaration {
        name: p.name,
        kind: p.kind,
        binders,
        type_sig,
        source_file: filename.to_owned(),
    }
}

fn decl_start(line: &str) -> Option<(DeclKind, &str)> {
    let mut rest = line.trim_start();
    loop {
        let mut changed = false;
        for modifier in MODIFIERS {
            if let Some(next) = strip_prefix_word(rest, modifier) {
                rest = next.trim_start();
                changed = true;
                break;
            }
        }
        if !changed {
            break;
        }
    }
    for (kw, kind) in DECL_STARTS {
        if let Some(rest) = strip_prefix_word(rest, kw) {
            return Some((kind, rest));
        }
    }
    None
}

fn handle_block_line(line: &str, blocks: &mut Vec<Block>) -> bool {
    if let Some(rest) = strip_prefix_word(line, "namespace") {
        if let Some(name) = parse_name(rest) {
            blocks.push(Block {
                is_namespace: true,
                name: Some(name),
            });
        }
        return true;
    }
    if let Some(rest) = strip_prefix_word(line, "section") {
        blocks.push(Block {
            is_namespace: false,
            name: parse_name(rest),
        });
        return true;
    }
    if let Some(rest) = strip_prefix_word(line, "end") {
        pop_block(blocks, parse_name(rest).as_deref());
        return true;
    }
    false
}

fn pop_block(blocks: &mut Vec<Block>, name: Option<&str>) {
    if blocks.is_empty() {
        return;
    }
    if let Some(name) = name {
        if let Some(pos) = blocks.iter().rposition(|b| b.name.as_deref() == Some(name)) {
            blocks.truncate(pos);
            return;
        }
    }
    blocks.pop();
}

fn is_variable_decl(line: &str) -> bool {
    VARIABLE_HEADS
        .iter()
        .any(|head| strip_prefix_word(line, head).is_some())
}
fn is_control_or_decl(line: &str) -> bool {
    line.is_empty()
        || strip_prefix_word(line, "namespace").is_some()
        || strip_prefix_word(line, "section").is_some()
        || strip_prefix_word(line, "end").is_some()
        || is_variable_decl(line)
        || decl_start(line).is_some()
}

fn starts_body_line(cur: &PendingDecl, raw: &str, line: &str) -> bool {
    cur.kind.body_block()
        && !line.is_empty()
        && (line.starts_with('|')
            || line.starts_with("where")
            || line.starts_with("extends")
            || (!is_top_level(raw) && !needs_continuation(&cur.text)))
}

fn needs_continuation(text: &str) -> bool {
    let mut p = 0i32;
    let mut b = 0i32;
    let mut s = 0i32;
    let mut in_str = false;
    let mut esc = false;
    for ch in text.chars() {
        if in_str {
            if esc {
                esc = false;
            } else if ch == '\\' {
                esc = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        match ch {
            '"' => in_str = true,
            '(' => p += 1,
            ')' => p = (p - 1).max(0),
            '[' => b += 1,
            ']' => b = (b - 1).max(0),
            '{' => s += 1,
            '}' => s = (s - 1).max(0),
            _ => {}
        }
    }
    let t = text.trim_end();
    p > 0
        || b > 0
        || s > 0
        || t.ends_with(':')
        || t.ends_with("->")
        || t.ends_with('→')
        || t.ends_with(',')
}

fn append_line(text: &mut String, line: &str) {
    if !text.is_empty() {
        text.push('\n');
    }
    text.push_str(line);
}

fn qualify_name(blocks: &[Block], name: &str) -> String {
    if let Some(stripped) = name.strip_prefix("_root_.") {
        return stripped.to_owned();
    }
    let mut prefix = String::new();
    for block in blocks.iter().filter(|b| b.is_namespace) {
        if let Some(name) = &block.name {
            if !prefix.is_empty() {
                prefix.push('.');
            }
            prefix.push_str(name);
        }
    }
    if prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{prefix}.{name}")
    }
}

fn parse_name(rest: &str) -> Option<String> {
    let s = rest.trim_start();
    let end = s.find(|ch: char| !is_name_char(ch)).unwrap_or(s.len());
    (end > 0).then(|| s[..end].to_owned())
}

fn extract_type_sig(text: &str) -> Option<String> {
    let start = find_top_level_char(text, ':')?;
    let end = find_top_level_token(text, ":=").unwrap_or(text.len());
    let sig = text[start + 1..end].trim();
    (!sig.is_empty()).then(|| sig.to_owned())
}

/// Split a declaration header into (binder-prefix, type-body). The
/// header is the source text from `theorem`/`def`/etc up to (but not
/// including) `:=`. The split point is the first top-level `:` after
/// the declaration name. Whatever sits BETWEEN the name and that `:`
/// is the binder prefix — for `theorem foo (n : Nat) (h : n > 0) :
/// body`, that's `(n : Nat) (h : n > 0)`. Empty when the declaration
/// has no binders. Returns `(binders, type_sig)`.
fn extract_binders_and_type(text: &str, name: &str) -> (Option<String>, Option<String>) {
    let Some(type_sig) = extract_type_sig(text) else {
        return (None, None);
    };
    let colon_idx = find_top_level_char(text, ':').expect("type_sig found ⇒ colon exists");
    // Find where the name ends in the source text.
    let name_end = match text.find(name) {
        Some(p) => p + name.len(),
        None => return (None, Some(type_sig)),
    };
    if name_end >= colon_idx {
        return (None, Some(type_sig));
    }
    let binders = text[name_end..colon_idx].trim();
    let binders = (!binders.is_empty()).then(|| binders.to_owned());
    (binders, Some(type_sig))
}

fn find_top_level_char(text: &str, needle: char) -> Option<usize> {
    let (mut p, mut b, mut s, mut in_str, mut esc) = (0i32, 0i32, 0i32, false, false);
    for (idx, ch) in text.char_indices() {
        if in_str {
            if esc {
                esc = false;
            } else if ch == '\\' {
                esc = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        match ch {
            '"' => in_str = true,
            '(' => p += 1,
            ')' => p = (p - 1).max(0),
            '[' => b += 1,
            ']' => b = (b - 1).max(0),
            '{' => s += 1,
            '}' => s = (s - 1).max(0),
            _ if ch == needle && p == 0 && b == 0 && s == 0 => return Some(idx),
            _ => {}
        }
    }
    None
}

fn find_top_level_token(text: &str, token: &str) -> Option<usize> {
    let (mut p, mut b, mut s, mut in_str, mut esc) = (0i32, 0i32, 0i32, false, false);
    for (idx, ch) in text.char_indices() {
        if in_str {
            if esc {
                esc = false;
            } else if ch == '\\' {
                esc = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        match ch {
            '"' => in_str = true,
            '(' => p += 1,
            ')' => p = (p - 1).max(0),
            '[' => b += 1,
            ']' => b = (b - 1).max(0),
            '{' => s += 1,
            '}' => s = (s - 1).max(0),
            _ if p == 0 && b == 0 && s == 0 && text[idx..].starts_with(token) => return Some(idx),
            _ => {}
        }
    }
    None
}

fn strip_prefix_word<'a>(text: &'a str, word: &str) -> Option<&'a str> {
    let rest = text.strip_prefix(word)?;
    (rest.is_empty() || rest.starts_with(char::is_whitespace)).then_some(rest)
}

fn is_top_level(line: &str) -> bool {
    line.trim_start() == line
}
fn is_name_char(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '.' | '\'' | '!' | '?')
}

fn strip_comments(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let mut out = String::with_capacity(content.len());
    let (mut i, mut depth, mut in_str, mut esc) = (0usize, 0usize, false, false);
    while i < chars.len() {
        if depth > 0 {
            if i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '-' {
                depth += 1;
                out.push(' ');
                out.push(' ');
                i += 2;
            } else if i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '/' {
                depth = depth.saturating_sub(1);
                out.push(' ');
                out.push(' ');
                i += 2;
            } else {
                out.push(if chars[i] == '\n' { '\n' } else { ' ' });
                i += 1;
            }
            continue;
        }
        if in_str {
            let ch = chars[i];
            out.push(ch);
            i += 1;
            if esc {
                esc = false;
            } else if ch == '\\' {
                esc = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        if i + 1 < chars.len() && chars[i] == '/' && chars[i + 1] == '-' {
            depth = 1;
            out.push(' ');
            out.push(' ');
            i += 2;
        } else if i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '-' {
            out.push(' ');
            out.push(' ');
            i += 2;
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
        } else {
            let ch = chars[i];
            out.push(ch);
            i += 1;
            if ch == '"' {
                in_str = true;
                esc = false;
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_lean3_file_with_namespaces_and_bodies() {
        let text = concat!(
            "/- theorem commented_out : False := by trivial -/\n",
            "namespace Nat\n",
            "private theorem add_zero (n : Nat) : Nat.add n 0 = n := by\n  theorem hidden_in_body : False := by trivial\n  exact rfl\n\n",
            "protected def add1 : Nat -> Nat :=\n  fun n => Nat.succ n\n\n",
            "namespace Inner\nnoncomputable meta definition chooser (α : Type) : α := by\n  admit\nend Inner\n\n",
            "axiom extensionality : Prop\nconstant seed : Nat\n\n",
            "inductive Tree : Type\n| leaf : Tree\n| node : Tree -> Tree -> Tree\n\n",
            "structure Point :=\n(x : Nat)\n(y : Nat)\n\n",
            "class Additive (α : Type) :=\n(add : α -> α -> α)\n\n",
            "section Local\nvariables {α : Type} (x : α)\nlemma local_id : x = x := rfl\nprotected def Core.id : α -> α :=\n  fun y => y\nend Local\nend Nat\n",
        );
        let decls = parse_lean3_file(text, "Synthetic.lean");
        let names: Vec<_> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "Nat.add_zero",
                "Nat.add1",
                "Nat.Inner.chooser",
                "Nat.extensionality",
                "Nat.seed",
                "Nat.Tree",
                "Nat.Point",
                "Nat.Additive",
                "Nat.local_id",
                "Nat.Core.id",
            ]
        );
        assert_eq!(decls[0].kind, DeclKind::Theorem);
        assert_eq!(decls[1].kind, DeclKind::Definition);
        assert_eq!(decls[2].kind, DeclKind::Definition);
        assert_eq!(decls[5].kind, DeclKind::Inductive);
        assert_eq!(decls[6].kind, DeclKind::Structure);
        assert_eq!(decls[7].kind, DeclKind::Class);
        assert_eq!(decls[0].type_sig.as_deref(), Some("Nat.add n 0 = n"));
        assert_eq!(decls[1].type_sig.as_deref(), Some("Nat -> Nat"));
        assert_eq!(decls[2].type_sig.as_deref(), Some("α"));
        assert_eq!(decls[3].type_sig.as_deref(), Some("Prop"));
        assert_eq!(decls[4].type_sig.as_deref(), Some("Nat"));
        assert_eq!(decls[5].type_sig.as_deref(), Some("Type"));
        assert_eq!(decls[8].type_sig.as_deref(), Some("x = x"));
        assert_eq!(decls[9].type_sig.as_deref(), Some("α -> α"));
        assert!(decls.iter().all(|d| d.name != "hidden_in_body"));
    }

    /// Real Lean 3 theorem statements carry binders BEFORE the `:`
    /// (e.g. `theorem foo (n : Nat) : n + 0 = n`). The historical
    /// `extract_type_sig` returns the text after the first top-level
    /// `:`, silently dropping those binders. With the lean3_type_parser
    /// wired in, the body `n + 0 = n` then references `n` as a free
    /// Const — losing the universal quantification entirely. This test
    /// PINS the contract: the binders must end up in the FlatExpr tree
    /// as Pi nodes, with body references resolving to BVars.
    /// `instance`, `example`, and `abbreviation` are standard Lean 3
    /// declaration keywords used throughout mathlib. The historical
    /// DECL_STARTS table omitted them, silently dropping these decls.
    #[test]
    fn instance_example_abbreviation_are_parsed() {
        // `example` is anonymous and is correctly skipped by parse_name.
        // `instance` and `abbreviation` were missing from DECL_STARTS
        // before this session and were silently dropped.
        let text = concat!(
            "instance nat.has_zero : has_zero nat := ⟨0⟩\n",
            "example : 1 + 1 = 2 := rfl\n",
            "abbreviation MyNat := nat\n",
        );
        let decls = parse_lean3_file(text, "Inst.lean");
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["nat.has_zero", "MyNat"]);
        assert_eq!(decls[0].kind, DeclKind::Definition);
        assert_eq!(decls[1].kind, DeclKind::Definition);
    }

    #[test]
    fn theorem_binders_before_colon_must_become_pi_nodes() {
        let text = "theorem add_zero_right (n : Nat) : n + 0 = n := rfl\n";
        let decls = parse_lean3_file(text, "T.lean");
        assert_eq!(decls.len(), 1);
        let decl = &decls[0];
        let mut writer = ShardWriter::new();
        let written = write_lean3_shard(&decls, &mut writer).unwrap();
        if written == 0 {
            panic!(
                "decl was skipped — extract_type_sig probably lost the binder \
                 `(n : Nat)`. type_sig={:?}",
                decl.type_sig
            );
        }
        // If binders were preserved, `n` is bound (BVar) — the only
        // strings added beyond the constant name are infix op names
        // (`Add`, `Eq`) and possibly `Nat`. If `n` leaks into the
        // string table as a free Const, that's the bug.
        let strings: Vec<&str> = (0..writer.string_count())
            .map(|i| writer.string_at(i as u32))
            .collect();
        assert!(
            !strings.contains(&"n"),
            "binder name 'n' leaked into string table: {strings:?} — \
             binders before the `:` were not parsed as Pi binders"
        );
    }

    #[test]
    fn test_write_lean3_shard_integration() {
        let text = concat!(
            "namespace Demo\naxiom base : Prop\n",
            "def id_nat : Nat -> Nat :=\n  fun n => n\n",
            "lemma id_nat_ok : id_nat 0 = 0 := rfl\nend Demo\n",
        );
        let decls = parse_lean3_file(text, "Demo.lean");
        let mut writer = ShardWriter::new();
        let written = write_lean3_shard(&decls, &mut writer).unwrap();
        let mut bytes = Vec::new();
        writer.write(&mut bytes).unwrap();
        assert_eq!(written, 3, "all three fixtures should parse");
        assert!(!bytes.is_empty());
        // Each decl's type signature parses into a real FlatExpr tree,
        // so expr_count must exceed constant_count — the structural
        // signature that mathverse_fidelity_check uses to distinguish a real
        // import from the old name-only stub. Three constants written
        // with one shared placeholder used to give `expr_count = 1,
        // constant_count = 3`; the new contract is the inverse.
        assert!(
            writer.expr_count() > writer.constant_count(),
            "expected expr_count ({}) > constant_count ({}) — real type \
             trees should outnumber declarations",
            writer.expr_count(),
            writer.constant_count(),
        );
    }
}
