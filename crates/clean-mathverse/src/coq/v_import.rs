// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for Coq `.v` source files.

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind as ShardDeclKind, ImportConfidence,
    MathverseConstantHeader, SourceSystem, NO_VALUE,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclKind {
    Theorem,
    Lemma,
    Definition,
    Fixpoint,
    Inductive,
    CoInductive,
    Axiom,
    Parameter,
    Hypothesis,
    Variable,
    Record,
    Class,
    Instance,
}

impl DeclKind {
    fn has_value(self) -> bool {
        !matches!(
            self,
            Self::Theorem
                | Self::Lemma
                | Self::Axiom
                | Self::Parameter
                | Self::Hypothesis
                | Self::Variable
        )
    }

    /// Map Coq `.v` surface-syntax kind to the shard-level [`ShardDeclKind`].
    /// Theorem/Lemma → Theorem; Axiom/Parameter/Hypothesis/Variable → Axiom;
    /// Inductive/CoInductive/Record/Class → Inductive;
    /// Definition/Fixpoint/Instance → Definition.
    fn to_shard(self) -> ShardDeclKind {
        match self {
            Self::Theorem | Self::Lemma => ShardDeclKind::Theorem,
            Self::Axiom | Self::Parameter | Self::Hypothesis | Self::Variable => {
                ShardDeclKind::Axiom
            }
            Self::Inductive | Self::CoInductive | Self::Record | Self::Class => {
                ShardDeclKind::Inductive
            }
            Self::Definition | Self::Fixpoint | Self::Instance => ShardDeclKind::Definition,
        }
    }
}

const DECL_STARTS: [(&str, DeclKind); 13] = [
    ("CoInductive", DeclKind::CoInductive),
    ("Definition", DeclKind::Definition),
    ("Inductive", DeclKind::Inductive),
    ("Fixpoint", DeclKind::Fixpoint),
    ("Parameter", DeclKind::Parameter),
    ("Hypothesis", DeclKind::Hypothesis),
    ("Instance", DeclKind::Instance),
    ("Theorem", DeclKind::Theorem),
    ("Variable", DeclKind::Variable),
    ("Record", DeclKind::Record),
    ("Axiom", DeclKind::Axiom),
    ("Lemma", DeclKind::Lemma),
    ("Class", DeclKind::Class),
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CoqVDeclaration {
    pub name: String,
    pub kind: DeclKind,
    /// Raw binder-prefix text between the declaration name and the first
    /// top-level `:` (e.g. `(A : Type)` in
    /// `Definition id (A : Type) : A -> A`). Empty when the declaration
    /// has no binders before the colon. Each binder becomes a Pi node at
    /// shard-emit time so that body references resolve to BVars rather
    /// than free Consts.
    pub binders: Option<String>,
    pub type_sig: Option<String>,
    pub source_file: String,
}

#[derive(Clone, Debug)]
struct Scope {
    name: String,
    qualifies: bool,
}

pub(crate) fn parse_coq_v_file(content: &str, filename: &str) -> Vec<CoqVDeclaration> {
    let mut decls = Vec::new();
    let mut scopes = Vec::<Scope>::new();
    let mut in_proof = false;
    for stmt in split_sentences(content) {
        let stmt = normalize_ws(&stmt);
        if stmt.is_empty() {
            continue;
        }
        if in_proof {
            if is_proof_end(&stmt) {
                in_proof = false;
            }
            continue;
        }
        if is_proof_start(&stmt) {
            in_proof = true;
            continue;
        }
        if is_notation(&stmt) || apply_block(&stmt, &mut scopes) {
            continue;
        }
        if let Some(decl) = parse_decl(&stmt, filename, &scopes) {
            decls.push(decl);
        }
    }
    decls
}

/// Write parsed declarations to a shard.
///
/// For each declaration, the Gallina `type_sig` string (with any binder
/// prefix re-attached as a leading `forall`) is parsed into a real
/// `FlatExpr` tree via [`crate::coq::v_type_parser`]. A declaration whose
/// type signature is absent or fails to parse is **skipped** — never
/// replaced with a `sort(0)` placeholder. This is the import-time
/// guarantee that the resulting shard's `expr_count > constant_count`.
///
/// This is a Level-0/1 data import, not a verified elaboration; every
/// header is tagged `ImportConfidence::Unverified` and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub(crate) fn write_coq_v_shard(
    decls: &[CoqVDeclaration],
    writer: &mut ShardWriter,
) -> MathverseResult<usize> {
    let mut written = 0usize;
    for decl in decls {
        let Some(sig) = decl.type_sig.as_deref() else {
            // No declared type — would have to emit a placeholder. Skip.
            continue;
        };
        // Re-attach any binder prefix as a leading `forall` so the parser
        // wraps the body in real Pi nodes and resolves binder-name
        // references inside the body as BVars rather than free Consts.
        let synthesized = match decl.binders.as_deref() {
            Some(binders) => format!("forall {binders}, {sig}"),
            None => sig.to_owned(),
        };
        let Some(type_idx) = crate::coq::v_type_parser::parse_coq_v_type(&synthesized, writer)
        else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        // A real value/proof-term translator is out of scope; mark the
        // constant axiomatized rather than emit a fake body.
        let value_idx = NO_VALUE;
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
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

fn parse_decl(stmt: &str, filename: &str, scopes: &[Scope]) -> Option<CoqVDeclaration> {
    let stmt = strip_prefixes(stmt);
    let (kind, rest) = decl_start(stmt)?;
    let (name, after_name) = take_ident(rest.trim_start())?;
    let (binders, type_sig) = extract_binders_and_type(after_name);
    Some(CoqVDeclaration {
        name: qualify_name(name, scopes),
        kind,
        binders,
        type_sig,
        source_file: filename.to_owned(),
    })
}

fn decl_start(stmt: &str) -> Option<(DeclKind, &str)> {
    for (keyword, kind) in DECL_STARTS {
        if let Some(rest) = match_word(stmt, keyword) {
            return Some((kind, rest));
        }
    }
    None
}

/// Split the text after a declaration name into its binder prefix and the
/// type body. The split point is the first top-level `:` (the one before
/// `:=` / the return type). For `Definition id (A : Type) : A -> A`, the
/// text after the name is ` (A : Type) : A -> A`, which splits into
/// binders `(A : Type)` and type `A -> A`. Returns `(binders, type_sig)`.
fn extract_binders_and_type(rest: &str) -> (Option<String>, Option<String>) {
    let Some(colon) = find_top_level_colon(rest) else {
        return (None, None);
    };
    let binders = normalize_ws(&rest[..colon]);
    let binders = (!binders.is_empty()).then_some(binders);
    let tail = &rest[colon + 1..];
    let end = find_top_level_assign(tail).unwrap_or(tail.len());
    let sig = normalize_ws(&tail[..end]);
    let type_sig = (!sig.is_empty()).then_some(sig);
    (binders, type_sig)
}

fn apply_block(stmt: &str, scopes: &mut Vec<Scope>) -> bool {
    let stmt = strip_prefixes(stmt);
    if let Some(rest) = match_word(stmt, "Module") {
        let rest = skip_module_modifiers(rest.trim_start());
        if let Some((name, after)) = take_ident(rest) {
            if after.trim().is_empty() {
                scopes.push(Scope {
                    name: name.to_owned(),
                    qualifies: true,
                });
                return true;
            }
        }
    }
    if let Some(rest) = match_word(stmt, "Section") {
        if let Some((name, after)) = take_ident(rest.trim_start()) {
            if after.trim().is_empty() {
                scopes.push(Scope {
                    name: name.to_owned(),
                    qualifies: false,
                });
                return true;
            }
        }
    }
    if let Some(rest) = match_word(stmt, "End") {
        if let Some((name, _)) = take_ident(rest.trim_start()) {
            while let Some(scope) = scopes.pop() {
                if scope.name == name {
                    break;
                }
            }
            return true;
        }
    }
    false
}

fn skip_module_modifiers(mut rest: &str) -> &str {
    loop {
        let trimmed = rest.trim_start();
        if let Some(next) = match_word(trimmed, "Import") {
            rest = next;
            continue;
        }
        if let Some(next) = match_word(trimmed, "Export") {
            rest = next;
            continue;
        }
        if let Some(next) = match_word(trimmed, "Type") {
            rest = next;
            continue;
        }
        return trimmed;
    }
}

fn is_notation(stmt: &str) -> bool {
    let stmt = strip_prefixes(stmt);
    match_word(stmt, "Notation").is_some()
        || match_word(stmt, "Infix").is_some()
        || match_word(stmt, "Reserved")
            .is_some_and(|rest| match_word(rest.trim_start(), "Notation").is_some())
}

fn is_proof_start(stmt: &str) -> bool {
    match_word(strip_prefixes(stmt), "Proof").is_some()
}

fn is_proof_end(stmt: &str) -> bool {
    let stmt = strip_prefixes(stmt);
    ["Qed", "Defined", "Admitted", "Abort"]
        .iter()
        .any(|kw| match_word(stmt, kw).is_some())
}

fn strip_prefixes(mut stmt: &str) -> &str {
    loop {
        stmt = stmt.trim_start();
        if let Some(rest) = strip_attribute(stmt) {
            stmt = rest;
            continue;
        }
        let mut stripped = false;
        for prefix in ["Local", "Global", "Polymorphic", "Monomorphic", "Program"] {
            if let Some(rest) = match_word(stmt, prefix) {
                stmt = rest;
                stripped = true;
                break;
            }
        }
        if !stripped {
            return stmt;
        }
    }
}

fn strip_attribute(stmt: &str) -> Option<&str> {
    let mut chars = stmt.char_indices();
    if chars.next()?.1 != '#' || chars.next()?.1 != '[' {
        return None;
    }
    let mut depth = 1usize;
    let mut in_string = false;
    let mut escaped = false;
    for (idx, ch) in stmt[2..].char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&stmt[idx + 3..]);
                }
            }
            _ => {}
        }
    }
    None
}

fn qualify_name(name: &str, scopes: &[Scope]) -> String {
    let mut out = String::new();
    for scope in scopes {
        if !scope.qualifies {
            continue;
        }
        if !out.is_empty() {
            out.push('.');
        }
        out.push_str(&scope.name);
    }
    if !out.is_empty() {
        out.push('.');
    }
    out.push_str(name);
    out
}

fn split_sentences(content: &str) -> Vec<String> {
    let chars: Vec<char> = content.chars().collect();
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut i = 0usize;
    let mut comment_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while i < chars.len() {
        let ch = chars[i];
        let next = chars.get(i + 1).copied();
        if comment_depth > 0 {
            if ch == '(' && next == Some('*') {
                comment_depth += 1;
                i += 2;
                continue;
            }
            if ch == '*' && next == Some(')') {
                comment_depth = comment_depth.saturating_sub(1);
                i += 2;
                continue;
            }
            cur.push(if ch == '\n' { '\n' } else { ' ' });
            i += 1;
            continue;
        }
        if in_string {
            cur.push(ch);
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if ch == '(' && next == Some('*') {
            comment_depth = 1;
            cur.push(' ');
            cur.push(' ');
            i += 2;
            continue;
        }
        if ch == '"' {
            in_string = true;
            cur.push(ch);
            i += 1;
            continue;
        }
        if ch == '.' && is_sentence_terminator(&chars, i) {
            let stmt = cur.trim();
            if !stmt.is_empty() {
                out.push(stmt.to_owned());
            }
            cur.clear();
            i += 1;
            continue;
        }
        cur.push(ch);
        i += 1;
    }
    let tail = cur.trim();
    if !tail.is_empty() {
        out.push(tail.to_owned());
    }
    out
}

fn is_sentence_terminator(chars: &[char], idx: usize) -> bool {
    let next = chars.get(idx + 1).copied();
    if matches!(next, Some(ch) if !ch.is_whitespace()) {
        return false;
    }
    let prev = idx.checked_sub(1).and_then(|i| chars.get(i)).copied();
    !(is_name_char(prev) && is_name_char(next))
}

fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut bracket = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut i = 0usize;
    while i < chars.len() {
        let (idx, ch) = chars[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            '[' => bracket += 1,
            ']' if bracket > 0 => bracket -= 1,
            ':' if paren == 0 && brace == 0 && bracket == 0 => {
                let next = chars.get(i + 1).map(|(_, c)| *c);
                if next != Some('=') {
                    return Some(idx);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn find_top_level_assign(text: &str) -> Option<usize> {
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut bracket = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut i = 0usize;
    while i + 1 < chars.len() {
        let (idx, ch) = chars[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => paren += 1,
            ')' if paren > 0 => paren -= 1,
            '{' => brace += 1,
            '}' if brace > 0 => brace -= 1,
            '[' => bracket += 1,
            ']' if bracket > 0 => bracket -= 1,
            ':' if paren == 0 && brace == 0 && bracket == 0 && chars[i + 1].1 == '=' => {
                return Some(idx);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn take_ident(text: &str) -> Option<(&str, &str)> {
    let text = text.trim_start();
    let first = text.chars().next()?;
    if !is_ident_start(first) {
        return None;
    }
    let mut end = 0usize;
    for (idx, ch) in text.char_indices() {
        if idx > 0 && !is_ident_continue(ch) {
            end = idx;
            break;
        }
    }
    if end == 0 {
        end = text.len();
    }
    Some((&text[..end], &text[end..]))
}

fn match_word<'a>(text: &'a str, word: &str) -> Option<&'a str> {
    let rest = text.strip_prefix(word)?;
    if is_name_char(rest.chars().next()) {
        return None;
    }
    Some(rest)
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    is_ident_start(ch) || ch.is_ascii_digit() || matches!(ch, '\'' | '.')
}

fn is_name_char(ch: Option<char>) -> bool {
    ch.map(is_ident_continue).unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_coq_v_file_with_modules_sections_and_proofs() {
        let content = r#"
Module Outer.
Section LocalFacts.
Notation "x == y" := (eq x y).
Definition id (A : Type) : A -> A := fun x => x.
Theorem id_ok : forall A (x : A), id A x = x.
Proof.
  Definition hidden : nat := 0.
  exact I.
Qed.
Lemma trivial : True.
Proof. exact I. Defined.
Parameter choice : forall A : Type, A.
Variable ctx : nat.
Hypothesis ctx_nonneg : 0 = 0.
Fixpoint add1 (n : nat) : nat := S n.
Inductive even : nat -> Prop := | even0 : even 0.
CoInductive stream : Type := { head : nat }.
Record point : Type := { px : nat; py : nat }.
Class eq_like : Type := { eq_like_refl : True }.
Instance point_inst : point := {| px := 0; py := 0 |}.
End LocalFacts.
End Outer.
"#;
        let decls = parse_coq_v_file(content, "Synthetic.v");
        let names: Vec<_> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "Outer.id",
                "Outer.id_ok",
                "Outer.trivial",
                "Outer.choice",
                "Outer.ctx",
                "Outer.ctx_nonneg",
                "Outer.add1",
                "Outer.even",
                "Outer.stream",
                "Outer.point",
                "Outer.eq_like",
                "Outer.point_inst"
            ]
        );
        assert!(decls.iter().all(|d| d.name != "hidden"));
        assert_eq!(decls[0].kind, DeclKind::Definition);
        assert_eq!(decls[0].type_sig.as_deref(), Some("A -> A"));
        assert_eq!(decls[1].kind, DeclKind::Theorem);
        assert_eq!(
            decls[1].type_sig.as_deref(),
            Some("forall A (x : A), id A x = x")
        );
        assert_eq!(decls[6].kind, DeclKind::Fixpoint);
        assert_eq!(decls[7].type_sig.as_deref(), Some("nat -> Prop"));
        assert_eq!(decls[8].kind, DeclKind::CoInductive);
        assert_eq!(decls[10].kind, DeclKind::Class);
        assert_eq!(decls[11].kind, DeclKind::Instance);
    }

    /// Real Coq declarations carry binders BEFORE the return-type colon
    /// (e.g. `Definition id (A : Type) : A -> A`). Those binders must end
    /// up in the FlatExpr tree as Pi nodes, with body references (`A`)
    /// resolving to BVars rather than free Consts.
    #[test]
    fn binders_before_colon_become_pi_nodes() {
        let decls = parse_coq_v_file("Definition id (A : Type) : A -> A := fun x => x.\n", "T.v");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].binders.as_deref(), Some("(A : Type)"));
        assert_eq!(decls[0].type_sig.as_deref(), Some("A -> A"));
        let mut writer = ShardWriter::new();
        let written = write_coq_v_shard(&decls, &mut writer).unwrap();
        assert_eq!(written, 1, "decl with parseable type must be written");
        // If the binder `(A : Type)` was preserved, the `A`s in `A -> A`
        // are bound (BVar). A leaked free Const `A` would land in strings.
        let strings: Vec<&str> = (0..writer.string_count())
            .map(|i| writer.string_at(i as u32))
            .collect();
        assert!(
            !strings.contains(&"A"),
            "binder name 'A' leaked into string table: {strings:?} — \
             binders before the `:` were not parsed as Pi binders"
        );
    }

    #[test]
    fn test_write_coq_v_shard_emits_real_types() {
        let content = r#"
Module M.
Definition zero : nat := 0.
Axiom ext : forall A : Type, A.
Theorem foo : forall n : nat, n + 0 = n.
Proof. intro n. apply plus_n_O. Qed.
End M.
"#;
        let decls = parse_coq_v_file(content, "RoundTrip.v");
        assert!(!decls.is_empty());
        let mut writer = ShardWriter::new();
        let written = write_coq_v_shard(&decls, &mut writer).expect("real importer must succeed");
        let mut bytes = Vec::new();
        writer.write(&mut bytes).unwrap();
        assert_eq!(written, 3, "all three fixtures should parse");
        assert!(!bytes.is_empty());
        // Each decl's type signature parses into a real FlatExpr tree, so
        // expr_count must exceed constant_count — the structural signature
        // distinguishing a real import from the old name-only stub (which
        // produced expr_count = 1, constant_count = N).
        assert!(
            writer.expr_count() > writer.constant_count(),
            "expected expr_count ({}) > constant_count ({}) — real type \
             trees should outnumber declarations",
            writer.expr_count(),
            writer.constant_count(),
        );
    }
}
