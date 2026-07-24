// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for ACL2 `.lisp` files.

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
    Definition,
    Macro,
    Constant,
    Rule,
    Stobj,
}

impl DeclKind {
    fn has_value(self) -> bool {
        !matches!(self, Self::Theorem | Self::Rule)
    }

    /// Map ACL2 surface-syntax kind to the shard-level [`ShardDeclKind`].
    /// Theorem/Rule → Theorem; Definition/Macro → Definition;
    /// Constant/Stobj → Axiom (opaque values with no kernel-checkable body).
    fn to_shard(self) -> ShardDeclKind {
        match self {
            Self::Theorem | Self::Rule => ShardDeclKind::Theorem,
            Self::Definition | Self::Macro => ShardDeclKind::Definition,
            Self::Constant | Self::Stobj => ShardDeclKind::Axiom,
        }
    }
}

/// A single declaration extracted from a source file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Acl2Declaration {
    pub name: String,
    pub kind: DeclKind,
    /// ACL2 is dynamically typed and has no surface type signature, so
    /// this is always `None`. Retained for parity with the other
    /// importers' declaration structs.
    pub type_sig: Option<String>,
    /// Raw text of the whole top-level form (e.g.
    /// `(defthm foo (equal (+ 0 x) x))`). This is the input that
    /// [`crate::acl2_term_translator`] re-parses into a `FlatExpr` term
    /// tree at shard-emit time. `None` when only the name was recovered.
    pub body: Option<String>,
    pub source_file: String,
}

/// Parse source file content, extracting structured declarations.
pub(crate) fn parse_acl2_file(content: &str, filename: &str) -> Vec<Acl2Declaration> {
    let cleaned = strip_comments(content);
    let mut decls = Vec::new();
    for form in top_level_forms(&cleaned) {
        parse_top_level_form(form, filename, &mut decls);
    }
    decls
}

/// Write parsed declarations to a shard.
///
/// Each declaration's raw ACL2 form is translated into a real
/// `FlatExpr` term tree via [`crate::acl2_term_translator`] and stored
/// in the constant's `type_idx` slot. ACL2 is dynamically typed, so the
/// "type" we record is the **term shape** of the declaration's logical
/// content (the `defthm` statement, or the `defun` lambda body wrapped
/// in `Lam` binders) — see that module for the translation contract.
///
/// A declaration whose form is absent or cannot be faithfully
/// translated is **skipped** — never replaced with a `sort(0)`
/// placeholder. This is the import-time guarantee that the resulting
/// shard's `expr_count > constant_count`.
///
/// This is a Level-0/1 structural data import: emitted constants carry
/// `ImportConfidence::Unverified` + `AxiomProfile::AXIOMATIZED`. No
/// kernel type-checking is performed.
///
/// Returns the number of declarations actually written.
pub(crate) fn write_acl2_shard(
    decls: &[Acl2Declaration],
    writer: &mut ShardWriter,
) -> MathverseResult<usize> {
    let mut written = 0usize;
    for decl in decls {
        let Some(form) = decl.body.as_deref() else {
            // No form text to translate — skip rather than fake.
            continue;
        };
        let Some(type_idx) = crate::acl2_term_translator::translate_acl2_form(form, writer) else {
            // Translation failure (quoted data, unsupported form, …):
            // skip rather than fall back to a placeholder.
            continue;
        };
        let name_idx = writer.add_string(&decl.name);
        // ACL2 evaluation semantics are not modelled, so even def-shaped
        // declarations get no separate value term. Mark axiomatized.
        let value_idx = NO_VALUE;
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Acl2 as u8,
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

fn parse_top_level_form(form: &str, filename: &str, decls: &mut Vec<Acl2Declaration>) {
    match form_head(form) {
        Some("defthm") => push_named_decl(form, DeclKind::Theorem, filename, decls),
        Some("defun") => push_named_decl(form, DeclKind::Definition, filename, decls),
        Some("defmacro") => push_named_decl(form, DeclKind::Macro, filename, decls),
        Some("defconst") => push_named_decl(form, DeclKind::Constant, filename, decls),
        Some("defrule") => push_named_decl(form, DeclKind::Rule, filename, decls),
        Some("defstobj") => push_named_decl(form, DeclKind::Stobj, filename, decls),
        Some("mutual-recursion") => parse_mutual_recursion(form, filename, decls),
        _ => {}
    }
}

fn push_named_decl(form: &str, kind: DeclKind, filename: &str, decls: &mut Vec<Acl2Declaration>) {
    if let Some(name) = form_name(form) {
        decls.push(Acl2Declaration {
            name: name.to_owned(),
            kind,
            type_sig: None,
            body: Some(form.to_owned()),
            source_file: filename.to_owned(),
        });
    }
}

fn parse_mutual_recursion(form: &str, filename: &str, decls: &mut Vec<Acl2Declaration>) {
    let bytes = form.as_bytes();
    let mut idx = after_head(form).unwrap_or(form.len());
    let limit = form.len().saturating_sub(1);

    while idx < limit {
        idx = skip_ws(form, idx);
        if idx >= limit {
            break;
        }
        match bytes[idx] {
            b'(' => {
                let Some(end) = find_list_end(form, idx) else {
                    break;
                };
                let child = &form[idx..=end];
                if matches!(form_head(child), Some("defun")) {
                    push_named_decl(child, DeclKind::Definition, filename, decls);
                }
                idx = end + 1;
            }
            b'"' => idx = skip_string(form, idx),
            _ => {
                if let Some((_, next)) = read_symbol(form, idx) {
                    idx = next;
                } else {
                    idx += 1;
                }
            }
        }
    }
}

fn top_level_forms(text: &str) -> Vec<&str> {
    let mut forms = Vec::new();
    let mut start = None;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;

    for (idx, ch) in text.char_indices() {
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
            '(' => {
                if depth == 0 {
                    start = Some(idx);
                }
                depth += 1;
            }
            ')' => {
                if depth == 0 {
                    continue;
                }
                depth -= 1;
                if depth == 0 {
                    if let Some(begin) = start.take() {
                        forms.push(&text[begin..idx + 1]);
                    }
                }
            }
            _ => {}
        }
    }

    forms
}

fn strip_comments(content: &str) -> String {
    let mut out = String::with_capacity(content.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut in_comment = false;

    for ch in content.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
                out.push('\n');
            } else {
                out.push(' ');
            }
            continue;
        }

        if in_string {
            out.push(ch);
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
            ';' => {
                in_comment = true;
                out.push(' ');
            }
            '"' => {
                in_string = true;
                out.push(ch);
            }
            _ => out.push(ch),
        }
    }

    out
}

fn form_head(form: &str) -> Option<&str> {
    read_symbol(form, 1).map(|(sym, _)| sym)
}

fn form_name(form: &str) -> Option<&str> {
    let idx = after_head(form)?;
    read_symbol(form, idx).map(|(name, _)| name)
}

fn after_head(form: &str) -> Option<usize> {
    let (_, idx) = read_symbol(form, 1)?;
    Some(idx)
}

fn read_symbol(text: &str, idx: usize) -> Option<(&str, usize)> {
    let bytes = text.as_bytes();
    let mut idx = skip_ws(text, idx);
    if idx >= bytes.len() {
        return None;
    }

    if bytes[idx] == b'|' {
        let start = idx;
        idx += 1;
        while idx < bytes.len() {
            match bytes[idx] {
                b'\\' if idx + 1 < bytes.len() => idx += 2,
                b'|' => return Some((&text[start..idx + 1], idx + 1)),
                _ => idx += 1,
            }
        }
        return Some((&text[start..], bytes.len()));
    }

    let start = idx;
    while idx < bytes.len() {
        let b = bytes[idx];
        if b.is_ascii_whitespace() || matches!(b, b'(' | b')') {
            break;
        }
        idx += 1;
    }
    (idx > start).then_some((&text[start..idx], idx))
}

fn skip_ws(text: &str, mut idx: usize) -> usize {
    let bytes = text.as_bytes();
    while idx < bytes.len() && bytes[idx].is_ascii_whitespace() {
        idx += 1;
    }
    idx
}

fn skip_string(text: &str, mut idx: usize) -> usize {
    let bytes = text.as_bytes();
    if idx >= bytes.len() || bytes[idx] != b'"' {
        return idx;
    }
    idx += 1;
    let mut escaped = false;
    while idx < bytes.len() {
        match bytes[idx] {
            b'\\' if !escaped => {
                escaped = true;
                idx += 1;
            }
            b'"' if !escaped => return idx + 1,
            _ => {
                escaped = false;
                idx += 1;
            }
        }
    }
    bytes.len()
}

fn find_list_end(text: &str, start: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    if start >= bytes.len() || bytes[start] != b'(' {
        return None;
    }

    let mut idx = start;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;

    while idx < bytes.len() {
        let b = bytes[idx];
        if in_string {
            if escaped {
                escaped = false;
            } else if b == b'\\' {
                escaped = true;
            } else if b == b'"' {
                in_string = false;
            }
            idx += 1;
            continue;
        }

        match b {
            b'"' => {
                in_string = true;
                idx += 1;
            }
            b'(' => {
                depth += 1;
                idx += 1;
            }
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(idx);
                }
                idx += 1;
            }
            _ => idx += 1,
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_acl2_file_extracts_supported_forms() {
        let text = r#"
; top-level comment
(in-package "ACL2")

(defun append* (x y)
  ; ignored body comment
  (if (endp x)
      y
    (cons (car x) (append* (cdr x) y))))

(defthm append*-id
  (equal (append* x nil) x))

(defmacro with-msg (x)
  `(list ,x "semi ; and paren ) inside string"))

(defconst *limit* 42)

(mutual-recursion
  (defun evenp* (n)
    (if (zp n)
        t
      (oddp* (- n 1))))
  ; interstitial comment
  (defun oddp* (n)
    (if (zp n)
        nil
      (evenp* (- n 1)))))

(defrule append*-assoc
  (equal (append* (append* x y) z) (append* x (append* y z))))

(defstobj state$)
"#;
        let decls = parse_acl2_file(text, "Synthetic.lisp");
        let names: Vec<_> = decls.iter().map(|d| d.name.as_str()).collect();
        let kinds: Vec<_> = decls.iter().map(|d| d.kind).collect();

        assert_eq!(
            names,
            vec![
                "append*",
                "append*-id",
                "with-msg",
                "*limit*",
                "evenp*",
                "oddp*",
                "append*-assoc",
                "state$",
            ]
        );
        assert_eq!(
            kinds,
            vec![
                DeclKind::Definition,
                DeclKind::Theorem,
                DeclKind::Macro,
                DeclKind::Constant,
                DeclKind::Definition,
                DeclKind::Definition,
                DeclKind::Rule,
                DeclKind::Stobj,
            ]
        );
        assert!(decls.iter().all(|d| d.type_sig.is_none()));
        assert!(decls.iter().all(|d| d.source_file == "Synthetic.lisp"));
    }

    #[test]
    fn test_parse_acl2_file_ignores_nested_non_top_level_forms() {
        let text = r#"
(defthm quoting-demo
  (equal '(defun hidden (x) x)
         '(defun hidden (x) x)))

(mutual-recursion
  (defun alpha (n)
    (if (zp n) "literal (defun hidden)" (beta (- n 1))))
  (defun beta (n)
    (if (zp n) nil (alpha (- n 1)))))
"#;
        let decls = parse_acl2_file(text, "Nested.lisp");
        let names: Vec<_> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["quoting-demo", "alpha", "beta"]);
    }

    #[test]
    fn test_write_acl2_shard_emits_real_types() {
        // The ACL2 importer now translates each form's s-expression body
        // into a real `FlatExpr` term tree (via `acl2_term_translator`).
        // Both fixtures below are translatable: `id$`'s body `x` resolves
        // to a BVar, and the `defthm` statement is a nested-App tree. So
        // the shard's expr_count must exceed its constant_count — the
        // structural signature of a real import (NOT a name-only stub
        // with one shared placeholder per constant).
        let decls = parse_acl2_file(
            r#"
(defun id$ (x) x)
(defthm id$-self (equal (id$ x) x))
"#,
            "Mini.lisp",
        );
        assert!(!decls.is_empty(), "parser still extracts declarations");
        let mut writer = ShardWriter::new();
        let written = write_acl2_shard(&decls, &mut writer).expect("write should succeed");
        assert_eq!(written, 2, "both fixtures should translate and be written");

        let mut bytes = Vec::new();
        writer.write(&mut bytes).unwrap();
        assert!(!bytes.is_empty());

        assert!(
            writer.expr_count() > writer.constant_count(),
            "expected expr_count ({}) > constant_count ({}) — real term \
             trees should outnumber declarations",
            writer.expr_count(),
            writer.constant_count(),
        );
    }

    #[test]
    fn test_write_acl2_shard_skips_untranslatable_forms() {
        // defmacro / defconst / defstobj have no faithful term shape;
        // they must be SKIPPED, not emitted with a placeholder type.
        let decls = parse_acl2_file(
            r#"
(defmacro m (x) `(list ,x))
(defconst *c* 42)
(defstobj st)
"#,
            "Skip.lisp",
        );
        assert_eq!(decls.len(), 3, "parser still recovers names");
        let mut writer = ShardWriter::new();
        let written = write_acl2_shard(&decls, &mut writer).expect("write should succeed");
        assert_eq!(written, 0, "all three forms are untranslatable");
        assert_eq!(
            writer.constant_count(),
            0,
            "no constant should be written for skipped forms"
        );
    }
}
