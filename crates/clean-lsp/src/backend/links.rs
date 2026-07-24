// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Document links and code lenses.
//!
//! - `textDocument/documentLink`: turns each `import Foo.Bar` module reference
//!   into a clickable link whose best-effort target is the `.lean` file the
//!   module path would resolve to relative to the importing document. The cheap
//!   pass attaches a [`DocumentLinkData`] payload and a generic tooltip;
//!   `documentLink/resolve` (see [`CleanBackend::resolve_document_link`]) then
//!   verifies the target against the filesystem and enriches the tooltip,
//!   keeping the link's target only when it points at a file that genuinely
//!   exists.
//! - `textDocument/codeLens`: surfaces one lens per top-level named declaration
//!   describing its kind and name. Lenses are produced *lazily*: the cheap
//!   `textDocument/codeLens` pass anchors a range and stashes a [`CodeLensData`]
//!   payload, and the title/command is filled in on demand by
//!   `codeLens/resolve` (see [`CleanBackend::resolve_code_lens`]). Resolve also
//!   enriches the title with the declaration's elaborated type when the
//!   document has been elaborated, without fabricating type information the
//!   document does not have.
//!
//! Both providers are driven by the lexer / parsed-command view rather than a
//! successful full elaboration, so they degrade gracefully on empty or
//! malformed input (returning an empty result instead of failing).

use super::CleanBackend;
use crate::document::CommandKind;
use clean_parser::lexer::{Lexer, TokenKind};
use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::*;

/// Opaque payload attached to a [`CodeLens`] so that `codeLens/resolve` can
/// recover the declaration the lens was produced for and lazily compute its
/// command/title without re-scanning every declaration in the document.
///
/// The LSP spec treats `CodeLens::data` as an opaque value owned by the server:
/// the client round-trips it verbatim between `textDocument/codeLens` and
/// `codeLens/resolve`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CodeLensData {
    /// Document the declaration belongs to (so resolve can find the live
    /// document even though resolve requests carry no `textDocument`).
    pub(crate) uri: String,
    /// Name of the declaration the lens anchors on.
    pub(crate) name: String,
    /// Human-readable keyword for the declaration's kind (e.g. `def`).
    pub(crate) kind: String,
}

impl CodeLensData {
    /// Encode into the `serde_json::Value` shape the `CodeLens::data` field
    /// expects. Returns `None` if serialization fails, which degrades the lens
    /// to a non-resolvable (but still valid) lens rather than dropping it.
    pub(crate) fn to_value(&self) -> Option<serde_json::Value> {
        serde_json::to_value(self).ok()
    }

    /// Decode from a `CodeLens::data` value, returning `None` when the value is
    /// absent or does not match our payload shape (e.g. a lens produced by a
    /// different code path or protocol version).
    pub(crate) fn from_value(value: &serde_json::Value) -> Option<Self> {
        serde_json::from_value(value.clone()).ok()
    }
}

/// Opaque payload attached to a [`DocumentLink`] so that `documentLink/resolve`
/// can recover which import the link covers and lazily verify/refine its target
/// and tooltip without re-scanning the whole document.
///
/// As with [`CodeLensData`], the LSP spec treats `DocumentLink::data` as an
/// opaque value the client round-trips verbatim between
/// `textDocument/documentLink` and `documentLink/resolve`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DocumentLinkData {
    /// Dotted module path the link covers (e.g. `Foo.Bar`).
    pub(crate) module: String,
}

impl DocumentLinkData {
    /// Encode into the `serde_json::Value` shape the `DocumentLink::data` field
    /// expects. Returns `None` if serialization fails, which degrades the link
    /// to a non-resolvable (but still valid) link rather than dropping it.
    pub(crate) fn to_value(&self) -> Option<serde_json::Value> {
        serde_json::to_value(self).ok()
    }

    /// Decode from a `DocumentLink::data` value, returning `None` when the value
    /// is absent or does not match our payload shape.
    pub(crate) fn from_value(value: &serde_json::Value) -> Option<Self> {
        serde_json::from_value(value.clone()).ok()
    }
}

/// A module path recovered from an `import` statement: its dotted components
/// and the byte span covering the whole path in the source text.
struct ImportModule {
    components: Vec<String>,
    start: usize,
    end: usize,
}

impl CleanBackend {
    /// Compute `textDocument/documentLink` entries for a document.
    ///
    /// Each `import` module reference becomes a [`DocumentLink`] whose range
    /// covers the dotted module path and whose target is the best-effort
    /// `.lean` file the path resolves to, relative to the importing document's
    /// directory. When no target can be derived (e.g. a non-`file:` URI) the
    /// link is still returned with a descriptive tooltip so the path remains
    /// surfaced. Each link carries a [`DocumentLinkData`] payload so that
    /// `documentLink/resolve` can later verify the target against the
    /// filesystem and enrich the tooltip. Returns an empty vector for unknown
    /// documents.
    pub(crate) fn get_document_links(&self, uri: &Url) -> Vec<DocumentLink> {
        let Some(doc) = self.documents.get(uri) else {
            return Vec::new();
        };
        let text = doc.text();

        Self::scan_import_modules(&text)
            .into_iter()
            .map(|module| {
                let dotted = module.components.join(".");
                let range = Range {
                    start: doc.offset_to_position(module.start),
                    end: doc.offset_to_position(module.end),
                };
                let target = Self::resolve_module_target(uri, &module.components);
                let data = DocumentLinkData {
                    module: dotted.clone(),
                }
                .to_value();
                DocumentLink {
                    range,
                    target,
                    tooltip: Some(format!("import {dotted}")),
                    data,
                }
            })
            .collect()
    }

    /// Resolve a [`DocumentLink`] for a `documentLink/resolve` request.
    ///
    /// The cheap `textDocument/documentLink` pass derives a *best-effort*
    /// `.lean` target by string-mapping the dotted module path; it deliberately
    /// does not touch the filesystem. Resolve performs that verification:
    ///
    /// - If the link's target points at a `.lean` file that genuinely exists on
    ///   disk, the target is kept and the tooltip is enriched with the file's
    ///   display path (`import Foo.Bar -> /proj/Foo/Bar.lean`).
    /// - If the best-effort target does not exist, the target is dropped (so the
    ///   client does not offer to open a missing file) and the tooltip notes the
    ///   module could not be located.
    ///
    /// A link whose payload is missing or malformed, or whose target is not a
    /// `file:` URI, is returned unchanged rather than failing the request.
    pub(crate) fn resolve_document_link(&self, mut link: DocumentLink) -> DocumentLink {
        let Some(data) = link.data.as_ref().and_then(DocumentLinkData::from_value) else {
            return link;
        };

        // Only `file:` targets can be checked against the filesystem; leave
        // anything else (e.g. a non-`file:` import, which never had a target)
        // exactly as produced.
        let Some(target) = link.target.as_ref() else {
            return link;
        };
        let Ok(path) = target.to_file_path() else {
            return link;
        };

        if path.is_file() {
            link.tooltip = Some(format!("import {} -> {}", data.module, path.display()));
        } else {
            // Faithful: do not hand back a target that points nowhere.
            link.target = None;
            link.tooltip = Some(format!("import {} (module file not found)", data.module));
        }
        link
    }

    /// Scan the source text for `import` statements and recover each module
    /// path with its byte span.
    ///
    /// Works directly off the lexer rather than the parser AST so it stays
    /// robust against parse failures elsewhere in the document. A module path
    /// is `Ident (Dot Ident)*` whose tokens are byte-adjacent (no interior
    /// whitespace), matching Lean's contiguous dotted module names. Multiple
    /// modules may follow a single `import` keyword when comma-separated or
    /// whitespace-separated on the same physical line, mirroring the grammar in
    /// `clean_parser::grammar::decl::commands::import_decl`.
    fn scan_import_modules(text: &str) -> Vec<ImportModule> {
        let tokens = Lexer::tokenize(text);
        let mut modules = Vec::new();
        let mut idx = 0;

        while idx < tokens.len() {
            if !matches!(tokens[idx].kind, TokenKind::Import) {
                idx += 1;
                continue;
            }
            idx += 1; // consume `import`

            // Parse one or more module paths belonging to this import.
            while let Some(module) = Self::take_module_path(&tokens, &mut idx) {
                modules.push(module);

                // Comma separates modules on the same import line.
                if idx < tokens.len() && matches!(tokens[idx].kind, TokenKind::Comma) {
                    idx += 1;
                    continue;
                }

                // A bare identifier still on the same physical line continues
                // the import (whitespace-separated form). Anything else — a
                // newline-led token or a non-identifier — ends the import.
                let continues = idx < tokens.len()
                    && matches!(tokens[idx].kind, TokenKind::Ident(_))
                    && !tokens[idx].preceded_by_newline;
                if !continues {
                    break;
                }
            }
        }

        modules
    }

    /// Consume a single `Ident (Dot Ident)*` module path starting at `*idx`,
    /// advancing `*idx` past it. Returns `None` (without advancing) when the
    /// cursor is not on an identifier.
    fn take_module_path(
        tokens: &[clean_parser::lexer::Token],
        idx: &mut usize,
    ) -> Option<ImportModule> {
        let TokenKind::Ident(first) = &tokens.get(*idx)?.kind else {
            return None;
        };
        let start = tokens[*idx].span.start;
        let mut end = tokens[*idx].span.end;
        let mut components = vec![first.clone()];
        *idx += 1;

        // Continue while the next two tokens are a byte-adjacent `. Ident`.
        while *idx + 1 < tokens.len() {
            let dot = &tokens[*idx];
            let ident = &tokens[*idx + 1];
            let adjacent = dot.span.start == end && ident.span.start == dot.span.end;
            if !matches!(dot.kind, TokenKind::Dot) || !adjacent {
                break;
            }
            let TokenKind::Ident(part) = &ident.kind else {
                break;
            };
            components.push(part.clone());
            end = ident.span.end;
            *idx += 2;
        }

        Some(ImportModule {
            components,
            start,
            end,
        })
    }

    /// Best-effort resolution of a dotted module path to a `.lean` file URI,
    /// relative to the importing document's directory.
    ///
    /// `Foo.Bar.Baz` relative to `file:///proj/Main.lean` resolves to
    /// `file:///proj/Foo/Bar/Baz.lean`. Returns `None` for non-`file:` URIs,
    /// rootless paths, or empty module components — callers keep the link but
    /// without a target in that case.
    fn resolve_module_target(uri: &Url, components: &[String]) -> Option<Url> {
        if components.is_empty() || components.iter().any(String::is_empty) {
            return None;
        }
        let base_path = uri.to_file_path().ok()?;
        let dir = base_path.parent()?;

        let mut path = dir.to_path_buf();
        for component in components {
            path.push(component);
        }
        path.set_extension("lean");

        Url::from_file_path(&path).ok()
    }

    /// Compute `textDocument/codeLens` entries for a document.
    ///
    /// Returns one *unresolved* lens per top-level named declaration, anchored
    /// on the declaration's start position. The cheap pass only records the
    /// range and a [`CodeLensData`] payload; the title and command are computed
    /// lazily by [`CleanBackend::resolve_code_lens`] when the client issues a
    /// `codeLens/resolve` request. Returns an empty vector for unknown or
    /// unparsed documents.
    ///
    /// A lens whose payload fails to serialize is dropped rather than emitted
    /// without a payload, since a `data`-less lens could never be resolved into
    /// a command.
    pub(crate) fn get_code_lenses(&self, uri: &Url) -> Vec<CodeLens> {
        let Some(doc) = self.documents.get(uri) else {
            return Vec::new();
        };
        let Some(parsed) = doc.parsed.as_ref() else {
            return Vec::new();
        };

        parsed
            .commands
            .iter()
            .filter_map(|cmd| {
                let name = cmd.name.as_ref()?;
                let kind = Self::command_kind_label(&cmd.kind)?;
                let position = doc.offset_to_position(cmd.start);
                let range = Range {
                    start: position,
                    end: position,
                };
                let data = CodeLensData {
                    uri: uri.to_string(),
                    name: name.clone(),
                    kind: kind.to_string(),
                }
                .to_value()?;
                Some(CodeLens {
                    range,
                    command: None,
                    data: Some(data),
                })
            })
            .collect()
    }

    /// Resolve the lazily-computed command/title of a [`CodeLens`] for a
    /// `codeLens/resolve` request.
    ///
    /// The lens's [`CodeLensData`] payload identifies the declaration; the
    /// title is built from its kind and name (e.g. `def foo`) and, when the
    /// owning document has been elaborated and exposes a matching declaration,
    /// enriched with the elaborated type (`def foo : Nat`). The lens carries a
    /// `clean.showDecl` command so a client can route activation back to the
    /// server. A lens whose payload is missing or malformed, or whose document
    /// is no longer open, is returned unchanged (still a valid, command-less
    /// lens) rather than failing the request.
    pub(crate) fn resolve_code_lens(&self, mut lens: CodeLens) -> CodeLens {
        let Some(data) = lens.data.as_ref().and_then(CodeLensData::from_value) else {
            return lens;
        };
        let Ok(uri) = Url::parse(&data.uri) else {
            return lens;
        };

        // Faithfully enrich with the elaborated type only when the live
        // document actually has one; otherwise fall back to kind + name.
        let type_str = self.documents.get(&uri).and_then(|doc| {
            doc.elaborated.as_ref().and_then(|elab| {
                elab.declarations
                    .iter()
                    .find(|decl| decl.name == data.name)
                    .map(|decl| decl.type_str.clone())
            })
        });

        let title = match type_str {
            Some(ty) => format!("{} {} : {}", data.kind, data.name, ty),
            None => format!("{} {}", data.kind, data.name),
        };

        lens.command = Some(Command {
            title,
            command: "clean.showDecl".to_string(),
            arguments: Some(vec![
                serde_json::Value::String(data.uri),
                serde_json::Value::String(data.name),
            ]),
        });
        lens
    }

    /// Human-readable keyword for a command kind, or `None` for kinds that do
    /// not correspond to a navigable top-level declaration.
    fn command_kind_label(kind: &CommandKind) -> Option<&'static str> {
        Some(match kind {
            CommandKind::Definition => "def",
            CommandKind::Theorem => "theorem",
            CommandKind::Lemma => "lemma",
            CommandKind::Inductive => "inductive",
            CommandKind::Coinductive => "coinductive",
            CommandKind::Structure => "structure",
            CommandKind::Class => "class",
            CommandKind::Instance => "instance",
            CommandKind::Axiom => "axiom",
            CommandKind::Variable => "variable",
            CommandKind::Universe => "universe",
            CommandKind::Namespace => "namespace",
            CommandKind::Example
            | CommandKind::Import
            | CommandKind::Open
            | CommandKind::Section
            | CommandKind::End
            | CommandKind::Other(_) => return None,
        })
    }
}
