// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Notation harvested from OTHER modules, replayed into a parser before the
//! file under parse is read.
//!
//! Lean 4's notation is an environment extension: `infixr:26 " ⥤ " => Functor`
//! declared in `Mathlib/CategoryTheory/Functor/Basic.lean` is visible in every
//! one of the 1,151 files that transitively import it. Clean's parser, by
//! contrast, starts every file from an empty registry
//! (`grammar/mod.rs`, `custom_operators` / `custom_mixfixes` are both
//! `Vec::new()` in the single constructor), so a notation is **file-local**: a
//! Mathlib file can only use a symbol that Clean hand-wrote into its builtin
//! grammar or that the file itself declares. That is the ceiling this module
//! lifts.
//!
//! # What is modelled
//!
//! [`NotationSeed`] is an ordered list of [`SeededNotation`] entries, each one
//! a notation *command* recovered from another module's source. A seed is
//! replayed through the SAME registration path a file-local declaration takes
//! ([`crate::Parser::seed_notation`] →
//! `Parser::register_custom_operator_ns`), so a seeded notation is neither more nor
//! less capable than a declared one: whatever shape the registry models
//! (fixed-arity infix/prefix/postfix, closed multi-hole mixfix, nullary
//! notation) is modelled for a seed too, and whatever stays parse-only stays
//! parse-only.
//!
//! # Harvesting, and why it is a line prescan
//!
//! [`NotationSeed::harvest_module_source`] recovers the notation commands of
//! one module from its `.lean` source WITHOUT parsing the module. A full parse
//! of an arbitrary Mathlib module is both expensive and (today) incomplete, and
//! a module whose body Clean cannot parse must still be able to contribute its
//! notation. The prescan therefore:
//!
//! * tracks `namespace` / `section` / `end` so a `scoped` notation is tagged
//!   with its FULL declaring namespace path, exactly as an in-file `scoped`
//!   declaration is;
//! * tracks `/- … -/` block-comment nesting and `--` line comments, so a
//!   notation *quoted in a docstring* is not harvested as a declaration;
//! * skips `local` notation, which Lean does not export past its own file —
//!   **615** of mathlib4 `43ad0e9d2`'s notation commands are `local`, MORE than
//!   the 579 exportable ones, and seeding them would be a parser lie, not a
//!   completeness win;
//! * skips `notation3`, Mathlib's own extended-binder macro command (162
//!   occurrences), which is not the core `notation` grammar;
//! * joins continuation lines only while the command is INCOMPLETE — see
//!   [`command_is_complete`] — which recovers all 12 of the checkout's wrapped
//!   commands while never reading past a command that already has its
//!   expansion;
//! * hands the recovered command text — and only that text — to the ordinary
//!   parser, and keeps the resulting [`crate::SurfaceDecl::Notation`].
//!
//! The prescan is deliberately conservative: anything it cannot recognise it
//! ignores, so the worst case is the status quo (a notation stays invisible),
//! never a wrong parse of the module it came from.

use crate::grammar::Parser;
use crate::surface::{DeclScope, NotationItem, NotationKind, SurfaceDecl, SurfaceExpr};

/// One notation command recovered from another module, ready to be registered.
#[derive(Debug, Clone)]
pub struct SeededNotation {
    /// `infixl` / `infixr` / `infix` / `prefix` / `postfix` / `notation`.
    pub kind: NotationKind,
    /// The `:N` suffix, if the command carried one.
    pub precedence: Option<u32>,
    /// The literal/variable pattern between the keyword and `=>`.
    pub pattern: Vec<NotationItem>,
    /// The term to the right of `=>`.
    pub expansion: SurfaceExpr,
    /// FULL declaring namespace path for a `scoped` notation; `None` for a
    /// plain one (always active once imported). A `local` notation is never
    /// seeded at all.
    pub scope_ns: Option<String>,
}

/// An ordered collection of notation commands harvested from a file's imports.
///
/// Order is preserved and duplicates are kept: registration order is what the
/// registry's overlap resolution consumes, and two modules may legitimately
/// declare the same symbol in different namespaces.
#[derive(Debug, Clone, Default)]
pub struct NotationSeed {
    entries: Vec<SeededNotation>,
}

/// Upper bound on the lines one notation command may span. Mathlib's longest
/// wrapped `notation` is well under this; the cap only stops a malformed
/// command from swallowing a whole file.
const MAX_COMMAND_LINES: usize = 12;

impl NotationSeed {
    /// An empty seed. A parser built with one behaves exactly as an unseeded
    /// parser does.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of harvested notation commands.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the seed carries no notation at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Append one already-built entry (used by callers that harvest from a
    /// source other than `.lean` text).
    pub fn push(&mut self, entry: SeededNotation) {
        self.entries.push(entry);
    }

    /// The harvested entries, in harvest order.
    #[must_use]
    pub fn entries(&self) -> &[SeededNotation] {
        &self.entries
    }

    /// Harvest every exportable notation command from one module's `.lean`
    /// source and append it to this seed. Returns how many were appended.
    ///
    /// See the module documentation for what is and is not recovered. This
    /// never fails: an unrecognised or unparseable command contributes
    /// nothing.
    pub fn harvest_module_source(&mut self, source: &str) -> usize {
        let before = self.entries.len();
        let lines: Vec<&str> = source.lines().collect();
        // Namespace path stack. `namespace A` pushes `Some("A")` (or
        // `Some("Outer.A")` when nested); `section`/`noncomputable section`
        // pushes `None` because a section does not extend the namespace path.
        let mut ns_stack: Vec<Option<String>> = Vec::new();
        // `/- … -/` nesting depth. Lean's block comments nest.
        let mut comment_depth: usize = 0;
        let mut idx = 0usize;
        while idx < lines.len() {
            let line = lines[idx];
            let (code, depth_after) = strip_comments(line, comment_depth);
            comment_depth = depth_after;
            let trimmed = code.trim();
            if trimmed.is_empty() {
                idx += 1;
                continue;
            }
            if let Some(rest) = strip_keyword(trimmed, "namespace") {
                let name = rest.split_whitespace().next().unwrap_or("");
                if !name.is_empty() {
                    let full = match ns_stack.iter().rev().flatten().next() {
                        Some(parent) => format!("{parent}.{name}"),
                        None => name.to_owned(),
                    };
                    ns_stack.push(Some(full));
                }
                idx += 1;
                continue;
            }
            if strip_keyword(trimmed, "section").is_some()
                || strip_keyword(trimmed, "noncomputable section").is_some()
                || trimmed == "section"
                || trimmed == "noncomputable section"
            {
                ns_stack.push(None);
                idx += 1;
                continue;
            }
            if trimmed == "end" || strip_keyword(trimmed, "end").is_some() {
                ns_stack.pop();
                idx += 1;
                continue;
            }
            let Some(command) = classify_notation_command(trimmed) else {
                idx += 1;
                continue;
            };
            // Recover the whole command. A command whose `=>` already has an
            // expansion after it is COMPLETE, and stops here — that is what
            // keeps the scan from eating the declaration below it. An
            // INCOMPLETE one must continue: Lean cannot start a new top-level
            // command while this one is unfinished, so the next non-blank
            // CODE line belongs to it whatever its indentation. Both shapes
            // occur in Mathlib: nine commands wrap after a trailing `=>` or
            // after `notation:25 (name := «…»)`, and three put the pattern on
            // the next line at column 0, below a `--` comment on the keyword's
            // own line (`Mathlib/Data/Opposite.lean:48`,
            // `Mathlib/CategoryTheory/Shift/Basic.lean:220`,
            // `Mathlib/Analysis/Normed/Affine/Isometry.lean:60`).
            let mut text = String::from(command.body);
            let mut consumed = 1usize;
            while consumed < MAX_COMMAND_LINES && !command_is_complete(&text) {
                let Some(next_raw) = lines.get(idx + consumed) else {
                    break;
                };
                let (next_code, next_depth) = strip_comments(next_raw, comment_depth);
                comment_depth = next_depth;
                consumed += 1;
                if next_code.trim().is_empty() {
                    continue;
                }
                text.push('\n');
                text.push_str(&next_code);
            }
            // `local` notation is consumed (so its continuation lines are not
            // re-scanned) but never recorded: Lean does not export it.
            if !command.local {
                self.record_command(&text, &ns_stack);
            }
            idx += consumed;
        }
        self.entries.len() - before
    }

    /// Parse one recovered command and record every notation declaration it
    /// produced, tagged with the namespace in force at its source position.
    fn record_command(&mut self, text: &str, ns_stack: &[Option<String>]) {
        let scope_ns = ns_stack.iter().rev().flatten().next().cloned();
        for decl in parse_notation_command(text) {
            let SurfaceDecl::Notation {
                kind,
                precedence,
                pattern,
                expansion,
                scope,
                ..
            } = decl
            else {
                continue;
            };
            // `local` is filtered above; `Default` and `Scoped` differ only in
            // whether the declaring namespace gates the notation.
            let entry_ns = match scope {
                DeclScope::Scoped => match &scope_ns {
                    // A `scoped` notation at file root has no namespace to
                    // gate on. Lean rejects it; harvest nothing.
                    None => continue,
                    some => some.clone(),
                },
                DeclScope::Default | DeclScope::Local => None,
            };
            self.entries.push(SeededNotation {
                kind,
                precedence,
                pattern,
                expansion: *expansion,
                scope_ns: entry_ns,
            });
        }
    }
}

/// Header modifiers Lean 4's module system allows in front of `import`.
///
/// The pinned Mathlib checkout (`43ad0e9d2`) is module-system source: of its
/// 25,590 import commands, **24,640 are `public import`** and 469 are
/// `public meta import`; a bare `import` is the minority at 451. A scanner
/// that only knew the bare spelling read ZERO imports from a Mathlib file and
/// silently harvested nothing — measured before this list existed.
const IMPORT_MODIFIERS: [&str; 4] = ["public", "private", "protected", "meta"];

/// The module names a Lean source file imports, in source order.
///
/// Lean's file header is `module`? `prelude`? followed by a run of `import`
/// commands and terminated by the first other command, so the scan stops there
/// rather than reading the whole file. Comments are stripped with the same
/// machinery [`NotationSeed::harvest_module_source`] uses, so the copyright
/// block every Mathlib file opens with — and any `import` quoted inside a
/// docstring — is not mistaken for the header.
#[must_use]
pub fn scan_imports(source: &str) -> Vec<String> {
    let mut modules = Vec::new();
    let mut comment_depth = 0usize;
    for line in source.lines() {
        let (code, depth_after) = strip_comments(line, comment_depth);
        comment_depth = depth_after;
        let trimmed = code.trim();
        if trimmed.is_empty() {
            continue;
        }
        // `module` opens a module-system file; `prelude` opens a core file.
        // Neither ends the header.
        if trimmed == "module" || trimmed == "prelude" {
            continue;
        }
        let mut tokens = trimmed.split_whitespace().peekable();
        while tokens.peek().is_some_and(|t| IMPORT_MODIFIERS.contains(t)) {
            tokens.next();
        }
        if tokens.next() != Some("import") {
            // First non-header command: the import block is over.
            break;
        }
        // `import all Foo` re-exports; the module named is still `Foo`.
        if tokens.peek() == Some(&"all") {
            tokens.next();
        }
        if let Some(module) = tokens.next() {
            if is_module_name(module) {
                modules.push(module.to_owned());
            }
        }
    }
    modules
}

/// Whether `s` is a plausible dotted Lean module name.
fn is_module_name(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with('.')
        && !s.ends_with('.')
        && s.split('.').all(|seg| {
            !seg.is_empty()
                && seg
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        })
}

/// What a candidate notation line was recognised as.
struct NotationCommand<'a> {
    /// The command text with any `@[…]` attribute prefix removed.
    body: &'a str,
    /// `local notation …` — file-local in Lean, never exported.
    local: bool,
}

/// The core notation command keywords. Order is irrelevant:
/// [`starts_with_command`] requires the keyword to end at a non-identifier
/// character, so `infixl:65` never matches `infix` (`l` continues the word).
const NOTATION_KEYWORDS: [&str; 6] = ["infixl", "infixr", "infix", "prefix", "postfix", "notation"];

/// Recognise a notation command at the start of `trimmed`, tolerating an
/// `@[…]` attribute prefix and a `scoped` / `local` modifier.
fn classify_notation_command(trimmed: &str) -> Option<NotationCommand<'_>> {
    let body = strip_attribute_prefix(trimmed);
    let mut rest = body;
    let mut local = false;
    loop {
        if let Some(after) = strip_keyword(rest, "scoped") {
            rest = after;
            continue;
        }
        if let Some(after) = strip_keyword(rest, "local") {
            local = true;
            rest = after;
            continue;
        }
        break;
    }
    // `notation3` (Mathlib's extended-binder command, 140 occurrences) shares
    // the `notation` prefix and is NOT the core grammar. It is refused here
    // rather than filtered later: `starts_with_command` requires the keyword to
    // end at a non-identifier character, and `3` continues an identifier.
    NOTATION_KEYWORDS
        .iter()
        .find(|kw| starts_with_command(rest, kw))?;
    Some(NotationCommand { body, local })
}

/// Whether `s` begins with the command keyword `kw` followed by something that
/// cannot continue an identifier — a space, `:` (the precedence suffix), or a
/// string literal.
fn starts_with_command(s: &str, kw: &str) -> bool {
    let Some(rest) = s.strip_prefix(kw) else {
        return false;
    };
    match rest.chars().next() {
        None => true,
        Some(c) => !(c.is_alphanumeric() || c == '_' || c == '\'' || c == '!' || c == '?'),
    }
}

/// Strip a leading `@[…]` attribute list (possibly several), returning the
/// remaining command text. Bracket nesting is respected so `@[simp, foo[1]]`
/// is handled.
fn strip_attribute_prefix(s: &str) -> &str {
    let mut cur = s.trim_start();
    while let Some(after_at) = cur.strip_prefix("@[") {
        let mut depth = 1usize;
        let mut end = None;
        for (i, c) in after_at.char_indices() {
            match c {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(end) = end else {
            return cur;
        };
        cur = after_at[end + 1..].trim_start();
    }
    cur
}

/// Whether a recovered command already carries a non-empty expansion, i.e. a
/// `=>` OUTSIDE a string literal with something after it.
///
/// The `=>` must be found outside strings because a notation's own symbol may
/// contain one (`" => "` is a legal literal), and because Mathlib writes
/// `notation:25 (name := «…»)` whose `:=` is not the separator.
fn command_is_complete(text: &str) -> bool {
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0usize;
    let mut in_string = false;
    while i < chars.len() {
        let c = chars[i];
        if in_string {
            if c == '\\' {
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if c == '"' {
            in_string = true;
            i += 1;
            continue;
        }
        if c == '=' && chars.get(i + 1) == Some(&'>') {
            return chars[i + 2..].iter().any(|c| !c.is_whitespace());
        }
        i += 1;
    }
    false
}

/// If `s` starts with the word `kw` followed by whitespace, return the
/// remainder with that whitespace consumed.
fn strip_keyword<'a>(s: &'a str, kw: &str) -> Option<&'a str> {
    let rest = s.strip_prefix(kw)?;
    let mut chars = rest.chars();
    match chars.next() {
        Some(c) if c.is_whitespace() => Some(rest.trim_start()),
        _ => None,
    }
}

/// Blank out the comment regions of one source line, given the `/- … -/`
/// nesting depth on entry. Returns the code-only text and the depth on exit.
///
/// String literals are respected, so a notation whose symbol is `"--"` or
/// `"/-"` does not truncate its own command. This is the same discipline
/// `scripts/check_add_decl_ratchet.py` and
/// `crates/clean-elab/src/test_support/source_scan.rs` apply to source
/// scanners: a scan that matches raw text counts prose, not code.
fn strip_comments(line: &str, mut depth: usize) -> (String, usize) {
    let mut out = String::with_capacity(line.len());
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0usize;
    let mut in_string = false;
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        if depth > 0 {
            if c == '-' && next == Some('/') {
                depth -= 1;
                out.push(' ');
                out.push(' ');
                i += 2;
                continue;
            }
            if c == '/' && next == Some('-') {
                depth += 1;
                out.push(' ');
                out.push(' ');
                i += 2;
                continue;
            }
            out.push(' ');
            i += 1;
            continue;
        }
        if in_string {
            out.push(c);
            if c == '\\' && next.is_some() {
                out.extend(next);
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if c == '"' {
            in_string = true;
            out.push(c);
            i += 1;
            continue;
        }
        if c == '/' && next == Some('-') {
            depth += 1;
            out.push(' ');
            out.push(' ');
            i += 2;
            continue;
        }
        if c == '-' && next == Some('-') {
            // Line comment: the rest of the line is not code.
            break;
        }
        out.push(c);
        i += 1;
    }
    (out, depth)
}

/// Parse one recovered notation command and return the notation declarations
/// it produced. Anything that fails to parse yields nothing.
fn parse_notation_command(text: &str) -> Vec<SurfaceDecl> {
    match Parser::parse_file(text) {
        Ok(decls) => decls
            .into_iter()
            .filter(|d| matches!(d, SurfaceDecl::Notation { .. }))
            .collect(),
        Err(_) => Vec::new(),
    }
}

#[cfg(test)]
mod tests;
