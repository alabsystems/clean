// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pure parsing for the RECORD-RECONSTRUCTION salvage rung.
//!
//! sertop 8.20 SEGFAULTS serializing any kernel term containing a primitive-
//! projection `Proj` node (measured live: a minimal `Definition use (x : pr
//! nat) := pfst nat x` kills the process on the `Definition` query while its
//! `TypeOf` serializes fine). Hierarchy-style records (`Finite.class_of`,
//! `GRing.Ring.class_of`, ...) therefore cannot be dumped whole: their MInd
//! payload embeds projection data that mentions earlier primitive projections,
//! and 41 of the 53 measured mathcomp crash-families ALSO have a Proj inside
//! the constructor type itself (base chains like `choice.Choice.base base`).
//!
//! The reconstruction recovers the inductive from PARTS that survive:
//! - the constructor NAMES from the `Print <record>.` Notice text,
//! - the parameter count from the `Print` header binder groups,
//! - each constructor TYPE from `TypeOf` when it serializes (12/53), else
//!   from the `Check <ctor>.` pretty-print under `Set Printing All. Set
//!   Printing Primitive Projection Parameters.` (which prints the record
//!   parameters a raw `Proj` node does not store), parsed here into the
//!   importer DIALECT (bare-name `Prod` binders, 0-based `Rel`, flattened
//!   `App`, `(Const n)` / `(Ind n i)` / `(Construct n i j)` references).
//!
//! Everything is FAIL-CLOSED twice over: any unrecognized text shape returns
//! `None` (the family keeps today's type-only stand-in), and a wrong guess
//! (parameter count, universe collapse, compat-constant reading of a
//! projection) is caught by the kernel `add_inductive` replay at verify time,
//! which falls back to the checked family stand-in — today's behavior.

use std::collections::HashMap;
use std::path::Path;

use clean_mathverse::coq::alpha::Sexp;

/// What an already-dumped importer-form name denotes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormEntry {
    /// `(CoqInductive <name> <idx> ...)` — inductive block `idx`.
    Ind(u32),
    /// A `(Ctor <name> ...)` entry: constructor `ctor_idx` of `block`'s
    /// block `block_idx`.
    Ctor {
        block: String,
        block_idx: u32,
        ctor_idx: u32,
    },
    /// `(CoqConstant ...)` / `(CoqAxiom ...)`.
    Const,
}

/// Cross-module name index for the salvage rungs: every importer-form name
/// already dumped into the output directory (earlier modules of this run AND
/// prior runs' modules), mapped to what it denotes. Lets the salvage resolve
/// the SEMI-QUALIFIED atoms Coq pretty-prints (`ssralg.GRing.Ring.type`,
/// `eqtype.Equality.Pack` — measured live on the mathcomp 1.19 container) by
/// unique-suffix match; a missing or ambiguous atom fails the salvage closed.
pub struct DumpNameIndex {
    forms: HashMap<String, FormEntry>,
}

impl DumpNameIndex {
    /// Scan `out_dir`'s `*.sexp` dumps for top-level importer forms, PLUS its
    /// sibling library directories (the corpus layout is
    /// `coq-sexp/{stdlib,mathcomp}` and the import session resolves names
    /// across libraries — mathcomp's crash-family constructor types mention
    /// stdlib names like `Coq.ssr.ssrfun.commutative` and the
    /// `Coq.ssr.ssreflect.Phant` constructor, measured live). One sequential
    /// pass over line heads; unreadable files are skipped and `out_dir`'s own
    /// entries win over same-named sibling entries (they only shrink or
    /// stale-shift the resolvable set — fail closed either way).
    pub fn load(out_dir: &Path) -> Self {
        let mut forms = HashMap::new();
        Self::scan_dir(out_dir, &mut forms, true);
        let canon_out = out_dir.canonicalize().ok();
        if let Some(parent) = out_dir.parent() {
            if let Ok(siblings) = std::fs::read_dir(parent) {
                for entry in siblings.flatten() {
                    let path = entry.path();
                    if path.is_dir() && path.canonicalize().ok() != canon_out {
                        Self::scan_dir(&path, &mut forms, false);
                    }
                }
            }
        }
        Self { forms }
    }

    fn scan_dir(dir: &Path, forms: &mut HashMap<String, FormEntry>, overwrite: bool) {
        use std::io::BufRead as _;
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("sexp") {
                continue;
            }
            let Ok(file) = std::fs::File::open(&path) else {
                continue;
            };
            if overwrite {
                for line in std::io::BufReader::new(file).lines().map_while(Result::ok) {
                    scan_form_line(&line, forms);
                }
            } else {
                let mut fresh = HashMap::new();
                for line in std::io::BufReader::new(file).lines().map_while(Result::ok) {
                    scan_form_line(&line, &mut fresh);
                }
                for (name, entry) in fresh {
                    forms.entry(name).or_insert(entry);
                }
            }
        }
    }

    /// Build from explicit entries (tests, and the run overlay's base).
    #[cfg(test)]
    pub fn from_entries(entries: Vec<(&str, FormEntry)>) -> Self {
        Self {
            forms: entries
                .into_iter()
                .map(|(n, e)| (n.to_string(), e))
                .collect(),
        }
    }

    /// Resolve a pretty-printed semi-qualified atom against the dumped
    /// CONSTANT/INDUCTIVE names (constructor entries are deliberately
    /// excluded so the pre-existing type-only arity rung keeps byte-identical
    /// resolution behavior): an exact match wins; otherwise the UNIQUE name
    /// ending in `.<atom>`. Zero or several candidates → `None` (fail
    /// closed).
    pub fn resolve(&self, atom: &str) -> Option<(&str, &FormEntry)> {
        let non_ctor = |e: &&FormEntry| !matches!(e, FormEntry::Ctor { .. });
        if let Some((name, form)) = self.forms.get_key_value(atom).filter(|(_, e)| non_ctor(e)) {
            return Some((name.as_str(), form));
        }
        let suffix = format!(".{atom}");
        let mut hit: Option<(&str, &FormEntry)> = None;
        for (name, form) in self.forms.iter().filter(|(_, e)| non_ctor(e)) {
            if name.ends_with(&suffix) {
                if hit.is_some() {
                    return None; // ambiguous
                }
                hit = Some((name.as_str(), form));
            }
        }
        hit
    }
}

/// Scan one dump line for a top-level importer form, recording the declared
/// name plus (for inductives) every `(Ctor <name> ...)` constructor entry.
pub fn scan_form_line(line: &str, forms: &mut HashMap<String, FormEntry>) {
    let mut toks = line.split_whitespace();
    match toks.next() {
        Some("(CoqInductive") => {
            let (Some(name), Some(idx)) = (toks.next(), toks.next()) else {
                return;
            };
            let Ok(idx) = idx.parse::<u32>() else {
                return;
            };
            forms.insert(name.to_string(), FormEntry::Ind(idx));
            // `(Ctor <name> <type>)` sub-forms only ever appear at the top
            // level of a CoqInductive line (constructor REFERENCES in terms
            // are `(Construct ...)`), so a flat token scan is exact.
            let mut ctor_idx = 0u32;
            let mut prev_was_ctor = false;
            for tok in toks {
                if prev_was_ctor {
                    forms.insert(
                        tok.to_string(),
                        FormEntry::Ctor {
                            block: name.to_string(),
                            block_idx: idx,
                            ctor_idx,
                        },
                    );
                    ctor_idx += 1;
                    prev_was_ctor = false;
                }
                if tok == "(Ctor" {
                    prev_was_ctor = true;
                }
            }
        }
        Some("(CoqConstant") | Some("(CoqAxiom") => {
            if let Some(name) = toks.next() {
                forms.insert(name.to_string(), FormEntry::Const);
            }
        }
        _ => {}
    }
}

/// Names emitted by the CURRENT module dump run (the file index is stale for
/// them: a `--force` re-dump still sees the module's OLD `.sexp`, where a
/// crash family is a `CoqAxiom` stand-in even after this run reconstructed it
/// as a real inductive).
pub type RunOverlay = HashMap<String, FormEntry>;

/// Scan an in-memory dump buffer (the run's emitted forms so far).
pub fn scan_buffer(buf: &str) -> RunOverlay {
    let mut forms = HashMap::new();
    for line in buf.lines() {
        scan_form_line(line, &mut forms);
    }
    forms
}

/// Name-resolution scope for the reconstruction parser: run overlay entries
/// override the file index per fully-qualified name; the inductive currently
/// being reconstructed resolves to itself (it exists in NEITHER index — its
/// MInd crashed — or only as the stale type-only stand-in).
pub struct NameScope<'a> {
    pub file: &'a DumpNameIndex,
    pub run: &'a RunOverlay,
    /// Fully-qualified name of the inductive under reconstruction, if any.
    pub self_ind: Option<&'a str>,
}

/// A resolved pretty-printed atom, in importer-dialect reference terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolved {
    Ind(String, u32),
    Ctor(String, u32, u32),
    Const(String),
}

impl NameScope<'_> {
    /// Resolve an atom: self-reference first, then exact match, then unique
    /// suffix across the MERGED (overlay-wins) view of both indexes — with
    /// constructor entries INCLUDED (unlike [`DumpNameIndex::resolve`]):
    /// constructor references (`eqtype.Equality.Pack`) are exactly what the
    /// crash-family constructor types mention. Ambiguity fails closed.
    pub fn resolve(&self, atom: &str) -> Option<Resolved> {
        if let Some(s) = self.self_ind {
            if s == atom || s.ends_with(&format!(".{atom}")) {
                return Some(Resolved::Ind(s.to_string(), 0));
            }
        }
        if let Some(e) = self.run.get(atom) {
            return Some(to_resolved(atom, e));
        }
        if let Some((n, e)) = self.file.forms.get_key_value(atom) {
            return Some(to_resolved(n, e));
        }
        let suffix = format!(".{atom}");
        let mut hit: Option<(&str, &FormEntry)> = None;
        for (name, form) in self
            .run
            .iter()
            .chain(self.file.forms.iter().filter(|(n, _)| {
                // Overlay wins per fully-qualified name.
                !self.run.contains_key(n.as_str())
            }))
        {
            if name.ends_with(&suffix) {
                if hit.is_some_and(|(h, _)| h != name.as_str()) {
                    return None; // ambiguous across distinct names
                }
                hit = Some((name.as_str(), form));
            }
        }
        hit.map(|(n, e)| to_resolved(n, e))
    }
}

fn to_resolved(name: &str, e: &FormEntry) -> Resolved {
    match e {
        FormEntry::Ind(i) => Resolved::Ind(name.to_string(), *i),
        FormEntry::Ctor {
            block,
            block_idx,
            ctor_idx,
        } => Resolved::Ctor(block.clone(), *block_idx, *ctor_idx),
        FormEntry::Const => Resolved::Const(name.to_string()),
    }
}

// ---------------------------------------------------------------------------
// Print-text header parsing (keyword, name, params, constructor names)
// ---------------------------------------------------------------------------

/// Header facts extracted from a `Print <inductive>.` Notice text.
#[derive(Debug, PartialEq, Eq)]
pub struct PrintHeader {
    /// `Record` | `Structure` | `Class` | `Variant` | `Inductive`.
    pub keyword: String,
    /// The SHORT name printed after the keyword.
    pub short_name: String,
    /// Number of parameter binders between the name and the arity colon.
    pub num_params: u32,
    /// Constructor SHORT names, in declaration order.
    pub ctor_names: Vec<String>,
    /// The record has primitive projections (informational — sertop 8.20
    /// cannot serialize `Proj`-valued accessor bodies).
    pub prim_record: bool,
}

/// Parse the header of a `Print <inductive>.` text: keyword, short name,
/// parameter-binder count, and constructor names. Fail-closed `None` for
/// COINDUCTIVE blocks (their statement-only axiomatization is the correct
/// semantics — no sound inductive replay), MUTUAL blocks (`with` alternative
/// at top level), and any unrecognized shape.
pub fn parse_print_inductive(text: &str) -> Option<PrintHeader> {
    // The declaration runs to the first '.' at bracket-depth 0 followed by
    // whitespace/EOF (qualified names' dots have no following whitespace;
    // the trailing "Arguments ..." / "has primitive projections" prose is
    // after it).
    let decl = {
        let b = text.as_bytes();
        let mut depth = 0i32;
        let mut end = text.len();
        for (i, &c) in b.iter().enumerate() {
            match c {
                b'(' | b'{' | b'[' => depth += 1,
                b')' | b'}' | b']' => depth -= 1,
                b'.' if depth == 0 && b.get(i + 1).is_none_or(|n| n.is_ascii_whitespace()) => {
                    end = i;
                    break;
                }
                _ => {}
            }
        }
        &text[..end]
    };
    let toks = tokenize_print(decl);
    let mut i = 0usize;
    // Skip printed modifiers (universe-polymorphic records print e.g.
    // `Polymorphic Record ...`).
    const MODIFIERS: &[&str] = &[
        "Polymorphic",
        "Monomorphic",
        "Cumulative",
        "NonCumulative",
        "Private",
    ];
    while toks.get(i).is_some_and(|t| MODIFIERS.contains(&t.as_str())) {
        i += 1;
    }
    let keyword = toks.get(i)?.clone();
    if !matches!(
        keyword.as_str(),
        "Record" | "Structure" | "Class" | "Variant" | "Inductive"
    ) {
        return None; // CoInductive and non-inductive prints fail closed
    }
    i += 1;
    let short_name = toks.get(i)?.clone();
    if !is_ident(&short_name) {
        return None;
    }
    i += 1;
    // Parameter binder groups up to the top-level arity colon.
    let mut num_params = 0u32;
    loop {
        match toks.get(i).map(String::as_str) {
            Some("(") | Some("{") => {
                // `( names+ : type )` — count the names, then skip the
                // balanced remainder of the group (the type may nest).
                i += 1;
                let mut names = 0u32;
                while toks.get(i).is_some_and(|t| t != ":") {
                    if !is_ident_or_hole(toks.get(i)?) {
                        return None;
                    }
                    names += 1;
                    i += 1;
                }
                if names == 0 {
                    return None;
                }
                i += 1; // ':'
                let mut depth = 1i32;
                while depth > 0 {
                    match toks.get(i).map(String::as_str) {
                        Some("(") | Some("{") => depth += 1,
                        Some(")") | Some("}") => depth -= 1,
                        Some(_) => {}
                        None => return None,
                    }
                    i += 1;
                }
                num_params += names;
            }
            Some(":") => break,
            _ => return None,
        }
    }
    // Skip the arity text up to the top-level `:=`.
    while !(toks.get(i).is_some_and(|t| t == ":") && toks.get(i + 1).is_some_and(|t| t == "=")) {
        toks.get(i)?;
        i += 1;
    }
    i += 2;
    // Constructor section: record `{`-body carries ONE constructor; variant
    // alternatives split on top-level `|`. A top-level `with` is a MUTUAL
    // block — fail closed (the family export path is required for those).
    let rest = &toks[i.min(toks.len())..];
    let mut ctor_names = Vec::new();
    let mut depth = 0i32;
    let mut alt_start = true;
    for tok in rest {
        match tok.as_str() {
            "(" | "{" => {
                depth += 1;
                alt_start = false;
            }
            ")" | "}" => depth -= 1,
            "|" if depth == 0 => alt_start = true,
            "with" if depth == 0 => return None,
            t => {
                if alt_start && depth == 0 {
                    if !is_ident(t) {
                        return None;
                    }
                    ctor_names.push(t.to_string());
                }
                alt_start = false;
            }
        }
    }
    if matches!(keyword.as_str(), "Record" | "Structure" | "Class") && ctor_names.len() != 1 {
        return None;
    }
    Some(PrintHeader {
        keyword,
        short_name,
        num_params,
        ctor_names,
        prim_record: text.contains("has primitive projections"),
    })
}

/// Tokenize a `Print` declaration: whitespace-split, with `( ) { } | :`
/// separated into single-char tokens (`:=` therefore becomes `:` `=`).
fn tokenize_print(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        match ch {
            '(' | ')' | '{' | '}' | '|' | ':' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn is_ident(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
        && s.chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
}

fn is_ident_or_hole(s: &str) -> bool {
    s == "_" || is_ident(s)
}

// ---------------------------------------------------------------------------
// Check-text type parsing (pretty-printed Gallina -> importer dialect)
// ---------------------------------------------------------------------------

/// Parse a `Check`-pretty-printed TYPE (under `Set Printing All. Set Printing
/// Primitive Projection Parameters.`) into an importer-DIALECT term sexp.
///
/// Recognized grammar (everything else fails closed with `None`):
///
/// ```text
/// type   := 'forall' group+ ',' type | arrow
/// group  := '(' name ':' type ')'    (single-name groups only)
///         | name ':' arrow           (the bare single-group print form)
/// arrow  := app ('->' arrow)?
/// app    := atom+
/// atom   := '(' type ')' | 'Type' | 'Set' | 'Prop' | ['@']path
/// ```
///
/// Path atoms resolve through `scope` into `(Ind n i)` / `(Construct n i j)`
/// / `(Const n)`; single-segment atoms are first matched against the binder
/// stack (de Bruijn `Rel`, innermost = 0). `Type` collapses to the importer's
/// single-level `(Sort (Type 1))` model — the same collapse the importer
/// applies to raw named global levels, so parsed and raw payloads agree.
pub fn parse_check_type(text: &str, scope: &NameScope<'_>) -> Option<Sexp> {
    let toks = tokenize_type(text);
    let mut p = TypeParser {
        toks: &toks,
        pos: 0,
        scope,
        binders: Vec::new(),
    };
    let ty = p.parse_type()?;
    if p.pos != toks.len() {
        return None; // trailing tokens: not a shape we recognize
    }
    Some(ty)
}

/// Tokenize a pretty-printed type: whitespace-split with `( ) , :` separated
/// out (`->` survives as its own token; `@` stays glued to its path).
fn tokenize_type(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        match ch {
            '(' | ')' | ',' | ':' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// Gallina keywords that must never be consumed as term atoms.
const TERM_KEYWORDS: &[&str] = &[
    "forall", "fun", "match", "fix", "cofix", "let", "in", "with", "end", "if", "then", "else",
    "as", "return",
];

struct TypeParser<'a> {
    toks: &'a [String],
    pos: usize,
    scope: &'a NameScope<'a>,
    /// Binder names, outermost first (`Rel k` = distance from the end).
    binders: Vec<String>,
}

impl TypeParser<'_> {
    fn peek(&self) -> Option<&str> {
        self.toks.get(self.pos).map(String::as_str)
    }

    fn bump(&mut self) -> Option<&str> {
        let t = self.toks.get(self.pos).map(String::as_str);
        self.pos += 1;
        t
    }

    fn expect(&mut self, t: &str) -> Option<()> {
        (self.bump() == Some(t)).then_some(())
    }

    fn parse_type(&mut self) -> Option<Sexp> {
        if self.peek() != Some("forall") {
            return self.parse_arrow();
        }
        self.pos += 1;
        // (name, type) groups; each type is parsed in the context of the
        // binders before it. Multi-name groups (`(x y : T)`) would need a
        // de Bruijn lift of the shared type — fail closed (none measured in
        // the mathcomp crash families).
        let mut groups: Vec<(String, Sexp)> = Vec::new();
        if self.peek() == Some("(") {
            while self.peek() == Some("(") {
                self.pos += 1;
                let name = self.bump()?.to_string();
                if !is_ident_or_hole(&name) {
                    self.unwind(groups.len());
                    return None;
                }
                let Some(()) = self.expect(":") else {
                    self.unwind(groups.len());
                    return None; // multi-name group or stranger shape
                };
                let Some(ty) = self.parse_type() else {
                    self.unwind(groups.len());
                    return None;
                };
                let Some(()) = self.expect(")") else {
                    self.unwind(groups.len());
                    return None;
                };
                self.binders.push(name.clone());
                groups.push((name, ty));
            }
        } else {
            // Bare single group: `forall T : Type, ...`.
            let name = self.bump()?.to_string();
            if !is_ident_or_hole(&name) {
                return None;
            }
            self.expect(":")?;
            let ty = self.parse_arrow()?;
            self.binders.push(name.clone());
            groups.push((name, ty));
        }
        let Some(()) = self.expect(",") else {
            self.unwind(groups.len());
            return None;
        };
        let Some(body) = self.parse_type() else {
            self.unwind(groups.len());
            return None;
        };
        self.unwind(groups.len());
        let mut acc = body;
        for (name, ty) in groups.into_iter().rev() {
            acc = Sexp::List(vec![atom("Prod"), Sexp::Atom(name), ty, acc]);
        }
        Some(acc)
    }

    fn unwind(&mut self, n: usize) {
        for _ in 0..n {
            self.binders.pop();
        }
    }

    fn parse_arrow(&mut self) -> Option<Sexp> {
        let lhs = self.parse_app()?;
        if self.peek() != Some("->") {
            return Some(lhs);
        }
        self.pos += 1;
        self.binders.push("_".to_string());
        let rhs = self.parse_arrow();
        self.binders.pop();
        Some(Sexp::List(vec![atom("Prod"), atom("_"), lhs, rhs?]))
    }

    fn parse_app(&mut self) -> Option<Sexp> {
        let head = self.parse_atom()?;
        let mut args = Vec::new();
        while !matches!(self.peek(), None | Some(")" | "," | "->" | ":")) {
            args.push(self.parse_atom()?);
        }
        if args.is_empty() {
            return Some(head);
        }
        // Flatten a parenthesized-application head: `(f a) b` -> (App f a b).
        let mut items = match head {
            Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "App") => v,
            other => vec![atom("App"), other],
        };
        items.extend(args);
        Some(Sexp::List(items))
    }

    fn parse_atom(&mut self) -> Option<Sexp> {
        if self.peek() == Some("(") {
            self.pos += 1;
            let ty = self.parse_type()?;
            self.expect(")")?;
            return Some(ty);
        }
        let tok = self.bump()?;
        match tok {
            "Type" => {
                return Some(Sexp::List(vec![
                    atom("Sort"),
                    Sexp::List(vec![atom("Type"), atom("1")]),
                ]))
            }
            "Set" => return Some(Sexp::List(vec![atom("Sort"), atom("Set")])),
            "Prop" => return Some(Sexp::List(vec![atom("Sort"), atom("Prop")])),
            "_" => return None, // a hole the printer could not fill
            t if TERM_KEYWORDS.contains(&t) => return None,
            _ => {}
        }
        let name = tok.strip_prefix('@').unwrap_or(tok);
        if !is_path_atom(name) {
            return None;
        }
        let name = name.to_string();
        // Single-segment atoms: a binder in scope shadows every global.
        if !name.contains('.') {
            if let Some(d) = self.binders.iter().rev().position(|b| *b == name) {
                return Some(Sexp::List(vec![atom("Rel"), Sexp::Atom(d.to_string())]));
            }
        }
        match self.scope.resolve(&name)? {
            Resolved::Ind(n, i) => Some(Sexp::List(vec![
                atom("Ind"),
                Sexp::Atom(n),
                Sexp::Atom(i.to_string()),
            ])),
            Resolved::Ctor(n, i, j) => Some(Sexp::List(vec![
                atom("Construct"),
                Sexp::Atom(n),
                Sexp::Atom(i.to_string()),
                Sexp::Atom(j.to_string()),
            ])),
            Resolved::Const(n) => Some(Sexp::List(vec![atom("Const"), Sexp::Atom(n)])),
        }
    }
}

fn atom(s: &str) -> Sexp {
    Sexp::Atom(s.to_string())
}

/// The fully-qualified names a pretty-printed type MENTIONS, resolved through
/// `scope`, used only to DEFER reconstruction while a mentioned name is still
/// pending — never to build terms. DOT-LESS atoms are skipped: a top-level
/// fully-qualified query always pretty-prints globals with at least a module
/// segment (`fintype.Finite.class_of`), so a bare atom is a BINDER occurrence
/// — resolving those deadlocked the fixpoint (measured: `NumDomain.class_of`'s
/// `order_mixin` FIELD binder suffix-resolved to the pending
/// `Num.NumDomain.order_mixin` constant, whose own type defers on `class_of`
/// — a two-cycle that left the whole family stand-in).
pub fn referenced_names(text: &str, scope: &NameScope<'_>) -> Vec<String> {
    let mut out = Vec::new();
    for tok in tokenize_type(text) {
        let name = tok.strip_prefix('@').unwrap_or(&tok);
        if matches!(name, "Type" | "Set" | "Prop" | "_" | "->")
            || TERM_KEYWORDS.contains(&name)
            || !name.contains('.')
            || !is_path_atom(name)
        {
            continue;
        }
        let resolved = match scope.resolve(name) {
            Some(Resolved::Ind(n, _)) | Some(Resolved::Const(n)) => n,
            Some(Resolved::Ctor(n, _, _)) => n,
            None => continue,
        };
        if !out.contains(&resolved) {
            out.push(resolved);
        }
    }
    out
}

/// A pretty-printed atom that can denote a global reference: a dotted path
/// of identifier segments (`ssralg.GRing.Ring.type`), nothing else.
pub fn is_path_atom(atom: &str) -> bool {
    !atom.is_empty() && atom.split('.').all(is_ident)
}

/// Count the leading `Prod` binders of a dialect/serapi arity telescope and
/// check the codomain is a syntactic sort (what the checked `add_inductive`
/// replay requires of a type former).
pub fn arity_shape(arity: &Sexp) -> (u32, bool) {
    let mut cur = arity;
    let mut n = 0u32;
    loop {
        match cur {
            Sexp::List(v) if v.len() == 4 && matches!(&v[0], Sexp::Atom(h) if h == "Prod") => {
                n += 1;
                cur = &v[3];
            }
            _ => break,
        }
    }
    let is_sort =
        matches!(cur, Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Sort"));
    (n, is_sort)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp_io::sexp_to_string;

    fn index() -> DumpNameIndex {
        DumpNameIndex::from_entries(vec![
            (
                "mathcomp.ssreflect.choice.Choice.class_of",
                FormEntry::Ind(0),
            ),
            ("mathcomp.ssreflect.choice.Choice.base", FormEntry::Const),
            (
                "mathcomp.ssreflect.fintype.Finite.mixin_of",
                FormEntry::Ind(0),
            ),
            (
                "mathcomp.ssreflect.eqtype.Equality.Pack",
                FormEntry::Ctor {
                    block: "mathcomp.ssreflect.eqtype.Equality.type".to_string(),
                    block_idx: 0,
                    ctor_idx: 0,
                },
            ),
        ])
    }

    fn scope<'a>(file: &'a DumpNameIndex, run: &'a RunOverlay) -> NameScope<'a> {
        NameScope {
            file,
            run,
            self_ind: Some("mathcomp.ssreflect.fintype.Finite.class_of"),
        }
    }

    /// The measured `Check fintype.Finite.Class` text (Set Printing All +
    /// Set Printing Primitive Projection Parameters, live on the mathcomp
    /// 1.19 container) parses to the full importer-dialect constructor type:
    /// self-reference as `(Ind self 0)`, the `Equality.Pack` constructor as
    /// `(Construct <block> 0 0)`, the `Choice.base` projection as its compat
    /// `(Const ...)`, binders as 0-based `Rel`.
    #[test]
    fn test_parse_check_type_finite_class_ctor() {
        let text = "forall (T : Type) (base : choice.Choice.class_of T)\n         \
                    (_ : fintype.Finite.mixin_of\n                \
                    (@eqtype.Equality.Pack T (@choice.Choice.base T base))),\n       \
                    fintype.Finite.class_of T";
        let file = index();
        let run = RunOverlay::new();
        let got = parse_check_type(text, &scope(&file, &run)).expect("ctor type should parse");
        assert_eq!(
            sexp_to_string(&got),
            "(Prod T (Sort (Type 1)) \
             (Prod base (App (Ind mathcomp.ssreflect.choice.Choice.class_of 0) (Rel 0)) \
             (Prod _ (App (Ind mathcomp.ssreflect.fintype.Finite.mixin_of 0) \
             (App (Construct mathcomp.ssreflect.eqtype.Equality.type 0 0) (Rel 1) \
             (App (Const mathcomp.ssreflect.choice.Choice.base) (Rel 1) (Rel 0)))) \
             (App (Ind mathcomp.ssreflect.fintype.Finite.class_of 0) (Rel 2)))))"
        );
    }

    /// Arrow types and the bare (unparenthesized) forall group parse; the
    /// binder stack shadows globals of the same short name.
    #[test]
    fn test_parse_check_type_arrow_and_bare_group() {
        let file = index();
        let run = RunOverlay::new();
        let sc = scope(&file, &run);
        let got = parse_check_type("Type -> Prop", &sc).expect("arrow should parse");
        assert_eq!(sexp_to_string(&got), "(Prod _ (Sort (Type 1)) (Sort Prop))");
        let got = parse_check_type("forall T : Type, choice.Choice.class_of T", &sc)
            .expect("bare group should parse");
        assert_eq!(
            sexp_to_string(&got),
            "(Prod T (Sort (Type 1)) \
             (App (Ind mathcomp.ssreflect.choice.Choice.class_of 0) (Rel 0)))"
        );
    }

    /// Fail-closed set: holes, keywords, unresolved atoms, multi-name binder
    /// groups, and trailing garbage all yield `None`.
    #[test]
    fn test_parse_check_type_fails_closed() {
        let file = index();
        let run = RunOverlay::new();
        let sc = scope(&file, &run);
        for bad in [
            "forall (T : Type), foo _ T",        // hole in argument position
            "match x with end",                  // keyword
            "forall (T : Type), no.such.name T", // unresolved
            "forall (x y : Type), Prop",         // multi-name group (needs lift)
            "Type -> Prop extra",                // trailing tokens
            "",                                  // empty
        ] {
            assert_eq!(parse_check_type(bad, &sc), None, "must fail closed: {bad}");
        }
    }

    /// The run overlay overrides the file index per fully-qualified name
    /// (stale stand-in kind -> reconstructed inductive), and constructor
    /// entries resolve only through the scope (not the arity-rung resolve).
    #[test]
    fn test_name_scope_overlay_wins_and_ctor_resolution() {
        let file = DumpNameIndex::from_entries(vec![(
            "mathcomp.algebra.ssralg.GRing.Ring.class_of",
            FormEntry::Const,
        )]);
        let mut run = RunOverlay::new();
        run.insert(
            "mathcomp.algebra.ssralg.GRing.Ring.class_of".to_string(),
            FormEntry::Ind(0),
        );
        run.insert(
            "mathcomp.algebra.ssralg.GRing.Ring.Class".to_string(),
            FormEntry::Ctor {
                block: "mathcomp.algebra.ssralg.GRing.Ring.class_of".to_string(),
                block_idx: 0,
                ctor_idx: 0,
            },
        );
        let sc = NameScope {
            file: &file,
            run: &run,
            self_ind: None,
        };
        assert_eq!(
            sc.resolve("ssralg.GRing.Ring.class_of"),
            Some(Resolved::Ind(
                "mathcomp.algebra.ssralg.GRing.Ring.class_of".to_string(),
                0
            )),
            "overlay entry must override the stale file stand-in"
        );
        assert_eq!(
            sc.resolve("GRing.Ring.Class"),
            Some(Resolved::Ctor(
                "mathcomp.algebra.ssralg.GRing.Ring.class_of".to_string(),
                0,
                0
            ))
        );
        // The arity-rung resolve must NOT see constructor entries.
        assert_eq!(file.resolve("GRing.Ring.Class"), None);
    }

    /// The measured `Print fintype.Finite.class_of` text yields the record
    /// header: keyword, short name, 1 parameter, the `Class` constructor,
    /// and the primitive-projections marker.
    #[test]
    fn test_parse_print_inductive_record_header() {
        let text = "Record class_of (T : Type) : Type := Class\n  \
                    { base : choice.Choice.class_of T;\n    \
                    mixin : fintype.Finite.mixin_of\n              \
                    (eqtype.Equality.Pack (choice.Choice.base base)) }.\n\n\
                    class_of has primitive projections with eta conversion.\n\
                    Arguments fintype.Finite.class_of T%type_scope";
        let h = parse_print_inductive(text).expect("record header should parse");
        assert_eq!(h.keyword, "Record");
        assert_eq!(h.short_name, "class_of");
        assert_eq!(h.num_params, 1);
        assert_eq!(h.ctor_names, vec!["Class".to_string()]);
        assert!(h.prim_record);
    }

    /// Two-parameter record headers count every group; the `with eta
    /// conversion` prose inside the trailing text must not trip the mutual
    /// detector (it is beyond the terminating top-level dot).
    #[test]
    fn test_parse_print_inductive_two_param_record() {
        let text = "Record class_of (R : ssralg.GRing.Ring.type) (M : Type) : Type := Class\n  \
                    { base : ssralg.GRing.Lmodule.class_of R M }.\n\n\
                    class_of has primitive projections with eta conversion.";
        let h = parse_print_inductive(text).expect("two-param header should parse");
        assert_eq!(h.num_params, 2);
        assert_eq!(h.ctor_names, vec!["Class".to_string()]);
    }

    /// Variant alternatives split on top-level `|`; nested `|` inside
    /// parenthesized types must not create constructors.
    #[test]
    fn test_parse_print_inductive_variant_ctors() {
        let text = "Variant rat_spec (n d : ssrint.int) : Set :=\n    \
                    Qint : rat_spec n d\n  | Qnat (m : nat) : rat_spec n d\n  \
                    | Qneg : rat_spec n d.";
        let h = parse_print_inductive(text).expect("variant header should parse");
        assert_eq!(h.keyword, "Variant");
        assert_eq!(h.num_params, 2);
        assert_eq!(
            h.ctor_names,
            vec!["Qint".to_string(), "Qnat".to_string(), "Qneg".to_string()]
        );
        assert!(!h.prim_record);
    }

    /// Fail-closed: coinductives keep their statement-only semantics; mutual
    /// blocks need the family export path; non-inductive prints are not
    /// headers at all.
    #[test]
    fn test_parse_print_inductive_fails_closed() {
        assert_eq!(
            parse_print_inductive("CoInductive stream (A : Type) : Type := Cons"),
            None,
            "coinductive must stay axiomatized"
        );
        assert_eq!(
            parse_print_inductive(
                "Inductive tree : Set := Node : forest -> tree\n  with forest : Set := Leaf"
            ),
            None,
            "mutual blocks fail closed"
        );
        assert_eq!(parse_print_inductive("Notation x := GRing.Ring.type"), None);
        assert_eq!(parse_print_inductive(""), None);
    }

    /// `scan_form_line` records constructor entries with their block name and
    /// running index; `scan_buffer` aggregates lines.
    #[test]
    fn test_scan_form_line_records_ctors() {
        let mut forms = HashMap::new();
        scan_form_line(
            "(CoqInductive nat 0 (Sort Set) (NumParams 0) (Ctor O (Ind nat 0)) \
             (Ctor S (Prod n (Ind nat 0) (Ind nat 0))))",
            &mut forms,
        );
        scan_form_line("(CoqAxiom foo.bar (Sort Prop))", &mut forms);
        assert_eq!(forms.get("nat"), Some(&FormEntry::Ind(0)));
        assert_eq!(
            forms.get("O"),
            Some(&FormEntry::Ctor {
                block: "nat".to_string(),
                block_idx: 0,
                ctor_idx: 0
            })
        );
        assert_eq!(
            forms.get("S"),
            Some(&FormEntry::Ctor {
                block: "nat".to_string(),
                block_idx: 0,
                ctor_idx: 1
            })
        );
        assert_eq!(forms.get("foo.bar"), Some(&FormEntry::Const));
    }

    /// The arity-shape guard: leading Prod count and sort codomain.
    #[test]
    fn test_arity_shape_counts_prods_and_sort_codomain() {
        let file = index();
        let run = RunOverlay::new();
        let sc = scope(&file, &run);
        let arity = parse_check_type("Type -> Type", &sc).expect("arity parses");
        assert_eq!(arity_shape(&arity), (1, true));
        let non_sort =
            parse_check_type("forall T : Type, choice.Choice.class_of T", &sc).expect("parses");
        assert_eq!(arity_shape(&non_sort), (1, false));
    }
}
