// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured importer for F* `.fst` source files.
//!
//! F* surface declarations carry their type either in an explicit
//! `val <name> : <type>` signature (also `assume val <name> : <type>`) or
//! inline as `let <name> : <type> = …`. This importer scans the top-level
//! signatures in a module, parses each `type` string into a real structural
//! [`FlatExpr`] tree, and writes one shard per directory via
//! [`write_fstar_shard`]. It mirrors the Agda `.agda` importer
//! ([`crate::agda_source`]): every header is tagged `SourceSystem::FStar`,
//! `ImportConfidence::Unverified`, and `AXIOMATIZED`, with
//! `value_idx = NO_VALUE` because F* source carries no proof term we
//! reconstruct here.
//!
//! Like the Agda importer, this is a Level-0/1 **data import**, not a
//! verified elaboration. A signature whose type cannot be parsed into a
//! real tree is **skipped** — never replaced with a `FlatExpr::sort(0)`
//! placeholder (the `structured_importers_refuse_stubs` invariant).

use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// The kernel declaration kind an [`FStarDecl`] maps to.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum FStarDeclKind {
    /// A `val` / `let` / `assume` signature — imported as an assumed axiom
    /// (`DeclKind::Axiom`, no proof term). The default.
    #[default]
    Axiom,
    /// An inductive type former (`DeclKind::Inductive`) carrying its parameter
    /// count. Replayed through `add_inductive`; reduces to the foundational
    /// axioms when the kernel accepts it.
    Inductive { num_params: u32 },
    /// A constructor of the immediately-preceding inductive
    /// (`DeclKind::Constructor`).
    Constructor,
}

/// A top-level F* signature: `name : type_repr`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct FStarDecl {
    /// The declared name. The identifier token introduced by the
    /// `val` / `assume val` / `let` keyword.
    pub name: String,
    /// The raw type text following the top-level `:`, with continuation
    /// lines flattened to single spaces.
    pub type_repr: String,
    /// The kernel declaration kind (axiom by default; inductive/constructor for
    /// `type` definitions).
    pub kind: FStarDeclKind,
    /// The typed binder groups preceding the `:` (`(x:t) (y:u)`), empty for a
    /// `val` or a nullary definition. Used to build the lambda value.
    pub binders_repr: String,
    /// The definition body — the source after the top-level `=` (for a `let`)
    /// or the RHS (for a `type` abbreviation). `Some` ⇒ try to reconstruct a
    /// real `DeclKind::Definition` value (`λ binders. body`); `None` ⇒ axiom.
    pub value_repr: Option<String>,
}

/// Parse the top-level signatures of an F* source file.
///
/// What is handled:
///   * line comments (`// …`) and block comments (`(* … *)`, nestable),
///     replaced with whitespace so line/column structure is preserved,
///   * `val <name> : <type>` and `assume val <name> : <type>` declarations,
///   * `let <name> : <type> = …` declarations — only the annotated *type*
///     is taken (the value/proof term is discarded; `value_idx = NO_VALUE`),
///   * multi-line type signatures: a `val`/`let` whose type continues on
///     following indented lines (the type runs until a blank line, a line at
///     column ≤ the declaration's own column, the `=` of a `let` body, or an
///     obvious new top-level declaration).
///
/// What is skipped:
///   * `module` / `open` / `include` / `friend` lines,
///   * `#`-pragmas (`#set-options`, `#push-options`, …),
///   * `type` / `let rec` / `let f x = …` (no top-level type annotation),
///     and anything else not confidently a top-level annotated signature.
///
/// Be conservative: anything not confidently a top-level signature is
/// skipped. We never fabricate a declaration.
pub fn parse_fstar_file(content: &str, filename: &str) -> Vec<FStarDecl> {
    let logical = strip_comments(content);
    let lines: Vec<&str> = logical.lines().collect();
    // The module prefix qualifies every declared name (`FStar.List.Tot.length`)
    // so identically-named types/constructors across the 6,658-file corpus stay
    // globally unique — keeping inductive families from colliding when shards
    // merge, and giving the kernel re-verifier a one-to-one constructor↔family
    // association.
    let module_pref = module_prefix(&lines, filename);
    let mut decls = Vec::new();
    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        if line.trim().is_empty() {
            i += 1;
            continue;
        }
        let indent = leading_ws(line);
        let trimmed = line.trim_start();
        // `type` declarations: capture the type former (with its kind) and any
        // GADT constructors. Handled before the skippable-keyword check (which
        // covers `type`) so inductives and abbreviations are imported, not
        // dropped. The body spans constructor (`| C : …`) and indented
        // continuation lines.
        if split_type_head(trimmed).is_some() {
            let mut parts = vec![trimmed.to_owned()];
            let mut j = i + 1;
            while j < lines.len() {
                let cont = lines[j];
                if cont.trim().is_empty() {
                    break;
                }
                let cont_indent = leading_ws(cont);
                let ct = cont.trim_start();
                let is_ctor_bar = ct.starts_with('|');
                if !is_ctor_bar
                    && cont_indent <= indent
                    && (split_decl_head(ct).is_some()
                        || split_type_head(ct).is_some()
                        || is_skippable_line(ct))
                {
                    break;
                }
                parts.push(ct.to_owned());
                j += 1;
            }
            let text = normalize_ws(&parts.join(" "));
            decls.extend(parse_type_decl(&text, &module_pref));
            i = j;
            continue;
        }
        // Skip keyword / structural lines that are never plain signatures.
        if is_skippable_line(trimmed) {
            i += 1;
            continue;
        }
        // Recognise the declaration keyword and the identifier it introduces.
        let Some((name, after_name)) = split_decl_head(trimmed) else {
            i += 1;
            continue;
        };
        // Flatten the declaration across continuation lines: the binders and/or
        // the type may span several indented lines (both before and after the
        // `:`). Collect lines indented strictly more than this declaration,
        // stopping at a blank line or a new declaration — but while a bracket is
        // still open (`(`/`[`/`{` unbalanced), keep collecting regardless of
        // indentation, so a multi-line parenthesised type is not truncated.
        let mut flat = after_name.to_owned();
        let mut j = i + 1;
        while j < lines.len() {
            let cont = lines[j];
            if cont.trim().is_empty() {
                break;
            }
            let cont_trimmed = cont.trim_start();
            if bracket_balance(&flat) <= 0 {
                if leading_ws(cont) <= indent {
                    break;
                }
                if is_skippable_line(cont_trimmed) || starts_new_decl(cont_trimmed) {
                    break;
                }
            }
            flat.push(' ');
            flat.push_str(cont_trimmed);
            j += 1;
        }
        // The type-annotation `:` precedes the `let`-body `=` (if any). Search
        // for it only in the header (everything before the first top-level
        // `=`), so a `:` inside a `let`-body is never mistaken for the
        // annotation. No header colon ⇒ an unannotated `let f x = …` we skip.
        let header_end = find_top_level_eq(&flat).unwrap_or(flat.len());
        let header = &flat[..header_end];
        let Some(colon) = find_top_level_colon(header) else {
            i = j;
            continue;
        };
        let mut type_repr = normalize_ws(&header[colon + 1..]);
        // For a `let f (x:t) (y:u) : ret`, the *declared type* is the full
        // function type `(x:t) -> (y:u) -> ret`. Reconstruct it from the typed
        // binder groups between the name and the top-level `:` (otherwise the
        // binders are silently dropped, yielding an under-applied type). A
        // `val` has no such binders; an untyped binder leaves
        // `binders_are_typed` false, so the return type is used verbatim rather
        // than reconstructed wrongly.
        let binders = header[..colon].trim();
        let typed_binders = !binders.is_empty() && binders_are_typed(binders);
        if typed_binders {
            type_repr = normalize_ws(&format!("{binders} -> {type_repr}"));
        }
        // The `let`-body after the top-level `=` (if any). We keep it so
        // `write_fstar_shard` can try to reconstruct a real `DeclKind::Definition`
        // value (`λ binders. body`); an unparseable body falls back to an axiom.
        // Only reconstruct the lambda when binders are absent (nullary `let`) or
        // fully typed (so the lambda's binder types match the declared type).
        let value_repr = if header_end < flat.len() {
            let body = normalize_ws(&flat[header_end + 1..]);
            (!body.is_empty() && (binders.is_empty() || typed_binders)).then_some(body)
        } else {
            None
        };
        let binders_repr = if typed_binders {
            binders.to_owned()
        } else {
            String::new()
        };
        if !name.is_empty() && !type_repr.is_empty() {
            decls.push(FStarDecl {
                name: qualify(&module_pref, &name),
                type_repr,
                kind: FStarDeclKind::Axiom,
                binders_repr,
                value_repr,
            });
        }
        i = j;
    }
    decls
}

/// Write parsed F* declarations to a shard.
///
/// For each decl the `type_repr` string is parsed into a real `FlatExpr`
/// tree via [`parse_fstar_type`]. A decl whose type fails to parse is
/// **skipped** — never replaced with a `sort(0)` placeholder. This is the
/// import-time guarantee that the resulting shard satisfies
/// `expr_count > constant_count`.
///
/// Every header carries `value_idx = NO_VALUE` (F* source has no proof
/// term we reconstruct), `ImportConfidence::Unverified`, and `AXIOMATIZED`.
///
/// Returns the number of declarations actually written.
pub fn write_fstar_shard(decls: &[FStarDecl], writer: &mut ShardWriter) -> usize {
    let mut written = 0usize;
    for decl in decls {
        let Some(type_idx) = parse_fstar_type(&decl.type_repr, writer) else {
            // Parse failure: skip rather than fall back to sort(0).
            continue;
        };
        // A `let`/`type` definition carries a body: try to reconstruct a real
        // `λ binders. body` value so the re-verifier *checks* it (KernelVerified,
        // or bedrock when self-contained) instead of assuming it. An unparseable
        // body (`match`/`fun`/unmodelled) yields `None` ⇒ axiom fallback.
        let value_idx = decl
            .value_repr
            .as_deref()
            .and_then(|body| parse_fstar_lambda(&decl.binders_repr, body, writer));
        let name_idx = writer.add_string(&decl.name);
        // `type` definitions emit real `Inductive` / `Constructor` declarations
        // so the corpus re-verifier replays them through `add_inductive`; those
        // the kernel accepts become `KernelVerified` (closure ⊆ the foundational
        // axioms). A value-carrying `let`/`type` becomes a `DeclKind::Definition`
        // (the kernel checks the body against the type). `val`/`assume` and
        // unparseable-body `let`s remain assumed axioms. The shard tier stays
        // `Unverified`; the kernel re-verifier is the arbiter.
        let (decl_kind, axiom_profile) = if value_idx.is_some() {
            (DeclKind::Definition, AxiomProfile::NONE)
        } else {
            match decl.kind {
                FStarDeclKind::Axiom => (DeclKind::Axiom, AxiomProfile::AXIOMATIZED),
                FStarDeclKind::Inductive { .. } => (DeclKind::Inductive, AxiomProfile::NONE),
                FStarDeclKind::Constructor => (DeclKind::Constructor, AxiomProfile::NONE),
            }
        };
        let mut header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: value_idx.unwrap_or(NO_VALUE),
            source_system: SourceSystem::FStar as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        if let FStarDeclKind::Inductive { num_params } = decl.kind {
            header.set_inductive_decl_num_params(num_params);
        }
        writer.add_constant(header);
        written += 1;
    }
    written
}

/// Strip F* comments (line `// …`, nestable block `(* … *)`), replacing them
/// with whitespace so column/line structure is preserved. String literals
/// are respected so a `//` or `(*` inside a string is not treated as a
/// comment opener.
fn strip_comments(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let mut out = String::with_capacity(content.len());
    let mut i = 0usize;
    let mut block_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while i < chars.len() {
        let ch = chars[i];
        let next = chars.get(i + 1).copied();
        if block_depth > 0 {
            if ch == '(' && next == Some('*') {
                block_depth += 1;
                out.push(' ');
                out.push(' ');
                i += 2;
                continue;
            }
            if ch == '*' && next == Some(')') {
                block_depth -= 1;
                out.push(' ');
                out.push(' ');
                i += 2;
                continue;
            }
            out.push(if ch == '\n' { '\n' } else { ' ' });
            i += 1;
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
            i += 1;
            continue;
        }
        // Block comment start.
        if ch == '(' && next == Some('*') {
            block_depth = 1;
            out.push(' ');
            out.push(' ');
            i += 2;
            continue;
        }
        // Line comment.
        if ch == '/' && next == Some('/') {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
            continue;
        }
        if ch == '"' {
            in_string = true;
            out.push(ch);
            i += 1;
            continue;
        }
        out.push(ch);
        i += 1;
    }
    out
}

/// True for lines that are keywords / structural, never a plain signature.
fn is_skippable_line(trimmed: &str) -> bool {
    if let Some(rest) = trimmed.strip_prefix('#') {
        // F* pragma lines (`#set-options`, `#push-options`, `#restart-solver`,
        // …) are noise. But an implicit-binder *continuation* (`#a:Type`,
        // `#k2:parser_kind`) starts with `#` too and is part of a multi-line
        // signature — it must NOT be skipped or the signature is truncated.
        let word = rest
            .split(|c: char| c.is_whitespace() || c == ':')
            .next()
            .unwrap_or("");
        return word.ends_with("-options")
            || matches!(
                word,
                "restart-solver" | "light" | "print" | "reset" | "monadic" | "layered_effect"
            );
    }
    for kw in [
        "module",
        "open",
        "include",
        "friend",
        "type",
        "class",
        "instance",
        "effect",
        "new_effect",
        "sub_effect",
        "exception",
        "noeq",
        "unopteq",
        "irreducible",
    ] {
        if matches_keyword(trimmed, kw) {
            return true;
        }
    }
    false
}

/// True if a continuation line begins a new top-level declaration, ending the
/// current signature's type collection.
fn starts_new_decl(trimmed: &str) -> bool {
    split_decl_head(trimmed).is_some() || is_skippable_line(trimmed)
}

/// `kw` appears as a leading whole word (followed by whitespace or EOL).
fn matches_keyword(text: &str, kw: &str) -> bool {
    match text.strip_prefix(kw) {
        Some(rest) => rest.is_empty() || rest.starts_with(|c: char| c.is_whitespace()),
        None => false,
    }
}

/// Recognise a declaration head: an optional qualifier run, then `val` or
/// `let`, then the declared identifier. Returns `(name, rest_after_name)`
/// where `rest_after_name` is the slice following the identifier (expected to
/// begin, after whitespace, with the `:` type annotation).
///
/// Accepts `assume val f : t`, `val f : t`, `let f : t = …`, and the same
/// forms preceded by F* qualifiers such as `private`, `inline_for_extraction`,
/// `unfold`, `noextract`, `assume`. A bare `let f x = …` (no `:`) is not a
/// signature head we use; it will be rejected later by the missing top-level
/// `:` check, or its `x` will not be a valid colon position.
fn split_decl_head(trimmed: &str) -> Option<(String, &str)> {
    // Strip a run of leading qualifiers, then require `val` or `let`.
    let mut rest = trimmed;
    loop {
        let tok_end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let tok = &rest[..tok_end];
        match tok {
            "val" | "let" => {
                let after_kw = rest[tok_end..].trim_start();
                // For `let`, skip a `rec` qualifier.
                let after_kw = after_kw.strip_prefix("rec").map_or(after_kw, |r| {
                    if r.is_empty() || r.starts_with(char::is_whitespace) {
                        r.trim_start()
                    } else {
                        after_kw
                    }
                });
                // Operator definitions: `val ( +^ ) : …`, `let ( <=. ) …`.
                // The parenthesised symbolic name (pervasive in HACL*'s
                // `Lib.IntTypes`) is taken verbatim as the constant name.
                if let Some(inner_start) = after_kw.strip_prefix('(') {
                    if let Some(close) = inner_start.find(')') {
                        let opname = inner_start[..close].trim();
                        if is_operator_name(opname) {
                            return Some((opname.to_owned(), &inner_start[close + 1..]));
                        }
                    }
                }
                let id_end = after_kw
                    .find(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '#')
                    .unwrap_or(after_kw.len());
                let name = &after_kw[..id_end];
                if name.is_empty() || !is_valid_name(name) {
                    return None;
                }
                return Some((name.to_owned(), &after_kw[id_end..]));
            }
            // Recognised leading qualifiers that may precede `val`/`let`.
            "assume"
            | "private"
            | "abstract"
            | "noextract"
            | "unfold"
            | "inline"
            | "inline_for_extraction"
            | "irreducible"
            | "unobservable"
            | "total"
            | "logic"
            | "opaque" => {
                let next = rest[tok_end..].trim_start();
                if next.is_empty() || std::ptr::eq(next, rest) {
                    return None;
                }
                rest = next;
            }
            _ => return None,
        }
    }
}

/// Recognise a `type` declaration head: an optional qualifier run, then
/// `type`, then the declared type-former identifier. Returns `(name, rest)`
/// where `rest` is the slice after the identifier (binders, optional `: kind`,
/// optional `= body`).
fn split_type_head(trimmed: &str) -> Option<(String, &str)> {
    let mut rest = trimmed;
    loop {
        let tok_end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let tok = &rest[..tok_end];
        match tok {
            "type" => {
                let after = rest[tok_end..].trim_start();
                let id_end = after
                    .find(|c: char| c.is_whitespace() || matches!(c, ':' | '(' | '{' | '=' | '#'))
                    .unwrap_or(after.len());
                let name = &after[..id_end];
                if name.is_empty() || !is_valid_name(name) {
                    return None;
                }
                return Some((name.to_owned(), &after[id_end..]));
            }
            // Qualifiers that may precede `type`.
            "noeq"
            | "unopteq"
            | "private"
            | "abstract"
            | "noextract"
            | "inline_for_extraction"
            | "unfold"
            | "irreducible"
            | "logic"
            | "assume"
            | "new"
            | "erasable"
            | "must_erase_for_extraction" => {
                let next = rest[tok_end..].trim_start();
                if next.is_empty() || std::ptr::eq(next, rest) {
                    return None;
                }
                rest = next;
            }
            _ => return None,
        }
    }
}

/// Parse one flattened `type` declaration into the type former (with its
/// kind) plus any GADT / nullary constructors. `text` is the whole
/// declaration on a single logical line (`type Name binders [: kind] [= …]`).
///
/// The former's kind is `binders -> kind` when the binders are all typed and a
/// kind is given, else `binders -> Type`, else the explicit kind, else `Type`.
/// GADT constructors `| C : ty` are captured with their written type; bare
/// nullary `| C` constructors get the (parameter-erased) former type; OCaml
/// `| C of …` constructors are skipped (their argument types would be lost).
fn parse_type_decl(text: &str, module: &str) -> Vec<FStarDecl> {
    let mut out = Vec::new();
    let Some((name, rest)) = split_type_head(text) else {
        return out;
    };
    if !is_valid_name(&name) {
        return out;
    }
    // The module-qualified former name (`FStar.Pervasives.option`); constructor
    // return types reference it, so families stay globally unique on merge.
    let qual_former = qualify(module, &name);
    let (header, body) = match find_top_level_eq(rest) {
        Some(eq) => (rest[..eq].trim(), Some(rest[eq + 1..].trim())),
        None => (rest.trim(), None),
    };
    let (binders, kind) = match find_top_level_colon(header) {
        Some(c) => (header[..c].trim(), Some(header[c + 1..].trim())),
        None => (header, None),
    };
    let base_kind = kind.filter(|k| !k.is_empty()).unwrap_or("Type");
    // Typed parameters (if any) prefix both the inductive's arity and every
    // constructor type, in kernel form: `option : (a:Type) -> Type` and
    // `Some : (a:Type) -> a -> option a`.
    let typed_params = !binders.is_empty() && binders_are_typed(binders);
    let params = if typed_params { binders } else { "" };
    let pnames = if typed_params {
        param_names(binders)
    } else {
        Vec::new()
    };
    let former_ty = if typed_params {
        normalize_ws(&format!("{params} -> {base_kind}"))
    } else {
        base_kind.to_owned()
    };

    // Determine inductive-ness up front so the former is tagged correctly.
    let is_inductive =
        body.is_some_and(|b| b.trim_start().starts_with('|') || split_top_level_pipes(b).len() > 1);

    // A non-inductive `type t params = rhs` is a type abbreviation: carry the
    // RHS as a `DeclKind::Definition` value (`λ params. rhs`) so the re-verifier
    // checks it (KernelVerified, or bedrock when self-contained). Only when the
    // params are absent or fully typed (so the lambda binders match the kind).
    let abbrev_value = if !is_inductive && (binders.is_empty() || typed_params) {
        body.map(normalize_ws).filter(|b| !b.is_empty())
    } else {
        None
    };
    out.push(FStarDecl {
        name: qual_former.clone(),
        type_repr: former_ty,
        kind: if is_inductive {
            FStarDeclKind::Inductive {
                num_params: pnames.len() as u32,
            }
        } else {
            FStarDeclKind::Axiom
        },
        binders_repr: if abbrev_value.is_some() && typed_params {
            params.to_owned()
        } else {
            String::new()
        },
        value_repr: abbrev_value,
    });

    if is_inductive {
        let body = body.unwrap();
        let body = body.trim_start().strip_prefix('|').unwrap_or(body);
        // `FStar.Pervasives.option a` (the inductive applied to its parameters)
        // — the (qualified) return type of a nullary constructor.
        let applied = if pnames.is_empty() {
            qual_former.clone()
        } else {
            format!("{qual_former} {}", pnames.join(" "))
        };
        for seg in split_top_level_pipes(body) {
            let seg = seg.trim();
            if seg.is_empty() {
                continue;
            }
            let (cname, cty) = if let Some(c) = find_top_level_colon(seg) {
                // GADT constructor `C : ty`.
                (
                    seg[..c].split_whitespace().next().unwrap_or(""),
                    seg[c + 1..].trim().to_owned(),
                )
            } else {
                // Bare nullary constructor `| C` → result is the inductive.
                let mut toks = seg.split_whitespace();
                let cn = toks.next().unwrap_or("");
                if toks.next().is_some() {
                    // `C of …` (OCaml-style) — argument types lost; skip.
                    continue;
                }
                (cn, applied.clone())
            };
            if !is_valid_name(cname) || cty.is_empty() {
                continue;
            }
            // Qualify the inductive self-reference inside the constructor type
            // (`option a` → `FStar.Pervasives.option a`) so the re-verifier maps
            // the constructor to exactly this family, then prepend the params in
            // kernel form.
            let cty = replace_token(&cty, &name, &qual_former);
            let ctor_ty = if typed_params {
                normalize_ws(&format!("{params} -> {cty}"))
            } else {
                normalize_ws(&cty)
            };
            out.push(FStarDecl {
                name: qualify(module, cname),
                type_repr: ctor_ty,
                kind: FStarDeclKind::Constructor,
                ..Default::default()
            });
        }
    }
    out
}

/// Extract the (typed) binder names from an F* binder prefix like
/// `(a:Type) (n:nat)` or `(a b : Type)` → `["a","n"]` / `["a","b"]`. Leading
/// `#`/`$` qualifiers and `_` are dropped. Used to count inductive parameters
/// and to apply the inductive to them in nullary-constructor return types.
fn param_names(binders: &str) -> Vec<String> {
    let bytes: Vec<char> = binders.chars().collect();
    let mut names = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i];
        if c == '(' || c == '{' {
            let (open, close) = if c == '(' { ('(', ')') } else { ('{', '}') };
            let mut depth = 0i32;
            let mut j = i;
            let mut colon = None;
            while j < bytes.len() {
                let ch = bytes[j];
                if ch == open {
                    depth += 1;
                } else if ch == close {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                } else if ch == ':' && depth == 1 && colon.is_none() {
                    colon = Some(j);
                }
                j += 1;
            }
            if let Some(cp) = colon {
                let seg: String = bytes[i + 1..cp].iter().collect();
                for tok in seg.split_whitespace() {
                    let t = tok.trim_start_matches(['#', '$']);
                    if !t.is_empty() && t != "_" {
                        names.push(t.to_string());
                    }
                }
            }
            i = j + 1;
        } else {
            i += 1;
        }
    }
    names
}

/// Split `s` on depth-0 `|` separators (not `||`, and not inside brackets or
/// strings). Used to break an inductive body into constructor alternatives.
fn split_top_level_pipes(s: &str) -> Vec<&str> {
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut in_string = false;
    let mut escaped = false;
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
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' if depth > 0 => depth -= 1,
            '|' if depth == 0 => {
                let next = chars.get(i + 1).map(|(_, c)| *c);
                let prev = i.checked_sub(1).and_then(|p| chars.get(p)).map(|(_, c)| *c);
                if next != Some('|') && prev != Some('|') {
                    out.push(&s[start..idx]);
                    start = idx + 1; // `|` is one byte
                }
            }
            _ => {}
        }
        i += 1;
    }
    out.push(&s[start..]);
    out
}

/// A declared name must be a plausible F* identifier (alnum / `_` / `'` /
/// qualified `.`), not lone punctuation.
fn is_valid_name(tok: &str) -> bool {
    if tok.is_empty() {
        return false;
    }
    tok.chars()
        .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.'))
        && tok.chars().any(|c| c.is_alphanumeric() || c == '_')
}

/// A parenthesised operator name like `+^`, `<=.`, `|>`, `=` (the symbolic
/// definitions `let ( +^ ) …` / `val ( = ) …`). Distinguished from a binder
/// pattern `(x:t)` (which carries a `:` and alphanumerics) so the latter is
/// not mistaken for a declaration name.
fn is_operator_name(inner: &str) -> bool {
    if inner.is_empty() || inner.contains(':') {
        return false;
    }
    let is_op = |c: char| is_op_char(c) || c == '|';
    inner.chars().all(|c| is_op(c) || c.is_whitespace()) && inner.chars().any(is_op)
}

/// Find the first top-level `:` (depth-0, not `::`, not `:=`) in `text`.
fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut bracket = 0i32;
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
                let prev = i.checked_sub(1).and_then(|p| chars.get(p)).map(|(_, c)| *c);
                if next != Some('=') && next != Some(':') && prev != Some(':') {
                    return Some(idx);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Find the first top-level `=` (depth-0, not `==`, not `=>`, not `>=`/`<=`/
/// `:=`) that begins a `let` body. Used to truncate a `let f : t = body`
/// type at the body boundary.
fn find_top_level_eq(text: &str) -> Option<usize> {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut bracket = 0i32;
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
            '=' if paren == 0 && brace == 0 && bracket == 0 => {
                let next = chars.get(i + 1).map(|(_, c)| *c);
                let prev = i.checked_sub(1).and_then(|p| chars.get(p)).map(|(_, c)| *c);
                // A standalone `=` (assignment), not `==`, `=>`, `<=`, `>=`,
                // or `:=`.
                if next != Some('=')
                    && next != Some('>')
                    && prev != Some('=')
                    && prev != Some('<')
                    && prev != Some('>')
                    && prev != Some(':')
                {
                    return Some(idx);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn leading_ws(line: &str) -> usize {
    line.chars().take_while(|c| c.is_whitespace()).count()
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Prepend the module prefix to a declared name (`length` →
/// `FStar.List.Tot.Base.length`). An empty module leaves the name unchanged.
fn qualify(module: &str, name: &str) -> String {
    if module.is_empty() {
        name.to_owned()
    } else {
        format!("{module}.{name}")
    }
}

/// The F* module prefix for a file: the first top-level `module A.B.C`
/// declaration (NOT a `module M = A.B` abbreviation), else the dotted filename
/// stem (F* requires the filename to match the module name).
fn module_prefix(lines: &[&str], filename: &str) -> String {
    for line in lines {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("module") {
            if rest.starts_with(char::is_whitespace) {
                let rest = rest.trim();
                if !rest.contains('=') {
                    if let Some(first) = rest.split_whitespace().next() {
                        if first.chars().next().is_some_and(char::is_uppercase) {
                            return first.to_owned();
                        }
                    }
                }
            }
        }
    }
    let base = filename.rsplit(['/', '\\']).next().unwrap_or(filename);
    base.strip_suffix(".fsti")
        .or_else(|| base.strip_suffix(".fst"))
        .unwrap_or(base)
        .to_owned()
}

/// Replace whole-token occurrences of `from` with `to` in `s` (a token is
/// bounded by non-identifier characters — alnum / `_` / `'` / `.`). Used to
/// qualify an inductive's self-reference inside its constructor types without
/// touching other identifiers that merely contain it as a substring.
fn replace_token(s: &str, from: &str, to: &str) -> String {
    if from.is_empty() {
        return s.to_owned();
    }
    let chars: Vec<char> = s.chars().collect();
    let pat: Vec<char> = from.chars().collect();
    let is_id = |c: char| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.');
    let mut out = String::with_capacity(s.len());
    let mut i = 0usize;
    while i < chars.len() {
        if i + pat.len() <= chars.len() && chars[i..i + pat.len()] == pat[..] {
            let before_ok = i == 0 || !is_id(chars[i - 1]);
            let after = i + pat.len();
            let after_ok = after >= chars.len() || !is_id(chars[after]);
            if before_ok && after_ok {
                out.push_str(to);
                i = after;
                continue;
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

/// Net bracket depth of `text`: `(` / `[` / `{` count `+1`, their closers
/// `-1` (string-literal contents skipped). `> 0` means a bracket is still open,
/// so a multi-line declaration continues onto the next line.
fn bracket_balance(text: &str) -> i32 {
    let mut depth = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    for c in text.chars() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// True iff `binders` is a whitespace-separated run of *typed* binder groups —
/// each a balanced `(...)` / `{...}` (optionally `#`-prefixed) carrying a
/// top-level `:`. Only then can `let f (x:t) (y:u) : ret` be faithfully
/// reconstructed as `(x:t) -> (y:u) -> ret`; a bare/untyped binder
/// (`let f x : t`, `let f #a (x:a) : t`) is not reconstructible, so we decline
/// and keep the return type verbatim rather than synthesise a wrong type.
fn binders_are_typed(binders: &str) -> bool {
    let chars: Vec<char> = binders.chars().collect();
    let mut i = 0usize;
    let mut saw_group = false;
    while i < chars.len() {
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }
        // An optional leading `#` (explicit-implicit binder) must still be
        // followed by a bracketed, typed group — a bare `#a` is untyped.
        if chars[i] == '#' {
            i += 1;
        }
        let (open, close) = match chars.get(i) {
            Some('(') => ('(', ')'),
            Some('{') => ('{', '}'),
            _ => return false, // a bare token: untyped binder, not reconstructible
        };
        let mut depth = 0i32;
        let mut has_colon = false;
        let mut closed = false;
        while i < chars.len() {
            let c = chars[i];
            if c == open {
                depth += 1;
            } else if c == close {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    closed = true;
                    break;
                }
            } else if depth == 1 && c == ':' {
                has_colon = true;
            }
            i += 1;
        }
        if !closed || !has_colon {
            return false;
        }
        saw_group = true;
    }
    saw_group
}

// ---------------------------------------------------------------------------
// F* type-expression parser → FlatExpr tree.
//
// A recursive-descent parser over a token stream producing Pi / Const / App /
// BVar / Sort nodes. It now covers the surface constructs that dominate the
// F* / Project-Everest corpus (HACL*, KaRaMeL, EverParse, Vale, AlgoStar):
//
//   * refinement types `x:t{φ}`, `t{φ}`, and set-builder `{x:t | φ}` — the
//     refinement predicate `φ` is a documented *surface erasure*: a refined
//     value is a value of its base type `t`, so we keep the real structural
//     `t` and drop the proposition (the same stance the file already takes for
//     universe levels), never a `sort(0)` stub,
//   * dependent function types with **bare** binders `x:t -> u` and implicit
//     `#x:t -> u`, alongside the parenthesised `(x:t) -> u` / `{a:t} -> u`
//     forms, and multi-binder runs `(a:Type) (x:a) -> u`,
//   * computation / effect result types — `Tot t`, `GTot t`, `Pure t _ _`,
//     `ST t _ _`, `Stack t _ _`, `Ghost t`, `Div t`, `ML t`, `Steel t …`, …
//     erase to their value type `t`; `Lemma …` erases to `unit` — the
//     WP / pre / post / `decreases` / `SMTPat` arguments are dropped,
//   * tuple / product types `t1 & t2` and `t1 * t2`,
//   * `'a` / `'b` prime-prefixed type variables and `Type u#n` universes.
//
// It stays conservative: anything it cannot model faithfully makes it return
// `None`, and the caller skips the declaration (never a `sort(0)` stub).
// ---------------------------------------------------------------------------

use clean_kernel::flat::FlatExpr;

const NO_LEVELS: u32 = u32::MAX;
const BINDER_DEFAULT: u8 = 0;
const BINDER_IMPLICIT: u8 = 1;

/// A computation-type head's value-type discipline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompKind {
    /// Result type is the first type argument (`Tot t`, `ST t _ _`, …).
    FirstArg,
    /// Result type is `unit` (`Lemma (requires …) (ensures …)`).
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Nat(u64),
    LParen,
    RParen,
    LBrace, // implicit binder `{x:t}` or set-builder refinement `{x:t|φ}`
    RBrace,
    LBracket, // `[` — SMTPat / list-literal brackets (balanced-skipped)
    RBracket, // `]`
    Arrow,
    Comma,
    Colon,
    Hash,       // `#` — implicit-binder / implicit-argument marker
    Pipe,       // `|` — set-builder refinement separator / inductive bar
    Op(String), // any other operator-character run (`*`, `&`, `==>`, `<`, …)
    Kw(String), // a reserved term keyword (`fun`, `match`, `let`, …): invalid
    // in atom position, but balanced-skippable inside an effect
    // spec / refinement (`requires (fun h -> …)`)
    Forall, // `forall` or `∀`
    Underscore,
}

/// Classify an F* computation-type head. `None` means "not an effect".
fn effect_kind(name: &str) -> Option<CompKind> {
    // Effects are often written qualified (`T.Tac`, `FStar.HyperStack.ST.Stack`);
    // classify on the final dotted component.
    let base = name.rsplit('.').next().unwrap_or(name);
    match base {
        "Lemma" => Some(CompKind::Unit),
        "Tot" | "GTot" | "Ghost" | "GhostST" | "Pure" | "PURE" | "Div" | "DIV" | "Dv" | "ML"
        | "All" | "ALL" | "Ex" | "EXN" | "Exn" | "ST" | "St" | "STATE" | "State" | "Stack"
        | "StackInline" | "Heap" | "HEAP" | "Steel" | "SteelT" | "STT" | "STTtot" | "STAtomic"
        | "Tac" | "TacH" | "TacS" | "TacRO" | "Dv'" | "HoareST" | "HoareSTNS" | "stt"
        | "stt_atomic" | "stt_ghost" | "stt_unobservable" | "STGhost" | "STGhostT"
        | "STAtomicBase" | "STAtomicT" => Some(CompKind::FirstArg),
        _ => None,
    }
}

fn lex(src: &str) -> Vec<Tok> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        // Arrows: ASCII `->` and Unicode `→`.
        if ch == '-' && chars.get(i + 1) == Some(&'>') {
            out.push(Tok::Arrow);
            i += 2;
            continue;
        }
        if ch == '\u{2192}' {
            // →
            out.push(Tok::Arrow);
            i += 1;
            continue;
        }
        // `:=` is not valid in a type expr — stop defensively.
        if ch == ':' && chars.get(i + 1) == Some(&'=') {
            break;
        }
        // `::` (list cons) is an infix operator, not two annotation colons.
        if ch == ':' && chars.get(i + 1) == Some(&':') {
            out.push(Tok::Op("::".into()));
            i += 2;
            continue;
        }
        match ch {
            '(' => {
                out.push(Tok::LParen);
                i += 1;
                continue;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
                continue;
            }
            '{' => {
                out.push(Tok::LBrace);
                i += 1;
                continue;
            }
            '}' => {
                out.push(Tok::RBrace);
                i += 1;
                continue;
            }
            '[' => {
                out.push(Tok::LBracket);
                i += 1;
                continue;
            }
            ']' => {
                out.push(Tok::RBracket);
                i += 1;
                continue;
            }
            ',' => {
                out.push(Tok::Comma);
                i += 1;
                continue;
            }
            ':' => {
                out.push(Tok::Colon);
                i += 1;
                continue;
            }
            // `#` (implicit) and `$` (strict-implicit / equational) are both
            // binder-qualifier prefixes; model both as `Hash`.
            '#' | '$' => {
                out.push(Tok::Hash);
                i += 1;
                continue;
            }
            '|' => {
                // A single `|` is the set-builder refinement separator (and the
                // inductive bar). A longer run (`||`) is an ordinary operator.
                if chars.get(i + 1) == Some(&'|') {
                    out.push(Tok::Op("||".into()));
                    i += 2;
                } else {
                    out.push(Tok::Pipe);
                    i += 1;
                }
                continue;
            }
            '\u{2200}' => {
                // ∀
                out.push(Tok::Forall);
                i += 1;
                continue;
            }
            _ => {}
        }
        if ch.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let s: String = chars[start..i].iter().collect();
            match s.parse::<u64>() {
                Ok(n) => out.push(Tok::Nat(n)),
                Err(_) => return out, // overflow: bail, caller skips
            }
            continue;
        }
        // `λ` introduces a lambda abstraction — a *term*, not a type former.
        // Bail so the caller skips (the unparsed remainder fails the
        // fully-consumed check). `\` is an operator char (`\/`), handled below.
        if ch == '\u{3bb}' {
            return out;
        }
        if is_ident_start(ch) {
            let start = i;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let id: String = chars[start..i].iter().collect();
            // Reserved F* term keywords. They cannot head a plain type
            // expression (the parser rejects a `Kw` in atom position), but they
            // appear inside effect specs and refinements we balanced-skip
            // (`requires (fun h -> …)`, `{x | match … with …}`). Emitting a
            // `Kw` token — rather than bailing the whole lex — keeps the stream
            // complete so those regions can be skipped.
            if matches!(
                id.as_str(),
                "let"
                    | "in"
                    | "match"
                    | "with"
                    | "fun"
                    | "if"
                    | "then"
                    | "else"
                    | "begin"
                    | "end"
                    | "rec"
                    | "and"
                    | "type"
            ) {
                out.push(Tok::Kw(id));
                continue;
            }
            // `Type`, `Type0`, … optionally carry a universe annotation
            // `u#n` / `u#a` / `u#(max a b)`. Fold the annotation into the sort
            // atom so `Type u#0` lexes as a single `Type` identifier.
            if is_sort_atom(&id) {
                let mut k = i;
                while k < chars.len() && chars[k].is_whitespace() {
                    k += 1;
                }
                if chars.get(k) == Some(&'u') && chars.get(k + 1) == Some(&'#') {
                    k += 2;
                    if chars.get(k) == Some(&'(') {
                        let mut depth = 0i32;
                        while k < chars.len() {
                            match chars[k] {
                                '(' => depth += 1,
                                ')' => {
                                    depth -= 1;
                                    k += 1;
                                    if depth == 0 {
                                        break;
                                    }
                                    continue;
                                }
                                _ => {}
                            }
                            k += 1;
                        }
                    } else {
                        while k < chars.len()
                            && (chars[k].is_alphanumeric() || matches!(chars[k], '_' | '\'' | '+'))
                        {
                            k += 1;
                        }
                    }
                    i = k;
                }
                out.push(Tok::Ident(id));
                continue;
            }
            if id == "forall" {
                out.push(Tok::Forall);
            } else if id == "_" {
                out.push(Tok::Underscore);
            } else {
                out.push(Tok::Ident(id));
            }
            continue;
        }
        // Any other run of operator characters (`*`, `&`, `==>`, `/\`, `<=`,
        // `+`, `~`, …). Tokenising rather than bailing keeps the stream
        // complete so refinement predicates and effect specs can be
        // balanced-skipped. Stop before a `-` that begins an arrow.
        if is_op_char(ch) {
            let start = i;
            while i < chars.len() && is_op_char(chars[i]) {
                if chars[i] == '-' && chars.get(i + 1) == Some(&'>') {
                    break;
                }
                i += 1;
            }
            if i == start {
                out.push(Tok::Op(chars[start].to_string()));
                i += 1;
            } else {
                out.push(Tok::Op(chars[start..i].iter().collect()));
            }
            continue;
        }
        // An unknown, non-operator glyph we cannot classify. Return what we
        // have; the incomplete structure fails the fully-consumed check.
        return out;
    }
    out
}

/// Operator characters that form an [`Tok::Op`] run. Excludes the structural
/// glyphs handled above (`( ) { } [ ] , : # $ |`) and the arrow `->` / `→`.
/// Includes the backtick so F*'s backtick-infix `a `op` b` tokenises rather
/// than bailing the lex.
fn is_op_char(ch: char) -> bool {
    matches!(
        ch,
        '+' | '-'
            | '*'
            | '/'
            | '%'
            | '<'
            | '>'
            | '='
            | '~'
            | '!'
            | '?'
            | '^'
            | '&'
            | '@'
            | '\\'
            | '.'
            | '`'
    )
}

/// F* identifiers begin with a letter, `_`, or `'` (the prime-prefixed type
/// variables `'a`, `'b`, … that pervade the corpus).
fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_' || ch == '\''
}

/// F* identifiers accept alphanumerics, `_`, `'`, and `.` (qualified names).
fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '.')
}

/// Recognise an F* sort atom: `Type`, `Type0`, `Type u#n`, `prop`, `Prop`.
/// `Type` with an explicit-universe suffix like `Type0` is still a sort.
/// Anything else (e.g. `Tot`, `Property`) is a user constant, not a sort.
fn is_sort_atom(name: &str) -> bool {
    if name == "prop" || name == "Prop" || name == "logical" {
        return true;
    }
    match name.strip_prefix("Type") {
        Some(rest) => rest.is_empty() || rest.chars().all(|c| c.is_ascii_digit()),
        None => false,
    }
}

struct Parser<'w> {
    toks: Vec<Tok>,
    pos: usize,
    writer: &'w mut ShardWriter,
    bound: Vec<String>,
    expr_budget: u32,
}

impl<'w> Parser<'w> {
    fn new(toks: Vec<Tok>, writer: &'w mut ShardWriter) -> Self {
        Self {
            toks,
            pos: 0,
            writer,
            bound: Vec::new(),
            expr_budget: 4096,
        }
    }
    /// Like [`Parser::new`] but with a pre-seeded binder scope, so a definition
    /// body parses with its lambda binders already in scope (de-Bruijn resolved
    /// against `bound`).
    fn with_bound(toks: Vec<Tok>, writer: &'w mut ShardWriter, bound: Vec<String>) -> Self {
        Self {
            toks,
            pos: 0,
            writer,
            bound,
            expr_budget: 4096,
        }
    }
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos + n)
    }
    /// A parenthesised argument we drop rather than parse: a computation spec
    /// `( requires … )` / `( ensures … )` / `( decreases … )` / `( modifies … )`
    /// (lets *any* effect survive `fun`-bodied specs), or a `( fun … )` lambda
    /// argument (a type family / WP we keep only structurally).
    fn peek_is_spec_paren(&self) -> bool {
        if !matches!(self.peek(), Some(Tok::LParen)) {
            return false;
        }
        match self.peek_at(1) {
            Some(Tok::Ident(s)) => matches!(
                s.rsplit('.').next().unwrap_or(s),
                "requires" | "ensures" | "decreases" | "modifies"
            ),
            Some(Tok::Kw(k)) => k == "fun",
            _ => false,
        }
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned()?;
        self.pos += 1;
        Some(t)
    }
    fn eat(&mut self, want: &Tok) -> bool {
        if self.peek() == Some(want) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn add(&mut self, e: FlatExpr) -> Option<u32> {
        if self.expr_budget == 0 {
            return None;
        }
        self.expr_budget -= 1;
        Some(self.writer.add_expr(e))
    }

    /// `Prop = Sort 0` — universe level `zero`, pre-seeded at level index 0.
    fn sort_prop(&mut self) -> Option<u32> {
        self.add(FlatExpr::sort(0))
    }

    /// `Type0 = Sort (succ zero)` — register the `succ(zero)` universe level
    /// (deduped) and reference it, so the sort is valid in the shard's level
    /// table. A bare `sort(1)` would index a level that was never registered
    /// (the writer seeds only `zero` at index 0), corrupting the shard.
    fn sort_type(&mut self) -> Option<u32> {
        let succ = clean_kernel::flat::FlatLevel::succ(0);
        let lvl = self.writer.add_level(succ);
        self.add(FlatExpr::sort(lvl))
    }

    fn parse_type(&mut self) -> Option<u32> {
        if matches!(self.peek(), Some(Tok::Forall)) {
            self.bump();
            return self.parse_forall_chain();
        }
        // A type-level `let [open] … in body` (Pulse / module-local
        // definitions): the type *is* the body — skip the bindings up to the
        // matching `in` (nested `let`/`in` balanced) and parse the body.
        if matches!(self.peek(), Some(Tok::Kw(k)) if k == "let") {
            self.bump();
            let mut depth = 1i32;
            while let Some(t) = self.peek() {
                match t {
                    Tok::Kw(k) if k == "let" => depth += 1,
                    Tok::Kw(k) if k == "in" => {
                        depth -= 1;
                        self.bump();
                        if depth == 0 {
                            break;
                        }
                        continue;
                    }
                    _ => {}
                }
                self.bump();
            }
            return self.parse_type();
        }
        // A computation-type head (`Tot t`, `Lemma …`, `ST t _ _`, …) erases
        // to its value type.
        let eff = match self.peek() {
            Some(Tok::Ident(name)) => effect_kind(name),
            _ => None,
        };
        if let Some(kind) = eff {
            self.bump();
            return self.parse_computation(kind);
        }
        self.parse_arrow()
    }

    /// After `forall`/`∀`, parse one or more binder groups followed by a
    /// `.` (consumed by the lexer into the qualified-name machinery is not a
    /// concern here) — F* separates the binders from the body with `.`. We
    /// accept either a `,` or `→`/`->` separator the way Agda does, plus the
    /// F* `.` which the lexer folds into identifiers; to keep this robust we
    /// accept a `Comma` or `Arrow` separator only and otherwise bail.
    fn parse_forall_chain(&mut self) -> Option<u32> {
        let mut binders: Vec<(u8, u32)> = Vec::new();
        let mut pushed = 0usize;
        loop {
            if matches!(self.peek(), Some(Tok::Comma) | Some(Tok::Arrow)) {
                self.bump();
                break;
            }
            if self.peek().is_none() {
                self.unwind(pushed);
                return None;
            }
            let group = match self.parse_binder_group() {
                Some(g) => g,
                None => {
                    self.unwind(pushed);
                    return None;
                }
            };
            for (name, binfo, ty_idx) in group {
                self.bound.push(name);
                pushed += 1;
                binders.push((binfo, ty_idx));
            }
        }
        let body = match self.parse_type() {
            Some(b) => b,
            None => {
                self.unwind(pushed);
                return None;
            }
        };
        let mut acc = body;
        for (binfo, ty_idx) in binders.iter().rev() {
            acc = self.add(FlatExpr::pi(*binfo, *ty_idx, acc))?;
        }
        self.unwind(pushed);
        Some(acc)
    }

    fn unwind(&mut self, n: usize) {
        for _ in 0..n {
            self.bound.pop();
        }
    }

    /// Parse one binder group: `(x y : T)` or `{x : T}`. An untyped binder
    /// has no annotation to reconstruct faithfully, so we bail rather than
    /// fabricate a placeholder type.
    fn parse_binder_group(&mut self) -> Option<Vec<(String, u8, u32)>> {
        let (close, mut binfo) = match self.peek() {
            Some(Tok::LParen) => (Tok::RParen, BINDER_DEFAULT),
            Some(Tok::LBrace) => (Tok::RBrace, BINDER_IMPLICIT),
            _ => return None,
        };
        self.bump(); // opening bracket

        // Typeclass binder `{| [name :] C t |}` (closed by `|}`). The instance
        // is usually anonymous (`{| ord a |}`), so a binder name is optional.
        if close == Tok::RBrace && matches!(self.peek(), Some(Tok::Pipe)) {
            self.bump(); // leading `|`
            let name = if matches!(self.peek(), Some(Tok::Ident(_)) | Some(Tok::Underscore))
                && matches!(self.peek_at(1), Some(Tok::Colon))
            {
                let n = self.expect_ident()?;
                self.bump(); // `:`
                n
            } else {
                "_".to_string()
            };
            let ty = self.parse_type()?;
            if !self.eat(&Tok::Pipe) || !self.eat(&Tok::RBrace) {
                return None;
            }
            return Some(vec![(name, BINDER_IMPLICIT, ty)]);
        }

        // An explicit-implicit binder `(#x : T)` / `($x : T)`.
        if matches!(self.peek(), Some(Tok::Hash)) {
            self.bump();
            binfo = BINDER_IMPLICIT;
        }
        // A binder attribute `(#[@@@ refine] u : T)` / `([@@ ...] x : T)`.
        while matches!(self.peek(), Some(Tok::LBracket)) {
            self.skip_balanced(&Tok::LBracket, &Tok::RBracket);
        }
        // Names: ordinary `x y`, or a tuple/record *pattern* `(x, y)` whose
        // shape we drop and bind anonymously (its type annotation is real).
        let mut names = Vec::new();
        if matches!(self.peek(), Some(Tok::LParen)) {
            self.skip_balanced(&Tok::LParen, &Tok::RParen);
            names.push("_".to_string());
        } else {
            while matches!(self.peek(), Some(Tok::Ident(_)) | Some(Tok::Underscore)) {
                names.push(self.expect_ident()?);
            }
        }
        if names.is_empty() {
            return None;
        }
        let ty = if matches!(self.peek(), Some(Tok::Colon)) {
            self.bump();
            self.parse_type()?
        } else {
            // Untyped binder: no annotation to reconstruct. Bail rather than
            // emit a placeholder type.
            return None;
        };
        if !self.eat(&close) {
            return None;
        }
        Some(names.into_iter().map(|n| (n, binfo, ty)).collect())
    }

    fn expect_ident(&mut self) -> Option<String> {
        match self.bump()? {
            Tok::Ident(s) => Some(s),
            Tok::Underscore => Some("_".into()),
            _ => None,
        }
    }

    /// `arrow := binder_groups -> | bare_binder -> | product (-> type)?`.
    /// Handles parenthesised/implicit binder runs `(a:Type) (x:a) -> u`, bare
    /// dependent binders `x:t -> u` / `#x:t -> u`, and the non-dependent
    /// product `t -> u` (right-associative).
    fn parse_arrow(&mut self) -> Option<u32> {
        if self.looks_like_binder_group() {
            return self.parse_binder_group_arrow();
        }
        if self.looks_like_bare_binder() {
            return self.parse_bare_binder_arrow();
        }
        let lhs = self.parse_product()?;
        if !self.eat(&Tok::Arrow) {
            return Some(lhs);
        }
        // `A → B` ≡ `(_ : A) → B`. Push an anonymous binder so de Bruijn
        // indices in `B` account for the new binding level.
        self.bound.push("_".into());
        let rhs = self.parse_type();
        self.bound.pop();
        let rhs = rhs?;
        self.add(FlatExpr::pi(BINDER_DEFAULT, lhs, rhs))
    }

    /// Parse a run of consecutive parenthesised/implicit binder groups, then
    /// `->` and the codomain: `(a:Type) (x:a) {y:b} -> body`. Names are pushed
    /// as they bind so later groups' types resolve dependent references.
    fn parse_binder_group_arrow(&mut self) -> Option<u32> {
        let mut binders: Vec<(u8, u32)> = Vec::new();
        let mut pushed = 0usize;
        while self.looks_like_binder_group() {
            let group = match self.parse_binder_group() {
                Some(g) => g,
                None => {
                    self.unwind(pushed);
                    return None;
                }
            };
            for (name, binfo, ty) in group {
                self.bound.push(name);
                pushed += 1;
                binders.push((binfo, ty));
            }
        }
        if !self.eat(&Tok::Arrow) {
            self.unwind(pushed);
            // A standalone parenthesised refinement type `(x:t{φ})` (no `->`):
            // its type is the (first) binder's base type. (The binder type was
            // parsed in the outer scope, so it carries no dangling de-Bruijn.)
            return binders.first().map(|(_, ty)| *ty);
        }
        let body = self.parse_type();
        self.unwind(pushed);
        let body = body?;
        let mut acc = body;
        for (binfo, ty) in binders.iter().rev() {
            acc = self.add(FlatExpr::pi(*binfo, *ty, acc))?;
        }
        Some(acc)
    }

    /// Lookahead: an unparenthesised dependent binder `x : t` or `#x : t`,
    /// distinguished from `x == y` (no colon) and from plain application.
    fn looks_like_bare_binder(&self) -> bool {
        match self.peek() {
            Some(Tok::Hash) => {
                // `#x : t`, or `#[@@@ …] x : t` (attribute before the name).
                matches!(self.peek_at(1), Some(Tok::LBracket))
                    || (matches!(self.peek_at(1), Some(Tok::Ident(_)) | Some(Tok::Underscore))
                        && matches!(self.peek_at(2), Some(Tok::Colon)))
            }
            Some(Tok::Ident(_)) | Some(Tok::Underscore) => {
                matches!(self.peek_at(1), Some(Tok::Colon))
            }
            _ => false,
        }
    }

    /// Parse a bare dependent binder. With a trailing `->` it is a dependent
    /// function type `x:t -> body`; without, it is a standalone refinement
    /// type `x:t{φ}` whose base type `t` we keep (predicate erased).
    fn parse_bare_binder_arrow(&mut self) -> Option<u32> {
        let mut binfo = BINDER_DEFAULT;
        if matches!(self.peek(), Some(Tok::Hash)) {
            self.bump();
            binfo = BINDER_IMPLICIT;
        }
        // An attribute before the binder name: `#[@@@ unrefine] a : t`.
        while matches!(self.peek(), Some(Tok::LBracket)) {
            self.skip_balanced(&Tok::LBracket, &Tok::RBracket);
        }
        let name = self.expect_ident()?;
        if !self.eat(&Tok::Colon) {
            return None;
        }
        // Parse the binder's type at *application* level (not product), so a
        // top-level `&` is recognised as a dependent-sum separator rather than
        // being eaten as a tuple — `x:a & y:b` is a dependent sum, not
        // `x:(a & b)`.
        let ty = self.parse_app()?;
        if self.eat(&Tok::Arrow) {
            self.bound.push(name);
            let body = self.parse_type();
            self.bound.pop();
            let body = body?;
            self.add(FlatExpr::pi(binfo, ty, body))
        } else if matches!(self.peek(), Some(Tok::Op(s)) if s == "&" || s == "*") {
            // Dependent sum `x:t & rest` (the binder `x` scopes over `rest`).
            // Model structurally as a `dtuple2` of the component types; the
            // binder is dropped (references to it in `rest` stay free Consts).
            self.bump();
            let rest = self.parse_type()?;
            let name_idx = self.writer.add_string("FStar.Pervasives.dtuple2");
            let dt = self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))?;
            let app1 = self.add(FlatExpr::app(dt, ty))?;
            self.add(FlatExpr::app(app1, rest))
        } else {
            // `x:t{φ}` used as a type by itself — erase to the base type `t`.
            Some(ty)
        }
    }

    /// Infix type operators, left-associative. `t1 * t2` / `t1 & t2` become
    /// `tuple2` applications; every other infix operator `a <op> b` (including
    /// `==`, `==>`, `<==>`, `/\`, `\/`, `=~`, `@~>`, `^->>`, list cons `::`,
    /// and backtick-infix `a `op` b`) becomes a structural
    /// `App(App(Const op, a), b)` so propositions and operator-bearing types
    /// import as real trees rather than being skipped.
    fn parse_product(&mut self) -> Option<u32> {
        let mut lhs = self.parse_app()?;
        while let Some(Tok::Op(s)) = self.peek() {
            let op = s.clone();
            self.bump();
            let rhs = self.parse_app()?;
            lhs = if op == "*" || op == "&" {
                self.tuple2_app(lhs, rhs)?
            } else {
                self.infix_app(&op, lhs, rhs)?
            };
        }
        Some(lhs)
    }

    fn tuple2_app(&mut self, a: u32, b: u32) -> Option<u32> {
        let name_idx = self.writer.add_string("FStar.Pervasives.Native.tuple2");
        let tup = self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))?;
        let app1 = self.add(FlatExpr::app(tup, a))?;
        self.add(FlatExpr::app(app1, b))
    }

    /// A generic binary type-operator application `a <op> b`, modelled as
    /// `App(App(Const "<op>", a), b)`.
    fn infix_app(&mut self, op: &str, a: u32, b: u32) -> Option<u32> {
        let name_idx = self.writer.add_string(op);
        let opc = self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))?;
        let app1 = self.add(FlatExpr::app(opc, a))?;
        self.add(FlatExpr::app(app1, b))
    }

    /// Skip to the close of a paren whose opening `(` was already consumed
    /// (depth starts at 1). Used for `(| … |)` dependent tuples.
    fn skip_to_paren_close(&mut self) {
        let mut depth = 1i32;
        while let Some(t) = self.peek() {
            match t {
                Tok::LParen => depth += 1,
                Tok::RParen => {
                    depth -= 1;
                    self.bump();
                    if depth == 0 {
                        return;
                    }
                    continue;
                }
                _ => {}
            }
            self.bump();
        }
    }

    /// Lookahead: a leading binder group. `(x : T)` needs a top-level colon;
    /// `{a : T}` is an implicit binder *unless* it carries a depth-1 `|` (then
    /// it is a set-builder refinement `{x:t | φ}`, parsed as an atom).
    fn looks_like_binder_group(&self) -> bool {
        match self.peek() {
            // `{| … |}` typeclass binder (a `|` right after `{`); otherwise an
            // implicit binder `{a:t}` unless it is a set-builder refinement.
            Some(Tok::LBrace) => {
                matches!(self.peek_at(1), Some(Tok::Pipe)) || !self.brace_has_top_pipe()
            }
            Some(Tok::LParen) => self.bracket_has_top_colon(&Tok::LParen, &Tok::RParen),
            _ => false,
        }
    }

    /// Lookahead from a `{`: is there a depth-1 `|`? Then it is a set-builder
    /// refinement `{x:t | φ}`, not an implicit binder group `{a:t}`.
    fn brace_has_top_pipe(&self) -> bool {
        let mut depth = 0i32;
        let mut k = self.pos;
        while let Some(t) = self.toks.get(k) {
            match t {
                Tok::LBrace => depth += 1,
                Tok::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return false;
                    }
                }
                Tok::Pipe if depth == 1 => return true,
                _ => {}
            }
            k += 1;
        }
        false
    }

    fn bracket_has_top_colon(&self, open: &Tok, close: &Tok) -> bool {
        let mut depth = 0i32;
        let mut k = self.pos;
        while let Some(t) = self.toks.get(k) {
            if t == open {
                depth += 1;
            } else if t == close {
                depth -= 1;
                if depth == 0 {
                    return false;
                }
            } else if depth == 1 && matches!(t, Tok::Colon) {
                return true;
            }
            k += 1;
        }
        false
    }

    /// Left-associative application: `f a b` ≡ `((f a) b)`. An explicitly
    /// supplied implicit argument `f #t` is dropped — the explicit applicative
    /// spine is what we model.
    fn parse_app(&mut self) -> Option<u32> {
        let mut head = self.parse_atom()?;
        loop {
            // A `(requires …)` / `(ensures …)` / `(decreases …)` /
            // `(modifies …)` computation-spec argument is dropped — this lets
            // *any* effect (including ones we do not name: `HoareST`, `stt`,
            // user-defined) survive even though its spec bodies contain `fun`.
            if self.peek_is_spec_paren() {
                self.skip_balanced(&Tok::LParen, &Tok::RParen);
                continue;
            }
            match self.peek() {
                Some(Tok::Ident(_) | Tok::Nat(_) | Tok::Underscore | Tok::LParen) => {
                    let arg = self.parse_atom()?;
                    head = self.add(FlatExpr::app(head, arg))?;
                }
                Some(Tok::Hash) => {
                    self.bump();
                    let _ = self.parse_atom()?;
                }
                // A bracketed argument — a normalization-step list
                // (`norm [delta; iota] t`) or an `SMTPat`/attribute tail — is
                // dropped; the applicative spine is what we model.
                Some(Tok::LBracket) => {
                    self.skip_balanced(&Tok::LBracket, &Tok::RBracket);
                }
                _ => break,
            }
        }
        Some(head)
    }

    fn parse_atom(&mut self) -> Option<u32> {
        let base = match self.peek().cloned()? {
            Tok::LParen => {
                self.bump();
                // Dependent-tuple literal / type `(| e1, e2, … |)` (F*
                // `Mkdtuple`): skip to the matching `)`, model as `dtuple2`.
                if matches!(self.peek(), Some(Tok::Pipe)) {
                    self.skip_to_paren_close();
                    let name_idx = self.writer.add_string("FStar.Pervasives.dtuple2");
                    self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))?
                } else {
                    let inner = self.parse_type()?;
                    if !self.eat(&Tok::RParen) {
                        return None;
                    }
                    inner
                }
            }
            // A prefix / stray operator (`~ p`, `(==)`, backtick) in atom
            // position becomes a `Const` so it composes structurally.
            Tok::Op(s) => {
                self.bump();
                let name_idx = self.writer.add_string(&s);
                self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))?
            }
            Tok::LBrace => {
                // Set-builder refinement `{ x : t | φ }` (or `{ t | φ }`):
                // erase to the base type `t`, dropping the predicate.
                self.bump(); // `{`
                if matches!(self.peek(), Some(Tok::Ident(_)) | Some(Tok::Underscore))
                    && matches!(self.peek_at(1), Some(Tok::Colon))
                {
                    self.bump(); // binder name
                    self.bump(); // `:`
                }
                let base = self.parse_product()?;
                self.skip_to_brace_close();
                base
            }
            Tok::Nat(n) => {
                self.bump();
                self.add(FlatExpr::lit_nat(n))?
            }
            Tok::Underscore => {
                self.bump();
                self.sort_prop()?
            }
            Tok::Ident(name) => {
                self.bump();
                self.emit_name(&name)?
            }
            // Brackets / arrows / commas / operators in atom position: invalid.
            _ => return None,
        };
        // Postfix refinement `t{φ}` — erase the predicate, keep the base.
        while matches!(self.peek(), Some(Tok::LBrace)) {
            self.skip_balanced(&Tok::LBrace, &Tok::RBrace);
        }
        Some(base)
    }

    /// A computation type whose head effect was already consumed. The value
    /// type is the first type argument (or `unit` for `Lemma`); the remaining
    /// pre / post / `decreases` / `SMTPat` arguments are dropped.
    fn parse_computation(&mut self, kind: CompKind) -> Option<u32> {
        match kind {
            CompKind::Unit => {
                self.skip_comp_args();
                let name_idx = self.writer.add_string("Prims.unit");
                self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
            }
            CompKind::FirstArg => {
                let res = self.parse_atom()?;
                self.skip_comp_args();
                Some(res)
            }
        }
    }

    /// Drop a computation type's trailing arguments up to a structural
    /// boundary, balancing nested brackets.
    fn skip_comp_args(&mut self) {
        loop {
            match self.peek() {
                None | Some(Tok::Arrow) | Some(Tok::RParen) | Some(Tok::RBrace)
                | Some(Tok::RBracket) | Some(Tok::Comma) | Some(Tok::Pipe) => break,
                Some(Tok::LParen) => self.skip_balanced(&Tok::LParen, &Tok::RParen),
                Some(Tok::LBrace) => self.skip_balanced(&Tok::LBrace, &Tok::RBrace),
                Some(Tok::LBracket) => self.skip_balanced(&Tok::LBracket, &Tok::RBracket),
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// Skip a balanced bracketed region. Assumes `peek() == open`.
    fn skip_balanced(&mut self, open: &Tok, close: &Tok) {
        let mut depth = 0i32;
        while let Some(t) = self.peek() {
            if t == open {
                depth += 1;
            } else if t == close {
                depth -= 1;
                self.bump();
                if depth == 0 {
                    return;
                }
                continue;
            }
            self.bump();
        }
    }

    /// Skip to the close of a brace whose opening `{` was already consumed
    /// (depth starts at 1).
    fn skip_to_brace_close(&mut self) {
        let mut depth = 1i32;
        while let Some(t) = self.peek() {
            match t {
                Tok::LBrace => depth += 1,
                Tok::RBrace => {
                    depth -= 1;
                    self.bump();
                    if depth == 0 {
                        return;
                    }
                    continue;
                }
                _ => {}
            }
            self.bump();
        }
    }

    fn emit_name(&mut self, name: &str) -> Option<u32> {
        // F* universe atoms: `Type`, `Type0`, …, `prop`. Map `prop`/`Prop`/
        // `logical` → sort(0); every `Type`-level sort → sort(1) (universe
        // levels are out of scope for a Level-0 import — a documented surface
        // approximation, not a verified universe). Only recognised sort
        // shapes become sorts so user names like `Tot` / `Property` stay
        // Consts.
        if is_sort_atom(name) {
            return if matches!(name, "prop" | "Prop" | "logical") {
                self.sort_prop()
            } else {
                self.sort_type()
            };
        }
        // Bound variable: innermost binding wins.
        if let Some(pos) = self.bound.iter().rposition(|n| n == name) {
            let depth = self.bound.len() - 1 - pos;
            return self.add(FlatExpr::bvar(depth as u32));
        }
        // Free name → Const reference.
        let name_idx = self.writer.add_string(name);
        self.add(FlatExpr::const_ref(name_idx, NO_LEVELS))
    }
}

/// Parse an F* type-expression string into `writer`, returning the root
/// expression index. Returns `None` on parse failure or empty input; callers
/// must treat that as "skip this declaration", never as a licence to emit a
/// placeholder. On success the entire token stream must be consumed (a
/// trailing unparsed remainder is a failure).
pub(crate) fn parse_fstar_type(src: &str, writer: &mut ShardWriter) -> Option<u32> {
    let toks = lex(src);
    if toks.is_empty() {
        return None;
    }
    let mut p = Parser::new(toks, writer);
    let root = p.parse_type()?;
    if p.pos != p.toks.len() {
        // Unconsumed tokens mean the type contained a construct we do not
        // model (e.g. refinement `{x:t | …}`, effect annotations, `match`).
        // Skip it.
        return None;
    }
    Some(root)
}

/// Reconstruct a definition *value* `λ binders. body` into `writer`, returning
/// the root expression index — the proof/value term of a `let`/`type`
/// definition. `binders` is the typed binder prefix (`(x:t) (y:u)`, possibly
/// empty for a nullary definition); `body` is the source after the `=`.
///
/// Returns `None` (⇒ fall back to an axiom, never a placeholder) when the
/// binders are untyped/odd or the body uses a construct we do not model
/// (`match`, `fun`, unmodelled operators). The binder de-Bruijn indices match
/// the reconstructed *type* `Π binders. ret`, so the kernel can check
/// `λ binders. body : Π binders. ret`.
pub(crate) fn parse_fstar_lambda(
    binders: &str,
    body: &str,
    writer: &mut ShardWriter,
) -> Option<u32> {
    let body = body.trim();
    if body.is_empty() {
        return None;
    }
    // Nullary definition (`let x : t = body`, `type t = rhs`): the value is the
    // body term, parsed in the empty scope.
    if binders.trim().is_empty() {
        return parse_fstar_type(body, writer);
    }
    // 1. Parse the typed binder groups, pushing each name so later groups'
    //    types resolve dependent references (mirrors `parse_binder_group_arrow`).
    let btoks = lex(binders);
    if btoks.is_empty() {
        return None;
    }
    let mut bp = Parser::new(btoks, writer);
    let mut binder_tys: Vec<(u8, u32)> = Vec::new();
    while bp.looks_like_binder_group() {
        let group = bp.parse_binder_group()?;
        for (name, binfo, ty) in group {
            bp.bound.push(name);
            binder_tys.push((binfo, ty));
        }
    }
    // Leftover binder tokens (an untyped or unmodelled binder) ⇒ bail.
    if bp.pos != bp.toks.len() || binder_tys.is_empty() {
        return None;
    }
    let bound = std::mem::take(&mut bp.bound);
    drop(bp);
    // 2. Parse the body term with the binders in scope.
    let body_toks = lex(body);
    if body_toks.is_empty() {
        return None;
    }
    let mut p = Parser::with_bound(body_toks, writer, bound);
    let body_idx = p.parse_type()?;
    if p.pos != p.toks.len() {
        return None;
    }
    // 3. Wrap in `Lam` over the binder types, innermost first.
    let mut acc = body_idx;
    for (binfo, ty) in binder_tys.iter().rev() {
        acc = p.add(FlatExpr::lam(*binfo, *ty, acc))?;
    }
    Some(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(w: &ShardWriter) -> Vec<String> {
        (0..w.string_count())
            .map(|i| w.string_at(i as u32).to_owned())
            .collect()
    }

    /// Names are now module-qualified (`Example.id`). Look a decl up by its
    /// unqualified short name for assertions.
    fn by_short<'a>(decls: &'a [FStarDecl], short: &str) -> Option<&'a FStarDecl> {
        let suffix = format!(".{short}");
        decls
            .iter()
            .find(|d| d.name == short || d.name.ends_with(&suffix))
    }

    #[test]
    fn parse_fstar_file_extracts_signatures_skipping_noise() {
        let content = "\
module Example
// the polymorphic identity function
open FStar.Mul

#set-options \"--z3rlimit 20\"

val id : a -> a

assume val ax : nat -> nat

(* a block comment
   spanning lines *)
let double (x:nat) : nat = x + x
";
        let decls = parse_fstar_file(content, "Example.fst");
        // Names are module-qualified from the `module Example` declaration.
        let names: Vec<&str> = decls.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["Example.id", "Example.ax", "Example.double"]);
        assert_eq!(decls[0].type_repr, "a -> a");
        assert_eq!(decls[1].type_repr, "nat -> nat");
        // `let double (x:nat) : nat = …` — the typed binder `(x:nat)` is folded
        // into the declared function type and the `= x + x` body truncated.
        assert_eq!(decls[2].type_repr, "(x:nat) -> nat");
    }

    #[test]
    fn multiline_val_signature_is_joined() {
        let content = "\
val compose : (b -> c)
            -> (a -> b)
            -> a
            -> c
";
        let decls = parse_fstar_file(content, "T.fst");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "T.compose");
        assert_eq!(decls[0].type_repr, "(b -> c) -> (a -> b) -> a -> c");
    }

    #[test]
    fn write_fstar_shard_emits_real_type_not_litstr_or_sort0() {
        // `val id : a -> a` must produce a real Pi/Const tree: multiple
        // FlatExpr nodes, type_idx must not be a LitStr or a lone sort(0).
        let decls = vec![FStarDecl {
            name: "id".into(),
            type_repr: "a -> a".into(),
            kind: FStarDeclKind::Axiom,
            ..Default::default()
        }];
        let mut w = ShardWriter::new();
        let written = write_fstar_shard(&decls, &mut w);
        assert_eq!(written, 1, "the id signature must be written");
        // Real tree ⇒ more exprs than constants (the no-stub signature).
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({})",
            w.expr_count(),
            w.constant_count()
        );
    }

    #[test]
    fn write_fstar_shard_dependent_type_resolves_binder_no_stub() {
        // Tighter than the count check: `val id : (a:Type) -> a -> a` builds
        // a real Pi/BVar tree. A sort(0) stub would give expr_count == 1 ==
        // constant_count (not greater), and the binder `a` must resolve to a
        // BVar — so `a` must NOT leak into the string table as a free Const.
        let decls = vec![FStarDecl {
            name: "id".into(),
            type_repr: "(a:Type) -> a -> a".into(),
            kind: FStarDeclKind::Axiom,
            ..Default::default()
        }];
        let mut w = ShardWriter::new();
        let written = write_fstar_shard(&decls, &mut w);
        assert_eq!(written, 1, "the id signature must be written");
        assert!(
            w.expr_count() > w.constant_count(),
            "expected expr_count ({}) > constant_count ({}) — a sort(0) stub \
             would make these equal",
            w.expr_count(),
            w.constant_count()
        );
        let ss = strings(&w);
        assert!(
            !ss.iter().any(|s| s == "a"),
            "binder name 'a' leaked into strings {ss:?} — dependent binder \
             not parsed as a Pi/BVar"
        );
    }

    #[test]
    fn parse_fstar_type_arrow_chain_builds_pis() {
        let mut w = ShardWriter::new();
        let root = parse_fstar_type("nat -> nat -> Type", &mut w).expect("parse");
        // Const(nat) [shared], sort(1) for Type, inner Pi, outer Pi.
        assert!(w.expr_count() >= 3, "expected real tree");
        assert_eq!(root, w.expr_count() as u32 - 1, "root is the outer Pi");
        let ss = strings(&w);
        assert!(ss.iter().any(|s| s == "nat"), "nat head missing: {ss:?}");
    }

    #[test]
    fn dependent_pi_resolves_binder_to_bvar() {
        // `(a:Type) -> a -> a`: the two `a` in the body must be BVars, so
        // `a` must NOT appear in the string table.
        let mut w = ShardWriter::new();
        let _ = parse_fstar_type("(a:Type) -> a -> a", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "a"), "a leaked as Const: {ss:?}");
    }

    #[test]
    fn implicit_binder_pi_parses() {
        let mut w = ShardWriter::new();
        let _ = parse_fstar_type("{a:Type} -> a -> a", &mut w).expect("parse");
        let ss = strings(&w);
        assert!(!ss.iter().any(|s| s == "a"), "a leaked: {ss:?}");
    }

    #[test]
    fn application_nests_left() {
        let mut w = ShardWriter::new();
        let _ = parse_fstar_type("list a", &mut w).expect("parse");
        // Const(list), Const(a), App.
        assert!(w.expr_count() >= 3, "expected real app tree");
    }

    #[test]
    fn empty_and_garbage_return_none() {
        let mut w = ShardWriter::new();
        assert!(parse_fstar_type("", &mut w).is_none());
        assert!(parse_fstar_type("   ", &mut w).is_none());
        // A `fun`-term is out of scope; the keyword aborts the lex and leaves
        // an unconsumable remainder ⇒ None (skip, not stub).
        assert!(parse_fstar_type("fun x -> x", &mut w).is_none());
        // A leading arrow has no domain atom ⇒ None.
        assert!(parse_fstar_type("-> nat", &mut w).is_none());
        // A lone closing bracket is not an atom ⇒ None.
        assert!(parse_fstar_type(")", &mut w).is_none());
    }

    #[test]
    fn infix_and_prefix_operators_import_structurally() {
        // Propositions and operator-bearing types now import as real `App`
        // trees (structural, Unverified) rather than being skipped.
        for src in [
            "a == b",
            "p ==> q",
            "p /\\ q",
            "x <= y",
            "either 'a 'b @~> either 'c 'd",
            "squash (Seq.length s == 0)",
            "~ (a == b)",
            "p :: rs",
        ] {
            let mut w = ShardWriter::new();
            assert!(
                parse_fstar_type(src, &mut w).is_some(),
                "operator-bearing type `{src}` should import"
            );
            assert!(w.expr_count() > 0, "`{src}` should yield a real expr tree");
        }
    }

    #[test]
    fn refinement_type_erases_to_base() {
        // `x:nat{x > 0}` is now modelled as its base type `nat` (the predicate
        // is a documented surface erasure) — a real Const, never a stub.
        let mut w = ShardWriter::new();
        let root = parse_fstar_type("x:nat{x > 0}", &mut w).expect("refinement parses");
        let _ = root;
        let ss: Vec<String> = (0..w.string_count())
            .map(|i| w.string_at(i as u32).to_owned())
            .collect();
        assert!(
            ss.iter().any(|s| s == "nat"),
            "base type nat missing: {ss:?}"
        );
        // The refinement binder `x` must not leak into the string table.
        assert!(!ss.iter().any(|s| s == "x"), "binder x leaked: {ss:?}");
    }

    /// Parse `src`, asserting it succeeds, and return the writer's string table.
    fn parse_strings(src: &str) -> Vec<String> {
        let mut w = ShardWriter::new();
        parse_fstar_type(src, &mut w).unwrap_or_else(|| panic!("expected `{src}` to parse"));
        strings(&w)
    }

    #[test]
    fn effect_tot_erases_to_value_type() {
        // `list 'a -> Tot nat` — the `Tot` effect wrapper erases to `nat`, and
        // the prime-prefixed type variable `'a` is a real identifier.
        let ss = parse_strings("list 'a -> Tot nat");
        assert!(ss.iter().any(|s| s == "nat"), "nat missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "list"), "list missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "'a"), "type var 'a missing: {ss:?}");
        assert!(!ss.iter().any(|s| s == "Tot"), "effect Tot leaked: {ss:?}");
    }

    #[test]
    fn lemma_effect_erases_to_unit() {
        // A `Lemma (requires …) (ensures …)` codomain erases to `unit`; the
        // spec keywords/predicates and the binder `x` never reach the shard.
        let ss = parse_strings("x:nat -> Lemma (requires x > 0) (ensures x >= 0)");
        assert!(ss.iter().any(|s| s == "nat"), "nat missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "Prims.unit"), "unit missing: {ss:?}");
        for leaked in ["Lemma", "requires", "ensures", "x"] {
            assert!(!ss.iter().any(|s| s == leaked), "{leaked} leaked: {ss:?}");
        }
    }

    #[test]
    fn stack_effect_with_pre_post_keeps_result_type() {
        // The HACL* `Stack t (requires …) (ensures …)` shape: result `unit`,
        // `fun`-bodied pre/post discarded without aborting the parse.
        let ss = parse_strings(
            "h:HS.mem -> Stack unit (requires (fun h0 -> True)) (ensures (fun h0 _ h1 -> True))",
        );
        assert!(
            ss.iter().any(|s| s == "unit"),
            "unit result missing: {ss:?}"
        );
        assert!(ss.iter().any(|s| s == "HS.mem"), "HS.mem missing: {ss:?}");
        assert!(
            !ss.iter().any(|s| s == "requires"),
            "requires leaked: {ss:?}"
        );
    }

    #[test]
    fn bare_dependent_binders_chain() {
        // `n:nat -> b:bool -> Tot int` — unparenthesised dependent binders.
        let ss = parse_strings("n:nat -> b:bool -> Tot int");
        for c in ["nat", "bool", "int"] {
            assert!(ss.iter().any(|s| s == c), "{c} missing: {ss:?}");
        }
        for binder in ["n", "b"] {
            assert!(
                !ss.iter().any(|s| s == binder),
                "binder {binder} leaked: {ss:?}"
            );
        }
    }

    #[test]
    fn implicit_bare_binder_resolves_bvar() {
        // `#a:Type -> a -> a` — implicit binder; both `a` occurrences are
        // BVars, so `a` must not appear as a free Const.
        let ss = parse_strings("#a:Type -> a -> a");
        assert!(
            !ss.iter().any(|s| s == "a"),
            "binder a leaked as Const: {ss:?}"
        );
    }

    #[test]
    fn refinement_binder_dependent_buffer_signature() {
        // A HACL*-shaped signature: refined length binder used dependently in a
        // later argument, stateful effect codomain.
        let ss = parse_strings(
            "len:size_t{v len > 0} -> b:lbuffer uint8 len -> \
             Stack unit (requires foo) (ensures bar)",
        );
        for c in ["size_t", "lbuffer", "uint8", "unit"] {
            assert!(ss.iter().any(|s| s == c), "{c} missing: {ss:?}");
        }
        // `len` is bound (BVar in `lbuffer uint8 len`), never a free Const.
        assert!(!ss.iter().any(|s| s == "len"), "binder len leaked: {ss:?}");
    }

    #[test]
    fn tuple_and_product_types() {
        let amp = parse_strings("int & bool");
        assert!(
            amp.iter().any(|s| s == "FStar.Pervasives.Native.tuple2"),
            "tuple2 missing for `&`: {amp:?}"
        );
        let star = parse_strings("a * b");
        assert!(
            star.iter().any(|s| s == "FStar.Pervasives.Native.tuple2"),
            "tuple2 missing for `*`: {star:?}"
        );
    }

    #[test]
    fn multi_binder_run_is_dependent() {
        // `(a:Type) (x:a) -> a` — a run of parenthesised binders before the
        // arrow; both binders resolve to BVars.
        let ss = parse_strings("(a:Type) (x:a) -> a");
        assert!(!ss.iter().any(|s| s == "a"), "binder a leaked: {ss:?}");
        assert!(!ss.iter().any(|s| s == "x"), "binder x leaked: {ss:?}");
    }

    #[test]
    fn set_builder_refinement_domain() {
        // `{x:nat | x > 0} -> bool` — set-builder refinement as the domain.
        let ss = parse_strings("{x:nat | x > 0} -> bool");
        assert!(ss.iter().any(|s| s == "nat"), "nat missing: {ss:?}");
        assert!(ss.iter().any(|s| s == "bool"), "bool missing: {ss:?}");
        assert!(!ss.iter().any(|s| s == "x"), "binder x leaked: {ss:?}");
    }

    #[test]
    fn type_universe_annotation_is_a_sort() {
        // `Type u#0`, `Type u#a`, and `Type u#(max a b)` are all sorts.
        for src in ["Type u#0", "Type u#a", "Type u#(max a b)"] {
            let mut w = ShardWriter::new();
            assert!(
                parse_fstar_type(src, &mut w).is_some(),
                "universe-annotated sort `{src}` failed to parse"
            );
        }
    }

    #[test]
    fn pure_effect_with_spec_args() {
        // `Pure (option a) (requires True) (ensures (fun _ -> True))` → result
        // `option a`, spec args dropped.
        let ss =
            parse_strings("x:int -> Pure (option a) (requires True) (ensures (fun _ -> True))");
        assert!(ss.iter().any(|s| s == "option"), "option missing: {ss:?}");
        assert!(!ss.iter().any(|s| s == "Pure"), "Pure leaked: {ss:?}");
    }

    #[test]
    fn let_with_typed_binders_reconstructs_function_type() {
        let content = "\
let add (x:nat) (y:nat) : nat = x + y
let id_ (#a:Type) (x:a) : a = x
let plain : nat = 0
let untyped f x : nat = x
";
        let decls = parse_fstar_file(content, "T.fst");
        let by_name = |n: &str| by_short(&decls, n).map(|d| d.type_repr.clone());
        // Typed binder groups are folded into the declared function type.
        assert_eq!(by_name("add").as_deref(), Some("(x:nat) (y:nat) -> nat"));
        assert_eq!(by_name("id_").as_deref(), Some("(#a:Type) (x:a) -> a"));
        // A `val`-style let with no binders is unchanged.
        assert_eq!(by_name("plain").as_deref(), Some("nat"));
        // Untyped binders `f x` cannot be reconstructed: return type verbatim.
        assert_eq!(by_name("untyped").as_deref(), Some("nat"));
    }

    #[test]
    fn multiline_binders_before_colon_are_reconstructed() {
        // The binders and the `:` annotation span several lines before the
        // body — the flattened header still yields the full function type.
        let content = "\
let lemma_long_name (x:nat)
                    (y:nat)
                  : Lemma (requires x < y)
                          (ensures x <= y)
                  = ()
";
        let decls = parse_fstar_file(content, "T.fst");
        let d = by_short(&decls, "lemma_long_name").expect("multi-line decl recognised");
        assert_eq!(
            d.type_repr,
            "(x:nat) (y:nat) -> Lemma (requires x < y) (ensures x <= y)"
        );
    }

    #[test]
    fn let_body_colon_is_not_mistaken_for_annotation() {
        // `let f = …` with a `:` inside the body must NOT be read as a type
        // annotation — `f` has no declared type, so it is skipped.
        let decls = parse_fstar_file("let f = fun (x:int) -> (x <: int)\n", "T.fst");
        assert!(
            !decls.iter().any(|d| d.name == "f"),
            "unannotated let with a body colon must be skipped: {decls:?}"
        );
    }

    #[test]
    fn type_sorted_decls_write_a_loadable_shard() {
        // A `Type`-sorted declaration must register the `succ(zero)` universe
        // level so the emitted `Sort` is valid; otherwise the shard is corrupt
        // and `ShardReader` rejects it. Regression for the
        // "sort level index 1 out of bounds" bug the real corpus surfaced.
        use crate::shard::ShardReader;
        let decls = vec![
            FStarDecl {
                name: "a_type".into(),
                type_repr: "Type".into(),
                kind: FStarDeclKind::Axiom,
                ..Default::default()
            },
            FStarDecl {
                name: "a_prop".into(),
                type_repr: "prop".into(),
                kind: FStarDeclKind::Axiom,
                ..Default::default()
            },
            FStarDecl {
                name: "poly_id".into(),
                type_repr: "(a:Type) -> a -> a".into(),
                kind: FStarDeclKind::Axiom,
                ..Default::default()
            },
        ];
        let mut w = ShardWriter::new();
        let written = write_fstar_shard(&decls, &mut w);
        assert_eq!(written, 3, "all three decls must be written");
        let path = std::env::temp_dir().join(format!(
            "fstar_sort_regression_{}.mathverse",
            std::process::id()
        ));
        w.write_to_file(&path).expect("write shard");
        let reader =
            ShardReader::from_file(&path).expect("shard must load (valid universe levels)");
        assert!(reader.lookup_name("a_type").is_some(), "a_type missing");
        assert!(reader.lookup_name("poly_id").is_some(), "poly_id missing");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn let_with_binders_writes_real_tree() {
        let decls = parse_fstar_file("let add (x:nat) (y:nat) : nat = x + y\n", "T.fst");
        assert_eq!(decls.len(), 1);
        let mut w = ShardWriter::new();
        let written = write_fstar_shard(&decls, &mut w);
        assert_eq!(written, 1, "reconstructed let type must be written");
        assert!(
            w.expr_count() > w.constant_count(),
            "expected a real Pi tree, got expr_count {} <= constant_count {}",
            w.expr_count(),
            w.constant_count()
        );
    }

    #[test]
    fn definition_body_reconstructed_as_value() {
        // A `let` with a reconstructable body becomes a real `DeclKind::Definition`
        // carrying `λ binders. body` — not an assumed axiom.
        use crate::shard::ShardReader;
        use crate::types::{DeclKind, NO_VALUE};
        let decls = parse_fstar_file("let myid (a:Type) (x:a) : a = x\n", "T.fst");
        let d = by_short(&decls, "myid").expect("myid parsed");
        assert_eq!(d.binders_repr, "(a:Type) (x:a)");
        assert_eq!(d.value_repr.as_deref(), Some("x"));
        let mut w = ShardWriter::new();
        assert_eq!(write_fstar_shard(std::slice::from_ref(d), &mut w), 1);
        let path = std::env::temp_dir().join(format!("fstar_def_{}.mathverse", std::process::id()));
        w.write_to_file(&path).expect("write shard");
        let reader = ShardReader::from_file(&path).expect("shard loads");
        let (_, h) = reader.lookup_name("T.myid").expect("T.myid present");
        assert_eq!(
            h.decl_kind,
            DeclKind::Definition as u8,
            "emitted as a Definition"
        );
        assert_ne!(h.value_idx, NO_VALUE, "Definition carries a value term");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn type_abbreviation_reconstructed_as_value() {
        // `type bytes = Seq.seq uint8` → a Definition whose value is the RHS type.
        use crate::shard::ShardReader;
        use crate::types::NO_VALUE;
        let decls = parse_fstar_file("type bytes = Seq.seq uint8\n", "T.fst");
        let d = by_short(&decls, "bytes").expect("bytes parsed");
        assert_eq!(d.value_repr.as_deref(), Some("Seq.seq uint8"));
        let mut w = ShardWriter::new();
        assert_eq!(write_fstar_shard(std::slice::from_ref(d), &mut w), 1);
        let path =
            std::env::temp_dir().join(format!("fstar_abbrev_{}.mathverse", std::process::id()));
        w.write_to_file(&path).expect("write shard");
        let reader = ShardReader::from_file(&path).expect("shard loads");
        let (_, h) = reader.lookup_name("T.bytes").expect("T.bytes present");
        assert_ne!(h.value_idx, NO_VALUE, "abbreviation carries its RHS value");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn operator_definitions_are_captured() {
        let content = "\
val ( +^ ) : int -> int -> int
let ( <=. ) (a:int) (b:int) : bool = a <= b
val ( = ) : a -> a -> bool
let (x:int) = 0
";
        let decls = parse_fstar_file(content, "Ops.fst");
        assert!(by_short(&decls, "+^").is_some(), "operator +^ missing");
        assert!(by_short(&decls, "<=.").is_some(), "operator <=. missing");
        assert!(by_short(&decls, "=").is_some(), "operator = missing");
        // `let (x:int) = 0` is a pattern-let, not an operator def — not a name.
        assert!(
            by_short(&decls, "x").is_none(),
            "pattern-let x wrongly captured"
        );
        // The operator `let` still folds its typed binders into the type.
        let leq = by_short(&decls, "<=.").unwrap();
        assert_eq!(leq.type_repr, "(a:int) (b:int) -> bool");
    }

    #[test]
    fn is_operator_name_discriminates() {
        assert!(is_operator_name("+^"));
        assert!(is_operator_name("<=."));
        assert!(is_operator_name("|>"));
        assert!(is_operator_name("="));
        assert!(!is_operator_name("")); // empty
        assert!(!is_operator_name("x:t")); // binder
        assert!(!is_operator_name("x")); // identifier
    }

    #[test]
    fn standalone_parenthesised_refinement_imports() {
        // `(x:UInt32.t { … })` as a whole type (no `->`) — pervasive in HACL*
        // test vectors — imports as its base type, not skipped.
        let ss = parse_strings("(x:UInt32.t { UInt32.v x = B.length key0 })");
        assert!(
            ss.iter().any(|s| s == "UInt32.t"),
            "base type UInt32.t missing: {ss:?}"
        );
        assert!(!ss.iter().any(|s| s == "x"), "binder x leaked: {ss:?}");
    }

    #[test]
    fn anonymous_typeclass_binder_imports() {
        // `{| ord a |}` — an anonymous typeclass binder (no `name :`).
        let ss = parse_strings("#a:Type -> {| ord a |} -> a -> a -> bool");
        assert!(
            ss.iter().any(|s| s == "ord"),
            "typeclass ord missing: {ss:?}"
        );
        assert!(ss.iter().any(|s| s == "bool"), "bool missing: {ss:?}");
        // The named form still works.
        assert!(
            parse_fstar_type("(#a:eqtype) {| _ : ordered a |} (x:a) -> bool", &mut {
                ShardWriter::new()
            })
            .is_some()
        );
    }

    #[test]
    fn unknown_and_pulse_effects_with_specs_import() {
        // Any effect with `(requires …)` / `(ensures …)` (fun-bodied) specs —
        // including Pulse `stt` / `HoareST` and effects we do not name.
        for src in [
            "x:int -> HoareST int (requires fun _ -> True) (ensures fun s0 _ s1 -> True)",
            "r:ref int -> v:int -> stt unit (pts_to r v) (fun _ -> pts_to r v)",
            "x:a -> UserEff b (requires fun _ -> True) (ensures fun _ -> True)",
        ] {
            let mut w = ShardWriter::new();
            assert!(
                parse_fstar_type(src, &mut w).is_some(),
                "effectful type `{src}` should import"
            );
        }
    }

    #[test]
    fn type_abbreviation_and_inductive_capture() {
        let content = "\
type bytes = Seq.seq uint8
type option (a:Type) =
  | None : option a
  | Some : a -> option a
type color =
  | Red
  | Green
  | Blue
";
        let decls = parse_fstar_file(content, "T.fst");
        let get = |n: &str| by_short(&decls, n).cloned();
        let by = |n: &str| get(n).map(|d| d.type_repr);
        // Abbreviation former: a `Type` (axiom, not an inductive).
        assert_eq!(by("bytes").as_deref(), Some("Type"));
        assert_eq!(get("bytes").unwrap().kind, FStarDeclKind::Axiom);
        // Parameterised inductive former: `(a:Type) -> Type`, tagged Inductive
        // with 1 parameter. The family is module-qualified (`T.option`).
        assert_eq!(get("option").unwrap().name, "T.option");
        assert_eq!(by("option").as_deref(), Some("(a:Type) -> Type"));
        assert_eq!(
            get("option").unwrap().kind,
            FStarDeclKind::Inductive { num_params: 1 }
        );
        // Constructors carry the parameter in kernel form AND the qualified
        // inductive self-reference, and are tagged Constructor.
        assert_eq!(by("None").as_deref(), Some("(a:Type) -> T.option a"));
        assert_eq!(by("Some").as_deref(), Some("(a:Type) -> a -> T.option a"));
        assert_eq!(get("Some").unwrap().kind, FStarDeclKind::Constructor);
        // A parameterless inductive: nullary constructors return the inductive.
        assert_eq!(by("color").as_deref(), Some("Type"));
        assert_eq!(
            get("color").unwrap().kind,
            FStarDeclKind::Inductive { num_params: 0 }
        );
        assert_eq!(by("Red").as_deref(), Some("T.color"));
        assert_eq!(by("Green").as_deref(), Some("T.color"));
        assert_eq!(by("Blue").as_deref(), Some("T.color"));
    }

    #[test]
    fn type_decl_with_explicit_kind() {
        let decls = parse_fstar_file("type u8 : eqtype = UInt8.t\n", "T.fst");
        let d = by_short(&decls, "u8").expect("u8 former");
        assert_eq!(d.type_repr, "eqtype");
    }

    #[test]
    fn type_decls_write_real_trees() {
        let content = "\
type option (a:Type) =
  | None : option a
  | Some : a -> option a
";
        let decls = parse_fstar_file(content, "T.fst");
        let mut w = ShardWriter::new();
        let written = write_fstar_shard(&decls, &mut w);
        // Former + 2 constructors, all real trees, none skipped.
        assert_eq!(written, 3, "former and both constructors must be written");
    }

    #[test]
    fn binders_are_typed_discriminates() {
        assert!(binders_are_typed("(x:nat)"));
        assert!(binders_are_typed("(x:nat) (y:bool)"));
        assert!(binders_are_typed("(#a:Type) (x:a)"));
        assert!(binders_are_typed("{a:Type} (x:a)"));
        assert!(!binders_are_typed(""));
        assert!(!binders_are_typed("x y")); // untyped binders
        assert!(!binders_are_typed("#a (x:a)")); // bare `#a` is untyped
        assert!(!binders_are_typed("(x)")); // no `:`
    }
}
