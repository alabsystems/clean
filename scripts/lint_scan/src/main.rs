// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The source scan of `scripts/check_lint_coverage.py`.
//!
//! That check runs each STANDALONE_GATED crate's tests and its clippy with the
//! three wildcard lints FORBIDDEN. Some source keeps a catch-all out of that
//! lint without lowering any level, while `cargo test` still compiles and runs
//! it; this binary refuses it. It is given exactly the files rustc compiled (the
//! check reads them off rustc's dep-info), parses each with syn, and prints one
//! `FILE:LINE: why` line per refusal: exit 1 when there is one, 0 when there is
//! none, 2 on a usage error. What it does not model is refused, not judged:
//!
//! * a file syn cannot parse, and any syntax syn keeps unparsed (`Verbatim`);
//! * a macro other than [`ALLOWED_MACROS`] -- std macros that take expressions,
//!   never patterns -- invoked by its bare name. Clippy's match lints skip what
//!   a macro writes, so `macro_rules!` and `matches!` (whose expansion carries a
//!   `_ => false` arm) are refused; each admitted macro's arguments are parsed
//!   as expressions and scanned like any other code;
//! * a `use` or `extern crate` binding a name the scan admits by name, or a glob
//!   (`use core::matches as todo;` runs `matches!` as `todo!`);
//! * an attribute outside [`ALLOWED_ATTRS`] (and a `feature` other than
//!   `rustc_private`, which the typed scan's own crate needs); a `cfg`/`cfg_attr`
//!   predicate naming anything but `test` (any other cfg can hold in one of the
//!   lint run, the test build and the release build and not in another, so the
//!   code it guards is run and never linted); a derive outside the builtin ones;
//!   an inner `deny`/`forbid` of a clippy lint the check does not forbid.
//!
//! A catch-all in a pattern is not judged here any more: which of them the
//! wildcard lints read was decided by hand, from syntax, and rustc resolves
//! what syntax cannot (a constant from a unit variant, `Self` and an alias, a
//! field counted from the end); verifiers r10 and r10b measured each passing.
//! The typed scan, scripts/lint_types, is rustc itself and judges every
//! pattern the compiler builds (lane r11).
//!
//! Names are read the way rustc reads them: syn takes `r#if` as ONE identifier
//! and [`IdentExt::unraw`] strips the prefix, and a non-ASCII identifier is an
//! identifier like any other. The hand-written lexer this replaced read `r#if`
//! as `r`, `#`, `if` and `ñ` as punctuation, and each carried a renamed
//! `matches!` past it (verifier r9c, 2026-09-25).

use std::collections::BTreeSet;
use std::process::ExitCode;

use proc_macro2::Span;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::{Comma, Semi};
use syn::visit::{self, Visit};
use syn::{AttrStyle, Attribute, Expr, Ident, Meta, Pat, Path, UseTree};

/// Std macros that take expressions, never patterns: nothing they expand to is
/// a match the source wrote. (`stringify!` takes tokens it never compiles.)
const ALLOWED_MACROS: &[&str] = &[
    "assert",
    "assert_eq",
    "assert_ne",
    "column",
    "concat",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "env",
    "eprint",
    "eprintln",
    "file",
    "format",
    "format_args",
    "line",
    "module_path",
    "option_env",
    "panic",
    "print",
    "println",
    "stringify",
    "todo",
    "unimplemented",
    "unreachable",
    "vec",
    "write",
    "writeln",
];
const ALLOWED_ATTRS: &[&str] = &[
    "allow",
    "cfg",
    "cfg_attr",
    "cold",
    "deny",
    "derive",
    "doc",
    "expect",
    "feature",
    "forbid",
    "inline",
    "must_use",
    "non_exhaustive",
    "repr",
    "should_panic",
    "test",
    "track_caller",
    "warn",
];
const ALLOWED_DERIVES: &[&str] = &[
    "Clone",
    "Copy",
    "Debug",
    "Default",
    "Eq",
    "Hash",
    "Ord",
    "PartialEq",
    "PartialOrd",
];

fn main() -> ExitCode {
    let mut forbidden = BTreeSet::new();
    let mut files = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg != "--forbidden" {
            files.push(arg);
        } else if let Some(lint) = args.next() {
            forbidden.insert(lint);
        } else {
            eprintln!("lint-scan: --forbidden takes a lint name");
            return ExitCode::from(2);
        }
    }
    if files.is_empty() {
        eprintln!("usage: lint-scan [--forbidden <clippy::lint>]... <file.rs>...");
        return ExitCode::from(2);
    }
    let mut refused = 0usize;
    for file in &files {
        let found = std::fs::read_to_string(file).map_or_else(
            |err| vec![format!("{file}: cannot be read ({err})")],
            |text| scan(file, &text, &forbidden),
        );
        refused += found.len();
        for line in found {
            println!("{line}");
        }
    }
    if refused == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Every refusal in one file's source, as `LABEL:LINE: why`.
fn scan(label: &str, text: &str, forbidden: &BTreeSet<String>) -> Vec<String> {
    let mut scan = Scan {
        label,
        forbidden,
        found: Vec::new(),
    };
    match syn::parse_file(text) {
        Ok(file) => scan.visit_file(&file),
        Err(err) => scan.refuse(
            err.span(),
            format!("cannot be parsed ({err}); source this scan cannot read is refused"),
        ),
    }
    scan.found
}

struct Scan<'a> {
    label: &'a str,
    forbidden: &'a BTreeSet<String>,
    found: Vec<String>,
}

fn modeled(name: &str) -> bool {
    ALLOWED_MACROS.contains(&name)
        || ALLOWED_ATTRS.contains(&name)
        || ALLOWED_DERIVES.contains(&name)
}

/// The one identifier a path is, unraw'd -- `None` for a path of more than one
/// segment, a leading `::` or generic arguments.
fn bare_name(path: &Path) -> Option<String> {
    let seg = path.segments.first()?;
    let bare = path.leading_colon.is_none() && path.segments.len() == 1 && seg.arguments.is_none();
    bare.then(|| seg.ident.unraw().to_string())
}

fn path_text(path: &Path) -> String {
    let segs: Vec<String> = path
        .segments
        .iter()
        .map(|s| s.ident.unraw().to_string())
        .collect();
    format!(
        "{}{}",
        if path.leading_colon.is_some() {
            "::"
        } else {
            ""
        },
        segs.join("::")
    )
}

/// A cfg predicate over `test` alone: `test`, `not(test)`, `all(..)`/`any(..)`
/// of such.
fn cfg_names_test(pred: &Meta) -> bool {
    match pred {
        Meta::Path(path) => bare_name(path).as_deref() == Some("test"),
        Meta::List(list) => {
            let op = bare_name(&list.path).unwrap_or_default();
            ["all", "any", "not"].contains(&op.as_str())
                && list
                    .parse_args_with(Punctuated::<Meta, Comma>::parse_terminated)
                    .is_ok_and(|inner| inner.iter().all(cfg_names_test))
        }
        Meta::NameValue(_) => false,
    }
}

/// `vec![elem; n]`, read as the two expressions it holds.
fn repeat(input: ParseStream) -> syn::Result<Punctuated<Expr, Comma>> {
    let elem: Expr = input.parse()?;
    let _: Semi = input.parse()?;
    let count: Expr = input.parse()?;
    Ok([elem, count].into_iter().collect())
}

impl Scan<'_> {
    fn refuse(&mut self, span: Span, why: String) {
        self.found
            .push(format!("{}:{}: {why}", self.label, span.start().line));
    }

    fn unparsed(&mut self, span: Span, what: &str) {
        self.refuse(
            span,
            format!("{what} syn keeps unparsed -- syntax this scan does not model"),
        );
    }

    fn macro_call(&mut self, mac: &syn::Macro) {
        let span = mac.path.span();
        let Some(name) = bare_name(&mac.path) else {
            let path = path_text(&mac.path);
            self.refuse(span, format!("the macro `{path}!` -- a macro is modeled by its bare name; a path names some other one"));
            return;
        };
        if !ALLOWED_MACROS.contains(&name.as_str()) {
            self.refuse(
                span,
                format!(
                    "the macro `{name}!` -- only std macros that take no pattern are modeled; clippy's match lints skip what a macro writes, so a catch-all in a `macro_rules!` body, or the `_ => false` arm `matches!` expands to, is never linted"
                ),
            );
            return;
        }
        if name == "stringify" {
            return;
        }
        let args = mac
            .parse_body_with(Punctuated::<Expr, Comma>::parse_terminated)
            .or_else(|_| mac.parse_body_with(repeat));
        match args {
            Ok(exprs) => exprs.iter().for_each(|e| self.visit_expr(e)),
            Err(err) => self.refuse(
                span,
                format!(
                    "the arguments of `{name}!` are not the expressions this scan reads ({err})"
                ),
            ),
        }
    }

    fn attribute(&mut self, meta: &Meta, style: &AttrStyle) {
        let span = meta.path().span();
        let Some(name) = bare_name(meta.path()) else {
            let path = path_text(meta.path());
            self.refuse(span, format!("the attribute `#[{path}]` -- an attribute is modeled by its bare name; a tool or proc-macro attribute rewrites code this scan cannot see"));
            return;
        };
        if !ALLOWED_ATTRS.contains(&name.as_str()) {
            self.refuse(
                span,
                format!(
                    "the attribute `#[{name}]` -- only {} are modeled; `#[path]` and proc-macro attributes pull in or rewrite code this scan cannot see",
                    ALLOWED_ATTRS.join(", ")
                ),
            );
            return;
        }
        let Meta::List(list) = meta else {
            return;
        };
        let metas = list.parse_args_with(Punctuated::<Meta, Comma>::parse_terminated);
        let Ok(metas) = metas else {
            if name == "cfg" || name == "cfg_attr" || name == "derive" {
                self.refuse(span, format!("a `#[{name}(..)]` this scan does not read"));
            }
            return;
        };
        let first = metas.first();
        if name == "feature" {
            let only = metas.len() == 1
                && first.is_some_and(|m| bare_name(m.path()).as_deref() == Some("rustc_private"));
            if !only {
                self.refuse(span, "a `#![feature(..)]` other than `rustc_private` -- an unstable feature is syntax and semantics this scan does not model".to_string());
            }
        } else if name == "cfg" && (metas.len() != 1 || !first.is_some_and(cfg_names_test)) {
            let text = list
                .tokens
                .to_string()
                .replace(" (", "(")
                .replace("( ", "(")
                .replace(" )", ")");
            self.refuse(span, format!("the predicate `cfg({text})` -- a `cfg` may name only `test` (under all/any/not): anything else can hold in one of the lint run, the test build and the release build and not in another, so the code it guards is run and never linted"));
        } else if name == "cfg_attr" {
            if !first.is_some_and(cfg_names_test) {
                self.refuse(span, "the predicate of a `cfg_attr` -- a `cfg_attr` may name only `test`: the attribute it carries would hold in one run and not in another".to_string());
            }
            metas.iter().skip(1).for_each(|m| self.attribute(m, style));
        } else if name == "derive" {
            for m in &metas {
                let ok = bare_name(m.path()).is_some_and(|n| ALLOWED_DERIVES.contains(&n.as_str()));
                if !ok || m.require_path_only().is_err() {
                    let derive = path_text(m.path());
                    self.refuse(span, format!("`#[derive({derive})]` -- only the builtin derives, by their bare names, are modeled; a proc-macro derive writes code nobody reads here"));
                }
            }
        } else if name == "deny" || name == "forbid" {
            if let AttrStyle::Inner(_) = style {
                for m in &metas {
                    let lint = path_text(m.path());
                    if lint.starts_with("clippy::") && !self.forbidden.contains(&lint) {
                        self.refuse(span, format!("the source denies `{lint}`, which the check does not FORBID on the command line, so an `#[allow]` in the source lowers it back"));
                    }
                }
            }
        }
    }

    fn binds(&mut self, ident: &Ident) {
        let name = ident.unraw().to_string();
        if modeled(&name) {
            self.refuse(ident.span(), format!("a `use` binding `{name}` -- the scan admits `{name}` by NAME, so an import re-pointing it (`use core::matches as todo;`) runs something nobody modeled under that name"));
        }
    }

    fn use_tree(&mut self, tree: &UseTree, parent: Option<&Ident>) {
        match tree {
            UseTree::Path(path) => self.use_tree(&path.tree, Some(&path.ident)),
            UseTree::Name(name) => {
                let bound = if name.ident == "self" { parent } else { Some(&name.ident) };
                bound.into_iter().for_each(|b| self.binds(b));
            }
            UseTree::Rename(rename) => self.binds(&rename.rename),
            UseTree::Glob(glob) => self.refuse(
                glob.star_token.span(),
                "a glob `use` -- it binds names this scan never sees, a macro under a modeled name among them".to_string(),
            ),
            UseTree::Group(group) => group.items.iter().for_each(|t| self.use_tree(t, parent)),
        }
    }
}

impl<'ast> Visit<'ast> for Scan<'_> {
    fn visit_attribute(&mut self, attr: &'ast Attribute) {
        self.attribute(&attr.meta, &attr.style);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        self.macro_call(mac);
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        item.attrs.iter().for_each(|a| self.visit_attribute(a));
        self.use_tree(&item.tree, None);
    }

    fn visit_item_extern_crate(&mut self, item: &'ast syn::ItemExternCrate) {
        visit::visit_item_extern_crate(self, item);
        self.binds(item.rename.as_ref().map_or(&item.ident, |(_, name)| name));
    }

    fn visit_item(&mut self, item: &'ast syn::Item) {
        if let syn::Item::Verbatim(tokens) = item {
            self.unparsed(tokens.span(), "an item");
        }
        visit::visit_item(self, item);
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        if let Expr::Verbatim(tokens) = expr {
            self.unparsed(tokens.span(), "an expression");
        }
        visit::visit_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'ast Pat) {
        if let Pat::Verbatim(tokens) = pat {
            self.unparsed(tokens.span(), "a pattern");
        }
        visit::visit_pat(self, pat);
    }

    fn visit_type(&mut self, ty: &'ast syn::Type) {
        if let syn::Type::Verbatim(tokens) = ty {
            self.unparsed(tokens.span(), "a type");
        }
        visit::visit_type(self, ty);
    }

    fn visit_impl_item(&mut self, item: &'ast syn::ImplItem) {
        if let syn::ImplItem::Verbatim(tokens) = item {
            self.unparsed(tokens.span(), "an impl item");
        }
        visit::visit_impl_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'ast syn::TraitItem) {
        if let syn::TraitItem::Verbatim(tokens) = item {
            self.unparsed(tokens.span(), "a trait item");
        }
        visit::visit_trait_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'ast syn::ForeignItem) {
        if let syn::ForeignItem::Verbatim(tokens) = item {
            self.unparsed(tokens.span(), "a foreign item");
        }
        visit::visit_foreign_item(self, item);
    }
}

#[cfg(test)]
mod tests {
    use super::scan;

    fn refusals(src: &str) -> Vec<String> {
        let forbidden = [
            "clippy::wildcard_enum_match_arm",
            "clippy::match_wildcard_for_single_variants",
            "clippy::wildcard_in_or_patterns",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        scan("t.rs", src, &forbidden)
    }

    #[track_caller]
    fn refused(src: &str, needle: &str) {
        let found = refusals(src);
        assert!(
            found.iter().any(|f| f.contains(needle)),
            "expected a refusal naming {needle:?} in {src:?}, got {found:?}"
        );
    }

    #[track_caller]
    fn passes(src: &str) {
        let found = refusals(src);
        assert!(
            found.is_empty(),
            "expected no refusal in {src:?}, got {found:?}"
        );
    }

    // ── macros, by the name rustc resolves ──────────────────────────────────

    #[test]
    fn a_macro_renamed_onto_a_raw_keyword_is_seen_under_that_name() {
        // verifier r9c: the lexer read `r#if` as `r`, `#`, `if`.
        refused(
            "use core::matches as r#if;\nfn f(x: Option<u8>) -> bool { r#if!(x, Some(1)) }",
            "the macro `if!`",
        );
    }

    #[test]
    fn a_macro_renamed_onto_a_non_ascii_name_is_seen() {
        // verifier r9c: the lexer read `ñ` as punctuation.
        refused(
            "use core::matches as ñ;\nfn f(x: Option<u8>) -> bool { ñ!(x, Some(1)) }",
            "the macro `ñ!`",
        );
    }

    #[test]
    fn a_keyword_of_a_later_edition_as_a_name_is_unreadable_and_refused() {
        refused("use core::matches as async;", "cannot be parsed");
    }

    #[test]
    fn a_macro_renamed_onto_a_modeled_name_is_refused_at_the_use() {
        refused(
            "use core::matches as todo;\nfn f(x: Option<u8>) -> bool { todo!(x, Some(1)) }",
            "a `use` binding `todo`",
        );
        refused("use core::matches as r#todo;", "a `use` binding `todo`");
        refused("use dep::Expander as Clone;", "a `use` binding `Clone`");
        refused("use dep::{self as todo};", "a `use` binding `todo`");
        refused("extern crate dep as todo;", "a `use` binding `todo`");
        refused("use dep::*;", "a glob `use`");
    }

    #[test]
    fn a_pattern_writing_macro_is_refused_wherever_it_is_invoked() {
        refused(
            "fn f(x: Option<u8>) -> bool { matches!(x, Some(1)) }",
            "the macro `matches!`",
        );
        refused("macro_rules! hide { () => {} }", "the macro `macro_rules!`");
        refused(r#"include!("elsewhere.rs");"#, "the macro `include!`");
        refused("fn f() -> u8 { dep::todo!() }", "the macro `dep::todo!`");
        // inside an admitted macro's arguments
        refused(
            r#"fn f(x: Option<u8>) { println!("{}", matches!(x, Some(1))); }"#,
            "the macro `matches!`",
        );
        refused(
            "fn f() { let v = vec![matches!(1, 1); 2]; }",
            "the macro `matches!`",
        );
    }

    // ── attributes and cfgs ─────────────────────────────────────────────────

    #[test]
    fn a_cfg_may_name_test_alone() {
        refused(
            "#[cfg(not(clippy))] fn hidden() {}",
            "the predicate `cfg(not(clippy))`",
        );
        refused(
            "#[cfg(not(debug_assertions))] fn hidden() {}",
            "the predicate",
        );
        refused(r#"#[cfg(feature = "x")] fn hidden() {}"#, "the predicate");
        refused(
            "#[cfg(not(clean_lint_run))] fn hidden() {}",
            "the predicate",
        );
        refused(
            "#[cfg_attr(clippy, allow(dead_code))] fn f() {}",
            "the predicate of a `cfg_attr`",
        );
        refused(
            "#[cfg_attr(debug_assertions, allow(dead_code))] fn f() {}",
            "the predicate of a `cfg_attr`",
        );
        refused(
            r#"#[cfg_attr(test, path = "elsewhere.rs")] mod elsewhere;"#,
            "the attribute `#[path]`",
        );
    }

    #[test]
    fn attributes_and_derives_outside_the_model_are_refused() {
        refused(
            r#"#[path = "elsewhere.rs"] mod elsewhere;"#,
            "the attribute `#[path]`",
        );
        refused(
            "#[rustfmt::skip] fn f() {}",
            "the attribute `#[rustfmt::skip]`",
        );
        refused(
            "#[derive(serde::Serialize)] struct S;",
            "`#[derive(serde::Serialize)]`",
        );
        refused("#[derive(dep::Clone)] struct S;", "`#[derive(dep::Clone)]`");
        refused(
            "#[macro_use] extern crate dep;",
            "the attribute `#[macro_use]`",
        );
        refused(
            "#![deny(clippy::unwrap_used)]",
            "denies `clippy::unwrap_used`",
        );
        refused("macro m() {}", "syn keeps unparsed");
        refused(
            "#![feature(stmt_expr_attributes)]",
            "a `#![feature(..)]` other than `rustc_private`",
        );
        refused(
            "#![feature(rustc_private, box_patterns)]",
            "a `#![feature(..)]` other than `rustc_private`",
        );
    }

    // ── controls ────────────────────────────────────────────────────────────

    #[test]
    fn refused_spellings_in_comments_strings_and_chars_are_not_code() {
        passes(concat!(
            "#![forbid(clippy::wildcard_enum_match_arm)]\n",
            "#![feature(rustc_private)]\n",
            "// macro_rules! include!() #[cfg(clippy)] matches!(x)\n",
            "/* #[path = \"x.rs\"] /* nested */ cfg_attr(clippy) */\n",
            "fn g() -> (&'static str, char, &'static str, char) {\n",
            "    (\"#[cfg(not(clippy))] macro_rules!\", '\\'', r#\"matches!(\"x\")\"#, '\"')\n}\n",
            "#[derive(Clone, Debug)] struct T<'a>(&'a u8);\n",
            "#[cfg(test)] #[allow(clippy::too_many_lines)] fn h() { assert!(true, \"{}\", 1); }\n",
            "fn k(a: bool) -> bool { if !(a) { return !a; } while !a {} a }\n",
            "use std::fmt::Write as _;\nuse crate::test::helper;\n",
            "#[cfg(any(test, all(not(test))))] #[cfg_attr(not(test), derive(Clone))] struct U;\n",
            "fn m() -> String { let r#type = 1; format!(\"{}{x}\", r#type, x = vec![0u8; 2].len()) }\n",
            "fn n<'a>() -> impl Sized + use<'a> {}\n",
        ));
    }
}
