// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Every catch-all in the crate's `trust_ir::Inst` dispatches, refused by a
//! parse that no attribute can silence.
//!
//! A catch-all arm in an `Inst` dispatch compiles unchanged when trust-ir adds
//! a variant, so the new instruction joins that dispatch's refusal (or a
//! handled arm) without anyone deciding whether it should. Two halves refuse
//! it:
//!
//! * the crate root denies the catch-all by TYPE (`clippy::wildcard_enum_match_arm`
//!   and its two siblings, see `src/lib.rs`), over EVERY enum the crate
//!   matches, and the full gate's `dispatch-exhaustive-lint` leg runs that
//!   clippy;
//! * this module PARSES every source file of every target of the crate
//!   (`src/`, `tests/`, `benches/`, `examples/`) with `syn` and refuses every
//!   catch-all arm in an `Inst` dispatch itself -- at top level or one level
//!   down -- whether or not clippy also judges it.
//!
//! The parse does not defer to clippy on `Inst`, because clippy's verdict is a
//! DEFAULT, not a `forbid`: an item- or module-level `#[allow]` / `#[expect]`
//! of `clippy::wildcard_enum_match_arm` overrides the crate-root `deny`, and
//! this crate uses that idiom itself over syn's `#[non_exhaustive]` enums. From
//! 54861cbce until verifier r7 (2026-09-24) the parse left a top-level
//! catch-all beside a named arm to clippy, and `_ =>` in `fragment2_inst_label`
//! under `#[expect(clippy::wildcard_enum_match_arm)]` linted AND scanned clean.
//! Measured 2026-09-24 on a probe crate, clippy also does NOT see, even
//! un-silenced:
//!
//! * a catch-all one level DOWN, in an arm that destructures a tuple, a slice,
//!   or a struct / tuple struct that is not an `Inst` variant around the
//!   `Inst` (`Ok(..)`, `(_, true)`, `InstrNode { .. }`): the scrutinee's type
//!   is the wrapper, not `Inst`;
//! * a match whose arms name NO `Inst` variant at top level
//!   (`match &n.inst { i if is_call(i) => …, _ => … }`): clippy only judges a
//!   match that names some variant;
//! * a `match` inside a `macro_rules!` body: clippy skips expanded code.
//!
//! The parse refuses all of those too, plus what keeps its own view of the
//! crate honest:
//!
//! * an `Inst` dispatch is any `match` one of whose arms names an `Inst::…`
//!   path or the crate's `insts!` pattern macro, and any `match` whose
//!   scrutinee is spelled `inst` / `….inst` (behind `&`, `*` or parentheses);
//! * `insts!` must keep expanding to named `Inst::$variant` alternatives, and
//!   whatever would let a variant be named WITHOUT an `Inst::` path -- a `use`
//!   of `Inst`'s variants, a rename or type alias of `Inst`, an `impl` on
//!   `Inst` -- is refused crate-wide, because it would hide a dispatch from
//!   the first rule;
//! * a macro CALL whose tokens contain `match` is parsed as its
//!   comma-separated expressions and scanned, or refused when it does not
//!   parse that way;
//! * the dispatches found are pinned by function, so one the parse stops
//!   seeing fails here instead of passing vacuously, and a new one is named;
//! * every target ROOT carries the crate's deny attribute -- an integration
//!   test is its own crate, and one that dropped it would be linted by
//!   nothing.
//!
//! THREAT MODEL: accidental catch-alls in first-party code. A deliberately
//! obfuscated spelling -- a variant named through
//! `<() as SomeAlias>::I::Unreachable`, a proc macro, a `cfg`'d twin -- is out
//! of scope for both halves and belongs to code review; a syntactic scan that
//! chased every spelling would never be finished.
//!
//! NOT a dispatch here: a one-variant test (`if let Inst::Call { .. } = …`,
//! `let Inst::Return { .. } = … else { refuse }`, `matches!`). Those ask
//! whether an `Inst` IS one variant; they do not decide per variant.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use syn::punctuated::Punctuated;
use syn::visit::{self, Visit};
use syn::{Pat, Token, UseTree};

/// The `Inst` dispatches this crate has, as `(file, enclosing fn)`.
const EXPECTED_DISPATCHES: &[(&str, &str)] = &[
    ("src/denote.rs", "denote_closed_zeroary"),
    ("src/denote.rs", "denote_function"),
    ("src/denote.rs", "eval_heap_node"),
    ("src/denote.rs", "eval_value_node"),
    ("src/denote.rs", "f5_ownership_balance"),
    ("src/denote.rs", "fragment2_inst_label"),
    ("src/reflect.rs", "reflect_inst"),
    ("src/scalar_denote.rs", "denote_scalar_function"),
];

/// The one pattern macro a dispatch may use, and the rule it must keep: named
/// `Inst::$variant { .. }` alternatives and nothing else (whitespace-free).
const INSTS_MACRO: &str = "insts";
const INSTS_RULE: &str = "($($variant:ident),+$(,)?)=>{$(Inst::$variant{..})|+};";

/// What one parse found.
#[derive(Debug, Default)]
struct Findings {
    dispatches: BTreeSet<(String, String)>,
    offenders: Vec<String>,
}

struct Scan<'f> {
    file: &'f str,
    fns: Vec<String>,
    found: Findings,
}

impl Scan<'_> {
    fn here(&self) -> String {
        self.fns.last().cloned().unwrap_or_else(|| "<no fn>".into())
    }

    fn refuse(&mut self, what: String) {
        let at = format!("{}: fn {}: {what}", self.file, self.here());
        self.found.offenders.push(at);
    }

    fn check_macro_rules(&mut self, mac: &syn::Macro, name: Option<&syn::Ident>) {
        if !mac.path.is_ident("macro_rules") {
            return;
        }
        let body = mac.tokens.to_string();
        let flat: String = body.split_whitespace().collect();
        if body.split_whitespace().any(|t| t == "match") {
            self.refuse(
                "a `macro_rules!` body contains `match`, which this parse cannot see".into(),
            );
        }
        if name.is_some_and(|n| n == INSTS_MACRO) && flat != INSTS_RULE {
            self.refuse(format!(
                "`insts!` no longer expands to named `Inst::$variant {{ .. }}` alternatives \
                 only: `{body}`"
            ));
        }
    }
}

impl<'ast> Visit<'ast> for Scan<'_> {
    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
        self.fns.push(f.sig.ident.to_string());
        visit::visit_item_fn(self, f);
        self.fns.pop();
    }

    fn visit_impl_item_fn(&mut self, f: &'ast syn::ImplItemFn) {
        self.fns.push(f.sig.ident.to_string());
        visit::visit_impl_item_fn(self, f);
        self.fns.pop();
    }

    fn visit_trait_item_fn(&mut self, f: &'ast syn::TraitItemFn) {
        self.fns.push(f.sig.ident.to_string());
        visit::visit_trait_item_fn(self, f);
        self.fns.pop();
    }

    fn visit_expr_match(&mut self, m: &'ast syn::ExprMatch) {
        if scrutinee_is_inst(&m.expr) || m.arms.iter().any(|a| names_inst(&a.pat)) {
            self.found
                .dispatches
                .insert((self.file.to_string(), self.here()));
            // Every catch-all is refused HERE, whether or not clippy also
            // judges the match: an item- or module-level `#[allow]` /
            // `#[expect]` of clippy's wildcard lints overrides the crate-root
            // `deny` (a default, not a `forbid`). With this rule gated on
            // "names no variant" (54861cbce), `_ =>` in `fragment2_inst_label`
            // under `#[expect(clippy::wildcard_enum_match_arm)]` was refused by
            // nothing (verifier r7, 2026-09-24).
            for (i, arm) in m.arms.iter().enumerate() {
                if wraps(&arm.pat) {
                    self.refuse(format!(
                        "arm {i} `{}` destructures a tuple, slice or non-`Inst` struct around \
                         the `Inst`; which field is the `Inst` is not syntactic, so match the \
                         `Inst` on its own",
                        describe(&arm.pat)
                    ));
                } else if catches_unnamed(&arm.pat) {
                    let guard = if arm.guard.is_some() { " if …" } else { "" };
                    self.refuse(format!(
                        "arm {i} `{}{guard}` can match an `Inst` variant it does not name",
                        describe(&arm.pat)
                    ));
                }
            }
        }
        visit::visit_expr_match(self, m);
    }

    fn visit_item_use(&mut self, u: &'ast syn::ItemUse) {
        let mut hidden = Vec::new();
        use_hides_inst(&u.tree, &mut Vec::new(), &mut hidden);
        for h in hidden {
            self.refuse(h);
        }
        visit::visit_item_use(self, u);
    }

    fn visit_item_type(&mut self, t: &'ast syn::ItemType) {
        if let syn::Type::Path(p) = t.ty.as_ref() {
            if p.path.segments.last().is_some_and(|s| s.ident == "Inst") {
                self.refuse(format!(
                    "`type {} = …Inst` would let a variant be named without `Inst::`",
                    t.ident
                ));
            }
        }
        visit::visit_item_type(self, t);
    }

    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        if type_is_inst(&i.self_ty) {
            self.refuse(
                "an `impl` on `Inst` lets `Self::Variant` name a variant without `Inst::`".into(),
            );
        }
        visit::visit_item_impl(self, i);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if !mac.path.is_ident("macro_rules") && mentions_match(&mac.tokens.to_string()) {
            match mac.parse_body_with(Punctuated::<syn::Expr, Token![,]>::parse_terminated) {
                Ok(args) => {
                    for e in &args {
                        self.visit_expr(e);
                    }
                }
                Err(e) => {
                    let name = mac.path.segments.last().map(|s| s.ident.to_string());
                    self.refuse(format!(
                        "a `{}!` call contains `match` in arguments this parse cannot read ({e})",
                        name.unwrap_or_default()
                    ));
                }
            }
        }
        visit::visit_macro(self, mac);
    }

    fn visit_item_macro(&mut self, m: &'ast syn::ItemMacro) {
        self.check_macro_rules(&m.mac, m.ident.as_ref());
        visit::visit_item_macro(self, m);
    }

    fn visit_stmt_macro(&mut self, m: &'ast syn::StmtMacro) {
        self.check_macro_rules(&m.mac, None);
        visit::visit_stmt_macro(self, m);
    }
}

/// Does `path` name something INSIDE `Inst` (`Inst::X`, `trust_ir::Inst::X`)?
fn path_names_inst(path: &syn::Path) -> bool {
    let segs: Vec<_> = path.segments.iter().collect();
    segs.iter()
        .take(segs.len().saturating_sub(1))
        .any(|s| s.ident == "Inst")
}

/// Does this pattern name an `Inst` variant anywhere (or the `insts!` macro)?
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "syn::Pat is #[non_exhaustive]; a kind not modelled names no variant"
)]
fn names_inst(p: &Pat) -> bool {
    match p {
        Pat::Path(x) => path_names_inst(&x.path),
        Pat::Struct(x) => path_names_inst(&x.path) || x.fields.iter().any(|f| names_inst(&f.pat)),
        Pat::TupleStruct(x) => path_names_inst(&x.path) || x.elems.iter().any(names_inst),
        Pat::Ident(x) => x.subpat.as_ref().is_some_and(|(_, s)| names_inst(s)),
        Pat::Or(x) => x.cases.iter().any(names_inst),
        Pat::Paren(x) => names_inst(&x.pat),
        Pat::Reference(x) => names_inst(&x.pat),
        Pat::Tuple(x) => x.elems.iter().any(names_inst),
        Pat::Slice(x) => x.elems.iter().any(names_inst),
        Pat::Type(x) => names_inst(&x.pat),
        Pat::Macro(x) => x.mac.path.is_ident(INSTS_MACRO),
        _ => false,
    }
}

/// Could this arm pattern match an `Inst` variant it does not name?
///
/// Fail-closed: a pattern kind this does not model answers yes.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "syn::Pat is #[non_exhaustive]; a kind not modelled answers yes (fail-closed)"
)]
fn catches_unnamed(p: &Pat) -> bool {
    match p {
        Pat::Path(_) | Pat::Struct(_) | Pat::TupleStruct(_) | Pat::Lit(_) | Pat::Range(_) => false,
        Pat::Ident(x) => x.subpat.as_ref().is_none_or(|(_, s)| catches_unnamed(s)),
        Pat::Or(x) => x.cases.iter().any(catches_unnamed),
        Pat::Paren(x) => catches_unnamed(&x.pat),
        Pat::Reference(x) => catches_unnamed(&x.pat),
        Pat::Type(x) => catches_unnamed(&x.pat),
        Pat::Macro(x) => !x.mac.path.is_ident(INSTS_MACRO),
        _ => true,
    }
}

/// Does this arm pattern destructure something AROUND the `Inst`: a tuple, a
/// slice, or a struct / tuple struct whose path is not an `Inst` variant?
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "syn::Pat is #[non_exhaustive]; the wrapper kinds are named, the rest wrap nothing"
)]
fn wraps(p: &Pat) -> bool {
    match p {
        Pat::Tuple(_) | Pat::Slice(_) => true,
        Pat::Struct(x) => !path_names_inst(&x.path),
        Pat::TupleStruct(x) => !path_names_inst(&x.path),
        Pat::Ident(x) => x.subpat.as_ref().is_some_and(|(_, s)| wraps(s)),
        Pat::Or(x) => x.cases.iter().any(wraps),
        Pat::Paren(x) => wraps(&x.pat),
        Pat::Reference(x) => wraps(&x.pat),
        Pat::Type(x) => wraps(&x.pat),
        _ => false,
    }
}

/// Is the scrutinee spelled `inst` / `….inst` (behind `&`, `*` or parens)?
/// A match that decides by guards alone (`match n.inst { i if p(i) => …,
/// _ => … }`) names no `Inst` path, so its scrutinee is what makes it one.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "syn::Expr is #[non_exhaustive]; only the named spellings are `inst`"
)]
fn scrutinee_is_inst(e: &syn::Expr) -> bool {
    match e {
        syn::Expr::Path(p) => p.path.is_ident("inst"),
        syn::Expr::Field(f) => matches!(&f.member, syn::Member::Named(i) if i == "inst"),
        syn::Expr::Reference(r) => scrutinee_is_inst(&r.expr),
        syn::Expr::Unary(u) => scrutinee_is_inst(&u.expr),
        syn::Expr::Paren(p) => scrutinee_is_inst(&p.expr),
        _ => false,
    }
}

/// Is this type `Inst` (behind any number of references)?
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "syn::Type is #[non_exhaustive]; only a path names `Inst`"
)]
fn type_is_inst(t: &syn::Type) -> bool {
    match t {
        syn::Type::Path(p) => p.path.segments.last().is_some_and(|s| s.ident == "Inst"),
        syn::Type::Reference(r) => type_is_inst(&r.elem),
        syn::Type::Paren(p) => type_is_inst(&p.elem),
        syn::Type::Group(g) => type_is_inst(&g.elem),
        _ => false,
    }
}

/// Does a macro's token text contain the `match` keyword as a word?
fn mentions_match(text: &str) -> bool {
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .any(|w| w == "match")
}

/// `use` trees that would name `Inst`'s variants without `Inst::`: an import
/// FROM `Inst` (a variant, a group, a glob) or a rename of `Inst` itself.
fn use_hides_inst(tree: &UseTree, prefix: &mut Vec<String>, out: &mut Vec<String>) {
    let inside_inst = prefix.last().is_some_and(|s| s == "Inst");
    match tree {
        UseTree::Path(p) => {
            prefix.push(p.ident.to_string());
            use_hides_inst(&p.tree, prefix, out);
            prefix.pop();
        }
        UseTree::Name(n) if inside_inst => {
            out.push(format!(
                "`use {}::{}` imports an `Inst` variant",
                prefix.join("::"),
                n.ident
            ));
        }
        UseTree::Rename(r) if inside_inst || r.ident == "Inst" => {
            out.push(format!(
                "`use …{} as {}` renames `Inst` or its variant",
                r.ident, r.rename
            ));
        }
        UseTree::Glob(_) if inside_inst => {
            out.push(format!(
                "`use {}::*` imports every `Inst` variant",
                prefix.join("::")
            ));
        }
        UseTree::Group(g) => {
            for t in &g.items {
                use_hides_inst(t, prefix, out);
            }
        }
        UseTree::Name(_) | UseTree::Rename(_) | UseTree::Glob(_) => {}
    }
}

/// A short rendering of an arm pattern for the failure message.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "syn::Pat is #[non_exhaustive]; an unmodelled kind prints as `<pattern>`"
)]
fn describe(p: &Pat) -> String {
    let path = |p: &syn::Path| {
        p.segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("::")
    };
    match p {
        Pat::Wild(_) => "_".into(),
        Pat::Rest(_) => "..".into(),
        Pat::Ident(x) => {
            let r = if x.by_ref.is_some() { "ref " } else { "" };
            let m = if x.mutability.is_some() { "mut " } else { "" };
            let sub = x
                .subpat
                .as_ref()
                .map_or(String::new(), |(_, s)| format!(" @ {}", describe(s)));
            format!("{r}{m}{}{sub}", x.ident)
        }
        Pat::Paren(x) => format!("({})", describe(&x.pat)),
        Pat::Reference(x) => format!("&{}", describe(&x.pat)),
        Pat::Or(x) => x.cases.iter().map(describe).collect::<Vec<_>>().join(" | "),
        Pat::Path(x) => path(&x.path),
        Pat::Struct(x) => format!("{} {{ .. }}", path(&x.path)),
        Pat::TupleStruct(x) => format!("{}(..)", path(&x.path)),
        Pat::Macro(x) => format!("{}!(..)", path(&x.mac.path)),
        Pat::Tuple(_) => "(..)".into(),
        _ => "<pattern>".into(),
    }
}

/// Parse one file's source and scan it.
fn scan(file: &str, src: &str) -> Findings {
    let ast = syn::parse_file(src).unwrap_or_else(|e| panic!("{file} does not parse: {e}"));
    let mut s = Scan {
        file,
        fns: Vec::new(),
        found: Findings::default(),
    };
    s.visit_file(&ast);
    s.found
}

/// Every `.rs` file under `dir`, recursively, skipping any `target/`.
fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("a directory entry").path();
        if path.is_dir() {
            if path.file_name().is_some_and(|n| n == "target") {
                continue;
            }
            rust_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
}

/// The directories cargo builds a target from: the library and binaries,
/// integration tests, benches and examples.
const TARGET_DIRS: [&str; 4] = ["src", "tests", "benches", "examples"];

/// Every source file the dispatch parse reads: every `.rs` under every target
/// directory of the crate, sorted.
fn scanned_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for target in TARGET_DIRS {
        if root.join(target).is_dir() {
            rust_files(&root.join(target), &mut files);
        }
    }
    files.sort();
    files
}

/// `path` relative to the crate root, `/`-separated.
fn rel(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .expect("under the crate")
        .to_string_lossy()
        .replace('\\', "/")
}

#[test]
fn every_inst_dispatch_names_its_variants() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut all = Findings::default();
    for path in &scanned_files(root) {
        let rel = rel(root, path);
        let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let found = scan(&rel, &src);
        all.dispatches.extend(found.dispatches);
        all.offenders.extend(found.offenders);
    }
    assert!(
        all.offenders.is_empty(),
        "an `Inst` dispatch can match a variant it does not name, so a variant trust-ir adds \
         would compile unchanged and be handled or refused unseen; name the variants instead:\n  {}",
        all.offenders.join("\n  ")
    );
    let expected: BTreeSet<(String, String)> = EXPECTED_DISPATCHES
        .iter()
        .map(|(f, n)| ((*f).to_string(), (*n).to_string()))
        .collect();
    assert_eq!(
        all.dispatches, expected,
        "the `Inst` dispatches the parse found are not the pinned set; a dispatch it cannot see \
         is one it cannot check, and a new one belongs in EXPECTED_DISPATCHES"
    );
}

/// The parse reads EVERY Rust file of the crate, not only `src/`: measured
/// 2026-09-24, the r6 verifier cut the target list back to `src` and every
/// test here still passed, because nothing asked what was read. Derived from
/// the tree -- every `.rs` under the crate root outside `target/` -- so a new
/// target directory, or a file outside every target directory, fails here
/// until the scan reads it.
#[test]
fn the_scan_reads_every_rust_file_of_every_target() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut everything = Vec::new();
    rust_files(root, &mut everything);
    let everything: BTreeSet<String> = everything.iter().map(|p| rel(root, p)).collect();
    let scanned: BTreeSet<String> = scanned_files(root).iter().map(|p| rel(root, p)).collect();
    assert_eq!(
        scanned, everything,
        "the dispatch parse does not read every Rust file of the crate"
    );
    for (dir, why) in [
        ("tests", "integration tests are targets of their own"),
        ("src", "the library"),
    ] {
        assert!(
            scanned.iter().any(|f| f.starts_with(&format!("{dir}/"))),
            "{dir}/ is not scanned ({why})"
        );
    }
}

/// The lints every target root denies, as the crate root spells them.
const ROOT_DENIES: [&str; 3] = [
    "clippy::wildcard_enum_match_arm",
    "clippy::match_wildcard_for_single_variants",
    "clippy::wildcard_in_or_patterns",
];

/// The lint paths a file's inner `#![deny(…)]` attributes name.
fn inner_denies(src: &str) -> BTreeSet<String> {
    let ast = syn::parse_file(src).expect("a target root parses");
    let mut out = BTreeSet::new();
    for attr in &ast.attrs {
        if !matches!(attr.style, syn::AttrStyle::Inner(_)) || !attr.path().is_ident("deny") {
            continue;
        }
        let paths = attr
            .parse_args_with(Punctuated::<syn::Path, Token![,]>::parse_terminated)
            .expect("a deny list of lint paths");
        for path in paths {
            let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
            out.insert(segs.join("::"));
        }
    }
    out
}

/// Clippy's half only runs where the attribute is: an integration test, a
/// bench or an example is its OWN crate root, and one that dropped the deny
/// would be linted by nothing. Every root carries all three.
#[test]
fn every_target_root_denies_the_wildcard_lints() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut roots = vec![root.join("src/lib.rs")];
    for dir in ["tests", "benches", "examples"] {
        let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("a directory entry").path();
            if path.extension().is_some_and(|x| x == "rs") {
                roots.push(path);
            } else if path.join("main.rs").is_file() {
                roots.push(path.join("main.rs"));
            }
        }
    }
    assert!(roots.len() > 1, "no integration-test root found: {roots:?}");
    for path in &roots {
        let src = std::fs::read_to_string(path).expect("a target root reads");
        let denied = inner_denies(&src);
        let missing: Vec<&str> = ROOT_DENIES
            .iter()
            .copied()
            .filter(|l| !denied.contains(*l))
            .collect();
        assert!(
            missing.is_empty(),
            "{} does not deny {missing:?}: clippy's exhaustive-dispatch check does not run \
             in that target",
            rel(root, path)
        );
    }
    // The instrument, both ways.
    assert!(
        inner_denies("#![deny(clippy::wildcard_enum_match_arm)]\nfn f() {}")
            .contains("clippy::wildcard_enum_match_arm")
    );
    assert!(inner_denies("#[deny(clippy::wildcard_enum_match_arm)]\nfn f() {}").is_empty());
}

/// The instrument itself, on source it has to get right. A catch-all in an
/// `Inst` dispatch is refused here, in every spelling, whether or not an arm
/// names a variant (clippy judges the latter too, but an item-level
/// `#[allow]` / `#[expect]` silences clippy and not this parse); and the
/// crate-wide refusals that keep the parse's own view honest fire.
#[test]
fn the_dispatch_parse_discriminates() {
    let found = |body: &str| -> Vec<String> {
        let src = format!("fn d(inst: &Inst, g: bool) -> u8 {{ match inst {{ {body} }} }}");
        scan("t.rs", &src).offenders
    };
    for catch_all in [
        "other => 1,",
        "_ => 1,",
        "ref other => 1,",
        "mut other => 1,",
        "other @ _ => 1,",
        "other @ (_) => 1,",
        "(other) => 1,",
        "&other => 1,",
        "other if g => 1,",
        "other @ any!() => 1,",
        "other @ (x @ _) => 1,",
    ] {
        assert_eq!(
            found(catch_all).len(),
            1,
            "`{catch_all}` in a match naming no variant must be refused once"
        );
        assert_eq!(
            found(&format!("Inst::Br {{ .. }} => 0, {catch_all}")).len(),
            1,
            "`{catch_all}` beside a named arm must be refused here too: clippy's verdict \
             can be silenced by an item-level allow/expect"
        );
    }
    for named in [
        "Inst::Br { .. } => 0, Inst::Call { .. } | Inst::NullPtr => 1,",
        "Inst::Br { .. } => 0, other @ insts!(Call, NullPtr) => 1,",
        "Inst::Overflow { op: _, .. } => 0, trust_ir::Inst::Br(..) => 1,",
        "Inst::Br { .. } => match g { true => 0, _ => 1 },",
    ] {
        assert!(found(named).is_empty(), "`{named}` names its variants");
    }
    // Verifier r7 (2026-09-24): a catch-all beside a named arm, with clippy's
    // wildcard lint EXPECTED or ALLOWED on the item or its module, lints clean
    // -- the parse must still refuse it. The first is the measured plant: the
    // named arms of `fragment2_inst_label` replaced by `_`, the fn expecting
    // the lint.
    for silenced in [
        "#[expect(clippy::wildcard_enum_match_arm, reason = \"x\")] \
         fn d(inst: &Inst) -> u8 { match inst { Inst::Br { .. } => 0, _ => 1 } }",
        "#[allow(clippy::wildcard_enum_match_arm)] \
         fn d(inst: &Inst) -> u8 { match inst { Inst::Br { .. } => 0, other => 1 } }",
        "mod m { #![allow(clippy::wildcard_enum_match_arm)] \
         fn d(inst: &Inst) -> u8 { match inst { Inst::Br { .. } => 0, _ => 1 } } }",
    ] {
        let f = scan("t.rs", silenced);
        assert_eq!(f.offenders.len(), 1, "`{silenced}`: {f:?}");
    }
    // The scrutinee's spelling does not matter: the arms identify a dispatch.
    let src = "fn e(n: &N) -> u8 { let t = &n.inst; match t { Inst::Br { .. } => 0, \
               Inst::Call { .. } => 1 } }";
    let f = scan("t.rs", src);
    assert!(f.offenders.is_empty(), "{f:?}");
    assert!(f.dispatches.contains(&("t.rs".into(), "e".into())));
    // A match that names no Inst path over a scrutinee not spelled `inst` is
    // not a dispatch.
    assert!(scan(
        "t.rs",
        "fn f(o: Option<u8>) -> u8 { match o { Some(_) => 0, _ => 1 } }"
    )
    .dispatches
    .is_empty());
    for (hidden, why) in [
        ("use trust_ir::Inst::*;", "glob of Inst's variants"),
        (
            "use trust_ir::inst::Inst::{Br, Call};",
            "Inst variants by name",
        ),
        ("use trust_ir::Inst as I;", "a renamed Inst"),
        ("type I = trust_ir::Inst;", "an alias of Inst"),
        (
            "macro_rules! d { ($x:expr) => { match $x { _ => 0 } }; }",
            "a match in a macro",
        ),
        (
            "macro_rules! insts { ($($v:ident),+) => { _ }; }",
            "an insts! that expands to a wildcard",
        ),
        (
            "fn g() { macro_rules! h { () => { match 0 { _ => 0 } }; } }",
            "a statement macro_rules",
        ),
    ] {
        assert!(
            !scan("t.rs", hidden).offenders.is_empty(),
            "{why}: `{hidden}`"
        );
    }
    assert!(scan(
        "t.rs",
        "use trust_ir::inst::{Inst, BinOp}; use trust_ir::Inst;"
    )
    .offenders
    .is_empty());
    let vetted =
        "macro_rules! insts { ($($variant:ident),+ $(,)?) => { $(Inst::$variant { .. })|+ }; }";
    assert!(scan("t.rs", vetted).offenders.is_empty());
}

/// Dispatches clippy's type-based lint does not judge, each measured: a
/// catch-all one level down, inside a wrapper around the `Inst` (`Ok(..)` in
/// `fragment2_inst_label`, `InstrNode { .. }` in `eval_heap_node`, measured
/// on the real crate before 0d9e23736 -- clippy fired on neither); a
/// guard-only match over `….inst`; a wrapped dispatch inside a macro call's
/// arguments; and `Self::Variant` in an `impl` on `Inst`.
#[test]
fn the_dispatch_parse_sees_wrapped_and_hidden_dispatches() {
    // A catch-all one level down, around the `Inst`, is refused: clippy sees
    // the wrapper's type, not `Inst`.
    for (wrapped, why) in [
        (
            "fn d(x: Result<&Inst, ()>) -> u8 { match x { Ok(Inst::Br { .. }) => 0, Ok(..) => 1, \
             Err(()) => 2 } }",
            "`Ok(..)` around the Inst",
        ),
        (
            "fn d(n: &N) -> u8 { match n { N { inst: Inst::Br { .. }, .. } => 0, N { .. } => 1 } }",
            "a struct around the Inst",
        ),
        (
            "fn d(n: &N) -> u8 { match n { N { inst: Inst::Br { .. }, .. } => 0, \
             N { inst: _, .. } => 1 } }",
            "a struct whose Inst field is a wildcard",
        ),
        (
            "fn d(i: &Inst, b: bool) -> u8 { match (i, b) { (Inst::Br { .. }, _) => 0, \
             (_, true) => 1, (_, false) => 2 } }",
            "a tuple around the Inst",
        ),
    ] {
        let f = scan("t.rs", wrapped);
        assert!(!f.offenders.is_empty(), "{why}: `{wrapped}`");
        assert!(
            f.dispatches.contains(&("t.rs".into(), "d".into())),
            "{why}: {f:?}"
        );
    }
    // A match over a scrutinee spelled `….inst` is a dispatch even when no
    // arm names an `Inst` path -- and clippy does not judge it -- so its guard
    // binding and its `_` are refused.
    let f = scan(
        "t.rs",
        "fn g(n: &N) -> u8 { match &n.inst { i if is_call(i) => 0, _ => 1 } }",
    );
    assert_eq!(f.offenders.len(), 2, "{f:?}");
    assert!(f.dispatches.contains(&("t.rs".into(), "g".into())), "{f:?}");
    // A dispatch inside a macro call's arguments is scanned, not skipped: a
    // catch-all there is refused, wrapped or at top level.
    let f = scan(
        "t.rs",
        "fn m(x: Result<&Inst, ()>) -> Vec<u8> { vec![match x { Ok(Inst::Br { .. }) => 0, \
         Ok(..) => 1, Err(()) => 2 }] }",
    );
    assert!(
        f.offenders.iter().any(|o| o.contains("arm 1 `Ok(..)`")),
        "{f:?}"
    );
    assert!(f.dispatches.contains(&("t.rs".into(), "m".into())), "{f:?}");
    let f = scan(
        "t.rs",
        "fn m(x: &Inst) -> String { format!(\"{}\", match x { Inst::Br { .. } => 0, \
         Inst::Call { .. } => 1 }) }",
    );
    assert!(
        f.offenders.is_empty(),
        "a named dispatch in a macro call passes: {f:?}"
    );
    assert!(f.dispatches.contains(&("t.rs".into(), "m".into())), "{f:?}");
    for (hidden, why) in [
        (
            "impl T for trust_ir::Inst { fn f(&self) -> u8 { match self { Self::Br { .. } => 0, \
             _ => 1 } } }",
            "an impl on Inst, where Self:: names a variant",
        ),
        (
            "fn g(x: &Inst) -> Vec<u8> { vec![match x { _ => 1 }; 3] }",
            "a match in macro arguments that do not parse as expressions",
        ),
    ] {
        assert!(
            !scan("t.rs", hidden).offenders.is_empty(),
            "{why}: `{hidden}`"
        );
    }
}
