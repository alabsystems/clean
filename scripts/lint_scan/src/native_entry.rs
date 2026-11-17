// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One syntax contract, selected explicitly for the typed scanner's own root.
//! This grants no SDK identity or execution evidence. The owner also requires
//! the actual test-compilation witness and the complete original test suite.
//! A scoped exemption never adds an attribute or identifier to the general
//! source model. All other files and all other nodes retain that model.

use std::collections::BTreeSet;
use std::str::FromStr;

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{Attribute, Item};

pub(super) const CALLBACK: &str = "lint_types_native_test_entry";
const FEATURE: &str = "cfg_attr(test, feature(test, custom_test_frameworks, exitcode_exit_method))";
const RUNNER: &str = "cfg_attr(test, test_runner(lint_types_native_test_entry))";
#[cfg(test)]
const TEST_EXTERN: &str = "#[cfg(test)] extern crate test;";
const PROTECTED: &[&str] = &[
    "std",
    "core",
    "test",
    "rustc_data_structures",
    "Err",
    "Ok",
    "lint_types_native_test_entry",
];

// Tokens, not spelling/layout/comments, define this fixed control flow. In
// particular capture is the first operation; both branches forward the same
// immutable parameter; and the genuine ExitCode is consumed by a diverging
// method. Resolved identities and synthesized-harness origins are checked by
// lint_types during the ACTUAL test compilation, not inferred from this text.
pub(super) const ENTRY: &str = r#"
fn lint_types_native_test_entry(tests: &[&test::TestDescAndFn]) {
    if let Err(error) =
        unsafe { rustc_data_structures::jobserver::capture_early_for_test_harness() }
    {
        eprintln!("lint-types test entry: inherited compiler scheduler refused: {error}");
        std::process::exit(75);
    }
    let sdk_loan = rustc_data_structures::jobserver::lends_own_execution();
    let test_threads = std::env::var_os("RUST_TEST_THREADS");
    eprintln!("lint-types test entry policy: sdk_loan={sdk_loan}, RUST_TEST_THREADS={test_threads:?}");
    #[cfg(panic = "unwind")]
    let result = test::test_main_env_args(tests);
    #[cfg(not(panic = "unwind"))]
    let result = test::test_main_env_args_abort(tests);
    result.exit_process();
}
"#;

type Location = (usize, usize, usize, usize);

fn location(span: Span) -> Location {
    let start = span.start();
    let end = span.end();
    (start.line, start.column, end.line, end.column)
}

/// Node identities are parser locations from this SAME parsed file. Never
/// reuse them across files or parse passes, nor exempt a feature by its name.
#[derive(Default)]
pub(super) struct Exemptions {
    attributes: BTreeSet<Location>,
    test_extern: Option<Location>,
}

impl Exemptions {
    pub(super) fn attribute(&self, attr: &Attribute) -> bool {
        self.attributes.contains(&location(attr.span()))
    }

    pub(super) fn test_extern(&self, item: &syn::ItemExternCrate) -> bool {
        self.test_extern == Some(location(item.span()))
    }
}

fn normalized(text: &str) -> Result<String, String> {
    TokenStream::from_str(text)
        .map(|tokens| tokens.to_string())
        .map_err(|error| format!("native entry tokens cannot be read: {error}"))
}

fn attribute_is(attr: &Attribute, expected: &str) -> bool {
    // All admitted special attributes are lists. Comparing the path and the
    // recursively tokenized argument stream rejects aliases and extra args.
    if let syn::Meta::List(list) = &attr.meta {
        let text = format!("{}({})", super::path_text(&list.path), list.tokens);
        return normalized(&text).ok() == normalized(expected).ok();
    }
    false
}

fn inherited(visibility: &syn::Visibility) -> bool {
    if let syn::Visibility::Inherited = visibility {
        return true;
    }
    false
}

fn one_attribute(attrs: &[Attribute], expected: &str) -> bool {
    attrs.len() == 1 && attribute_is(&attrs[0], expected)
}

/// Top-level function tokens through its body, excluding attributes. Groups
/// are opaque here, so a matching name inside a string/macro/nested module
/// never supplies the top-level callback. The AST validates its declaration.
fn callback_tokens(text: &str) -> Result<String, String> {
    let tokens: Vec<TokenTree> = TokenStream::from_str(text)
        .map_err(|error| format!("native entry tokens cannot be read: {error}"))?
        .into_iter()
        .collect();
    let mut found = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        let TokenTree::Ident(keyword) = token else {
            continue;
        };
        if keyword != "fn" {
            continue;
        }
        let Some(TokenTree::Ident(name)) = tokens.get(index + 1) else {
            continue;
        };
        if name != CALLBACK {
            continue;
        }
        let mut body_end = None;
        for (offset, next) in tokens[index + 2..].iter().enumerate() {
            if let TokenTree::Group(group) = next {
                if group.delimiter() == Delimiter::Brace {
                    body_end = Some(index + 2 + offset + 1);
                    break;
                }
            }
        }
        let end = body_end.ok_or("native entry callback has no body")?;
        let function: TokenStream = tokens[index..end].iter().cloned().collect();
        found.push(function.to_string());
    }
    if found.len() != 1 {
        return Err("native entry needs exactly one top-level callback".to_string());
    }
    found
        .pop()
        .ok_or_else(|| "native entry callback disappeared".to_string())
}

struct Namespace<'a> {
    callback: Location,
    data_structures: Location,
    test_extern: Location,
    errors: &'a mut Vec<String>,
}

impl Namespace<'_> {
    fn binding(&mut self, ident: &syn::Ident) {
        let name = ident.unraw().to_string();
        if PROTECTED.contains(&name.as_str()) {
            self.errors
                .push(format!("native entry reserved binding `{name}`"));
        }
    }

    fn import(&mut self, tree: &syn::UseTree, parent: Option<&syn::Ident>) {
        match tree {
            syn::UseTree::Path(path) => self.import(&path.tree, Some(&path.ident)),
            syn::UseTree::Name(name) => {
                if name.ident == "self" {
                    if let Some(parent) = parent {
                        self.binding(parent);
                    }
                } else {
                    self.binding(&name.ident);
                }
            }
            syn::UseTree::Rename(rename) => self.binding(&rename.rename),
            syn::UseTree::Glob(_) => self
                .errors
                .push("native entry forbids glob imports".to_string()),
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.import(item, parent);
                }
            }
        }
    }
}

impl<'ast> Visit<'ast> for Namespace<'_> {
    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        self.import(&item.tree, None);
        visit::visit_item_use(self, item);
    }

    fn visit_item_extern_crate(&mut self, item: &'ast syn::ItemExternCrate) {
        let here = location(item.span());
        if here != self.test_extern && here != self.data_structures {
            self.binding(item.rename.as_ref().map_or(&item.ident, |(_, name)| name));
        }
        visit::visit_item_extern_crate(self, item);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if location(item.span()) != self.callback {
            self.binding(&item.sig.ident);
        }
        visit::visit_item_fn(self, item);
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.binding(&item.ident);
        visit::visit_item_mod(self, item);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.binding(&item.ident);
        visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.binding(&item.ident);
        visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.binding(&item.ident);
        visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.binding(&item.ident);
        visit::visit_item_type(self, item);
    }

    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        self.binding(&item.ident);
        visit::visit_item_const(self, item);
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        self.binding(&item.ident);
        visit::visit_item_static(self, item);
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.binding(&item.ident);
        visit::visit_item_trait(self, item);
    }
}

struct PanicAttributes<'a>(&'a mut Exemptions);

impl<'ast> Visit<'ast> for PanicAttributes<'_> {
    fn visit_attribute(&mut self, attr: &'ast Attribute) {
        if attribute_is(attr, "cfg(panic = \"unwind\")")
            || attribute_is(attr, "cfg(not(panic = \"unwind\"))")
        {
            self.0.attributes.insert(location(attr.span()));
        }
        visit::visit_attribute(self, attr);
    }
}

/// Check the WHOLE selected root before exempting any of its syntax. The
/// generic model runs too, so an unrelated constructor, include, macro,
/// feature, cfg or custom attribute still refuses at its original boundary.
pub(super) fn check(file: &syn::File, text: &str) -> Result<Exemptions, String> {
    let feature: Vec<_> = file
        .attrs
        .iter()
        .filter(|a| attribute_is(a, FEATURE))
        .collect();
    let runner: Vec<_> = file
        .attrs
        .iter()
        .filter(|a| attribute_is(a, RUNNER))
        .collect();
    if feature.len() != 1 || runner.len() != 1 {
        return Err(
            "native entry needs its exact single cfg(test) feature and runner attributes"
                .to_string(),
        );
    }
    let mut callback = Vec::new();
    let mut test_extern = Vec::new();
    let mut data_structures = Vec::new();
    let mut main = Vec::new();
    for item in &file.items {
        if let Item::Fn(function) = item {
            if function.sig.ident == CALLBACK {
                callback.push(function);
            }
            if function.sig.ident == "main" {
                main.push(function);
            }
        }
        if let Item::ExternCrate(extern_crate) = item {
            if extern_crate.ident == "test" {
                test_extern.push(extern_crate);
            }
            if extern_crate.ident == "rustc_data_structures" {
                data_structures.push(extern_crate);
            }
        }
    }
    if callback.len() != 1
        || test_extern.len() != 1
        || data_structures.len() != 1
        || main.len() != 1
    {
        return Err(
            "native entry needs exactly one callback, test extern, SDK extern and production main"
                .to_string(),
        );
    }
    let callback = callback[0];
    if !one_attribute(&callback.attrs, "cfg(test)")
        || !one_attribute(&main[0].attrs, "cfg(not(test))")
        || !one_attribute(&test_extern[0].attrs, "cfg(test)")
        || !inherited(&test_extern[0].vis)
        || !inherited(&callback.vis)
        || !inherited(&data_structures[0].vis)
        || test_extern[0].rename.is_some()
        || !data_structures[0].attrs.is_empty()
        || data_structures[0].rename.is_some()
        || callback.sig.constness.is_some()
        || callback.sig.asyncness.is_some()
        || callback.sig.unsafety.is_some()
        || callback.sig.abi.is_some()
        || !callback.sig.generics.params.is_empty()
        || callback.sig.generics.where_clause.is_some()
        || callback.sig.variadic.is_some()
        || callback_tokens(text)? != normalized(ENTRY)?
    {
        return Err("native entry must retain the exact first capture, Err75, original slice, panic branches and exit".to_string());
    }
    // The exact body token comparison includes all local attributes. The
    // two panic cfg nodes below are the ONLY extra predicate exemptions.
    let mut exemptions = Exemptions::default();
    exemptions.attributes.insert(location(feature[0].span()));
    exemptions.attributes.insert(location(runner[0].span()));
    exemptions.test_extern = Some(location(test_extern[0].span()));
    PanicAttributes(&mut exemptions).visit_item_fn(callback);
    let mut errors = Vec::new();
    Namespace {
        callback: location(callback.span()),
        data_structures: location(data_structures[0].span()),
        test_extern: location(test_extern[0].span()),
        errors: &mut errors,
    }
    .visit_file(file);
    if !errors.is_empty() {
        return Err(errors.join("; "));
    }
    Ok(exemptions)
}

#[cfg(test)]
mod tests {
    use super::{ENTRY, FEATURE, RUNNER, TEST_EXTERN};

    fn fixture() -> String {
        format!("#![feature(rustc_private)]\n#![{FEATURE}]\n#![{RUNNER}]\nextern crate rustc_data_structures;\n{TEST_EXTERN}\n#[cfg(not(test))] fn main() {{}}\n#[cfg(test)]\n{ENTRY}")
    }

    fn scan(source: &str, enabled: bool) -> Vec<String> {
        super::super::scan_with_native_entry("fixture.rs", source, &Default::default(), enabled)
    }

    fn refuses(source: &str, needle: &str) {
        let found = scan(source, true);
        assert!(
            found.iter().any(|line| line.contains(needle)),
            "expected {needle}, got {found:?}"
        );
    }

    #[test]
    fn exact_entry_has_only_scoped_exemptions() {
        assert!(scan(&fixture(), true).is_empty());
        assert!(!scan(&fixture(), false).is_empty());
    }

    #[test]
    fn missing_capture_is_refused() {
        refuses(
            &fixture().replace("capture_early_for_test_harness", "capture_early"),
            "exact first capture",
        );
    }

    #[test]
    fn capture_after_argument_handling_is_refused() {
        refuses(
            &fixture().replace(
                "    if let Err(error)",
                "    let _args = std::env::args();\n    if let Err(error)",
            ),
            "exact first capture",
        );
    }

    #[test]
    fn capture_after_io_or_late_helper_is_refused() {
        refuses(
            &fixture().replace(
                "    if let Err(error)",
                "    eprintln!(\"early\");\n    if let Err(error)",
            ),
            "exact first capture",
        );
        refuses(
            &fixture().replace(
                "unsafe { rustc_data_structures::jobserver::capture_early_for_test_harness() }",
                "late_capture()",
            ),
            "exact first capture",
        );
    }

    #[test]
    fn wrong_callback_signature_or_target_is_refused() {
        refuses(
            &fixture().replace(
                "tests: &[&test::TestDescAndFn]",
                "mut tests: &[&test::TestDescAndFn]",
            ),
            "exact first capture",
        );
        refuses(
            &fixture().replace(
                "test_runner(lint_types_native_test_entry)",
                "test_runner(other)",
            ),
            "exact single",
        );
        refuses(
            &fixture().replace(ENTRY, &format!("mod nested {{ {ENTRY} }}")),
            "exactly one callback",
        );
        refuses(
            &(fixture().replace("fn lint_types_native_test_entry", "fn alternate_entry")
                + "\n#[cfg(test)] use alternate_entry as lint_types_native_test_entry;"),
            "exactly one callback",
        );
    }

    #[test]
    fn empty_and_subset_slices_are_refused() {
        refuses(
            &fixture().replace("test_main_env_args(tests)", "test_main_env_args(&[])"),
            "exact first capture",
        );
        refuses(
            &fixture().replace(
                "test_main_env_args(tests)",
                "test_main_env_args(&tests[1..])",
            ),
            "exact first capture",
        );
    }

    #[test]
    fn reordered_or_filtered_descriptor_forwarding_is_refused() {
        refuses(
            &fixture().replace(
                "test_main_env_args(tests)",
                "test_main_env_args(tests.iter().rev().copied().collect())",
            ),
            "exact first capture",
        );
    }

    #[test]
    fn swallowed_or_constant_success_is_refused() {
        refuses(
            &fixture().replace("result.exit_process();", "let _ = result;"),
            "exact first capture",
        );
        refuses(
            &fixture().replace("result.exit_process();", "std::process::exit(0);"),
            "exact first capture",
        );
    }

    #[test]
    fn result_err_inversion_alias_is_refused() {
        refuses(
            &(fixture() + "\nuse core::result::Result::Ok as Err;"),
            "reserved binding `Err`",
        );
    }

    #[test]
    fn api_alias_or_shadowed_sdk_namespace_is_refused() {
        refuses(
            &(fixture() + "\nuse counterfeit as rustc_data_structures;"),
            "reserved binding",
        );
        refuses(&(fixture() + "\nmod std {}"), "reserved binding `std`");
        refuses(
            &(fixture() + "\nmod nested { extern crate counterfeit as test; }"),
            "reserved binding `test`",
        );
    }

    #[test]
    fn entry_attrs_do_not_enable_unrelated_features_or_runners() {
        refuses(
            &(fixture() + "\n#[test_runner(other)] fn other() {}"),
            "the attribute `#[test_runner]`",
        );
        refuses(
            &(fixture() + "\n#[cfg_attr(test, feature(box_patterns))] fn other() {}"),
            "other than `rustc_private`",
        );
        refuses(
            &(fixture() + "\n#[cfg(panic = \"unwind\")] fn other() {}"),
            "the predicate",
        );
    }

    #[test]
    fn duplicate_or_missing_scope_nodes_are_refused() {
        refuses(
            &(fixture() + "\n#[cfg(test)] extern crate test;"),
            "exactly one",
        );
        refuses(&fixture().replace(TEST_EXTERN, ""), "exactly one");
        refuses(
            &(fixture() + &format!("\n#![{RUNNER}]")),
            "cannot be parsed",
        );
    }

    #[test]
    fn hidden_custom_entry_or_forged_harness_markers_stay_refused() {
        refuses(
            &(fixture() + "\n#[reexport_test_harness_main = \"hidden\"] fn other() {}"),
            "the attribute `#[reexport_test_harness_main]`",
        );
        refuses(
            &(fixture() + "\n#[rustc_test_marker = \"x\"] fn other() {}"),
            "the attribute `#[rustc_test_marker]`",
        );
        refuses(
            &(fixture() + "\n#[test_case] fn other() {}"),
            "the attribute `#[test_case]`",
        );
    }

    #[test]
    fn constructor_or_source_rewriting_stays_refused() {
        refuses(
            &(fixture()
                + "\n#[used] #[link_section = \"init\"] static INIT: fn() = init; fn init() {}"),
            "the attribute `#[used]`",
        );
        refuses(
            &(fixture() + "\ninclude!(\"other.rs\");"),
            "the macro `include!`",
        );
    }
}
