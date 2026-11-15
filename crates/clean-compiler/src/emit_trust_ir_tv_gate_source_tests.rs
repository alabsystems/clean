// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Syntax-aware inspection of the minter's license construction sites.

use syn::visit::{self, Visit};
use syn::{Attribute, Expr, Item, Pat};

#[derive(Clone, Copy, Debug)]
pub(crate) struct LicenseSite {
    pub certified_arm: bool,
    pub obligation: bool,
    pub certificate: bool,
}

fn path_is(path: &syn::Path, names: &[&str]) -> bool {
    path.segments.len() == names.len()
        && path
            .segments
            .iter()
            .zip(names)
            .all(|(segment, name)| segment.ident == *name)
}

fn path_ends_with(path: &syn::Path, names: &[&str]) -> bool {
    path.segments.len() >= names.len()
        && path
            .segments
            .iter()
            .skip(path.segments.len() - names.len())
            .zip(names)
            .all(|(segment, name)| segment.ident == *name)
}

fn test_only(attributes: &[Attribute]) -> bool {
    attributes.iter().any(|attribute| {
        attribute.path().is_ident("cfg")
            && attribute
                .parse_args::<syn::Path>()
                .is_ok_and(|path| path.is_ident("test"))
    })
}

fn attributes(item: &Item) -> &[Attribute] {
    match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::ExternCrate(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::ForeignMod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::TraitAlias(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Use(item) => &item.attrs,
        _ => panic!("license-site guard encountered an unsupported Rust item"),
    }
}

#[derive(Default)]
struct Pushes {
    obligation: bool,
    certificate: bool,
}

impl<'ast> Visit<'ast> for Pushes {
    fn visit_item(&mut self, _: &'ast Item) {
        // A nested item does not execute with the containing match arm.
    }

    fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
        if call.method == "push" && call.args.len() == 1 {
            if let (Expr::Field(field), Some(Expr::Path(argument))) =
                (call.receiver.as_ref(), call.args.first())
            {
                if let Expr::Path(receiver) = field.base.as_ref() {
                    if path_is(&receiver.path, &["module"]) {
                        self.obligation |= matches!(&field.member, syn::Member::Named(name) if name == "proof_obligations")
                            && path_is(&argument.path, &["obligation"]);
                        self.certificate |= matches!(&field.member, syn::Member::Named(name) if name == "proof_certificates")
                            && path_is(&argument.path, &["cert"]);
                    }
                }
            }
        }
        visit::visit_expr_method_call(self, call);
    }
}

#[derive(Default)]
struct Sites {
    arm: Option<LicenseSite>,
    sites: Vec<LicenseSite>,
}

impl<'ast> Visit<'ast> for Sites {
    fn visit_item(&mut self, item: &'ast Item) {
        if !test_only(attributes(item)) {
            visit::visit_item(self, item);
        }
    }

    fn visit_item_fn(&mut self, function: &'ast syn::ItemFn) {
        let outer = self.arm.take();
        visit::visit_item_fn(self, function);
        self.arm = outer;
    }

    fn visit_arm(&mut self, arm: &'ast syn::Arm) {
        let outer = self.arm;
        let path = match &arm.pat {
            Pat::Struct(pattern) => Some(&pattern.path),
            Pat::TupleStruct(pattern) => Some(&pattern.path),
            Pat::Path(pattern) => Some(&pattern.path),
            _ => None,
        };
        if path.is_some_and(|path| {
            path.segments
                .iter()
                .rev()
                .nth(1)
                .is_some_and(|s| s.ident == "Attempt")
        }) {
            let mut pushes = Pushes::default();
            pushes.visit_expr(&arm.body);
            self.arm = Some(LicenseSite {
                certified_arm: path
                    .is_some_and(|path| path_ends_with(path, &["Attempt", "Certified"])),
                obligation: pushes.obligation,
                certificate: pushes.certificate,
            });
        }
        visit::visit_arm(self, arm);
        self.arm = outer;
    }

    fn visit_expr_struct(&mut self, expression: &'ast syn::ExprStruct) {
        if path_ends_with(&expression.path, &["BodyGate", "Gated"]) {
            self.sites.push(self.arm.unwrap_or(LicenseSite {
                certified_arm: false,
                obligation: false,
                certificate: false,
            }));
        }
        visit::visit_expr_struct(self, expression);
    }

    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        assert!(
            !invocation.tokens.to_string().contains("BodyGate :: Gated"),
            "license-site guard cannot inspect a BodyGate::Gated inside a macro"
        );
        visit::visit_macro(self, invocation);
    }
}

pub(crate) fn gated_sites(source: &str) -> Vec<LicenseSite> {
    let file = syn::parse_file(source).expect("license-site guard requires valid Rust syntax");
    let mut sites = Sites::default();
    sites.visit_file(&file);
    sites.sites
}

#[test]
fn test_only_import_and_helper_do_not_hide_later_production() {
    let source = r#"
        #[cfg(test)] use crate::test_helper;
        #[cfg(test)] fn oracle() { let _ = BodyGate::Gated {}; }
        #[cfg(test)] mod tests { fn oracle() { let _ = BodyGate::Gated {}; } }
        fn production() { let _ = BodyGate::Gated {}; }
    "#;
    assert_eq!(gated_sites(source).len(), 1);
}

#[test]
fn comments_strings_and_test_modules_cannot_invent_a_production_site() {
    let source = r#"
        // BodyGate::Gated {}
        const NOTE: &str = "BodyGate::Gated {}";
        #[cfg(test)] mod tests { fn oracle() { let _ = BodyGate::Gated {}; } }
        fn production() {}
    "#;
    assert!(gated_sites(source).is_empty());
}

#[test]
fn gate_outside_certified_arm_is_not_licensed() {
    let sites = gated_sites("fn production() { let _ = BodyGate::Gated {}; }");
    assert_eq!(sites.len(), 1);
    assert!(!sites[0].certified_arm);
    assert_eq!(
        gated_sites("fn production() { let _ = trust_ir::BodyGate::Gated {}; }").len(),
        1
    );
}

#[test]
#[should_panic(expected = "cannot inspect a BodyGate::Gated inside a macro")]
fn macro_cannot_hide_a_license_site() {
    let _ = gated_sites("fn production() { install!(BodyGate::Gated {}); }");
}

#[test]
fn certified_arm_requires_both_actual_evidence_pushes() {
    let source = r#"fn production() { match attempt {
        Attempt::Certified {} => {
            let _ = BodyGate::Gated {};
            module.proof_obligations.push(obligation);
            module.proof_certificates.push(cert);
        }
        Attempt::Skip(_) => {}
    }}"#;
    let sites = gated_sites(source);
    assert_eq!(sites.len(), 1);
    assert!(sites[0].certified_arm && sites[0].obligation && sites[0].certificate);
    for statement in [
        "module.proof_obligations.push(obligation);",
        "module.proof_certificates.push(cert);",
    ] {
        let sites = gated_sites(&source.replace(statement, ""));
        assert!(!(sites[0].obligation && sites[0].certificate));
    }
    assert_eq!(
        gated_sites(&source.replace(
            "let _ = BodyGate::Gated {};",
            "let _ = BodyGate::Gated {}; let _ = BodyGate::Gated {};"
        ))
        .len(),
        2
    );
    let sites = gated_sites(&source.replace("Attempt::Certified", "Attempt::Skip"));
    assert!(!sites[0].certified_arm);
}
