// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::Parser;
use crate::{Attribute, AttributeCommandAttr, SurfaceDecl};

#[test]
fn class_attribute_scope_is_retained_for_declaration_and_command_validation() {
    for scope in ["local", "scoped"] {
        for source in [
            format!("attribute [{scope} class] Candidate"),
            format!("@[{scope} class] axiom Candidate : Type"),
        ] {
            let decl = Parser::parse_decl(&source).expect("class scope syntax must parse");
            let attrs = match decl {
                SurfaceDecl::Attribute { attrs, .. } => attrs
                    .into_iter()
                    .map(|attr| match attr {
                        AttributeCommandAttr::Add(attr) => attr,
                        other => panic!("expected attribute addition: {other:?}"),
                    })
                    .collect(),
                SurfaceDecl::Axiom { attrs, .. } => attrs,
                other => panic!("expected class attribute fixture: {other:?}"),
            };
            let [attr] = attrs.as_slice() else {
                panic!("exactly one attribute must survive: {attrs:?}");
            };
            let inner = match (scope, attr) {
                ("local", Attribute::Local(inner)) | ("scoped", Attribute::Scoped(inner)) => inner,
                other => panic!("scope must not disappear into an unknown attribute: {other:?}"),
            };
            assert!(matches!(inner.as_ref(), Attribute::Class));
        }
    }
}
