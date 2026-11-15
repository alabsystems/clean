// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn a_matcher_row_cannot_relabel_a_foreign_resident_definition() {
    let name = Name::from_string("ordinary.match_1");
    let mut env = Environment::default();
    env.add_decl(clean_kernel::Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop())),
        value: Expr::lam(
            clean_kernel::BinderInfo::Default,
            Expr::prop(),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                Expr::prop(),
                Expr::bvar(1),
            ),
        ),
        is_reducible: false,
    })
    .unwrap();
    let row = TypedExtension {
        extension_name: Name::from_string("Lean.Meta.Match.Extension.extension"),
        source_rows: Some(1),
        undecoded_entries: 0,
        compiler_names: None,
        entries: vec![TypedExtensionEntry::Matcher {
            name: name.clone(),
            info: clean_kernel::env::MatcherInfo {
                num_params: 0,
                num_discrs: 0,
                alt_num_params: vec![0],
                u_elim_pos: None,
                discr_names: vec![],
                details: None,
            },
        }],
    };
    assert_eq!(
        register_real_matcher_entries(&mut env, Some("Incoming"), &[row]).unwrap(),
        1
    );
    assert!(env.get_matcher_info(&name).is_none());
}
