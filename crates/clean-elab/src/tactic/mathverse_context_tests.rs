// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact context-hint extraction, not a proof-search or shard-format claim.

use super::{mathverse_context_names, mathverse_context_path};
use crate::tactic::LocalDecl;
use crate::unify::MetaState;
use clean_kernel::{Expr, FVarId, Name};
use clean_parser::SurfaceName;

#[test]
fn legacy_context_paths_preserve_components_and_numeric_kinds() {
    assert_eq!(
        mathverse_context_path(&Name::anon().str("A").str("B")),
        Some("A.B".to_owned())
    );
    assert_eq!(mathverse_context_path(&Name::anon().str("A.B")), None);
    assert_eq!(
        mathverse_context_path(&Name::anon().num(7).str("field")),
        Some("7.field".to_owned())
    );
    for text in ["7", "+7", "007", "", "A.B"] {
        assert_eq!(mathverse_context_path(&Name::anon().str(text)), None);
    }
    assert_eq!(mathverse_context_path(&Name::anon()), None);
}

#[test]
fn local_binder_spelling_never_selects_a_global_neighborhood() {
    let metas = MetaState::new();
    for label in [
        SurfaceName::generated_path("Nat.add"),
        SurfaceName::component("Nat.add", true),
        SurfaceName::from_name(Name::anon().num(7)),
    ] {
        let local = LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: label,
            ty: Expr::prop(),
            value: None,
        };
        assert!(mathverse_context_names(&metas, &[local]).is_empty());
    }
}

#[test]
fn context_hints_use_actual_type_and_value_constants_once() {
    let metas = MetaState::new();
    let local = LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(0),
        name: SurfaceName::generated_path("Nat.add"),
        ty: Expr::const_(Name::anon().str("Nat"), vec![]),
        value: Some(Expr::const_(Name::anon().str("Nat").str("zero"), vec![])),
    };
    let mut second = local.clone();
    second.fvar = FVarId::new(1);
    assert_eq!(
        mathverse_context_names(&metas, &[local, second]),
        vec!["Nat".to_owned(), "Nat.zero".to_owned()]
    );
}

#[test]
fn unrepresentable_constants_do_not_alias_representable_hint_keys() {
    let metas = MetaState::new();
    let locals: Vec<_> = [
        Name::anon().str("A.B"),
        Name::anon().str("A").str("B"),
        Name::anon().str("7"),
        Name::anon().num(7),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, name)| LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(index as u64),
        name: SurfaceName::generated_path("h"),
        ty: Expr::const_(name, vec![]),
        value: None,
    })
    .collect();
    let mut hints = mathverse_context_names(&metas, &locals);
    hints.sort();
    assert_eq!(hints, vec!["7".to_owned(), "A.B".to_owned()]);
}
