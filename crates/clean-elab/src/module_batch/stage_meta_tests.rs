// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G46 (ledger (116)) mutation control for header staging: a written
//! signature that still holds an elaborator metavariable is NOT staged. The
//! guard asked `has_expr_mvar_quick`, constant false for elaborator metas
//! (bit-63 FVars), so until 2026-10-08 `g`'s provisional `?T → Nat` was
//! recorded as its header. Pinned Lean 4.8.0 refuses `g` itself ("failed to
//! infer binder type"); a header is never the place to learn `?T`.

use super::*;
use crate::module_batch::{SourceUnit, UnitId};

fn staged(source: &str) -> Plan {
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    let decls = clean_parser::parse_file(source).expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let mut plan = super::super::plan::plan(&mut env, &mut file_ctx, &units);
    stage_headers(&env, &mut plan).expect("the header index settles");
    plan
}

fn node<'p>(plan: &'p Plan, name: &str) -> &'p Node {
    plan.nodes
        .iter()
        .find(|n| n.name.as_ref().is_some_and(|n| n.to_string() == name))
        .unwrap_or_else(|| panic!("`{name}` is planned"))
}

#[test]
fn test_stage_headers_refuses_a_signature_with_an_open_metavariable() {
    let plan = staged("def g (x : _) : Nat := Nat.succ x\ndef h (x : Nat) : Nat := x\n");
    let g = node(&plan, "g");
    assert!(g.header.is_none(), "`g`'s `?T → Nat` must not be staged");
    assert_eq!(g.no_header, Some(NoHeaderReason::ResidualMetavariable));
    // Control: a ground signature is staged.
    assert!(
        node(&plan, "h").header.is_some(),
        "`h : Nat → Nat` is staged"
    );
}
