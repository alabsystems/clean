// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A local is a LOCAL INSTANCE because of its type, not its brackets.
//!
//! Lean's rule (`Lean.Meta.withNewLocalInstances`, keyed on `isClass?` of the
//! local's type): `[inst : C α]`, `{_ : C α}`, `{inst : C α}` and `(h : C α)`
//! all put an instance of `C α` in scope. Clean pushed only the
//! instance-implicit spelling until 2026-09-10, so every other spelling failed
//! `failed to synthesize instance C` with the instance in the local context —
//! Mathlib's `uniqueElim_default {_ : Unique ι}` shape.
//!
//! Fixture-driven from `tests/fixtures/source_frontier/`, where the battery
//! (`scripts/source_frontier_battery.sh`) pins the same file through the
//! release binary; this test runs it in the library suite so the rule is
//! checked on every `cargo test -p clean-elab --lib`, not only in the full
//! gate. The pinned `lean` v4.30.0-rc2 accepts the fixture verbatim.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE: &str =
    "../../tests/fixtures/source_frontier/p28_class_typed_local_is_an_instance.lean";

fn verdicts() -> Vec<(String, Result<(), String>)> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE);
    let src = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()));
    let decls = parse_file(&src).unwrap_or_else(|e| panic!("fixture must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut out = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            out.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            out.push((name.to_string(), Ok(())));
                        }
                        _ => {}
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", out.len()), ToString::to_string);
                out.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    out
}

/// Every spelling of a class-typed local is a local instance. `viaInst` is
/// the bracket control that passed before the rule changed.
#[test]
fn test_class_typed_local_is_a_local_instance_whatever_its_brackets() {
    let got = verdicts();
    for want in [
        "viaInst",
        "viaImplicit",
        "viaExplicit",
        "viaNamedImplicit",
        "viaImplicitThm",
    ] {
        let verdict = got
            .iter()
            .find(|(n, _)| n == want)
            .unwrap_or_else(|| panic!("`{want}` produced no verdict: {got:?}"));
        assert_eq!(
            verdict.1,
            Ok(()),
            "`{want}`: a local of class type must be a local instance, as in Lean"
        );
    }
}
