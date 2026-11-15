// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The observer's own fail-closed arms, driven directly.

use super::CheckObserver;
use crate::cmd_core::{FileCheckOutcome, ImportCheckState};
use clean_elab::module_driver::{parse_module, BudgetReading, ModuleObserver};
use clean_elab::FileContext;
use std::path::Path;

/// A declaration that spent its whole budget is never left standing on what
/// it recorded, even when no outcome mark was taken for it: the `diverged` row
/// is recorded and the missing mark is reported as an internal error.
#[test]
fn test_check_observer_exhausted_budget_without_mark_still_diverges() {
    let source = "def x : Nat := 1\n";
    let decls = parse_module(Path::new("NoMark.lean"), source)
        .1
        .expect("fixture parses")
        .decls;
    let mut state = ImportCheckState::default();
    let mut outcome = FileCheckOutcome::default();
    let mut observer = CheckObserver::new(
        &mut state,
        &mut outcome,
        source,
        "NoMark",
        true,
        false,
        false,
        true,
        false,
    );
    // `before_decl` deliberately not called: the mark is absent.
    observer.after_decl(
        &FileContext::new(),
        &decls[0],
        &BudgetReading {
            spent: 7,
            exhausted: true,
            limit: 7,
        },
    );
    drop(observer);
    assert_eq!(
        outcome.diverged.len(),
        1,
        "diverged: {:?}",
        outcome.diverged
    );
    assert!(
        outcome.diverged[0].starts_with("x: did not finish"),
        "diverged row: {}",
        outcome.diverged[0]
    );
    assert_eq!(
        outcome.errors,
        vec![
            "internal: x spent its budget with no outcome mark, so what it recorded was not \
             rolled back"
                .to_owned()
        ]
    );
}
