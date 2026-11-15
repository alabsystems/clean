// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-declaration timing (`crate::begin_decl_timing` / `take_decl_timings`),
//! the recorder behind `clean check --json`'s `timing.per_declaration`.
//!
//! What is pinned is the SHAPE of the record, because that is what a
//! performance gate keys on: one record per declaration the user wrote, under
//! the name the check report already uses for it, never one for a `section` /
//! `namespace` / `set_option … in` wrapper (those would double-count their
//! members), never two for one `mutual` block, and nothing at all unless the
//! thread asked. Every fixture here is accepted by the pinned Lean
//! (`lean` v4.30.0-rc2, exit 0), measured 2026-09-24.

use clean_kernel::Environment;

use crate::{DeclTiming, DeclTimingKind};

/// Elaborate `src` as one file, exactly as `clean check`'s main loop does.
fn elab_file(src: &str) {
    use crate::tactic::builtins::builtin_tactic_patterns;
    use crate::{preprocess_decl_with_context, FileContext};
    use clean_parser::parse_file_with_tactics;
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        // A failing declaration is still timed; the verdict is not this
        // test's subject.
        let _ = crate::elaborate_decl_and_register_with_context_and_warning(
            &mut env,
            &processed,
            &mut file_ctx,
        );
    }
}

fn names(records: &[DeclTiming]) -> Vec<&str> {
    records.iter().map(|r| r.name.as_str()).collect()
}

const NESTED: &str = "namespace Foo\n\
def a : Nat := 1\n\
def b : Nat := a + 1\n\
end Foo\n\
section S\n\
theorem t : Foo.b = 2 := rfl\n\
end S\n\
set_option maxHeartbeats 400000 in\n\
def c : Nat := 3\n\
open Foo\n";

#[test]
fn test_decl_timing_unarmed_records_nothing() {
    let _ = crate::take_decl_timings();
    elab_file(NESTED);
    assert!(
        crate::take_decl_timings().is_empty(),
        "a thread that never armed recording must accumulate nothing"
    );
}

#[test]
fn test_decl_timing_containers_record_their_members_not_themselves() {
    crate::begin_decl_timing();
    elab_file(NESTED);
    let records = crate::take_decl_timings();
    let decls: Vec<&DeclTiming> = records
        .iter()
        .filter(|r| r.kind == DeclTimingKind::Declaration)
        .collect();
    assert_eq!(
        decls.iter().map(|r| r.name.as_str()).collect::<Vec<_>>(),
        vec!["Foo.a", "Foo.b", "t", "c"],
        "one record per declaration, namespace-qualified, and none for the \
         namespace/section/set_option wrappers: {records:?}"
    );
    assert!(
        !names(&records).iter().any(|n| *n == "Foo" || *n == "S"),
        "a container must not be timed as a declaration: {records:?}"
    );
    let commands: Vec<&str> = records
        .iter()
        .filter(|r| r.kind == DeclTimingKind::Command)
        .map(|r| r.name.as_str())
        .collect();
    assert_eq!(
        commands,
        vec!["[anonymous]"],
        "`open Foo` is one command record: {records:?}"
    );
    // Byte offsets point at each declaration's own text, in source order.
    let offsets: Vec<usize> = decls.iter().map(|r| r.byte_start).collect();
    assert!(offsets.windows(2).all(|w| w[0] < w[1]), "{offsets:?}");
    assert!(
        NESTED[decls[2].byte_start..].starts_with("theorem t"),
        "{:?}",
        decls[2]
    );
    // Disarmed after take: a second drain is empty.
    assert!(crate::take_decl_timings().is_empty());
}

#[test]
fn test_decl_timing_mutual_block_is_one_record() {
    let src = "mutual\n\
def isEven : Nat → Bool\n\
  | 0 => true\n\
  | n+1 => isOdd n\n\
def isOdd : Nat → Bool\n\
  | 0 => false\n\
  | n+1 => isEven n\n\
end\n";
    crate::begin_decl_timing();
    elab_file(src);
    let records = crate::take_decl_timings();
    assert_eq!(
        names(&records),
        vec!["mutual(isEven, isOdd)"],
        "a mutual block is elaborated as one unit and charged once, however \
         the elaborator splits it internally: {records:?}"
    );
}

#[test]
fn test_decl_timing_begin_discards_an_earlier_run() {
    crate::begin_decl_timing();
    elab_file("def early : Nat := 0\n");
    crate::begin_decl_timing();
    elab_file("def late : Nat := 1\n");
    let records = crate::take_decl_timings();
    assert_eq!(names(&records), vec!["late"], "{records:?}");
}

/// `open X in <decl>` is elaborated inline (not through the registration
/// entry's recursion), so the wrapper's one record must carry the wrapped
/// declaration's name, kind and line -- otherwise the declaration is filed as
/// an anonymous command and vanishes from `per_declaration`. Pinned Lean
/// v4.30.0-rc2 accepts the fixture (exit 0), measured 2026-09-25.
#[test]
fn test_decl_timing_open_in_is_timed_as_the_wrapped_declaration() {
    let src = "namespace Foo\ndef a : Nat := 1\nend Foo\nopen Foo in\ndef d : Nat := a\n";
    crate::begin_decl_timing();
    elab_file(src);
    let records = crate::take_decl_timings();
    let decls: Vec<&DeclTiming> = records
        .iter()
        .filter(|r| r.kind == DeclTimingKind::Declaration)
        .collect();
    assert_eq!(
        decls.iter().map(|r| r.name.as_str()).collect::<Vec<_>>(),
        vec!["Foo.a", "d"],
        "the `open … in` wrapper is timed as `d`: {records:?}"
    );
    assert!(
        src[decls[1].byte_start..].starts_with("def d"),
        "the record points at the wrapped declaration's own text: {:?}",
        decls[1]
    );
}
