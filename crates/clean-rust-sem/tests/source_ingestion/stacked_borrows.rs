// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::EvalResult;
use clean_rust_sem::{SourceProgram, Value};

fn run_source_with_aliasing(source: &str, parse_msg: &str) -> EvalResult {
    let program = SourceProgram::parse(source).expect(parse_msg);
    program.run_with_aliasing_checks()
}

#[test]
fn test_source_program_default_run_keeps_mut_deref_write_disabled() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            *r = 2u32;
            x
        }
    "#;

    let program = SourceProgram::parse(source).expect("mutable reference write should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(
        matches!(
            result,
            EvalResult::Error(ref msg)
                if msg.contains("deref write requires tracked reference provenance")
        ),
        "default source execution should stay on the legacy non-aliasing path, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_support_mut_deref_assignment() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            *r = 2u32;
            x
        }
    "#;

    let result = run_source_with_aliasing(source, "mutable reference write should parse");
    assert_eq!(
        result.value(),
        Some(Value::u32(2)),
        "run_with_aliasing_checks should make source-level deref writes reach the tracked referent"
    );
}

#[test]
fn test_source_program_aliasing_checks_support_mut_reborrow_assignment() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let s: &mut u32 = &mut *r;
            *s = 2u32;
            *s
        }
    "#;

    let result = run_source_with_aliasing(source, "mutable reborrow write should parse");
    assert_eq!(
        result.value(),
        Some(Value::u32(2)),
        "run_with_aliasing_checks should preserve referent provenance across `&mut *r`"
    );
}

#[test]
fn test_source_program_aliasing_checks_reject_invalidated_mut_reborrow() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let s: &mut u32 = &mut *r;
            let parent_read: u32 = *r;
            let child_read: u32 = *s;
            child_read + parent_read
        }
    "#;

    let result = run_source_with_aliasing(source, "invalidated mutable reborrow should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "using the parent after `&mut *r` should invalidate the child reborrow, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_reject_stale_block_reference() {
    let source = r#"
        fn main() -> u32 {
            let r: &u32 = {
                let x: u32 = 11u32;
                &x
            };
            let x: u32 = 22u32;
            *r
        }
    "#;

    let result = run_source_with_aliasing(source, "stale block reference should parse");
    assert!(
        matches!(
            result,
            EvalResult::Error(ref msg)
                if msg.contains("cannot resolve tracked place root")
                    || msg.contains("cannot read unbound tracked root")
        ),
        "stale block reference must not rebind to a later local when aliasing checks are enabled, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_reject_whole_place_overwrite_of_borrowed_field() {
    let source = r#"
        struct Pair {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let mut s: Pair = Pair { x: 1u32, y: 2u32 };
            let r: &mut u32 = &mut s.x;
            s = Pair { x: 3u32, y: 4u32 };
            *r
        }
    "#;

    let result = run_source_with_aliasing(
        source,
        "whole-place overwrite with borrowed field should parse",
    );
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "overwriting a whole place should invalidate a borrowed field, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_support_raw_deref_from_ref_cast() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 55u32;
            let r: &u32 = &x;
            let p: *const u32 = r as *const u32;
            unsafe { *p }
        }
    "#;

    let result = run_source_with_aliasing(source, "raw deref through ref cast should parse");
    assert_eq!(
        result.value(),
        Some(Value::u32(55)),
        "raw deref should preserve tracked provenance through a source-level ref-to-raw cast"
    );
}

#[test]
fn test_source_program_aliasing_checks_reject_invalidated_raw_pointer_from_ref_cast() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let p: *mut u32 = r as *mut u32;
            *r = 2u32;
            unsafe { *p }
        }
    "#;

    let result = run_source_with_aliasing(
        source,
        "invalidated raw pointer cast from mutable reference should parse",
    );
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "a raw pointer derived from `&mut` should be invalidated by a later parent write, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_reject_shared_ref_cast_to_mut_raw_write() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 1u32;
            let r: &u32 = &x;
            let p: *mut u32 = r as *mut u32;
            unsafe { *p = 2u32; }
            x
        }
    "#;

    let result = run_source_with_aliasing(source, "shared-ref to mutable-raw write should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "a raw write derived from `&T` should be rejected, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_support_raw_mut_deref_write() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let p: *mut u32 = r as *mut u32;
            unsafe { *p = 99u32; }
            unsafe { *p }
        }
    "#;

    let result = run_source_with_aliasing(
        source,
        "raw mutable deref write through ref cast should parse",
    );
    assert_eq!(
        result.value(),
        Some(Value::u32(99)),
        "write through *mut raw pointer should update the tracked place"
    );
}

#[test]
fn test_source_program_aliasing_checks_enforce_fn_entry_protector() {
    let source = r#"
        fn read_ref(r: &u32) -> u32 {
            *r
        }
        fn main() -> u32 {
            let x: u32 = 42u32;
            read_ref(&x)
        }
    "#;

    let result = run_source_with_aliasing(source, "function taking shared reference should parse");
    assert_eq!(
        result.value(),
        Some(Value::u32(42)),
        "reading through a function-entry-protected reference should succeed"
    );
}

#[test]
fn test_source_program_aliasing_checks_reject_fn_entry_protector_invalidation_in_body() {
    let source = r#"
        fn bad(r: &u32, p: *mut u32) -> u32 {
            unsafe { *p = 7u32; }
            *r
        }

        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let p: *mut u32 = (&mut x) as *mut u32;
            bad(&x, p)
        }
    "#;

    let result = run_source_with_aliasing(
        source,
        "fn-entry protector invalidation through raw pointer should parse",
    );
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "writing through a raw pointer should not invalidate a protected function-entry borrow, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_support_two_phase_mut_method_receiver() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn get(&self) -> u32 {
                self.value
            }

            fn add(&mut self, n: u32) -> u32 {
                self.value = self.value + n;
                self.value
            }
        }

        fn main() -> u32 {
            let mut counter = Counter { value: 1u32 };
            let added = counter.add(counter.get());
            added + counter.value
        }
    "#;

    let result = run_source_with_aliasing(
        source,
        "two-phase mutable method receiver should allow shared argument reads",
    );
    assert_eq!(
        result.clone().value(),
        Some(Value::u32(4)),
        "method-call receiver reservation should activate after evaluating shared arguments and persist the receiver mutation, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_mut_borrowed_receiver_updates_underlying_referent() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn bump(&mut self) -> u32 {
                self.value = self.value + 1u32;
                self.value
            }
        }

        fn main() -> u32 {
            let mut counter = Counter { value: 1u32 };
            {
                let r: &mut Counter = &mut counter;
                let seen: u32 = r.bump();
                if seen == 0u32 {
                    return 99u32;
                }
            }
            counter.value
        }
    "#;

    let result =
        run_source_with_aliasing(source, "borrowed mutable receiver method call should parse");
    assert_eq!(
        result.clone().value(),
        Some(Value::u32(2)),
        "method-call syntax on a borrowed mutable receiver should update the underlying referent, got {result:?}"
    );
}

#[test]
fn test_source_program_aliasing_checks_borrowed_shared_receiver_protects_referent() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn read_after_raw_write(&self, p: *mut Counter) -> u32 {
                unsafe { *p = Counter { value: 7u32 }; }
                self.value
            }
        }

        fn main() -> u32 {
            let mut counter = Counter { value: 1u32 };
            let p: *mut Counter = (&mut counter) as *mut Counter;
            let r: &Counter = &counter;
            r.read_after_raw_write(p)
        }
    "#;

    let result = run_source_with_aliasing(
        source,
        "borrowed shared receiver with whole-place raw write should parse",
    );
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "borrowed shared receiver method call should protect the underlying referent, got {result:?}"
    );
}
