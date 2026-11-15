// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Rust runtime copies free a deep object graph in constant stack (plan
//! item `runtime-rc-sticky`, the worklist half of lean4#15241).
//!
//! Both copies used to recurse on every child but the last, so a chain
//! threaded through field 0 overflowed the stack. Each test builds a
//! 1,000,000-node chain through field 0 on a thread with a fixed 512 KiB
//! stack and drops its head. A stack overflow aborts the whole process
//! ("has overflowed its stack"), which is why these tests are their own
//! binary: the abort cannot take other results with it. The last-field
//! control is `runtime::tests::test_dec_deep_linked_list_no_stack_overflow`.

use clean_runtime::{clean_alloc_ctor, clean_box, clean_dec, LeanObjPtr};

const DEPTH: usize = 1_000_000;
const STACK: usize = 512 * 1024;

/// Run `f` on a thread with a fixed [`STACK`] and require it to finish.
fn on_small_stack(name: &str, f: fn()) {
    std::thread::Builder::new()
        .name(name.to_owned())
        .stack_size(STACK)
        .spawn(f)
        .expect("spawn small-stack thread")
        .join()
        .expect("the deep chain must free without overflowing the thread's stack");
}

#[test]
fn test_runtime_dec_deep_first_field_chain_frees() {
    on_small_stack("runtime-deep-chain", || {
        let mut head: LeanObjPtr = clean_box(0);
        for _ in 0..DEPTH {
            head = clean_alloc_ctor(0, 2, 0, &[head, clean_box(0)]);
        }
        clean_dec(head);
    });
}

#[test]
fn test_native_dec_deep_first_field_chain_frees() {
    on_small_stack("native-deep-chain", || {
        // SAFETY: every pointer is a fresh native allocation or a tagged
        // scalar; the chain owns each node exactly once and `dec` drops the
        // only reference to its head.
        unsafe {
            let mut head = clean_runtime::native::box_val(0);
            for _ in 0..DEPTH {
                head = clean_runtime::native::alloc_ctor(
                    0,
                    &[head, clean_runtime::native::box_val(0)],
                );
            }
            clean_runtime::native::dec(head);
        }
    });
}
