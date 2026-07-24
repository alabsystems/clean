// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::{
    anonymous_local_of_named_type, lowered_main, named_local, storage_live_has_prior_storage_dead,
};

#[test]
fn test_loop_break_cleans_body_temp_before_post_loop_binding() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let mut done: bool = false;
            loop {
                if done {
                    break;
                }
                done = true;
                MyString { data: 1u32 }
            }
            let after_break: u32 = 7u32;
            after_break
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "MyString");
    let after_break = named_local(&body, "after_break");

    assert!(
        storage_live_has_prior_storage_dead(&body, after_break, body_temp),
        "loop-break exit should retire the loop body temp before the post-loop binding becomes live: {body:#?}"
    );
}

#[test]
fn test_while_natural_exit_cleans_body_temp_before_post_loop_binding() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let mut i: u32 = 0u32;
            while i < 1u32 {
                i = i + 1u32;
                MyString { data: i }
            }
            let after_loop: u32 = 9u32;
            after_loop
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "MyString");
    let after_loop = named_local(&body, "after_loop");

    assert!(
        storage_live_has_prior_storage_dead(&body, after_loop, body_temp),
        "while natural exit should retire the loop body temp before the post-loop binding becomes live: {body:#?}"
    );
}

#[test]
fn test_for_natural_exit_cleans_body_temp_before_post_loop_binding() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            for i in 0u32..1u32 {
                MyString { data: i }
            }
            let after_for: u32 = 11u32;
            after_for
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "MyString");
    let after_for = named_local(&body, "after_for");

    assert!(
        storage_live_has_prior_storage_dead(&body, after_for, body_temp),
        "for natural exit should retire the loop body temp before the post-loop binding becomes live: {body:#?}"
    );
}
