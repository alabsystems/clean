// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::{
    anonymous_local_of_named_type, drop_terminator_count, entry_goto_target,
    has_drop_continuing_to, has_switch_targeting_immediate_drop, lowered_main,
};

#[test]
fn test_while_backedge_drops_loop_body_temp_before_reuse() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let mut i: u32 = 0u32;
            while i < 2u32 {
                i = i + 1u32;
                MyString { data: i }
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let header = entry_goto_target(&body);
    let temp = anonymous_local_of_named_type(&body, "MyString");

    assert!(
        has_drop_continuing_to(&body, temp, header),
        "while body temp should drop before the lowered backedge returns to the header: {body:#?}"
    );
}

#[test]
fn test_for_continue_drops_next_result_before_reentering_header() {
    let source = r#"
        fn main() -> u32 {
            let mut total: u32 = 0u32;
            for i in 0u32..3u32 {
                if i == 1u32 {
                    continue;
                }
                total = total + i;
            }
            total
        }
    "#;

    let body = lowered_main(source);
    let next_result = anonymous_local_of_named_type(&body, "Option");

    assert!(
        drop_terminator_count(&body, next_result) >= 3,
        "for-loop continue should drop the lowered Option temp on the normal backedge, on continue, and at loop exit: {body:#?}"
    );
}

#[test]
fn test_while_continue_uses_init_flag_before_dropping_body_temp() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let mut i: u32 = 0u32;
            while i < 2u32 {
                if i == 0u32 {
                    i = i + 1u32;
                    continue;
                }
                MyString { data: i }
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "MyString");

    assert!(
        has_switch_targeting_immediate_drop(&body, body_temp),
        "while-continue lowering should guard loop body temp cleanup behind an init-state switch before dropping {body_temp}: {body:#?}"
    );
}

#[test]
fn test_while_break_uses_init_flag_before_dropping_body_temp() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let mut i: u32 = 0u32;
            while i < 2u32 {
                if i == 0u32 {
                    break;
                }
                MyString { data: i }
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "MyString");

    assert!(
        has_switch_targeting_immediate_drop(&body, body_temp),
        "while-break lowering should guard loop body temp cleanup behind an init-state switch before dropping {body_temp}: {body:#?}"
    );
}

#[test]
fn test_for_continue_uses_init_flag_before_dropping_body_temp() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            for i in 0u32..3u32 {
                if i == 1u32 {
                    continue;
                }
                MyString { data: i }
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "MyString");

    assert!(
        has_switch_targeting_immediate_drop(&body, body_temp),
        "for-continue lowering should guard loop body temp cleanup behind an init-state switch before dropping {body_temp}: {body:#?}"
    );
}

#[test]
fn test_labeled_continue_outer_uses_init_flag_for_inner_loop_body_temp() {
    let source = r#"
        struct InnerTemp { data: u32 }

        fn main() -> u32 {
            let mut i: u32 = 0u32;
            'outer: while i < 2u32 {
                loop {
                    if i == 0u32 {
                        i = 1u32;
                        continue 'outer;
                    }
                    InnerTemp { data: i }
                }
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let body_temp = anonymous_local_of_named_type(&body, "InnerTemp");

    assert!(
        has_switch_targeting_immediate_drop(&body, body_temp),
        "labeled outer continue should guard inner loop body temp cleanup behind an init-state switch before dropping {body_temp}: {body:#?}"
    );
}
