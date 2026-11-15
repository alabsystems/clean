// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_one_and_two_byte_input_matches_actual_std() {
    run(&[]);
    for a in 0..=255u8 {
        run(&[a]);
        for b in 0..=255u8 {
            run(&[a, b]);
        }
    }
}
#[test]
fn every_unicode_scalar_canonical_encoding_matches_actual_std() {
    let mut buffer = [0u8; 4];
    for code in 0..=0x10ffff {
        if let Some(c) = char::from_u32(code) {
            assert!(run(c.encode_utf8(&mut buffer).as_bytes()).0);
        }
    }
}
#[test]
fn all_boundary_class_three_and_four_byte_products_match_actual_std() {
    let bytes = [
        0, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2, 0xdf, 0xe0, 0xed, 0xef,
        0xf0, 0xf4, 0xf5, 0xff,
    ];
    for a in bytes {
        for b in bytes {
            for c in bytes {
                run(&[a, b, c]);
                for d in bytes {
                    run(&[a, b, c, d]);
                }
            }
        }
    }
}
#[test]
fn truncated_overlong_surrogate_and_out_of_range_sequences_refuse_semantically() {
    for bytes in [
        &[0xc0, 0x80][..],
        &[0xe0, 0x80, 0x80],
        &[0xed, 0xa0, 0x80],
        &[0xf0, 0x80, 0x80, 0x80],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xf5, 0x80, 0x80, 0x80],
        &[0xc2],
        &[0xe2, 0x82],
        &[0xf0, 0x9f, 0x98],
    ] {
        assert!(!run(bytes).0);
    }
}
#[test]
fn original_window_is_checked_without_claiming_whole_global_validity() {
    let bytes = [0xff, b'a', 0xc2, 0xa2, 0xff];
    assert!(!run(&bytes).0);
    assert!(run(&bytes[1..4]).0);
    assert!(!run(&bytes[2..3]).0);
    assert!(!run(&bytes[3..4]).0);
}
#[test]
fn repeated_mixed_scalar_stream_and_every_prefix_match_actual_std() {
    let bytes = "a\0¢€😀\n".repeat(32).into_bytes();
    for end in 0..=bytes.len() {
        run(&bytes[..end]);
    }
}
#[test]
fn first_invalid_prefix_does_not_visit_unread_arbitrary_tail() {
    let mut bytes = vec![0xff];
    bytes.resize(128 * 1024, b'a');
    let (valid, o) = run(&bytes);
    assert!(!valid);
    assert_eq!(o.calls, 3);
    assert_eq!(o.work, 34);
}
