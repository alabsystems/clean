// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Build a minimal-but-parseable v1 .olean header with the given base_addr.
/// Only the header is required for `parse_load_module_incremental` to reach
/// the `base_base_addr + base_bytes.len()` arithmetic at line 171.
fn v1_file(base_addr: u64, total_len: usize) -> Vec<u8> {
    let mut b = vec![0u8; total_len.max(crate::header::HEADER_SIZE)];
    b[0..5].copy_from_slice(b"olean");
    b[5] = 1; // version 1
    b[6..46].copy_from_slice(b"0000000000000000000000000000000000000000");
    b[48..56].copy_from_slice(&base_addr.to_le_bytes());
    b
}

#[test]
fn base_addr_near_u64_max_does_not_panic() {
    // base_addr chosen so base_addr + base_bytes.len() overflows u64.
    // With overflow-checks=true (dev+release) the current code PANICS here.
    let base_addr = u64::MAX - 40; // even => valid pointer base
    let base = v1_file(base_addr, 128); // len 128 > 40 => base_addr + len overflows
                                        // private header: any valid header; base_addr irrelevant to the overflow.
    let private = v1_file(0x1000, crate::header::HEADER_SIZE);

    // Must return an Err (rejected), never panic/abort.
    let res = parse_load_module_incremental(&base, None, private);
    assert!(res.is_err(), "huge base_addr must be rejected, got Ok");
}

/// End-to-end reachability: a base file that ALSO parses via `parse_load_module`
/// (the on-disk `load_module_recursive` gate) and still overflows at line 171.
#[test]
fn e2e_parseable_base_reaches_incremental_overflow() {
    // room = u64::MAX - base_addr. We need room < len (=> overflow) and the root
    // object to sit at offset <= room (=> no wrap when forming its absolute ptr).
    let room: u64 = 103; // max - 103 is 8-byte aligned; offsets 0..=103 do not wrap
    let base_addr = u64::MAX - room;
    let len = 200usize; // > room => base_addr + len overflows u64
    let mut base = v1_file(base_addr, len);

    // Place a valid Clean-export ModuleData with five fields at an EVEN offset <= room,
    // so base_addr + root_off is even (is_ptr), <= u64::MAX (no wrap), and its
    // 8-byte header fits within len.
    let root_off = 88usize; // aligned, <= room(103), 88+48=136 <= len(200)
                            // A real empty Array before the root is shared by all five fields.
    base[64 + 7] = tags::ARRAY;
    base[root_off + 6] = 5;
    base[root_off + 7] = 0; // ctor tag
    for field in 0..5 {
        let offset = root_off + 8 + field * 8;
        base[offset..offset + 8].copy_from_slice(&(base_addr + 64).to_le_bytes());
    }
    // Root pointer stored at header_size (56) points at the root object.
    let root_ptr = base_addr + root_off as u64; // even => is_ptr
    base[crate::header::HEADER_SIZE..crate::header::HEADER_SIZE + 8]
        .copy_from_slice(&root_ptr.to_le_bytes());

    // Sanity: the base MUST parse through the normal load gate first
    // (this is the `load_module_recursive` gate before companions load).
    let parsed = parse_load_module(base.clone());
    assert!(
        parsed.is_ok(),
        "base must parse via parse_load_module to reach the companion/incremental path"
    );

    // Now the companion path calls the incremental parser with this same base.
    let private = v1_file(0x1000, crate::header::HEADER_SIZE);
    let res = parse_load_module_incremental(&base, None, private);
    assert!(res.is_err(), "huge base_addr must be rejected, got Ok");
}
