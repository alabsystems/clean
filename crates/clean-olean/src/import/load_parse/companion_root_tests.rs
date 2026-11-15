// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn parts() -> [Vec<u8>; 3] {
    let lib = crate::pinned_lean_lib_path().expect("explicit pinned Lean fixture is required");
    ["Lean.olean", "Lean.olean.server", "Lean.olean.private"]
        .map(|name| std::fs::read(lib.join(name)).expect("required actual pinned Lean root part"))
}
fn word(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}
fn private(parts: &[Vec<u8>; 3]) -> OleanResult<LoadModule> {
    parse_load_module_incremental(&parts[0], Some(&parts[1]), parts[2].clone())
}

#[test]
fn actual_modern_empty_companions_reuse_the_captured_base_root() {
    let parts = parts();
    let base_root = word(&parts[0], 88);
    for part in &parts[1..] {
        assert_eq!(part.len(), 96, "actual empty root companions");
        assert_eq!(word(part, 88), base_root);
        assert!(base_root < word(part, 80));
    }
    let server = parse_load_module_incremental(&parts[0], None, parts[1].clone())
        .expect("server may borrow the captured base root");
    let private = private(&parts).expect("private may borrow the captured base root");
    for module in [server, private] {
        assert!(module.constants.is_empty());
        assert!(
            !module.imports.is_empty(),
            "base imports must remain visible"
        );
    }
}

#[test]
fn actual_modern_companion_roots_require_full_prior_captured_extent() {
    let original = parts();
    let base = word(&original[0], 80);
    let base_end = base + original[0].len() as u64;
    let private_base = word(&original[2], 80);
    for part in [1, 2] {
        for pointer in [base - 8, base_end + 8, private_base + 96, u64::MAX - 7] {
            let mut parts = original.clone();
            parts[part][88..96].copy_from_slice(&pointer.to_le_bytes());
            assert!(private(&parts).is_err(), "part {part}, root {pointer}");
            if part == 1 {
                assert!(parse_load_module_incremental(&parts[0], None, parts[1].clone()).is_err());
            }
        }
    }
    let mut truncated = original.clone();
    truncated[0].pop();
    assert!(
        private(&truncated).is_err(),
        "whole root, not just its header, must be captured"
    );
    truncated[0].truncate(96);
    assert!(
        private(&truncated).is_err(),
        "missing base range must not become a gap allocation"
    );

    // A concrete mutation copies the genuine root into the server's own
    // range. Private may borrow it only when that exact server is supplied.
    let mut relocated = original.clone();
    let root = (word(&original[0], 88) - base) as usize;
    let copy = original[0][root..root + 56].to_vec();
    let server_root = word(&original[1], 80) + 96;
    relocated[1].extend_from_slice(&copy);
    relocated[1][88..96].copy_from_slice(&server_root.to_le_bytes());
    relocated[2][88..96].copy_from_slice(&server_root.to_le_bytes());
    assert!(
        private(&relocated).is_ok(),
        "captured server root positive witness"
    );
    assert!(parse_load_module_incremental(&relocated[0], None, relocated[2].clone()).is_err());

    // Conversely, a server root may not borrow a future private object.
    let mut future = original.clone();
    let future_root = private_base + 96;
    future[2].extend_from_slice(&copy);
    future[1][88..96].copy_from_slice(&future_root.to_le_bytes());
    future[2][88..96].copy_from_slice(&future_root.to_le_bytes());
    assert!(
        private(&future).is_err(),
        "future part is not an earlier captured region"
    );
}
