// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// VF5 mirror of aterm's "PM-1-free, F1" rows (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"): each function is
// the aterm function verbatim (aterm main 5285726838: attributes, `const fn`,
// signature and body), with its constants, in a module named after the aterm
// one; the one change is visibility, `pub` throughout (aterm's `bar_glints`
// and `osc_put_keeps` are `pub(crate)`, `over_bound` and `at_low_water`
// private), so that each is a root the artifact keeps. The aterm crates' own
// modules are not F1 as a whole (derived impls read through pointers), so the
// rows are compiled from this mirror; every function here is a root (no
// caller), so no row carries a precondition.
#![crate_type = "lib"]
#![no_std]

/// aterm-control `src/wire.rs:113` (row 13).
pub mod wire {
    pub const WAIT_MAX_MS: u64 = 600_000;
    #[must_use]
    #[inline]
    pub const fn clamp_wait_ms(ms: u64) -> u64 {
        if ms > WAIT_MAX_MS {
            WAIT_MAX_MS
        } else {
            ms
        }
    }
}

/// aterm-messages `src/chrome.rs:64` (row 19).
pub mod chrome {
    #[inline]
    #[must_use]
    pub const fn is_rise(reserved: u16, rows: u16) -> bool {
        rows > reserved
    }
}

/// aterm-messages `src/waits.rs:390` (row 20).
pub mod waits {
    pub const LARGE_PASTE_BYTES: u64 = 64 * 1024;
    #[must_use]
    pub const fn paste_is_watched(bytes: u64) -> bool {
        bytes >= LARGE_PASTE_BYTES
    }
}

/// aterm-messages `src/animate.rs:628` (row 21; `GLINT_RADIUS_PERMILLE` from `src/lib.rs:156`).
pub mod animate {
    pub const GLINT_RADIUS_PERMILLE: u32 = 30;
    #[inline]
    #[must_use]
    pub const fn bar_glints(shown: u16) -> bool {
        (shown as u32) * 2 >= GLINT_RADIUS_PERMILLE
    }
}

/// aterm-link `src/mailbox.rs:322,326` (rows 15, 16).
pub mod mailbox {
    pub const QUEUE_ROWS_MAX: usize = 1024;
    pub const QUEUE_BYTES_MAX: usize = 8 * 1024 * 1024;
    pub const fn over_bound(rows: usize, bytes: usize) -> bool {
        rows > 0 && (rows >= QUEUE_ROWS_MAX || bytes >= QUEUE_BYTES_MAX)
    }
    pub const fn at_low_water(rows: usize, bytes: usize) -> bool {
        rows <= QUEUE_ROWS_MAX / 2 && bytes <= QUEUE_BYTES_MAX / 2
    }
}

/// aterm-parser `src/dispatch.rs:23` (row 22; `MAX_OSC_DATA` from `src/lib.rs:97`).
pub mod dispatch {
    pub const MAX_OSC_DATA: usize = 8 * 1024 * 1024;
    #[inline]
    pub const fn osc_put_keeps(len: usize) -> bool {
        len < MAX_OSC_DATA
    }
}
