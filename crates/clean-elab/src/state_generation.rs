// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process-unique state generations for the elaborator's memoised views.
//!
//! `ElabCtx::shared_local_ctx` memoises the kernel `LocalContext` it builds
//! from the local bindings and the metavariable state, and serves the cached
//! context while both are unchanged. "Unchanged" is decided by comparing
//! generation numbers, so the whole soundness of that cache rests on two
//! properties of the numbers handed out here:
//!
//! 1. **Every mutation mints a fresh number** — the mutating methods of
//!    `MetaState` and `LocalBindings` call [`next_generation`] and store the
//!    result; nothing else writes their generation fields.
//! 2. **A number is never handed out twice, process-wide.** A per-state `+1`
//!    counter would NOT do: both states are `Clone`, and elaboration restores
//!    clones (`ElabCtx::restore_local_scope`, the tactic framework's
//!    `ProofState` snapshots). With a local counter, "restore the clone taken
//!    at generation G, then mutate twice" lands on G+2 — the same number an
//!    earlier, different timeline already reached, and a cache entry minted
//!    on that timeline would be served for this one. With a process-wide
//!    monotone source the restored clone still carries G, whose content is by
//!    construction the content the clone was taken from, and every later
//!    mutation gets a number no timeline has ever seen.
//!
//! Together these make "same generation" equivalent to "same
//! instantiation-relevant content", which is exactly what the cache needs.

use std::sync::atomic::{AtomicU64, Ordering};

/// Next unissued generation. Starts at 1 so 0 can never match a live state.
static NEXT_GENERATION: AtomicU64 = AtomicU64::new(1);

/// Mint a generation number no state in this process has carried before.
#[must_use]
pub(crate) fn next_generation() -> u64 {
    // Only uniqueness is required, and the RMW is atomic under every ordering.
    NEXT_GENERATION.fetch_add(1, Ordering::Relaxed)
}

#[cfg(test)]
mod tests {
    use super::next_generation;

    #[test]
    fn test_next_generation_strictly_increases_and_never_yields_zero() {
        let a = next_generation();
        let b = next_generation();
        assert!(a > 0, "generation 0 is reserved for 'never a live state'");
        assert!(
            b > a,
            "generations must be strictly increasing: {a} then {b}"
        );
    }
}
