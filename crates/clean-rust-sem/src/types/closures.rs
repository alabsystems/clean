// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure trait kinds and coercion rules.

use serde::{Deserialize, Serialize};

use super::Mutability;

/// Closure trait kind determining how the closure captures its environment.
///
/// Corresponds to Rust's Fn/FnMut/FnOnce traits. The kind is determined by
/// how captured variables are used within the closure body:
/// - `Fn`: Only reads captures (borrows as `&T`)
/// - `FnMut`: Mutates captures (borrows as `&mut T`)
/// - `FnOnce`: Moves/consumes captures (takes ownership)
///
/// Reference: Rust Reference, "Closure types" section
/// <https://doc.rust-lang.org/reference/types/closure.html>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ClosureKind {
    /// `Fn` - closure borrows captured variables immutably
    Fn,
    /// `FnMut` - closure borrows captured variables mutably
    FnMut,
    /// `FnOnce` - closure consumes (moves) captured variables
    FnOnce,
}

impl ClosureKind {
    /// Determine closure kind from capture mutabilities.
    ///
    /// Currently only distinguishes Fn vs FnMut based on mutability:
    /// - Any mutable capture → FnMut
    /// - Otherwise → Fn
    ///
    /// **Limitation:** FnOnce detection requires tracking whether captures
    /// are moved (owned) vs borrowed, which isn't currently tracked in
    /// the capture representation. This is a simplification.
    ///
    /// Note: The actual Rust compiler also considers how captured variables
    /// are used within the closure body.
    pub fn from_captures(captures: &[(String, Mutability)]) -> Self {
        for (_, mutability) in captures {
            if *mutability == Mutability::Mutable {
                return ClosureKind::FnMut;
            }
        }
        ClosureKind::Fn
    }

    /// Check if this kind is compatible with (can be coerced to) another kind.
    ///
    /// `Fn` can be coerced to `FnMut` or `FnOnce`.
    /// `FnMut` can be coerced to `FnOnce`.
    /// `FnOnce` cannot be coerced to anything.
    pub fn can_coerce_to(&self, other: ClosureKind) -> bool {
        matches!(
            (self, other),
            (ClosureKind::Fn, _)
                | (ClosureKind::FnMut, ClosureKind::FnMut | ClosureKind::FnOnce)
                | (ClosureKind::FnOnce, ClosureKind::FnOnce)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_closure_kind_from_captures() {
        // No captures → Fn
        let empty: Vec<(String, Mutability)> = vec![];
        assert_eq!(ClosureKind::from_captures(&empty), ClosureKind::Fn);

        // Only shared captures → Fn
        let shared_captures = vec![
            ("x".to_string(), Mutability::Shared),
            ("y".to_string(), Mutability::Shared),
        ];
        assert_eq!(
            ClosureKind::from_captures(&shared_captures),
            ClosureKind::Fn
        );

        // Any mutable capture → FnMut
        let mut_captures = vec![
            ("x".to_string(), Mutability::Shared),
            ("y".to_string(), Mutability::Mutable),
        ];
        assert_eq!(
            ClosureKind::from_captures(&mut_captures),
            ClosureKind::FnMut
        );

        // All mutable → FnMut
        let all_mut = vec![("x".to_string(), Mutability::Mutable)];
        assert_eq!(ClosureKind::from_captures(&all_mut), ClosureKind::FnMut);
    }

    #[test]
    fn test_closure_kind_coercion() {
        // Fn can coerce to anything
        assert!(ClosureKind::Fn.can_coerce_to(ClosureKind::Fn));
        assert!(ClosureKind::Fn.can_coerce_to(ClosureKind::FnMut));
        assert!(ClosureKind::Fn.can_coerce_to(ClosureKind::FnOnce));

        // FnMut can coerce to FnMut or FnOnce
        assert!(!ClosureKind::FnMut.can_coerce_to(ClosureKind::Fn));
        assert!(ClosureKind::FnMut.can_coerce_to(ClosureKind::FnMut));
        assert!(ClosureKind::FnMut.can_coerce_to(ClosureKind::FnOnce));

        // FnOnce can only be FnOnce
        assert!(!ClosureKind::FnOnce.can_coerce_to(ClosureKind::Fn));
        assert!(!ClosureKind::FnOnce.can_coerce_to(ClosureKind::FnMut));
        assert!(ClosureKind::FnOnce.can_coerce_to(ClosureKind::FnOnce));
    }
}
