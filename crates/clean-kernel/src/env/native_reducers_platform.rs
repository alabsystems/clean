// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for platform-dependent constants.
//!
//! `System.Platform.getNumBits` is `@[extern]` with no computational body.
//! On a 64-bit platform (which clean targets), it returns `⟨64, Or.inr rfl⟩`.
//! Without a native reducer, any proof that depends on `numBits` (= `(getNumBits ()).val`)
//! gets stuck because `getNumBits ()` cannot be reduced.
//!
//! This file provides native reducers for:
//! - `System.Platform.getNumBits` → `Subtype.mk 64 (Or.inr (Eq.refl 64))`
//! - `System.Platform.getIsWindows` → `Bool.false`
//! - `System.Platform.getIsOSX` → `Bool.true` (macOS target)
//! - `System.Platform.getIsEmscripten` → `Bool.false`
//!
//! These unblock 934 heartbeat-exceeded constants in Init, including all
//! `USize.size_*`, `Int32.toISize_*`, and platform-dependent proof obligations.
//!
//! Reference: Lean 4 Init/Prelude.lean:2284-2297
//!   `@[extern "lean_system_platform_nbits"] opaque getNumBits : Unit → { n : Nat // n = 32 ∨ n = 64 }`
//!   `def numBits : Nat := (getNumBits ()).val`
//!   `theorem numBits_eq : numBits = 32 ∨ numBits = 64 := (getNumBits ()).property`

//! NOTE (carrier-parity Phase 1, §7.4): the `System.Platform.getNumBits`
//! reducer that computed `⟨64, …⟩` was DELETED — it was the silent
//! `numBits = 64` def-eq excess. `getNumBits` is now a seeded OPAQUE and
//! `numBits` is genuinely abstract in the kernel, matching Lean exactly. Only
//! the platform boolean reducers (OS-target facts, not a numBits excess) remain.

use crate::env::Environment;
use crate::expr::Expr;

/// Well-known names for platform native reducers.
mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static GET_IS_WINDOWS: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("System.Platform.getIsWindows"));
    pub(crate) static GET_IS_OSX: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("System.Platform.getIsOSX"));
    pub(crate) static GET_IS_EMSCRIPTEN: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("System.Platform.getIsEmscripten"));
}

/// Well-known names for the platform boolean reducer results.
mod expr_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    pub(crate) static BOOL_FALSE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Bool.false"));
}

/// Native reducer for `System.Platform.getIsWindows : Unit → Bool`.
///
/// Returns `Bool.false` (clean runs on macOS/Linux, not Windows).
fn reduce_get_is_windows(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    Some(Expr::const_(expr_names::BOOL_FALSE.clone(), vec![]))
}

/// Native reducer for `System.Platform.getIsOSX : Unit → Bool`.
///
/// Returns `Bool.true` for macOS targets.
fn reduce_get_is_osx(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    if cfg!(target_os = "macos") {
        Some(Expr::const_(expr_names::BOOL_TRUE.clone(), vec![]))
    } else {
        Some(Expr::const_(expr_names::BOOL_FALSE.clone(), vec![]))
    }
}

/// Native reducer for `System.Platform.getIsEmscripten : Unit → Bool`.
///
/// Returns `Bool.false` (clean never targets Emscripten).
fn reduce_get_is_emscripten(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    Some(Expr::const_(expr_names::BOOL_FALSE.clone(), vec![]))
}

/// Register all platform native reducers on the environment.
impl Environment {
    pub(crate) fn init_platform_native_reducers(&mut self) {
        self.register_native_reducer(names::GET_IS_WINDOWS.clone(), reduce_get_is_windows);
        self.register_native_reducer(names::GET_IS_OSX.clone(), reduce_get_is_osx);
        self.register_native_reducer(names::GET_IS_EMSCRIPTEN.clone(), reduce_get_is_emscripten);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::expr::ExprKind;

    /// Q6 (carrier-parity §7.4): the `getNumBits` reducer is DELETED, so
    /// `System.Platform.getNumBits ()` must NOT reduce natively — `numBits` is
    /// abstract, matching Lean's kernel stuckness.
    #[test]
    fn test_get_num_bits_no_longer_registered() {
        let mut env = Environment::new();
        env.init_platform_native_reducers();
        assert!(
            env.get_native_reducer(&crate::name::Name::from_string(
                "System.Platform.getNumBits"
            ))
            .is_none(),
            "getNumBits reducer must be gone (P1 removed the numBits=64 excess)"
        );
    }

    #[test]
    fn test_reduce_get_is_windows_returns_false() {
        let unit_val = Expr::const_str("Unit.unit");
        let result = reduce_get_is_windows(&[&unit_val]);
        assert!(result.is_some());
        let val = result.unwrap();
        let head = val.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    #[test]
    fn test_reduce_get_is_emscripten_returns_false() {
        let unit_val = Expr::const_str("Unit.unit");
        let result = reduce_get_is_emscripten(&[&unit_val]);
        assert!(result.is_some());
        let val = result.unwrap();
        let head = val.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    #[test]
    fn test_reduce_get_is_osx_returns_bool() {
        let unit_val = Expr::const_str("Unit.unit");
        let result = reduce_get_is_osx(&[&unit_val]);
        assert!(result.is_some());
        let val = result.unwrap();
        let head = val.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            // On macOS: Bool.true, on other: Bool.false
            let s = name.to_string();
            assert!(
                s == "Bool.true" || s == "Bool.false",
                "Expected Bool.true or Bool.false, got {s}"
            );
        } else {
            panic!("Expected Bool constant");
        }
    }

    #[test]
    fn test_platform_reducers_registered() {
        let mut env = Environment::new();
        env.init_platform_native_reducers();

        assert!(env.get_native_reducer(&names::GET_IS_WINDOWS).is_some());
        assert!(env.get_native_reducer(&names::GET_IS_OSX).is_some());
        assert!(env.get_native_reducer(&names::GET_IS_EMSCRIPTEN).is_some());
    }
}
