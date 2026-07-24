// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Undefined Behavior Detection and Categorization
//!
//! This module defines all categories of undefined behavior in C and
//! provides a consistent error type for operations that can trigger UB.
//!
//! ## Design Philosophy
//!
//! C has extensive undefined behavior. Rather than trying to define
//! what happens when UB occurs, we detect it and report the specific
//! kind of UB. This allows:
//!
//! 1. **Verification**: Prove that programs never trigger UB
//! 2. **Testing**: Detect UB in test runs
//! 3. **Debugging**: Clear error messages about what went wrong
//!
//! ## UB Categories
//!
//! We categorize UB following the C standard and common tooling:
//!
//! - **Memory Safety**: null deref, use-after-free, out-of-bounds
//! - **Integer Overflow**: signed overflow, division by zero
//! - **Type Punning**: strict aliasing violations
//! - **Concurrency**: data races (when we add threading)
//! - **Misc**: infinite loops without side effects, etc.
//!
//! ## References
//!
//! - C11 standard Annex J.2 (Undefined behavior)
//! - UBSan (LLVM's undefined behavior sanitizer)
//! - Cerberus C semantics

use serde::{Deserialize, Serialize};
use std::fmt;
use thiserror::Error;

/// Categories of undefined behavior in C
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Error)]
pub enum UBKind {
    // === Memory Safety ===
    /// Dereferencing a null pointer
    #[error("null pointer dereference")]
    NullDeref,

    /// Using memory after it has been freed
    #[error("use after free")]
    UseAfterFree,

    /// Freeing memory that was already freed
    #[error("double free")]
    DoubleFree,

    /// Freeing a pointer that wasn't from malloc
    #[error("invalid free (pointer not from malloc)")]
    InvalidFree,

    /// Accessing memory outside allocated bounds
    #[error("out of bounds memory access")]
    OutOfBounds,

    /// Invalid pointer (garbage value, etc.)
    #[error("invalid pointer")]
    InvalidPointer,

    /// Unaligned memory access
    #[error("unaligned memory access")]
    UnalignedAccess,

    /// Reading uninitialized memory
    #[error("read of uninitialized memory")]
    UninitializedRead,

    /// Using memcpy with overlapping regions
    #[error("memcpy with overlapping source and destination")]
    OverlappingMemcpy,

    /// Accessing memory through incompatible pointer type
    #[error("strict aliasing violation")]
    StrictAliasingViolation,

    /// Read permission violation
    #[error("read permission violation")]
    ReadViolation,

    /// Write permission violation
    #[error("write permission violation")]
    WriteViolation,

    // === Integer Arithmetic ===
    /// Signed integer overflow
    #[error("signed integer overflow")]
    SignedOverflow,

    /// Division by zero
    #[error("division by zero")]
    DivisionByZero,

    /// Shift by negative amount or >= width
    #[error("invalid shift: {0}")]
    InvalidShift(String),

    /// INT_MIN % -1 or INT_MIN / -1
    #[error("division overflow")]
    DivisionOverflow,

    // === Floating Point ===
    /// Float-to-int conversion overflow
    #[error("float to integer overflow")]
    FloatToIntOverflow,

    // === Pointer Arithmetic ===
    /// Pointer arithmetic overflow
    #[error("pointer arithmetic overflow")]
    PointerOverflow,

    /// Comparing pointers to different objects
    #[error("comparing pointers to different objects")]
    InvalidPointerComparison,

    /// Subtracting pointers to different objects
    #[error("subtracting pointers to different objects")]
    InvalidPointerSubtraction,

    // === Type System ===
    /// Accessing wrong union member
    #[error("accessing inactive union member")]
    WrongUnionMember,

    /// Modifying const-qualified object
    #[error("modifying const-qualified object")]
    ModifyConst,

    // === Control Flow ===
    /// Non-void function doesn't return a value
    #[error("non-void function missing return value")]
    MissingReturn,

    /// A `_Noreturn` function (C11 6.7.4) can return to its caller —
    /// either via a reachable `return` statement or by falling off the
    /// end of its body. A `_Noreturn` function that returns is undefined
    /// behavior (C11 6.7.4p2). The payload names the offending function.
    #[error("_Noreturn function '{0}' can return to its caller")]
    NoreturnReturns(String),

    /// Reaching end of main without return
    #[error("reaching end of main without return")]
    NoMainReturn,

    /// Function call with wrong number of arguments
    #[error("function call argument count mismatch")]
    ArgumentCountMismatch,

    /// Function call with incompatible argument type
    #[error("function call argument type mismatch")]
    ArgumentTypeMismatch,

    // === Concurrency (future) ===
    /// Data race (concurrent read/write without synchronization)
    #[error("data race")]
    DataRace,

    // === Misc ===
    /// va_arg with incorrect type
    #[error("va_arg with incompatible type")]
    InvalidVaArg,

    /// Recursive function with unbounded recursion
    #[error("stack overflow")]
    StackOverflow,

    /// Generic/other UB not covered above
    #[error("undefined behavior: {0}")]
    Other(String),
}

/// Result type for operations that may trigger UB
pub type UBResult<T> = Result<T, UBKind>;

/// A UB detection report
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UBReport {
    /// The kind of UB detected
    pub kind: UBKind,
    /// Source location (if available)
    pub location: Option<SourceLocation>,
    /// Additional context
    pub context: Vec<String>,
    /// Stack trace (if available)
    pub stack: Vec<StackFrame>,
}

/// Source location information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceLocation {
    /// File name
    pub file: String,
    /// Line number (1-based)
    pub line: u32,
    /// Column number (1-based)
    pub column: u32,
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

/// Stack frame for error reporting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StackFrame {
    /// Function name
    pub function: String,
    /// Source location (if available)
    pub location: Option<SourceLocation>,
}

impl UBReport {
    /// Create a new UB report
    pub fn new(kind: UBKind) -> Self {
        Self {
            kind,
            location: None,
            context: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// Add source location
    #[must_use]
    pub fn with_location(mut self, loc: SourceLocation) -> Self {
        self.location = Some(loc);
        self
    }

    /// Add context message
    #[must_use]
    pub fn with_context(mut self, msg: impl Into<String>) -> Self {
        self.context.push(msg.into());
        self
    }

    /// Add stack frame
    #[must_use]
    pub fn with_frame(mut self, frame: StackFrame) -> Self {
        self.stack.push(frame);
        self
    }
}

impl fmt::Display for UBReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UNDEFINED BEHAVIOR: {}", self.kind)?;

        if let Some(ref loc) = self.location {
            write!(f, " at {loc}")?;
        }

        if !self.context.is_empty() {
            writeln!(f)?;
            for ctx in &self.context {
                writeln!(f, "  note: {ctx}")?;
            }
        }

        if !self.stack.is_empty() {
            writeln!(f, "Stack trace:")?;
            for frame in &self.stack {
                write!(f, "  in {}", frame.function)?;
                if let Some(ref loc) = frame.location {
                    write!(f, " at {loc}")?;
                }
                writeln!(f)?;
            }
        }

        Ok(())
    }
}

/// Check helpers for common UB conditions
pub mod checks {
    use super::*;

    /// Check for signed integer overflow in addition
    pub fn check_add_overflow(a: i64, b: i64) -> UBResult<i64> {
        a.checked_add(b).ok_or(UBKind::SignedOverflow)
    }

    /// Check for signed integer overflow in subtraction
    pub fn check_sub_overflow(a: i64, b: i64) -> UBResult<i64> {
        a.checked_sub(b).ok_or(UBKind::SignedOverflow)
    }

    /// Check for signed integer overflow in multiplication
    pub fn check_mul_overflow(a: i64, b: i64) -> UBResult<i64> {
        a.checked_mul(b).ok_or(UBKind::SignedOverflow)
    }

    /// Check for division by zero and overflow
    pub fn check_div(a: i64, b: i64) -> UBResult<i64> {
        if b == 0 {
            return Err(UBKind::DivisionByZero);
        }
        // INT_MIN / -1 overflows
        if a == i64::MIN && b == -1 {
            return Err(UBKind::DivisionOverflow);
        }
        Ok(a / b)
    }

    /// Check for modulo by zero and overflow
    pub fn check_mod(a: i64, b: i64) -> UBResult<i64> {
        if b == 0 {
            return Err(UBKind::DivisionByZero);
        }
        // INT_MIN % -1 is UB
        if a == i64::MIN && b == -1 {
            return Err(UBKind::DivisionOverflow);
        }
        Ok(a % b)
    }

    /// Check for valid shift amount
    pub fn check_shift(amount: i64, bit_width: u32) -> UBResult<()> {
        if amount < 0 {
            return Err(UBKind::InvalidShift("negative shift amount".to_string()));
        }
        if amount >= bit_width as i64 {
            return Err(UBKind::InvalidShift(format!(
                "shift amount {amount} >= bit width {bit_width}"
            )));
        }
        Ok(())
    }

    /// Check left shift for overflow (shifting into sign bit is UB for signed)
    pub fn check_shl_overflow(value: i64, amount: u32, bit_width: u32) -> UBResult<i64> {
        check_shift(amount as i64, bit_width)?;

        // For signed values, we need to check if we shift into the sign bit
        if value < 0 {
            return Err(UBKind::SignedOverflow);
        }

        // Shifting zero is always well-defined (0 << amount == 0) and would
        // otherwise underflow the `63 - leading_zeros()` computation below,
        // since 0i64.leading_zeros() == 64.
        if value == 0 {
            return Ok(0);
        }

        // Check if result would overflow (value > 0 here, so leading_zeros() <= 63
        // and the subtraction cannot underflow).
        let max_shift = 63 - value.leading_zeros();
        if amount > max_shift {
            return Err(UBKind::SignedOverflow);
        }

        Ok(value << amount)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ub_display() {
        let ub = UBKind::NullDeref;
        assert_eq!(format!("{ub}"), "null pointer dereference");

        let ub = UBKind::InvalidShift("negative".to_string());
        assert_eq!(format!("{ub}"), "invalid shift: negative");
    }

    #[test]
    fn test_ub_report() {
        let report = UBReport::new(UBKind::OutOfBounds)
            .with_location(SourceLocation {
                file: "test.c".to_string(),
                line: 42,
                column: 10,
            })
            .with_context("accessing array element 10 of array with size 5")
            .with_frame(StackFrame {
                function: "foo".to_string(),
                location: None,
            });

        let s = format!("{report}");
        assert!(s.contains("out of bounds"));
        assert!(s.contains("test.c:42:10"));
        assert!(s.contains("array element 10"));
    }

    #[test]
    fn test_checked_add() {
        assert_eq!(checks::check_add_overflow(1, 2), Ok(3));
        assert_eq!(
            checks::check_add_overflow(i64::MAX, 1),
            Err(UBKind::SignedOverflow)
        );
    }

    #[test]
    fn test_checked_sub() {
        assert_eq!(checks::check_sub_overflow(5, 3), Ok(2));
        assert_eq!(
            checks::check_sub_overflow(i64::MIN, 1),
            Err(UBKind::SignedOverflow)
        );
    }

    #[test]
    fn test_checked_mul() {
        assert_eq!(checks::check_mul_overflow(3, 4), Ok(12));
        assert_eq!(
            checks::check_mul_overflow(i64::MAX, 2),
            Err(UBKind::SignedOverflow)
        );
    }

    #[test]
    fn test_checked_div() {
        assert_eq!(checks::check_div(10, 3), Ok(3));
        assert_eq!(checks::check_div(10, 0), Err(UBKind::DivisionByZero));
        assert_eq!(
            checks::check_div(i64::MIN, -1),
            Err(UBKind::DivisionOverflow)
        );
    }

    #[test]
    fn test_checked_mod() {
        assert_eq!(checks::check_mod(10, 3), Ok(1));
        assert_eq!(checks::check_mod(10, 0), Err(UBKind::DivisionByZero));
        assert_eq!(
            checks::check_mod(i64::MIN, -1),
            Err(UBKind::DivisionOverflow)
        );
    }

    #[test]
    fn test_checked_shift() {
        checks::check_shift(5, 32).expect("shift 5 within 32-bit width should succeed");
        assert!(
            matches!(checks::check_shift(-1, 32), Err(UBKind::InvalidShift(_))),
            "negative shift should produce InvalidShift"
        );
        assert!(
            matches!(checks::check_shift(32, 32), Err(UBKind::InvalidShift(_))),
            "shift >= bit_width should produce InvalidShift"
        );
        assert!(
            matches!(checks::check_shift(100, 32), Err(UBKind::InvalidShift(_))),
            "shift >> bit_width should produce InvalidShift"
        );
    }

    #[test]
    fn test_check_shl_overflow_zero_value_does_not_underflow() {
        // Regression: `0 << amount` is legal C. Before the fix, computing
        // `63 - 0i64.leading_zeros()` == `63 - 64` underflowed, panicking in
        // debug builds ("attempt to subtract with overflow") and wrapping to
        // u32::MAX in release. Shifting zero must yield zero for any valid amount.
        assert_eq!(
            checks::check_shl_overflow(0, 3, 32),
            Ok(0),
            "0 << 3 is well-defined and must not underflow"
        );
        assert_eq!(
            checks::check_shl_overflow(0, 0, 32),
            Ok(0),
            "0 << 0 is well-defined and must not underflow"
        );
        assert_eq!(
            checks::check_shl_overflow(0, 31, 32),
            Ok(0),
            "0 shifted by max valid 32-bit amount is still zero"
        );

        // Correct-path behavior for nonzero values is unchanged by the fix
        // (the `value == 0` guard is only reached when value == 0).
        assert_eq!(checks::check_shl_overflow(1, 0, 32), Ok(1), "1 << 0 == 1");
        assert_eq!(checks::check_shl_overflow(8, 3, 32), Ok(64), "8 << 3 == 64");
        assert_eq!(
            checks::check_shl_overflow(255, 8, 32),
            Err(UBKind::SignedOverflow),
            "255 << 8 exceeds the value's magnitude budget (unchanged behavior)"
        );
        assert_eq!(
            checks::check_shl_overflow(-1, 1, 32),
            Err(UBKind::SignedOverflow),
            "shifting a negative value is signed overflow"
        );
    }
}
