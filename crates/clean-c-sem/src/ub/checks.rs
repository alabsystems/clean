//! Check helpers for common UB conditions.
//!
//! Extracted verbatim from the `checks` inline module of `ub.rs`; every
//! helper maps one C operation to the [`UBKind`] it can raise.

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
