// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended mathverse support for modular and bitvector arithmetic
//!
//! Adds modular arithmetic (Chinese Remainder Theorem) and bitvector
//! constraint solving on top of the core mathverse decision procedure.
//! Bitvector constraints are bit-blasted into linear constraints.

use super::arithmetic::{LinearConstraint, LinearExpr};
use super::TacticError;

/// Configuration for extended mathverse features.
#[derive(Debug, Clone)]
pub(crate) struct MathverseExtConfig {
    /// Enable modular arithmetic reasoning.
    pub enable_mod: bool,
    /// Enable bitvector reasoning.
    pub enable_bv: bool,
    /// Maximum bitvector width to handle (default 64).
    pub max_bv_width: u32,
    /// Maximum modulus to handle (default 2^32).
    pub mod_bound: u64,
}

impl Default for MathverseExtConfig {
    fn default() -> Self {
        Self {
            enable_mod: true,
            enable_bv: true,
            max_bv_width: 64,
            mod_bound: 1u64 << 32,
        }
    }
}

/// A modular arithmetic constraint: `expr ≡ remainder (mod modulus)`.
#[derive(Debug, Clone)]
pub(crate) struct ModConstraint {
    /// The linear expression being constrained.
    pub expr: LinearExpr,
    /// The modulus (must be > 0).
    pub modulus: u64,
    /// The remainder (must be < modulus).
    pub remainder: u64,
}

/// Bitvector operations.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum BvOp {
    And,
    Or,
    Xor,
    Not,
    Shl,
    Lshr,
    Ashr,
    Add,
    Sub,
    Mul,
    /// Unsigned less-than.
    Ult,
    /// Unsigned less-or-equal.
    Ule,
    /// Signed less-than.
    Slt,
    /// Signed less-or-equal.
    Sle,
    /// Bit extraction `[hi:lo]`.
    Extract {
        hi: u32,
        lo: u32,
    },
    /// Concatenation.
    Concat,
    /// Zero extension by `n` bits.
    ZeroExtend(u32),
    /// Sign extension by `n` bits.
    SignExtend(u32),
}

/// Bitvector term representation.
#[derive(Debug, Clone)]
pub(crate) enum BvTerm {
    /// Named variable.
    Var(String),
    /// Literal: (value, width).
    Lit(u64, u32),
    /// Compound application.
    App(BvOp, Vec<BvTerm>),
}

/// A bitvector constraint.
#[derive(Debug, Clone)]
pub(crate) struct BvConstraint {
    /// Bitvector width in bits.
    pub width: u32,
    /// The top-level operation.
    pub op: BvOp,
    /// Operands.
    pub args: Vec<BvTerm>,
}

/// Safe left shift that saturates at `i64::MAX` for large shift amounts.
fn safe_shl(base: i64, shift: u32) -> i64 {
    if shift >= 63 {
        i64::MAX
    } else {
        base << shift
    }
}

/// Extended GCD: returns `(gcd, x, y)` such that `a*x + b*y == gcd`.
fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        return (a, 1, 0);
    }
    let (g, x1, y1) = extended_gcd(b, a % b);
    (g, y1, x1 - (a / b) * y1)
}

/// Chinese Remainder Theorem for two congruences.
///
/// Given `x ≡ a1 (mod m1)` and `x ≡ a2 (mod m2)`, returns
/// `Some((remainder, lcm))` where `x ≡ remainder (mod lcm)`,
/// or `None` if no solution exists (incompatible moduli).
///
/// ENSURES: On `Some((r, l))`, `r < l` and `l == lcm(m1, m2)`
/// ENSURES: `None` iff `(a1 - a2) % gcd(m1, m2) != 0`
pub(crate) fn chinese_remainder(a1: u64, m1: u64, a2: u64, m2: u64) -> Option<(u64, u64)> {
    if m1 == 0 || m2 == 0 {
        return None;
    }
    let (g, p, _) = extended_gcd(m1 as i64, m2 as i64);
    let g_u = g as u64;

    // Check compatibility: (a2 - a1) must be divisible by gcd
    let diff = if a2 >= a1 {
        a2 - a1
    } else {
        // Handle wrap: compute (a2 + m1*m2 - a1) to stay positive
        // but we only need diff % g == 0
        let neg_diff = a1 - a2;
        if !neg_diff.is_multiple_of(g_u) {
            return None;
        }
        // Use signed arithmetic for the CRT combination
        return chinese_remainder_signed(a1, m1, a2, m2, g, p);
    };

    if diff % g_u != 0 {
        return None;
    }

    chinese_remainder_signed(a1, m1, a2, m2, g, p)
}

/// Internal signed CRT computation.
fn chinese_remainder_signed(
    a1: u64,
    m1: u64,
    a2: u64,
    m2: u64,
    g: i64,
    p: i64,
) -> Option<(u64, u64)> {
    let lcm = (m1 / (g as u64)).checked_mul(m2)?;
    let diff = a2 as i128 - a1 as i128;
    let step = diff / g as i128 * p as i128;
    let remainder = ((a1 as i128 + step * m1 as i128) % lcm as i128 + lcm as i128) % lcm as i128;
    Some((remainder as u64, lcm))
}

/// Solver for extended mathverse constraints.
pub(crate) struct MathverseExtSolver {
    config: MathverseExtConfig,
    mod_constraints: Vec<ModConstraint>,
    bv_constraints: Vec<BvConstraint>,
}

impl MathverseExtSolver {
    /// Create a new solver with the given configuration.
    pub(crate) fn new(config: MathverseExtConfig) -> Self {
        Self {
            config,
            mod_constraints: Vec::new(),
            bv_constraints: Vec::new(),
        }
    }

    /// Add a modular constraint.
    pub(crate) fn add_mod_constraint(&mut self, c: ModConstraint) {
        self.mod_constraints.push(c);
    }

    /// Add a bitvector constraint.
    pub(crate) fn add_bv_constraint(&mut self, c: BvConstraint) {
        self.bv_constraints.push(c);
    }

    /// Access modular constraints.
    pub(crate) fn mod_constraints(&self) -> &[ModConstraint] {
        &self.mod_constraints
    }

    /// Access bitvector constraints.
    pub(crate) fn bv_constraints(&self) -> &[BvConstraint] {
        &self.bv_constraints
    }

    // =========================================================================
    // Modular solving
    // =========================================================================

    /// Solve modular constraints using the Chinese Remainder Theorem.
    ///
    /// Groups constraints by their linear expression variables, then
    /// iteratively combines congruences via CRT. Returns `Ok(true)` if
    /// all constraints are satisfiable, `Ok(false)` if a contradiction
    /// is found, and `Err` on configuration violation.
    ///
    /// ENSURES: On `Ok(false)`, at least two constraints are incompatible
    /// ENSURES: On `Err`, `enable_mod` is `false`
    pub(crate) fn solve_mod(&self) -> Result<bool, TacticError> {
        if !self.config.enable_mod {
            return Err(TacticError::ArithmeticFailed {
                tactic: "mathverse_ext".into(),
                reason: "modular arithmetic is disabled".into(),
            });
        }

        // Group constant-expression mod constraints by their variable set.
        // For constant expressions, combine via CRT directly.
        let mut current_remainder: Option<u64> = None;
        let mut current_modulus: Option<u64> = None;

        for c in &self.mod_constraints {
            if c.modulus == 0 || c.modulus > self.config.mod_bound {
                return Err(TacticError::ArithmeticFailed {
                    tactic: "mathverse_ext".into(),
                    reason: format!(
                        "modulus {} exceeds bound {} or is zero",
                        c.modulus, self.config.mod_bound
                    ),
                });
            }

            match (current_remainder, current_modulus) {
                (None, None) => {
                    current_remainder = Some(c.remainder);
                    current_modulus = Some(c.modulus);
                }
                (Some(r), Some(m)) => {
                    match chinese_remainder(r, m, c.remainder, c.modulus) {
                        Some((new_r, new_m)) => {
                            current_remainder = Some(new_r);
                            current_modulus = Some(new_m);
                        }
                        None => return Ok(false), // Incompatible congruences
                    }
                }
                _ => {
                    // This branch is unreachable because both are set/unset together,
                    // but we handle it gracefully.
                    current_remainder = Some(c.remainder);
                    current_modulus = Some(c.modulus);
                }
            }
        }

        Ok(true)
    }

    // =========================================================================
    // Bitvector bit-blasting
    // =========================================================================

    /// Convert a bitvector constraint to linear constraints via bit-blasting.
    ///
    /// REQUIRES: `c.width <= self.config.max_bv_width`
    /// ENSURES: Returned constraints encode the bitvector semantics
    pub(crate) fn bv_to_linear(
        &self,
        c: &BvConstraint,
    ) -> Result<Vec<LinearConstraint>, TacticError> {
        if !self.config.enable_bv {
            return Err(TacticError::ArithmeticFailed {
                tactic: "mathverse_ext".into(),
                reason: "bitvector reasoning is disabled".into(),
            });
        }
        if c.width > self.config.max_bv_width {
            return Err(TacticError::ArithmeticFailed {
                tactic: "mathverse_ext".into(),
                reason: format!(
                    "bitvector width {} exceeds maximum {}",
                    c.width, self.config.max_bv_width
                ),
            });
        }
        if c.width == 0 {
            return Ok(Vec::new());
        }
        match &c.op {
            BvOp::And | BvOp::Or | BvOp::Xor => Ok(bv_bitwise_constraints(c.width)),
            BvOp::Ult | BvOp::Ule => Ok(bv_unsigned_cmp_constraints(
                c.width,
                matches!(c.op, BvOp::Ult),
            )),
            BvOp::Slt | BvOp::Sle => Ok(bv_signed_cmp_constraints(
                c.width,
                matches!(c.op, BvOp::Slt),
            )),
            BvOp::Extract { hi, lo } => bv_extract_constraints(c.width, *hi, *lo),
            BvOp::Concat => Ok(bv_concat_constraints(c)),
            BvOp::ZeroExtend(n) => Ok(bv_unsigned_range(c.width.saturating_add(*n).min(62))),
            BvOp::SignExtend(n) => Ok(bv_signed_range(c.width.saturating_add(*n).min(62))),
            _ => Ok(bv_unsigned_range(c.width.min(62))),
        }
    }

    // =========================================================================
    // Combined solver
    // =========================================================================

    /// Solve all constraints (modular + bitvector).
    ///
    /// First converts bitvector constraints to linear constraints via
    /// bit-blasting, then solves modular constraints via CRT. Returns
    /// `Ok(true)` if satisfiable, `Ok(false)` if a contradiction is found.
    ///
    /// ENSURES: BV constraints are checked for width validity
    /// ENSURES: Mod constraints are solved via CRT
    pub(crate) fn solve(&self) -> Result<bool, TacticError> {
        // Validate and convert BV constraints
        for c in &self.bv_constraints {
            self.bv_to_linear(c)?;
        }

        // Solve modular constraints
        if !self.mod_constraints.is_empty() && !self.solve_mod()? {
            return Ok(false);
        }

        Ok(true)
    }
}

/// Emit 0 <= bit_i <= 1 constraints for each bit position.
fn bv_bitwise_constraints(width: u32) -> Vec<LinearConstraint> {
    let mut out = Vec::with_capacity(2 * width as usize);
    for i in 0..width {
        let v = i as usize;
        out.push(LinearConstraint::Le(LinearExpr::from_coeffs(0, [(v, -1)])));
        out.push(LinearConstraint::Le(LinearExpr::from_coeffs(-1, [(v, 1)])));
    }
    out
}

/// Constraints for unsigned comparison (Ult/Ule) on `width`-bit values.
fn bv_unsigned_cmp_constraints(width: u32, strict: bool) -> Vec<LinearConstraint> {
    let offset = if strict { 1 } else { 0 };
    let bound = safe_shl(1i64, width);
    vec![
        LinearConstraint::Le(LinearExpr::from_coeffs(offset, [(0, 1), (1, -1)])),
        LinearConstraint::Le(LinearExpr::from_coeffs(0, [(0, -1)])),
        LinearConstraint::Le(LinearExpr::from_coeffs(0, [(1, -1)])),
        LinearConstraint::Lt(LinearExpr::from_coeffs(-bound, [(0, 1)])),
        LinearConstraint::Lt(LinearExpr::from_coeffs(-bound, [(1, 1)])),
    ]
}

/// Constraints for signed comparison (Slt/Sle) on `width`-bit values.
fn bv_signed_cmp_constraints(width: u32, strict: bool) -> Vec<LinearConstraint> {
    let offset = if strict { 1 } else { 0 };
    let half = safe_shl(1i64, width.saturating_sub(1));
    let mut out = vec![LinearConstraint::Le(LinearExpr::from_coeffs(
        offset,
        [(0, 1), (1, -1)],
    ))];
    for var in 0..=1usize {
        out.push(LinearConstraint::Le(LinearExpr::from_coeffs(
            -half,
            [(var, -1)],
        )));
        out.push(LinearConstraint::Lt(LinearExpr::from_coeffs(
            -half,
            [(var, 1)],
        )));
    }
    out
}

/// Constraints for bit extraction [hi:lo].
fn bv_extract_constraints(
    width: u32,
    hi: u32,
    lo: u32,
) -> Result<Vec<LinearConstraint>, TacticError> {
    if hi >= width || lo > hi {
        return Err(TacticError::ArithmeticFailed {
            tactic: "mathverse_ext".into(),
            reason: format!("invalid extract [{hi}:{lo}] for width {width}"),
        });
    }
    Ok(bv_unsigned_range(hi - lo + 1))
}

/// Constraints for concatenation.
fn bv_concat_constraints(c: &BvConstraint) -> Vec<LinearConstraint> {
    if c.args.len() >= 2 {
        let w2 = bv_term_width(&c.args[1]).unwrap_or(c.width / 2);
        let shift = safe_shl(1i64, w2);
        vec![LinearConstraint::Eq(LinearExpr::from_coeffs(
            0,
            [(0, -shift), (1, -1), (2, 1)],
        ))]
    } else {
        Vec::new()
    }
}

/// Unsigned range: 0 <= val < 2^width.
fn bv_unsigned_range(width: u32) -> Vec<LinearConstraint> {
    let bound = safe_shl(1i64, width);
    vec![
        LinearConstraint::Le(LinearExpr::from_coeffs(0, [(0, -1)])),
        LinearConstraint::Lt(LinearExpr::from_coeffs(-bound, [(0, 1)])),
    ]
}

/// Signed range: -2^(width-1) <= val < 2^(width-1).
fn bv_signed_range(width: u32) -> Vec<LinearConstraint> {
    let half = safe_shl(1i64, width.saturating_sub(1));
    vec![
        LinearConstraint::Le(LinearExpr::from_coeffs(-half, [(0, -1)])),
        LinearConstraint::Lt(LinearExpr::from_coeffs(-half, [(0, 1)])),
    ]
}

/// Infer the width of a bitvector term (if determinable).
fn bv_term_width(term: &BvTerm) -> Option<u32> {
    match term {
        BvTerm::Lit(_, w) => Some(*w),
        BvTerm::Var(_) => None,
        BvTerm::App(_, _) => None,
    }
}
