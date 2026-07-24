// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BV (Bitvector) theory checker.
//!
//! Validates bitvector theory lemmas by evaluating concrete BV operations
//! and detecting contradictions in BV constraints. Covers SMT-LIB QF_BV
//! operations: bitwise (and, or, xor, not), arithmetic (add, sub, mul, neg),
//! comparison (ult, slt, ule, sle), shift (shl, lshr, ashr), and
//! extract/concat/extend.
//!
//! ## Algorithm
//!
//! 1. Parse clause literals as BV equalities, disequalities, or predicates.
//! 2. Build an assignment map from concrete BV values.
//! 3. Evaluate BV operations where all operands are known.
//! 4. Detect contradictions: conflicting assignments or unsatisfiable predicates.
//! 5. For non-concrete cases, structurally accept (full bit-blasting deferred).
//!
//! ## Reference
//!
//! SMT-LIB BV theory: <https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml>

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "bv";

/// A fixed-width bitvector value.
///
/// Uses `u64` for widths <= 64. Wider bitvectors are not yet supported
/// (structurally accepted).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct BitVec {
    /// The value, masked to `width` bits.
    pub(crate) value: u64,
    /// Bit-width (1..=64).
    pub(crate) width: u32,
}

impl BitVec {
    /// Create a new bitvector, masking the value to the given width.
    ///
    /// # Panics (debug only)
    ///
    /// Debug-asserts `1 <= width <= 64`. Callers that build `BitVec`s from
    /// untrusted proof text (widths parsed from `(_ bvN width)` literals) must
    /// route through [`BitVec::try_new`] first, which rejects out-of-range
    /// widths without panicking. `as_signed` (and the signed comparisons that
    /// use it) shift by `width - 1`, which overflows for `width == 0` or
    /// `width > 64` — a hard abort under `overflow-checks`/`panic = "abort"`.
    #[must_use]
    pub(crate) fn new(value: u64, width: u32) -> Self {
        debug_assert!(width > 0 && width <= 64);
        Self {
            value: value & Self::mask(width),
            width,
        }
    }

    /// Fallible constructor: returns `None` for widths outside the supported
    /// `1..=64` range instead of building an invalid `BitVec`.
    ///
    /// This is the safe entry point for values whose width originates from
    /// untrusted proof text. Wider (or zero-width) bitvectors are not modeled
    /// by this `u64`-backed evaluator and must be structurally accepted rather
    /// than evaluated (see module docs).
    #[must_use]
    pub(crate) fn try_new(value: u64, width: u32) -> Option<Self> {
        if width == 0 || width > 64 {
            return None;
        }
        Some(Self::new(value, width))
    }

    /// Bitmask for a given width (all 1s in the lower `width` bits).
    #[must_use]
    fn mask(width: u32) -> u64 {
        if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        }
    }

    /// The mask for this bitvector's width.
    #[must_use]
    fn bitmask(&self) -> u64 {
        Self::mask(self.width)
    }

    /// Interpret as a signed value (sign-extend to i64).
    #[must_use]
    fn as_signed(&self) -> i64 {
        if self.width == 64 {
            self.value as i64
        } else {
            let sign_bit = 1u64 << (self.width - 1);
            if self.value & sign_bit != 0 {
                // Negative: sign-extend
                (self.value | !self.bitmask()) as i64
            } else {
                self.value as i64
            }
        }
    }

    // ── Bitwise operations ──

    #[must_use]
    pub(crate) fn bvand(self, other: Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        Self::new(self.value & other.value, self.width)
    }

    #[must_use]
    pub(crate) fn bvor(self, other: Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        Self::new(self.value | other.value, self.width)
    }

    #[must_use]
    pub(crate) fn bvxor(self, other: Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        Self::new(self.value ^ other.value, self.width)
    }

    #[must_use]
    pub(crate) fn bvnot(self) -> Self {
        Self::new(!self.value, self.width)
    }

    // ── Arithmetic operations (modular) ──

    #[must_use]
    pub(crate) fn bvadd(self, other: Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        Self::new(self.value.wrapping_add(other.value), self.width)
    }

    #[must_use]
    pub(crate) fn bvsub(self, other: Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        Self::new(self.value.wrapping_sub(other.value), self.width)
    }

    #[must_use]
    pub(crate) fn bvmul(self, other: Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        Self::new(self.value.wrapping_mul(other.value), self.width)
    }

    #[must_use]
    pub(crate) fn bvneg(self) -> Self {
        Self::new((!self.value).wrapping_add(1), self.width)
    }

    // ── Comparison operations ──

    #[must_use]
    pub(crate) fn bvult(self, other: Self) -> bool {
        debug_assert_eq!(self.width, other.width);
        self.value < other.value
    }

    #[must_use]
    pub(crate) fn bvule(self, other: Self) -> bool {
        debug_assert_eq!(self.width, other.width);
        self.value <= other.value
    }

    #[must_use]
    pub(crate) fn bvslt(self, other: Self) -> bool {
        debug_assert_eq!(self.width, other.width);
        self.as_signed() < other.as_signed()
    }

    #[must_use]
    pub(crate) fn bvsle(self, other: Self) -> bool {
        debug_assert_eq!(self.width, other.width);
        self.as_signed() <= other.as_signed()
    }

    // ── Shift operations ──

    #[must_use]
    pub(crate) fn bvshl(self, shift: Self) -> Self {
        debug_assert_eq!(self.width, shift.width);
        if shift.value >= u64::from(self.width) {
            Self::new(0, self.width)
        } else {
            Self::new(self.value << shift.value, self.width)
        }
    }

    #[must_use]
    pub(crate) fn bvlshr(self, shift: Self) -> Self {
        debug_assert_eq!(self.width, shift.width);
        if shift.value >= u64::from(self.width) {
            Self::new(0, self.width)
        } else {
            Self::new(self.value >> shift.value, self.width)
        }
    }

    #[must_use]
    pub(crate) fn bvashr(self, shift: Self) -> Self {
        debug_assert_eq!(self.width, shift.width);
        let signed = self.as_signed();
        if shift.value >= u64::from(self.width) {
            // All sign bits
            if signed < 0 {
                Self::new(Self::mask(self.width), self.width)
            } else {
                Self::new(0, self.width)
            }
        } else {
            Self::new((signed >> shift.value) as u64, self.width)
        }
    }

    // ── Extract / Concat / Extend ──

    /// Extract bits `[high:low]` (inclusive, 0-indexed from LSB).
    #[must_use]
    pub(crate) fn extract(self, high: u32, low: u32) -> Self {
        debug_assert!(high >= low);
        debug_assert!(high < self.width);
        let new_width = high - low + 1;
        Self::new(self.value >> low, new_width)
    }

    /// Concatenate: `self` is the high part, `other` is the low part.
    #[must_use]
    pub(crate) fn concat(self, other: Self) -> Self {
        let new_width = self.width + other.width;
        debug_assert!(new_width <= 64);
        Self::new((self.value << other.width) | other.value, new_width)
    }

    /// Zero-extend by `extra` bits.
    #[must_use]
    pub(crate) fn zero_extend(self, extra: u32) -> Self {
        let new_width = self.width + extra;
        debug_assert!(new_width <= 64);
        Self::new(self.value, new_width)
    }

    /// Sign-extend by `extra` bits.
    #[must_use]
    pub(crate) fn sign_extend(self, extra: u32) -> Self {
        let new_width = self.width + extra;
        debug_assert!(new_width <= 64);
        Self::new(self.as_signed() as u64, new_width)
    }
}

/// A BV constraint extracted from a clause literal.
#[derive(Debug, Clone)]
pub(crate) enum BvConstraint {
    /// `term = bv_constant`
    Eq(SmtTermId, SmtTermId),
    /// `term != bv_constant`
    Neq(SmtTermId, SmtTermId),
    /// BV predicate (comparison) that must hold.
    Pred {
        op: BvPredOp,
        lhs: SmtTermId,
        rhs: SmtTermId,
        negated: bool,
    },
}

/// BV comparison predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BvPredOp {
    Ult,
    Ule,
    Slt,
    Sle,
}

/// Check a BV theory lemma.
///
/// The clause is a blocking clause (disjunction). The negation of the clause
/// forms the conflict. We check whether the conflict is indeed unsatisfiable
/// by evaluating concrete bitvector operations.
///
/// Returns `KernelVerified` if a concrete contradiction is found,
/// `StructurallyAccepted` if the clause contains non-concrete terms that
/// cannot be fully evaluated, or `Trusted` on error.
pub(crate) fn check_bv_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "bv: empty clause");
    }

    // Parse the clause into BV constraints (negated, since the clause is a
    // blocking clause -- we negate to get conflict constraints).
    let mut constraints = Vec::with_capacity(clause.len());
    let mut all_concrete = true;

    for &lit in clause {
        match parse_bv_literal(dag, lit) {
            Some(c) => constraints.push(c),
            None => {
                all_concrete = false;
            }
        }
    }

    if constraints.is_empty() {
        return structural_accept(step_id, "bv: no parseable BV constraints");
    }

    // Fixpoint loop: propagate concrete values through equalities until no
    // new assignments are discovered. This handles cases like:
    //   x = 5, y = 0x0F, bvand(x, y) = 0xFF
    // where we first assign x and y, then evaluate bvand(x,y).
    let mut assignments: std::collections::HashMap<SmtTermId, BitVec> =
        std::collections::HashMap::new();

    // Cap iterations to prevent infinite loops on pathological inputs.
    let max_iters = constraints.len() + 1;
    for _ in 0..max_iters {
        let prev_count = assignments.len();

        for constraint in &constraints {
            if let BvConstraint::Eq(lhs_id, rhs_id) = constraint {
                // Try to evaluate both sides and propagate assignments.
                try_assign(dag, *lhs_id, *rhs_id, &mut assignments);
                try_assign(dag, *rhs_id, *lhs_id, &mut assignments);
            }
        }

        // If no new assignments were added, we've reached a fixpoint.
        if assignments.len() == prev_count {
            break;
        }
    }

    // Check all constraints for contradictions with the final assignment map.
    let has_contradiction = constraints
        .iter()
        .any(|c| is_contradiction(dag, c, &assignments));

    if has_contradiction {
        ok(step_id)
    } else if all_concrete {
        fail(
            step_id,
            "bv: no contradiction found in concrete constraints",
        )
    } else {
        structural_accept(
            step_id,
            "bv: non-concrete BV constraints, structurally accepted",
        )
    }
}

/// Try to assign a concrete value to a variable: if `val_id` evaluates to a
/// concrete BV and `term_id` is a variable, assign the value.
///
/// Only variables receive assignments. Constants and complex expressions
/// (function applications) are evaluated structurally -- assigning to them
/// would mask contradictions (e.g., assigning 0xFF to `bvand(x, y)` hides
/// the fact that `bvand(0x0F, 0x0F)` actually produces 0x0F).
fn try_assign(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    val_id: SmtTermId,
    assignments: &mut std::collections::HashMap<SmtTermId, BitVec>,
) {
    // Skip if already assigned.
    if assignments.contains_key(&term_id) {
        return;
    }
    // Only assign to variable terms.
    if let Some(SmtTerm::Var(..)) = dag.term(term_id) {
        if let Some(bv) = eval_bv_term(dag, val_id, assignments) {
            assignments.insert(term_id, bv);
        }
    }
}

/// Check if a single constraint is contradicted by the current assignments.
fn is_contradiction(
    dag: &SmtProofDag,
    constraint: &BvConstraint,
    assignments: &std::collections::HashMap<SmtTermId, BitVec>,
) -> bool {
    match constraint {
        BvConstraint::Eq(lhs_id, rhs_id) => {
            if let (Some(lhs_bv), Some(rhs_bv)) = (
                eval_bv_term(dag, *lhs_id, assignments),
                eval_bv_term(dag, *rhs_id, assignments),
            ) {
                lhs_bv != rhs_bv
            } else {
                false
            }
        }
        BvConstraint::Neq(lhs_id, rhs_id) => {
            if let (Some(lhs_bv), Some(rhs_bv)) = (
                eval_bv_term(dag, *lhs_id, assignments),
                eval_bv_term(dag, *rhs_id, assignments),
            ) {
                lhs_bv == rhs_bv
            } else {
                false
            }
        }
        BvConstraint::Pred {
            op,
            lhs,
            rhs,
            negated,
        } => {
            if let (Some(lhs_bv), Some(rhs_bv)) = (
                eval_bv_term(dag, *lhs, assignments),
                eval_bv_term(dag, *rhs, assignments),
            ) {
                let result = match op {
                    BvPredOp::Ult => lhs_bv.bvult(rhs_bv),
                    BvPredOp::Ule => lhs_bv.bvule(rhs_bv),
                    BvPredOp::Slt => lhs_bv.bvslt(rhs_bv),
                    BvPredOp::Sle => lhs_bv.bvsle(rhs_bv),
                };
                // In conflict: if negated=false, the predicate must hold (true).
                // If negated=true, the predicate must NOT hold (false).
                // Contradiction when the required condition is violated.
                if *negated {
                    result
                } else {
                    !result
                }
            } else {
                false
            }
        }
    }
}

/// Parse a blocking-clause literal into a BV constraint.
///
/// A blocking clause literal is negated to get the conflict constraint:
/// - Positive `(= a b)` in blocking clause => conflict is `not(= a b)`, i.e., `a != b`
/// - Negative `(not (= a b))` in blocking clause => conflict is `(= a b)`, i.e., `a = b`
/// - Positive `(bvult a b)` => conflict is `not(bvult a b)`
/// - Negative `(not (bvult a b))` => conflict is `(bvult a b)`
fn parse_bv_literal(dag: &SmtProofDag, lit: SmtTermId) -> Option<BvConstraint> {
    let term = dag.term(lit)?;

    match term {
        // Positive literal in blocking clause => negate for conflict.
        SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
            match op.as_str() {
                "=" => {
                    // Blocking: (= a b). Conflict: a != b.
                    Some(BvConstraint::Neq(args[0], args[1]))
                }
                "distinct" => {
                    // Blocking: (distinct a b). Conflict: a = b.
                    Some(BvConstraint::Eq(args[0], args[1]))
                }
                "bvult" => Some(BvConstraint::Pred {
                    op: BvPredOp::Ult,
                    lhs: args[0],
                    rhs: args[1],
                    negated: true,
                }),
                "bvule" => Some(BvConstraint::Pred {
                    op: BvPredOp::Ule,
                    lhs: args[0],
                    rhs: args[1],
                    negated: true,
                }),
                "bvslt" => Some(BvConstraint::Pred {
                    op: BvPredOp::Slt,
                    lhs: args[0],
                    rhs: args[1],
                    negated: true,
                }),
                "bvsle" => Some(BvConstraint::Pred {
                    op: BvPredOp::Sle,
                    lhs: args[0],
                    rhs: args[1],
                    negated: true,
                }),
                _ => None,
            }
        }
        // Negated literal in blocking clause => conflict is the atom.
        SmtTerm::Not(inner) => {
            let inner_term = dag.term(*inner)?;
            match inner_term {
                SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
                    match op.as_str() {
                        "=" => {
                            // Blocking: not(= a b). Conflict: a = b.
                            Some(BvConstraint::Eq(args[0], args[1]))
                        }
                        "distinct" => {
                            // Blocking: not(distinct a b). Conflict: a != b.
                            Some(BvConstraint::Neq(args[0], args[1]))
                        }
                        "bvult" => Some(BvConstraint::Pred {
                            op: BvPredOp::Ult,
                            lhs: args[0],
                            rhs: args[1],
                            negated: false,
                        }),
                        "bvule" => Some(BvConstraint::Pred {
                            op: BvPredOp::Ule,
                            lhs: args[0],
                            rhs: args[1],
                            negated: false,
                        }),
                        "bvslt" => Some(BvConstraint::Pred {
                            op: BvPredOp::Slt,
                            lhs: args[0],
                            rhs: args[1],
                            negated: false,
                        }),
                        "bvsle" => Some(BvConstraint::Pred {
                            op: BvPredOp::Sle,
                            lhs: args[0],
                            rhs: args[1],
                            negated: false,
                        }),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Evaluate a BV term to a concrete `BitVec` value, if possible.
///
/// Recursively evaluates BV operations when all operands are concrete
/// constants or previously-assigned variables.
fn eval_bv_term(
    dag: &SmtProofDag,
    term_id: SmtTermId,
    assignments: &std::collections::HashMap<SmtTermId, BitVec>,
) -> Option<BitVec> {
    // Check assignment map first.
    if let Some(bv) = assignments.get(&term_id) {
        return Some(*bv);
    }

    let term = dag.term(term_id)?;
    match term {
        // Width comes from untrusted proof text; reject unsupported widths
        // (0 or > 64) rather than building an invalid BitVec that would abort
        // in `as_signed`'s `1 << (width - 1)` shift.
        SmtTerm::BitVec(value, width) => BitVec::try_new(*value, *width),

        SmtTerm::Var(..) => {
            // Variable without assignment: cannot evaluate.
            None
        }

        SmtTerm::App(sym, args) => eval_bv_app(dag, sym, args, assignments),

        _ => None,
    }
}

/// Evaluate a BV function application.
fn eval_bv_app(
    dag: &SmtProofDag,
    sym: &SmtSymbol,
    args: &[SmtTermId],
    assignments: &std::collections::HashMap<SmtTermId, BitVec>,
) -> Option<BitVec> {
    match sym {
        SmtSymbol::Named(name) => eval_bv_named_op(dag, name.as_str(), args, assignments),
        SmtSymbol::Indexed(name, indices) => {
            eval_bv_indexed_op(dag, name.as_str(), indices, args, assignments)
        }
    }
}

/// Evaluate a named BV operation (non-indexed).
fn eval_bv_named_op(
    dag: &SmtProofDag,
    op: &str,
    args: &[SmtTermId],
    assignments: &std::collections::HashMap<SmtTermId, BitVec>,
) -> Option<BitVec> {
    match op {
        "bvand" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvand(b))
        }
        "bvor" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvor(b))
        }
        "bvxor" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvxor(b))
        }
        "bvnot" if args.len() == 1 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            Some(a.bvnot())
        }
        "bvadd" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvadd(b))
        }
        "bvsub" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvsub(b))
        }
        "bvmul" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvmul(b))
        }
        "bvneg" if args.len() == 1 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            Some(a.bvneg())
        }
        "bvshl" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvshl(b))
        }
        "bvlshr" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvlshr(b))
        }
        "bvashr" if args.len() == 2 => {
            let a = eval_bv_term(dag, args[0], assignments)?;
            let b = eval_bv_term(dag, args[1], assignments)?;
            Some(a.bvashr(b))
        }
        "concat" if args.len() == 2 => {
            let hi = eval_bv_term(dag, args[0], assignments)?;
            let lo = eval_bv_term(dag, args[1], assignments)?;
            if hi.width + lo.width > 64 {
                return None; // Too wide for u64.
            }
            Some(hi.concat(lo))
        }
        _ => None,
    }
}

/// Evaluate an indexed BV operation (e.g., `extract`, `zero_extend`, `sign_extend`).
fn eval_bv_indexed_op(
    dag: &SmtProofDag,
    op: &str,
    indices: &[u32],
    args: &[SmtTermId],
    assignments: &std::collections::HashMap<SmtTermId, BitVec>,
) -> Option<BitVec> {
    match op {
        "extract" if indices.len() == 2 && args.len() == 1 => {
            let bv = eval_bv_term(dag, args[0], assignments)?;
            let high = indices[0];
            let low = indices[1];
            if high >= bv.width || high < low {
                return None;
            }
            Some(bv.extract(high, low))
        }
        "zero_extend" if indices.len() == 1 && args.len() == 1 => {
            let bv = eval_bv_term(dag, args[0], assignments)?;
            let extra = indices[0];
            // `extra` is an untrusted index from proof text (up to u32::MAX);
            // use checked_add so `width + extra` cannot overflow before the
            // `> 64` width-support check rejects it.
            match bv.width.checked_add(extra) {
                Some(w) if w <= 64 => Some(bv.zero_extend(extra)),
                _ => None, // Result too wide for this u64-backed evaluator.
            }
        }
        "sign_extend" if indices.len() == 1 && args.len() == 1 => {
            let bv = eval_bv_term(dag, args[0], assignments)?;
            let extra = indices[0];
            // `extra` is an untrusted index from proof text (up to u32::MAX);
            // use checked_add so `width + extra` cannot overflow before the
            // `> 64` width-support check rejects it.
            match bv.width.checked_add(extra) {
                Some(w) if w <= 64 => Some(bv.sign_extend(extra)),
                _ => None, // Result too wide for this u64-backed evaluator.
            }
        }
        _ => None,
    }
}

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

fn structural_accept(step_id: SmtStepId, detail: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker: CHECKER_NAME,
        detail: Some(detail.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtSymbol, SmtTerm};
    use crate::smt_verify::trust::StepTrustLevel;

    // ── BitVec unit tests ──

    #[test]
    fn test_bitvec_new_masks_value() {
        let bv = BitVec::new(0xFF, 4);
        assert_eq!(bv.value, 0x0F); // Only lower 4 bits.
        assert_eq!(bv.width, 4);
    }

    #[test]
    fn test_bitvec_new_64bit() {
        let bv = BitVec::new(u64::MAX, 64);
        assert_eq!(bv.value, u64::MAX);
    }

    #[test]
    fn test_bitvec_bvand() {
        let a = BitVec::new(0b1100, 4);
        let b = BitVec::new(0b1010, 4);
        assert_eq!(a.bvand(b).value, 0b1000);
    }

    #[test]
    fn test_bitvec_bvor() {
        let a = BitVec::new(0b1100, 4);
        let b = BitVec::new(0b1010, 4);
        assert_eq!(a.bvor(b).value, 0b1110);
    }

    #[test]
    fn test_bitvec_bvxor() {
        let a = BitVec::new(0b1100, 4);
        let b = BitVec::new(0b1010, 4);
        assert_eq!(a.bvxor(b).value, 0b0110);
    }

    #[test]
    fn test_bitvec_bvnot() {
        let a = BitVec::new(0b1100, 4);
        assert_eq!(a.bvnot().value, 0b0011);
    }

    #[test]
    fn test_bitvec_bvadd_wrapping() {
        // 8-bit: 255 + 1 = 0 (wraps).
        let a = BitVec::new(255, 8);
        let b = BitVec::new(1, 8);
        assert_eq!(a.bvadd(b).value, 0);
    }

    #[test]
    fn test_bitvec_bvsub() {
        let a = BitVec::new(5, 8);
        let b = BitVec::new(3, 8);
        assert_eq!(a.bvsub(b).value, 2);
    }

    #[test]
    fn test_bitvec_bvsub_underflow() {
        // 8-bit: 0 - 1 = 255.
        let a = BitVec::new(0, 8);
        let b = BitVec::new(1, 8);
        assert_eq!(a.bvsub(b).value, 255);
    }

    #[test]
    fn test_bitvec_bvmul() {
        let a = BitVec::new(7, 8);
        let b = BitVec::new(3, 8);
        assert_eq!(a.bvmul(b).value, 21);
    }

    #[test]
    fn test_bitvec_bvneg() {
        let a = BitVec::new(5, 8);
        // -5 mod 256 = 251.
        assert_eq!(a.bvneg().value, 251);
    }

    #[test]
    fn test_bitvec_bvneg_zero() {
        let a = BitVec::new(0, 8);
        assert_eq!(a.bvneg().value, 0);
    }

    #[test]
    fn test_bitvec_unsigned_comparisons() {
        let a = BitVec::new(3, 8);
        let b = BitVec::new(5, 8);
        assert!(a.bvult(b));
        assert!(a.bvule(b));
        assert!(!b.bvult(a));
        assert!(!b.bvule(a));
        assert!(a.bvule(BitVec::new(3, 8)));
        assert!(!a.bvult(BitVec::new(3, 8)));
    }

    #[test]
    fn test_bitvec_signed_comparisons() {
        // 8-bit: 0xFF = -1 (signed), 0x01 = 1.
        let neg1 = BitVec::new(0xFF, 8);
        let pos1 = BitVec::new(0x01, 8);
        assert!(neg1.bvslt(pos1)); // -1 < 1
        assert!(neg1.bvsle(pos1));
        assert!(!pos1.bvslt(neg1));
    }

    #[test]
    fn test_bitvec_as_signed() {
        assert_eq!(BitVec::new(0xFF, 8).as_signed(), -1);
        assert_eq!(BitVec::new(0x80, 8).as_signed(), -128);
        assert_eq!(BitVec::new(0x7F, 8).as_signed(), 127);
        assert_eq!(BitVec::new(5, 8).as_signed(), 5);
    }

    #[test]
    fn test_bitvec_shifts() {
        let a = BitVec::new(0b0011, 4);
        assert_eq!(a.bvshl(BitVec::new(1, 4)).value, 0b0110);
        assert_eq!(a.bvshl(BitVec::new(4, 4)).value, 0); // Shift >= width.
        assert_eq!(
            BitVec::new(0b1100, 4).bvlshr(BitVec::new(2, 4)).value,
            0b0011
        );
    }

    #[test]
    fn test_bitvec_ashr() {
        // 8-bit: 0x80 = -128 (signed). ashr by 1 => -64 = 0xC0.
        let a = BitVec::new(0x80, 8);
        assert_eq!(a.bvashr(BitVec::new(1, 8)).value, 0xC0);
        // Positive: 0x40 ashr 1 => 0x20.
        let b = BitVec::new(0x40, 8);
        assert_eq!(b.bvashr(BitVec::new(1, 8)).value, 0x20);
    }

    #[test]
    fn test_bitvec_extract() {
        let bv = BitVec::new(0x1234, 16);
        // extract[7:0] => lower byte = 0x34.
        assert_eq!(bv.extract(7, 0).value, 0x34);
        assert_eq!(bv.extract(7, 0).width, 8);
        // extract[15:8] => upper byte = 0x12.
        assert_eq!(bv.extract(15, 8).value, 0x12);
        assert_eq!(bv.extract(15, 8).width, 8);
        // extract[11:4] => 0x23.
        assert_eq!(bv.extract(11, 4).value, 0x23);
        assert_eq!(bv.extract(11, 4).width, 8);
    }

    #[test]
    fn test_bitvec_concat() {
        let hi = BitVec::new(0x12, 8);
        let lo = BitVec::new(0x34, 8);
        let result = hi.concat(lo);
        assert_eq!(result.value, 0x1234);
        assert_eq!(result.width, 16);
    }

    #[test]
    fn test_bitvec_zero_extend() {
        let bv = BitVec::new(0xFF, 8);
        let ext = bv.zero_extend(8);
        assert_eq!(ext.value, 0xFF);
        assert_eq!(ext.width, 16);
    }

    #[test]
    fn test_bitvec_sign_extend() {
        // Negative: 0xFF (8-bit -1) sign-extended to 16 bits => 0xFFFF.
        let bv = BitVec::new(0xFF, 8);
        let ext = bv.sign_extend(8);
        assert_eq!(ext.value, 0xFFFF);
        assert_eq!(ext.width, 16);

        // Positive: 0x7F (127) sign-extended to 16 bits => 0x007F.
        let bv2 = BitVec::new(0x7F, 8);
        let ext2 = bv2.sign_extend(8);
        assert_eq!(ext2.value, 0x007F);
        assert_eq!(ext2.width, 16);
    }

    #[test]
    fn test_eval_bv_indexed_op_huge_extend_index_no_overflow() {
        // Regression: an untrusted Alethe proof can produce an indexed
        // `(_ zero_extend N)` / `(_ sign_extend N)` with N up to u32::MAX
        // (expect_u32 accepts the full u32 range). The old guard computed
        // `bv.width + extra` as a raw u32 add, which overflows (8 + u32::MAX)
        // before the `> 64` check and aborts under overflow-checks/panic=abort.
        // With checked_add the oversized extension is cleanly rejected (None).
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::BitVec(8)));
        let ext_ze = dag.add_term(SmtTerm::App(
            SmtSymbol::Indexed("zero_extend".to_string(), vec![u32::MAX]),
            vec![x],
        ));
        let ext_se = dag.add_term(SmtTerm::App(
            SmtSymbol::Indexed("sign_extend".to_string(), vec![u32::MAX]),
            vec![x],
        ));

        let mut assignments = std::collections::HashMap::new();
        assignments.insert(x, BitVec::new(0xFF, 8));

        // Must return None (unsupported width), not panic.
        assert_eq!(eval_bv_term(&dag, ext_ze, &assignments), None);
        assert_eq!(eval_bv_term(&dag, ext_se, &assignments), None);

        // A supported extension still evaluates exactly as before.
        let ext_ok = dag.add_term(SmtTerm::App(
            SmtSymbol::Indexed("zero_extend".to_string(), vec![8]),
            vec![x],
        ));
        let result = eval_bv_term(&dag, ext_ok, &assignments).expect("8+8=16 <= 64 evaluates");
        assert_eq!(result.width, 16);
        assert_eq!(result.value, 0xFF);
    }

    // ── Theory lemma integration tests ──

    /// Helper: build a BV constant term in the DAG.
    fn add_bv_const(dag: &mut SmtProofDag, value: u64, width: u32) -> SmtTermId {
        dag.add_term(SmtTerm::BitVec(value, width))
    }

    /// Helper: build a BV variable term.
    fn add_bv_var(dag: &mut SmtProofDag, name: &str, width: u32) -> SmtTermId {
        dag.add_term(SmtTerm::Var(name.to_string(), SmtSort::BitVec(width)))
    }

    /// Helper: build a binary BV operation.
    fn add_bv_binop(dag: &mut SmtProofDag, op: &str, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named(op.to_string()),
            vec![lhs, rhs],
        ))
    }

    /// Helper: build an equality `(= lhs rhs)`.
    fn add_eq(dag: &mut SmtProofDag, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named("=".to_string()),
            vec![lhs, rhs],
        ))
    }

    /// Helper: build `(not t)`.
    fn add_not(dag: &mut SmtProofDag, t: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::Not(t))
    }

    #[test]
    fn test_bv_lemma_contradiction_different_values() {
        // x[8] = 5 AND x[8] = 3 => contradiction.
        //
        // Blocking clause: (= x 5) OR (= x 3) (at least one must be false).
        // Wait -- the blocking clause is the negation of the conflict.
        // Conflict: x = 5 AND x = 3.
        // Blocking clause: not(x = 5) OR not(x = 3).
        //
        // Clause literals: [not(= x #b00000101), not(= x #b00000011)]
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let five = add_bv_const(&mut dag, 5, 8);
        let three = add_bv_const(&mut dag, 3, 8);

        let eq_x_5 = add_eq(&mut dag, x, five);
        let eq_x_3 = add_eq(&mut dag, x, three);
        let not_eq_x_5 = add_not(&mut dag, eq_x_5);
        let not_eq_x_3 = add_not(&mut dag, eq_x_3);

        let clause = vec![not_eq_x_5, not_eq_x_3];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect x=5 AND x=3 contradiction; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bv_lemma_bitwise_and_invalid() {
        // Claim: bvand(x, y) = 0xFF, x = 0x0F, y = 0x0F => invalid
        // because bvand(0x0F, 0x0F) = 0x0F, not 0xFF.
        //
        // Conflict: x = 0x0F AND y = 0x0F AND bvand(x,y) = 0xFF
        // Blocking clause: not(= x 0x0F) OR not(= y 0x0F) OR not(= (bvand x y) 0xFF)
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let y = add_bv_var(&mut dag, "y", 8);
        let x0f = add_bv_const(&mut dag, 0x0F, 8);
        let y0f = add_bv_const(&mut dag, 0x0F, 8);
        let xff = add_bv_const(&mut dag, 0xFF, 8);
        let and_xy = add_bv_binop(&mut dag, "bvand", x, y);

        let eq_x = add_eq(&mut dag, x, x0f);
        let eq_y = add_eq(&mut dag, y, y0f);
        let eq_and = add_eq(&mut dag, and_xy, xff);
        let not_eq_x = add_not(&mut dag, eq_x);
        let not_eq_y = add_not(&mut dag, eq_y);
        let not_eq_and = add_not(&mut dag, eq_and);

        let clause = vec![not_eq_x, not_eq_y, not_eq_and];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect bvand contradiction; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bv_lemma_overflow_add() {
        // x[8] + y[8] = 0, x = 1, y = 255 => valid (wraps to 0).
        // Conflict: x = 1 AND y = 255 AND bvadd(x,y) = 0 => this is SATISFIABLE.
        // So the blocking clause not(x=1) OR not(y=255) OR not(bvadd(x,y)=0)
        // is NOT a valid lemma (the conjunction IS satisfiable).
        //
        // Actually, the task says this should be "valid" meaning the conflict
        // is satisfiable, so the lemma (blocking clause) is INVALID as a tautology.
        // Let me re-read...
        //
        // "x[8] + y[8] = 0, x = 1, y = 255 -> valid (wraps to 0)"
        // This means the equation IS satisfied (1 + 255 = 0 mod 256).
        // So there's no contradiction, meaning the blocking clause is NOT a valid lemma.
        //
        // Hmm, but the task says "valid". I think they mean the computation
        // is valid (wraps to 0), confirming that this set of constraints is
        // satisfiable (no contradiction). So check_bv_lemma should NOT return
        // KernelVerified for this.
        //
        // Let me test the opposite: x[8] + y[8] = 1 (should be a contradiction
        // with x=1, y=255 since 1+255=0, not 1).

        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let y = add_bv_var(&mut dag, "y", 8);
        let one = add_bv_const(&mut dag, 1, 8);
        let ff = add_bv_const(&mut dag, 255, 8);
        let target = add_bv_const(&mut dag, 1, 8); // 1, not 0
        let add_xy = add_bv_binop(&mut dag, "bvadd", x, y);

        let eq_x = add_eq(&mut dag, x, one);
        let eq_y = add_eq(&mut dag, y, ff);
        let eq_sum = add_eq(&mut dag, add_xy, target);
        let not_eq_x = add_not(&mut dag, eq_x);
        let not_eq_y = add_not(&mut dag, eq_y);
        let not_eq_sum = add_not(&mut dag, eq_sum);

        let clause = vec![not_eq_x, not_eq_y, not_eq_sum];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect bvadd contradiction (1+255=0, not 1); detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bv_lemma_satisfiable_not_contradiction() {
        // x[8] + y[8] = 0, x = 1, y = 255 => satisfiable (wraps).
        // The blocking clause for this conflict should NOT be KernelVerified
        // because the conflict is satisfiable.
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let y = add_bv_var(&mut dag, "y", 8);
        let one = add_bv_const(&mut dag, 1, 8);
        let ff = add_bv_const(&mut dag, 255, 8);
        let zero = add_bv_const(&mut dag, 0, 8);
        let add_xy = add_bv_binop(&mut dag, "bvadd", x, y);

        let eq_x = add_eq(&mut dag, x, one);
        let eq_y = add_eq(&mut dag, y, ff);
        let eq_sum = add_eq(&mut dag, add_xy, zero);
        let not_eq_x = add_not(&mut dag, eq_x);
        let not_eq_y = add_not(&mut dag, eq_y);
        let not_eq_sum = add_not(&mut dag, eq_sum);

        let clause = vec![not_eq_x, not_eq_y, not_eq_sum];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        // Should NOT be KernelVerified because the conflict IS satisfiable.
        assert_ne!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "satisfiable conflict should not be verified; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bv_lemma_extract_contradiction() {
        // x[16] = 0x1234, extract[7:0](x) != 0x34 => contradiction.
        // Because extract[7:0](0x1234) = 0x34, so the disequality fails.
        //
        // Conflict: x = 0x1234 AND extract[7:0](x) != 0x34.
        // Blocking clause: not(= x 0x1234) OR (= extract[7:0](x) 0x34)
        //
        // In terms of our parser:
        // lit0: not(= x 0x1234) => conflict: x = 0x1234
        // lit1: (= (extract 7 0 x) 0x34) => conflict: (extract 7 0 x) != 0x34
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 16);
        let val_1234 = add_bv_const(&mut dag, 0x1234, 16);
        let val_34 = add_bv_const(&mut dag, 0x34, 8);

        // extract[7:0](x)
        let extract_x = dag.add_term(SmtTerm::App(
            SmtSymbol::Indexed("extract".to_string(), vec![7, 0]),
            vec![x],
        ));

        let eq_x = add_eq(&mut dag, x, val_1234);
        let eq_ext = add_eq(&mut dag, extract_x, val_34);
        let not_eq_x = add_not(&mut dag, eq_x);

        // Blocking clause: not(= x 0x1234) OR (= extract[7:0](x) 0x34)
        // lit0 => conflict: x = 0x1234
        // lit1 => conflict: extract[7:0](x) != 0x34
        let clause = vec![not_eq_x, eq_ext];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect extract contradiction; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bv_lemma_empty_clause() {
        let dag = SmtProofDag::new();
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_bv_lemma_non_bv_literals() {
        // Integer/Boolean literals that can't be parsed as BV.
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &[t]);
        assert_eq!(verdict.trust_level, StepTrustLevel::StructurallyAccepted);
    }

    #[test]
    fn test_bv_lemma_shift_contradiction() {
        // x[8] = 0x03, bvshl(x, 2) != 0x0C => contradiction.
        // Because bvshl(0x03, 2) = 0x0C.
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let three = add_bv_const(&mut dag, 0x03, 8);
        let two = add_bv_const(&mut dag, 2, 8);
        let twelve = add_bv_const(&mut dag, 0x0C, 8);
        let shl_x = add_bv_binop(&mut dag, "bvshl", x, two);

        let eq_x = add_eq(&mut dag, x, three);
        let eq_shl = add_eq(&mut dag, shl_x, twelve);
        let not_eq_x = add_not(&mut dag, eq_x);

        // Blocking clause: not(= x 3) OR (= shl(x,2) 0x0C)
        // Conflict: x = 3 AND shl(x,2) != 0x0C
        // But shl(3,2) = 0x0C, so the disequality contradicts.
        let clause = vec![not_eq_x, eq_shl];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect shift contradiction; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bv_lemma_comparison_contradiction() {
        // x[8] = 5, bvult(x, 3) => contradiction (5 is not < 3 unsigned).
        //
        // Conflict: x = 5 AND bvult(x, 3).
        // Blocking clause: not(= x 5) OR not(bvult x 3)
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let five = add_bv_const(&mut dag, 5, 8);
        let three = add_bv_const(&mut dag, 3, 8);

        let eq_x = add_eq(&mut dag, x, five);
        let ult = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("bvult".to_string()),
            vec![x, three],
        ));
        let not_eq_x = add_not(&mut dag, eq_x);
        let not_ult = add_not(&mut dag, ult);

        let clause = vec![not_eq_x, not_ult];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect bvult contradiction; detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_bitvec_try_new_rejects_out_of_range_widths() {
        // Widths outside 1..=64 are not modeled by this u64-backed evaluator.
        assert!(BitVec::try_new(0, 0).is_none(), "width 0 must be rejected");
        assert!(
            BitVec::try_new(0, 65).is_none(),
            "width 65 must be rejected"
        );
        assert!(
            BitVec::try_new(0, 100).is_none(),
            "width 100 must be rejected"
        );
        assert_eq!(BitVec::try_new(5, 8), Some(BitVec::new(5, 8)));
        assert_eq!(
            BitVec::try_new(u64::MAX, 64),
            Some(BitVec::new(u64::MAX, 64))
        );
        assert_eq!(BitVec::try_new(1, 1), Some(BitVec::new(1, 1)));
    }

    #[test]
    fn test_bv_lemma_wide_width_slt_no_overflow() {
        // Regression: a (bvslt (_ bv0 100) (_ bv0 100)) lemma feeds width-100
        // BitVec constants into as_signed's `1u64 << (width - 1)` shift.
        // Before the fix this aborted (debug: shift/debug_assert; release with
        // overflow-checks + panic=abort: hard process abort) on untrusted proof
        // text. After the fix the width-100 constants are unmodeled, so the
        // lemma is structurally accepted instead of evaluated.
        let proof_text = "(step t1 (cl (bvslt (_ bv0 100) (_ bv0 100))) :rule bv_bitblast)\n";
        // The bug was a hard abort (shift overflow / failed debug_assert) while
        // evaluating the width-100 constants. After the fix, verification must
        // simply *return* — whether Ok (structurally accepted, no contradiction)
        // or a benign Err (this single-step proof's final clause is non-empty).
        // Either way, the process must not abort.
        let result = crate::smt_verify::verify_alethe_proof(proof_text);
        if let Ok(res) = result {
            // If it does verify the step, it must not be kernel-verified from
            // unmodeled-width constants.
            assert_eq!(
                res.stats.kernel_verified, 0,
                "unmodeled-width lemma must not be kernel-verified; verdicts: {:?}",
                res.verdicts
            );
        }
    }

    #[test]
    fn test_bv_lemma_zero_width_slt_no_overflow() {
        // Companion regression: width-0 literal makes `self.width - 1` underflow
        // (u32 0 - 1) in as_signed. Must not abort.
        let proof_text = "(step t1 (cl (bvslt (_ bv0 0) (_ bv0 0))) :rule bv_bitblast)\n";
        // Must return (Ok or benign Err) rather than abort on the `width - 1`
        // (0u32 - 1) underflow inside as_signed.
        let _ = crate::smt_verify::verify_alethe_proof(proof_text);
    }

    #[test]
    fn test_bv_lemma_signed_comparison() {
        // x[8] = 0xFF (-1 signed), bvslt(0x01, x) => contradiction.
        // Because 1 is NOT < -1 in signed comparison (1 > -1).
        //
        // Conflict: x = 0xFF AND bvslt(1, x) (i.e., 1 <_s x = 1 <_s -1 = false).
        // Blocking clause: not(= x 0xFF) OR not(bvslt 1 x)
        let mut dag = SmtProofDag::new();
        let x = add_bv_var(&mut dag, "x", 8);
        let xff = add_bv_const(&mut dag, 0xFF, 8);
        let one = add_bv_const(&mut dag, 1, 8);

        let eq_x = add_eq(&mut dag, x, xff);
        let slt = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("bvslt".to_string()),
            vec![one, x],
        ));
        let not_eq_x = add_not(&mut dag, eq_x);
        let not_slt = add_not(&mut dag, slt);

        let clause = vec![not_eq_x, not_slt];
        let verdict = check_bv_lemma(&dag, SmtStepId(0), &clause);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "should detect signed comparison contradiction; detail: {:?}",
            verdict.detail
        );
    }
}
