// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The bit-vector GOAL a sited panic-class obligation states, derived from the
//! IR by validator-owned code.
//!
//! # Why this module exists, and why it is here rather than in the adapter
//!
//! A bit-blasted refutation payload (ay's `BvBlastProof`) certifies that its
//! internally authenticated Boolean graph and exact disequality are
//! unsatisfiable. It does **not** say which live program fact produced that
//! graph: `asserted_smt` is descriptive text, expression-tree `obligation`
//! metadata is lineage rather than source authentication, and `validate()`
//! intentionally checks the graph rather than a caller's source. A consumer
//! that granted proof authority on `validate() == Ok` alone could therefore
//! accept a valid refutation of an unrelated formula as discharge for an
//! obligation in the module.
//!
//! The binding therefore cannot come from the payload. It must be
//! **re-derived**: given the module and the obligation, reconstruct the exact
//! goal the obligation states, hash it, and require the stored artifact to be a
//! refutation of *that* goal's negation and no other. [`derive_site_goal`] is
//! that reconstruction, and it lives in `trust-ir` (zero-dep) for one reason:
//! the producer and the validator must not be able to disagree about what an
//! obligation says. There is exactly one implementation, and both sides call
//! it.
//!
//! # What a goal is
//!
//! [`BvGoal`] is `lhs == rhs` over [`BvTerm`], a closed bit-vector fragment.
//! For a sited assert (an `Inst::Assert`, or a lowered `CondBr` assert) the
//! goal is always
//! `<condition, 1 bit> == Const { value: 1, width: 1 }` — "the checked
//! condition is true for every valuation of the block's free parameters".
//!
//! # The fragment, and the one deliberate omission
//!
//! [`BvTerm`] mirrors the pinned ay `BvExpr` fragment **minus `Mul`**. That
//! omission is enforced by the type rather than by a check, because it is not a
//! stylistic preference: bit-blasting a width-8 multiply commutativity goal was
//! measured at 1,617,446 resolution steps and 1.29 GB of JSON, and width 16 did
//! not terminate. The exporter takes no step budget or timeout, and the
//! allocation happens before any timer could fire, so a rejected-by-construction
//! node is the only guard that actually holds. `BinOp::Mul` is a hard reject in
//! [`derive_site_goal`] for the same reason.
//!
//! # Fail-closed
//!
//! Every function here returns an error rather than a guess. An unsupported
//! instruction, an unsupported type, a width mismatch, a value defined outside
//! the block's pure prefix, or an unrecognised branch shape all produce
//! [`GoalDeriveError`]. There is no arm that approximates.

use crate::constant::Constant;
use crate::inst::{BinOp, CastOp, ICmpOp, Inst, OverflowOp, UnOp};
use crate::node::InstrNode;
use crate::ty::Ty;
use crate::value::{BlockId, ValueId};
use crate::{Function, Module};

use super::evidence::ProofDigest;
use super::obligations::{ObligationKind, ProofFormula, ProofObligation};

/// Maximum bit width of any leaf or intermediate term in a derived goal.
///
/// The comparison in a predicate-shaped goal is 1 bit wide, so ay's own
/// `SOLVED_MAX_WIDTH = 64` (which is checked against the *compared* width) never
/// binds and 128-bit operands stay in scope. This cap bounds the *blast* instead:
/// every node of width `w` costs `O(w)` gates, and a barrel shifter costs
/// `O(w log w)`.
pub const BVGOAL_MAX_WIDTH: u32 = 128;

/// Maximum number of nodes in a derived goal term.
///
/// Defence in depth behind the structural `Mul` rejection. The measured corpus
/// slices are 1..=9 nodes deep.
///
/// NOTE: a node COUNT alone is not a cost bound — see [`BVGOAL_MAX_BLAST_COST`].
/// This constant's original rationale ("far below anything that blasts slowly")
/// was measured to be FALSE: 68 nodes of 128-bit `Shl` did not finish blasting
/// in 400 s, well inside this budget.
pub const BVGOAL_MAX_NODES: usize = 256;

/// Maximum estimated blast cost of a derived goal.
///
/// **Why a node count was not enough.** `BVGOAL_MAX_NODES` claimed 256 nodes was
/// "far below anything that blasts slowly". Measured at width 128: 6 nodes
/// blasted in 20 ms, 36 nodes in 237 ms, and **68 nodes did not finish in
/// 400 s** — all far under the node cap. Cost is driven by width and by shift
/// nodes (a barrel shifter is `O(w log w)` gates), not by node count, so a
/// count-only budget bounds the wrong quantity.
///
/// That mattered beyond tidiness: the validator re-solves from scratch, so an
/// unbounded goal is a denial-of-service reachable with no valid proof at all —
/// an attacker needs only an honestly-computable formula digest and any
/// decodable payload.
///
/// The estimate charges `w` per node and `w * ceil(log2 w)` per shift. Against
/// the real corpus the worst case is ~9 nodes at width 128 with every node a
/// shift = 8_064, so this cap leaves 2x headroom while rejecting the 36-node
/// (32_256) and 68-node (60_928) hostile shapes measured above.
pub const BVGOAL_MAX_BLAST_COST: u64 = 16_384;

/// A bit-vector term over the closed fragment this route can prove.
///
/// One-to-one with the pinned ay `BvExpr` **except** that `Mul` is absent (see
/// the module docs). Kept structurally identical so the lowering in the adapter
/// is a total, non-normalizing 1:1 map — a normalizing rewriter between this
/// type and `BvExpr` would put a rewrite engine in the trusted base.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BvTerm {
    /// A named free variable of the given bit width. The SAME name denotes the
    /// SAME variable; [`BvTerm::width`] enforces that one name never carries two
    /// widths, because the pinned ay blaster does **not** — its leaf cache keys
    /// on the name and silently ignores the width argument on every lookup after
    /// the first.
    Leaf {
        name: String,
        width: u32,
    },
    /// A fixed unsigned bit pattern. Bits at or above `width` must be zero.
    Const {
        value: u128,
        width: u32,
    },
    Add(Box<BvTerm>, Box<BvTerm>),
    Sub(Box<BvTerm>, Box<BvTerm>),
    And(Box<BvTerm>, Box<BvTerm>),
    Or(Box<BvTerm>, Box<BvTerm>),
    Xor(Box<BvTerm>, Box<BvTerm>),
    /// Logical shift left by a variable amount (barrel shifter).
    Shl(Box<BvTerm>, Box<BvTerm>),
    /// Logical (zero-filling) shift right by a variable amount.
    Lshr(Box<BvTerm>, Box<BvTerm>),
    /// Arithmetic (sign-filling) shift right by a variable amount.
    Ashr(Box<BvTerm>, Box<BvTerm>),
    /// Per-bit NOT.
    Not(Box<BvTerm>),
    /// Append `added` zero bits above `inner`.
    ZeroExt(Box<BvTerm>, u32),
    /// Append `added` copies of `inner`'s MSB above `inner`.
    SignExt(Box<BvTerm>, u32),
    /// Bits `low..=high` of `inner` (LSB = 0).
    Extract {
        inner: Box<BvTerm>,
        high: u32,
        low: u32,
    },
    /// Bit-vector equality reduced to exactly 1 bit.
    Eq(Box<BvTerm>, Box<BvTerm>),
    /// Final carry-out of a ripple-carry add (`is_sub == false`) or subtract
    /// (`is_sub == true`). Exactly 1 bit. `unsigned_lt(a, b)` is
    /// `Not(CarryOut { lhs: a, rhs: b, is_sub: true })`.
    CarryOut {
        lhs: Box<BvTerm>,
        rhs: Box<BvTerm>,
        is_sub: bool,
    },
}

/// Why a term is not well-formed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvTermError {
    /// Two operands of a same-width node blasted to different widths.
    WidthMismatch { lhs: u32, rhs: u32 },
    /// A width of zero, or one above [`BVGOAL_MAX_WIDTH`].
    UnsupportedWidth { got: u32 },
    /// One leaf name carries two different widths in the same term. ay's blaster
    /// would silently coerce the second to the first; this rejects instead.
    LeafWidthConflict {
        name: String,
        first: u32,
        second: u32,
    },
    /// A constant has set bits at or above its declared width.
    ConstOutOfRange { value: u128, width: u32 },
    /// An extract range is empty or reaches past its operand.
    ExtractOutOfBounds { high: u32, low: u32, width: u32 },
    /// The term exceeds [`BVGOAL_MAX_NODES`].
    TooManyNodes { got: usize, max: usize },
    /// The term's estimated blast cost exceeds [`BVGOAL_MAX_BLAST_COST`].
    ///
    /// Distinct from `TooManyNodes` because the two bound different quantities
    /// and only this one tracks blast time — a small node count of wide shifts
    /// is cheap by the former and ruinous by the latter.
    TooExpensive { got: u64, max: u64 },
}

impl core::fmt::Display for BvTermError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WidthMismatch { lhs, rhs } => {
                write!(f, "width mismatch: lhs is {lhs} bits, rhs is {rhs} bits")
            }
            Self::UnsupportedWidth { got } => write!(
                f,
                "unsupported width {got} (supported: 1..={BVGOAL_MAX_WIDTH})"
            ),
            Self::LeafWidthConflict {
                name,
                first,
                second,
            } => write!(
                f,
                "leaf {name:?} appears at width {first} and width {second}; one name must denote \
                 one variable of one width"
            ),
            Self::ConstOutOfRange { value, width } => {
                write!(f, "constant {value} does not fit in {width} bits")
            }
            Self::ExtractOutOfBounds { high, low, width } => write!(
                f,
                "extract [{high}:{low}] is out of bounds for a {width}-bit operand"
            ),
            Self::TooManyNodes { got, max } => {
                write!(f, "goal has {got} nodes, above the cap of {max}")
            }
            Self::TooExpensive { got, max } => write!(
                f,
                "goal has an estimated blast cost of {got}, above the cap of {max} \
                 (cost is width x gates, with shifts charged w*log2(w) — a node count \
                 does not bound it)"
            ),
        }
    }
}

impl BvTerm {
    /// Convenience constructor for a leaf.
    pub fn leaf(name: impl Into<String>, width: u32) -> Self {
        Self::Leaf {
            name: name.into(),
            width,
        }
    }

    /// The 1-bit constant `1` — the right-hand side of every predicate goal.
    pub const fn one_bit_true() -> Self {
        Self::Const { value: 1, width: 1 }
    }

    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }

    /// Total node count, including this node.
    pub fn node_count(&self) -> usize {
        1 + match self {
            Self::Leaf { .. } | Self::Const { .. } => 0,
            Self::Not(inner) | Self::ZeroExt(inner, _) | Self::SignExt(inner, _) => {
                inner.node_count()
            }
            Self::Extract { inner, .. } => inner.node_count(),
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::And(a, b)
            | Self::Or(a, b)
            | Self::Xor(a, b)
            | Self::Shl(a, b)
            | Self::Lshr(a, b)
            | Self::Ashr(a, b)
            | Self::Eq(a, b) => a.node_count() + b.node_count(),
            Self::CarryOut { lhs, rhs, .. } => lhs.node_count() + rhs.node_count(),
        }
    }

    /// Estimated bit-blast cost: `w` per node, `w * ceil(log2 w)` per shift.
    ///
    /// Bounds the quantity that actually drives blast time (width x gate count,
    /// with the barrel shifter's `O(w log w)` charged explicitly), rather than
    /// the node count, which was measured not to correlate — see
    /// [`BVGOAL_MAX_BLAST_COST`]. Saturating throughout: an overflow must
    /// surface as "too expensive", never wrap to a small number.
    pub fn blast_cost(&self) -> u64 {
        let w = self.declared_width() as u64;
        let here = match self {
            Self::Shl(..) | Self::Lshr(..) | Self::Ashr(..) => {
                // ceil(log2 w) for w >= 1.
                let log = if w <= 1 {
                    1
                } else {
                    64 - (w - 1).leading_zeros() as u64
                };
                w.saturating_mul(log)
            }
            _ => w,
        };
        let children: u64 = match self {
            Self::Leaf { .. } | Self::Const { .. } => 0,
            Self::Not(inner) | Self::ZeroExt(inner, _) | Self::SignExt(inner, _) => {
                inner.blast_cost()
            }
            Self::Extract { inner, .. } => inner.blast_cost(),
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::And(a, b)
            | Self::Or(a, b)
            | Self::Xor(a, b)
            | Self::Shl(a, b)
            | Self::Lshr(a, b)
            | Self::Ashr(a, b)
            | Self::Eq(a, b) => a.blast_cost().saturating_add(b.blast_cost()),
            Self::CarryOut { lhs, rhs, .. } => lhs.blast_cost().saturating_add(rhs.blast_cost()),
        };
        here.saturating_add(children)
    }

    /// Width as DECLARED at this node, without the full consistency check.
    ///
    /// Only for cost estimation, which must work on terms that have not yet
    /// passed [`BvTerm::width`]: a cost bound that required a well-formed term
    /// could not run before the expensive work it exists to bound.
    fn declared_width(&self) -> u32 {
        match self {
            Self::Leaf { width, .. } | Self::Const { width, .. } => *width,
            Self::Eq(..) | Self::CarryOut { .. } => 1,
            Self::Extract { high, low, .. } => high.saturating_sub(*low).saturating_add(1),
            Self::ZeroExt(inner, added) | Self::SignExt(inner, added) => {
                inner.declared_width().saturating_add(*added)
            }
            Self::Not(inner) => inner.declared_width(),
            Self::Add(a, _)
            | Self::Sub(a, _)
            | Self::And(a, _)
            | Self::Or(a, _)
            | Self::Xor(a, _)
            | Self::Shl(a, _)
            | Self::Lshr(a, _)
            | Self::Ashr(a, _) => a.declared_width(),
        }
    }

    /// Number of [`BvTerm::Leaf`] occurrences.
    ///
    /// **The anti-vacuity gate.** A goal with zero leaves is a statement about
    /// literals: structurally provable, and entirely uninformative about any
    /// execution. The corpus measurement found 45 such conditions (monomorphised
    /// `size_of::<T>() != 0` checks and friends) — exactly the population that
    /// produced the earlier round of vacuous certificates. Unlike a
    /// constant-folding check on a rendered solver term, this is purely
    /// syntactic on the term the validator itself derived, so it cannot be
    /// evaded by a constructor that folds before the check runs.
    pub fn leaf_count(&self) -> usize {
        match self {
            Self::Leaf { .. } => 1,
            Self::Const { .. } => 0,
            Self::Not(inner) | Self::ZeroExt(inner, _) | Self::SignExt(inner, _) => {
                inner.leaf_count()
            }
            Self::Extract { inner, .. } => inner.leaf_count(),
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::And(a, b)
            | Self::Or(a, b)
            | Self::Xor(a, b)
            | Self::Shl(a, b)
            | Self::Lshr(a, b)
            | Self::Ashr(a, b)
            | Self::Eq(a, b) => a.leaf_count() + b.leaf_count(),
            Self::CarryOut { lhs, rhs, .. } => lhs.leaf_count() + rhs.leaf_count(),
        }
    }

    /// Bit width of this term, checking every structural constraint on the way.
    pub fn width(&self) -> Result<u32, BvTermError> {
        let mut leaves = Vec::new();
        self.width_checked(&mut leaves)
    }

    fn width_checked(&self, leaves: &mut Vec<(String, u32)>) -> Result<u32, BvTermError> {
        let ok = |w: u32| -> Result<u32, BvTermError> {
            if w == 0 || w > BVGOAL_MAX_WIDTH {
                Err(BvTermError::UnsupportedWidth { got: w })
            } else {
                Ok(w)
            }
        };
        match self {
            Self::Leaf { name, width } => {
                let width = ok(*width)?;
                if let Some((_, seen)) = leaves.iter().find(|(n, _)| n == name) {
                    if *seen != width {
                        return Err(BvTermError::LeafWidthConflict {
                            name: name.clone(),
                            first: *seen,
                            second: width,
                        });
                    }
                } else {
                    leaves.push((name.clone(), width));
                }
                Ok(width)
            }
            Self::Const { value, width } => {
                let width = ok(*width)?;
                if width < 128 && (*value >> width) != 0 {
                    return Err(BvTermError::ConstOutOfRange {
                        value: *value,
                        width,
                    });
                }
                Ok(width)
            }
            Self::Not(inner) => inner.width_checked(leaves),
            Self::ZeroExt(inner, added) | Self::SignExt(inner, added) => {
                let base = inner.width_checked(leaves)?;
                ok(base.saturating_add(*added))
            }
            Self::Extract { inner, high, low } => {
                let base = inner.width_checked(leaves)?;
                if *low > *high || *high >= base {
                    return Err(BvTermError::ExtractOutOfBounds {
                        high: *high,
                        low: *low,
                        width: base,
                    });
                }
                ok(high - low + 1)
            }
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::And(a, b)
            | Self::Or(a, b)
            | Self::Xor(a, b)
            | Self::Shl(a, b)
            | Self::Lshr(a, b)
            | Self::Ashr(a, b) => {
                let lhs = a.width_checked(leaves)?;
                let rhs = b.width_checked(leaves)?;
                if lhs != rhs {
                    return Err(BvTermError::WidthMismatch { lhs, rhs });
                }
                ok(lhs)
            }
            Self::Eq(a, b) => {
                let lhs = a.width_checked(leaves)?;
                let rhs = b.width_checked(leaves)?;
                if lhs != rhs {
                    return Err(BvTermError::WidthMismatch { lhs, rhs });
                }
                Ok(1)
            }
            Self::CarryOut { lhs, rhs, .. } => {
                let l = lhs.width_checked(leaves)?;
                let r = rhs.width_checked(leaves)?;
                if l != r {
                    return Err(BvTermError::WidthMismatch { lhs: l, rhs: r });
                }
                Ok(1)
            }
        }
    }
}

/// A validity claim: `lhs == rhs` holds for every valuation of the free leaves.
///
/// For a sited lowered assert, `rhs` is always [`BvTerm::one_bit_true`] and
/// `lhs` is the 1-bit checked condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BvGoal {
    pub lhs: BvTerm,
    pub rhs: BvTerm,
}

impl BvGoal {
    /// A predicate goal: `condition == #b1`.
    pub fn predicate(condition: BvTerm) -> Self {
        Self {
            lhs: condition,
            rhs: BvTerm::one_bit_true(),
        }
    }

    /// Structural well-formedness: both sides check, agree in width, the node
    /// budget holds, and at least one free leaf occurs (anti-vacuity).
    pub fn validate_shape(&self) -> Result<(), BvTermError> {
        let nodes = self.lhs.node_count() + self.rhs.node_count();
        if nodes > BVGOAL_MAX_NODES {
            return Err(BvTermError::TooManyNodes {
                got: nodes,
                max: BVGOAL_MAX_NODES,
            });
        }
        // The cost bound, which is the one that actually holds. Checked here so
        // EVERY path that admits a goal — producer and validator alike — is
        // bounded, including the validator's from-scratch re-solve.
        let cost = self.lhs.blast_cost().saturating_add(self.rhs.blast_cost());
        if cost > BVGOAL_MAX_BLAST_COST {
            return Err(BvTermError::TooExpensive {
                got: cost,
                max: BVGOAL_MAX_BLAST_COST,
            });
        }
        // One shared leaf environment across both sides: a name occurring on
        // both sides must denote one variable at one width, exactly as the
        // blaster's shared leaf cache will treat it.
        let mut leaves = Vec::new();
        let lhs = self.lhs.width_checked(&mut leaves)?;
        let rhs = self.rhs.width_checked(&mut leaves)?;
        if lhs != rhs {
            return Err(BvTermError::WidthMismatch { lhs, rhs });
        }
        Ok(())
    }

    /// Total free-leaf occurrences across both sides.
    pub fn leaf_count(&self) -> usize {
        self.lhs.leaf_count() + self.rhs.leaf_count()
    }

    /// True iff the goal mentions no free variable — a fact about literals only.
    /// See [`BvTerm::leaf_count`] for why this is refused as evidence.
    pub fn is_ground(&self) -> bool {
        self.leaf_count() == 0
    }
}

// ───────────────────────── canonical bytes and digest ─────────────────────────

const TAG_LEAF: u8 = 0x01;
const TAG_CONST: u8 = 0x02;
const TAG_ADD: u8 = 0x03;
const TAG_SUB: u8 = 0x04;
const TAG_AND: u8 = 0x05;
const TAG_OR: u8 = 0x06;
const TAG_XOR: u8 = 0x07;
const TAG_SHL: u8 = 0x08;
const TAG_LSHR: u8 = 0x09;
const TAG_ASHR: u8 = 0x0a;
const TAG_NOT: u8 = 0x0b;
const TAG_ZEXT: u8 = 0x0c;
const TAG_SEXT: u8 = 0x0d;
const TAG_EXTRACT: u8 = 0x0e;
const TAG_EQ: u8 = 0x0f;
const TAG_CARRY_OUT: u8 = 0x10;

fn write_term(term: &BvTerm, out: &mut Vec<u8>) {
    match term {
        BvTerm::Leaf { name, width } => {
            out.push(TAG_LEAF);
            out.extend_from_slice(&width.to_le_bytes());
            let len = u64::try_from(name.len()).expect("leaf name length exceeds u64 framing");
            out.extend_from_slice(&len.to_le_bytes());
            out.extend_from_slice(name.as_bytes());
        }
        BvTerm::Const { value, width } => {
            out.push(TAG_CONST);
            out.extend_from_slice(&width.to_le_bytes());
            out.extend_from_slice(&value.to_le_bytes());
        }
        BvTerm::Not(inner) => {
            out.push(TAG_NOT);
            write_term(inner, out);
        }
        BvTerm::ZeroExt(inner, added) => {
            out.push(TAG_ZEXT);
            out.extend_from_slice(&added.to_le_bytes());
            write_term(inner, out);
        }
        BvTerm::SignExt(inner, added) => {
            out.push(TAG_SEXT);
            out.extend_from_slice(&added.to_le_bytes());
            write_term(inner, out);
        }
        BvTerm::Extract { inner, high, low } => {
            out.push(TAG_EXTRACT);
            out.extend_from_slice(&high.to_le_bytes());
            out.extend_from_slice(&low.to_le_bytes());
            write_term(inner, out);
        }
        BvTerm::CarryOut { lhs, rhs, is_sub } => {
            out.push(TAG_CARRY_OUT);
            out.push(u8::from(*is_sub));
            write_term(lhs, out);
            write_term(rhs, out);
        }
        BvTerm::Add(a, b)
        | BvTerm::Sub(a, b)
        | BvTerm::And(a, b)
        | BvTerm::Or(a, b)
        | BvTerm::Xor(a, b)
        | BvTerm::Shl(a, b)
        | BvTerm::Lshr(a, b)
        | BvTerm::Ashr(a, b)
        | BvTerm::Eq(a, b) => {
            out.push(match term {
                BvTerm::Add(..) => TAG_ADD,
                BvTerm::Sub(..) => TAG_SUB,
                BvTerm::And(..) => TAG_AND,
                BvTerm::Or(..) => TAG_OR,
                BvTerm::Xor(..) => TAG_XOR,
                BvTerm::Shl(..) => TAG_SHL,
                BvTerm::Lshr(..) => TAG_LSHR,
                BvTerm::Ashr(..) => TAG_ASHR,
                _ => TAG_EQ,
            });
            write_term(a, out);
            write_term(b, out);
        }
    }
}

/// Canonical byte framing of a goal: a tagged pre-order walk with explicit
/// widths, little-endian scalars, and length-prefixed leaf names.
///
/// Injective on well-formed goals — every node emits its tag before its
/// children and every variable-length field is length-prefixed, so no two
/// distinct goals share an encoding.
pub fn bvgoal_canonical_bytes(goal: &BvGoal) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"trust-ir.bvgoal.v1\0");
    write_term(&goal.lhs, &mut out);
    write_term(&goal.rhs, &mut out);
    out
}

/// Domain-separated SHA-256 over [`bvgoal_canonical_bytes`].
///
/// SHA-256 (not the legacy stable checksum) is mandatory: this digest selects
/// evidence, crosses serialization, and is the sole link between a stored
/// refutation and the obligation it is claimed to discharge.
pub fn bvgoal_digest(goal: &BvGoal) -> ProofDigest {
    ProofDigest::sha256_domain(
        "trust_ir.proof.bvblast.goal.v1",
        &bvgoal_canonical_bytes(goal),
    )
}

// ───────────────────────────── obligation formula ─────────────────────────────

/// Schema of the machine-readable claim a bv-blast-backed obligation carries.
pub const BVBLAST_GOAL_SCHEMA: &str = "trust-ir.bvblast.goal.v1";

fn obligation_kind_tag(kind: &ObligationKind) -> Option<&'static str> {
    Some(match kind {
        ObligationKind::BoundsCheck => "BoundsCheck",
        ObligationKind::ArithmeticSafety => "ArithmeticSafety",
        ObligationKind::PanicFreedom => "PanicFreedom",
        ObligationKind::MemorySafety => "MemorySafety",
        _ => return None,
    })
}

fn digest_hex(digest: &ProofDigest) -> String {
    let mut out = String::with_capacity(64);
    for byte in digest.bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).unwrap_or('0'));
        out.push(char::from_digit(u32::from(byte & 0x0f), 16).unwrap_or('0'));
    }
    out
}

/// The obligation's own machine-readable statement of which goal it is about.
///
/// This is the field the authority capability binds against: the obligation
/// declares a goal digest, the validator re-derives the goal from the IR, and
/// the two must agree. Returns `None` for a kind outside the panic-class
/// allowlist (nothing else has a "the sited CondBr condition holds" reading).
pub fn bvblast_goal_formula(
    site: &super::obligations::ObligationSite,
    kind: &ObligationKind,
    goal: &BvGoal,
) -> Option<ProofFormula> {
    let kind_tag = obligation_kind_tag(kind)?;
    let payload = format!(
        "site={}:{}:{}\nkind={}\ngoal={}",
        site.function.index(),
        site.block.index(),
        site.inst_index,
        kind_tag,
        digest_hex(&bvgoal_digest(goal))
    );
    Some(ProofFormula::new(BVBLAST_GOAL_SCHEMA, payload))
}

/// Strictly parse a [`bvblast_goal_formula`] payload back into its three parts:
/// `((function, block, inst_index), kind_tag, goal_digest_hex)`.
///
/// Returns `None` on any deviation — wrong schema, wrong line count, wrong key
/// order, a malformed integer, or a digest that is not 64 lowercase hex digits.
/// A lenient parse here would let a producer smuggle an unbound claim past the
/// binding check.
pub fn bvblast_goal_formula_parts(formula: &ProofFormula) -> Option<((u32, u32, u32), &str, &str)> {
    if formula.schema != BVBLAST_GOAL_SCHEMA {
        return None;
    }
    let mut lines = formula.payload.split('\n');
    let site = lines.next()?.strip_prefix("site=")?;
    let kind = lines.next()?.strip_prefix("kind=")?;
    let goal = lines.next()?.strip_prefix("goal=")?;
    if lines.next().is_some() {
        return None;
    }
    let mut parts = site.split(':');
    let function: u32 = parts.next()?.parse().ok()?;
    let block: u32 = parts.next()?.parse().ok()?;
    let inst_index: u32 = parts.next()?.parse().ok()?;
    if parts.next().is_some() {
        return None;
    }
    if obligation_kind_tag_is_known(kind) && is_bvgoal_digest_hex(goal) {
        Some(((function, block, inst_index), kind, goal))
    } else {
        None
    }
}

/// Whether `digest` is spelled exactly as [`bvgoal_digest_hex`] spells a goal
/// digest: 64 lowercase hexadecimal digits, nothing else.
///
/// The ONE spelling rule for a goal digest. [`bvblast_goal_formula_parts`]
/// holds a formula's claimed digest to it, and a consumer that decodes a digest
/// from untrusted bytes (the bit-blast certificate payload in `trust-ir-ay`)
/// holds that one to it before using it, so no code path ever compares, slices
/// or prints a digest of any other shape.
pub fn is_bvgoal_digest_hex(digest: &str) -> bool {
    digest.len() == 64
        && digest
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn obligation_kind_tag_is_known(tag: &str) -> bool {
    matches!(
        tag,
        "BoundsCheck" | "ArithmeticSafety" | "PanicFreedom" | "MemorySafety"
    )
}

/// Hex rendering of a goal digest, in the spelling
/// [`bvblast_goal_formula_parts`] returns.
pub fn bvgoal_digest_hex(goal: &BvGoal) -> String {
    digest_hex(&bvgoal_digest(goal))
}

// ───────────────────── producer formulas against the site goal ─────────────────────

fn write_smtlib(term: &BvTerm, out: &mut String) {
    use core::fmt::Write as _;
    let binary = |out: &mut String, op: &str, a: &BvTerm, b: &BvTerm| {
        out.push('(');
        out.push_str(op);
        out.push(' ');
        write_smtlib(a, out);
        out.push(' ');
        write_smtlib(b, out);
        out.push(')');
    };
    match term {
        BvTerm::Leaf { name, .. } => out.push_str(name),
        BvTerm::Const { value, width } => {
            let _ = write!(out, "(_ bv{value} {width})");
        }
        BvTerm::Add(a, b) => binary(out, "bvadd", a, b),
        BvTerm::Sub(a, b) => binary(out, "bvsub", a, b),
        BvTerm::And(a, b) => binary(out, "bvand", a, b),
        BvTerm::Or(a, b) => binary(out, "bvor", a, b),
        BvTerm::Xor(a, b) => binary(out, "bvxor", a, b),
        BvTerm::Shl(a, b) => binary(out, "bvshl", a, b),
        BvTerm::Lshr(a, b) => binary(out, "bvlshr", a, b),
        BvTerm::Ashr(a, b) => binary(out, "bvashr", a, b),
        BvTerm::Not(inner) => {
            out.push_str("(bvnot ");
            write_smtlib(inner, out);
            out.push(')');
        }
        BvTerm::ZeroExt(inner, added) => {
            let _ = write!(out, "((_ zero_extend {added}) ");
            write_smtlib(inner, out);
            out.push(')');
        }
        BvTerm::SignExt(inner, added) => {
            let _ = write!(out, "((_ sign_extend {added}) ");
            write_smtlib(inner, out);
            out.push(')');
        }
        BvTerm::Extract { inner, high, low } => {
            let _ = write!(out, "((_ extract {high} {low}) ");
            write_smtlib(inner, out);
            out.push(')');
        }
        // A 1-bit result, as every predicate node of the fragment is.
        BvTerm::Eq(a, b) => {
            out.push_str("(ite ");
            binary(out, "=", a, b);
            out.push_str(" #b1 #b0)");
        }
        // Carry out of `a + b`: the wrapped sum is below `a`.
        BvTerm::CarryOut {
            lhs,
            rhs,
            is_sub: false,
        } => {
            out.push_str("(ite (bvult (bvadd ");
            write_smtlib(lhs, out);
            out.push(' ');
            write_smtlib(rhs, out);
            out.push_str(") ");
            write_smtlib(lhs, out);
            out.push_str(") #b1 #b0)");
        }
        // Carry out of `a - b` (no borrow): `a >=u b`.
        BvTerm::CarryOut {
            lhs,
            rhs,
            is_sub: true,
        } => {
            out.push_str("(ite ");
            binary(out, "bvuge", lhs, rhs);
            out.push_str(" #b1 #b0)");
        }
    }
}

/// The canonical SMT-LIB2 rendering of a goal: `(= <lhs> <rhs>)`, one fixed
/// spelling per node, single spaces, no line breaks.
///
/// This is the canonical bit-vector rendering a producer formula is compared
/// against by [`formula_matches_goal`]. It is injective on well-formed goals
/// TOGETHER WITH the leaf widths: every operator and every constant carries its
/// width, and a leaf's width is supplied by the formula's `bindings`, which
/// [`formula_matches_goal`] requires to name exactly the goal's leaves at
/// exactly their widths.
pub fn bvgoal_smtlib(goal: &BvGoal) -> String {
    let mut out = String::new();
    out.push_str("(= ");
    write_smtlib(&goal.lhs, &mut out);
    out.push(' ');
    write_smtlib(&goal.rhs, &mut out);
    out.push(')');
    out
}

fn collect_leaves(term: &BvTerm, out: &mut Vec<(String, u32)>) {
    match term {
        BvTerm::Leaf { name, width } => {
            if !out.iter().any(|(seen, _)| seen == name) {
                out.push((name.clone(), *width));
            }
        }
        BvTerm::Const { .. } => {}
        BvTerm::Not(inner)
        | BvTerm::ZeroExt(inner, _)
        | BvTerm::SignExt(inner, _)
        | BvTerm::Extract { inner, .. } => collect_leaves(inner, out),
        BvTerm::Add(a, b)
        | BvTerm::Sub(a, b)
        | BvTerm::And(a, b)
        | BvTerm::Or(a, b)
        | BvTerm::Xor(a, b)
        | BvTerm::Shl(a, b)
        | BvTerm::Lshr(a, b)
        | BvTerm::Ashr(a, b)
        | BvTerm::Eq(a, b)
        | BvTerm::CarryOut { lhs: a, rhs: b, .. } => {
            collect_leaves(a, out);
            collect_leaves(b, out);
        }
    }
}

/// The refusal every route reports when a row's own formula does not state
/// the goal re-derived at its site. One spelling, matched by substring.
pub const PRODUCER_FORMULA_DISAGREES: &str = "producer formula disagrees with the site goal";

/// Does a producer-carried formula state exactly `goal`? (WS5.4 (1b))
///
/// A row that already carries a formula is discharged only when this holds; a
/// discharge route must NEVER replace the producer's formula with "whatever
/// condition sits at the site", because that erases exactly the disagreement a
/// verifier must see. True iff ALL of:
///
/// 1. the formula's ONE SMT-LIB text ([`ProofFormula::smtlib_text`]: an
///    `smtlib2` payload whose `smtlib` rendering, if any, is that payload) is
///    exactly [`bvgoal_smtlib`]`(goal)` — canonical bit-vector rendering
///    equality, byte for byte (no normalization: a rewriter here would be
///    trusted code between the claim and the proof). Any other schema's
///    payload is opaque to trust-ir, so nothing shows it states the goal,
///    whatever its rendering says; it never matches. (It used to match on
///    the rendering alone, so an opaque payload stating another claim was
///    discharged and accepted by the authority.)
/// 2. `formula.sort`, if recorded, is `Bool`;
/// 3. `formula.bindings` binds EXACTLY the goal's free leaves, each once, each
///    to [`ClausePlace::Value`] of the SSA value the leaf names
///    ([`bvgoal_leaf_name`]) at [`ClauseSort::BitVec`] of the leaf's width.
///    Empty bindings are UNBINDABLE, never a wildcard, and an extra binding is
///    refused rather than ignored: the formula must mean one thing.
///
/// Anything else — including a formula in a schema this crate cannot read —
/// is `false`, and the row stays undischarged ([`PRODUCER_FORMULA_DISAGREES`]).
pub fn formula_matches_goal(formula: &ProofFormula, goal: &BvGoal) -> bool {
    if formula.smtlib_text() != Some(bvgoal_smtlib(goal).as_str()) {
        return false;
    }
    if formula.sort.as_deref().is_some_and(|sort| sort != "Bool") {
        return false;
    }
    let mut leaves = Vec::new();
    collect_leaves(&goal.lhs, &mut leaves);
    collect_leaves(&goal.rhs, &mut leaves);
    if formula.bindings.len() != leaves.len() {
        return false;
    }
    leaves.iter().all(|(name, width)| {
        let mut bound = formula.bindings.iter().filter(|(n, _)| n == name);
        let (Some((_, binding)), None) = (bound.next(), bound.next()) else {
            return false;
        };
        let names_this_value = match binding.place {
            super::obligations::ClausePlace::Value(value) => bvgoal_leaf_name(value) == *name,
            _ => false,
        };
        names_this_value && binding.sort == super::obligations::ClauseSort::BitVec(*width)
    })
}

/// Does the obligation's formula state the goal re-derived at its site?
///
/// Two spellings are admitted, and nothing else:
///
/// * the bit-blast goal CLAIM ([`BVBLAST_GOAL_SCHEMA`], what a discharge route
///   stamps on a formula-less row): its site, kind and goal digest must each be
///   the obligation's own and the re-derived goal's;
/// * a producer formula for which [`formula_matches_goal`] holds.
///
/// `false` for a formula-less obligation: the caller decides what an absent
/// formula means (a discharge route stamps the claim; nothing is inferred here).
pub fn formula_binds_site_goal(obligation: &ProofObligation, goal: &BvGoal) -> bool {
    let Some(formula) = obligation.formula.as_ref() else {
        return false;
    };
    if formula.schema == BVBLAST_GOAL_SCHEMA {
        let (Some(site), Some(((f, b, i), kind_tag, digest))) = (
            obligation.site.as_ref(),
            bvblast_goal_formula_parts(formula),
        ) else {
            return false;
        };
        return (f, b, i) == (site.function.index(), site.block.index(), site.inst_index)
            && obligation_kind_tag(&obligation.kind) == Some(kind_tag)
            && digest == bvgoal_digest_hex(goal);
    }
    formula_matches_goal(formula, goal)
}

/// Build the producer-side formula [`formula_matches_goal`] admits for `goal`:
/// schema `smtlib2`, payload and `smtlib` the canonical rendering, sort `Bool`,
/// and one `Value`-place `BitVec` binding per free leaf. For producers and
/// tests; a discharge route never calls it on a row that already has a formula.
pub fn bvgoal_formula(goal: &BvGoal) -> Option<ProofFormula> {
    let mut leaves = Vec::new();
    collect_leaves(&goal.lhs, &mut leaves);
    collect_leaves(&goal.rhs, &mut leaves);
    let mut bindings = Vec::with_capacity(leaves.len());
    for (name, width) in leaves {
        let index: u32 = name.strip_prefix('v')?.parse().ok()?;
        let value = ValueId::new(index);
        if bvgoal_leaf_name(value) != name {
            return None;
        }
        bindings.push((
            name,
            super::obligations::ClauseBinding {
                sort: super::obligations::ClauseSort::BitVec(width),
                place: super::obligations::ClausePlace::Value(value),
            },
        ));
    }
    let mut formula = ProofFormula::smtlib2(bvgoal_smtlib(goal), "Bool");
    formula.bindings = bindings;
    Some(formula)
}

// ───────────────────────────── goal derivation ─────────────────────────────

/// Why a sited obligation yields no goal. Every variant is a refusal, never an
/// approximation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalDeriveError {
    /// The obligation records no `site`, so there is no instruction to read a
    /// condition from. A missing site is unbindable, never a wildcard.
    NoSite,
    /// The obligation's kind is outside [`ASSERT_CLASS_OBLIGATION_KINDS`], so a
    /// sited assert condition is not what it states (WS5.4 (1a)).
    KindNotAssertClass { kind: ObligationKind },
    /// `ProofObligation::function` and `ObligationSite::function` disagree.
    SiteFunctionMismatch { obligation: u32, site: u32 },
    /// The site names a function, block, or instruction index this module does
    /// not have.
    SiteNotResolvable { detail: String },
    /// The sited instruction is not a recognisable lowered assert.
    NotALoweredAssert { detail: String },
    /// The condition depends on a value the block's pure prefix does not define
    /// (memory, a call, or a cross-block definition).
    ConditionNotPure { value: u32, detail: String },
    /// The condition's value graph contains an instruction, type, or operator
    /// outside the encodable fragment.
    Unsupported { detail: String },
    /// The derived term is not well-formed.
    Shape(BvTermError),
    /// The derived goal mentions no free variable: a statement about literals,
    /// which is refused as evidence.
    GroundGoal,
}

impl core::fmt::Display for GoalDeriveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoSite => write!(
                f,
                "obligation records no site; a bv-blast goal is derived from the sited assert \
                 only (fail-closed)"
            ),
            Self::KindNotAssertClass { kind } => f.write_str(&assert_class_kind_refusal(kind)),
            Self::SiteFunctionMismatch { obligation, site } => write!(
                f,
                "obligation is scoped to function {obligation} but its site names function {site}"
            ),
            Self::SiteNotResolvable { detail } => write!(f, "site does not resolve: {detail}"),
            Self::NotALoweredAssert { detail } => write!(f, "{detail}"),
            Self::ConditionNotPure { value, detail } => write!(
                f,
                "the assert condition v{value} is not derivable from this block's pure prefix: \
                 {detail} (fail-closed)"
            ),
            Self::Unsupported { detail } => write!(f, "outside the encodable fragment: {detail}"),
            Self::Shape(err) => write!(f, "derived goal is not well-formed: {err}"),
            Self::GroundGoal => write!(
                f,
                "the derived goal mentions no free variable, so it is a fact about literals only; \
                 a refutation of its negation says nothing about any execution (anti-vacuity)"
            ),
        }
    }
}

impl std::error::Error for GoalDeriveError {}

/// True iff the block is a DIVERGING arm: it cannot fall through to any
/// in-function successor, which is how the frontend lowers an assert's failure
/// path (a `core::panicking` call, or a trap under `panic=abort`, then
/// `Unreachable`).
///
/// Recognised structurally rather than by callee name so it does not depend on
/// the panic lane, the runtime's symbol names, or the `Invoke`/`Call` choice.
pub fn is_diverging_arm(function: &Function, target: BlockId) -> bool {
    function
        .blocks
        .iter()
        .find(|b| b.id == target)
        .and_then(|b| b.body.last())
        .is_some_and(|node| matches!(node.inst, Inst::Unreachable))
}

/// Read the assert condition out of the node at an obligation site:
/// `(cond, expected)` where `expected` is the boolean the condition must take
/// for control to continue past the check.
///
/// Two shapes are recognised, and nothing else:
///
/// * **`Inst::Assert { cond }`** (WS5.4) — the ratified proof-carrying
///   instruction: control continues only if `cond` holds, so the obligation it
///   states is exactly `cond` at that point. There is no polarity to infer:
///   the result is always `(cond, true)`. This is the shape the direct lane
///   emits (`assert %c` after `select %overflowed, false, true`).
/// * **A lowered `CondBr`** exactly one of whose successors diverges, in the
///   producer's fixed `condbr assert_cond, <success>, <panic>` convention.
///
/// Fail-closed on ambiguity. If both successors of a `CondBr` diverge, or
/// neither does, the node is not a recognisable lowered assert and no
/// condition is derived — guessing the polarity would prove `cond == false`
/// and record it as discharging an obligation that says `cond == true`.
///
/// Which obligation KINDS a sited assert may back is a separate question,
/// answered by [`is_assert_class_kind`]; every caller gates on it before
/// reading a condition here.
///
/// # Why this lives in `trust-ir`
///
/// The producer (which decides what to emit evidence for) and the validator
/// (which decides what to accept) must not be able to disagree about what an
/// obligation states. There is one implementation and both call it.
pub fn lowered_assert_condition(
    function: &Function,
    node: &InstrNode,
) -> Result<(ValueId, bool), String> {
    if let Inst::Assert { cond, .. } = &node.inst {
        // The condition IS the obligation: `assert c` traps unless `c`, so the
        // fact a proof must establish is `c == true` at this point, read off the
        // instruction itself rather than out of the block graph.
        return Ok((*cond, true));
    }
    let Inst::CondBr {
        cond,
        then_target,
        else_target,
        ..
    } = &node.inst
    else {
        return Err(format!(
            "the instruction at this obligation's site is {}, not an Assert or a CondBr; the \
             sited VC only recognises an Inst::Assert or a lowered assert (fail-closed)",
            inst_label(&node.inst)
        ));
    };
    let then_diverges = is_diverging_arm(function, *then_target);
    let else_diverges = is_diverging_arm(function, *else_target);
    match (then_diverges, else_diverges) {
        // Taking `else` diverges, so the condition must be TRUE. This is the
        // ONLY accepted shape, and it is not an inference — it is the producer's
        // fixed convention: the frontend normalises `assert_cond = cond ==
        // expected` and then ALWAYS emits `condbr assert_cond, <success>,
        // <panic>` (mir_lower.rs, the Assert arm). `expected` is therefore
        // always `true` at a genuine lowered-assert site.
        (false, true) => Ok((*cond, true)),

        // A diverging THEN arm is NOT an inverted assert — it means we are not
        // looking at the producer's assert shape at all, so we must not read a
        // polarity out of it.
        //
        // This arm previously returned `(cond, false)`, deriving polarity from
        // block shape. That inverts in the unwind lane: the panic arm is emitted
        // as `invoke ... -> dead, pad`, whose last node is `Invoke`, NOT
        // `Unreachable` — so the panic arm does not look diverging — while a
        // SUCCESS target whose own MIR terminator is a diverging call
        // (`panic!`/`unreachable!`/`abort()`) does end in `unreachable`. The two
        // tests then swap and the VC proves the NEGATION of the obligation while
        // reporting it as backing that obligation. Measured on the corpus: 0 of
        // 385 sites invert today, but 19 already have panic arms ending in
        // `invoke`, so the precondition is present and one diverging successor
        // is all it takes. Fail closed instead.
        (true, false) => Err(
            "the sited CondBr's THEN arm diverges; the producer convention is \
             `condbr assert_cond, <success>, <panic>` (diverging arm is ELSE), so this is \
             not a recognisable lowered assert and its polarity must not be inferred \
             from block shape (fail-closed)"
                .to_string(),
        ),
        (true, true) => Err(
            "both successors of the sited CondBr diverge; there is no non-diverging arm \
             to prove control stays on (fail-closed)"
                .to_string(),
        ),
        (false, false) => Err(
            "neither successor of the sited CondBr diverges; this is ordinary control flow, \
             not a lowered assert, so no assert condition can be derived (fail-closed)"
                .to_string(),
        ),
    }
}

/// The obligation kinds a sited assert — an `Inst::Assert` or a lowered
/// `CondBr` assert — can back: the panic-class checks whose meaning IS "this
/// check cannot fail".
///
/// ONE constant, read by every route (the bit-blast producer and its validator
/// capability, the SMT sited VC, and [`derive_site_goal`] itself), so the routes
/// cannot disagree about which rows an assert condition may discharge.
///
/// Deliberately narrow. A proof that the sited condition always holds is a
/// panic-freedom fact about THAT check. It is sound for `BoundsCheck`
/// (index-in-bounds) and `ArithmeticSafety` (overflow / shift range / divisor
/// nonzero). It says nothing about a `Postcondition`, a `LoopInvariant` or a
/// `Termination` row that merely happens to be sited on a node that is an
/// assert (WS5.5 sites loop rows at `(header, 0)`, and a header can open with a
/// bounds check): admitting those would let an unrelated condition "prove"
/// them. `MemorySafety` is excluded because alignment and non-nullness are
/// provenance facts a bit-vector condition over an unconstrained pointer does
/// not establish, and `PanicFreedom` because it is a whole-function claim that
/// one site does not establish.
pub const ASSERT_CLASS_OBLIGATION_KINDS: [ObligationKind; 2] = [
    ObligationKind::BoundsCheck,
    ObligationKind::ArithmeticSafety,
];

/// True iff `kind` is in [`ASSERT_CLASS_OBLIGATION_KINDS`]: the table
/// [`super::ObligationKindShape::is_assert_class`], every cell of which is a
/// proved Trust contract (gate 13). The array stays as the same set spelled as
/// data; `assert_class_array_is_the_proved_table` holds the two equal.
pub fn is_assert_class_kind(kind: &ObligationKind) -> bool {
    kind.shape().is_assert_class()
}

/// True iff `inst` is an assert-shaped site node — an `Inst::Assert` or a
/// `CondBr` — i.e. a node whose condition some route could read as the
/// obligation's statement. A row of a non-assert-class kind sited on one is
/// refused with [`assert_class_kind_refusal`], never backed by the condition.
pub fn is_assert_site_inst(inst: &Inst) -> bool {
    matches!(inst, Inst::Assert { .. } | Inst::CondBr { .. })
}

/// The refusal every route reports for a non-assert-class row sited on an
/// assert-shaped node. One spelling, so a consumer can match it by substring.
pub fn assert_class_kind_refusal(kind: &ObligationKind) -> String {
    format!(
        "kind {kind} is not an assert-class obligation: a sited assert condition backs only \
         bounds_check and arithmetic_safety rows (fail-closed)"
    )
}

/// Compact label for an instruction in fail-closed error messages.
fn inst_label(inst: &Inst) -> String {
    let debug = format!("{inst:?}");
    debug
        .split([' ', '{', '('])
        .next()
        .unwrap_or(&debug)
        .to_string()
}

/// The instructions whose results are a pure function of the block's parameters
/// and constants — the only definitions the goal derivation will look through.
///
/// Deliberately narrower than the sited VC's whitelist: `FCmp`, float `BinOp`
/// and float `UnOp` are pure but have no representation in the bit-blast
/// fragment, so they are excluded here rather than being walked into and then
/// rejected deeper. `Overflow` (add/sub only — `MulOverflow` is refused for the
/// same reason `BinOp::Mul` is) and `Select` ARE admitted since WS5.4: the
/// direct lane spells every checked add/sub as `add.overflow` + `select
/// %overflowed, false, true` + `assert`, and both lower to existing nodes of the
/// fragment with no new gate kind (see [`Lowering::lower_overflow`] and
/// [`Lowering::lower_select`]).
fn is_bv_pure_inst(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::NullPtr
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
    )
}

/// Canonical leaf name for a free SSA value. Stable and re-derivable: the same
/// `ValueId` always yields the same name, which is what makes operand sharing in
/// the blasted goal faithful to sharing in the IR.
pub fn bvgoal_leaf_name(value: ValueId) -> String {
    format!("v{}", value.index())
}

struct Lowering<'a> {
    /// `ValueId` -> defining node, restricted to the pure prefix before the site.
    defs: Vec<(ValueId, &'a InstrNode)>,
    /// Block parameters: the free variables of the goal.
    params: &'a [(ValueId, Ty)],
    pointer_bits: u32,
    /// Recursion budget; a cyclic or pathological graph cannot spin here.
    budget: usize,
}

impl<'a> Lowering<'a> {
    fn ty_width(&self, ty: &Ty) -> Result<u32, GoalDeriveError> {
        match ty.bit_width_with(self.pointer_bits) {
            Some(width) if (1..=BVGOAL_MAX_WIDTH).contains(&width) => Ok(width),
            Some(width) => Err(GoalDeriveError::Unsupported {
                detail: format!("type {ty} has width {width}, outside 1..={BVGOAL_MAX_WIDTH}"),
            }),
            None => Err(GoalDeriveError::Unsupported {
                detail: format!("type {ty} has no bit-vector width"),
            }),
        }
    }

    fn lower(&mut self, value: ValueId) -> Result<BvTerm, GoalDeriveError> {
        self.budget = self
            .budget
            .checked_sub(1)
            .ok_or_else(|| GoalDeriveError::Unsupported {
                detail: "condition value graph exceeded the traversal budget".to_string(),
            })?;

        if let Some((_, ty)) = self.params.iter().find(|(id, _)| *id == value) {
            let width = self.ty_width(ty)?;
            return Ok(BvTerm::leaf(bvgoal_leaf_name(value), width));
        }
        let Some((_, node)) = self.defs.iter().find(|(id, _)| *id == value).copied() else {
            return Err(GoalDeriveError::ConditionNotPure {
                value: value.index(),
                detail: "no defining instruction for it appears in this block's pure prefix"
                    .to_string(),
            });
        };
        self.lower_inst(value, node)
    }

    fn lower_inst(
        &mut self,
        value: ValueId,
        node: &'a InstrNode,
    ) -> Result<BvTerm, GoalDeriveError> {
        match &node.inst {
            Inst::Const { ty, value: konst } => self.lower_const(ty, konst),
            Inst::NullPtr => Ok(BvTerm::Const {
                value: 0,
                width: self.pointer_bits,
            }),
            Inst::Copy { operand, .. } => self.lower(*operand),
            Inst::BinOp { op, ty, lhs, rhs } => {
                let width = self.ty_width(ty)?;
                let a = self.lower(*lhs)?;
                let b = self.lower(*rhs)?;
                self.lower_binop(*op, width, a, b)
            }
            Inst::UnOp { op, ty, operand } => {
                let width = self.ty_width(ty)?;
                let x = self.lower(*operand)?;
                match op {
                    UnOp::Not => Ok(BvTerm::Not(x.boxed())),
                    UnOp::Neg => Ok(BvTerm::Sub(
                        BvTerm::Const { value: 0, width }.boxed(),
                        x.boxed(),
                    )),
                    other => Err(GoalDeriveError::Unsupported {
                        detail: format!(
                            "UnOp::{other:?} has no bit-vector encoding in this fragment"
                        ),
                    }),
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let width = self.ty_width(ty)?;
                let a = self.lower(*lhs)?;
                let b = self.lower(*rhs)?;
                Ok(lower_icmp(*op, width, a, b))
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let src = self.ty_width(src_ty)?;
                let dst = self.ty_width(dst_ty)?;
                let x = self.lower(*operand)?;
                lower_cast(*op, src, dst, x)
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                self.lower_overflow(value, node, *op, ty, *lhs, *rhs)
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => self.lower_select(ty, *cond, *then_val, *else_val),
            other => Err(GoalDeriveError::ConditionNotPure {
                value: value.index(),
                detail: format!(
                    "it is defined by {}, which is not a pure bit-vector instruction",
                    inst_label(other)
                ),
            }),
        }
    }

    /// `%r, %o = add.overflow|sub.overflow T a, b`: result 0 is the wrapped
    /// value, result 1 the 1-bit overflow flag, at `T`'s signedness (the same
    /// reading the reference interpreter and the adapter's `encode_overflow_check`
    /// give it).
    ///
    /// The flag uses only existing nodes:
    ///
    /// * unsigned add — the ripple carry-out: `CarryOut { a, b, is_sub: false }`;
    /// * unsigned sub — the borrow, `a <u b`: `Not(CarryOut { a, b, is_sub: true })`;
    /// * signed add — both operands' signs agree and the result's differs:
    ///   `msb((a ^ r) & (b ^ r))` with `r = a + b`;
    /// * signed sub — the operands' signs differ and the result's differs from
    ///   `a`'s: `msb((a ^ b) & (a ^ r))` with `r = a - b`.
    ///
    /// `MulOverflow` is refused for the reason `BinOp::Mul` is.
    fn lower_overflow(
        &mut self,
        value: ValueId,
        node: &'a InstrNode,
        op: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<BvTerm, GoalDeriveError> {
        if op == OverflowOp::MulOverflow {
            return Err(GoalDeriveError::Unsupported {
                detail: "OverflowOp::MulOverflow is refused structurally, as BinOp::Mul is: \
                         bit-blasting a multiply is unbounded in practice"
                    .to_string(),
            });
        }
        if !ty.is_integer() {
            return Err(GoalDeriveError::Unsupported {
                detail: format!("overflow arithmetic over the non-integer type {ty}"),
            });
        }
        let position = match node.results.as_slice() {
            [v0, _] if *v0 == value => 0,
            [_, v1] if *v1 == value => 1,
            _ => {
                return Err(GoalDeriveError::Unsupported {
                    detail: "an Overflow node must carry exactly (value, overflowed) results"
                        .to_string(),
                });
            }
        };
        let width = self.ty_width(ty)?;
        let a = self.lower(lhs)?;
        let b = self.lower(rhs)?;
        let is_add = op == OverflowOp::AddOverflow;
        let wrapped = if is_add {
            BvTerm::Add(a.clone().boxed(), b.clone().boxed())
        } else {
            BvTerm::Sub(a.clone().boxed(), b.clone().boxed())
        };
        if position == 0 {
            return Ok(wrapped);
        }
        if !ty.is_signed() {
            let carry = BvTerm::CarryOut {
                lhs: a.boxed(),
                rhs: b.boxed(),
                is_sub: !is_add,
            };
            return Ok(if is_add {
                carry
            } else {
                BvTerm::Not(carry.boxed())
            });
        }
        let sign_mix = if is_add {
            BvTerm::And(
                BvTerm::Xor(a.boxed(), wrapped.clone().boxed()).boxed(),
                BvTerm::Xor(b.boxed(), wrapped.boxed()).boxed(),
            )
        } else {
            BvTerm::And(
                BvTerm::Xor(a.clone().boxed(), b.boxed()).boxed(),
                BvTerm::Xor(a.boxed(), wrapped.boxed()).boxed(),
            )
        };
        Ok(BvTerm::Extract {
            inner: sign_mix.boxed(),
            high: width - 1,
            low: width - 1,
        })
    }

    /// `select T c, t, e` over a 1-bit `c`: `(m & t) | (~m & e)` where `m` is
    /// `c` replicated to `T`'s width (`c` itself at width 1, `SignExt(c, w-1)`
    /// otherwise — all ones when `c` is set, all zeros when it is clear).
    fn lower_select(
        &mut self,
        ty: &Ty,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> Result<BvTerm, GoalDeriveError> {
        let width = self.ty_width(ty)?;
        let c = self.lower(cond)?;
        let cond_width = c.width().map_err(GoalDeriveError::Shape)?;
        if cond_width != 1 {
            return Err(GoalDeriveError::Unsupported {
                detail: format!("select condition is {cond_width} bits wide, not a 1-bit bool"),
            });
        }
        let t = self.lower(then_val)?;
        let e = self.lower(else_val)?;
        let mask = if width == 1 {
            c
        } else {
            BvTerm::SignExt(c.boxed(), width - 1)
        };
        Ok(BvTerm::Or(
            BvTerm::And(mask.clone().boxed(), t.boxed()).boxed(),
            BvTerm::And(BvTerm::Not(mask.boxed()).boxed(), e.boxed()).boxed(),
        ))
    }

    fn lower_const(&self, ty: &Ty, konst: &Constant) -> Result<BvTerm, GoalDeriveError> {
        let width = self.ty_width(ty)?;
        let value = match konst {
            Constant::Bool(b) => {
                if width != 1 {
                    return Err(GoalDeriveError::Unsupported {
                        detail: format!("boolean constant declared at {width} bits"),
                    });
                }
                u128::from(*b)
            }
            // Two's-complement truncation to the declared width is the IR's own
            // reading of an integer literal at that type, not a reinterpretation.
            Constant::Int(i) => mask_to_width(*i as u128, width),
            Constant::U128(u) => mask_to_width(*u, width),
            other => {
                return Err(GoalDeriveError::Unsupported {
                    detail: format!(
                        "constant {} has no bit-vector encoding in this fragment",
                        constant_label(other)
                    ),
                });
            }
        };
        Ok(BvTerm::Const { value, width })
    }

    fn lower_binop(
        &self,
        op: BinOp,
        width: u32,
        a: BvTerm,
        b: BvTerm,
    ) -> Result<BvTerm, GoalDeriveError> {
        let _ = width;
        Ok(match op {
            BinOp::Add => BvTerm::Add(a.boxed(), b.boxed()),
            BinOp::Sub => BvTerm::Sub(a.boxed(), b.boxed()),
            BinOp::And => BvTerm::And(a.boxed(), b.boxed()),
            BinOp::Or => BvTerm::Or(a.boxed(), b.boxed()),
            BinOp::Xor => BvTerm::Xor(a.boxed(), b.boxed()),
            BinOp::Shl => BvTerm::Shl(a.boxed(), b.boxed()),
            BinOp::LShr => BvTerm::Lshr(a.boxed(), b.boxed()),
            BinOp::AShr => BvTerm::Ashr(a.boxed(), b.boxed()),
            // MEASURED, not stylistic: a width-8 multiply goal blasted to
            // 1,617,446 resolution steps and 1.29 GB of JSON in 63 s, and width
            // 16 did not terminate. The exporter has no step budget and the
            // allocation precedes any timer, so refusing the node is the only
            // guard that holds.
            BinOp::Mul => {
                return Err(GoalDeriveError::Unsupported {
                    detail: "BinOp::Mul is refused structurally: bit-blasting a multiply is \
                             unbounded in practice (measured 1.29 GB / 63 s at width 8, \
                             non-terminating at width 16) and the exporter offers no budget"
                        .to_string(),
                });
            }
            // Division has no divider node in the fragment; a restoring-division
            // gate topology would have to be introduced and re-checked.
            BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem => {
                return Err(GoalDeriveError::Unsupported {
                    detail: format!("BinOp::{op:?} has no gate topology in this fragment"),
                });
            }
            other => {
                return Err(GoalDeriveError::Unsupported {
                    detail: format!("BinOp::{other:?} has no bit-vector encoding (float or wide)"),
                });
            }
        })
    }
}

fn mask_to_width(value: u128, width: u32) -> u128 {
    if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    }
}

fn constant_label(konst: &Constant) -> String {
    let debug = format!("{konst:?}");
    debug
        .split([' ', '{', '('])
        .next()
        .unwrap_or(&debug)
        .to_string()
}

/// Integer comparison to a 1-bit predicate.
///
/// Unsigned compares decompose to the borrow flag of `a - b`:
/// `a <u b  ⟺  NOT CarryOut(a, b, is_sub = true)`. The signed forms use the
/// bias identity `a <s b ⟺ (a XOR 2^(w-1)) <u (b XOR 2^(w-1))`, which
/// introduces no new gate kind. `Eq`/`Ne` are the `Eq` node and its negation.
fn lower_icmp(op: ICmpOp, width: u32, a: BvTerm, b: BvTerm) -> BvTerm {
    let ult = |x: BvTerm, y: BvTerm| {
        BvTerm::Not(
            BvTerm::CarryOut {
                lhs: x.boxed(),
                rhs: y.boxed(),
                is_sub: true,
            }
            .boxed(),
        )
    };
    let uge = |x: BvTerm, y: BvTerm| BvTerm::CarryOut {
        lhs: x.boxed(),
        rhs: y.boxed(),
        is_sub: true,
    };
    let bias = |x: BvTerm| {
        BvTerm::Xor(
            x.boxed(),
            BvTerm::Const {
                value: 1u128 << (width - 1),
                width,
            }
            .boxed(),
        )
    };
    match op {
        ICmpOp::Eq => BvTerm::Eq(a.boxed(), b.boxed()),
        ICmpOp::Ne => BvTerm::Not(BvTerm::Eq(a.boxed(), b.boxed()).boxed()),
        ICmpOp::Ult => ult(a, b),
        ICmpOp::Uge => uge(a, b),
        ICmpOp::Ugt => ult(b, a),
        ICmpOp::Ule => uge(b, a),
        ICmpOp::Slt => ult(bias(a), bias(b)),
        ICmpOp::Sge => uge(bias(a), bias(b)),
        ICmpOp::Sgt => ult(bias(b), bias(a)),
        ICmpOp::Sle => uge(bias(b), bias(a)),
    }
}

/// Cast to a width adjustment.
///
/// The pointer casts are the identity at equal width — the same flat
/// `pointer_bits`-wide pointer model the adapter's `encode_cast` already uses.
/// This model can express `p & 7 == 0`, but it cannot express *provenance*
/// (that `p` came from an 8-aligned allocation), so alignment obligations
/// encode fine and then refute; that is a hypothesis gap, not an encoding gap.
fn lower_cast(op: CastOp, src: u32, dst: u32, x: BvTerm) -> Result<BvTerm, GoalDeriveError> {
    let widen_or_narrow = |zero_fill: bool| -> Result<BvTerm, GoalDeriveError> {
        Ok(match dst.cmp(&src) {
            core::cmp::Ordering::Equal => x.clone(),
            core::cmp::Ordering::Less => BvTerm::Extract {
                inner: x.clone().boxed(),
                high: dst - 1,
                low: 0,
            },
            core::cmp::Ordering::Greater if zero_fill => {
                BvTerm::ZeroExt(x.clone().boxed(), dst - src)
            }
            core::cmp::Ordering::Greater => BvTerm::SignExt(x.clone().boxed(), dst - src),
        })
    };
    match op {
        CastOp::Trunc => {
            if dst > src {
                return Err(GoalDeriveError::Unsupported {
                    detail: format!("Trunc widens {src} -> {dst}"),
                });
            }
            widen_or_narrow(true)
        }
        CastOp::ZExt => {
            if dst < src {
                return Err(GoalDeriveError::Unsupported {
                    detail: format!("ZExt narrows {src} -> {dst}"),
                });
            }
            widen_or_narrow(true)
        }
        CastOp::SExt => {
            if dst < src {
                return Err(GoalDeriveError::Unsupported {
                    detail: format!("SExt narrows {src} -> {dst}"),
                });
            }
            widen_or_narrow(false)
        }
        // Bit-pattern-preserving casts in the flat pointer model.
        CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr | CastOp::Bitcast => {
            widen_or_narrow(true)
        }
        other => Err(GoalDeriveError::Unsupported {
            detail: format!("CastOp::{other:?} has no bit-vector encoding in this fragment"),
        }),
    }
}

/// Reconstruct the bit-vector goal a sited panic-class obligation states.
///
/// The obligation's kind must be assert-class ([`is_assert_class_kind`]);
/// any other kind is refused with [`GoalDeriveError::KindNotAssertClass`]
/// before the site is read. The result is `condition == #b1` where
/// `condition` is the assert condition at `obligation.site` — the `cond` of an
/// `Inst::Assert`, or of a lowered `CondBr` assert ([`lowered_assert_condition`])
/// — lowered over the block's parameters as free variables
/// and the block's pure prefix as definitions. Nothing about how control reached
/// the block is assumed: no path condition, no caller precondition, no memory.
/// That is a strictly weaker hypothesis set than any real execution has, so a
/// proof of this goal implies the condition holds on every real path into the
/// block — weakening hypotheses can only lose proofs, never manufacture them.
///
/// # Errors
///
/// [`GoalDeriveError`] on any refusal. In particular a goal with no free leaf is
/// rejected as [`GoalDeriveError::GroundGoal`]: it is a fact about literals and
/// carries no information about any execution.
pub fn derive_site_goal(
    module: &Module,
    obligation: &ProofObligation,
) -> Result<BvGoal, GoalDeriveError> {
    let site = obligation.site.as_ref().ok_or(GoalDeriveError::NoSite)?;
    // The kind gate comes before anything is read from the site: a
    // non-assert-class row sited on an assert does not STATE that assert's
    // condition, so there is no goal to derive for it (WS5.4 (1a)).
    if !is_assert_class_kind(&obligation.kind) {
        return Err(GoalDeriveError::KindNotAssertClass {
            kind: obligation.kind.clone(),
        });
    }
    if let Some(scoped) = obligation.function
        && scoped != site.function
    {
        return Err(GoalDeriveError::SiteFunctionMismatch {
            obligation: scoped.index(),
            site: site.function.index(),
        });
    }
    let function = module
        .functions
        .iter()
        .find(|f| f.id == site.function)
        .ok_or_else(|| GoalDeriveError::SiteNotResolvable {
            detail: format!("module has no function {}", site.function.index()),
        })?;
    let block = function
        .blocks
        .iter()
        .find(|b| b.id == site.block)
        .ok_or_else(|| GoalDeriveError::SiteNotResolvable {
            detail: format!(
                "function {} has no block bb{}",
                function.name,
                site.block.index()
            ),
        })?;
    let index = site.inst_index as usize;
    let node = block
        .body
        .get(index)
        .ok_or_else(|| GoalDeriveError::SiteNotResolvable {
            detail: format!(
                "bb{} has {} instructions, so index {index} is out of range",
                site.block.index(),
                block.body.len()
            ),
        })?;

    let (cond, expected) = lowered_assert_condition(function, node)
        .map_err(|detail| GoalDeriveError::NotALoweredAssert { detail })?;

    // Definitions available to the condition: the pure prefix STRICTLY BEFORE
    // the site. A later definition cannot be an input to an earlier branch, and
    // admitting one would let a value be read before it exists.
    let mut defs: Vec<(ValueId, &InstrNode)> = Vec::new();
    for prior in block.body.iter().take(index) {
        if !is_bv_pure_inst(&prior.inst) {
            continue;
        }
        for result in &prior.results {
            defs.push((*result, prior));
        }
    }

    let mut lowering = Lowering {
        defs,
        params: &block.params,
        pointer_bits: module.pointer_bits(),
        budget: BVGOAL_MAX_NODES,
    };
    let condition = lowering.lower(cond)?;
    // `expected` is always `true` at an accepted site; the `false` arm is
    // retained as defensive structure so a future producer shape that genuinely
    // inverts cannot silently take the `true` path.
    let condition = if expected {
        condition
    } else {
        BvTerm::Not(condition.boxed())
    };

    let goal = BvGoal::predicate(condition);
    goal.validate_shape().map_err(GoalDeriveError::Shape)?;
    if goal.is_ground() {
        return Err(GoalDeriveError::GroundGoal);
    }
    Ok(goal)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn width_rejects_a_leaf_used_at_two_widths() {
        // ay's blaster caches leaves by NAME and ignores the width on every
        // lookup after the first, silently coercing the second occurrence. This
        // must be caught here, because it will not be caught there.
        let term = BvTerm::Add(BvTerm::leaf("x", 8).boxed(), BvTerm::leaf("x", 32).boxed());
        assert_eq!(
            term.width(),
            Err(BvTermError::LeafWidthConflict {
                name: "x".to_string(),
                first: 8,
                second: 32
            })
        );
    }

    #[test]
    fn width_of_a_predicate_is_one_bit() {
        let term = BvTerm::Not(
            BvTerm::CarryOut {
                lhs: BvTerm::leaf("x", 64).boxed(),
                rhs: BvTerm::Const {
                    value: 16,
                    width: 64,
                }
                .boxed(),
                is_sub: true,
            }
            .boxed(),
        );
        assert_eq!(term.width(), Ok(1));
        let goal = BvGoal::predicate(term);
        assert_eq!(goal.validate_shape(), Ok(()));
        assert!(!goal.is_ground());
    }

    #[test]
    fn ground_goals_are_detectable_syntactically() {
        let goal = BvGoal::predicate(BvTerm::Eq(
            BvTerm::Const {
                value: 1,
                width: 64,
            }
            .boxed(),
            BvTerm::Const {
                value: 1,
                width: 64,
            }
            .boxed(),
        ));
        assert_eq!(goal.validate_shape(), Ok(()));
        assert!(goal.is_ground());
    }

    #[test]
    fn canonical_bytes_separate_distinct_goals() {
        let a = BvGoal::predicate(BvTerm::Eq(
            BvTerm::leaf("v1", 64).boxed(),
            BvTerm::leaf("v2", 64).boxed(),
        ));
        let b = BvGoal::predicate(BvTerm::Eq(
            BvTerm::leaf("v1", 64).boxed(),
            BvTerm::leaf("v3", 64).boxed(),
        ));
        assert_ne!(bvgoal_canonical_bytes(&a), bvgoal_canonical_bytes(&b));
        assert_ne!(bvgoal_digest(&a), bvgoal_digest(&b));
        // The ay payload cannot make this distinction: leaf names are erased
        // from the serialized proof (VarRole::InputLeaf carries an index only),
        // so proofs of these two goals are byte-identical. The digest is the
        // only thing that separates them.
    }

    #[test]
    fn canonical_bytes_separate_a_name_prefix_from_its_extension() {
        // Length-prefixing, not delimiters: `v1`+`v23` must not collide with
        // `v12`+`v3`.
        let a = BvGoal::predicate(BvTerm::Eq(
            BvTerm::leaf("v1", 64).boxed(),
            BvTerm::leaf("v23", 64).boxed(),
        ));
        let b = BvGoal::predicate(BvTerm::Eq(
            BvTerm::leaf("v12", 64).boxed(),
            BvTerm::leaf("v3", 64).boxed(),
        ));
        assert_ne!(bvgoal_canonical_bytes(&a), bvgoal_canonical_bytes(&b));
    }

    #[test]
    fn formula_round_trips_strictly() {
        use crate::value::{BlockId, FuncId};
        let site =
            super::super::obligations::ObligationSite::new(FuncId::new(7), BlockId::new(4), 74);
        let goal = BvGoal::predicate(BvTerm::Not(
            BvTerm::CarryOut {
                lhs: BvTerm::leaf("v9", 64).boxed(),
                rhs: BvTerm::Const {
                    value: 16,
                    width: 64,
                }
                .boxed(),
                is_sub: true,
            }
            .boxed(),
        ));
        let formula = bvblast_goal_formula(&site, &ObligationKind::BoundsCheck, &goal)
            .expect("kind is in the allowlist");
        let (parsed_site, kind, digest) = bvblast_goal_formula_parts(&formula).expect("round trip");
        assert_eq!(parsed_site, (7, 4, 74));
        assert_eq!(kind, "BoundsCheck");
        assert_eq!(digest, bvgoal_digest_hex(&goal));
    }

    #[test]
    fn goal_digest_spelling_is_exactly_what_the_digest_writer_emits() {
        let goal = BvGoal::predicate(BvTerm::leaf("v0", 1));
        let digest = bvgoal_digest_hex(&goal);
        assert!(is_bvgoal_digest_hex(&digest), "the writer's own spelling");
        assert!(!is_bvgoal_digest_hex(&digest[..63]), "one digit short");
        assert!(
            !is_bvgoal_digest_hex(&format!("{digest}0")),
            "one digit long"
        );
        assert!(
            !is_bvgoal_digest_hex(&digest.to_uppercase()),
            "uppercase hex"
        );
        // 21 three-byte characters plus one byte: 64 BYTES, no hex digit.
        let non_ascii = format!("{}0", "\u{20ac}".repeat(21));
        assert_eq!(non_ascii.len(), 64);
        assert!(
            !is_bvgoal_digest_hex(&non_ascii),
            "non-ASCII of the right byte length"
        );
    }

    #[test]
    fn formula_parse_is_strict() {
        let mut formula =
            ProofFormula::new(BVBLAST_GOAL_SCHEMA, "site=1:2:3\nkind=BoundsCheck\ngoal=00");
        assert_eq!(bvblast_goal_formula_parts(&formula), None, "short digest");
        formula.payload = format!("site=1:2:3\nkind=Nonsense\ngoal={}", "a".repeat(64));
        assert_eq!(bvblast_goal_formula_parts(&formula), None, "unknown kind");
        formula.payload = format!("site=1:2\nkind=BoundsCheck\ngoal={}", "a".repeat(64));
        assert_eq!(bvblast_goal_formula_parts(&formula), None, "short site");
        formula.payload = format!(
            "site=1:2:3\nkind=BoundsCheck\ngoal={}\nextra",
            "a".repeat(64)
        );
        assert_eq!(bvblast_goal_formula_parts(&formula), None, "trailing line");
        formula.payload = format!("site=1:2:3\nkind=BoundsCheck\ngoal={}", "A".repeat(64));
        assert_eq!(bvblast_goal_formula_parts(&formula), None, "uppercase hex");
        let wrong_schema = ProofFormula::new(
            "smtlib2",
            format!("site=1:2:3\nkind=BoundsCheck\ngoal={}", "a".repeat(64)),
        );
        assert_eq!(bvblast_goal_formula_parts(&wrong_schema), None, "schema");
    }

    /// REGRESSION: a goal must be bounded by BLAST COST, not node count.
    ///
    /// `BVGOAL_MAX_NODES = 256` was documented as "far below anything that
    /// blasts slowly". That was measured to be false: at width 128, 6 nodes
    /// blasted in 20 ms, 36 nodes in 237 ms, and 68 nodes did not finish in
    /// 400 s — every one of them far inside the node cap. Because the validator
    /// re-solves from scratch, an unbounded goal is a denial-of-service
    /// reachable with no valid proof at all.
    #[test]
    fn wide_shift_chains_are_rejected_by_cost_though_they_pass_the_node_cap() {
        // A chain of 128-bit shifts, well under BVGOAL_MAX_NODES.
        let mut term = BvTerm::leaf("x", 128);
        for _ in 0..40 {
            term = BvTerm::Shl(
                term.boxed(),
                BvTerm::Const {
                    value: 1,
                    width: 128,
                }
                .boxed(),
            );
        }
        let nodes = term.node_count();
        assert!(
            nodes <= BVGOAL_MAX_NODES,
            "precondition: this shape must PASS the node cap ({nodes} nodes) so the test \
             exercises the cost bound and not the count bound"
        );

        let goal = BvGoal {
            lhs: BvTerm::Eq(term.clone().boxed(), term.boxed()),
            rhs: BvTerm::one_bit_true(),
        };
        match goal.validate_shape() {
            Err(BvTermError::TooExpensive { got, max }) => {
                assert!(got > max, "cost {got} must exceed the cap {max}");
            }
            other => panic!(
                "a {nodes}-node chain of 128-bit shifts must be refused on COST; got {other:?}"
            ),
        }
    }

    /// The real corpus shapes stay comfortably inside the cost bound — the
    /// budget must not be so tight that it rejects honest work.
    #[test]
    fn corpus_shaped_goals_are_within_the_cost_budget() {
        // `zext_64(x:u32 >>u k & 0xF) <u 16`, the proved corpus shape.
        let x = BvTerm::leaf("x", 32);
        let shifted = BvTerm::Lshr(x.boxed(), BvTerm::leaf("k", 32).boxed());
        let masked = BvTerm::And(
            shifted.boxed(),
            BvTerm::Const {
                value: 0xF,
                width: 32,
            }
            .boxed(),
        );
        let widened = BvTerm::ZeroExt(masked.boxed(), 32);
        let cond = BvTerm::Not(
            BvTerm::CarryOut {
                lhs: widened.boxed(),
                rhs: BvTerm::Const {
                    value: 16,
                    width: 64,
                }
                .boxed(),
                is_sub: true,
            }
            .boxed(),
        );
        let goal = BvGoal {
            lhs: cond,
            rhs: BvTerm::one_bit_true(),
        };
        let cost = goal.lhs.blast_cost() + goal.rhs.blast_cost();
        assert!(
            cost <= BVGOAL_MAX_BLAST_COST,
            "the proved corpus shape costs {cost}, above the cap {BVGOAL_MAX_BLAST_COST}"
        );
        assert_eq!(goal.validate_shape(), Ok(()));
    }

    /// WS5.4 (1b): the canonical rendering, and the exact-match admission of a
    /// producer formula against it.
    #[test]
    fn a_producer_formula_matches_only_its_own_goal() {
        let x = BvTerm::leaf("v3", 8);
        let add = BvGoal::predicate(BvTerm::Not(Box::new(BvTerm::CarryOut {
            lhs: Box::new(x.clone()),
            rhs: Box::new(BvTerm::Const { value: 1, width: 8 }),
            is_sub: false,
        })));
        let sub = BvGoal::predicate(BvTerm::CarryOut {
            lhs: Box::new(x),
            rhs: Box::new(BvTerm::Const { value: 1, width: 8 }),
            is_sub: true,
        });
        assert_eq!(
            bvgoal_smtlib(&add),
            "(= (bvnot (ite (bvult (bvadd v3 (_ bv1 8)) v3) #b1 #b0)) (_ bv1 1))"
        );
        assert_eq!(
            bvgoal_smtlib(&sub),
            "(= (ite (bvuge v3 (_ bv1 8)) #b1 #b0) (_ bv1 1))"
        );

        let formula = bvgoal_formula(&add).expect("IR-named leaves");
        assert!(formula_matches_goal(&formula, &add));
        assert!(
            !formula_matches_goal(&formula, &sub),
            "a formula for a+.. is not a-.."
        );
        // Unbound, mis-sorted, or mis-placed leaves never match.
        let mut unbound = formula.clone();
        unbound.bindings.clear();
        assert!(!formula_matches_goal(&unbound, &add));
        let mut mis_sorted = formula.clone();
        mis_sorted.bindings[0].1.sort = super::super::obligations::ClauseSort::BitVec(16);
        assert!(!formula_matches_goal(&mis_sorted, &add));
        let mut mis_placed = formula.clone();
        mis_placed.bindings[0].1.place =
            super::super::obligations::ClausePlace::Value(ValueId::new(4));
        assert!(!formula_matches_goal(&mis_placed, &add));
        // Only the ONE SMT-LIB text is matched: an opaque schema never is,
        // whatever its rendering says; an `smtlib2` payload with no rendering
        // states the same text.
        let mut opaque = formula.clone();
        opaque.schema = "trust-types.Formula@1".to_string();
        assert!(!formula_matches_goal(&opaque, &add));
        let mut payload_only = formula.clone();
        payload_only.smtlib = None;
        assert!(formula_matches_goal(&payload_only, &add));
        // A non-IR leaf name has no formula.
        assert!(bvgoal_formula(&BvGoal::predicate(BvTerm::leaf("x", 1))).is_none());
    }

    #[test]
    fn only_assert_class_kinds_are_admitted() {
        assert!(is_assert_class_kind(&ObligationKind::BoundsCheck));
        assert!(is_assert_class_kind(&ObligationKind::ArithmeticSafety));
        for kind in [
            ObligationKind::Postcondition,
            ObligationKind::LoopInvariant,
            ObligationKind::Termination,
            ObligationKind::MemorySafety,
            ObligationKind::PanicFreedom,
        ] {
            assert!(!is_assert_class_kind(&kind));
            assert!(assert_class_kind_refusal(&kind).contains("is not an assert-class obligation"));
        }
    }

    /// The data spelling of the assert-class set and the PROVED table agree on
    /// every kind shape — the array is what callers enumerate, the table is
    /// what the gate proves, and neither may drift from the other.
    #[test]
    fn assert_class_array_is_the_proved_table() {
        use super::super::ObligationKindShape;
        for &shape in ObligationKindShape::ALL {
            let in_array = ASSERT_CLASS_OBLIGATION_KINDS
                .iter()
                .any(|kind| kind.shape() == shape);
            assert_eq!(in_array, shape.is_assert_class(), "{}", shape.name());
        }
        for kind in &ASSERT_CLASS_OBLIGATION_KINDS {
            assert!(is_assert_class_kind(kind));
        }
    }
}
