// trust-ir-contract/formula: SMT-level formulas
//
// These are the verification conditions sent to solvers. Backend-agnostic —
// trust-router encodes these into ay/trust-wp/ty specific representations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashSet;
use serde::{Deserialize, Serialize};

// Re-export Sort under the formula module path so `crate::formula::Sort`
// resolves exactly as it did in trust-types' `formula` module.
pub use crate::sort::{RoundingMode, Sort};

// ── Wide (128-bit) integer literal serde helpers ────────────────────────────
//
// serde_json (without the `arbitrary_precision` feature) cannot represent an
// i128/u128 outside the i64/u64 range: `serialize_i128`/`serialize_u128` fail
// with "number out of range". A `Formula` carrying a 128-bit literal (e.g. an
// AArch64 128-bit NEON vector constant, or a Rust i128/u128) therefore could
// not be turned into JSON at all — which ICE'd trust's verifier-api digest
// path (`serde_json::to_value` inside `stable_json_digest`).
//
// These helpers keep the encoding of every currently-working value byte-for-
// byte identical and only fix the previously-crashing tail:
//   * Human-readable formats (serde_json): in-range values serialize as a bare
//     number exactly as the derive did; only values outside [i64::MIN, u64::MAX]
//     fall back to a decimal string. Deserialization accepts either form
//     (`deserialize_any`, valid because JSON is self-describing).
//   * Binary self-describing formats (bincode / MessagePack): always use the
//     native 128-bit path, so their bytes are unchanged for ALL values and
//     `deserialize_any` is never required (`deserialize_i128`/`deserialize_u128`).
mod wide_i128 {
    use core::fmt;
    use serde::de::{self, Visitor};
    use serde::{Deserializer, Serializer};

    // serde_json's Number holds [i64::MIN, u64::MAX]; outside it errors.
    const LO: i128 = i64::MIN as i128;
    const HI: i128 = u64::MAX as i128;

    pub fn serialize<S: Serializer>(v: &i128, s: S) -> Result<S::Ok, S::Error> {
        if s.is_human_readable() && !(*v >= LO && *v <= HI) {
            s.serialize_str(&v.to_string())
        } else {
            s.serialize_i128(*v)
        }
    }

    struct WideI128;
    impl Visitor<'_> for WideI128 {
        type Value = i128;
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a 128-bit signed integer or its decimal string")
        }
        fn visit_i64<E: de::Error>(self, v: i64) -> Result<i128, E> {
            Ok(i128::from(v))
        }
        fn visit_u64<E: de::Error>(self, v: u64) -> Result<i128, E> {
            Ok(i128::from(v))
        }
        fn visit_i128<E: de::Error>(self, v: i128) -> Result<i128, E> {
            Ok(v)
        }
        fn visit_u128<E: de::Error>(self, v: u128) -> Result<i128, E> {
            i128::try_from(v).map_err(|_| E::custom("integer literal exceeds i128 range"))
        }
        fn visit_str<E: de::Error>(self, s: &str) -> Result<i128, E> {
            s.parse::<i128>()
                .map_err(|_| E::custom("invalid i128 decimal string literal"))
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<i128, D::Error> {
        if d.is_human_readable() {
            d.deserialize_any(WideI128)
        } else {
            d.deserialize_i128(WideI128)
        }
    }
}

mod wide_u128 {
    use core::fmt;
    use serde::de::{self, Visitor};
    use serde::{Deserializer, Serializer};

    const HI: u128 = u64::MAX as u128;

    pub fn serialize<S: Serializer>(v: &u128, s: S) -> Result<S::Ok, S::Error> {
        if s.is_human_readable() && *v > HI {
            s.serialize_str(&v.to_string())
        } else {
            s.serialize_u128(*v)
        }
    }

    struct WideU128;
    impl Visitor<'_> for WideU128 {
        type Value = u128;
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a 128-bit unsigned integer or its decimal string")
        }
        fn visit_u64<E: de::Error>(self, v: u64) -> Result<u128, E> {
            Ok(u128::from(v))
        }
        fn visit_i64<E: de::Error>(self, v: i64) -> Result<u128, E> {
            u128::try_from(v).map_err(|_| E::custom("negative literal for unsigned field"))
        }
        fn visit_u128<E: de::Error>(self, v: u128) -> Result<u128, E> {
            Ok(v)
        }
        fn visit_i128<E: de::Error>(self, v: i128) -> Result<u128, E> {
            u128::try_from(v).map_err(|_| E::custom("negative literal for unsigned field"))
        }
        fn visit_str<E: de::Error>(self, s: &str) -> Result<u128, E> {
            s.parse::<u128>()
                .map_err(|_| E::custom("invalid u128 decimal string literal"))
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<u128, D::Error> {
        if d.is_human_readable() {
            d.deserialize_any(WideU128)
        } else {
            d.deserialize_u128(WideU128)
        }
    }
}

/// SMT-level formula (what solvers receive).
///
/// Formulas are backend-agnostic logical expressions that trust-router
/// encodes into solver-specific representations (ay, trust-wp, ty).
///
/// # Examples
///
/// ```
/// use trust_ir_contract::{Formula, Sort};
///
/// // Boolean literal
/// let f = Formula::Bool(true);
///
/// // Integer variable
/// let x = Formula::Var("x".into(), Sort::Int);
///
/// // Comparison: x > 0
/// let gt = Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0)));
///
/// // Conjunction: x > 0 AND x < 10
/// let range = Formula::And(vec![
///     Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0))),
///     Formula::Lt(Box::new(x), Box::new(Formula::Int(10))),
/// ]);
///
/// // Implication: a => b
/// let a = Formula::Var("a".into(), Sort::Bool);
/// let b = Formula::Var("b".into(), Sort::Bool);
/// let imp = Formula::Implies(Box::new(a), Box::new(b));
///
/// // Negation
/// let neg = Formula::Not(Box::new(Formula::Bool(false)));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Formula {
    // Literals
    Bool(bool),
    Int(#[serde(with = "wide_i128")] i128),
    UInt(#[serde(with = "wide_u128")] u128),
    BitVec {
        #[serde(with = "wide_i128")]
        value: i128,
        width: u32,
    },

    // Variables
    Var(String, Sort),
    // Interned variable name variant for reduced heap allocation.
    // SymVar(Symbol, Sort) is semantically identical to Var(String, Sort)
    // but uses a Copy, 4-byte Symbol instead of a heap-allocated String.
    SymVar(crate::Symbol, Sort),

    // Boolean connectives
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),

    // Comparisons
    Eq(Box<Formula>, Box<Formula>),
    Lt(Box<Formula>, Box<Formula>),
    Le(Box<Formula>, Box<Formula>),
    Gt(Box<Formula>, Box<Formula>),
    Ge(Box<Formula>, Box<Formula>),

    // Integer arithmetic (mathematical integers, unbounded)
    Add(Box<Formula>, Box<Formula>),
    Sub(Box<Formula>, Box<Formula>),
    Mul(Box<Formula>, Box<Formula>),
    Div(Box<Formula>, Box<Formula>),
    Rem(Box<Formula>, Box<Formula>),
    Neg(Box<Formula>),

    // Bitvector arithmetic (fixed-width, machine semantics)
    BvAdd(Box<Formula>, Box<Formula>, u32),
    BvSub(Box<Formula>, Box<Formula>, u32),
    BvMul(Box<Formula>, Box<Formula>, u32),
    BvUDiv(Box<Formula>, Box<Formula>, u32),
    BvSDiv(Box<Formula>, Box<Formula>, u32),
    BvURem(Box<Formula>, Box<Formula>, u32),
    BvSRem(Box<Formula>, Box<Formula>, u32),
    BvAnd(Box<Formula>, Box<Formula>, u32),
    BvOr(Box<Formula>, Box<Formula>, u32),
    BvXor(Box<Formula>, Box<Formula>, u32),
    BvNot(Box<Formula>, u32),
    BvShl(Box<Formula>, Box<Formula>, u32),
    BvLShr(Box<Formula>, Box<Formula>, u32),
    BvAShr(Box<Formula>, Box<Formula>, u32),

    // Bitvector comparisons
    BvULt(Box<Formula>, Box<Formula>, u32),
    BvULe(Box<Formula>, Box<Formula>, u32),
    BvSLt(Box<Formula>, Box<Formula>, u32),
    BvSLe(Box<Formula>, Box<Formula>, u32),

    // Bitvector conversions
    BvToInt(Box<Formula>, u32, bool),
    IntToBv(Box<Formula>, u32),
    BvExtract {
        inner: Box<Formula>,
        high: u32,
        low: u32,
    },
    BvConcat(Box<Formula>, Box<Formula>),
    BvZeroExt(Box<Formula>, u32),
    BvSignExt(Box<Formula>, u32),

    // ── IEEE-754 floating point (SMT-LIB FloatingPoint theory) ──────────────
    // Float values carry their format `{ eb, sb }` on literals and bit-reinterp
    // nodes so the sort is recoverable without context; arithmetic nodes recover
    // their format from an operand. The leading `Box<Formula>` of the rounding
    // ops is a `FpRoundingMode` term. Lowered by `to_smtlib` to `fp.*` operators;
    // the backend bit-blasts the FloatingPoint theory to `QF_BV`.
    /// IEEE-754 literal from a raw bit pattern (`((_ to_fp eb sb) (_ bvBITS eb+sb))`).
    FpConst {
        #[serde(with = "wide_u128")]
        bits: u128,
        eb: u32,
        sb: u32,
    },
    /// Not-a-number (`(_ NaN eb sb)`).
    FpNaN {
        eb: u32,
        sb: u32,
    },
    /// Signed infinity (`(_ +oo eb sb)` / `(_ -oo eb sb)`).
    FpInf {
        neg: bool,
        eb: u32,
        sb: u32,
    },
    /// Signed zero (`(_ +zero eb sb)` / `(_ -zero eb sb)`).
    FpZero {
        neg: bool,
        eb: u32,
        sb: u32,
    },
    /// A `RoundingMode` literal.
    FpRoundingMode(RoundingMode),

    // Arithmetic with an explicit rounding-mode operand (first child).
    FpAdd(Box<Formula>, Box<Formula>, Box<Formula>),
    FpSub(Box<Formula>, Box<Formula>, Box<Formula>),
    FpMul(Box<Formula>, Box<Formula>, Box<Formula>),
    FpDiv(Box<Formula>, Box<Formula>, Box<Formula>),
    FpFma(Box<Formula>, Box<Formula>, Box<Formula>, Box<Formula>),
    FpSqrt(Box<Formula>, Box<Formula>),
    // Arithmetic that takes no rounding mode (exact in IEEE-754).
    FpRem(Box<Formula>, Box<Formula>),
    FpNeg(Box<Formula>),
    FpAbs(Box<Formula>),
    FpMin(Box<Formula>, Box<Formula>),
    FpMax(Box<Formula>, Box<Formula>),

    // Comparisons (result sort Bool). `FpEq` is IEEE equality (`NaN != NaN`,
    // `+0 == -0`), distinct from structural `Eq`.
    FpEq(Box<Formula>, Box<Formula>),
    FpLt(Box<Formula>, Box<Formula>),
    FpLe(Box<Formula>, Box<Formula>),
    FpGt(Box<Formula>, Box<Formula>),
    FpGe(Box<Formula>, Box<Formula>),

    // Classification predicates (result sort Bool).
    FpIsNaN(Box<Formula>),
    FpIsInfinite(Box<Formula>),
    FpIsZero(Box<Formula>),
    FpIsNormal(Box<Formula>),
    FpIsSubnormal(Box<Formula>),
    FpIsNegative(Box<Formula>),
    FpIsPositive(Box<Formula>),

    /// Reinterpret a `BitVec(eb+sb)` term's bits as an IEEE-754 float
    /// (`((_ to_fp eb sb) <bv>)`). The bridge between the bitvector modelling of
    /// float locals and real FP semantics.
    FpFromBits {
        bits: Box<Formula>,
        eb: u32,
        sb: u32,
    },

    /// Convert an IEEE-754 float to a SIGNED two's-complement integer of
    /// `width` bits, rounding toward the mode's direction.
    ///
    /// TOTAL, with the AArch64/Rust saturating reading — this is deliberately
    /// NOT SMT-LIB's `fp.to_sbv`, which is UNSPECIFIED for NaN and out-of-range
    /// inputs: NaN converts to 0, and out-of-range values clamp to the type's
    /// minimum/maximum. `to_smtlib` therefore emits the GUARDED expansion
    /// (`ite (fp.isNaN ..) 0 (ite (fp.geq ..) MAX ..)`) around `fp.to_sbv`,
    /// never the bare unspecified operator. A consumer that cannot honour the
    /// total reading must refuse the node, not approximate it.
    FpToSbv {
        rm: Box<Formula>,
        value: Box<Formula>,
        /// Result bitvector width.
        width: u32,
        /// The OPERAND's format, carried so the guarded lowering can build its
        /// range bounds in the right sort (SMT-LIB has no sort inference that
        /// would recover it from the term).
        eb: u32,
        sb: u32,
    },

    /// Unsigned counterpart of [`Formula::FpToSbv`]: NaN -> 0, negative values
    /// clamp to 0, overflow clamps to the maximum. Same guarded lowering.
    FpToUbv {
        rm: Box<Formula>,
        value: Box<Formula>,
        /// Result bitvector width.
        width: u32,
        /// The OPERAND's format; see [`Formula::FpToSbv`].
        eb: u32,
        sb: u32,
    },

    /// Convert a SIGNED two's-complement bitvector to an IEEE-754 float
    /// (`((_ to_fp eb sb) rm <bv>)`) — fully specified by SMT-LIB.
    FpFromSbv {
        rm: Box<Formula>,
        value: Box<Formula>,
        eb: u32,
        sb: u32,
    },

    /// Unsigned counterpart (`((_ to_fp_unsigned eb sb) rm <bv>)`).
    FpFromUbv {
        rm: Box<Formula>,
        value: Box<Formula>,
        eb: u32,
        sb: u32,
    },

    /// Convert between IEEE-754 formats (`((_ to_fp eb sb) rm <fp>)`) — FCVT.
    /// Fully specified by SMT-LIB: NaN propagates, overflow goes to infinity
    /// under the rounding mode.
    FpConvert {
        rm: Box<Formula>,
        value: Box<Formula>,
        eb: u32,
        sb: u32,
    },

    /// Reinterpret an IEEE-754 float term's bits as a `BitVec(eb+sb)`
    /// (`(fp.to_ieee_bv <fp>)`) — the exact inverse of [`Formula::FpFromBits`].
    /// The inner operand is `Float { eb, sb }`-sorted; the result sort is
    /// `BitVec(eb + sb)`, with the width recovered from the inner's format (the
    /// result width of `fp.to_ieee_bv` is inferred from the operand's FP sort, so
    /// no width index is carried on the node). This is the missing FP -> BV half:
    /// the machine register file is BV-typed, so an `fp.*` result must be pushed
    /// back to bits before it can be stored to a float local. The concrete solver
    /// lowering (and its bijection axioms against `to_fp`) is applied downstream
    /// in the `trust-types` ay bridge; the reference interpreter here is
    /// fail-closed on this node.
    FpToIeeeBv(Box<Formula>),

    // Conditional
    Ite(Box<Formula>, Box<Formula>, Box<Formula>),

    // Quantifiers
    // Bindings use interned Symbol instead of heap-allocated String.
    Forall(Vec<(crate::Symbol, Sort)>, Box<Formula>),
    Exists(Vec<(crate::Symbol, Sort)>, Box<Formula>),

    // Arrays
    Select(Box<Formula>, Box<Formula>),
    Store(Box<Formula>, Box<Formula>, Box<Formula>),

    // safe-api: Uninterpreted predicate application (SAFE_API.md §3).
    // Opaque to the solver: no axioms, no definition unless an explicit `Iff`
    // equation is asserted in scope. `name` is drawn from a closed, reviewed
    // per-category vocabulary (`pred_vocab::PRED_VOCAB`); args are sorted terms;
    // the result sort is always `Bool`. Lowers to a `(declare-fun name (..) Bool)`
    // + application (EUF). This is the honest substrate for capability safety
    // predicates (e.g. `dir_open(d)`): an opaque `Pred` can only become true at a
    // use site via an in-scope hypothesis, which can come only from a proved
    // constructor postcondition — the solver cannot invent it.
    Pred(crate::Symbol, Vec<Formula>),

    // ── Algebraic-datatype terms (Lever A) ──────────────────────────────────
    // These make a datatype equation (e.g. `Sort(succ l) = Sort(succ l)`)
    // WRITABLE as a Formula. `Sort::Datatype` can DECLARE an ADT to the solver,
    // but before these nodes no term could REFERENCE its constructors. They
    // lower faithfully: to genuine SMT-LIB datatype terms on the text path
    // (`to_smtlib`) and to ay's `DatatypeConstructor`/`Selector`/`Tester` Expr
    // nodes on the in-process path (the trust-types `ay_bridge`).
    //
    // SOUNDNESS: a datatype term asserts no fact on its own. It only references
    // the constructor/selector/tester of an already-declared datatype, whose
    // axioms are the standard, sound datatype theory the backend supplies (see
    // `sort.rs` `Sort::Datatype` note). A fresh datatype-sorted constant is
    // unconstrained (SAT), so these can never manufacture a false PROVE.
    /// Datatype constructor application `(ctor args…)`. `sort` is the datatype's
    /// own `Sort::Datatype` (carries the datatype name + full constructor
    /// structure — the result sort); `ctor` names the constructor; `args` are
    /// the field terms. A nullary constructor (`args` empty) is a datatype
    /// constant.
    Ctor {
        ctor: String,
        args: Vec<Formula>,
        sort: Sort,
    },
    /// Datatype field selector `(field arg)`. `arg` is a datatype-sorted term;
    /// `datatype` is its datatype (sort) name; `field` is the selector/field
    /// name; `field_sort` is the selected field's sort (the result sort).
    Sel {
        datatype: String,
        field: String,
        field_sort: Sort,
        arg: Box<Formula>,
    },
    /// Datatype constructor tester `((_ is ctor) arg)` — result sort `Bool`.
    /// `arg` is a datatype-sorted term; `datatype` is its datatype (sort) name;
    /// `ctor` is the constructor being tested.
    IsCtor {
        datatype: String,
        ctor: String,
        arg: Box<Formula>,
    },

    /// Uninterpreted FUNCTION application `(func args…)` — the function-symbol
    /// twin of [`Formula::Pred`] (which is the `Bool`-result special case).
    /// `sort` is the application's RESULT sort. Opaque to the solver: no
    /// axioms, no definition; on the text path it lowers to a bare EUF
    /// application whose `(declare-fun func (<arg-sorts>) <sort>)` must be
    /// emitted by the backend's declaration collector.
    ///
    /// Introduced for function-vs-function postconditions (the
    /// `model = reference` shape of the recursive-datatype induction lanes):
    /// an `Ensures` clause `Eq(_0, FnApp(reference, [fuel, e]))` names a second
    /// function symbol whose DEFINITION travels separately (the lane's
    /// definitional VCs), so a consumer can reconstruct and discharge the
    /// two-function goal. SOUNDNESS: like `Pred`, a bare application asserts
    /// nothing on its own — it can only be constrained by in-scope equations.
    FnApp {
        func: String,
        args: Vec<Formula>,
        sort: Sort,
    },
}

impl Formula {
    /// Collect references to all direct sub-formulas.
    #[must_use]
    pub fn children(&self) -> Vec<&Formula> {
        match self {
            // Leaves
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..) => {
                vec![]
            }

            // Unary
            Formula::Not(a) | Formula::Neg(a) => vec![a],
            Formula::BvNot(a, _)
            | Formula::BvToInt(a, _, _)
            | Formula::IntToBv(a, _)
            | Formula::BvZeroExt(a, _)
            | Formula::BvSignExt(a, _) => vec![a],
            Formula::BvExtract { inner, .. } => vec![inner],

            // N-ary
            Formula::And(terms) | Formula::Or(terms) => terms.iter().collect(),

            // Binary
            Formula::Implies(a, b)
            | Formula::Eq(a, b)
            | Formula::Lt(a, b)
            | Formula::Le(a, b)
            | Formula::Gt(a, b)
            | Formula::Ge(a, b)
            | Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b)
            | Formula::Div(a, b)
            | Formula::Rem(a, b)
            | Formula::BvConcat(a, b)
            | Formula::Select(a, b) => vec![a, b],

            // Binary with width
            Formula::BvAdd(a, b, _)
            | Formula::BvSub(a, b, _)
            | Formula::BvMul(a, b, _)
            | Formula::BvUDiv(a, b, _)
            | Formula::BvSDiv(a, b, _)
            | Formula::BvURem(a, b, _)
            | Formula::BvSRem(a, b, _)
            | Formula::BvAnd(a, b, _)
            | Formula::BvOr(a, b, _)
            | Formula::BvXor(a, b, _)
            | Formula::BvShl(a, b, _)
            | Formula::BvLShr(a, b, _)
            | Formula::BvAShr(a, b, _)
            | Formula::BvULt(a, b, _)
            | Formula::BvULe(a, b, _)
            | Formula::BvSLt(a, b, _)
            | Formula::BvSLe(a, b, _) => vec![a, b],

            // Ternary
            Formula::Ite(a, b, c) | Formula::Store(a, b, c) => vec![a, b, c],

            // Floating point — leaves
            Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_) => vec![],
            // Floating point — unary
            Formula::FpNeg(a)
            | Formula::FpAbs(a)
            | Formula::FpIsNaN(a)
            | Formula::FpIsInfinite(a)
            | Formula::FpIsZero(a)
            | Formula::FpIsNormal(a)
            | Formula::FpIsSubnormal(a)
            | Formula::FpIsNegative(a)
            | Formula::FpIsPositive(a) => vec![a],
            Formula::FpFromBits { bits, .. } => vec![bits],
            Formula::FpToIeeeBv(a) => vec![a],
            Formula::FpToSbv { rm, value, .. }
            | Formula::FpToUbv { rm, value, .. }
            | Formula::FpFromSbv { rm, value, .. }
            | Formula::FpFromUbv { rm, value, .. }
            | Formula::FpConvert { rm, value, .. } => vec![rm, value],
            // Floating point — binary
            Formula::FpRem(a, b)
            | Formula::FpMin(a, b)
            | Formula::FpMax(a, b)
            | Formula::FpEq(a, b)
            | Formula::FpLt(a, b)
            | Formula::FpLe(a, b)
            | Formula::FpGt(a, b)
            | Formula::FpGe(a, b)
            | Formula::FpSqrt(a, b) => vec![a, b],
            // Floating point — ternary (rounding mode + two operands)
            Formula::FpAdd(a, b, c)
            | Formula::FpSub(a, b, c)
            | Formula::FpMul(a, b, c)
            | Formula::FpDiv(a, b, c) => vec![a, b, c],
            // Floating point — quaternary (rounding mode + three operands)
            Formula::FpFma(a, b, c, d) => vec![a, b, c, d],

            // Quantifiers (body only; bindings are not sub-formulas)
            Formula::Forall(_, body) | Formula::Exists(_, body) => vec![body],

            // Uninterpreted predicate: the argument terms are the sub-formulas.
            Formula::Pred(_, args) => args.iter().collect(),

            // Datatype terms: the field/operand terms are the sub-formulas.
            Formula::Ctor { args, .. } => args.iter().collect(),
            Formula::Sel { arg, .. } | Formula::IsCtor { arg, .. } => vec![arg],

            // Uninterpreted function application: the argument terms.
            Formula::FnApp { args, .. } => args.iter().collect(),
        }
    }

    /// Map over all direct sub-formulas, replacing each via `f`.
    /// Non-formula data (widths, sorts, bindings) is preserved.
    #[must_use]
    pub fn map_children(self, f: &mut impl FnMut(Formula) -> Formula) -> Formula {
        match self {
            // Leaves
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..) => self,

            // Unary
            Formula::Not(a) => Formula::Not(Box::new(f(*a))),
            Formula::Neg(a) => Formula::Neg(Box::new(f(*a))),
            Formula::BvNot(a, w) => Formula::BvNot(Box::new(f(*a)), w),
            Formula::BvToInt(a, w, s) => Formula::BvToInt(Box::new(f(*a)), w, s),
            Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(f(*a)), w),
            Formula::BvZeroExt(a, bits) => Formula::BvZeroExt(Box::new(f(*a)), bits),
            Formula::BvSignExt(a, bits) => Formula::BvSignExt(Box::new(f(*a)), bits),
            Formula::BvExtract { inner, high, low } => Formula::BvExtract {
                inner: Box::new(f(*inner)),
                high,
                low,
            },

            // N-ary
            Formula::And(terms) => Formula::And(terms.into_iter().map(&mut *f).collect()),
            Formula::Or(terms) => Formula::Or(terms.into_iter().map(&mut *f).collect()),

            // Binary
            Formula::Implies(a, b) => Formula::Implies(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Eq(a, b) => Formula::Eq(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Lt(a, b) => Formula::Lt(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Le(a, b) => Formula::Le(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Gt(a, b) => Formula::Gt(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Ge(a, b) => Formula::Ge(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Add(a, b) => Formula::Add(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Sub(a, b) => Formula::Sub(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Mul(a, b) => Formula::Mul(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Div(a, b) => Formula::Div(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Rem(a, b) => Formula::Rem(Box::new(f(*a)), Box::new(f(*b))),
            Formula::BvConcat(a, b) => Formula::BvConcat(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Select(a, b) => Formula::Select(Box::new(f(*a)), Box::new(f(*b))),

            // Binary with width
            Formula::BvAdd(a, b, w) => Formula::BvAdd(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSub(a, b, w) => Formula::BvSub(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvMul(a, b, w) => Formula::BvMul(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvUDiv(a, b, w) => Formula::BvUDiv(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSDiv(a, b, w) => Formula::BvSDiv(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvURem(a, b, w) => Formula::BvURem(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSRem(a, b, w) => Formula::BvSRem(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvAnd(a, b, w) => Formula::BvAnd(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvOr(a, b, w) => Formula::BvOr(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvXor(a, b, w) => Formula::BvXor(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvShl(a, b, w) => Formula::BvShl(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvLShr(a, b, w) => Formula::BvLShr(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvAShr(a, b, w) => Formula::BvAShr(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvULt(a, b, w) => Formula::BvULt(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvULe(a, b, w) => Formula::BvULe(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSLt(a, b, w) => Formula::BvSLt(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSLe(a, b, w) => Formula::BvSLe(Box::new(f(*a)), Box::new(f(*b)), w),

            // Ternary
            Formula::Ite(a, b, c) => {
                Formula::Ite(Box::new(f(*a)), Box::new(f(*b)), Box::new(f(*c)))
            }
            Formula::Store(a, b, c) => {
                Formula::Store(Box::new(f(*a)), Box::new(f(*b)), Box::new(f(*c)))
            }

            // Floating point — leaves (no sub-formulas to map)
            Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_) => self,
            // Floating point — unary
            Formula::FpNeg(a) => Formula::FpNeg(Box::new(f(*a))),
            Formula::FpAbs(a) => Formula::FpAbs(Box::new(f(*a))),
            Formula::FpIsNaN(a) => Formula::FpIsNaN(Box::new(f(*a))),
            Formula::FpIsInfinite(a) => Formula::FpIsInfinite(Box::new(f(*a))),
            Formula::FpIsZero(a) => Formula::FpIsZero(Box::new(f(*a))),
            Formula::FpIsNormal(a) => Formula::FpIsNormal(Box::new(f(*a))),
            Formula::FpIsSubnormal(a) => Formula::FpIsSubnormal(Box::new(f(*a))),
            Formula::FpIsNegative(a) => Formula::FpIsNegative(Box::new(f(*a))),
            Formula::FpIsPositive(a) => Formula::FpIsPositive(Box::new(f(*a))),
            Formula::FpFromBits { bits, eb, sb } => Formula::FpFromBits {
                bits: Box::new(f(*bits)),
                eb,
                sb,
            },
            Formula::FpToIeeeBv(a) => Formula::FpToIeeeBv(Box::new(f(*a))),
            Formula::FpToSbv {
                rm,
                value,
                width,
                eb,
                sb,
            } => Formula::FpToSbv {
                rm: Box::new(f(*rm)),
                value: Box::new(f(*value)),
                width,
                eb,
                sb,
            },
            Formula::FpToUbv {
                rm,
                value,
                width,
                eb,
                sb,
            } => Formula::FpToUbv {
                rm: Box::new(f(*rm)),
                value: Box::new(f(*value)),
                width,
                eb,
                sb,
            },
            Formula::FpFromSbv { rm, value, eb, sb } => Formula::FpFromSbv {
                rm: Box::new(f(*rm)),
                value: Box::new(f(*value)),
                eb,
                sb,
            },
            Formula::FpFromUbv { rm, value, eb, sb } => Formula::FpFromUbv {
                rm: Box::new(f(*rm)),
                value: Box::new(f(*value)),
                eb,
                sb,
            },
            Formula::FpConvert { rm, value, eb, sb } => Formula::FpConvert {
                rm: Box::new(f(*rm)),
                value: Box::new(f(*value)),
                eb,
                sb,
            },
            // Floating point — binary
            Formula::FpRem(a, b) => Formula::FpRem(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpMin(a, b) => Formula::FpMin(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpMax(a, b) => Formula::FpMax(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpEq(a, b) => Formula::FpEq(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpLt(a, b) => Formula::FpLt(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpLe(a, b) => Formula::FpLe(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpGt(a, b) => Formula::FpGt(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpGe(a, b) => Formula::FpGe(Box::new(f(*a)), Box::new(f(*b))),
            Formula::FpSqrt(rm, a) => Formula::FpSqrt(Box::new(f(*rm)), Box::new(f(*a))),
            // Floating point — ternary
            Formula::FpAdd(rm, a, b) => {
                Formula::FpAdd(Box::new(f(*rm)), Box::new(f(*a)), Box::new(f(*b)))
            }
            Formula::FpSub(rm, a, b) => {
                Formula::FpSub(Box::new(f(*rm)), Box::new(f(*a)), Box::new(f(*b)))
            }
            Formula::FpMul(rm, a, b) => {
                Formula::FpMul(Box::new(f(*rm)), Box::new(f(*a)), Box::new(f(*b)))
            }
            Formula::FpDiv(rm, a, b) => {
                Formula::FpDiv(Box::new(f(*rm)), Box::new(f(*a)), Box::new(f(*b)))
            }
            // Floating point — quaternary
            Formula::FpFma(rm, a, b, c) => Formula::FpFma(
                Box::new(f(*rm)),
                Box::new(f(*a)),
                Box::new(f(*b)),
                Box::new(f(*c)),
            ),

            // Quantifiers
            Formula::Forall(bindings, body) => Formula::Forall(bindings, Box::new(f(*body))),
            Formula::Exists(bindings, body) => Formula::Exists(bindings, Box::new(f(*body))),

            // Uninterpreted predicate: map each argument term.
            Formula::Pred(name, args) => {
                Formula::Pred(name, args.into_iter().map(&mut *f).collect())
            }

            // Datatype terms: map the field/operand terms; preserve names/sorts.
            Formula::Ctor { ctor, args, sort } => Formula::Ctor {
                ctor,
                args: args.into_iter().map(&mut *f).collect(),
                sort,
            },
            Formula::Sel {
                datatype,
                field,
                field_sort,
                arg,
            } => Formula::Sel {
                datatype,
                field,
                field_sort,
                arg: Box::new(f(*arg)),
            },
            Formula::IsCtor {
                datatype,
                ctor,
                arg,
            } => Formula::IsCtor {
                datatype,
                ctor,
                arg: Box::new(f(*arg)),
            },

            // Uninterpreted function application: map the argument terms.
            Formula::FnApp { func, args, sort } => Formula::FnApp {
                func,
                args: args.into_iter().map(&mut *f).collect(),
                sort,
            },
        }
    }

    /// Recursively visit all sub-formulas depth-first (pre-order).
    pub fn visit(&self, f: &mut impl FnMut(&Formula)) {
        f(self);
        for child in self.children() {
            child.visit(f);
        }
    }

    /// Recursively map all sub-formulas bottom-up (post-order).
    /// Children are transformed first, then `f` is applied to the result.
    #[must_use]
    pub fn map(self, f: &mut impl FnMut(Formula) -> Formula) -> Formula {
        let mapped = self.map_children(&mut |child| child.map(f));
        f(mapped)
    }

    /// Collect all free variable names in this formula.
    /// Variables bound by Forall/Exists are excluded.
    #[must_use]
    pub fn free_variables(&self) -> FxHashSet<String> {
        let mut free = FxHashSet::default();
        self.free_variables_inner(&mut free, &FxHashSet::default());
        free
    }

    fn free_variables_inner(&self, free: &mut FxHashSet<String>, bound: &FxHashSet<String>) {
        match self {
            Formula::Var(name, _) => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }
            // SymVar uses Symbol; resolve to string for free variable tracking.
            Formula::SymVar(sym, _) => {
                let name = sym.as_str().to_string();
                if !bound.contains(&name) {
                    free.insert(name);
                }
            }
            // Quantifier bindings use Symbol; convert to String for tracking.
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let mut new_bound = bound.clone();
                for (sym, _) in bindings {
                    new_bound.insert(sym.as_str().to_string());
                }
                body.free_variables_inner(free, &new_bound);
            }
            _ => {
                for child in self.children() {
                    child.free_variables_inner(free, bound);
                }
            }
        }
    }

    /// Check if this formula contains bitvector operations or types.
    #[must_use]
    pub fn has_bitvectors(&self) -> bool {
        let mut found = false;
        self.visit(&mut |f| {
            if found {
                return;
            }
            match f {
                Formula::BitVec { .. }
                | Formula::BvAdd(..)
                | Formula::BvSub(..)
                | Formula::BvMul(..)
                | Formula::BvUDiv(..)
                | Formula::BvSDiv(..)
                | Formula::BvURem(..)
                | Formula::BvSRem(..)
                | Formula::BvAnd(..)
                | Formula::BvOr(..)
                | Formula::BvXor(..)
                | Formula::BvNot(..)
                | Formula::BvShl(..)
                | Formula::BvLShr(..)
                | Formula::BvAShr(..)
                | Formula::BvULt(..)
                | Formula::BvULe(..)
                | Formula::BvSLt(..)
                | Formula::BvSLe(..)
                | Formula::BvToInt(..)
                | Formula::IntToBv(..)
                | Formula::BvExtract { .. }
                | Formula::BvConcat(..)
                | Formula::BvZeroExt(..)
                | Formula::BvSignExt(..)
                // FP -> BV reinterpret: the result is a bitvector term.
                | Formula::FpToIeeeBv(..) => found = true,
                Formula::Var(_, Sort::BitVec(_)) | Formula::SymVar(_, Sort::BitVec(_)) => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    /// Check if this formula contains array theory operations (Select/Store)
    /// or array-typed variables.
    ///
    /// Cheap structural check for trust_wp translatability.
    #[must_use]
    pub fn has_arrays(&self) -> bool {
        let mut found = false;
        self.visit(&mut |f| {
            if found {
                return;
            }
            match f {
                Formula::Select(..) | Formula::Store(..) => found = true,
                Formula::Var(_, Sort::Array(_, _)) | Formula::SymVar(_, Sort::Array(_, _)) => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    /// Check if this formula contains integer literals outside the i64 range.
    ///
    /// trust-wp-core uses i64 for integer literals. Formulas with
    /// Int/UInt values that exceed i64 range cannot be translated to PureExpr.
    #[must_use]
    pub fn has_large_integers(&self) -> bool {
        let mut found = false;
        self.visit(&mut |f| {
            if found {
                return;
            }
            match f {
                Formula::Int(n) if i64::try_from(*n).is_err() => {
                    found = true;
                }
                Formula::UInt(n) if i64::try_from(*n).is_err() => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    // Convenience constructors that produce SymVar (interned) instead
    // of Var (heap-allocated String). New code should prefer these over raw
    // Formula::Var(...) to reduce per-variable heap allocations.

    /// Create a variable formula using an interned symbol.
    ///
    /// Create a variable formula from a string name.
    ///
    /// Equivalent to `Formula::Var(name.to_string(), sort)`.
    /// For interned variables, use `var_sym()` with a `Symbol`.
    #[must_use]
    pub fn var(name: &str, sort: Sort) -> Formula {
        Formula::Var(name.to_string(), sort)
    }

    /// Create a variable formula from an owned String.
    ///
    /// Takes ownership of the String to avoid an extra clone when the caller
    /// already has an owned String (e.g. from `format!`).
    #[must_use]
    pub fn var_owned(name: String, sort: Sort) -> Formula {
        Formula::Var(name, sort)
    }

    /// Create a variable formula from an already-interned Symbol.
    #[must_use]
    pub fn var_sym(sym: crate::Symbol, sort: Sort) -> Formula {
        Formula::SymVar(sym, sort)
    }

    /// Return the variable name if this formula is a variable (Var or SymVar).
    ///
    /// Returns `None` for non-variable formulas. The returned `&str` has
    /// `'static` lifetime for SymVar (interned) and borrows `self` for Var.
    #[must_use]
    pub fn var_name(&self) -> Option<&str> {
        match self {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(sym, _) => Some(sym.as_str()),
            _ => None,
        }
    }

    /// Return the sort if this formula is a variable (Var or SymVar).
    #[must_use]
    pub fn var_sort(&self) -> Option<&Sort> {
        match self {
            Formula::Var(_, sort) | Formula::SymVar(_, sort) => Some(sort),
            _ => None,
        }
    }

    // Convenience constructors for quantifiers with interned bindings.

    /// Create a universally quantified formula with interned bindings.
    ///
    /// Accepts `&str` binding names and interns them automatically.
    #[must_use]
    pub fn forall(bindings: &[(&str, Sort)], body: Formula) -> Formula {
        let sym_bindings: Vec<(crate::Symbol, Sort)> = bindings
            .iter()
            .map(|(name, sort)| (crate::Symbol::intern(name), sort.clone()))
            .collect();
        Formula::Forall(sym_bindings, Box::new(body))
    }

    /// Create an existentially quantified formula with interned bindings.
    ///
    /// Accepts `&str` binding names and interns them automatically.
    #[must_use]
    pub fn exists(bindings: &[(&str, Sort)], body: Formula) -> Formula {
        let sym_bindings: Vec<(crate::Symbol, Sort)> = bindings
            .iter()
            .map(|(name, sort)| (crate::Symbol::intern(name), sort.clone()))
            .collect();
        Formula::Exists(sym_bindings, Box::new(body))
    }

    /// Rename a variable throughout the formula.
    #[must_use]
    pub fn rename_var(&self, from: &str, to: &str) -> Formula {
        match self {
            Formula::Var(name, sort) if name == from => Formula::Var(to.to_string(), sort.clone()),
            // SymVar rename resolves symbol, produces new SymVar.
            Formula::SymVar(sym, sort) if sym.as_str() == from => {
                Formula::SymVar(crate::Symbol::intern(to), sort.clone())
            }
            _ => self
                .clone()
                .map_children(&mut |child| child.rename_var(from, to)),
        }
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 text serialization (moved from trust-types' formula/smtlib.rs).
// ---------------------------------------------------------------------------

/// `2^width` as an exact decimal string, overflow-free for any width. `1u128 <<
/// width` is undefined behaviour for `width >= 128` (the i128/u128 case): in
/// release builds it masks the shift amount and yields a wrong value (`1u128 <<
/// 128 == 1`), in debug it panics. Used to build the signed `BvToInt` correction
/// term, where a wrong `2^width` would mistranslate negative values and could
/// surface as a false-PROVE.
fn pow2_decimal(width: u32) -> String {
    let mut digits: Vec<u8> = vec![1]; // little-endian decimal digits of 2^0
    for _ in 0..width {
        let mut carry = 0u8;
        for d in digits.iter_mut() {
            let v = *d * 2 + carry;
            *d = v % 10;
            carry = v / 10;
        }
        while carry > 0 {
            digits.push(carry % 10);
            carry /= 10;
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

/// Escape an SMT-LIB symbol when it is not a valid simple symbol.
#[must_use]
pub fn escape_smtlib_symbol(name: &str) -> String {
    if is_simple_smtlib_symbol(name) {
        name.to_string()
    } else {
        let escaped = name.replace('\\', "\\\\").replace('|', "\\|");
        format!("|{escaped}|")
    }
}

fn is_simple_smtlib_symbol(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    if name.parse::<i128>().is_ok() || name.parse::<u128>().is_ok() {
        return false;
    }
    name.chars().all(|ch| {
        ch.is_ascii_alphanumeric()
            || matches!(
                ch,
                '~' | '!'
                    | '@'
                    | '$'
                    | '%'
                    | '^'
                    | '&'
                    | '*'
                    | '_'
                    | '-'
                    | '+'
                    | '='
                    | '<'
                    | '>'
                    | '.'
                    | '?'
                    | '/'
            )
    })
}

impl Formula {
    /// Convert this Formula to its SMT-LIB2 text representation.
    ///
    /// This is the canonical serializer used by all crates (trust-router,
    /// trust_vcgen, trust-cegar). Covers every Formula variant.
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        match self {
            // Literals
            Formula::Bool(true) => "true".to_string(),
            Formula::Bool(false) => "false".to_string(),
            Formula::UInt(n) => n.to_string(),
            Formula::Int(n) => {
                if *n < 0 {
                    let abs = n.unsigned_abs();
                    format!("(- {abs})")
                } else {
                    n.to_string()
                }
            }
            Formula::BitVec { value, width } => {
                if *value >= 0 {
                    format!("(_ bv{value} {width})")
                } else {
                    // Use u128 for two's complement to handle width=128 correctly.
                    // i128 mask overflows at width=128; u128::MAX is the correct all-ones mask.
                    let mask: u128 = if *width < 128 {
                        (1u128 << width) - 1
                    } else {
                        u128::MAX
                    };
                    let twos_comp = (*value as u128) & mask;
                    format!("(_ bv{twos_comp} {width})")
                }
            }

            // Variables
            Formula::Var(name, _sort) => escape_smtlib_symbol(name),
            Formula::SymVar(sym, _sort) => escape_smtlib_symbol(sym.as_str()),

            // Boolean connectives
            Formula::Not(inner) => format!("(not {})", inner.to_smtlib()),
            Formula::And(terms) => {
                if terms.is_empty() {
                    "true".to_string()
                } else if terms.len() == 1 {
                    terms[0].to_smtlib()
                } else {
                    let parts: Vec<String> = terms.iter().map(|t| t.to_smtlib()).collect();
                    format!("(and {})", parts.join(" "))
                }
            }
            Formula::Or(terms) => {
                if terms.is_empty() {
                    "false".to_string()
                } else if terms.len() == 1 {
                    terms[0].to_smtlib()
                } else {
                    let parts: Vec<String> = terms.iter().map(|t| t.to_smtlib()).collect();
                    format!("(or {})", parts.join(" "))
                }
            }
            Formula::Implies(a, b) => {
                format!("(=> {} {})", a.to_smtlib(), b.to_smtlib())
            }

            // Comparisons
            Formula::Eq(a, b) => format!("(= {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Lt(a, b) => format!("(< {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Le(a, b) => format!("(<= {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Gt(a, b) => format!("(> {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Ge(a, b) => format!("(>= {} {})", a.to_smtlib(), b.to_smtlib()),

            // Integer arithmetic
            Formula::Add(a, b) => format!("(+ {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Sub(a, b) => format!("(- {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::Mul(a, b) => format!("(* {} {})", a.to_smtlib(), b.to_smtlib()),
            // Rust integer `/` and `%` are TRUNCATED (quotient toward zero; the
            // remainder takes the sign of the dividend). SMT-LIB integer `div`/`mod`
            // are EUCLIDEAN (`mod` is always non-negative; `div` floors toward -inf),
            // which diverges for negative dividends. Lowering `%`/`/` as bare
            // `mod`/`div` proved sign/range properties that real Rust violates — e.g.
            // `#[ensures(result >= 0)] fn f(x:i32)->i32 { x % 256 }` was falsely
            // Proved although `(-1) % 256 == -1`. Encode truncation explicitly. For
            // non-negative operands (all unsigned div/rem) these reduce to plain
            // `div`/`mod`, so the encoding is correct for both signed and unsigned.
            // (Division by zero is governed by a separate div-by-zero VC, so the
            // unconstrained `mod`/`div` value at b==0 is not relied upon here.)
            Formula::Rem(a, b) => {
                let a = a.to_smtlib();
                let b = b.to_smtlib();
                // trem(a,b) = ite(a >= 0, mod(a,b), -mod(-a,b))
                format!("(ite (>= {a} 0) (mod {a} {b}) (- (mod (- {a}) {b})))")
            }
            Formula::Div(a, b) => {
                let a = a.to_smtlib();
                let b = b.to_smtlib();
                // a == b*tdiv + trem, so tdiv = (a - trem)/b is an EXACT division
                // (remainder 0) where Euclidean `div` agrees with truncation.
                let trem = format!("(ite (>= {a} 0) (mod {a} {b}) (- (mod (- {a}) {b})))");
                format!("(div (- {a} {trem}) {b})")
            }
            Formula::Neg(inner) => format!("(- {})", inner.to_smtlib()),

            // Bitvector arithmetic
            Formula::BvAdd(a, b, _) => format!("(bvadd {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSub(a, b, _) => format!("(bvsub {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvMul(a, b, _) => format!("(bvmul {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvUDiv(a, b, _) => format!("(bvudiv {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSDiv(a, b, _) => format!("(bvsdiv {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvURem(a, b, _) => format!("(bvurem {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSRem(a, b, _) => format!("(bvsrem {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvAnd(a, b, _) => format!("(bvand {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvOr(a, b, _) => format!("(bvor {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvXor(a, b, _) => format!("(bvxor {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvNot(inner, _) => format!("(bvnot {})", inner.to_smtlib()),
            Formula::BvShl(a, b, _) => format!("(bvshl {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvLShr(a, b, _) => format!("(bvlshr {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvAShr(a, b, _) => format!("(bvashr {} {})", a.to_smtlib(), b.to_smtlib()),

            // Bitvector comparisons
            Formula::BvULt(a, b, _) => format!("(bvult {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvULe(a, b, _) => format!("(bvule {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSLt(a, b, _) => format!("(bvslt {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvSLe(a, b, _) => format!("(bvsle {} {})", a.to_smtlib(), b.to_smtlib()),

            // Bitvector conversions
            //
            // SMT-LIB FixedSizeBitVectors defines `bv2nat` (unsigned) and lets the
            // caller build signed conversion by subtracting 2^N when the sign bit is
            // set. We emit the SMT-LIB-standard name (`bv2nat`). A legacy spelling
            // (`bv2int`) exists in some non-standard solver dialects, but `ay`
            // recognizes only the standard form.
            Formula::BvToInt(inner, width, signed) => {
                let inner_smt = inner.to_smtlib();
                if *signed {
                    let two_to_width = pow2_decimal(*width);
                    format!(
                        "(ite (bvsge {inner_smt} (_ bv0 {width})) \
                         (bv2nat {inner_smt}) \
                         (- (bv2nat {inner_smt}) {two_to_width}))"
                    )
                } else {
                    format!("(bv2nat {inner_smt})")
                }
            }
            Formula::IntToBv(inner, width) => {
                format!("((_ int2bv {width}) {})", inner.to_smtlib())
            }
            Formula::BvExtract { inner, high, low } => {
                format!("((_ extract {high} {low}) {})", inner.to_smtlib())
            }
            Formula::BvConcat(a, b) => format!("(concat {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::BvZeroExt(inner, bits) => {
                format!("((_ zero_extend {bits}) {})", inner.to_smtlib())
            }
            Formula::BvSignExt(inner, bits) => {
                format!("((_ sign_extend {bits}) {})", inner.to_smtlib())
            }

            // Conditional
            Formula::Ite(cond, then, els) => {
                format!(
                    "(ite {} {} {})",
                    cond.to_smtlib(),
                    then.to_smtlib(),
                    els.to_smtlib()
                )
            }

            // Quantifiers
            Formula::Forall(bindings, body) => {
                let params: Vec<String> = bindings
                    .iter()
                    .map(|(name, sort)| {
                        format!(
                            "({} {})",
                            escape_smtlib_symbol(name.as_str()),
                            sort.to_smtlib()
                        )
                    })
                    .collect();
                format!("(forall ({}) {})", params.join(" "), body.to_smtlib())
            }
            Formula::Exists(bindings, body) => {
                let params: Vec<String> = bindings
                    .iter()
                    .map(|(name, sort)| {
                        format!(
                            "({} {})",
                            escape_smtlib_symbol(name.as_str()),
                            sort.to_smtlib()
                        )
                    })
                    .collect();
                format!("(exists ({}) {})", params.join(" "), body.to_smtlib())
            }

            // Arrays
            Formula::Select(arr, idx) => {
                format!("(select {} {})", arr.to_smtlib(), idx.to_smtlib())
            }
            Formula::Store(arr, idx, val) => {
                format!(
                    "(store {} {} {})",
                    arr.to_smtlib(),
                    idx.to_smtlib(),
                    val.to_smtlib()
                )
            }

            // ── IEEE-754 floating point (SMT-LIB FloatingPoint theory) ──────
            Formula::FpConst { bits, eb, sb } => {
                format!("((_ to_fp {eb} {sb}) (_ bv{bits} {}))", eb + sb)
            }
            Formula::FpNaN { eb, sb } => format!("(_ NaN {eb} {sb})"),
            Formula::FpInf { neg, eb, sb } => {
                if *neg {
                    format!("(_ -oo {eb} {sb})")
                } else {
                    format!("(_ +oo {eb} {sb})")
                }
            }
            Formula::FpZero { neg, eb, sb } => {
                if *neg {
                    format!("(_ -zero {eb} {sb})")
                } else {
                    format!("(_ +zero {eb} {sb})")
                }
            }
            Formula::FpRoundingMode(rm) => rm.to_smtlib().to_string(),
            Formula::FpAdd(rm, a, b) => {
                format!(
                    "(fp.add {} {} {})",
                    rm.to_smtlib(),
                    a.to_smtlib(),
                    b.to_smtlib()
                )
            }
            Formula::FpSub(rm, a, b) => {
                format!(
                    "(fp.sub {} {} {})",
                    rm.to_smtlib(),
                    a.to_smtlib(),
                    b.to_smtlib()
                )
            }
            Formula::FpMul(rm, a, b) => {
                format!(
                    "(fp.mul {} {} {})",
                    rm.to_smtlib(),
                    a.to_smtlib(),
                    b.to_smtlib()
                )
            }
            Formula::FpDiv(rm, a, b) => {
                format!(
                    "(fp.div {} {} {})",
                    rm.to_smtlib(),
                    a.to_smtlib(),
                    b.to_smtlib()
                )
            }
            Formula::FpFma(rm, a, b, c) => format!(
                "(fp.fma {} {} {} {})",
                rm.to_smtlib(),
                a.to_smtlib(),
                b.to_smtlib(),
                c.to_smtlib()
            ),
            Formula::FpSqrt(rm, a) => {
                format!("(fp.sqrt {} {})", rm.to_smtlib(), a.to_smtlib())
            }
            Formula::FpRem(a, b) => format!("(fp.rem {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpNeg(a) => format!("(fp.neg {})", a.to_smtlib()),
            Formula::FpAbs(a) => format!("(fp.abs {})", a.to_smtlib()),
            Formula::FpMin(a, b) => format!("(fp.min {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpMax(a, b) => format!("(fp.max {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpEq(a, b) => format!("(fp.eq {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpLt(a, b) => format!("(fp.lt {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpLe(a, b) => format!("(fp.leq {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpGt(a, b) => format!("(fp.gt {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpGe(a, b) => format!("(fp.geq {} {})", a.to_smtlib(), b.to_smtlib()),
            Formula::FpIsNaN(a) => format!("(fp.isNaN {})", a.to_smtlib()),
            Formula::FpIsInfinite(a) => format!("(fp.isInfinite {})", a.to_smtlib()),
            Formula::FpIsZero(a) => format!("(fp.isZero {})", a.to_smtlib()),
            Formula::FpIsNormal(a) => format!("(fp.isNormal {})", a.to_smtlib()),
            Formula::FpIsSubnormal(a) => format!("(fp.isSubnormal {})", a.to_smtlib()),
            Formula::FpIsNegative(a) => format!("(fp.isNegative {})", a.to_smtlib()),
            Formula::FpIsPositive(a) => format!("(fp.isPositive {})", a.to_smtlib()),
            Formula::FpFromBits { bits, eb, sb } => {
                format!("((_ to_fp {eb} {sb}) {})", bits.to_smtlib())
            }
            // FP -> BV bit reinterpret (inverse of `to_fp` on a bit pattern). The
            // result width is inferred by the solver from the inner FP sort, so no
            // width index is carried. The concrete solver lowering / bijection
            // axioms are applied by the `trust-types` ay bridge downstream.
            Formula::FpToIeeeBv(a) => format!("(fp.to_ieee_bv {})", a.to_smtlib()),
            // The saturating conversions lower to a COMPLETE guarded
            // expansion, never the bare SMT operator: `fp.to_sbv`/`fp.to_ubv`
            // are UNSPECIFIED for NaN and out-of-range inputs, while these
            // nodes are TOTAL with the AArch64 reading (NaN -> 0, out-of-range
            // -> clamp). Emitting the bare operator would let a solver choose
            // arbitrary values exactly where the semantics promise saturation.
            //
            // Bounds are exact: powers of two are representable in any format
            // whose exponent range admits them (f32/f64 do for width <= 64),
            // and each bound is written as `to_fp` of a wider bitvector
            // literal in the operand's own format, which the node carries.
            // Boundary subtlety on the low side: overflow is x <= MIN-1, and
            // in formats too coarse to represent MIN-1 the bound rounds to
            // MIN — where the guard may fire on x == MIN exactly, but the
            // clamp value IS the true conversion there, so the answer is
            // unchanged.
            Formula::FpToSbv {
                rm,
                value,
                width,
                eb,
                sb,
            } => {
                let w = *width;
                let x = value.to_smtlib();
                let rm = rm.to_smtlib();
                // 2^(w-1) as an unsigned (w+1)-bit literal, in the operand's format.
                let pos = format!(
                    "((_ to_fp_unsigned {eb} {sb}) RNE (_ bv{} {}))",
                    1u128 << (w - 1),
                    w + 1
                );
                // -(2^(w-1)) - 1 as a signed (w+2)-bit literal.
                let min_minus_one = (1u128 << (w + 2)) - (1u128 << (w - 1)) - 1;
                let neg = format!("((_ to_fp {eb} {sb}) RNE (_ bv{min_minus_one} {}))", w + 2);
                let max_bv = format!("(_ bv{} {w})", (1u128 << (w - 1)) - 1);
                let min_bv = format!("(_ bv{} {w})", 1u128 << (w - 1));
                format!(
                    "(ite (fp.isNaN {x}) (_ bv0 {w}) \
                     (ite (fp.geq {x} {pos}) {max_bv} \
                     (ite (fp.leq {x} {neg}) {min_bv} \
                     ((_ fp.to_sbv {w}) {rm} {x}))))"
                )
            }
            Formula::FpToUbv {
                rm,
                value,
                width,
                eb,
                sb,
            } => {
                let w = *width;
                let x = value.to_smtlib();
                let rm = rm.to_smtlib();
                // 2^w as an unsigned (w+1)-bit literal.
                let pos = format!(
                    "((_ to_fp_unsigned {eb} {sb}) RNE (_ bv{} {}))",
                    1u128 << w,
                    w + 1
                );
                // -1.0 in the operand's format.
                let neg_one = format!(
                    "(fp.neg ((_ to_fp_unsigned {eb} {sb}) RNE (_ bv1 {})))",
                    w + 1
                );
                let max_bv = format!("(_ bv{} {w})", (1u128 << w) - 1);
                format!(
                    "(ite (fp.isNaN {x}) (_ bv0 {w}) \
                     (ite (fp.geq {x} {pos}) {max_bv} \
                     (ite (fp.leq {x} {neg_one}) (_ bv0 {w}) \
                     ((_ fp.to_ubv {w}) {rm} {x}))))"
                )
            }
            Formula::FpFromSbv { rm, value, eb, sb } => format!(
                "((_ to_fp {eb} {sb}) {} {})",
                rm.to_smtlib(),
                value.to_smtlib()
            ),
            Formula::FpFromUbv { rm, value, eb, sb } => format!(
                "((_ to_fp_unsigned {eb} {sb}) {} {})",
                rm.to_smtlib(),
                value.to_smtlib()
            ),
            Formula::FpConvert { rm, value, eb, sb } => format!(
                "((_ to_fp {eb} {sb}) {} {})",
                rm.to_smtlib(),
                value.to_smtlib()
            ),

            // Uninterpreted predicate application (EUF). Lowers to a bare symbol
            // when nullary, or `(name arg1 ..)` otherwise. The symbol's
            // `(declare-fun name (<arg-sorts>) Bool)` is emitted once by the
            // backend's declaration collector; the application is opaque to the
            // solver (no axioms).
            Formula::Pred(name, args) => {
                let sym = escape_smtlib_symbol(name.as_str());
                if args.is_empty() {
                    sym
                } else {
                    let parts: Vec<String> = args.iter().map(Formula::to_smtlib).collect();
                    format!("({} {})", sym, parts.join(" "))
                }
            }

            // ── Algebraic-datatype terms (Lever A) ──────────────────────────
            // The `(declare-datatype …)` that DEFINES the sort is emitted
            // separately from the datatype-sorted variable's `Sort`
            // (`Sort::datatype_declarations`); here we only reference its
            // constructors/selectors/testers.
            Formula::Ctor { ctor, args, sort } => {
                let ctor_sym = escape_smtlib_symbol(ctor);
                if args.is_empty() {
                    // A nullary constructor is a bare constant, not a 0-ary
                    // application; qualify it with its datatype sort
                    // (`(as C Sort)`) so constructors shared across datatype
                    // families are unambiguous — matches the in-process ay path.
                    format!("(as {} {})", ctor_sym, sort.to_smtlib())
                } else {
                    let parts: Vec<String> = args.iter().map(Formula::to_smtlib).collect();
                    format!("({} {})", ctor_sym, parts.join(" "))
                }
            }
            Formula::Sel { field, arg, .. } => {
                format!("({} {})", escape_smtlib_symbol(field), arg.to_smtlib())
            }
            Formula::IsCtor { ctor, arg, .. } => {
                format!(
                    "((_ is {}) {})",
                    escape_smtlib_symbol(ctor),
                    arg.to_smtlib()
                )
            }

            // Uninterpreted function application (EUF). Lowers like `Pred` —
            // a bare symbol when nullary, `(func arg1 ..)` otherwise; the
            // result-sorted `declare-fun` is the backend's job.
            Formula::FnApp { func, args, .. } => {
                let sym = escape_smtlib_symbol(func);
                if args.is_empty() {
                    sym
                } else {
                    let parts: Vec<String> = args.iter().map(Formula::to_smtlib).collect();
                    format!("({} {})", sym, parts.join(" "))
                }
            }
        }
    }
}

#[cfg(test)]
mod truncation_tests {
    use super::pow2_decimal;
    use crate::formula::Formula;
    use crate::formula::Sort;

    fn var(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.to_string(), Sort::Int))
    }

    #[test]
    fn rem_lowers_to_truncated_not_euclidean() {
        // Regression (round-7 false-PROVE): Rust `%` is TRUNCATED (sign follows
        // the dividend). It must NOT lower to bare SMT-LIB `(mod a b)`, which is
        // Euclidean (always non-negative) and falsely proves `result >= 0` for
        // `x % 256` even though `(-1) % 256 == -1`.
        let s = Formula::Rem(var("x"), Box::new(Formula::Int(256))).to_smtlib();
        assert!(s.contains("ite"), "expected sign-correcting ite, got {s}");
        assert!(
            s.contains("(- (mod"),
            "expected negative-dividend branch, got {s}"
        );
        assert_ne!(s, "(mod x 256)", "must not be bare Euclidean mod");
    }

    #[test]
    fn div_lowers_to_truncated_not_floor() {
        // Rust `/` truncates toward zero; SMT-LIB `div` floors toward -inf.
        let s = Formula::Div(var("x"), Box::new(Formula::Int(2))).to_smtlib();
        assert!(
            s.contains("ite") && s.contains("mod"),
            "expected truncated div encoding, got {s}"
        );
        assert_ne!(s, "(div x 2)", "must not be bare Euclidean div");
    }

    #[test]
    fn pow2_decimal_is_overflow_free() {
        assert_eq!(pow2_decimal(0), "1");
        assert_eq!(pow2_decimal(8), "256");
        assert_eq!(pow2_decimal(64), "18446744073709551616");
        // The bug being fixed: `1u128 << 128` masks to 1 in release / panics in
        // debug. The correct value is 2^128.
        assert_eq!(pow2_decimal(128), "340282366920938463463374607431768211456");
    }

    #[test]
    fn bvtoint_signed_128_uses_correct_two_to_128() {
        let inner = Box::new(Formula::Var("v".to_string(), Sort::BitVec(128)));
        let s = Formula::BvToInt(inner, 128, true).to_smtlib();
        assert!(
            s.contains("340282366920938463463374607431768211456"),
            "signed 128-bit BvToInt must subtract 2^128, got {s}"
        );
        assert!(
            !s.contains(") 1)"),
            "must not subtract the masked value 1, got {s}"
        );
    }

    // Regression: 128-bit literals (produced by e.g. AArch64 128-bit NEON vector
    // constants) must survive the serde_json digest path used by trust's
    // verifier-api (`serde_json::to_value` / `to_vec` in `stable_json_digest`).
    // serde_json without `arbitrary_precision` rejects i128/u128 outside the
    // i64/u64 range with "number out of range", which previously ICE'd the
    // verifier's `json_digest_value!` unwrap. These four variants carry the
    // wide integers: Int(i128), UInt(u128), BitVec{value:i128}, FpConst{bits:u128}.
    #[test]
    fn wide_128bit_literals_survive_serde_json_digest() {
        let cases = [
            Formula::Int(i128::MIN),
            Formula::Int(i128::MAX),
            Formula::UInt(u128::MAX),
            Formula::UInt((u64::MAX as u128) + 1),
            Formula::BitVec {
                value: i128::MIN,
                width: 128,
            },
            Formula::BitVec {
                value: -1,
                width: 128,
            },
            Formula::FpConst {
                bits: u128::MAX,
                eb: 15,
                sb: 113,
            }, // f128
        ];
        for f in cases {
            // Exactly the two serde_json calls trust's digest path makes.
            let v = serde_json::to_value(&f)
                .unwrap_or_else(|e| panic!("to_value failed for {f:?}: {e}"));
            let bytes =
                serde_json::to_vec(&v).unwrap_or_else(|e| panic!("to_vec failed for {f:?}: {e}"));
            // And it must round-trip losslessly through both to_string/from_str
            // and to_value/from_value (flip.rs uses the latter).
            let back: Formula = serde_json::from_slice(&bytes)
                .unwrap_or_else(|e| panic!("from_slice failed for {f:?}: {e}"));
            assert_eq!(
                back, f,
                "128-bit literal did not round-trip through serde_json"
            );
            let back2: Formula = serde_json::from_value(v)
                .unwrap_or_else(|e| panic!("from_value failed for {f:?}: {e}"));
            assert_eq!(
                back2, f,
                "128-bit literal did not round-trip through serde_json::Value"
            );
        }
    }

    // Zero-regression guard: values that serde_json could always represent must
    // still serialize as a BARE NUMBER (not a string), so pre-existing digests
    // and JSON goldens are byte-identical. Only the out-of-[i64::MIN,u64::MAX]
    // tail becomes a string.
    #[test]
    fn in_range_128bit_literals_keep_bare_number_shape() {
        // Inner value of an externally-tagged variant, e.g. {"Int": 42}.
        let inner = |f: &Formula, key: &str| -> serde_json::Value {
            serde_json::to_value(f).unwrap().get(key).unwrap().clone()
        };
        assert!(inner(&Formula::Int(42), "Int").is_number());
        assert!(inner(&Formula::Int(-1), "Int").is_number());
        assert!(inner(&Formula::Int(i64::MAX as i128), "Int").is_number());
        assert!(inner(&Formula::Int(u64::MAX as i128), "Int").is_number()); // fits as u64
        assert!(inner(&Formula::UInt(u64::MAX as u128), "UInt").is_number());
        // Just past the representable range → string fallback.
        assert!(inner(&Formula::Int((u64::MAX as i128) + 1), "Int").is_string());
        assert!(inner(&Formula::UInt((u64::MAX as u128) + 1), "UInt").is_string());
        assert!(inner(&Formula::Int(i64::MIN as i128 - 1), "Int").is_string());
    }
}

#[cfg(test)]
mod fp_tests {
    use super::{Formula, RoundingMode, Sort};

    const EB: u32 = 11; // f64
    const SB: u32 = 53;

    fn fv(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(
            name.to_string(),
            Sort::Float { eb: EB, sb: SB },
        ))
    }
    fn rne() -> Box<Formula> {
        Box::new(Formula::FpRoundingMode(RoundingMode::RNE))
    }

    #[test]
    fn rounding_modes_render() {
        assert_eq!(
            Formula::FpRoundingMode(RoundingMode::RNE).to_smtlib(),
            "RNE"
        );
        assert_eq!(
            Formula::FpRoundingMode(RoundingMode::RTZ).to_smtlib(),
            "RTZ"
        );
    }

    #[test]
    fn special_constants_render() {
        assert_eq!(
            Formula::FpNaN { eb: EB, sb: SB }.to_smtlib(),
            "(_ NaN 11 53)"
        );
        assert_eq!(
            Formula::FpInf {
                neg: false,
                eb: EB,
                sb: SB
            }
            .to_smtlib(),
            "(_ +oo 11 53)"
        );
        assert_eq!(
            Formula::FpInf {
                neg: true,
                eb: EB,
                sb: SB
            }
            .to_smtlib(),
            "(_ -oo 11 53)"
        );
        assert_eq!(
            Formula::FpZero {
                neg: false,
                eb: EB,
                sb: SB
            }
            .to_smtlib(),
            "(_ +zero 11 53)"
        );
        assert_eq!(
            Formula::FpZero {
                neg: true,
                eb: EB,
                sb: SB
            }
            .to_smtlib(),
            "(_ -zero 11 53)"
        );
    }

    #[test]
    fn bit_pattern_literal_uses_total_width() {
        assert_eq!(
            Formula::FpConst {
                bits: 0,
                eb: EB,
                sb: SB
            }
            .to_smtlib(),
            "((_ to_fp 11 53) (_ bv0 64))"
        );
        assert_eq!(
            Formula::FpConst {
                bits: 1,
                eb: 8,
                sb: 24
            }
            .to_smtlib(),
            "((_ to_fp 8 24) (_ bv1 32))"
        );
    }

    #[test]
    fn arithmetic_and_ops_render() {
        assert_eq!(
            Formula::FpAdd(rne(), fv("x"), fv("y")).to_smtlib(),
            "(fp.add RNE x y)"
        );
        assert_eq!(
            Formula::FpMul(rne(), fv("x"), fv("y")).to_smtlib(),
            "(fp.mul RNE x y)"
        );
        assert_eq!(
            Formula::FpFma(rne(), fv("x"), fv("y"), fv("z")).to_smtlib(),
            "(fp.fma RNE x y z)"
        );
        assert_eq!(
            Formula::FpSqrt(rne(), fv("x")).to_smtlib(),
            "(fp.sqrt RNE x)"
        );
        assert_eq!(Formula::FpNeg(fv("x")).to_smtlib(), "(fp.neg x)");
        assert_eq!(Formula::FpRem(fv("x"), fv("y")).to_smtlib(), "(fp.rem x y)");
        assert_eq!(Formula::FpMin(fv("x"), fv("y")).to_smtlib(), "(fp.min x y)");
    }

    #[test]
    fn comparisons_use_ieee_operator_names() {
        assert_eq!(Formula::FpEq(fv("x"), fv("y")).to_smtlib(), "(fp.eq x y)");
        assert_eq!(Formula::FpLt(fv("x"), fv("y")).to_smtlib(), "(fp.lt x y)");
        assert_eq!(Formula::FpLe(fv("x"), fv("y")).to_smtlib(), "(fp.leq x y)");
        assert_eq!(Formula::FpGt(fv("x"), fv("y")).to_smtlib(), "(fp.gt x y)");
        assert_eq!(Formula::FpGe(fv("x"), fv("y")).to_smtlib(), "(fp.geq x y)");
    }

    #[test]
    fn predicates_and_from_bits_render() {
        assert_eq!(Formula::FpIsNaN(fv("x")).to_smtlib(), "(fp.isNaN x)");
        assert_eq!(
            Formula::FpIsInfinite(fv("x")).to_smtlib(),
            "(fp.isInfinite x)"
        );
        assert_eq!(Formula::FpIsZero(fv("x")).to_smtlib(), "(fp.isZero x)");
        let bv = Box::new(Formula::Var("bits".to_string(), Sort::BitVec(64)));
        assert_eq!(
            Formula::FpFromBits {
                bits: bv,
                eb: EB,
                sb: SB
            }
            .to_smtlib(),
            "((_ to_fp 11 53) bits)"
        );
    }

    #[test]
    fn sort_renders_floatingpoint_and_roundingmode() {
        assert_eq!(
            Sort::Float { eb: 8, sb: 24 }.to_smtlib(),
            "(_ FloatingPoint 8 24)"
        );
        assert_eq!(Sort::RoundingMode.to_smtlib(), "RoundingMode");
    }

    #[test]
    fn nested_no_nan_property_renders_end_to_end() {
        let prod = Formula::FpMul(rne(), fv("x"), fv("y"));
        let no_nan = Formula::Not(Box::new(Formula::FpIsNaN(Box::new(prod))));
        assert_eq!(no_nan.to_smtlib(), "(not (fp.isNaN (fp.mul RNE x y)))");
    }

    #[test]
    fn fp_to_ieee_bv_is_the_inverse_of_from_bits() {
        // FpToIeeeBv(FpFromBits(<bv64>)) constructs and renders as the round-trip
        // BV -> FP -> BV. The inner `to_fp` carries its (eb, sb); the outer
        // reinterpret needs no width index (result width inferred from FP sort).
        let a_bv_64 = Box::new(Formula::Var("a".to_string(), Sort::BitVec(EB + SB)));
        let from_bits = Formula::FpFromBits {
            bits: a_bv_64,
            eb: EB,
            sb: SB,
        };
        let to_bv = Formula::FpToIeeeBv(Box::new(from_bits));
        assert_eq!(to_bv.to_smtlib(), "(fp.to_ieee_bv ((_ to_fp 11 53) a))");
    }

    #[test]
    fn fp_to_ieee_bv_counts_as_a_bitvector_term() {
        // The result is a BitVec(eb+sb), so `has_bitvectors()` must see it even
        // when the immediate inner term is a pure FP variable.
        let to_bv = Formula::FpToIeeeBv(fv("x"));
        assert!(
            to_bv.has_bitvectors(),
            "FP -> BV reinterpret yields a bitvector term"
        );
    }

    #[test]
    fn fp_to_ieee_bv_serde_round_trips() {
        let a_bv_64 = Box::new(Formula::Var("a".to_string(), Sort::BitVec(EB + SB)));
        let from_bits = Formula::FpFromBits {
            bits: a_bv_64,
            eb: EB,
            sb: SB,
        };
        let f = Formula::FpToIeeeBv(Box::new(from_bits));
        let json = serde_json::to_string(&f).expect("serialize FpToIeeeBv");
        let back: Formula = serde_json::from_str(&json).expect("deserialize FpToIeeeBv");
        assert_eq!(
            f, back,
            "FpToIeeeBv must round-trip losslessly through serde"
        );
    }

    #[test]
    fn fp_to_ieee_bv_recurses_in_walks() {
        // children()/free_variables() recurse into the boxed inner.
        let a_bv_64 = Box::new(Formula::Var("a".to_string(), Sort::BitVec(EB + SB)));
        let from_bits = Formula::FpFromBits {
            bits: a_bv_64,
            eb: EB,
            sb: SB,
        };
        let f = Formula::FpToIeeeBv(Box::new(from_bits));

        assert_eq!(f.children().len(), 1, "one boxed sub-formula");
        assert!(
            f.free_variables().contains("a"),
            "free var of the inner is visible"
        );

        // substitute-via-map recurses into the inner: renaming `a` -> `b` reaches
        // through both the outer reinterpret and the inner `to_fp`.
        let renamed = f.rename_var("a", "b");
        assert!(renamed.free_variables().contains("b"));
        assert!(!renamed.free_variables().contains("a"));
        assert_eq!(renamed.to_smtlib(), "(fp.to_ieee_bv ((_ to_fp 11 53) b))");
    }
}

#[cfg(test)]
mod datatype_term_tests {
    //! Lever A step-1 infrastructure: the datatype term nodes
    //! (`Ctor`/`Sel`/`IsCtor`) must be WRITABLE and must lower faithfully to
    //! SMT-LIB datatype terms. This makes a datatype equation like
    //! `Sort(succ l) = Sort(succ l)` expressible; it proves no VC on its own.
    use super::{Formula, Sort};

    /// A recursive toy `Level = zero | succ(pred: Level)` — the shape the
    /// clean-kernel universe-level fidelity equation rides. The recursive
    /// `pred` field is a BY-NAME reference (empty `constructors`), matching the
    /// natively-recursive SMT-LIB datatype encoding.
    fn level_sort() -> Sort {
        let level_ref = Sort::Datatype {
            name: "Level".into(),
            constructors: Vec::new(),
        };
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("zero".into(), vec![]),
                ("succ".into(), vec![("pred".into(), level_ref)]),
            ],
        }
    }

    fn succ(arg: Formula) -> Formula {
        Formula::Ctor {
            ctor: "succ".into(),
            args: vec![arg],
            sort: level_sort(),
        }
    }

    #[test]
    fn nullary_ctor_lowers_to_sort_qualified_constant() {
        // A nullary constructor is a datatype constant, `(as zero Level)`, NOT a
        // 0-ary application `(zero)` (invalid SMT-LIB).
        let zero = Formula::Ctor {
            ctor: "zero".into(),
            args: vec![],
            sort: level_sort(),
        };
        assert_eq!(zero.to_smtlib(), "(as zero Level)");
    }

    #[test]
    fn applied_ctor_lowers_to_constructor_application() {
        let l = Formula::Var("l".into(), level_sort());
        assert_eq!(succ(l).to_smtlib(), "(succ l)");
    }

    #[test]
    fn selector_lowers_to_field_application() {
        let x = Formula::Var("x".into(), level_sort());
        let sel = Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_sort(),
            arg: Box::new(x),
        };
        assert_eq!(sel.to_smtlib(), "(pred x)");
    }

    #[test]
    fn tester_lowers_to_is_recognizer() {
        let x = Formula::Var("x".into(), level_sort());
        let is = Formula::IsCtor {
            datatype: "Level".into(),
            ctor: "succ".into(),
            arg: Box::new(x),
        };
        assert_eq!(is.to_smtlib(), "((_ is succ) x)");
    }

    #[test]
    fn fidelity_equation_is_writable_and_lowers() {
        // The step-1 headline: `Sort(succ l) = Sort(succ l)` — here directly
        // `succ l = succ l` over the Level datatype — is now EXPRESSIBLE as a
        // Formula and lowers to a genuine SMT-LIB datatype equation. (This is
        // NOT a proof; it is the writability the fidelity VC depends on.)
        let l = || Formula::Var("l".into(), level_sort());
        let eq = Formula::Eq(Box::new(succ(l())), Box::new(succ(l())));
        assert_eq!(eq.to_smtlib(), "(= (succ l) (succ l))");

        // The datatype itself is declarable — the `(declare-datatype …)` the
        // above references is emitted from the sort, exactly once, finitely
        // (the recursive `pred` field is a by-name reference).
        let decls = level_sort().datatype_declarations();
        assert_eq!(
            decls,
            vec!["(declare-datatype Level ((zero) (succ (pred Level))))".to_string()]
        );
    }

    #[test]
    fn datatype_terms_recurse_in_walks() {
        // children()/free_variables()/map recurse through the new nodes.
        let l = Formula::Var("l".into(), level_sort());
        let f = succ(l);
        assert_eq!(f.children().len(), 1, "the constructor's single field arg");
        assert!(
            f.free_variables().contains("l"),
            "the arg's free var is visible"
        );

        let renamed = f.rename_var("l", "m");
        assert!(renamed.free_variables().contains("m"));
        assert!(!renamed.free_variables().contains("l"));
        assert_eq!(renamed.to_smtlib(), "(succ m)");
    }

    #[test]
    fn datatype_terms_serde_round_trip() {
        let l = Formula::Var("l".into(), level_sort());
        let eq = Formula::Eq(Box::new(succ(l.clone())), Box::new(succ(l)));
        let json = serde_json::to_string(&eq).expect("serialize datatype equation");
        let back: Formula = serde_json::from_str(&json).expect("deserialize datatype equation");
        assert_eq!(
            eq, back,
            "datatype terms must round-trip losslessly through serde"
        );
    }
}

#[cfg(test)]
mod fnapp_tests {
    use super::*;

    fn level_sort() -> Sort {
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("zero".into(), vec![]),
                (
                    "succ".into(),
                    vec![(
                        "pred".into(),
                        Sort::Datatype {
                            name: "Level".into(),
                            constructors: vec![],
                        },
                    )],
                ),
            ],
        }
    }

    fn app(args: Vec<Formula>) -> Formula {
        Formula::FnApp {
            func: "mirror_ref".into(),
            args,
            sort: level_sort(),
        }
    }

    #[test]
    fn fnapp_to_smtlib_is_an_euf_application() {
        let f = app(vec![
            Formula::Var("fuel".into(), level_sort()),
            Formula::Var("e".into(), level_sort()),
        ]);
        assert_eq!(f.to_smtlib(), "(mirror_ref fuel e)");
        assert_eq!(
            app(vec![]).to_smtlib(),
            "mirror_ref",
            "nullary lowers to a bare symbol"
        );
    }

    #[test]
    fn fnapp_recurses_in_walks() {
        let f = app(vec![Formula::Var("e".into(), level_sort())]);
        assert_eq!(f.children().len(), 1, "the argument term is a sub-formula");
        assert!(f.free_variables().contains("e"));
        let renamed = f.rename_var("e", "x");
        assert!(renamed.free_variables().contains("x"));
        assert!(!renamed.free_variables().contains("e"));
        assert_eq!(renamed.to_smtlib(), "(mirror_ref x)");
    }

    #[test]
    fn fnapp_serde_round_trip() {
        let f = app(vec![Formula::Var("e".into(), level_sort())]);
        let json = serde_json::to_string(&f).expect("serialize function application");
        let back: Formula = serde_json::from_str(&json).expect("deserialize function application");
        assert_eq!(
            f, back,
            "function applications must round-trip losslessly through serde"
        );
    }
}
