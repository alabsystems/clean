// trust-ir-contract/formula: SMT-level formulas
//
// These are the verification conditions sent to solvers. Backend-agnostic —
// trust-router encodes these into ay/trust-wp/ty specific representations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashSet;
use crate::rat::RatLit;
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

    /// An EXACT rational literal `num / den` of sort [`Sort::Real`]. The
    /// payload [`RatLit`] carries the canonical decimal digit strings and
    /// ENFORCES their syntax on construction and deserialization (see its
    /// docs for the exact grammar and the producer-side reducedness contract).
    ///
    /// SEMANTICS: a `Rat` literal denotes a real number — the value the SMT-LIB
    /// term `(/ num den)` denotes in the `Reals` theory. It is NOT an `Int`
    /// term: `check_formula_sort`-style checkers sort it as `Real`, and an
    /// ordering atom mixing it with an `Int`-sorted variable or literal is
    /// ill-sorted; a producer spells an integer constant in a `Real` position
    /// as [`Formula::rat_from_int`].
    ///
    /// Appended after `FnApp` so the variant index of every existing formula is
    /// unchanged (index-based encodings of `Formula` stay stable); the newtype
    /// payload encodes exactly as a two-string struct variant would.
    Rat(RatLit),

    /// The CONSTANT ARRAY of sort `(Array index_sort elem_sort)` that maps
    /// every index to `value`: `λ i. value`, written in SMT-LIB as
    /// `((as const (Array I E)) v)`. `value` is an `elem_sort`-sorted term,
    /// evaluated once, and it may be symbolic.
    ///
    /// This is how a verifier states a uniform array `[v; N]` at a cost that
    /// does not depend on `N`: `N` does not occur in the term at all. The
    /// alternatives cost `N` (a chain of `N` `Store`s) or lose `v` (a free
    /// base array). It is also the neutral base for a store chain: `Store`s
    /// over `ConstArray(v)` give an array that is `v` everywhere except at the
    /// stored indices.
    ///
    /// Both sorts are carried, not inferred, because SMT-LIB needs the
    /// qualified sort `(Array I E)` and has no sort inference to recover `E`
    /// from `v`. `Ctor`, `FnApp` and `FpToSbv` carry sorts for the same
    /// reason. Carrying the two component sorts, rather than one full `Sort`,
    /// means a non-array result sort cannot be represented. A consumer that
    /// needs only the index sort, such as ay's
    /// `const_array(index_sort, value)`, reads `index_sort` and gets the
    /// element sort from `value`. A `Datatype` named in either sort must be
    /// declared, exactly as for a `Var` of that sort.
    ///
    /// SEMANTICS: `select(ConstArray { value: v, .. }, i) = v` for EVERY `i`.
    /// That includes indices at and beyond a Rust array's length, which a
    /// store chain over a free base leaves unconstrained. So a producer that
    /// models `[v; N]` this way pins the out-of-bounds lanes too. That is sound
    /// as long as the out-of-bounds reads are obligated separately and two
    /// Rust arrays are compared lane by lane over `0..N`, never by SMT array
    /// equality, since two arrays that agree on `0..N` can differ beyond it.
    /// `as const` is not in the SMT-LIB 2.6 `ArraysEx` signature. It is the
    /// de-facto extension that ay, Z3 and cvc5 all accept, so a text consumer
    /// whose solver lacks it must refuse the node, never approximate it.
    ///
    /// Appended after `Rat`, so every existing variant keeps its index and
    /// index-based encodings of `Formula` stay stable. Formula is not on the
    /// trust-ir wire. A `ProofFormula` carries it only as the opaque
    /// `trust-types.Formula@1` JSON payload, which trust-types owns. JSON for
    /// every formula without this node is unchanged, and a reader older than
    /// this variant refuses a payload that contains it instead of
    /// misreading it.
    ConstArray {
        index_sort: Sort,
        elem_sort: Sort,
        value: Box<Formula>,
    },
}

impl Formula {
    /// Checked constructor for an exact rational literal [`Formula::Rat`].
    ///
    /// Returns `None` unless both strings are in the canonical decimal syntax
    /// [`RatLit`] documents: `num` = `-?[1-9][0-9]*` or `0`, `den` =
    /// `[1-9][0-9]*`. Reducedness is not checked (see [`RatLit`]).
    ///
    /// ```
    /// use trust_ir_contract::Formula;
    ///
    /// let half = Formula::rat("1", "2").expect("canonical");
    /// assert_eq!(half.to_smtlib(), "(/ 1 2)");
    /// assert_eq!(Formula::rat("-7", "3").unwrap().to_smtlib(), "(/ (- 7) 3)");
    /// assert_eq!(Formula::rat("5", "1").unwrap().to_smtlib(), "5");
    /// assert!(Formula::rat("01", "2").is_none(), "leading zero");
    /// assert!(Formula::rat("1", "0").is_none(), "zero denominator");
    /// assert!(Formula::rat("-0", "1").is_none(), "negative zero");
    /// assert!(Formula::rat("1", "-2").is_none(), "sign belongs on the numerator");
    /// ```
    #[must_use]
    pub fn rat(num: &str, den: &str) -> Option<Formula> {
        RatLit::new(num, den).map(Formula::Rat)
    }

    /// An exact rational literal with the value of the integer `n`
    /// (`den = "1"`), for embedding an integer constant into a `Real`-sorted
    /// term without going through [`Formula::Int`].
    #[must_use]
    pub fn rat_from_int(n: i128) -> Formula {
        Formula::Rat(RatLit::from_int(n))
    }

    /// The constant array [`Formula::ConstArray`] of sort
    /// `(Array index_sort elem_sort)` mapping every index to `value`.
    ///
    /// ```
    /// use trust_ir_contract::{Formula, Sort};
    ///
    /// // `[7u8; N]` for ANY N: the length does not occur in the term.
    /// let splat = Formula::const_array(
    ///     Sort::Int,
    ///     Sort::BitVec(8),
    ///     Formula::BitVec { value: 7, width: 8 },
    /// );
    /// assert_eq!(splat.to_smtlib(), "((as const (Array Int (_ BitVec 8))) (_ bv7 8))");
    /// ```
    #[must_use]
    pub fn const_array(index_sort: Sort, elem_sort: Sort, value: Formula) -> Formula {
        Formula::ConstArray {
            index_sort,
            elem_sort,
            value: Box::new(value),
        }
    }

    /// The `(num, den)` decimal strings of a [`Formula::Rat`] literal, else
    /// `None`.
    #[must_use]
    pub fn rat_parts(&self) -> Option<(&str, &str)> {
        match self {
            Formula::Rat(lit) => Some((lit.num(), lit.den())),
            _ => None,
        }
    }

    /// Collect references to all direct sub-formulas.
    #[must_use]
    pub fn children(&self) -> Vec<&Formula> {
        match self {
            // Leaves
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Rat { .. }
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

            // Constant array: the one element term (the sorts are not
            // sub-formulas).
            Formula::ConstArray { value, .. } => vec![value],
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
            | Formula::Rat { .. }
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

            // Constant array: map the element term; preserve both sorts.
            Formula::ConstArray {
                index_sort,
                elem_sort,
                value,
            } => Formula::ConstArray {
                index_sort,
                elem_sort,
                value: Box::new(f(*value)),
            },
        }
    }

    // ── Node shells: the split/rebuild pair the hash-consed DAG is built on ──
    //
    // A SHELL is a node with its children stripped: the node's own payload
    // (operator, widths, sorts, names, bindings) and nothing of its children.
    // A fixed-arity child slot holds the placeholder `Formula::Bool(true)`;
    // the child LIST of an n-ary node (`And`, `Or`, `Pred`, `Ctor`, `FnApp`)
    // is empty, so a shell costs its payload, not a placeholder per child,
    // and the arity is carried beside it (`crate::formula_dag::Shell`).
    // `crate::formula_dag` keys its nodes on (shell, arity, child ids).
    //
    // The owned split and the rebuild are `map_children` itself (plus
    // `nary_args_mut` for the n-ary child list), so they cover exactly the
    // variants `map_children` covers. The borrowed split (`shell_clone`) is
    // the one other per-variant match; it is exhaustive (no wildcard, so a
    // new variant does not compile until it has an arm), and
    // `tests/formula_dag.rs` holds it equal to the `map_children` split for a
    // witness of EVERY variant, a list a serde-derived census keeps complete
    // (`crate::formula_census`).

    /// The placeholder a shell holds in each fixed-arity child slot.
    pub(crate) fn shell_hole() -> Formula {
        Formula::Bool(true)
    }

    /// The child list of an n-ary node (`And`, `Or`, `Pred`, `Ctor`,
    /// `FnApp`: the variants whose arity the variant does not fix), or `None`.
    ///
    /// Exhaustive on purpose (no wildcard): a new variant cannot compile
    /// until it says whether its children are a list.
    #[allow(clippy::too_many_lines)] // one arm per variant, by design
    pub(crate) fn nary_args_mut(&mut self) -> Option<&mut Vec<Formula>> {
        match self {
            Formula::And(args)
            | Formula::Or(args)
            | Formula::Pred(_, args)
            | Formula::Ctor { args, .. }
            | Formula::FnApp { args, .. } => Some(args),
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..)
            | Formula::Not(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
            | Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(_)
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
            | Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_)
            | Formula::FpAdd(..)
            | Formula::FpSub(..)
            | Formula::FpMul(..)
            | Formula::FpDiv(..)
            | Formula::FpFma(..)
            | Formula::FpSqrt(..)
            | Formula::FpRem(..)
            | Formula::FpNeg(_)
            | Formula::FpAbs(_)
            | Formula::FpMin(..)
            | Formula::FpMax(..)
            | Formula::FpEq(..)
            | Formula::FpLt(..)
            | Formula::FpLe(..)
            | Formula::FpGt(..)
            | Formula::FpGe(..)
            | Formula::FpIsNaN(_)
            | Formula::FpIsInfinite(_)
            | Formula::FpIsZero(_)
            | Formula::FpIsNormal(_)
            | Formula::FpIsSubnormal(_)
            | Formula::FpIsNegative(_)
            | Formula::FpIsPositive(_)
            | Formula::FpFromBits { .. }
            | Formula::FpToSbv { .. }
            | Formula::FpToUbv { .. }
            | Formula::FpFromSbv { .. }
            | Formula::FpFromUbv { .. }
            | Formula::FpConvert { .. }
            | Formula::FpToIeeeBv(_)
            | Formula::Ite(..)
            | Formula::Forall(..)
            | Formula::Exists(..)
            | Formula::Select(..)
            | Formula::Store(..)
            | Formula::Sel { .. }
            | Formula::IsCtor { .. }
            | Formula::Rat(_)
            | Formula::ConstArray { .. } => None,
        }
    }

    /// Split an owned node into its shell and its children (in
    /// [`Formula::children`] order), moving the children out. Built on
    /// [`Formula::map_children`]; an n-ary node's shell has an empty child
    /// list.
    pub(crate) fn split_children(self) -> (Formula, Vec<Formula>) {
        let mut kids = Vec::new();
        let mut shell = self.map_children(&mut |child| {
            kids.push(child);
            Formula::shell_hole()
        });
        if let Some(args) = shell.nary_args_mut() {
            args.clear();
        }
        (shell, kids)
    }

    /// Put `kids` (in [`Formula::children`] order) into the child slots of
    /// this shell: the inverse of [`Formula::split_children`].
    ///
    /// # Panics
    ///
    /// If `kids.len()` is not the shell's arity, or `self` is not a shell (an
    /// n-ary node whose child list is not empty). This is fail-closed on
    /// purpose: a missing child must never become a placeholder (`true`),
    /// and a surplus one must never be dropped. Every caller establishes the
    /// arity first (`Shell::rebuild` checks it and returns an error;
    /// `FormulaDag::expand` holds it by construction).
    pub(crate) fn fill_children(mut self, kids: Vec<Formula>) -> Formula {
        if let Some(args) = self.nary_args_mut() {
            assert!(
                args.is_empty(),
                "fill_children: an n-ary shell holds no child list"
            );
            *args = kids;
            return self;
        }
        let expected = kids.len();
        let mut kids = kids.into_iter();
        let mut filled = 0usize;
        let node = self.map_children(&mut |hole| {
            debug_assert_eq!(hole, Formula::shell_hole());
            filled += 1;
            kids.next()
                .expect("fill_children: fewer children than the shell's arity")
        });
        assert!(
            kids.next().is_none(),
            "fill_children: {expected} children for a shell of arity {filled}"
        );
        node
    }

    /// This node's shell without cloning any child: the payload is cloned,
    /// every fixed-arity child slot holds the placeholder and an n-ary child
    /// list is empty. Equal to the shell [`Formula::split_children`] returns
    /// for a clone of `self`.
    #[allow(clippy::too_many_lines)] // one arm per variant, by design
    pub(crate) fn shell_clone(&self) -> Formula {
        fn h() -> Box<Formula> {
            Box::new(Formula::shell_hole())
        }
        match self {
            // Leaves
            Formula::Bool(b) => Formula::Bool(*b),
            Formula::Int(n) => Formula::Int(*n),
            Formula::UInt(n) => Formula::UInt(*n),
            Formula::BitVec { value, width } => Formula::BitVec {
                value: *value,
                width: *width,
            },
            Formula::Var(name, sort) => Formula::Var(name.clone(), sort.clone()),
            Formula::SymVar(sym, sort) => Formula::SymVar(*sym, sort.clone()),
            Formula::Rat(lit) => Formula::Rat(lit.clone()),

            // Boolean connectives
            Formula::Not(_) => Formula::Not(h()),
            Formula::And(_) => Formula::And(Vec::new()),
            Formula::Or(_) => Formula::Or(Vec::new()),
            Formula::Implies(..) => Formula::Implies(h(), h()),

            // Comparisons and integer arithmetic
            Formula::Eq(..) => Formula::Eq(h(), h()),
            Formula::Lt(..) => Formula::Lt(h(), h()),
            Formula::Le(..) => Formula::Le(h(), h()),
            Formula::Gt(..) => Formula::Gt(h(), h()),
            Formula::Ge(..) => Formula::Ge(h(), h()),
            Formula::Add(..) => Formula::Add(h(), h()),
            Formula::Sub(..) => Formula::Sub(h(), h()),
            Formula::Mul(..) => Formula::Mul(h(), h()),
            Formula::Div(..) => Formula::Div(h(), h()),
            Formula::Rem(..) => Formula::Rem(h(), h()),
            Formula::Neg(_) => Formula::Neg(h()),

            // Bitvector arithmetic and comparisons
            Formula::BvAdd(_, _, w) => Formula::BvAdd(h(), h(), *w),
            Formula::BvSub(_, _, w) => Formula::BvSub(h(), h(), *w),
            Formula::BvMul(_, _, w) => Formula::BvMul(h(), h(), *w),
            Formula::BvUDiv(_, _, w) => Formula::BvUDiv(h(), h(), *w),
            Formula::BvSDiv(_, _, w) => Formula::BvSDiv(h(), h(), *w),
            Formula::BvURem(_, _, w) => Formula::BvURem(h(), h(), *w),
            Formula::BvSRem(_, _, w) => Formula::BvSRem(h(), h(), *w),
            Formula::BvAnd(_, _, w) => Formula::BvAnd(h(), h(), *w),
            Formula::BvOr(_, _, w) => Formula::BvOr(h(), h(), *w),
            Formula::BvXor(_, _, w) => Formula::BvXor(h(), h(), *w),
            Formula::BvNot(_, w) => Formula::BvNot(h(), *w),
            Formula::BvShl(_, _, w) => Formula::BvShl(h(), h(), *w),
            Formula::BvLShr(_, _, w) => Formula::BvLShr(h(), h(), *w),
            Formula::BvAShr(_, _, w) => Formula::BvAShr(h(), h(), *w),
            Formula::BvULt(_, _, w) => Formula::BvULt(h(), h(), *w),
            Formula::BvULe(_, _, w) => Formula::BvULe(h(), h(), *w),
            Formula::BvSLt(_, _, w) => Formula::BvSLt(h(), h(), *w),
            Formula::BvSLe(_, _, w) => Formula::BvSLe(h(), h(), *w),

            // Bitvector conversions
            Formula::BvToInt(_, w, signed) => Formula::BvToInt(h(), *w, *signed),
            Formula::IntToBv(_, w) => Formula::IntToBv(h(), *w),
            Formula::BvExtract { high, low, .. } => Formula::BvExtract {
                inner: h(),
                high: *high,
                low: *low,
            },
            Formula::BvConcat(..) => Formula::BvConcat(h(), h()),
            Formula::BvZeroExt(_, bits) => Formula::BvZeroExt(h(), *bits),
            Formula::BvSignExt(_, bits) => Formula::BvSignExt(h(), *bits),

            // Floating point — leaves
            Formula::FpConst { bits, eb, sb } => Formula::FpConst {
                bits: *bits,
                eb: *eb,
                sb: *sb,
            },
            Formula::FpNaN { eb, sb } => Formula::FpNaN { eb: *eb, sb: *sb },
            Formula::FpInf { neg, eb, sb } => Formula::FpInf {
                neg: *neg,
                eb: *eb,
                sb: *sb,
            },
            Formula::FpZero { neg, eb, sb } => Formula::FpZero {
                neg: *neg,
                eb: *eb,
                sb: *sb,
            },
            Formula::FpRoundingMode(rm) => Formula::FpRoundingMode(*rm),

            // Floating point — operators
            Formula::FpAdd(..) => Formula::FpAdd(h(), h(), h()),
            Formula::FpSub(..) => Formula::FpSub(h(), h(), h()),
            Formula::FpMul(..) => Formula::FpMul(h(), h(), h()),
            Formula::FpDiv(..) => Formula::FpDiv(h(), h(), h()),
            Formula::FpFma(..) => Formula::FpFma(h(), h(), h(), h()),
            Formula::FpSqrt(..) => Formula::FpSqrt(h(), h()),
            Formula::FpRem(..) => Formula::FpRem(h(), h()),
            Formula::FpNeg(_) => Formula::FpNeg(h()),
            Formula::FpAbs(_) => Formula::FpAbs(h()),
            Formula::FpMin(..) => Formula::FpMin(h(), h()),
            Formula::FpMax(..) => Formula::FpMax(h(), h()),
            Formula::FpEq(..) => Formula::FpEq(h(), h()),
            Formula::FpLt(..) => Formula::FpLt(h(), h()),
            Formula::FpLe(..) => Formula::FpLe(h(), h()),
            Formula::FpGt(..) => Formula::FpGt(h(), h()),
            Formula::FpGe(..) => Formula::FpGe(h(), h()),
            Formula::FpIsNaN(_) => Formula::FpIsNaN(h()),
            Formula::FpIsInfinite(_) => Formula::FpIsInfinite(h()),
            Formula::FpIsZero(_) => Formula::FpIsZero(h()),
            Formula::FpIsNormal(_) => Formula::FpIsNormal(h()),
            Formula::FpIsSubnormal(_) => Formula::FpIsSubnormal(h()),
            Formula::FpIsNegative(_) => Formula::FpIsNegative(h()),
            Formula::FpIsPositive(_) => Formula::FpIsPositive(h()),
            Formula::FpFromBits { eb, sb, .. } => Formula::FpFromBits {
                bits: h(),
                eb: *eb,
                sb: *sb,
            },
            Formula::FpToSbv { width, eb, sb, .. } => Formula::FpToSbv {
                rm: h(),
                value: h(),
                width: *width,
                eb: *eb,
                sb: *sb,
            },
            Formula::FpToUbv { width, eb, sb, .. } => Formula::FpToUbv {
                rm: h(),
                value: h(),
                width: *width,
                eb: *eb,
                sb: *sb,
            },
            Formula::FpFromSbv { eb, sb, .. } => Formula::FpFromSbv {
                rm: h(),
                value: h(),
                eb: *eb,
                sb: *sb,
            },
            Formula::FpFromUbv { eb, sb, .. } => Formula::FpFromUbv {
                rm: h(),
                value: h(),
                eb: *eb,
                sb: *sb,
            },
            Formula::FpConvert { eb, sb, .. } => Formula::FpConvert {
                rm: h(),
                value: h(),
                eb: *eb,
                sb: *sb,
            },
            Formula::FpToIeeeBv(_) => Formula::FpToIeeeBv(h()),

            // Conditional, quantifiers, arrays
            Formula::Ite(..) => Formula::Ite(h(), h(), h()),
            Formula::Forall(bindings, _) => Formula::Forall(bindings.clone(), h()),
            Formula::Exists(bindings, _) => Formula::Exists(bindings.clone(), h()),
            Formula::Select(..) => Formula::Select(h(), h()),
            Formula::Store(..) => Formula::Store(h(), h(), h()),

            // Applications and datatype terms
            Formula::Pred(name, _) => Formula::Pred(*name, Vec::new()),
            Formula::Ctor { ctor, sort, .. } => Formula::Ctor {
                ctor: ctor.clone(),
                args: Vec::new(),
                sort: sort.clone(),
            },
            Formula::Sel {
                datatype,
                field,
                field_sort,
                ..
            } => Formula::Sel {
                datatype: datatype.clone(),
                field: field.clone(),
                field_sort: field_sort.clone(),
                arg: h(),
            },
            Formula::IsCtor { datatype, ctor, .. } => Formula::IsCtor {
                datatype: datatype.clone(),
                ctor: ctor.clone(),
                arg: h(),
            },
            Formula::FnApp { func, sort, .. } => Formula::FnApp {
                func: func.clone(),
                args: Vec::new(),
                sort: sort.clone(),
            },
            Formula::ConstArray {
                index_sort,
                elem_sort,
                ..
            } => Formula::ConstArray {
                index_sort: index_sort.clone(),
                elem_sort: elem_sort.clone(),
                value: h(),
            },
        }
    }

    /// Whether this node BINDS variable names in (some of) its children —
    /// today exactly the quantifiers. Under such a node, a symbol spelled
    /// like a name it binds denotes the bound variable, so one DAG node can
    /// mean two different things on the two sides of the binder; a sharing
    /// printer may move a subterm across it only when the subterm mentions
    /// none of the names it binds (`crate::formula_dag`).
    #[must_use]
    pub fn binds_variables(&self) -> bool {
        self.bound_variables().is_some()
    }

    /// The variables this node binds (name and sort, in binding order), or
    /// `None` for a node that binds nothing. A binder's own children are
    /// not part of the answer: this reads the node's payload only.
    ///
    /// Exhaustive on purpose (no wildcard): a new binding variant cannot
    /// compile until this answers for it, and [`Formula::binds_variables`]
    /// is defined from it, so the two cannot disagree.
    #[must_use]
    #[allow(clippy::too_many_lines)] // one arm per variant, by design
    pub fn bound_variables(&self) -> Option<&[(crate::Symbol, Sort)]> {
        match self {
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => Some(bindings),
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..)
            | Formula::Not(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
            | Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(_)
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
            | Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_)
            | Formula::FpAdd(..)
            | Formula::FpSub(..)
            | Formula::FpMul(..)
            | Formula::FpDiv(..)
            | Formula::FpFma(..)
            | Formula::FpSqrt(..)
            | Formula::FpRem(..)
            | Formula::FpNeg(_)
            | Formula::FpAbs(_)
            | Formula::FpMin(..)
            | Formula::FpMax(..)
            | Formula::FpEq(..)
            | Formula::FpLt(..)
            | Formula::FpLe(..)
            | Formula::FpGt(..)
            | Formula::FpGe(..)
            | Formula::FpIsNaN(_)
            | Formula::FpIsInfinite(_)
            | Formula::FpIsZero(_)
            | Formula::FpIsNormal(_)
            | Formula::FpIsSubnormal(_)
            | Formula::FpIsNegative(_)
            | Formula::FpIsPositive(_)
            | Formula::FpFromBits { .. }
            | Formula::FpToSbv { .. }
            | Formula::FpToUbv { .. }
            | Formula::FpFromSbv { .. }
            | Formula::FpFromUbv { .. }
            | Formula::FpConvert { .. }
            | Formula::FpToIeeeBv(_)
            | Formula::Ite(..)
            | Formula::Select(..)
            | Formula::Store(..)
            | Formula::Pred(..)
            | Formula::Ctor { .. }
            | Formula::Sel { .. }
            | Formula::IsCtor { .. }
            | Formula::FnApp { .. }
            | Formula::Rat(_)
            | Formula::ConstArray { .. } => None,
        }
    }

    /// Drop a formula of any depth without recursion.
    ///
    /// The derived `Drop` of `Formula` recurses once per level, so a tree a
    /// million levels deep (which [`crate::formula_dag::FormulaDag::expand`]
    /// can return) overflows a thread's stack when it goes out of scope.
    /// This detaches the children onto a heap stack with
    /// [`Formula::map_children`] and drops each node once its slots hold only
    /// leaves.
    pub fn drop_iterative(self) {
        let mut stack = vec![self];
        while let Some(node) = stack.pop() {
            // The returned shell's children are leaf placeholders, so it
            // drops in constant depth.
            drop(node.split_children_into(&mut stack));
        }
    }

    /// [`Formula::split_children`] that pushes the children onto `sink`
    /// (in order) instead of returning them.
    fn split_children_into(self, sink: &mut Vec<Formula>) -> Formula {
        self.map_children(&mut |child| {
            sink.push(child);
            Formula::shell_hole()
        })
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
                // A constant array's carried sorts are written into the term
                // (`(as const (Array I E))`), so a bitvector sort there is a
                // bitvector type the formula mentions, even where `value`
                // itself is not a bitvector term (an `Int` element over a
                // `(_ BitVec 64)` index, or an element read out of another
                // array).
                Formula::ConstArray {
                    index_sort,
                    elem_sort,
                    ..
                } if sort_mentions_bitvec(index_sort) || sort_mentions_bitvec(elem_sort) => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    /// Check if this formula contains array theory operations
    /// (Select/Store/ConstArray) or array-typed variables.
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
                Formula::Select(..) | Formula::Store(..) | Formula::ConstArray { .. } => {
                    found = true;
                }
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

/// Whether `sort` is a bitvector sort or an array sort with one inside it. A
/// datatype is opaque here, as for a `Var` of datatype sort.
fn sort_mentions_bitvec(sort: &Sort) -> bool {
    match sort {
        Sort::BitVec(_) => true,
        Sort::Array(index, elem) => sort_mentions_bitvec(index) || sort_mentions_bitvec(elem),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 text serialization (moved from trust-types' formula/smtlib.rs).
// ---------------------------------------------------------------------------

/// `multiplier * 2^exp`, less one when `minus_one`, as an exact decimal string.
///
/// The exact-decimal family exists because `1u128 << n` is only defined for
/// `n <= 127`: in release builds Rust MASKS the shift amount and silently
/// yields a wrong value (`1u128 << 128 == 1`), in debug it panics. Every
/// SMT-LIB literal built from a `width` field has to be exact at every width
/// the contract can carry, because a wrong constant is a wrong PROBLEM, not a
/// crash — the solver answers the question it was asked.
///
/// Doubling on little-endian decimal digits, so the cost is quadratic in
/// `exp` and the result is exact wherever the emitted text is itself
/// constructible (a `2^exp` literal is about `0.302 * exp` digits long).
/// `multiplier` must be non-zero for `minus_one` to be meaningful; zero is
/// answered with `"0"` rather than borrowing past the end.
fn scaled_pow2_decimal(multiplier: u32, exp: u32, minus_one: bool) -> String {
    if multiplier == 0 {
        return "0".to_string();
    }
    // Little-endian decimal digits of `multiplier`.
    let mut digits: Vec<u8> = Vec::new();
    let mut m = multiplier;
    while m > 0 {
        digits.push((m % 10) as u8);
        m /= 10;
    }
    for _ in 0..exp {
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
    if minus_one {
        // `multiplier >= 1` so the value is >= 1 and the borrow terminates
        // inside the digit vector.
        let mut i = 0;
        while i < digits.len() {
            if digits[i] > 0 {
                digits[i] -= 1;
                break;
            }
            digits[i] = 9;
            i += 1;
        }
        while digits.len() > 1 && digits[digits.len() - 1] == 0 {
            digits.pop();
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

/// `2^width` as an exact decimal string, overflow-free for any width. Used to
/// build the signed `BvToInt` correction term, where a wrong `2^width` would
/// mistranslate negative values and could surface as a false-PROVE.
fn pow2_decimal(width: u32) -> String {
    scaled_pow2_decimal(1, width, false)
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
    // SMT-LIB 2.6 §3.1: a simple symbol cannot start with a digit,
    // even when the whole spelling is not a Rust integer (or overflows one).
    if name.is_empty() || name.as_bytes()[0].is_ascii_digit() {
        return false;
    }
    // Reserved tokens must be quoted in identifier positions. Predefined
    // theory symbols such as `true` are not lexical reserved words.
    if matches!(
        name,
        "BINARY"
            | "DECIMAL"
            | "HEXADECIMAL"
            | "NUMERAL"
            | "STRING"
            | "_"
            | "!"
            | "as"
            | "let"
            | "exists"
            | "forall"
            | "match"
            | "par"
            | "assert"
            | "check-sat"
            | "check-sat-assuming"
            | "declare-const"
            | "declare-datatype"
            | "declare-datatypes"
            | "declare-fun"
            | "declare-sort"
            | "define-fun"
            | "define-fun-rec"
            | "define-funs-rec"
            | "define-sort"
            | "echo"
            | "exit"
            | "get-assertions"
            | "get-assignment"
            | "get-info"
            | "get-model"
            | "get-option"
            | "get-proof"
            | "get-unsat-assumptions"
            | "get-unsat-core"
            | "get-value"
            | "pop"
            | "push"
            | "reset"
            | "reset-assertions"
            | "set-info"
            | "set-logic"
            | "set-option"
    ) {
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
    ///
    /// The spelling of every node lives in exactly one place,
    /// [`Formula::write_smtlib_node`]; this tree printer is its trivial
    /// instance (every child slot is the child's own full text), and
    /// [`crate::formula_dag::FormulaDag::to_smtlib`] is its sharing instance.
    /// The walk is iterative, so the depth of the formula is bounded by memory,
    /// not by the thread's stack.
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        let mut out = String::new();
        self.write_smtlib(&mut out);
        out
    }

    /// Append [`Formula::to_smtlib`]'s text to `out`.
    ///
    /// Iterative: an explicit stack of frames replaces recursion. Each frame
    /// holds one node's own spelling (rendered once by
    /// [`Formula::write_smtlib_node`]), the positions in it where child texts
    /// go, and the node's children; the frames on the stack share three
    /// arenas that are truncated as frames pop, so the working memory is
    /// proportional to the depth of the walk plus the spellings and child
    /// lists along it, and an n-ary node costs O(n), not O(n) per slot.
    pub fn write_smtlib(&self, out: &mut String) {
        struct Frame {
            text_start: usize,
            text_end: usize,
            emitted: usize,
            slot_start: usize,
            slot_next: usize,
            slot_end: usize,
            kid_start: usize,
        }

        /// The arenas the frames on the stack share. Each is truncated to a
        /// frame's start when the frame pops (frames are LIFO), so a level of
        /// the walk holds no allocation of its own.
        struct Arenas<'a> {
            /// The frames' own spellings.
            text: String,
            /// The frames' child slots: (position in `text`, child index).
            slots: Vec<(usize, usize)>,
            /// The frames' children, so a slot finds its child in O(1) (an
            /// n-ary node is not re-listed per slot).
            kids: Vec<&'a Formula>,
        }

        fn push<'a>(stack: &mut Vec<Frame>, node: &'a Formula, arenas: &mut Arenas<'a>) {
            let text_start = arenas.text.len();
            let slot_start = arenas.slots.len();
            let kid_start = arenas.kids.len();
            let slots = &mut arenas.slots;
            node.write_smtlib_node(&mut arenas.text, &mut |i, out| slots.push((out.len(), i)));
            arenas.kids.extend(node.children());
            stack.push(Frame {
                text_start,
                text_end: arenas.text.len(),
                emitted: text_start,
                slot_start,
                slot_next: slot_start,
                slot_end: arenas.slots.len(),
                kid_start,
            });
        }

        let mut arenas = Arenas {
            text: String::new(),
            slots: Vec::new(),
            kids: Vec::new(),
        };
        let mut stack: Vec<Frame> = Vec::new();
        push(&mut stack, self, &mut arenas);
        while let Some(top) = stack.last_mut() {
            if top.slot_next < top.slot_end {
                let (pos, child) = arenas.slots[top.slot_next];
                top.slot_next += 1;
                out.push_str(&arenas.text[top.emitted..pos]);
                top.emitted = pos;
                let kid = arenas.kids[top.kid_start + child];
                push(&mut stack, kid, &mut arenas);
            } else {
                out.push_str(&arenas.text[top.emitted..top.text_end]);
                let (text_start, slot_start, kid_start) =
                    (top.text_start, top.slot_start, top.kid_start);
                stack.pop();
                arenas.text.truncate(text_start);
                arenas.slots.truncate(slot_start);
                arenas.kids.truncate(kid_start);
            }
        }
    }

    /// Append THIS node's SMT-LIB2 spelling to `out`, calling `child(i, out)`
    /// at each place where the text of child `i` (in [`Formula::children`]
    /// order) belongs.
    ///
    /// This is the single source of the SMT-LIB spelling of every variant.
    /// The node's own children are never read: only their number is (an
    /// empty `And` is `true`, a one-element `And` is its element, a nullary
    /// `Pred` is a bare symbol). So the same function spells a tree node (the
    /// callback prints the child subtree), a [`crate::formula_dag::Shell`]
    /// (through [`crate::formula_dag::Shell::write_smtlib_node`], which
    /// supplies the arity a shell's empty n-ary child list does not hold),
    /// and a sharing printer's node (the callback prints a `let`-bound name).
    ///
    /// A child may be called more than once: the truncating `Div`/`Rem`, the
    /// signed `BvToInt` and the saturating `FpToSbv`/`FpToUbv` spell an
    /// operand several times. A tree printer repeats the operand's text; a
    /// sharing printer counts the calls and binds the operand once.
    ///
    /// ```
    /// use trust_ir_contract::{Formula, Sort};
    ///
    /// let x = Formula::Var("x".into(), Sort::Int);
    /// let f = Formula::Rem(Box::new(x), Box::new(Formula::Int(3)));
    /// let mut calls = Vec::new();
    /// let mut own = String::new();
    /// f.write_smtlib_node(&mut own, &mut |i, out| {
    ///     calls.push(i);
    ///     out.push_str(["A", "B"][i]);
    /// });
    /// assert_eq!(own, "(ite (>= A 0) (mod A B) (- (mod (- A) B)))");
    /// assert_eq!(calls, [0, 0, 1, 0, 1]);
    /// assert_eq!(f.to_smtlib(), "(ite (>= x 0) (mod x 3) (- (mod (- x) 3)))");
    /// ```
    pub fn write_smtlib_node(&self, out: &mut String, child: &mut dyn FnMut(usize, &mut String)) {
        self.write_smtlib_node_with(None, out, child);
    }

    /// [`Formula::write_smtlib_node`] for a SHELL (see
    /// `crate::formula_dag::Shell`): an n-ary node's (`And`, `Or`, `Pred`,
    /// `Ctor`, `FnApp`) child count is `arity`, not the length of its child
    /// list, which a shell keeps empty. Every other variant fixes its own
    /// arity and ignores `arity`.
    pub(crate) fn write_smtlib_shell(
        &self,
        arity: usize,
        out: &mut String,
        child: &mut dyn FnMut(usize, &mut String),
    ) {
        self.write_smtlib_node_with(Some(arity), out, child);
    }

    /// The one spelling of every variant. `nary` overrides the child count
    /// of an n-ary node (a shell's); `None` reads it from the child list.
    #[allow(clippy::too_many_lines)] // one arm per variant, by design
    fn write_smtlib_node_with(
        &self,
        nary: Option<usize>,
        out: &mut String,
        child: &mut dyn FnMut(usize, &mut String),
    ) {
        /// `(head c0)`.
        fn app1(out: &mut String, child: &mut dyn FnMut(usize, &mut String), head: &str) {
            out.push('(');
            out.push_str(head);
            out.push(' ');
            child(0, out);
            out.push(')');
        }
        /// `(head c0 c1 … c{n-1})`.
        fn app(out: &mut String, child: &mut dyn FnMut(usize, &mut String), head: &str, n: usize) {
            out.push('(');
            out.push_str(head);
            for i in 0..n {
                out.push(' ');
                child(i, out);
            }
            out.push(')');
        }
        /// The truncated remainder `trem(a, b) = ite(a >= 0, mod(a,b),
        /// -mod(-a,b))`, operands at child slots 0 and 1.
        fn trem(out: &mut String, child: &mut dyn FnMut(usize, &mut String)) {
            out.push_str("(ite (>= ");
            child(0, out);
            out.push_str(" 0) (mod ");
            child(0, out);
            out.push(' ');
            child(1, out);
            out.push_str(") (- (mod (- ");
            child(0, out);
            out.push_str(") ");
            child(1, out);
            out.push_str(")))");
        }

        match self {
            // Literals
            Formula::Bool(true) => out.push_str("true"),
            Formula::Bool(false) => out.push_str("false"),
            Formula::UInt(n) => out.push_str(&n.to_string()),
            Formula::Int(n) => {
                if *n < 0 {
                    let abs = n.unsigned_abs();
                    out.push_str(&format!("(- {abs})"));
                } else {
                    out.push_str(&n.to_string());
                }
            }
            Formula::BitVec { value, width } => {
                if *value >= 0 {
                    out.push_str(&format!("(_ bv{value} {width})"));
                } else {
                    // Use u128 for two's complement to handle width=128 correctly.
                    // i128 mask overflows at width=128; u128::MAX is the correct all-ones mask.
                    let mask: u128 = if *width < 128 {
                        (1u128 << width) - 1
                    } else {
                        u128::MAX
                    };
                    let twos_comp = (*value as u128) & mask;
                    out.push_str(&format!("(_ bv{twos_comp} {width})"));
                }
            }

            // Variables
            Formula::Var(name, _sort) => out.push_str(&escape_smtlib_symbol(name)),
            Formula::SymVar(sym, _sort) => out.push_str(&escape_smtlib_symbol(sym.as_str())),

            // Boolean connectives
            Formula::Not(_) => app1(out, child, "not"),
            Formula::And(terms) => match nary.unwrap_or(terms.len()) {
                0 => out.push_str("true"),
                1 => child(0, out),
                n => app(out, child, "and", n),
            },
            Formula::Or(terms) => match nary.unwrap_or(terms.len()) {
                0 => out.push_str("false"),
                1 => child(0, out),
                n => app(out, child, "or", n),
            },
            Formula::Implies(..) => app(out, child, "=>", 2),

            // Comparisons
            Formula::Eq(..) => app(out, child, "=", 2),
            Formula::Lt(..) => app(out, child, "<", 2),
            Formula::Le(..) => app(out, child, "<=", 2),
            Formula::Gt(..) => app(out, child, ">", 2),
            Formula::Ge(..) => app(out, child, ">=", 2),

            // Integer arithmetic
            Formula::Add(..) => app(out, child, "+", 2),
            Formula::Sub(..) => app(out, child, "-", 2),
            Formula::Mul(..) => app(out, child, "*", 2),
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
            Formula::Rem(..) => trem(out, child),
            Formula::Div(..) => {
                // a == b*tdiv + trem, so tdiv = (a - trem)/b is an EXACT division
                // (remainder 0) where Euclidean `div` agrees with truncation.
                out.push_str("(div (- ");
                child(0, out);
                out.push(' ');
                trem(out, child);
                out.push_str(") ");
                child(1, out);
                out.push(')');
            }
            Formula::Neg(_) => app1(out, child, "-"),

            // Bitvector arithmetic
            Formula::BvAdd(..) => app(out, child, "bvadd", 2),
            Formula::BvSub(..) => app(out, child, "bvsub", 2),
            Formula::BvMul(..) => app(out, child, "bvmul", 2),
            Formula::BvUDiv(..) => app(out, child, "bvudiv", 2),
            Formula::BvSDiv(..) => app(out, child, "bvsdiv", 2),
            Formula::BvURem(..) => app(out, child, "bvurem", 2),
            Formula::BvSRem(..) => app(out, child, "bvsrem", 2),
            Formula::BvAnd(..) => app(out, child, "bvand", 2),
            Formula::BvOr(..) => app(out, child, "bvor", 2),
            Formula::BvXor(..) => app(out, child, "bvxor", 2),
            Formula::BvNot(..) => app1(out, child, "bvnot"),
            Formula::BvShl(..) => app(out, child, "bvshl", 2),
            Formula::BvLShr(..) => app(out, child, "bvlshr", 2),
            Formula::BvAShr(..) => app(out, child, "bvashr", 2),

            // Bitvector comparisons
            Formula::BvULt(..) => app(out, child, "bvult", 2),
            Formula::BvULe(..) => app(out, child, "bvule", 2),
            Formula::BvSLt(..) => app(out, child, "bvslt", 2),
            Formula::BvSLe(..) => app(out, child, "bvsle", 2),

            // Bitvector conversions
            //
            // SMT-LIB FixedSizeBitVectors defines `bv2nat` (unsigned) and lets the
            // caller build signed conversion by subtracting 2^N when the sign bit is
            // set. We emit the SMT-LIB-standard name (`bv2nat`). A legacy spelling
            // (`bv2int`) exists in some non-standard solver dialects, but `ay`
            // recognizes only the standard form.
            Formula::BvToInt(_, width, signed) => {
                if *signed {
                    let two_to_width = pow2_decimal(*width);
                    out.push_str("(ite (bvsge ");
                    child(0, out);
                    out.push_str(&format!(" (_ bv0 {width})) (bv2nat "));
                    child(0, out);
                    out.push_str(") (- (bv2nat ");
                    child(0, out);
                    out.push_str(&format!(") {two_to_width}))"));
                } else {
                    app1(out, child, "bv2nat");
                }
            }
            Formula::IntToBv(_, width) => app1(out, child, &format!("(_ int2bv {width})")),
            Formula::BvExtract { high, low, .. } => {
                app1(out, child, &format!("(_ extract {high} {low})"));
            }
            Formula::BvConcat(..) => app(out, child, "concat", 2),
            Formula::BvZeroExt(_, bits) => app1(out, child, &format!("(_ zero_extend {bits})")),
            Formula::BvSignExt(_, bits) => app1(out, child, &format!("(_ sign_extend {bits})")),

            // Conditional
            Formula::Ite(..) => app(out, child, "ite", 3),

            // Quantifiers
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
                out.push_str(if matches!(self, Formula::Forall(..)) {
                    "(forall ("
                } else {
                    "(exists ("
                });
                for (i, (name, sort)) in bindings.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push('(');
                    out.push_str(&escape_smtlib_symbol(name.as_str()));
                    out.push(' ');
                    out.push_str(&sort.to_smtlib());
                    out.push(')');
                }
                out.push_str(") ");
                child(0, out);
                out.push(')');
            }

            // Arrays
            Formula::Select(..) => app(out, child, "select", 2),
            Formula::Store(..) => app(out, child, "store", 3),

            // ── IEEE-754 floating point (SMT-LIB FloatingPoint theory) ──────
            Formula::FpConst { bits, eb, sb } => {
                out.push_str(&format!("((_ to_fp {eb} {sb}) (_ bv{bits} {}))", eb + sb));
            }
            Formula::FpNaN { eb, sb } => out.push_str(&format!("(_ NaN {eb} {sb})")),
            Formula::FpInf { neg, eb, sb } => {
                if *neg {
                    out.push_str(&format!("(_ -oo {eb} {sb})"));
                } else {
                    out.push_str(&format!("(_ +oo {eb} {sb})"));
                }
            }
            Formula::FpZero { neg, eb, sb } => {
                if *neg {
                    out.push_str(&format!("(_ -zero {eb} {sb})"));
                } else {
                    out.push_str(&format!("(_ +zero {eb} {sb})"));
                }
            }
            Formula::FpRoundingMode(rm) => out.push_str(rm.to_smtlib()),
            Formula::FpAdd(..) => app(out, child, "fp.add", 3),
            Formula::FpSub(..) => app(out, child, "fp.sub", 3),
            Formula::FpMul(..) => app(out, child, "fp.mul", 3),
            Formula::FpDiv(..) => app(out, child, "fp.div", 3),
            Formula::FpFma(..) => app(out, child, "fp.fma", 4),
            Formula::FpSqrt(..) => app(out, child, "fp.sqrt", 2),
            Formula::FpRem(..) => app(out, child, "fp.rem", 2),
            Formula::FpNeg(_) => app1(out, child, "fp.neg"),
            Formula::FpAbs(_) => app1(out, child, "fp.abs"),
            Formula::FpMin(..) => app(out, child, "fp.min", 2),
            Formula::FpMax(..) => app(out, child, "fp.max", 2),
            Formula::FpEq(..) => app(out, child, "fp.eq", 2),
            Formula::FpLt(..) => app(out, child, "fp.lt", 2),
            Formula::FpLe(..) => app(out, child, "fp.leq", 2),
            Formula::FpGt(..) => app(out, child, "fp.gt", 2),
            Formula::FpGe(..) => app(out, child, "fp.geq", 2),
            Formula::FpIsNaN(_) => app1(out, child, "fp.isNaN"),
            Formula::FpIsInfinite(_) => app1(out, child, "fp.isInfinite"),
            Formula::FpIsZero(_) => app1(out, child, "fp.isZero"),
            Formula::FpIsNormal(_) => app1(out, child, "fp.isNormal"),
            Formula::FpIsSubnormal(_) => app1(out, child, "fp.isSubnormal"),
            Formula::FpIsNegative(_) => app1(out, child, "fp.isNegative"),
            Formula::FpIsPositive(_) => app1(out, child, "fp.isPositive"),
            Formula::FpFromBits { eb, sb, .. } => {
                app1(out, child, &format!("(_ to_fp {eb} {sb})"));
            }
            // FP -> BV bit reinterpret (inverse of `to_fp` on a bit pattern). The
            // result width is inferred by the solver from the inner FP sort, so no
            // width index is carried. The concrete solver lowering / bijection
            // axioms are applied by the `trust-types` ay bridge downstream.
            Formula::FpToIeeeBv(_) => app1(out, child, "fp.to_ieee_bv"),
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
            //
            // The clamp CONSTANTS are built with `scaled_pow2_decimal`, not
            // `1u128 << n`. `width` is a `u32` and nothing in this contract
            // bounds it, while a u128 shift is defined only to 127 — so the
            // shift spelling was exact only to width 125 (signed, whose
            // widest shift count is `w + 2`) and 127 (unsigned). Above that
            // it panicked in debug and, worse, MASKED the shift count in
            // release: `1u128 << 128 == 1`, a silently wrong bound with no
            // diagnostic. The native lane (trust's `ay_bridge`
            // `fp_to_bv_saturating`) has always computed these same constants
            // in bignum arithmetic, so the two lanes used to clamp
            // DIFFERENTLY above width 125/127. They no longer do: these
            // constants are now exact at every width, constant for constant
            // and literal-width for literal-width.
            //
            // Child slots: 0 is the rounding mode, 1 the operand `x`, which
            // the expansion spells four times.
            Formula::FpToSbv { width, eb, sb, .. } => {
                let w = *width;
                // Width 0 is not a legal SMT-LIB bitvector width and every
                // consumer refuses it upstream; saturate rather than
                // underflow so this formatter stays total.
                let hi = w.saturating_sub(1);
                // 2^(w-1) as an unsigned (w+1)-bit literal, in the operand's format.
                let pos = format!(
                    "((_ to_fp_unsigned {eb} {sb}) RNE (_ bv{} {}))",
                    pow2_decimal(hi),
                    w + 1
                );
                // -(2^(w-1)) - 1 as a signed (w+2)-bit literal. In two's
                // complement on w+2 bits that is 2^(w+2) - 2^(w-1) - 1, i.e.
                // 7 * 2^(w-1) - 1.
                let min_minus_one = scaled_pow2_decimal(7, hi, true);
                let neg = format!("((_ to_fp {eb} {sb}) RNE (_ bv{min_minus_one} {}))", w + 2);
                let max_bv = format!("(_ bv{} {w})", scaled_pow2_decimal(1, hi, true));
                let min_bv = format!("(_ bv{} {w})", pow2_decimal(hi));
                out.push_str("(ite (fp.isNaN ");
                child(1, out);
                out.push_str(&format!(") (_ bv0 {w}) (ite (fp.geq "));
                child(1, out);
                out.push_str(&format!(" {pos}) {max_bv} (ite (fp.leq "));
                child(1, out);
                out.push_str(&format!(" {neg}) {min_bv} ((_ fp.to_sbv {w}) "));
                child(0, out);
                out.push(' ');
                child(1, out);
                out.push_str("))))");
            }
            Formula::FpToUbv { width, eb, sb, .. } => {
                let w = *width;
                // 2^w as an unsigned (w+1)-bit literal.
                let pos = format!(
                    "((_ to_fp_unsigned {eb} {sb}) RNE (_ bv{} {}))",
                    pow2_decimal(w),
                    w + 1
                );
                // -1.0 in the operand's format.
                let neg_one = format!(
                    "(fp.neg ((_ to_fp_unsigned {eb} {sb}) RNE (_ bv1 {})))",
                    w + 1
                );
                let max_bv = format!("(_ bv{} {w})", scaled_pow2_decimal(1, w, true));
                out.push_str("(ite (fp.isNaN ");
                child(1, out);
                out.push_str(&format!(") (_ bv0 {w}) (ite (fp.geq "));
                child(1, out);
                out.push_str(&format!(" {pos}) {max_bv} (ite (fp.leq "));
                child(1, out);
                out.push_str(&format!(" {neg_one}) (_ bv0 {w}) ((_ fp.to_ubv {w}) "));
                child(0, out);
                out.push(' ');
                child(1, out);
                out.push_str("))))");
            }
            Formula::FpFromSbv { eb, sb, .. } | Formula::FpConvert { eb, sb, .. } => {
                app(out, child, &format!("(_ to_fp {eb} {sb})"), 2);
            }
            Formula::FpFromUbv { eb, sb, .. } => {
                app(out, child, &format!("(_ to_fp_unsigned {eb} {sb})"), 2);
            }

            // Uninterpreted predicate application (EUF). Lowers to a bare symbol
            // when nullary, or `(name arg1 ..)` otherwise. The symbol's
            // `(declare-fun name (<arg-sorts>) Bool)` is emitted once by the
            // backend's declaration collector; the application is opaque to the
            // solver (no axioms).
            Formula::Pred(name, args) => {
                let sym = escape_smtlib_symbol(name.as_str());
                match nary.unwrap_or(args.len()) {
                    0 => out.push_str(&sym),
                    n => app(out, child, &sym, n),
                }
            }

            // ── Algebraic-datatype terms (Lever A) ──────────────────────────
            // The `(declare-datatype …)` that DEFINES the sort is emitted
            // separately from the datatype-sorted variable's `Sort`
            // (`Sort::datatype_declarations`); here we only reference its
            // constructors/selectors/testers.
            Formula::Ctor { ctor, args, sort } => {
                let ctor_sym = escape_smtlib_symbol(ctor);
                let n = nary.unwrap_or(args.len());
                if n == 0 {
                    // A nullary constructor is a bare constant, not a 0-ary
                    // application; qualify it with its datatype sort
                    // (`(as C Sort)`) so constructors shared across datatype
                    // families are unambiguous — matches the in-process ay path.
                    out.push_str(&format!("(as {} {})", ctor_sym, sort.to_smtlib()));
                } else {
                    app(out, child, &ctor_sym, n);
                }
            }
            Formula::Sel { field, .. } => app1(out, child, &escape_smtlib_symbol(field)),
            Formula::IsCtor { ctor, .. } => {
                app1(
                    out,
                    child,
                    &format!("(_ is {})", escape_smtlib_symbol(ctor)),
                );
            }

            // Uninterpreted function application (EUF). Lowers like `Pred` —
            // a bare symbol when nullary, `(func arg1 ..)` otherwise; the
            // result-sorted `declare-fun` is the backend's job.
            Formula::FnApp { func, args, .. } => {
                let sym = escape_smtlib_symbol(func);
                match nary.unwrap_or(args.len()) {
                    0 => out.push_str(&sym),
                    n => app(out, child, &sym, n),
                }
            }

            // Exact rational literal (`Reals` theory): `(/ n d)`, `(- n)` for a
            // negative numerator, a bare numeral when integral.
            Formula::Rat(lit) => out.push_str(&lit.to_smtlib()),

            // Constant array: the sort-qualified `const` of the full array
            // sort, applied to the element. Spelled from the two carried sorts
            // directly; the text is exactly `Sort::Array(I, E).to_smtlib()`
            // (a test holds the two spellings together) without cloning
            // either sort into one.
            Formula::ConstArray {
                index_sort,
                elem_sort,
                ..
            } => {
                let head = format!(
                    "(as const (Array {} {}))",
                    index_sort.to_smtlib(),
                    elem_sort.to_smtlib()
                );
                app1(out, child, &head);
            }
        }
    }
}

#[cfg(test)]
mod rat_literal_tests {
    use super::*;

    #[test]
    fn rat_to_smtlib_is_a_reals_theory_term() {
        assert_eq!(Formula::rat("1", "2").unwrap().to_smtlib(), "(/ 1 2)");
        assert_eq!(Formula::rat("-1", "2").unwrap().to_smtlib(), "(/ (- 1) 2)");
        assert_eq!(Formula::rat("0", "1").unwrap().to_smtlib(), "0");
        assert_eq!(Formula::rat("-3", "1").unwrap().to_smtlib(), "(- 3)");
        assert_eq!(Formula::rat_from_int(-9).to_smtlib(), "(- 9)");
        assert_eq!(
            Formula::rat_from_int(i128::MIN).to_smtlib(),
            "(- 170141183460469231731687303715884105728)"
        );
        // The literal is opaque to the SMT symbol escaper: digits only.
        let big = "340282366920938463463374607431768211457"; // 2^128 + 1
        assert_eq!(
            Formula::rat(big, "3").unwrap().to_smtlib(),
            format!("(/ {big} 3)")
        );
    }

    #[test]
    fn rat_is_a_leaf_for_children_and_map_children() {
        let r = Formula::rat("7", "3").unwrap();
        assert!(r.children().is_empty());
        let mapped = r.clone().map_children(&mut |_| Formula::Bool(false));
        assert_eq!(mapped, r);
        assert_eq!(r.rat_parts(), Some(("7", "3")));
        assert_eq!(Formula::Int(7).rat_parts(), None);
        assert!(r.free_variables().is_empty());
    }

    #[test]
    fn rat_round_trips_through_serde_and_is_structurally_compared() {
        let r = Formula::rat("-22", "7").unwrap();
        let json = serde_json::to_string(&r).expect("serialize");
        // The newtype payload is invisible on the wire: exactly the shape a
        // `Rat { num, den }` struct variant would have.
        assert_eq!(json, r#"{"Rat":{"num":"-22","den":"7"}}"#);
        let back: Formula = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, r);
        // Structural, not value, equality: reducedness is the producer's job.
        assert_ne!(
            Formula::rat("2", "4").unwrap(),
            Formula::rat("1", "2").unwrap()
        );
    }

    /// A malformed literal cannot be smuggled in through deserialization: the
    /// same canonical-syntax check that guards the constructor guards the
    /// wire, so every `Formula::Rat` that exists parses exactly.
    #[test]
    fn rat_deserialization_rejects_non_canonical_digits() {
        for text in [
            r#"{"Rat":{"num":"01","den":"2"}}"#,
            r#"{"Rat":{"num":"1","den":"0"}}"#,
            r#"{"Rat":{"num":"-0","den":"1"}}"#,
            r#"{"Rat":{"num":"1","den":"-2"}}"#,
            r#"{"Rat":{"num":"0x10","den":"1"}}"#,
        ] {
            assert!(
                serde_json::from_str::<Formula>(text).is_err(),
                "{text} must be refused at the wire"
            );
        }
        // …while a canonical one inside a larger formula still round-trips.
        let f = Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Real)),
            Box::new(Formula::rat("7", "3").unwrap()),
        );
        let json = serde_json::to_string(&f).expect("serialize");
        let back: Formula = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, f);
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
    fn scaled_pow2_decimal_multiplies_and_borrows_exactly() {
        use super::scaled_pow2_decimal;
        // multiplier only
        assert_eq!(scaled_pow2_decimal(7, 0, false), "7");
        assert_eq!(scaled_pow2_decimal(7, 3, false), "56");
        // the minus-one borrow, including the all-nines chain and the
        // leading-zero strip it leaves behind
        assert_eq!(scaled_pow2_decimal(1, 0, true), "0");
        assert_eq!(scaled_pow2_decimal(1, 4, true), "15");
        assert_eq!(scaled_pow2_decimal(5, 1, true), "9"); // 10 - 1, borrows
        assert_eq!(scaled_pow2_decimal(125, 3, true), "999"); // 1000 - 1
        // the shape the signed FP clamp needs: 2^(w+2) - 2^(w-1) - 1 is
        // 7 * 2^(w-1) - 1. Cross-checked against u128 at w = 8.
        assert_eq!(
            scaled_pow2_decimal(7, 7, true),
            ((1u128 << 10) - (1u128 << 7) - 1).to_string()
        );
        // past the u128 ceiling
        assert_eq!(
            scaled_pow2_decimal(7, 127, true),
            "1190988284223284622121811126011188740095"
        );
        // zero multiplier is answered, not borrowed past
        assert_eq!(scaled_pow2_decimal(0, 9, true), "0");
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

    // ------------------------------------------------------------------
    // Saturating FP -> BV clamp constants.
    //
    // The guarded expansion's bounds used to be built with `1u128 << n`.
    // `width` is a `u32` and nothing in this contract bounds it, while a u128
    // shift is defined only to 127 — and the two arms shift by different
    // amounts, so the old spelling was exact only to w = 125 (signed, whose
    // widest shift count is `w + 2`) and w = 127 (unsigned, which shifts by
    // `w`). Past those bounds it panicked in debug and MASKED the shift count
    // in release (`1u128 << 128 == 1`), emitting a silently wrong bound.
    //
    // Two obligations, one test each:
    //   1. where the shift was defined, the text is BYTE-IDENTICAL to before;
    //   2. above it, the text is now exact.
    // ------------------------------------------------------------------

    /// The full signed expansion, assembled from the three decimal constants
    /// it carries: `pos` = 2^(w-1) (a w+1-bit literal), `min_minus_one` =
    /// 2^(w+2) - 2^(w-1) - 1 (a w+2-bit literal), `max` = 2^(w-1) - 1. The
    /// clamp value on the low side is `pos` again, at width w.
    fn expected_sbv(w: u32, pos: &str, min_minus_one: &str, max: &str) -> String {
        format!(
            "(ite (fp.isNaN x) (_ bv0 {w}) \
             (ite (fp.geq x ((_ to_fp_unsigned {EB} {SB}) RNE (_ bv{pos} {}))) (_ bv{max} {w}) \
             (ite (fp.leq x ((_ to_fp {EB} {SB}) RNE (_ bv{min_minus_one} {}))) (_ bv{pos} {w}) \
             ((_ fp.to_sbv {w}) RNE x))))",
            w + 1,
            w + 2
        )
    }

    /// The full unsigned expansion: `pos` = 2^w (a w+1-bit literal), `max` =
    /// 2^w - 1. The low guard is -1.0, built from a 1-valued w+1-bit literal.
    fn expected_ubv(w: u32, pos: &str, max: &str) -> String {
        format!(
            "(ite (fp.isNaN x) (_ bv0 {w}) \
             (ite (fp.geq x ((_ to_fp_unsigned {EB} {SB}) RNE (_ bv{pos} {}))) (_ bv{max} {w}) \
             (ite (fp.leq x (fp.neg ((_ to_fp_unsigned {EB} {SB}) RNE (_ bv1 {})))) (_ bv0 {w}) \
             ((_ fp.to_ubv {w}) RNE x))))",
            w + 1,
            w + 1
        )
    }

    fn sbv_text(w: u32) -> String {
        Formula::FpToSbv {
            rm: rne(),
            value: fv("x"),
            width: w,
            eb: EB,
            sb: SB,
        }
        .to_smtlib()
    }

    fn ubv_text(w: u32) -> String {
        Formula::FpToUbv {
            rm: rne(),
            value: fv("x"),
            width: w,
            eb: EB,
            sb: SB,
        }
        .to_smtlib()
    }

    #[test]
    fn clamp_text_is_byte_identical_where_the_u128_shift_was_defined() {
        // Signed: the widest shift count is `w + 2`, so `w <= 125`.
        for w in 1u32..=125 {
            let pos = (1u128 << (w - 1)).to_string();
            let min_minus_one = ((1u128 << (w + 2)) - (1u128 << (w - 1)) - 1).to_string();
            let max = ((1u128 << (w - 1)) - 1).to_string();
            assert_eq!(
                sbv_text(w),
                expected_sbv(w, &pos, &min_minus_one, &max),
                "signed width {w} must be unchanged"
            );
        }
        // Unsigned: the only shift count is `w`, so `w <= 127`.
        for w in 1u32..=127 {
            let pos = (1u128 << w).to_string();
            let max = ((1u128 << w) - 1).to_string();
            assert_eq!(
                ubv_text(w),
                expected_ubv(w, &pos, &max),
                "unsigned width {w} must be unchanged"
            );
        }
    }

    #[test]
    fn clamp_constants_are_exact_above_the_u128_bound() {
        // (width, 2^(w-1), 7*2^(w-1) - 1, 2^(w-1) - 1), computed off-machine.
        // 126 and 127 are the two widths the signed arm used to get wrong
        // while the unsigned arm was still right; 128 and up were wrong in
        // both.
        let signed: &[(u32, &str, &str, &str)] = &[
            (
                126,
                "42535295865117307932921825928971026432",
                "297747071055821155530452781502797185023",
                "42535295865117307932921825928971026431",
            ),
            (
                127,
                "85070591730234615865843651857942052864",
                "595494142111642311060905563005594370047",
                "85070591730234615865843651857942052863",
            ),
            (
                128,
                "170141183460469231731687303715884105728",
                "1190988284223284622121811126011188740095",
                "170141183460469231731687303715884105727",
            ),
            (
                200,
                "803469022129495137770981046170581301261101496891396417650688",
                "5624283154906465964396867323194069108827710478239774923554815",
                "803469022129495137770981046170581301261101496891396417650687",
            ),
        ];
        for (w, pos, min_minus_one, max) in signed {
            assert_eq!(
                sbv_text(*w),
                expected_sbv(*w, pos, min_minus_one, max),
                "signed width {w}"
            );
        }

        // (width, 2^w, 2^w - 1).
        let unsigned: &[(u32, &str, &str)] = &[
            (
                128,
                "340282366920938463463374607431768211456",
                "340282366920938463463374607431768211455",
            ),
            (
                200,
                "1606938044258990275541962092341162602522202993782792835301376",
                "1606938044258990275541962092341162602522202993782792835301375",
            ),
        ];
        for (w, pos, max) in unsigned {
            assert_eq!(
                ubv_text(*w),
                expected_ubv(*w, pos, max),
                "unsigned width {w}"
            );
        }
    }

    /// `width` is a `u32`, so the contract carries widths far past any machine
    /// integer. 1024 is well above the 1000 the u128 spelling could not have
    /// reached by any margin, and the emitted literal is the exact 2^1023.
    #[test]
    fn clamp_constants_are_exact_at_a_four_figure_width() {
        let pow_1023 = "89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608";
        let seven_1023_minus_one = "629192597201810567705256816776158656766291942629807300457005284052064365319253370964479670628426376073920398579549876751805764190850458178724966007238159435322187626987029198467057768604361329418085790332297520190933527388198620085158695886892895330071726787396052043839815360784679007066923747153684784480255";
        let pow_1023_minus_one = "89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068607";
        assert_eq!(
            sbv_text(1024),
            expected_sbv(1024, pow_1023, seven_1023_minus_one, pow_1023_minus_one),
            "signed width 1024"
        );

        let pow_1024 = "179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216";
        let pow_1024_minus_one = "179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215";
        assert_eq!(
            ubv_text(1024),
            expected_ubv(1024, pow_1024, pow_1024_minus_one),
            "unsigned width 1024"
        );
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

#[cfg(test)]
mod const_array_tests {
    //! `Formula::ConstArray`, the constant-size uniform array `[v; N]`: the
    //! SMT-LIB text it lowers to, its walks, its serde shape, and that its
    //! size does not depend on `N`. The solver-side meaning (select of it is
    //! its value, stores over it) is checked against ay in
    //! `trust-ir-ay/tests/formula_const_array.rs`.
    use super::*;

    fn bv8(value: i128) -> Formula {
        Formula::BitVec { value, width: 8 }
    }

    fn arr_var(name: &str, index: Sort, elem: Sort) -> Formula {
        Formula::Var(name.into(), Sort::Array(Box::new(index), Box::new(elem)))
    }

    #[test]
    fn const_array_lowers_to_sort_qualified_const() {
        let int_int = Formula::const_array(Sort::Int, Sort::Int, Formula::Int(7));
        assert_eq!(int_int.to_smtlib(), "((as const (Array Int Int)) 7)");

        let bv = Formula::const_array(Sort::BitVec(64), Sort::BitVec(8), bv8(-1));
        assert_eq!(
            bv.to_smtlib(),
            "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv255 8))"
        );

        // The qualifier is spelled from the two carried sorts; it must be
        // exactly the full array sort's own spelling, nested arrays included.
        let inner = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool));
        let nested = Formula::const_array(
            Sort::BitVec(32),
            inner.clone(),
            arr_var("row", Sort::Int, Sort::Bool),
        );
        let full = Sort::Array(Box::new(Sort::BitVec(32)), Box::new(inner));
        assert_eq!(
            nested.to_smtlib(),
            format!("((as const {}) row)", full.to_smtlib())
        );
    }

    #[test]
    fn select_and_store_over_a_const_array_render() {
        let base = Formula::const_array(Sort::Int, Sort::BitVec(8), bv8(7));
        let k = Formula::Var("k".into(), Sort::Int);
        let read = Formula::Select(Box::new(base.clone()), Box::new(k.clone()));
        assert_eq!(
            read.to_smtlib(),
            "(select ((as const (Array Int (_ BitVec 8))) (_ bv7 8)) k)"
        );
        let written = Formula::Store(Box::new(base), Box::new(Formula::Int(3)), Box::new(bv8(9)));
        assert_eq!(
            written.to_smtlib(),
            "(store ((as const (Array Int (_ BitVec 8))) (_ bv7 8)) 3 (_ bv9 8))"
        );
    }

    #[test]
    fn const_array_walks_reach_the_element_and_keep_the_sorts() {
        let v = Formula::Var("v".into(), Sort::BitVec(8));
        let f = Formula::const_array(Sort::Int, Sort::BitVec(8), v);
        assert_eq!(
            f.children().len(),
            1,
            "the element term is the one sub-formula"
        );
        assert!(f.free_variables().contains("v"));

        let renamed = f.rename_var("v", "w");
        assert!(renamed.free_variables().contains("w"));
        assert!(!renamed.free_variables().contains("v"));
        assert_eq!(
            renamed.to_smtlib(),
            "((as const (Array Int (_ BitVec 8))) w)"
        );

        // map rebuilds bottom-up and preserves both sorts.
        let mapped = renamed.map(&mut |g| match g {
            Formula::Var(name, sort) if name == "w" => {
                assert_eq!(sort, Sort::BitVec(8));
                bv8(0)
            }
            other => other,
        });
        assert_eq!(
            mapped,
            Formula::const_array(Sort::Int, Sort::BitVec(8), bv8(0))
        );

        let mut seen = 0;
        mapped.visit(&mut |_| seen += 1);
        assert_eq!(seen, 2, "visit sees the array and its element");
    }

    #[test]
    fn const_array_is_an_array_term() {
        assert!(Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0)).has_arrays());
        // Nested inside another term too.
        let eq = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Select(
                Box::new(Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0))),
                Box::new(Formula::Int(1)),
            )),
        );
        assert!(eq.has_arrays());
    }

    #[test]
    fn const_array_bitvector_sorts_count_as_bitvector_types() {
        // No bitvector anywhere.
        assert!(!Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0)).has_bitvectors());
        // A bitvector INDEX sort is written into the term even though the
        // element is an `Int`.
        assert!(
            Formula::const_array(Sort::BitVec(64), Sort::Int, Formula::Int(0)).has_bitvectors()
        );
        // A bitvector ELEMENT sort whose value is not itself a bitvector term
        // (a read out of an array variable, which `has_bitvectors` does not
        // flag on its own).
        let read = Formula::Select(
            Box::new(arr_var("src", Sort::Int, Sort::BitVec(8))),
            Box::new(Formula::Int(0)),
        );
        assert!(!read.has_bitvectors());
        assert!(Formula::const_array(Sort::Int, Sort::BitVec(8), read).has_bitvectors());
        // …and one nested inside an array element sort.
        let rows = Sort::Array(Box::new(Sort::BitVec(16)), Box::new(Sort::Int));
        assert!(
            Formula::const_array(Sort::Int, rows, arr_var("r", Sort::BitVec(16), Sort::Int))
                .has_bitvectors()
        );
    }

    #[test]
    fn const_array_serde_shape_and_round_trip() {
        let f = Formula::const_array(Sort::Int, Sort::BitVec(8), bv8(7));
        let json = serde_json::to_string(&f).expect("serialize const array");
        assert_eq!(
            json,
            r#"{"ConstArray":{"index_sort":"Int","elem_sort":{"BitVec":8},"value":{"BitVec":{"value":7,"width":8}}}}"#
        );
        let back: Formula = serde_json::from_str(&json).expect("deserialize const array");
        assert_eq!(back, f);

        // Inside a store chain and an equation, with a symbolic element.
        let seed = Formula::Eq(
            Box::new(arr_var("arr$v0", Sort::Int, Sort::BitVec(8))),
            Box::new(Formula::Store(
                Box::new(Formula::const_array(
                    Sort::Int,
                    Sort::BitVec(8),
                    Formula::Var("v".into(), Sort::BitVec(8)),
                )),
                Box::new(Formula::Int(0)),
                Box::new(bv8(1)),
            )),
        );
        let json = serde_json::to_string(&seed).expect("serialize seed");
        let back: Formula = serde_json::from_str(&json).expect("deserialize seed");
        assert_eq!(back, seed);
    }

    /// `[v; N]` stated with a const array is the same term for every `N`:
    /// the length never enters it. A read at the last lane adds one index
    /// literal, whatever `N` is.
    #[test]
    fn uniform_array_statement_is_constant_size_in_n() {
        fn node_count(f: &Formula) -> usize {
            let mut n = 0;
            f.visit(&mut |_| n += 1);
            n
        }
        let arr = || arr_var("arr$v0", Sort::Int, Sort::BitVec(8));
        let seed = || {
            Formula::Eq(
                Box::new(arr()),
                Box::new(Formula::const_array(
                    Sort::Int,
                    Sort::BitVec(8),
                    Formula::Var("v".into(), Sort::BitVec(8)),
                )),
            )
        };
        let reference = seed();
        let mut sizes = Vec::new();
        for n in [2_u64, 64, 65, 1 << 20, 1 << 40, u64::MAX] {
            let stated = seed();
            assert_eq!(
                stated, reference,
                "the statement of [v; {n}] does not mention {n}"
            );
            let last = Formula::Select(Box::new(arr()), Box::new(Formula::UInt(u128::from(n - 1))));
            sizes.push((node_count(&stated), node_count(&last)));
        }
        assert!(
            sizes.windows(2).all(|w| w[0] == w[1]),
            "node counts must not depend on N: {sizes:?}"
        );
        assert_eq!(sizes[0], (4, 3));
    }
}
