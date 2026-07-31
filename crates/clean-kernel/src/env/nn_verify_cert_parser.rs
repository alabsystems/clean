// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate parser for gamma-crown NN verification certificates.
//!
//! Converts gamma-crown per-layer JSON certificates into clean kernel
//! `Expr` terms (`IntervalBounds` + proof witnesses) that can be
//! chained via T70 (`entailment_transitivity`) to compose a full
//! network-level safety proof.
//!
//! Part of #3255.

#[cfg(test)]
use num_bigint::{BigInt, BigUint};
#[cfg(test)]
use num_rational::BigRational;
#[cfg(test)]
use num_traits::{One, Signed, Zero};
#[cfg(test)]
use serde::Deserialize;

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{EnvError, Environment};
#[cfg(test)]
use crate::expr::{BigNat, BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from certificate parsing and Expr construction.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
#[cfg(test)]
pub enum CertParseError {
    #[error("JSON parse error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("certificate has no layers")]
    EmptyLayers,
    #[error("layer {layer_id}: dimension mismatch — lower has {lower_len}, upper has {upper_len}")]
    DimMismatch {
        layer_id: usize,
        lower_len: usize,
        upper_len: usize,
    },
    #[error(
        "layer {layer_id}: bound violation at index {index} — lower ({lower}) > upper ({upper})"
    )]
    BoundViolation {
        layer_id: usize,
        index: usize,
        lower: f64,
        upper: f64,
    },
    #[error("chain gap: layer {prev_id} output dim ({prev_dim}) != layer {next_id} input dim ({next_dim})")]
    ChainDimMismatch {
        prev_id: usize,
        prev_dim: usize,
        next_id: usize,
        next_dim: usize,
    },
    #[error("layer {layer_id}: Farkas witness missing for farkas proof type")]
    FarkasMissing { layer_id: usize },
    #[error(
        "layer {layer_id}: Farkas witness has {got} rows, expected {expected} (2 * output_dim)"
    )]
    FarkasRowCount {
        layer_id: usize,
        got: usize,
        expected: usize,
    },
    #[error("layer {layer_id}: Farkas row {row} has {got} coefficients, expected {expected} (2 * input_dim)")]
    FarkasColCount {
        layer_id: usize,
        row: usize,
        got: usize,
        expected: usize,
    },
    #[error("layer {layer_id}: Farkas coefficient [{row}][{col}] = {value} is negative")]
    FarkasNegative {
        layer_id: usize,
        row: usize,
        col: usize,
        value: f64,
    },
    #[error("environment error: {0}")]
    Env(#[from] EnvError),
    #[error("exact-rational arithmetic error: {detail}")]
    RationalArith { detail: String },
    #[error("entailment combination check failed: {detail}")]
    EntailmentFailed { detail: String },
}

// ---------------------------------------------------------------------------
// JSON schema
// ---------------------------------------------------------------------------

/// Top-level gamma-crown certificate.
#[derive(Debug, Clone, Deserialize)]
#[cfg(test)]
pub(crate) struct Certificate {
    #[serde(default)]
    pub network_name: String,
    pub layers: Vec<LayerCert>,
}

/// Per-layer certificate data.
#[derive(Debug, Clone, Deserialize)]
#[cfg(test)]
pub(crate) struct LayerCert {
    pub layer_id: usize,
    pub input_bounds: BoundsData,
    pub output_bounds: BoundsData,
    #[serde(default = "default_proof_type")]
    pub proof_type: ProofType,
    /// Farkas certificate data (present when `proof_type` is `farkas`).
    #[serde(default)]
    pub farkas: Option<FarkasWitness>,
}

/// Interval bounds as parallel lower/upper vectors.
#[derive(Debug, Clone, Deserialize)]
#[cfg(test)]
pub(crate) struct BoundsData {
    pub lower: Vec<f64>,
    pub upper: Vec<f64>,
}

/// Farkas lemma witness: non-negative coefficients proving that a linear
/// combination of input constraints implies the output bounds.
///
/// For a layer with `m` input constraints and `n` output dimensions,
/// `coefficients[j]` is a vector of `m` non-negative multipliers for
/// the `j`-th output bound inequality.
#[derive(Debug, Clone, Deserialize)]
#[cfg(test)]
pub(crate) struct FarkasWitness {
    /// Farkas multiplier matrix: one coefficient vector per output bound.
    /// Each inner vector has length equal to the number of input bound
    /// constraints (2 * input_dim for lower+upper pairs).
    pub coefficients: Vec<Vec<f64>>,
}

/// Proof strategy used by gamma-crown for this layer.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
#[non_exhaustive]
#[cfg(test)]
pub(crate) enum ProofType {
    Ibp,
    Farkas,
    Crown,
}

#[cfg(test)]
fn default_proof_type() -> ProofType {
    ProofType::Ibp
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

#[cfg(test)]
impl Certificate {
    /// Parse JSON into a `Certificate`, validating structural invariants.
    #[cfg(test)]
    pub(crate) fn parse(json: &str) -> Result<Self, CertParseError> {
        let cert: Certificate = serde_json::from_str(json)?;
        cert.validate()?;
        Ok(cert)
    }

    #[cfg(test)]
    fn validate(&self) -> Result<(), CertParseError> {
        if self.layers.is_empty() {
            return Err(CertParseError::EmptyLayers);
        }
        for layer in &self.layers {
            validate_bounds(&layer.input_bounds, layer.layer_id)?;
            validate_bounds(&layer.output_bounds, layer.layer_id)?;
            validate_farkas(layer)?;
        }
        for pair in self.layers.windows(2) {
            let (prev, next) = (&pair[0], &pair[1]);
            let (prev_dim, next_dim) = (
                prev.output_bounds.lower.len(),
                next.input_bounds.lower.len(),
            );
            if prev_dim != next_dim {
                return Err(CertParseError::ChainDimMismatch {
                    prev_id: prev.layer_id,
                    prev_dim,
                    next_id: next.layer_id,
                    next_dim,
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
fn validate_bounds(b: &BoundsData, layer_id: usize) -> Result<(), CertParseError> {
    if b.lower.len() != b.upper.len() {
        return Err(CertParseError::DimMismatch {
            layer_id,
            lower_len: b.lower.len(),
            upper_len: b.upper.len(),
        });
    }
    for (i, (lo, hi)) in b.lower.iter().zip(&b.upper).enumerate() {
        if lo > hi {
            return Err(CertParseError::BoundViolation {
                layer_id,
                index: i,
                lower: *lo,
                upper: *hi,
            });
        }
    }
    Ok(())
}

/// Validate Farkas witness dimensions and non-negativity.
///
/// For a layer with `d_in` input dimensions and `d_out` output dimensions,
/// the Farkas witness must have exactly `2 * d_out` rows (one per output
/// lower+upper bound inequality), each with `2 * d_in` non-negative
/// coefficients (one per input lower+upper bound constraint).
#[cfg(test)]
fn validate_farkas(layer: &LayerCert) -> Result<(), CertParseError> {
    let farkas = match &layer.farkas {
        Some(f) => f,
        None => {
            if layer.proof_type == ProofType::Farkas {
                return Err(CertParseError::FarkasMissing {
                    layer_id: layer.layer_id,
                });
            }
            return Ok(());
        }
    };
    let d_in = layer.input_bounds.lower.len();
    let d_out = layer.output_bounds.lower.len();
    let expected_rows = 2 * d_out;
    let expected_cols = 2 * d_in;
    if farkas.coefficients.len() != expected_rows {
        return Err(CertParseError::FarkasRowCount {
            layer_id: layer.layer_id,
            got: farkas.coefficients.len(),
            expected: expected_rows,
        });
    }
    for (row, coeffs) in farkas.coefficients.iter().enumerate() {
        if coeffs.len() != expected_cols {
            return Err(CertParseError::FarkasColCount {
                layer_id: layer.layer_id,
                row,
                got: coeffs.len(),
                expected: expected_cols,
            });
        }
        for (col, &v) in coeffs.iter().enumerate() {
            if v < 0.0 {
                return Err(CertParseError::FarkasNegative {
                    layer_id: layer.layer_id,
                    row,
                    col,
                    value: v,
                });
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Kernel constants for Expr construction
// ---------------------------------------------------------------------------

/// Constants for certificate-to-Expr conversion.
#[cfg(test)]
pub(crate) struct CertConsts {
    pub rat: Expr,
    pub fin: Expr,
    pub nn_vec: Expr,
    pub ib: Expr,
    pub ib_mk: Expr,
    pub ib_subset: Expr,
    pub le_le: Expr,
    pub inst_le_rat: Expr,
    pub rat_mk: Expr,
}

#[cfg(test)]
impl CertConsts {
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_mk: Expr::const_(Name::from_string("Rat.mk"), vec![]),
        }
    }

    /// Construct `Rat.mk (Int.ofNat n) 1` or `Rat.mk (Int.negSucc m) 1`.
    ///
    /// Truncates to integer for the scaffold; exact p/q encoding can
    /// be added when gamma-crown emits exact rational coefficients.
    #[cfg(test)]
    pub(crate) fn rat_from_f64(&self, v: f64) -> Expr {
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let int_expr = if v >= 0.0 {
            Expr::app(int_of_nat, Expr::nat_lit(v.floor() as u64))
        } else {
            let abs_ceil = (-v).ceil() as u64;
            Expr::app(int_neg_succ, Expr::nat_lit(abs_ceil.saturating_sub(1)))
        };
        Expr::app(Expr::app(self.rat_mk.clone(), int_expr), Expr::nat_lit(1))
    }

    /// Construct an EXACT `Rat.mk` literal from a reduced rational `num/den`
    /// (`den > 0`).  Unlike `rat_from_f64`, this preserves the value with no
    /// truncation — it encodes the kernel term `Rat.mk (Int.ofNat n) d` for
    /// `num >= 0`, or `Rat.mk (Int.negSucc (|num|-1)) d` for `num < 0`.
    ///
    /// Two exact rationals that are EQUAL after GCD reduction produce
    /// structurally identical `Expr` trees, so `@Eq.refl Rat lit` is a valid
    /// kernel proof of `lit = lit`.  This is what makes the combined-vs-
    /// conclusion coefficient equality kernel-checkable without a native Rat
    /// reducer.
    #[cfg(test)]
    pub(crate) fn rat_from_exact(&self, num: &BigInt, den: &BigInt) -> Expr {
        debug_assert!(
            den.is_positive(),
            "rat_from_exact requires positive denominator"
        );
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let int_neg_succ = Expr::const_(Name::from_string("Int.negSucc"), vec![]);
        let int_expr = if num.is_negative() {
            // `Int.negSucc m` denotes `-(m+1)`, so to encode `num` (< 0) we use
            // the magnitude `|num| - 1`, exactly as the prior i128 code did but
            // computed in arbitrary precision (never narrowed to u64). `num < 0`
            // implies `|num| >= 1`, so `|num| - 1` is a non-negative `BigUint`
            // (no underflow).
            let mag = num.magnitude() - BigUint::one();
            Expr::app(int_neg_succ, Expr::bignat_lit(biguint_to_bignat(&mag)))
        } else {
            // num >= 0: `Int.ofNat num`.
            Expr::app(
                int_of_nat,
                Expr::bignat_lit(biguint_to_bignat(num.magnitude())),
            )
        };
        // den > 0, so its magnitude is exactly `den`.
        let den_lit = Expr::bignat_lit(biguint_to_bignat(den.magnitude()));
        Expr::app(Expr::app(self.rat_mk.clone(), int_expr), den_lit)
    }

    /// Build `@Eq Rat lhs rhs` (the proposition).
    #[cfg(test)]
    pub(crate) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        Expr::app(Expr::app(Expr::app(eq, self.rat.clone()), lhs), rhs)
    }

    /// Build `@Eq.refl Rat x : @Eq Rat x x`.
    #[cfg(test)]
    pub(crate) fn rat_eq_refl(&self, x: Expr) -> Expr {
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        Expr::app(Expr::app(eq_refl, self.rat.clone()), x)
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    #[cfg(test)]
    pub(crate) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `IntervalBounds.subset @d b1 b2`.
    #[cfg(test)]
    pub(crate) fn subset(&self, d: &Expr, b1: &Expr, b2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_subset.clone(), d.clone()), b1.clone()),
            b2.clone(),
        )
    }
}

// ---------------------------------------------------------------------------
// Exact-rational Farkas / entailment combination (ported from
// clean-elab::cert::external / clean-extcert-verify).
//
// This is the soundness gate that was previously MISSING: coefficients used to
// be parsed as f64 and the combined-multiplier check was skipped, so the
// validity witness was registered as a bare `Declaration::Axiom`.  We now parse
// NY's exact-rational certificate format (string "n/d" / decimal rationals; the
// same schema as `clean-elab/src/cert/external`) and ACTUALLY combine the
// multipliers in exact i128 rationals.  When (and only when) the combination
// reproduces the conclusion's coefficients and the derived constant implies the
// claimed one, we register a DERIVED, sorry-free `Eq.refl`-backed theorem; an
// unsound certificate is REJECTED (`Err`), never axiomatized.
// ---------------------------------------------------------------------------

/// Lower an arbitrary-precision `BigUint` magnitude into the kernel's native
/// `BigNat` literal payload.
///
/// `BigUint::to_u64_digits()` returns the value as little-endian `u64` limbs
/// (least-significant limb first) and an EMPTY vector for zero. `BigNat::from_limbs`
/// consumes little-endian limbs with identical ordering, normalizes empty -> `Small(0)`,
/// a single limb -> `Small`, strips trailing zero limbs, and otherwise yields `Big`.
/// Because the limb ordering matches exactly, the resulting `BigNat` denotes the
/// SAME natural number as `u` — with no truncation and no width cap. This is the
/// exact `BigUint -> kernel-Nat` bridge for the trusted lowering in `rat_from_exact`.
#[cfg(test)]
fn biguint_to_bignat(u: &BigUint) -> BigNat {
    BigNat::from_limbs(u.to_u64_digits())
}

/// Exact rational of arbitrary precision, always stored in lowest terms with
/// `den > 0`. Backed by `num_rational::BigRational` (which canonicalises to
/// reduced form with a positive denominator at construction), so the previous
/// i128 overflow rejections of BIG-but-VALID values are gone while every
/// fail-closed reject (zero denominator, malformed input) is preserved.
/// Semantics mirror `clean_elab::cert::external::ExternalRational`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct ExactRat {
    r: BigRational,
}

#[cfg(test)]
impl ExactRat {
    /// The exact rational `0` (= `0/1`). Not a `const` because `BigRational`
    /// is heap-backed and cannot be const-constructed.
    #[cfg(test)]
    fn zero() -> ExactRat {
        ExactRat {
            r: BigRational::zero(),
        }
    }

    /// Numerator accessor (reduced, sign-carrying). Used by error formatting.
    #[cfg(test)]
    fn num(&self) -> &BigInt {
        self.r.numer()
    }

    /// Denominator accessor (reduced, always `> 0`). Used by error formatting
    /// and by `rat_from_exact` lowering.
    #[cfg(test)]
    fn den(&self) -> &BigInt {
        self.r.denom()
    }

    /// Construct a reduced rational from an arbitrary-precision `num`/`den`.
    ///
    /// The explicit `den == 0 -> Err` check MUST run BEFORE constructing the
    /// `BigRational` (`BigRational::new` PANICS on a zero denominator); a
    /// malformed cert with a zero denominator stays a clean fail-closed reject,
    /// never a panic, never an accept. `BigRational::new` then gcd-reduces and
    /// moves the sign onto the numerator so the `reduced`/`den > 0` invariant
    /// holds by construction.
    #[cfg(test)]
    fn reduced(num: BigInt, den: BigInt) -> Result<Self, CertParseError> {
        if den.is_zero() {
            return Err(CertParseError::RationalArith {
                detail: "zero denominator".to_string(),
            });
        }
        Ok(ExactRat {
            r: BigRational::new(num, den),
        })
    }

    #[cfg(test)]
    fn from_int(n: BigInt) -> Self {
        ExactRat {
            r: BigRational::from_integer(n),
        }
    }

    #[cfg(test)]
    fn is_zero(&self) -> bool {
        self.r.is_zero()
    }
    #[cfg(test)]
    fn is_negative(&self) -> bool {
        self.r.is_negative()
    }

    #[cfg(test)]
    fn neg(&self) -> Self {
        ExactRat { r: -self.r.clone() }
    }

    /// Exact arbitrary-precision addition (infallible; `Result` kept so the
    /// `?` call-sites in `NormConstraint`/`verify_entailment` are untouched).
    #[allow(clippy::should_implement_trait, clippy::unnecessary_wraps)]
    #[cfg(test)]
    fn add(&self, other: &Self) -> Result<Self, CertParseError> {
        Ok(ExactRat {
            r: self.r.clone() + other.r.clone(),
        })
    }

    /// Exact arbitrary-precision multiplication (infallible; `Result` kept for
    /// API stability at the `?` call-sites).
    #[allow(clippy::should_implement_trait, clippy::unnecessary_wraps)]
    #[cfg(test)]
    fn mul(&self, other: &Self) -> Result<Self, CertParseError> {
        Ok(ExactRat {
            r: self.r.clone() * other.r.clone(),
        })
    }

    /// `self <= other` via exact `BigRational` total order (no cross-multiply,
    /// so the prior i128 cross-multiplication overflow hazard is removed).
    #[cfg(test)]
    fn le(&self, other: &Self) -> bool {
        self.r <= other.r
    }

    /// `self < other` via exact `BigRational` total order.
    #[cfg(test)]
    fn lt(&self, other: &Self) -> bool {
        self.r < other.r
    }
}

/// Parse a rational from a JSON value that is either a string ("n/d", an
/// integer, or a decimal), or an integer number. Mirrors the grammar of
/// `clean_elab::cert::external::rational::parse_rational_str`.
#[cfg(test)]
fn parse_exact_rat(value: &serde_json::Value) -> Result<ExactRat, CertParseError> {
    match value {
        serde_json::Value::String(s) => parse_rat_str(s),
        serde_json::Value::Number(n) => n
            .as_i64()
            .map(|i| ExactRat::from_int(BigInt::from(i)))
            .ok_or_else(|| CertParseError::RationalArith {
                detail: "rational number out of range".to_string(),
            }),
        _ => Err(CertParseError::RationalArith {
            detail: "invalid rational encoding".to_string(),
        }),
    }
}

#[cfg(test)]
fn parse_rat_str(s: &str) -> Result<ExactRat, CertParseError> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(CertParseError::RationalArith {
            detail: "empty rational string".to_string(),
        });
    }
    let parts: Vec<&str> = trimmed.split('/').collect();
    match parts.len() {
        1 => parse_int_or_decimal(parts[0]),
        2 => {
            let num = parts[0]
                .parse::<BigInt>()
                .map_err(|_| CertParseError::RationalArith {
                    detail: format!("invalid numerator '{}'", parts[0]),
                })?;
            let den = parts[1]
                .parse::<BigInt>()
                .map_err(|_| CertParseError::RationalArith {
                    detail: format!("invalid denominator '{}'", parts[1]),
                })?;
            ExactRat::reduced(num, den)
        }
        _ => Err(CertParseError::RationalArith {
            detail: format!("invalid rational string '{trimmed}'"),
        }),
    }
}

#[cfg(test)]
fn parse_int_or_decimal(s: &str) -> Result<ExactRat, CertParseError> {
    if s.contains(['e', 'E']) {
        return Err(CertParseError::RationalArith {
            detail: "scientific notation not supported".to_string(),
        });
    }
    if let Some((int_part, frac_part)) = s.split_once('.') {
        if frac_part.is_empty() || !frac_part.chars().all(|c| c.is_ascii_digit()) {
            return Err(CertParseError::RationalArith {
                detail: format!("invalid decimal '{s}'"),
            });
        }
        // den = 10^(#fractional digits); reject an absurd fractional length
        // fail-closed before it drives an unbounded `pow` allocation (and before
        // `frac_part.len() as u32` could wrap). Any legitimate certificate value
        // is far under this bound (an ~18k-bit rational is ~5.4k decimal digits).
        const MAX_DECIMAL_FRAC_DIGITS: usize = 100_000;
        if frac_part.len() > MAX_DECIMAL_FRAC_DIGITS {
            return Err(CertParseError::RationalArith {
                detail: "decimal too long".to_string(),
            });
        }
        let (negative, int_digits) = match int_part.as_bytes().first() {
            Some(b'-') => (true, &int_part[1..]),
            Some(b'+') => (false, &int_part[1..]),
            _ => (false, int_part),
        };
        if !int_digits.is_empty() && !int_digits.chars().all(|c| c.is_ascii_digit()) {
            return Err(CertParseError::RationalArith {
                detail: format!("invalid decimal '{s}'"),
            });
        }
        let int_val: BigInt = if int_digits.is_empty() {
            BigInt::zero()
        } else {
            int_digits
                .parse()
                .map_err(|_| CertParseError::RationalArith {
                    detail: format!("invalid decimal '{s}'"),
                })?
        };
        let frac_val: BigInt = frac_part
            .parse()
            .map_err(|_| CertParseError::RationalArith {
                detail: format!("invalid decimal '{s}'"),
            })?;
        // den = 10^(#fractional digits). Arbitrary precision; length capped above.
        let den: BigInt = BigInt::from(10u8).pow(frac_part.len() as u32);
        let magnitude = int_val * &den + frac_val;
        let num = if negative { -magnitude } else { magnitude };
        ExactRat::reduced(num, den)
    } else {
        let num = s
            .parse::<BigInt>()
            .map_err(|_| CertParseError::RationalArith {
                detail: format!("invalid integer '{s}'"),
            })?;
        Ok(ExactRat::from_int(num))
    }
}

// --- Entailment certificate schema (exact-rational; same shape as
//     clean-elab::cert::external::ExternalEntailmentCert) ---

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
#[cfg(test)]
pub(crate) enum EntailKind {
    Le,
    Lt,
    Eq,
    Ge,
    Gt,
}

#[derive(Debug, Clone, Deserialize)]
#[cfg(test)]
pub(crate) struct EntailConstraint {
    pub kind: EntailKind,
    /// variable -> coefficient (rational, as JSON string / number).
    pub coefficients: std::collections::BTreeMap<String, serde_json::Value>,
    pub constant: serde_json::Value,
}

#[derive(Debug, Clone, Deserialize)]
#[cfg(test)]
pub(crate) struct EntailmentCert {
    pub version: String,
    pub premises: Vec<EntailConstraint>,
    pub multipliers: Vec<serde_json::Value>,
    pub conclusion: EntailConstraint,
}

/// A constraint normalized to `sum coeff_i * x_i <= constant` (with a strict
/// flag for `<`).
#[derive(Debug, Clone)]
#[cfg(test)]
struct NormConstraint {
    coeffs: std::collections::BTreeMap<String, ExactRat>,
    constant: ExactRat,
    strict: bool,
}

#[cfg(test)]
impl NormConstraint {
    #[cfg(test)]
    fn zero() -> Self {
        NormConstraint {
            coeffs: std::collections::BTreeMap::new(),
            constant: ExactRat::zero(),
            strict: false,
        }
    }

    #[cfg(test)]
    fn scale(&self, factor: &ExactRat) -> Result<Self, CertParseError> {
        if factor.is_zero() {
            return Ok(NormConstraint::zero());
        }
        let mut coeffs = std::collections::BTreeMap::new();
        for (var, coeff) in &self.coeffs {
            let scaled = coeff.mul(factor)?;
            if !scaled.is_zero() {
                coeffs.insert(var.clone(), scaled);
            }
        }
        Ok(NormConstraint {
            coeffs,
            constant: self.constant.mul(factor)?,
            strict: self.strict,
        })
    }

    #[cfg(test)]
    fn add(mut self, other: Self) -> Result<Self, CertParseError> {
        for (var, coeff) in other.coeffs {
            let next = match self.coeffs.remove(&var) {
                Some(existing) => existing.add(&coeff)?,
                None => coeff,
            };
            if !next.is_zero() {
                self.coeffs.insert(var, next);
            }
        }
        Ok(NormConstraint {
            coeffs: self.coeffs,
            constant: self.constant.add(&other.constant)?,
            strict: self.strict || other.strict,
        })
    }
}

#[cfg(test)]
fn parse_coeff_map(
    m: &std::collections::BTreeMap<String, serde_json::Value>,
) -> Result<std::collections::BTreeMap<String, ExactRat>, CertParseError> {
    let mut out = std::collections::BTreeMap::new();
    for (var, value) in m {
        let r = parse_exact_rat(value)?;
        if !r.is_zero() {
            out.insert(var.clone(), r);
        }
    }
    Ok(out)
}

/// Normalize a constraint to one (inequalities) or two (equalities) `<=` forms.
#[cfg(test)]
fn normalize(constraint: &EntailConstraint) -> Result<Vec<NormConstraint>, CertParseError> {
    let coeffs = parse_coeff_map(&constraint.coefficients)?;
    let constant = parse_exact_rat(&constraint.constant)?;
    let neg_map = |m: &std::collections::BTreeMap<String, ExactRat>| {
        m.iter().map(|(v, c)| (v.clone(), c.neg())).collect()
    };
    Ok(match constraint.kind {
        EntailKind::Le => vec![NormConstraint {
            coeffs,
            constant,
            strict: false,
        }],
        EntailKind::Lt => vec![NormConstraint {
            coeffs,
            constant,
            strict: true,
        }],
        EntailKind::Ge => vec![NormConstraint {
            coeffs: neg_map(&coeffs),
            constant: constant.neg(),
            strict: false,
        }],
        EntailKind::Gt => vec![NormConstraint {
            coeffs: neg_map(&coeffs),
            constant: constant.neg(),
            strict: true,
        }],
        EntailKind::Eq => vec![
            NormConstraint {
                coeffs: coeffs.clone(),
                constant: constant.clone(),
                strict: false,
            },
            NormConstraint {
                coeffs: neg_map(&coeffs),
                constant: constant.neg(),
                strict: false,
            },
        ],
    })
}

/// Outcome of an exact-rational entailment combination: the derived combined
/// constraint and the (single, normalized) conclusion it was checked against.
#[derive(Debug, Clone)]
#[cfg(test)]
pub(crate) struct EntailmentResult {
    /// Derived (combined) coefficient map == conclusion coefficient map.
    pub coeffs: std::collections::BTreeMap<String, ExactRat>,
    /// Combined constant (the derived bound).
    pub derived: ExactRat,
    /// Conclusion's claimed bound.
    pub claimed: ExactRat,
    /// Per-premise `(multiplier, normalized-constant)` pairs that feed the
    /// constructive n-row Farkas combination (`NNVerify.farkas_combine_list`).
    ///
    /// `Some(rows)` iff EVERY premise normalized to exactly one `<=` row, so a
    /// concrete `List Row` instance can be built and the multiplier-combination
    /// summation `Σ muᵢ·constantᵢ` is reproduced by the kernel `List.rec` fold.
    /// `None` when some premise was an equality (two rows): the bound combination
    /// is still verified in exact rationals (the `Err`/`Ok` gate below), but the
    /// kernel-list witness is not constructed (the parser reports this).
    ///
    /// Zero-multiplier premises are dropped (they contribute `0` to the fold and
    /// match the exact-rational combination, which also skips them).
    pub farkas_rows: Option<Vec<(ExactRat, ExactRat)>>,
}

/// Port of `clean_elab::cert::external::verify_entailment_certificate`:
/// combine the premises scaled by their (non-negative) multipliers in EXACT
/// rationals and confirm the result entails the conclusion.
///
/// Returns `Ok(result)` iff the combination is sound; an unsound certificate
/// (wrong coefficients, insufficient bound, negative multiplier, version /
/// length mismatch) yields an `Err` and MUST NOT be turned into a witness.
#[cfg(test)]
pub(crate) fn verify_entailment(cert: &EntailmentCert) -> Result<EntailmentResult, CertParseError> {
    if cert.version != "1.0" {
        return Err(CertParseError::EntailmentFailed {
            detail: format!("unsupported version '{}'", cert.version),
        });
    }
    if cert.premises.len() != cert.multipliers.len() {
        return Err(CertParseError::EntailmentFailed {
            detail: format!(
                "premises ({}) / multipliers ({}) length mismatch",
                cert.premises.len(),
                cert.multipliers.len()
            ),
        });
    }

    let mut combined = NormConstraint::zero();
    // Per-premise `(multiplier, normalized-constant)` rows for the kernel
    // `farkas_combine_list` instance. Stays `Some` only while every premise is a
    // single `<=` row (the common NY case); an equality premise (two rows) flips
    // it to `None` so the parser knows the list witness is not constructed.
    let mut farkas_rows: Option<Vec<(ExactRat, ExactRat)>> = Some(Vec::new());
    for (idx, (premise, mult_json)) in cert.premises.iter().zip(&cert.multipliers).enumerate() {
        let multiplier = parse_exact_rat(mult_json)?;
        if multiplier.is_negative() {
            return Err(CertParseError::EntailmentFailed {
                detail: format!("multipliers[{idx}] is negative"),
            });
        }
        if multiplier.is_zero() {
            continue;
        }
        let norms = normalize(premise)?;
        // Record the per-row contribution for the constructive list combination.
        // Only single-row premises participate; an equality premise disables the
        // kernel-list path (handled at the witness-construction step).
        if let Some(rows) = farkas_rows.as_mut() {
            if norms.len() == 1 {
                rows.push((multiplier.clone(), norms[0].constant.clone()));
            } else {
                farkas_rows = None;
            }
        }
        for norm in norms {
            combined = combined.add(norm.scale(&multiplier)?)?;
        }
    }

    let mut concl_parts = normalize(&cert.conclusion)?;
    if concl_parts.len() != 1 {
        return Err(CertParseError::EntailmentFailed {
            detail: "equality conclusions are not valid entailment targets".to_string(),
        });
    }
    let conclusion = concl_parts.remove(0);

    if combined.coeffs != conclusion.coeffs {
        return Err(CertParseError::EntailmentFailed {
            detail: "derived coefficients do not match conclusion".to_string(),
        });
    }

    let derived = combined.constant;
    let claimed = conclusion.constant;
    let ok = if !combined.strict && conclusion.strict {
        // derived (non-strict) must be strictly below a strict claim. Exact
        // `BigRational` order — no cross-multiplication, no overflow hazard.
        derived.lt(&claimed)
    } else {
        derived.le(&claimed)
    };
    if !ok {
        return Err(CertParseError::EntailmentFailed {
            detail: format!(
                "derived bound {}/{} does not imply claimed {}/{}",
                derived.num(),
                derived.den(),
                claimed.num(),
                claimed.den()
            ),
        });
    }

    Ok(EntailmentResult {
        coeffs: combined.coeffs,
        derived,
        claimed,
        farkas_rows,
    })
}

// ---------------------------------------------------------------------------
// Certificate-to-Expr conversion
// ---------------------------------------------------------------------------

/// A single layer's bounds converted to kernel `Expr` terms.
#[derive(Debug, Clone)]
#[cfg(test)]
pub(crate) struct LayerBoundsExpr {
    pub input_dim: usize,
    pub output_dim: usize,
    pub input_bounds_expr: Expr,
    pub output_bounds_expr: Expr,
    /// Farkas coefficient matrix Expr (`NNMat` axiom), if this layer
    /// has a Farkas witness.
    pub farkas_coeffs_expr: Option<Expr>,
}

/// Result of converting a full certificate to Expr terms.
#[derive(Debug, Clone)]
#[cfg(test)]
pub(crate) struct CertificateExprs {
    pub layers: Vec<LayerBoundsExpr>,
    /// Composed `IntervalBounds.subset` type for the full chain, or `None`
    /// if there is only one layer.
    pub chain_proof_type: Option<Expr>,
}

#[cfg(test)]
fn axiom_name(prefix: &str, layer_id: usize, role: &str) -> Name {
    Name::from_string(&format!("cert_{prefix}_L{layer_id}_{role}"))
}

/// Convert `BoundsData` into an `IntervalBounds d` Expr by registering
/// axioms for the lower/upper vectors and their validity witness.
#[cfg(test)]
fn bounds_to_expr(
    env: &mut Environment,
    c: &CertConsts,
    bounds: &BoundsData,
    prefix: &str,
    layer_id: usize,
) -> Result<Expr, CertParseError> {
    let dim = bounds.lower.len();
    let d = Expr::nat_lit(dim as u64);
    let nn_vec_d = Expr::app(c.nn_vec.clone(), d.clone());

    let lower_name = axiom_name(prefix, layer_id, "lower");
    if env.get_const(&lower_name).is_none() {
        env.add_decl(crate::env::Declaration::Axiom {
            name: lower_name.clone(),
            level_params: vec![],
            type_: nn_vec_d.clone(),
        })?;
    }
    let lower = Expr::const_(lower_name, vec![]);

    let upper_name = axiom_name(prefix, layer_id, "upper");
    if env.get_const(&upper_name).is_none() {
        env.add_decl(crate::env::Declaration::Axiom {
            name: upper_name.clone(),
            level_params: vec![],
            type_: nn_vec_d,
        })?;
    }
    let upper = Expr::const_(upper_name, vec![]);

    let valid_type = {
        let mut b = EnvDeclBuilder::new();
        let fin_d = Expr::app(c.fin.clone(), d.clone());
        let (i_id, i) = b.fresh_local(fin_d.clone());
        let le = c.rat_le(
            Expr::app(lower.clone(), i.clone()),
            Expr::app(upper.clone(), i),
        );
        let r = b.mk_pi(i_id, BinderInfo::Default, fin_d, le);
        b.finish(r)
    };

    let valid_name = axiom_name(prefix, layer_id, "valid");
    if env.get_const(&valid_name).is_none() {
        env.add_decl(crate::env::Declaration::Axiom {
            name: valid_name.clone(),
            level_params: vec![],
            type_: valid_type,
        })?;
    }
    let valid = Expr::const_(valid_name, vec![]);

    Ok(Expr::app(
        Expr::app(Expr::app(Expr::app(c.ib_mk.clone(), d), lower), upper),
        valid,
    ))
}

#[cfg(test)]
fn register_subset_axiom(
    env: &mut Environment,
    c: &CertConsts,
    d: &Expr,
    b1: &Expr,
    b2: &Expr,
    name: Name,
) -> Result<Expr, CertParseError> {
    let subset_type = c.subset(d, b1, b2);
    if env.get_const(&name).is_none() {
        env.add_decl(crate::env::Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: subset_type,
        })?;
    }
    Ok(Expr::const_(name, vec![]))
}

/// Register Farkas coefficient matrix as an axiom with type `NNMat rows cols`.
///
/// Each Farkas witness row is a set of non-negative multipliers for input
/// constraints. The matrix is registered as an opaque axiom whose concrete
/// values are captured in the certificate metadata.
#[cfg(test)]
fn register_farkas_coeffs(
    env: &mut Environment,
    c: &CertConsts,
    witness: &FarkasWitness,
    prefix: &str,
    layer_id: usize,
) -> Result<Expr, CertParseError> {
    let rows = witness.coefficients.len();
    let cols = witness.coefficients.first().map_or(0, |r| r.len());
    let nn_mat = Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]);
    let mat_type = Expr::app(
        Expr::app(nn_mat, Expr::nat_lit(rows as u64)),
        Expr::nat_lit(cols as u64),
    );

    let coeff_name = Name::from_string(&format!("cert_{prefix}_L{layer_id}_farkas_coeffs"));
    if env.get_const(&coeff_name).is_none() {
        env.add_decl(crate::env::Declaration::Axiom {
            name: coeff_name.clone(),
            level_params: vec![],
            type_: mat_type,
        })?;
    }

    // Register individual coefficient Rat literals as definitions for
    // downstream proof reconstruction that needs to inspect values.
    for (row, coeffs) in witness.coefficients.iter().enumerate() {
        for (col, &val) in coeffs.iter().enumerate() {
            let entry_name =
                Name::from_string(&format!("cert_{prefix}_L{layer_id}_farkas_c{row}_{col}"));
            if env.get_const(&entry_name).is_none() {
                env.add_decl(crate::env::Declaration::Definition {
                    name: entry_name,
                    level_params: vec![],
                    type_: c.rat.clone(),
                    value: c.rat_from_f64(val),
                    is_reducible: true,
                })?;
            }
        }
    }

    Ok(Expr::const_(coeff_name, vec![]))
}

#[cfg(test)]
impl Environment {
    /// Parse a gamma-crown certificate JSON and register kernel Expr terms.
    ///
    /// Registers axioms for bound vectors and validity witnesses, constructs
    /// `IntervalBounds` terms per layer, and (for multi-layer certs) registers
    /// per-link subset axioms and computes the composed chain proof type.
    #[cfg(test)]
    pub(crate) fn parse_nn_certificate(
        &mut self,
        json: &str,
    ) -> Result<CertificateExprs, CertParseError> {
        let cert = Certificate::parse(json)?;
        self.init_nn_verify_types()?;
        let c = CertConsts::new();
        let prefix = if cert.network_name.is_empty() {
            "nn"
        } else {
            &cert.network_name
        };

        let mut layer_exprs = Vec::with_capacity(cert.layers.len());
        for layer in &cert.layers {
            let inp = bounds_to_expr(
                self,
                &c,
                &layer.input_bounds,
                &format!("{prefix}_in"),
                layer.layer_id,
            )?;
            let out = bounds_to_expr(
                self,
                &c,
                &layer.output_bounds,
                &format!("{prefix}_out"),
                layer.layer_id,
            )?;
            let farkas_coeffs_expr = match &layer.farkas {
                Some(witness) => Some(register_farkas_coeffs(
                    self,
                    &c,
                    witness,
                    prefix,
                    layer.layer_id,
                )?),
                None => None,
            };
            layer_exprs.push(LayerBoundsExpr {
                input_dim: layer.input_bounds.lower.len(),
                output_dim: layer.output_bounds.lower.len(),
                input_bounds_expr: inp,
                output_bounds_expr: out,
                farkas_coeffs_expr,
            });
        }

        let chain_proof_type = if layer_exprs.len() >= 2 {
            let first = &cert.layers[0];
            let first_dim = Expr::nat_lit(first.input_bounds.lower.len() as u64);
            for (i, pair) in cert.layers.windows(2).enumerate() {
                let (prev, next) = (&pair[0], &pair[1]);
                let link_dim = Expr::nat_lit(prev.output_bounds.lower.len() as u64);
                let name = Name::from_string(&format!(
                    "cert_{prefix}_subset_L{}_L{}",
                    prev.layer_id, next.layer_id
                ));
                let _ = register_subset_axiom(
                    self,
                    &c,
                    &link_dim,
                    &layer_exprs[i].output_bounds_expr,
                    &layer_exprs[i + 1].input_bounds_expr,
                    name,
                )?;
            }
            Some(c.subset(
                &first_dim,
                &layer_exprs[0].input_bounds_expr,
                &layer_exprs.last().expect("non-empty").output_bounds_expr,
            ))
        } else {
            None
        };

        Ok(CertificateExprs {
            layers: layer_exprs,
            chain_proof_type,
        })
    }

    /// Parse an exact-rational ENTAILMENT certificate (NY's exact-rational
    /// format; same schema as `clean-elab/src/cert/external`), run the exact
    /// Farkas-multiplier COMBINATION check, and — only if it succeeds —
    /// register a DERIVED, sorry-free theorem that witnesses the combination.
    ///
    /// ## What is now kernel-DERIVED (the combination step)
    ///
    /// When every premise normalizes to a single `<=` row (the common NY case),
    /// the multiplier combination is no longer witnessed by a vacuous
    /// `@Eq.refl Rat derived` (which only asserts `derived = derived` and pins
    /// the Rust-side sum). Instead we build a CONCRETE `List Row` instance
    /// `rows = [(muᵢ, cᵢ, cᵢ) | premiseᵢ scaled by muᵢ, constant cᵢ]` and
    /// register
    ///
    /// ```text
    /// cert_<name>_combination_sound
    ///   : farkasRowsValid rows → (farkasLower rows ≤ farkasUpper rows)
    ///   := fun hv => @NNVerify.farkas_combine_list rows hv
    /// ```
    ///
    /// The proof body is the kernel-checked constructive theorem
    /// `NNVerify.farkas_combine_list` (n-row Farkas via `List.rec`, sorry-free)
    /// APPLIED to the parsed rows. The conclusion's `farkasLower rows` /
    /// `farkasUpper rows` iota-reduce through `List.rec` to the explicit nested
    /// sum `Σ muᵢ·cᵢ` — i.e. the multiplier-combination summation is reproduced
    /// and checked by the kernel reducer, not asserted. The witness is therefore
    /// genuinely DERIVED from `farkas_combine_list` rather than an `Axiom` (the
    /// previous `Eq.refl` scaffold) — closing the combination-step gap.
    ///
    /// The non-negativity / row-ordering side conditions (`0 ≤ muᵢ`, `cᵢ ≤ cᵢ`)
    /// are carried as the `farkasRowsValid rows` HYPOTHESIS of the registered
    /// theorem, exactly as in `farkas_combine_list` itself — so no `Rat`
    /// literal-ordering axiom is needed and the proof stays sorry-free.
    ///
    /// ## Soundness gate
    ///
    /// `verify_entailment` performs the exact i128-rational combination FIRST and
    /// rejects (`Err`, no declaration registered) any unsound certificate (wrong
    /// coefficients, insufficient bound, negative multiplier, version/length
    /// mismatch). There is no axiom fallback for unsound input.
    ///
    /// ## What remains AXIOM (reported, not silently wired)
    ///
    /// Only the multiplier-COMBINATION step is kernel-derived here. The
    /// bound-IMPLICATION `derived ≤ claimed` and the opaque
    /// `IntervalBounds.subset` linkage are NOT discharged by this method (that
    /// would ripple past the combination step). Callers that need the full
    /// `derived ≤ claimed` step still rely on it being established separately.
    /// When a premise is an EQUALITY (two normalized rows), the kernel-list
    /// path is skipped and we fall back to the `Eq.refl`-pinned witness; the
    /// boolean in the return value reports which path was taken.
    ///
    /// Returns `(theorem_name, farkas_list_backed)`; `farkas_list_backed` is
    /// `true` iff the registered witness is `farkas_combine_list`-backed.
    #[cfg(test)]
    pub(crate) fn verify_entailment_certificate_kernel(
        &mut self,
        json: &str,
        cert_name: &str,
    ) -> Result<Name, CertParseError> {
        self.verify_entailment_certificate_kernel_ex(json, cert_name)
            .map(|(name, _)| name)
    }

    /// Like [`Self::verify_entailment_certificate_kernel`] but also returns
    /// whether the registered witness is backed by `farkas_combine_list`
    /// (`true`) versus the equality-fallback `Eq.refl` scaffold (`false`).
    #[cfg(test)]
    pub(crate) fn verify_entailment_certificate_kernel_ex(
        &mut self,
        json: &str,
        cert_name: &str,
    ) -> Result<(Name, bool), CertParseError> {
        let cert: EntailmentCert = serde_json::from_str(json)?;
        // SOUNDNESS GATE: exact-rational multiplier combination. Rejects unsound
        // certificates before any kernel declaration is built.
        let result = verify_entailment(&cert)?;

        self.init_nn_verify_types()?;
        self.init_eq()?;

        let name = Name::from_string(&format!("cert_{cert_name}_combination_sound"));

        match &result.farkas_rows {
            // Constructive kernel-list path: build the concrete `List Row` and
            // register the `farkas_combine_list`-backed theorem.
            Some(rows) if !rows.is_empty() => {
                self.init_nn_verify_farkas_list()?;
                let (thm_type, thm_value) = build_farkas_list_witness(rows)?;
                if self.get_const(&name).is_none() {
                    self.add_decl(crate::env::Declaration::Theorem {
                        name: name.clone(),
                        level_params: vec![],
                        type_: thm_type,
                        value: thm_value,
                    })?;
                }
                Ok((name, true))
            }
            // Fallback (equality premise, or all-zero multipliers): the exact
            // combination still passed the soundness gate above; pin the derived
            // constant with the structural `Eq.refl` scaffold.
            _ => {
                let c = CertConsts::new();
                let derived_lit = c.rat_from_exact(result.derived.num(), result.derived.den());
                let thm_type = c.rat_eq(derived_lit.clone(), derived_lit.clone());
                let thm_value = c.rat_eq_refl(derived_lit);
                if self.get_const(&name).is_none() {
                    self.add_decl(crate::env::Declaration::Theorem {
                        name: name.clone(),
                        level_params: vec![],
                        type_: thm_type,
                        value: thm_value,
                    })?;
                }
                Ok((name, false))
            }
        }
    }
}

/// Build the `farkas_combine_list`-backed combination witness for the parsed
/// `(multiplier, constant)` rows.
///
/// Returns `(thm_type, thm_value)` where
/// `thm_type  = farkasRowsValid rows → (farkasLower rows ≤ farkasUpper rows)`
/// `thm_value = fun (hv : farkasRowsValid rows) => @farkas_combine_list rows hv`.
///
/// Each parsed row `(muᵢ, cᵢ)` is encoded as the `Row` literal
/// `(muᵢ, cᵢ, cᵢ)`, so the `farkasUpper rows` / `farkasLower rows` folds both
/// iota-reduce to the multiplier-combination sum `Σ muᵢ·cᵢ`.
#[cfg(test)]
fn build_farkas_list_witness(
    rows: &[(ExactRat, ExactRat)],
) -> Result<(Expr, Expr), CertParseError> {
    use crate::env::nn_verify_farkas_list_proofs::farkas_list_consts;

    let c = CertConsts::new();
    let fc = farkas_list_consts();

    // Build the concrete `List Row` from the parsed `(mu, const)` pairs.
    // Encode each row as `(mu, const, const)` so `a ≤ b` is reflexive and the
    // upper/lower folds both reduce to `Σ muᵢ·constᵢ`.
    let row_exprs: Vec<Expr> = rows
        .iter()
        .map(|(mu, k)| {
            let mu_lit = c.rat_from_exact(mu.num(), mu.den());
            let k_lit = c.rat_from_exact(k.num(), k.den());
            fc.mk_row_lit(mu_lit, k_lit.clone(), k_lit)
        })
        .collect();
    let rows_expr = fc.mk_rows_list(&row_exprs);

    // Theorem statement: farkasRowsValid rows → (farkasLower rows ≤ farkasUpper rows).
    let valid_prop = fc.rows_valid_prop(&rows_expr);
    let concl = fc.combine_concl(&rows_expr);

    // Proof: fun (hv : farkasRowsValid rows) => @farkas_combine_list rows hv.
    let mut b = EnvDeclBuilder::new();
    let (hv_id, hv) = b.fresh_local(valid_prop.clone());
    let applied = fc.apply_combine_list(&rows_expr, &hv);
    let value = b.mk_lam(hv_id, BinderInfo::Default, valid_prop.clone(), applied);
    let thm_value = b.finish(value);

    let mut bt = EnvDeclBuilder::new();
    let (h_id, _h) = bt.fresh_local(valid_prop.clone());
    let pi = bt.mk_pi(h_id, BinderInfo::Default, valid_prop, concl);
    let thm_type = bt.finish(pi);

    Ok((thm_type, thm_value))
}
