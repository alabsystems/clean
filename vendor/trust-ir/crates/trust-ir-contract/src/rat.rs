// trust-ir-contract/rat: the exact-rational literal payload of `Formula::Rat`
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// An EXACT rational literal `num / den` — the payload of
/// [`crate::Formula::Rat`], of sort [`crate::Sort::Real`].
///
/// Both parts are canonical decimal strings so the literal is
/// arbitrary-precision without adding a bignum dependency to this leaf crate
/// (a neural-network verifier's Farkas certificate routinely needs 200–500-bit
/// numerators and denominators, far beyond `i128`):
///
/// * `num`: an optional leading `-` followed by decimal digits with no leading
///   zero (`"0"` is the only zero; `"-0"` is not canonical);
/// * `den`: decimal digits with no leading zero, and never zero.
///
/// The syntax is an INVARIANT of the type, not a convention: the fields are
/// private, [`RatLit::new`] is the only constructor, and deserialization goes
/// through the same check (`serde(try_from)`), so a literal that exists —
/// whether built in-process or decoded from a wire payload — always parses
/// exactly with any decimal bignum parser. A consumer never needs a fallback
/// for a malformed digit string.
///
/// REDUCEDNESS (`gcd(num, den) = 1`) is a PRODUCER contract this crate cannot
/// verify without bignum arithmetic: `Eq`/`Hash` are structural, so `2/4` and
/// `1/2` are distinct literals denoting the same value, and a consumer that
/// needs canonical values reduces on parse.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "RatLitWire", into = "RatLitWire")]
pub struct RatLit {
    num: String,
    den: String,
}

/// The on-the-wire shape of [`RatLit`]: the same two fields, unvalidated. It
/// exists only so the derived codec can be wrapped in the canonical-syntax
/// check; the encoding of every format is exactly that of a two-string struct
/// (JSON `{"num":"…","den":"…"}`; index-based codecs: two length-prefixed
/// strings), identical to what a plain struct variant would emit.
#[derive(Serialize, Deserialize)]
struct RatLitWire {
    num: String,
    den: String,
}

/// Why a digit string was refused by [`RatLit::new`] / deserialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RatLitError {
    /// Which part was malformed.
    pub part: &'static str,
    /// The offending text.
    pub text: String,
}

impl std::fmt::Display for RatLitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "rational literal {} {:?} is not a canonical decimal numeral",
            self.part, self.text
        )
    }
}

impl std::error::Error for RatLitError {}

/// `[1-9][0-9]*`, or exactly `0` when `allow_zero`.
fn canonical_unsigned(digits: &str, allow_zero: bool) -> bool {
    match digits.as_bytes() {
        [] => false,
        [b'0'] => allow_zero,
        [first, rest @ ..] => (b'1'..=b'9').contains(first) && rest.iter().all(u8::is_ascii_digit),
    }
}

impl RatLit {
    /// Checked constructor: `None` unless both strings are in the canonical
    /// decimal syntax documented on the type.
    #[must_use]
    pub fn new(num: &str, den: &str) -> Option<RatLit> {
        RatLit::try_new(num, den).ok()
    }

    fn try_new(num: &str, den: &str) -> Result<RatLit, RatLitError> {
        let num_ok = match num.strip_prefix('-') {
            // A negative literal: the magnitude must be a canonical NONZERO
            // numeral (`-0` is not canonical).
            Some(magnitude) => canonical_unsigned(magnitude, false),
            None => canonical_unsigned(num, true),
        };
        if !num_ok {
            return Err(RatLitError {
                part: "numerator",
                text: num.to_string(),
            });
        }
        if !canonical_unsigned(den, false) {
            return Err(RatLitError {
                part: "denominator",
                text: den.to_string(),
            });
        }
        Ok(RatLit {
            num: num.to_string(),
            den: den.to_string(),
        })
    }

    /// The literal with the value of the integer `n` (`den = "1"`).
    #[must_use]
    pub fn from_int(n: i128) -> RatLit {
        RatLit {
            num: n.to_string(),
            den: "1".to_string(),
        }
    }

    /// The canonical decimal numerator (with its `-` sign, if negative).
    #[must_use]
    pub fn num(&self) -> &str {
        &self.num
    }

    /// The canonical decimal denominator (always `≥ 1`).
    #[must_use]
    pub fn den(&self) -> &str {
        &self.den
    }

    /// True iff the denominator is `1`.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.den == "1"
    }

    /// True iff the numerator is negative.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.num.starts_with('-')
    }

    /// The `Reals`-theory SMT-LIB term: `(/ num den)`, with a negative numerator
    /// spelled `(- n)`, and a bare numeral when the value is integral (which
    /// the `Reals` theory sorts as `Real`, mirroring `Int`'s rendering so an
    /// integer embedded in a Real position prints the same either way).
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        let num_term = match self.num.strip_prefix('-') {
            Some(magnitude) => format!("(- {magnitude})"),
            None => self.num.clone(),
        };
        if self.is_integer() {
            num_term
        } else {
            format!("(/ {num_term} {})", self.den)
        }
    }
}

impl TryFrom<RatLitWire> for RatLit {
    type Error = RatLitError;

    fn try_from(wire: RatLitWire) -> Result<Self, Self::Error> {
        RatLit::try_new(&wire.num, &wire.den)
    }
}

impl From<RatLit> for RatLitWire {
    fn from(lit: RatLit) -> Self {
        RatLitWire {
            num: lit.num,
            den: lit.den,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructor_accepts_only_canonical_decimal_strings() {
        assert!(RatLit::new("0", "1").is_some());
        assert!(RatLit::new("1", "2").is_some());
        assert!(RatLit::new("-1", "2").is_some());
        assert!(
            RatLit::new(
                "123456789012345678901234567890123456789012345678901234567890",
                "7"
            )
            .is_some(),
            "arbitrary precision"
        );
        for (num, den) in [
            ("", "1"),
            ("1", ""),
            ("01", "2"),
            ("1", "02"),
            ("-0", "1"),
            ("1", "0"),
            ("1", "-2"),
            ("+1", "2"),
            ("1.5", "2"),
            ("1", "2 "),
            ("a", "1"),
            ("--1", "1"),
            ("-", "1"),
            ("１", "1"), // fullwidth digit: not ASCII
        ] {
            assert!(
                RatLit::new(num, den).is_none(),
                "{num:?}/{den:?} must be rejected"
            );
        }
    }

    #[test]
    fn deserialization_enforces_the_same_invariant() {
        let ok: RatLit = serde_json::from_str(r#"{"num":"-22","den":"7"}"#).expect("canonical");
        assert_eq!(ok, RatLit::new("-22", "7").unwrap());
        for text in [
            r#"{"num":"01","den":"7"}"#,
            r#"{"num":"1","den":"0"}"#,
            r#"{"num":"-0","den":"1"}"#,
            r#"{"num":"1","den":"-7"}"#,
            r#"{"num":"1e3","den":"1"}"#,
            r#"{"num":"","den":"1"}"#,
        ] {
            let err = serde_json::from_str::<RatLit>(text).expect_err(text);
            assert!(
                err.to_string().contains("not a canonical decimal numeral"),
                "{text}: {err}"
            );
        }
    }

    #[test]
    fn accessors_and_rendering() {
        let r = RatLit::new("-7", "3").unwrap();
        assert_eq!((r.num(), r.den()), ("-7", "3"));
        assert!(r.is_negative());
        assert!(!r.is_integer());
        assert_eq!(r.to_smtlib(), "(/ (- 7) 3)");
        let i = RatLit::from_int(5);
        assert!(i.is_integer());
        assert!(!i.is_negative());
        assert_eq!(i.to_smtlib(), "5");
        assert_eq!(
            RatLit::from_int(i128::MIN).to_smtlib(),
            "(- 170141183460469231731687303715884105728)"
        );
    }
}
