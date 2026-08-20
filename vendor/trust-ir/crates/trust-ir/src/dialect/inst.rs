// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `DialectInst` — the in-IR representation of a dialect operation.
//!
//! A `DialectInst` is a structured, typed payload carrying:
//!
//! - `dialect`: the string name of the dialect (e.g. `"verif"`), matched against
//!   `Dialect::name()` in the registry.
//! - `op`: the operation name within the dialect (e.g. `"bfs_step"`).
//! - `operands`: SSA values consumed by the op.
//! - `result_tys`: types produced by the op. Length equals the number of result
//!   `ValueId`s attached by the enclosing `InstrNode::results` vector. Keeping
//!   result types on the op (rather than only on the node) lets the lowering
//!   framework reason about a dialect op without having to walk to the node.
//! - `attrs`: named compile-time attributes (integers, strings, booleans, etc.)
//!   used to carry configuration that is not part of the SSA dataflow.
//! - `version`: the schema version of the op payload. Dialects may bump this
//!   when the attribute layout changes, enabling forward-compatible lowerings.
//!
//! Dialect ops round-trip through all TrustIr serialization formats (text, binary,
//! serde-JSON, serde-MessagePack). The binary and text writers emit the
//! structured fields verbatim; unknown dialects therefore still parse and
//! re-emit without loss.

use crate::ty::Ty;
use crate::value::ValueId;

/// A dialect operation embedded inside a TrustIr `Inst`.
///
/// See module documentation for the full lowering/registration story.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DialectInst {
    /// Dialect namespace, e.g. `"verif"`. Must be non-empty and match a
    /// `Dialect::name()` when lowerings are applied.
    pub dialect: String,
    /// Op name within the dialect, e.g. `"bfs_step"`. Non-empty.
    pub op: String,
    /// SSA operands.
    pub operands: Vec<ValueId>,
    /// Types of the op's results, in order. Mirrors (and must match length of)
    /// the `results` vector on the enclosing `InstrNode`.
    pub result_tys: Vec<Ty>,
    /// Named compile-time attributes. Preserved across serialization so
    /// unknown dialects round-trip without loss.
    pub attrs: Vec<AttrEntry>,
    /// Schema version of the op payload. Starts at 1.
    pub version: u32,
}

impl DialectInst {
    /// Creates a new `DialectInst` with no operands, results, or attrs.
    pub fn new(dialect: impl Into<String>, op: impl Into<String>) -> Self {
        Self {
            dialect: dialect.into(),
            op: op.into(),
            operands: Vec::new(),
            result_tys: Vec::new(),
            attrs: Vec::new(),
            version: 1,
        }
    }

    /// Builder: push an operand.
    pub fn with_operand(mut self, v: ValueId) -> Self {
        self.operands.push(v);
        self
    }

    /// Builder: push multiple operands.
    pub fn with_operands(mut self, it: impl IntoIterator<Item = ValueId>) -> Self {
        self.operands.extend(it);
        self
    }

    /// Builder: declare a result type.
    pub fn with_result_ty(mut self, ty: Ty) -> Self {
        self.result_tys.push(ty);
        self
    }

    /// Builder: declare multiple result types.
    pub fn with_result_tys(mut self, it: impl IntoIterator<Item = Ty>) -> Self {
        self.result_tys.extend(it);
        self
    }

    /// Builder: attach a named attribute.
    pub fn with_attr(mut self, name: impl Into<String>, value: AttrValue) -> Self {
        self.attrs.push(AttrEntry {
            name: name.into(),
            value,
        });
        self
    }

    /// Builder: explicitly set the payload version.
    pub fn with_version(mut self, version: u32) -> Self {
        self.version = version;
        self
    }

    /// Looks up an attribute by name.
    pub fn attr(&self, name: &str) -> Option<&AttrValue> {
        self.attrs.iter().find(|a| a.name == name).map(|a| &a.value)
    }

    /// Returns the fully-qualified op name, `"<dialect>.<op>"`.
    ///
    /// This is the canonical string form used in the text IR and in lowering
    /// rule lookups. Example: `"verif.bfs_step"`.
    pub fn qualified_name(&self) -> String {
        format!("{}.{}", self.dialect, self.op)
    }

    /// Validates that the dialect name, op name, and every attribute name are
    /// lexically well-formed.
    ///
    /// The textual IR spells a dialect op as `<dialect>.<op>(...) [name=value]*`
    /// and the parser splits the qualified name on the **first** `.`. A `.`
    /// embedded in `dialect` or `op` therefore re-splits incorrectly on a text
    /// round trip (a dialect named `"a.b"` reparses to dialect `"a"`, op
    /// `"b.<op>"`), and any whitespace / delimiter / control character would
    /// break parsing outright. To keep the in-memory payload, the text form,
    /// and lowering-rule string lookups in agreement, each name must:
    ///
    /// - be non-empty, and
    /// - contain only ASCII alphanumerics and `_` (the identifier alphabet the
    ///   text parser round-trips losslessly) — in particular **no** `.`,
    ///   whitespace, control characters, or bracket/paren/`=` delimiters.
    ///
    /// Returns the offending name's role on the first violation so callers can
    /// build a precise diagnostic.
    pub fn validate_names(&self) -> Result<(), NameError> {
        check_name(&self.dialect, NameRole::Dialect)?;
        check_name(&self.op, NameRole::Op)?;
        for attr in &self.attrs {
            check_name(&attr.name, NameRole::Attr)?;
        }
        Ok(())
    }
}

/// Which lexical name on a [`DialectInst`] failed validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameRole {
    /// The `dialect` namespace name.
    Dialect,
    /// The `op` name within the dialect.
    Op,
    /// An attribute name.
    Attr,
}

impl NameRole {
    fn label(self) -> &'static str {
        match self {
            NameRole::Dialect => "dialect",
            NameRole::Op => "op",
            NameRole::Attr => "attribute",
        }
    }
}

/// A lexically malformed dialect/op/attribute name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameError {
    /// Which name role was malformed.
    pub role: NameRole,
    /// The offending name (verbatim).
    pub name: String,
}

impl core::fmt::Display for NameError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.name.is_empty() {
            write!(f, "{} name must not be empty", self.role.label())
        } else {
            write!(
                f,
                "{} name {:?} contains an illegal character; \
                 dialect/op/attribute names must be non-empty and use only \
                 ASCII letters, digits, and '_' (no '.', whitespace, or delimiters)",
                self.role.label(),
                self.name
            )
        }
    }
}

/// True iff `c` is a legal dialect/op/attribute name character: an ASCII
/// alphanumeric or `_`. This is the alphabet the text parser's `read_ident`
/// round-trips without re-splitting (it deliberately excludes `.`, which is
/// the `<dialect>.<op>` delimiter).
pub fn is_valid_dialect_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn check_name(name: &str, role: NameRole) -> Result<(), NameError> {
    if !name.is_empty() && name.chars().all(is_valid_dialect_name_char) {
        Ok(())
    } else {
        Err(NameError {
            role,
            name: name.to_string(),
        })
    }
}

/// A single named attribute on a `DialectInst`.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AttrEntry {
    pub name: String,
    pub value: AttrValue,
}

/// Compile-time attribute value.
///
/// Deliberately narrow: dialects needing richer attributes should serialize
/// them into `Bytes(..)` or `Str(..)`. Keeping this enum small means all
/// unknown dialects still round-trip through every TrustIr serialization format.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AttrValue {
    /// 64-bit signed integer attribute.
    I64(i64),
    /// 64-bit unsigned integer attribute.
    U64(u64),
    /// 64-bit floating-point attribute. Serialized bit-exactly (see
    /// [`attr_f64_bits`]) so non-finite values (`NaN`/`±inf`) round-trip
    /// through JSON/MessagePack, which have no non-finite float literals —
    /// mirroring `Constant::Float`.
    F64(#[cfg_attr(feature = "serde", serde(with = "attr_f64_bits"))] f64),
    /// Boolean attribute.
    Bool(bool),
    /// UTF-8 string attribute.
    Str(String),
    /// Opaque byte payload. Dialects may use this for packed structured data.
    Bytes(Vec<u8>),
    /// A TrustIr type. Used by dialects whose ops carry type parameters that are
    /// not result types (e.g. element type of a frontier buffer).
    Ty(Ty),
}

/// Bit-exact `f64` codec for [`AttrValue::F64`] under the `serde` feature.
/// Wire format: a one-field struct `{ "bits": u64 }` carrying `f64::to_bits()`,
/// identical to the `Constant::Float` codec so JSON/MessagePack can represent
/// `NaN`/`±inf` dialect attributes losslessly.
#[cfg(feature = "serde")]
mod attr_f64_bits {
    pub(super) fn serialize<S>(v: &f64, ser: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut s = ser.serialize_struct("FloatBits", 1)?;
        s.serialize_field("bits", &v.to_bits())?;
        s.end()
    }

    pub(super) fn deserialize<'de, D>(de: D) -> Result<f64, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::Deserialize;
        #[derive(serde::Deserialize)]
        struct FloatBits {
            bits: u64,
        }
        let FloatBits { bits } = FloatBits::deserialize(de)?;
        Ok(f64::from_bits(bits))
    }
}

impl AttrValue {
    /// If the value is an `I64`, returns it.
    pub fn as_i64(&self) -> Option<i64> {
        if let AttrValue::I64(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    /// If the value is a `U64`, returns it.
    pub fn as_u64(&self) -> Option<u64> {
        if let AttrValue::U64(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    /// If the value is an `F64`, returns it.
    pub fn as_f64(&self) -> Option<f64> {
        if let AttrValue::F64(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    /// If the value is a `Bool`, returns it.
    pub fn as_bool(&self) -> Option<bool> {
        if let AttrValue::Bool(v) = self {
            Some(*v)
        } else {
            None
        }
    }

    /// If the value is a `Str`, returns it.
    pub fn as_str(&self) -> Option<&str> {
        if let AttrValue::Str(s) = self {
            Some(s.as_str())
        } else {
            None
        }
    }

    /// If the value is `Bytes`, returns it.
    pub fn as_bytes(&self) -> Option<&[u8]> {
        if let AttrValue::Bytes(b) = self {
            Some(b.as_slice())
        } else {
            None
        }
    }

    /// If the value is a `Ty`, returns it.
    pub fn as_ty(&self) -> Option<&Ty> {
        if let AttrValue::Ty(t) = self {
            Some(t)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder_produces_expected_fields() {
        let op = DialectInst::new("verif", "bfs_step")
            .with_operand(ValueId::new(0))
            .with_operand(ValueId::new(1))
            .with_result_ty(Ty::Ptr)
            .with_attr("parallel", AttrValue::Bool(true))
            .with_attr("max_depth", AttrValue::U64(16));

        assert_eq!(op.dialect, "verif");
        assert_eq!(op.op, "bfs_step");
        assert_eq!(op.qualified_name(), "verif.bfs_step");
        assert_eq!(op.operands.len(), 2);
        assert_eq!(op.result_tys, vec![Ty::Ptr]);
        assert_eq!(op.attrs.len(), 2);
        assert_eq!(op.attr("parallel"), Some(&AttrValue::Bool(true)));
        assert_eq!(op.attr("max_depth"), Some(&AttrValue::U64(16)));
        assert!(op.attr("missing").is_none());
        assert_eq!(op.version, 1);
    }

    #[test]
    fn attr_value_accessors() {
        assert_eq!(AttrValue::I64(-7).as_i64(), Some(-7));
        assert_eq!(AttrValue::U64(42).as_u64(), Some(42));
        assert_eq!(AttrValue::F64(3.5).as_f64(), Some(3.5));
        assert_eq!(AttrValue::Bool(true).as_bool(), Some(true));
        assert_eq!(AttrValue::Str("x".into()).as_str(), Some("x"));
        assert_eq!(
            AttrValue::Bytes(vec![1, 2, 3]).as_bytes(),
            Some(&[1u8, 2, 3][..])
        );
        assert_eq!(AttrValue::Ty(Ty::I64).as_ty(), Some(&Ty::I64));

        // Wrong variant returns None.
        assert!(AttrValue::I64(0).as_bool().is_none());
        assert!(AttrValue::Bool(true).as_i64().is_none());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn f64_attr_serde_round_trips_non_finite() {
        // JSON/MessagePack have no NaN/inf literals; the bit-exact codec must
        // round-trip them (and -0.0) losslessly.
        for v in [
            3.5_f64,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            -0.0_f64,
        ] {
            let attr = AttrValue::F64(v);
            let json = serde_json::to_string(&attr).expect("json serialize");
            let back: AttrValue = serde_json::from_str(&json).expect("json deserialize");
            let AttrValue::F64(got) = back else {
                panic!("expected F64, got {back:?}");
            };
            assert_eq!(
                got.to_bits(),
                v.to_bits(),
                "json round-trip changed bits for {v}"
            );

            let mp = rmp_serde::to_vec(&attr).expect("msgpack serialize");
            let back_mp: AttrValue = rmp_serde::from_slice(&mp).expect("msgpack deserialize");
            let AttrValue::F64(got_mp) = back_mp else {
                panic!("expected F64, got {back_mp:?}");
            };
            assert_eq!(
                got_mp.to_bits(),
                v.to_bits(),
                "msgpack round-trip changed bits for {v}"
            );
        }
    }

    #[test]
    fn clone_eq_works() {
        let op = DialectInst::new("verif", "frontier_drain")
            .with_operands([ValueId::new(3), ValueId::new(4)])
            .with_result_tys([Ty::I64, Ty::Bool])
            .with_attr("batch", AttrValue::U64(64));
        let cloned = op.clone();
        assert_eq!(op, cloned);
    }

    #[test]
    fn version_bump_roundtrips() {
        let op = DialectInst::new("d", "o").with_version(7);
        assert_eq!(op.version, 7);
    }

    // --- FIX: lexical name validation (text round-trip safety) ---

    #[test]
    fn validate_names_accepts_identifier_names() {
        let op = DialectInst::new("verif", "bfs_step")
            .with_attr("max_depth", AttrValue::U64(16))
            .with_attr("parallel0", AttrValue::Bool(true));
        assert!(op.validate_names().is_ok());
    }

    #[test]
    fn validate_names_rejects_dotted_dialect() {
        // A dialect named "a.b" reparses wrong on a text round trip because the
        // parser splits "<dialect>.<op>" on the first '.'.
        let op = DialectInst::new("a.b", "step");
        let err = op
            .validate_names()
            .expect_err("dotted dialect name must be rejected");
        assert_eq!(err.role, NameRole::Dialect);
        assert_eq!(err.name, "a.b");
    }

    #[test]
    fn validate_names_rejects_dotted_op() {
        let op = DialectInst::new("verif", "bfs.step");
        let err = op
            .validate_names()
            .expect_err("dotted op name must be rejected");
        assert_eq!(err.role, NameRole::Op);
    }

    #[test]
    fn validate_names_rejects_empty_and_whitespace() {
        assert_eq!(
            DialectInst::new("", "op")
                .validate_names()
                .unwrap_err()
                .role,
            NameRole::Dialect
        );
        assert_eq!(
            DialectInst::new("d", "").validate_names().unwrap_err().role,
            NameRole::Op
        );
        assert_eq!(
            DialectInst::new("d", "a b")
                .validate_names()
                .unwrap_err()
                .role,
            NameRole::Op
        );
    }

    #[test]
    fn validate_names_rejects_bad_attr_name() {
        let op = DialectInst::new("d", "o").with_attr("has space", AttrValue::Bool(true));
        let err = op
            .validate_names()
            .expect_err("attr name with a space must be rejected");
        assert_eq!(err.role, NameRole::Attr);
        assert_eq!(err.name, "has space");
    }

    #[test]
    fn validate_names_rejects_delimiter_and_control_chars() {
        for bad in ["d(", "d=", "d[", "d]", "d\tx", "d\n", "d\u{0}"] {
            assert!(
                DialectInst::new(bad, "o").validate_names().is_err(),
                "dialect name {bad:?} must be rejected"
            );
        }
    }

    #[test]
    fn name_char_predicate_matches_identifier_alphabet() {
        assert!(is_valid_dialect_name_char('a'));
        assert!(is_valid_dialect_name_char('Z'));
        assert!(is_valid_dialect_name_char('0'));
        assert!(is_valid_dialect_name_char('_'));
        assert!(!is_valid_dialect_name_char('.'));
        assert!(!is_valid_dialect_name_char(' '));
        assert!(!is_valid_dialect_name_char('-'));
    }
}
