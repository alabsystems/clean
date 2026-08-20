// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Constant {
    Int(#[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_i128"))] i128),
    /// Unsigned 128-bit integer constant ABOVE `i128::MAX` (v24, RFC
    /// TRUST_IR_V2 B1 breaking-batch member: the 128-bit-faithful carrier).
    ///
    /// CANONICALITY (one-spelling-per-construct, spec ratification 3): a
    /// `U128(v)` is well-formed IFF `v > i128::MAX as u128`. Every integer
    /// value has exactly ONE spelling — `Int` for everything representable in
    /// `i128` (all of it: every signed value and every unsigned value up to
    /// `i128::MAX`), `U128` only for the upper half of the `u128` range that
    /// `i128` cannot carry. The rule is ENFORCED, not assumed: the binary
    /// decoder rejects a non-canonical `U128`, `validate_module` rejects it
    /// structurally, the text parser picks the variant by VALUE, and the
    /// [`Constant::u128`] smart constructor is the only sanctioned way to
    /// build one from an unsigned source. This is what keeps `Eq`/`Hash`
    /// value-faithful with derived-style per-variant arms: a canonical `Int`
    /// and a canonical `U128` can never denote the same value.
    ///
    /// Before v24 the producer had to store a `u128` above `i128::MAX` as its
    /// wrapped-negative `i128` bit pattern — bit-preserving on the wire but
    /// value-DISHONEST everywhere the payload is read as a number (display,
    /// ordering, canonical text). This variant retires that ambiguity.
    U128(#[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_u128"))] u128),
    /// Raw byte-array constant (v25, RFC TRUST_IR_V2 B1): the payload of a
    /// `[u8; N]` array or the pointee bytes behind a `&str` / `&[u8]` fat
    /// pointer. Replaces the O(N)-`Constant::Int` element spelling for byte
    /// data (a 1 KiB string literal is 1 KiB of payload, not 1024 boxed Int
    /// nodes).
    ///
    /// `utf8: true` marks str-origin data and is a CHECKED claim — the
    /// validator rejects a `utf8` byte constant whose `data` is not valid
    /// UTF-8 (a str constant with invalid bytes would be an unsound input to
    /// every str-typed proof). `false` is raw `[u8]` data with no encoding
    /// claim. The flag is part of value identity (Eq/Hash) and of the wire
    /// form.
    Bytes {
        data: Vec<u8>,
        utf8: bool,
    },
    /// Bit-exact `f64` constant.
    ///
    /// With the `serde` feature enabled the `f64` payload is serialized
    /// through the `float_bits` helper below, which encodes the value as a
    /// single-field struct `{ "bits": <u64> }` carrying the raw
    /// `f64::to_bits()` representation. This guarantees that every IEEE-754
    /// bit pattern (finite, subnormal, `-0.0`, the full family of NaN
    /// payloads including signaling NaN, and `±∞`) round-trips byte-for-byte
    /// through both JSON and MessagePack.
    ///
    /// Without this custom encoding, `serde_json` collapses `NaN` / `±∞` to
    /// JSON `null` (JSON has no IEEE-754 literal for them) and historically
    /// lost a ULP on a small minority of finite bit patterns. For a
    /// verified compiler IR — where the constant must round-trip bit-exact
    /// or any proof about it becomes unsound — that is unacceptable data
    /// loss, so the wire format is deliberately `{ "bits": u64 }` rather
    /// than the idiomatic JSON number.
    Float(#[cfg_attr(feature = "serde", serde(with = "float_bits"))] f64),
    Bool(bool),
    /// Heterogeneous ordered aggregate (tuple / array literal style).
    ///
    /// Kept for backward compatibility. New aggregate-typed constants should
    /// prefer the more specific `Sequence`, `Set`, or `Record` variants so
    /// that the value shape matches its `Ty` classification.
    Aggregate(Vec<Constant>),
    /// Homogeneous fixed-length array literal (mirrors `Ty::Array`).
    Array(Vec<Constant>),
    /// Homogeneous fixed-width vector literal (mirrors `Ty::Vector`).
    ///
    /// Vector constants are distinct from aggregate and array constants so
    /// SIMD frontends do not need to encode `<N x T>` lanes as `array[...]`
    /// and rely on consumers to reinterpret the shape.
    Vector(Vec<Constant>),
    /// Ordered packed sequence constant (mirrors `Ty::Sequence`).
    ///
    /// Element order is significant and preserved on serialization.
    Sequence(Vec<Constant>),
    /// Unordered set literal (mirrors `Ty::Set`). Elements are stored in a
    /// canonical order chosen by the constructor; duplicate suppression is
    /// the frontend's responsibility so the constant remains a faithful
    /// record of what the source program wrote.
    Set(Vec<Constant>),
    /// Named-field record literal (mirrors `Ty::Record`).
    ///
    /// Field order is canonical (typically sorted by name) so records with
    /// equal field-sets compare equal by value.
    Record(Vec<(String, Constant)>),
    /// First-class closure constant: a captured-environment frame bundled
    /// with a direct `FuncId` target. Mirrors `Ty::Closure`.
    ///
    /// Captures are explicit typed values (not an opaque env pointer) —
    /// this is what lets a serialized closure be re-typed against its
    /// `ClosureTy` without relying on runtime state. The ty#4145 lesson
    /// (stale cached `SA[bb \in Ballot]` body) is prevented because the
    /// captured values are frozen at closure-literal time.
    Closure {
        func: crate::value::FuncId,
        captures: Vec<Constant>,
    },
    /// Bare Rust function item constant with no captured environment.
    ///
    /// This is distinct from `Closure`: `FnDef` carries only the function
    /// identity and matches `Ty::Func`, while `Closure` carries an explicit
    /// captured environment and matches `Ty::Closure`.
    FnDef(crate::value::FuncId),
    /// Pointer-sized, relocatable element holding the run-time ADDRESS of a
    /// named symbol (a function or a data global) plus a constant `addend`.
    ///
    /// This is the one constant whose value is NOT known until link time: it
    /// is a placeholder for `&symbol + addend` that the object writer turns
    /// into a data-section relocation (`X86_64_RELOC_UNSIGNED` on Mach-O,
    /// `R_X86_64_64` on ELF). It exists so a global-variable initializer can
    /// embed the address of another symbol — the canonical example being a
    /// vtable / `static FNS: [fn(); N]` whose slots are function addresses the
    /// linker fills in (the trait-object / `dyn` keystone).
    ///
    /// The `symbol` is resolved by NAME against the same symbol table the code
    /// relocations use: it may refer to a function or data global defined in
    /// the same module, or to an external symbol the linker resolves. Each
    /// `SymbolAddr` occupies exactly one native pointer (8 bytes on the
    /// supported 64-bit targets) inside its enclosing aggregate.
    ///
    /// This variant has no run-time value the interpreter can model (addresses
    /// are only assigned at link time), so it is exercised by link+run
    /// differential testing rather than the interpreter.
    SymbolAddr {
        /// Unmangled name of the target symbol (function or data global).
        symbol: String,
        /// Constant byte offset added to the resolved symbol address.
        addend: i64,
    },
    /// Zero-sized `PhantomData` marker.
    PhantomData,
}

// `Constant` equality is **bit-exact** for floats, deliberately rejecting
// `f64`'s IEEE-754 semantic equality.
//
// The derived `PartialEq` would inherit `f64`'s `==`, under which
// `NaN != NaN` (non-reflexive) and `-0.0 == +0.0` (distinct bit patterns
// conflated). For a verified IR that is unsound: a `Constant` is the *literal*
// the source program wrote, and any proof reasoning about it (constant
// folding, switch-table layout, translation validation) requires that two
// constants are equal iff they are the same value. So `Constant::Float`
// compares (and hashes) by `f64::to_bits()`:
//
// * `Float(NaN) == Float(NaN)` for identical NaN bit patterns (reflexive), and
//   distinct NaN payloads stay distinct;
// * `Float(-0.0) != Float(+0.0)` (different signs are different IR identities);
// * every other finite/subnormal/`±∞` pattern compares by its exact bits.
//
// Because the relation is now reflexive, `Eq` is sound and is implemented too.
// `Hash` hashes the same bit-exact key so the `Hash`/`Eq` contract holds
// (`a == b` implies `hash(a) == hash(b)`), letting `Constant` be used as a
// `HashMap`/`HashSet` key. All non-float variants compare/hash structurally.

impl PartialEq for Constant {
    fn eq(&self, other: &Self) -> bool {
        use Constant::*;
        match (self, other) {
            (Int(a), Int(b)) => a == b,
            // Canonicality (see the variant doc) means a well-formed `U128`
            // never overlaps a well-formed `Int`'s value range, so the
            // per-variant arm is value-faithful without a cross-variant case.
            (U128(a), U128(b)) => a == b,
            (Bytes { data: da, utf8: ua }, Bytes { data: db, utf8: ub }) => da == db && ua == ub,
            // Bit-exact float identity (NaN == NaN, -0.0 != +0.0).
            (Float(a), Float(b)) => a.to_bits() == b.to_bits(),
            (Bool(a), Bool(b)) => a == b,
            (Aggregate(a), Aggregate(b)) => a == b,
            (Array(a), Array(b)) => a == b,
            (Vector(a), Vector(b)) => a == b,
            (Sequence(a), Sequence(b)) => a == b,
            (Set(a), Set(b)) => a == b,
            (Record(a), Record(b)) => a == b,
            (
                Closure {
                    func: fa,
                    captures: ca,
                },
                Closure {
                    func: fb,
                    captures: cb,
                },
            ) => fa == fb && ca == cb,
            (FnDef(a), FnDef(b)) => a == b,
            (
                SymbolAddr {
                    symbol: sa,
                    addend: aa,
                },
                SymbolAddr {
                    symbol: sb,
                    addend: ab,
                },
            ) => sa == sb && aa == ab,
            (PhantomData, PhantomData) => true,
            // Different variants are never equal.
            _ => false,
        }
    }
}

impl Eq for Constant {}

impl core::hash::Hash for Constant {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        use Constant::*;
        // Hash the discriminant first so distinct variants with structurally
        // similar payloads (e.g. `Aggregate` vs `Sequence` vs `Set` over the
        // same element list) do not collide their hashes by construction.
        core::mem::discriminant(self).hash(state);
        match self {
            Int(v) => v.hash(state),
            U128(v) => v.hash(state),
            Bytes { data, utf8 } => {
                data.hash(state);
                utf8.hash(state);
            }
            // Mirror the bit-exact equality used in `PartialEq`.
            Float(v) => v.to_bits().hash(state),
            Bool(v) => v.hash(state),
            Aggregate(v) | Array(v) | Vector(v) | Sequence(v) | Set(v) => v.hash(state),
            Record(fields) => fields.hash(state),
            Closure { func, captures } => {
                func.hash(state);
                captures.hash(state);
            }
            FnDef(func) => func.hash(state),
            SymbolAddr { symbol, addend } => {
                symbol.hash(state);
                addend.hash(state);
            }
            PhantomData => {}
        }
    }
}

/// Bit-exact `f64` codec used by `Constant::Float` under the `serde` feature.
///
/// Wire format: a one-field struct `{ "bits": u64 }` carrying
/// `f64::to_bits()`. This makes the encoding symmetric across JSON and
/// MessagePack and sidesteps JSON's lack of `NaN`/`Infinity` literals. See
/// the `Constant::Float` doc comment for the full rationale (issue #48).
#[cfg(feature = "serde")]
mod float_bits {
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

impl Constant {
    pub fn i8(v: i8) -> Self {
        Constant::Int(v as i128)
    }
    pub fn i16(v: i16) -> Self {
        Constant::Int(v as i128)
    }
    pub fn i32(v: i32) -> Self {
        Constant::Int(v as i128)
    }
    pub fn i64(v: i64) -> Self {
        Constant::Int(v as i128)
    }
    pub fn u32(v: u32) -> Self {
        Constant::Int(v as i128)
    }
    pub fn u64(v: u64) -> Self {
        Constant::Int(v as i128)
    }
    /// Raw byte-array constant (no encoding claim).
    pub fn bytes(data: impl Into<Vec<u8>>) -> Self {
        Constant::Bytes {
            data: data.into(),
            utf8: false,
        }
    }
    /// UTF-8 string-byte constant. The flag is a CHECKED claim: prefer this
    /// constructor (which takes a `&str`, making the claim true by
    /// construction) over hand-building the variant.
    pub fn str_bytes(s: &str) -> Self {
        Constant::Bytes {
            data: s.as_bytes().to_vec(),
            utf8: true,
        }
    }
    /// The ONE sanctioned constructor from an unsigned 128-bit source: picks
    /// the canonical spelling by VALUE (`Int` for `v <= i128::MAX`, `U128`
    /// above). Building `Constant::U128` directly with a value at or below
    /// `i128::MAX` produces a NON-CANONICAL constant that the validator and
    /// the binary decoder reject (v24 one-spelling rule).
    pub fn u128(v: u128) -> Self {
        if v <= i128::MAX as u128 {
            Constant::Int(v as i128)
        } else {
            Constant::U128(v)
        }
    }
    /// Canonical-form check for the v24 one-spelling rule: `true` for every
    /// variant except a `U128` whose value `i128` could carry (which must be
    /// spelled `Int`). Composite constants are checked recursively — a
    /// non-canonical leaf poisons its enclosing aggregate.
    pub fn is_canonical_int_spelling(&self) -> bool {
        match self {
            Constant::U128(v) => *v > i128::MAX as u128,
            Constant::Aggregate(elems)
            | Constant::Array(elems)
            | Constant::Vector(elems)
            | Constant::Sequence(elems)
            | Constant::Set(elems) => elems.iter().all(Self::is_canonical_int_spelling),
            Constant::Record(fields) => fields.iter().all(|(_, c)| c.is_canonical_int_spelling()),
            Constant::Closure { captures, .. } => {
                captures.iter().all(Self::is_canonical_int_spelling)
            }
            _ => true,
        }
    }
    pub fn f32(v: f32) -> Self {
        Constant::Float(v as f64)
    }
    pub fn f64(v: f64) -> Self {
        Constant::Float(v)
    }
    pub fn vector(elems: impl IntoIterator<Item = Constant>) -> Self {
        Constant::Vector(elems.into_iter().collect())
    }
    /// Pointer-sized relocatable element holding `&symbol` (zero addend).
    pub fn symbol_addr(symbol: impl Into<String>) -> Self {
        Constant::SymbolAddr {
            symbol: symbol.into(),
            addend: 0,
        }
    }
    /// Pointer-sized relocatable element holding `&symbol + addend`.
    pub fn symbol_addr_with_addend(symbol: impl Into<String>, addend: i64) -> Self {
        Constant::SymbolAddr {
            symbol: symbol.into(),
            addend,
        }
    }
    pub fn vector_i32(values: impl IntoIterator<Item = i32>) -> Self {
        Constant::Vector(values.into_iter().map(Constant::i32).collect())
    }
    pub fn vector_i64(values: impl IntoIterator<Item = i64>) -> Self {
        Constant::Vector(values.into_iter().map(Constant::i64).collect())
    }
    pub fn v4_i32(values: [i32; 4]) -> Self {
        Constant::vector_i32(values)
    }
    pub fn v2_i64(values: [i64; 2]) -> Self {
        Constant::vector_i64(values)
    }
    pub fn splat_i32(lanes: usize, value: i32) -> Self {
        Constant::Vector((0..lanes).map(|_| Constant::i32(value)).collect())
    }
    pub fn splat_i64(lanes: usize, value: i64) -> Self {
        Constant::Vector((0..lanes).map(|_| Constant::i64(value)).collect())
    }
    pub fn zero_i32_vector(lanes: usize) -> Self {
        Constant::splat_i32(lanes, 0)
    }
    pub fn zero_i64_vector(lanes: usize) -> Self {
        Constant::splat_i64(lanes, 0)
    }
    pub fn all_ones_i32_mask(lanes: usize) -> Self {
        Constant::splat_i32(lanes, -1)
    }
    pub fn all_ones_i64_mask(lanes: usize) -> Self {
        Constant::splat_i64(lanes, -1)
    }
    pub fn v4_i32_zero_mask() -> Self {
        Constant::zero_i32_vector(4)
    }
    pub fn v4_i32_all_ones_mask() -> Self {
        Constant::all_ones_i32_mask(4)
    }
    pub fn v2_i64_zero_mask() -> Self {
        Constant::zero_i64_vector(2)
    }
    pub fn v2_i64_all_ones_mask() -> Self {
        Constant::all_ones_i64_mask(2)
    }
    pub fn vector_bool(values: impl IntoIterator<Item = bool>) -> Self {
        Constant::Vector(values.into_iter().map(Constant::Bool).collect())
    }
    pub fn v2_bool_mask(values: [bool; 2]) -> Self {
        Constant::vector_bool(values)
    }
    pub fn v4_bool_mask(values: [bool; 4]) -> Self {
        Constant::vector_bool(values)
    }
    pub fn v8_bool_mask(values: [bool; 8]) -> Self {
        Constant::vector_bool(values)
    }
    pub fn v16_bool_mask(values: [bool; 16]) -> Self {
        Constant::vector_bool(values)
    }
    pub fn splat_bool(lanes: usize, value: bool) -> Self {
        Constant::Vector((0..lanes).map(|_| Constant::Bool(value)).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i32_constructor() {
        let c = Constant::i32(42);
        assert_eq!(c, Constant::Int(42));
    }

    #[test]
    fn i64_constructor() {
        let c = Constant::i64(-100);
        assert_eq!(c, Constant::Int(-100));
    }

    #[test]
    fn u64_constructor() {
        let c = Constant::u64(u64::MAX);
        assert_eq!(c, Constant::Int(u64::MAX as i128));
    }

    #[test]
    fn u32_constructor() {
        let c = Constant::u32(999);
        assert_eq!(c, Constant::Int(999));
    }

    #[test]
    fn i8_constructor() {
        let c = Constant::i8(-1);
        assert_eq!(c, Constant::Int(-1));
    }

    #[test]
    fn i16_constructor() {
        let c = Constant::i16(32767);
        assert_eq!(c, Constant::Int(32767));
    }

    #[test]
    fn f32_constructor() {
        let c = Constant::f32(1.25);
        if let Constant::Float(v) = c {
            assert!((v - 1.25f32 as f64).abs() < 1e-5);
        } else {
            panic!("expected Float variant");
        }
    }

    #[test]
    fn f64_constructor() {
        let c = Constant::f64(2.75);
        assert_eq!(c, Constant::Float(2.75));
    }

    // --- Bit-exact float identity (issue: derived f64 PartialEq is unsound) ---

    #[test]
    fn float_equality_is_bit_exact_nan_is_reflexive() {
        // Derived `==` would make this FALSE (NaN != NaN); IR identity requires
        // reflexivity, so identical NaN bit patterns compare equal.
        let a = Constant::Float(f64::NAN);
        let b = Constant::Float(f64::NAN);
        assert_eq!(a, b);
        assert_eq!(a, a);

        // A signaling/quiet NaN with a distinct payload is a distinct constant.
        let quiet = Constant::Float(f64::from_bits(0x7ff8_0000_0000_0001));
        let other_payload = Constant::Float(f64::from_bits(0x7ff8_0000_0000_0002));
        assert_ne!(quiet, other_payload);
    }

    #[test]
    fn float_equality_distinguishes_signed_zero() {
        // Derived `==` would conflate these (-0.0 == +0.0); bit-exact identity
        // keeps them distinct because their sign bits differ.
        let neg = Constant::Float(-0.0);
        let pos = Constant::Float(0.0);
        assert_ne!(neg, pos);
        assert_eq!(neg, Constant::Float(-0.0));
        assert_eq!(pos, Constant::Float(0.0));
    }

    #[test]
    fn float_equality_inside_aggregates_is_bit_exact() {
        // The bit-exact rule recurses through composite constants.
        let nan_vec_a = Constant::Vector(vec![Constant::Float(f64::NAN)]);
        let nan_vec_b = Constant::Vector(vec![Constant::Float(f64::NAN)]);
        assert_eq!(nan_vec_a, nan_vec_b);

        let neg_zero_rec = Constant::Record(vec![("x".to_string(), Constant::Float(-0.0))]);
        let pos_zero_rec = Constant::Record(vec![("x".to_string(), Constant::Float(0.0))]);
        assert_ne!(neg_zero_rec, pos_zero_rec);
    }

    #[test]
    fn constant_hash_is_consistent_with_eq() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash_of(c: &Constant) -> u64 {
            let mut h = DefaultHasher::new();
            c.hash(&mut h);
            h.finish()
        }

        // Equal values (including NaN) hash equal.
        let nan_a = Constant::Float(f64::NAN);
        let nan_b = Constant::Float(f64::NAN);
        assert_eq!(nan_a, nan_b);
        assert_eq!(hash_of(&nan_a), hash_of(&nan_b));

        // -0.0 and +0.0 are distinct and (almost surely) hash differently.
        let neg = Constant::Float(-0.0);
        let pos = Constant::Float(0.0);
        assert_ne!(neg, pos);
        assert_ne!(hash_of(&neg), hash_of(&pos));

        // `Constant` is usable as a HashSet key.
        let mut set = std::collections::HashSet::new();
        assert!(set.insert(Constant::Float(f64::NAN)));
        // Re-inserting the same NaN value is a duplicate (Eq + Hash agree).
        assert!(!set.insert(Constant::Float(f64::NAN)));
        assert!(set.insert(Constant::Float(-0.0)));
        assert!(set.insert(Constant::Float(0.0)));
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn distinct_variants_with_same_payload_hash_distinctly() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn hash_of(c: &Constant) -> u64 {
            let mut h = DefaultHasher::new();
            c.hash(&mut h);
            h.finish()
        }

        let elems = vec![Constant::Int(1), Constant::Int(2)];
        let agg = Constant::Aggregate(elems.clone());
        let seq = Constant::Sequence(elems.clone());
        let set = Constant::Set(elems);
        // Eq already distinguishes them; Hash must too (discriminant-first).
        assert_ne!(agg, seq);
        assert_ne!(hash_of(&agg), hash_of(&seq));
        assert_ne!(hash_of(&seq), hash_of(&set));
    }

    #[test]
    fn bool_variant() {
        let t = Constant::Bool(true);
        let f = Constant::Bool(false);
        assert_eq!(t, Constant::Bool(true));
        assert_eq!(f, Constant::Bool(false));
        assert_ne!(t, f);
    }

    #[test]
    fn aggregate_variant() {
        let agg = Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Int(2),
            Constant::Float(3.0),
        ]);
        if let Constant::Aggregate(elems) = &agg {
            assert_eq!(elems.len(), 3);
            assert_eq!(elems[0], Constant::Int(1));
        } else {
            panic!("expected Aggregate variant");
        }
    }

    #[test]
    fn vector_i32_constructor() {
        assert_eq!(
            Constant::vector_i32([1, -2, 3, -4]),
            Constant::Vector(vec![
                Constant::Int(1),
                Constant::Int(-2),
                Constant::Int(3),
                Constant::Int(-4),
            ])
        );
        assert_eq!(
            Constant::all_ones_i32_mask(4),
            Constant::Vector(vec![Constant::Int(-1); 4])
        );
    }

    #[test]
    fn v4_i32_chc_x86_mask_constructors() {
        assert_eq!(
            Constant::v4_i32([1, -2, 0, i32::MIN]),
            Constant::Vector(vec![
                Constant::Int(1),
                Constant::Int(-2),
                Constant::Int(0),
                Constant::Int(i32::MIN as i128),
            ])
        );
        assert_eq!(
            Constant::v4_i32_zero_mask(),
            Constant::Vector(vec![Constant::Int(0); 4])
        );
        assert_eq!(
            Constant::v4_i32_all_ones_mask(),
            Constant::Vector(vec![Constant::Int(-1); 4])
        );
    }

    #[test]
    fn v2_i64_chc_x86_mask_constructors() {
        assert_eq!(
            Constant::v2_i64([1, i64::MIN]),
            Constant::Vector(vec![Constant::Int(1), Constant::Int(i64::MIN as i128),])
        );
        assert_eq!(
            Constant::v2_i64_zero_mask(),
            Constant::Vector(vec![Constant::Int(0); 2])
        );
        assert_eq!(
            Constant::v2_i64_all_ones_mask(),
            Constant::Vector(vec![Constant::Int(-1); 2])
        );
    }

    #[test]
    fn vector_bool_constructor() {
        assert_eq!(
            Constant::vector_bool([true, false, true, false]),
            Constant::Vector(vec![
                Constant::Bool(true),
                Constant::Bool(false),
                Constant::Bool(true),
                Constant::Bool(false),
            ])
        );
        assert_eq!(
            Constant::splat_bool(3, true),
            Constant::Vector(vec![Constant::Bool(true); 3])
        );
    }

    #[test]
    fn v4_bool_mask_constructor() {
        assert_eq!(
            Constant::v4_bool_mask([true, false, true, false]),
            Constant::Vector(vec![
                Constant::Bool(true),
                Constant::Bool(false),
                Constant::Bool(true),
                Constant::Bool(false),
            ])
        );
    }

    #[test]
    fn nested_aggregate() {
        let inner = Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]);
        let outer = Constant::Aggregate(vec![inner.clone(), Constant::Bool(true)]);
        if let Constant::Aggregate(elems) = &outer {
            assert_eq!(elems.len(), 2);
            assert_eq!(elems[0], inner);
        } else {
            panic!("expected Aggregate variant");
        }
    }

    #[test]
    fn display_int() {
        assert_eq!(format!("{}", Constant::Int(42)), "42");
        assert_eq!(format!("{}", Constant::Int(-1)), "-1");
    }

    #[test]
    fn display_float() {
        let output = format!("{}", Constant::Float(1.25));
        assert!(output.contains("1.25"));
    }

    #[test]
    fn display_bool() {
        assert_eq!(format!("{}", Constant::Bool(true)), "true");
        assert_eq!(format!("{}", Constant::Bool(false)), "false");
    }

    #[test]
    fn display_aggregate() {
        let agg = Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]);
        let output = format!("{}", agg);
        assert!(output.contains("1"));
        assert!(output.contains("2"));
    }

    // --- NEW CONSTANT TESTS ---

    #[test]
    fn display_aggregate_exact_format() {
        let agg = Constant::Aggregate(vec![Constant::Int(10), Constant::Int(20)]);
        assert_eq!(format!("{}", agg), "{ 10, 20 }");
    }

    #[test]
    fn display_nested_aggregate_format() {
        let inner = Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]);
        let outer = Constant::Aggregate(vec![inner, Constant::Bool(true)]);
        assert_eq!(format!("{}", outer), "{ { 1, 2 }, true }");
    }

    #[test]
    fn display_empty_aggregate() {
        let agg = Constant::Aggregate(vec![]);
        assert_eq!(format!("{}", agg), "{  }");
    }

    #[test]
    fn display_single_element_aggregate() {
        let agg = Constant::Aggregate(vec![Constant::Float(1.5)]);
        assert_eq!(format!("{}", agg), "{ 1.5 }");
    }

    #[test]
    fn large_integer_constant() {
        let large = Constant::Int(i128::MAX);
        assert_eq!(
            format!("{}", large),
            "170141183460469231731687303715884105727"
        );
    }

    // --- v24: the 128-bit-faithful carrier (RFC TRUST_IR_V2 B1 breaking-batch member) ---

    #[test]
    fn u128_constructor_picks_canonical_spelling_by_value() {
        // Everything i128 can carry is spelled Int — including the boundary.
        assert_eq!(Constant::u128(0), Constant::Int(0));
        assert_eq!(Constant::u128(5), Constant::Int(5));
        assert_eq!(Constant::u128(i128::MAX as u128), Constant::Int(i128::MAX));
        // The first value i128 cannot carry is the first U128.
        assert_eq!(
            Constant::u128(i128::MAX as u128 + 1),
            Constant::U128(i128::MAX as u128 + 1)
        );
        assert_eq!(Constant::u128(u128::MAX), Constant::U128(u128::MAX));
    }

    #[test]
    fn u128_canonicality_predicate() {
        assert!(Constant::U128(i128::MAX as u128 + 1).is_canonical_int_spelling());
        assert!(Constant::U128(u128::MAX).is_canonical_int_spelling());
        // A U128 whose value i128 could carry is the non-canonical spelling.
        assert!(!Constant::U128(5).is_canonical_int_spelling());
        assert!(!Constant::U128(i128::MAX as u128).is_canonical_int_spelling());
        // Every Int is canonical (Int is the sanctioned spelling for its range).
        assert!(Constant::Int(i128::MAX).is_canonical_int_spelling());
        assert!(Constant::Int(-1).is_canonical_int_spelling());
        // Recursion: a non-canonical leaf poisons the enclosing aggregate.
        assert!(!Constant::Aggregate(vec![Constant::U128(5)]).is_canonical_int_spelling());
        assert!(Constant::Aggregate(vec![Constant::U128(u128::MAX)]).is_canonical_int_spelling());
        assert!(
            !Constant::Record(vec![("f".into(), Constant::U128(1))]).is_canonical_int_spelling()
        );
        assert!(
            !Constant::Closure {
                func: crate::value::FuncId::new(0),
                captures: vec![Constant::U128(1)],
            }
            .is_canonical_int_spelling()
        );
    }

    #[test]
    fn u128_display_prints_true_value() {
        assert_eq!(
            format!("{}", Constant::U128(u128::MAX)),
            "340282366920938463463374607431768211455"
        );
        assert_eq!(
            format!("{}", Constant::U128(i128::MAX as u128 + 1)),
            "170141183460469231731687303715884105728"
        );
    }

    // --- v25: Constant::Bytes (RFC TRUST_IR_V2 B1, byte-array carrier) ---

    #[test]
    fn bytes_constructors_and_identity() {
        let raw = Constant::bytes(vec![0u8, 255, 16]);
        assert_eq!(
            raw,
            Constant::Bytes {
                data: vec![0, 255, 16],
                utf8: false
            }
        );
        let s = Constant::str_bytes("hé");
        assert_eq!(
            s,
            Constant::Bytes {
                data: "hé".as_bytes().to_vec(),
                utf8: true
            }
        );
        // The utf8 claim is part of value identity.
        assert_ne!(
            Constant::Bytes {
                data: b"hi".to_vec(),
                utf8: true
            },
            Constant::Bytes {
                data: b"hi".to_vec(),
                utf8: false
            }
        );
    }

    #[test]
    fn bytes_display_is_hex_and_flag_spelled() {
        assert_eq!(
            format!("{}", Constant::bytes(vec![0xde, 0xad, 0xbe, 0xef])),
            "bytes<deadbeef>"
        );
        assert_eq!(format!("{}", Constant::str_bytes("hi")), "utf8bytes<6869>");
        assert_eq!(format!("{}", Constant::bytes(Vec::new())), "bytes<>");
    }

    #[test]
    fn u128_eq_and_hash_are_value_faithful() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        fn hash_of(c: &Constant) -> u64 {
            let mut h = DefaultHasher::new();
            c.hash(&mut h);
            h.finish()
        }
        let a = Constant::U128(u128::MAX);
        let b = Constant::U128(u128::MAX);
        assert_eq!(a, b);
        assert_eq!(hash_of(&a), hash_of(&b));
        assert_ne!(Constant::U128(u128::MAX), Constant::U128(u128::MAX - 1));
        // Cross-variant: never equal (canonical values never overlap anyway).
        assert_ne!(Constant::U128(u128::MAX), Constant::Int(-1));
    }

    #[test]
    fn negative_integer_constant() {
        let neg = Constant::Int(i128::MIN);
        assert_eq!(
            format!("{}", neg),
            "-170141183460469231731687303715884105728"
        );
    }

    #[test]
    fn zero_float_constant() {
        // Float display must always be unambiguously a float literal so
        // `parse(display(x)) == x` holds (issue #45). `0.0` must NOT be
        // emitted as bare `0` (which the parser would read as
        // `Constant::Int(0)`).
        let zero = Constant::Float(0.0);
        assert_eq!(format!("{}", zero), "0.0");
    }

    #[test]
    fn negative_float_constant() {
        let neg = Constant::Float(-99.5);
        assert_eq!(format!("{}", neg), "-99.5");
    }

    #[test]
    fn constant_clone_equality() {
        let c = Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Float(2.0),
            Constant::Bool(true),
        ]);
        let cloned = c.clone();
        assert_eq!(c, cloned);
    }

    // --- New aggregate / closure constants (issue #30) ---

    #[test]
    fn sequence_constant_preserves_order() {
        let s = Constant::Sequence(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)]);
        if let Constant::Sequence(elems) = &s {
            assert_eq!(elems.len(), 3);
            assert_eq!(elems[0], Constant::Int(1));
            assert_eq!(elems[2], Constant::Int(3));
        } else {
            panic!("expected Sequence");
        }
    }

    #[test]
    fn sequence_constant_display() {
        let s = Constant::Sequence(vec![Constant::Int(7), Constant::Int(8)]);
        assert_eq!(format!("{}", s), "seq[ 7, 8 ]");
    }

    #[test]
    fn set_constant_basic() {
        let s = Constant::Set(vec![Constant::Int(1), Constant::Int(2)]);
        if let Constant::Set(elems) = &s {
            assert_eq!(elems.len(), 2);
        } else {
            panic!("expected Set");
        }
        assert_eq!(format!("{}", s), "set{ 1, 2 }");
    }

    #[test]
    fn record_constant_named_fields() {
        let r = Constant::Record(vec![
            ("x".to_string(), Constant::Int(10)),
            ("y".to_string(), Constant::Int(20)),
        ]);
        if let Constant::Record(fields) = &r {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "x");
            assert_eq!(fields[0].1, Constant::Int(10));
            assert_eq!(fields[1].0, "y");
        } else {
            panic!("expected Record");
        }
    }

    #[test]
    fn record_constant_display_named_fields() {
        let r = Constant::Record(vec![
            ("a".to_string(), Constant::Int(1)),
            ("b".to_string(), Constant::Bool(true)),
        ]);
        assert_eq!(format!("{}", r), "record{ a = 1, b = true }");
    }

    #[test]
    fn closure_constant_holds_func_and_captures() {
        use crate::value::FuncId;
        let c = Constant::Closure {
            func: FuncId::new(3),
            captures: vec![Constant::Int(42), Constant::Bool(false)],
        };
        if let Constant::Closure { func, captures } = &c {
            assert_eq!(*func, FuncId::new(3));
            assert_eq!(captures.len(), 2);
            assert_eq!(captures[0], Constant::Int(42));
        } else {
            panic!("expected Closure");
        }
    }

    #[test]
    fn closure_constant_display() {
        use crate::value::FuncId;
        let c = Constant::Closure {
            func: FuncId::new(2),
            captures: vec![Constant::Int(1)],
        };
        assert_eq!(format!("{}", c), "closure<func.2>{ 1 }");
    }

    #[test]
    fn closure_constant_no_captures_display() {
        use crate::value::FuncId;
        let c = Constant::Closure {
            func: FuncId::new(7),
            captures: vec![],
        };
        assert_eq!(format!("{}", c), "closure<func.7>{ }");
    }

    #[test]
    fn new_constants_are_distinct_variants() {
        // Sequence, Set, Aggregate with same element list are distinct values:
        // their variant identity matters for type-directed lowering.
        let elems = vec![Constant::Int(1), Constant::Int(2)];
        let agg = Constant::Aggregate(elems.clone());
        let seq = Constant::Sequence(elems.clone());
        let set = Constant::Set(elems);
        assert_ne!(agg, seq);
        assert_ne!(seq, set);
        assert_ne!(agg, set);
    }

    #[test]
    fn clone_new_constants() {
        use crate::value::FuncId;
        let s = Constant::Sequence(vec![Constant::Int(1)]);
        assert_eq!(s.clone(), s);
        let set = Constant::Set(vec![Constant::Bool(true)]);
        assert_eq!(set.clone(), set);
        let rec = Constant::Record(vec![("k".to_string(), Constant::Int(0))]);
        assert_eq!(rec.clone(), rec);
        let clos = Constant::Closure {
            func: FuncId::new(0),
            captures: vec![Constant::Int(1)],
        };
        assert_eq!(clos.clone(), clos);
    }

    // --- SymbolAddr: relocatable symbol-address initializer element ---

    #[test]
    fn symbol_addr_constructor_zero_addend() {
        let c = Constant::symbol_addr("vtable_slot_fn");
        assert_eq!(
            c,
            Constant::SymbolAddr {
                symbol: "vtable_slot_fn".to_string(),
                addend: 0,
            }
        );
    }

    #[test]
    fn symbol_addr_constructor_with_addend() {
        let c = Constant::symbol_addr_with_addend("data_global", 16);
        assert_eq!(
            c,
            Constant::SymbolAddr {
                symbol: "data_global".to_string(),
                addend: 16,
            }
        );
    }

    #[test]
    fn symbol_addr_negative_addend() {
        let c = Constant::symbol_addr_with_addend("g", -8);
        if let Constant::SymbolAddr { symbol, addend } = c {
            assert_eq!(symbol, "g");
            assert_eq!(addend, -8);
        } else {
            panic!("expected SymbolAddr variant");
        }
    }

    #[test]
    fn symbol_addr_is_distinct_from_int() {
        // A relocatable address element must not compare equal to any integer
        // bit-pattern: the linker decides the value, so identity is by variant.
        assert_ne!(Constant::symbol_addr("f"), Constant::Int(0));
    }

    #[test]
    fn symbol_addr_clone_and_display() {
        let c = Constant::symbol_addr_with_addend("fa", 8);
        assert_eq!(c.clone(), c);
        assert_eq!(format!("{}", c), "symaddr<fa + 8>");
        assert_eq!(format!("{}", Constant::symbol_addr("fb")), "symaddr<fb>");
    }

    #[test]
    fn vtable_aggregate_of_symbol_addrs() {
        // A mini-vtable: an aggregate whose elements are function addresses.
        let vtable = Constant::Aggregate(vec![
            Constant::symbol_addr("fa"),
            Constant::symbol_addr("fb"),
            Constant::symbol_addr("fc"),
        ]);
        if let Constant::Aggregate(elems) = &vtable {
            assert_eq!(elems.len(), 3);
            assert!(matches!(&elems[0], Constant::SymbolAddr { symbol, addend }
                if symbol == "fa" && *addend == 0));
        } else {
            panic!("expected Aggregate variant");
        }
    }

    // --- Issue #48: bit-exact f64 serde round-trips ---
    //
    // These tests exercise the custom `float_bits` codec on `Constant::Float`.
    // The goal is bit-exact preservation of every IEEE-754 pattern through
    // both JSON (lossy by default) and MessagePack (bit-faithful for finite
    // values, but we still want the wire format to be symmetric across
    // formats so callers can reason about one shape).

    #[cfg(feature = "serde")]
    mod serde_float_bits {
        use super::*;

        /// Assert that `value`, wrapped in `Constant::Float`, round-trips
        /// through `serde_json::{to_string, from_str}` with every one of its
        /// 64 IEEE-754 bits preserved.
        fn assert_json_bit_exact(value: f64) {
            let c = Constant::Float(value);
            let json = serde_json::to_string(&c).expect("serialize Constant::Float to JSON");
            let decoded: Constant =
                serde_json::from_str(&json).expect("deserialize Constant::Float from JSON");
            match decoded {
                Constant::Float(v) => assert_eq!(
                    v.to_bits(),
                    value.to_bits(),
                    "JSON round-trip changed bits for input bits {:016x}; json={json}",
                    value.to_bits()
                ),
                other => panic!("expected Constant::Float, got {:?}", other),
            }
        }

        /// Assert that `value`, wrapped in `Constant::Float`, round-trips
        /// through `rmp_serde::{to_vec, from_slice}` with all 64 bits
        /// preserved. MessagePack is bit-faithful natively for finite f64,
        /// but we still exercise the custom codec path to guarantee the
        /// `Constant::Float` wire shape is symmetric with JSON.
        fn assert_msgpack_bit_exact(value: f64) {
            let c = Constant::Float(value);
            let bytes = rmp_serde::to_vec(&c).expect("serialize Constant::Float to MessagePack");
            let decoded: Constant = rmp_serde::from_slice(&bytes)
                .expect("deserialize Constant::Float from MessagePack");
            match decoded {
                Constant::Float(v) => assert_eq!(
                    v.to_bits(),
                    value.to_bits(),
                    "MessagePack round-trip changed bits for {:016x}",
                    value.to_bits()
                ),
                other => panic!("expected Constant::Float, got {:?}", other),
            }
        }

        #[test]
        fn json_roundtrip_quiet_nan_with_payload() {
            assert_json_bit_exact(f64::from_bits(0x7ff8_0000_1234_5678));
        }

        #[test]
        fn json_roundtrip_signaling_nan() {
            assert_json_bit_exact(f64::from_bits(0x7ff0_0000_0000_0001));
        }

        #[test]
        fn json_roundtrip_positive_infinity() {
            assert_json_bit_exact(f64::INFINITY);
        }

        #[test]
        fn json_roundtrip_negative_infinity() {
            assert_json_bit_exact(f64::NEG_INFINITY);
        }

        #[test]
        fn json_roundtrip_negative_zero() {
            assert_json_bit_exact(-0.0_f64);
        }

        #[test]
        fn json_roundtrip_positive_zero() {
            assert_json_bit_exact(0.0_f64);
        }

        #[test]
        fn json_roundtrip_smallest_subnormal() {
            assert_json_bit_exact(f64::from_bits(1));
        }

        #[test]
        fn json_roundtrip_min_positive_normal() {
            assert_json_bit_exact(f64::MIN_POSITIVE);
        }

        #[test]
        fn json_roundtrip_largest_finite() {
            assert_json_bit_exact(f64::from_bits(0x7fef_ffff_ffff_ffff));
            assert_json_bit_exact(f64::from_bits(0xffef_ffff_ffff_ffff));
        }

        #[test]
        fn json_roundtrip_issue_48_pattern() {
            assert_json_bit_exact(2.1747727453455723e-213);
        }

        #[test]
        fn json_roundtrip_exponent_sweep() {
            // One bit pattern per biased exponent across the full
            // finite range: 0 (subnormals) through 2046 (largest
            // normal). We pair each exponent with the smallest
            // non-zero mantissa so we exercise values that were
            // historically prone to decimal-round-trip loss.
            for biased_exp in 0_u64..=2046 {
                let bits = (biased_exp << 52) | 1;
                assert_json_bit_exact(f64::from_bits(bits));
            }
        }

        #[test]
        fn json_roundtrip_mantissa_sweep() {
            // Walk a single set bit across every mantissa position
            // at a fixed biased exponent of 1 (smallest normal
            // exponent). This catches any codec that truncates
            // low-order mantissa bits.
            for shift in 0..52 {
                let bits = (1_u64 << 52) | (1_u64 << shift);
                assert_json_bit_exact(f64::from_bits(bits));
            }
        }

        #[test]
        fn msgpack_roundtrip_all_corners() {
            let corners = [
                f64::from_bits(0x7ff8_0000_1234_5678), // quiet NaN with payload
                f64::from_bits(0x7ff0_0000_0000_0001), // signaling NaN
                f64::INFINITY,
                f64::NEG_INFINITY,
                -0.0_f64,
                0.0_f64,
                f64::from_bits(1),                     // smallest subnormal
                f64::MIN_POSITIVE,                     // smallest normal
                f64::from_bits(0x7fef_ffff_ffff_ffff), // largest finite
                2.1747727453455723e-213,               // issue-48 documented pattern
            ];
            for v in corners {
                assert_msgpack_bit_exact(v);
            }
        }

        #[test]
        fn json_wire_shape_is_bits_object() {
            // Pin the wire format so downstream tools (tRust, TrustIr)
            // know what to expect. The `Constant::Float` variant
            // serializes as `{"Float":{"bits":<u64>}}` rather than
            // `{"Float":<number>}`.
            let c = Constant::Float(1.5);
            let json = serde_json::to_string(&c).expect("serialize");
            assert_eq!(
                json,
                format!(r#"{{"Float":{{"bits":{}}}}}"#, 1.5_f64.to_bits())
            );
        }
    }
}
