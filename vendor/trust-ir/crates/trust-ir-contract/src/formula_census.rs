// trust-ir-contract/formula_census: every `Formula` variant, and a witness of
// each
//
// An exhaustiveness test over `Formula` needs two things a hand-written list
// cannot give: the COMPLETE set of variants, and a well-sorted instance of
// each. `formula_variant_names` reads the set from the serde derive itself (a
// variant added to the enum appears here with no edit), and `witnesses` is the
// instance list; a test of this crate holds the two equal, so a new variant
// fails it until it has a witness. Downstream exhaustive walkers (digests,
// bridges, printers) can test themselves against the same list.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::{Formula, RoundingMode, Sort};
use crate::interner::Symbol;
use serde::de::{self, Deserialize, Deserializer, Visitor};

/// A deserializer that answers nothing and records the variant list an enum's
/// derived `Deserialize` hands to `deserialize_enum`.
struct VariantProbe {
    variants: Option<&'static [&'static str]>,
}

impl<'de> Deserializer<'de> for &mut VariantProbe {
    type Error = de::value::Error;

    fn deserialize_any<V: Visitor<'de>>(self, _visitor: V) -> Result<V::Value, Self::Error> {
        Err(de::Error::custom("variant probe: not a real input"))
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.variants = Some(variants);
        Err(de::Error::custom("variant probe: variants recorded"))
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

/// The name of every [`Formula`] variant, in declaration order, as the
/// derived `Deserialize` lists them. Complete by construction: the list is
/// generated from the enum.
///
/// ```
/// use trust_ir_contract::formula_census::formula_variant_names;
///
/// let names = formula_variant_names();
/// assert_eq!(names.first(), Some(&"Bool"));
/// assert!(names.contains(&"ConstArray"));
/// ```
#[must_use]
pub fn formula_variant_names() -> &'static [&'static str] {
    let mut probe = VariantProbe { variants: None };
    // The probe refuses every input; only the recorded list matters.
    let _ = Formula::deserialize(&mut probe);
    probe.variants.unwrap_or(&[])
}

/// The variant name of `f`, as serde spells it (the externally tagged key).
/// Reads the variant only, never the children.
#[must_use]
pub fn variant_name(f: &Formula) -> &'static str {
    // `index` is the position in `formula_variant_names`; the derived
    // `Serialize` passes it to every `serialize_*_variant` call.
    let names = formula_variant_names();
    names.get(variant_index(f)).copied().unwrap_or("")
}

/// The declaration-order index of `f`'s variant, read through the derived
/// `Serialize` (which passes it as `variant_index`) without serializing any
/// payload.
fn variant_index(f: &Formula) -> usize {
    use serde::Serialize;
    use serde::ser::{self, Impossible};

    #[derive(Debug)]
    struct Found(u32);
    impl std::fmt::Display for Found {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "variant {}", self.0)
        }
    }
    impl std::error::Error for Found {}
    impl ser::Error for Found {
        fn custom<T: std::fmt::Display>(_msg: T) -> Self {
            Found(u32::MAX)
        }
    }

    /// Stops at the variant header: every `*_variant` method fails with the
    /// index, every other method is never reached by an enum's derive.
    struct Probe;
    macro_rules! unreachable_scalar {
        ($($name:ident: $ty:ty),* $(,)?) => {$(
            fn $name(self, _v: $ty) -> Result<(), Found> { Err(Found(u32::MAX)) }
        )*};
    }
    impl ser::Serializer for Probe {
        type Ok = ();
        type Error = Found;
        type SerializeSeq = Impossible<(), Found>;
        type SerializeTuple = Impossible<(), Found>;
        type SerializeTupleStruct = Impossible<(), Found>;
        type SerializeTupleVariant = Impossible<(), Found>;
        type SerializeMap = Impossible<(), Found>;
        type SerializeStruct = Impossible<(), Found>;
        type SerializeStructVariant = Impossible<(), Found>;

        unreachable_scalar! {
            serialize_bool: bool, serialize_i8: i8, serialize_i16: i16,
            serialize_i32: i32, serialize_i64: i64, serialize_i128: i128,
            serialize_u8: u8, serialize_u16: u16, serialize_u32: u32,
            serialize_u64: u64, serialize_u128: u128, serialize_f32: f32,
            serialize_f64: f64, serialize_char: char, serialize_str: &str,
            serialize_bytes: &[u8],
        }
        fn serialize_none(self) -> Result<(), Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_some<T: ?Sized + Serialize>(self, _v: &T) -> Result<(), Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_unit(self) -> Result<(), Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_unit_struct(self, _name: &'static str) -> Result<(), Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_unit_variant(
            self,
            _name: &'static str,
            index: u32,
            _variant: &'static str,
        ) -> Result<(), Found> {
            Err(Found(index))
        }
        fn serialize_newtype_struct<T: ?Sized + Serialize>(
            self,
            _name: &'static str,
            _v: &T,
        ) -> Result<(), Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_newtype_variant<T: ?Sized + Serialize>(
            self,
            _name: &'static str,
            index: u32,
            _variant: &'static str,
            _v: &T,
        ) -> Result<(), Found> {
            Err(Found(index))
        }
        fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_tuple_struct(
            self,
            _name: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeTupleStruct, Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_tuple_variant(
            self,
            _name: &'static str,
            index: u32,
            _variant: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeTupleVariant, Found> {
            Err(Found(index))
        }
        fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_struct(
            self,
            _name: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeStruct, Found> {
            Err(Found(u32::MAX))
        }
        fn serialize_struct_variant(
            self,
            _name: &'static str,
            index: u32,
            _variant: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeStructVariant, Found> {
            Err(Found(index))
        }
    }

    match f.serialize(Probe) {
        Err(Found(index)) => usize::try_from(index).unwrap_or(usize::MAX),
        Ok(()) => usize::MAX,
    }
}

/// The SMT-LIB declarations of the vocabulary [`witnesses`] use, in an order
/// a solver accepts (the datatype before the constant of its sort).
#[must_use]
pub fn witness_declarations() -> String {
    let mut out = String::new();
    for decl in level_sort().datatype_declarations() {
        out.push_str(&decl);
        out.push('\n');
    }
    for (name, sort) in witness_constants() {
        out.push_str(&format!("(declare-const {name} {})\n", sort.to_smtlib()));
    }
    out.push_str("(declare-fun ready (Int) Bool)\n");
    out.push_str("(declare-fun flag () Bool)\n");
    out.push_str("(declare-fun f (Int) Int)\n");
    out.push_str("(declare-fun c () Int)\n");
    out
}

fn f32_sort() -> Sort {
    Sort::Float { eb: 8, sb: 24 }
}

fn int_array() -> Sort {
    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))
}

/// `Level = zero | succ(pred: Level)`, the recursive datatype of the
/// witnesses (the recursive field is a by-name reference).
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

fn witness_constants() -> Vec<(&'static str, Sort)> {
    vec![
        ("x", Sort::Int),
        ("y", Sort::Int),
        ("z", Sort::Int),
        ("p", Sort::Bool),
        ("q", Sort::Bool),
        ("r", Sort::Real),
        ("a", Sort::BitVec(8)),
        ("b", Sort::BitVec(8)),
        ("w32", Sort::BitVec(32)),
        ("fa", f32_sort()),
        ("fb", f32_sort()),
        ("fc", f32_sort()),
        ("arr", int_array()),
        ("lv", level_sort()),
    ]
}

/// At least one well-sorted witness of every [`Formula`] variant (several
/// for variants whose spelling has cases: the arities of `And`/`Or`, signed
/// and unsigned literals and conversions, nullary applications). Every free
/// symbol is declared by [`witness_declarations`].
#[must_use]
#[allow(clippy::too_many_lines)] // one witness per variant, by design
pub fn witnesses() -> Vec<Formula> {
    fn bx(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    let var = |name: &str, sort: Sort| Formula::Var(name.into(), sort);
    let x = || var("x", Sort::Int);
    let y = || var("y", Sort::Int);
    let p = || var("p", Sort::Bool);
    let q = || var("q", Sort::Bool);
    let a = || var("a", Sort::BitVec(8));
    let b = || var("b", Sort::BitVec(8));
    let w32 = || var("w32", Sort::BitVec(32));
    let fa = || var("fa", f32_sort());
    let fb = || var("fb", f32_sort());
    let fc = || var("fc", f32_sort());
    let lv = || var("lv", level_sort());
    let arr = || var("arr", int_array());
    let rne = || Formula::FpRoundingMode(RoundingMode::RNE);
    let k = Symbol::intern("k");
    let kv = || Formula::SymVar(k, Sort::Int);

    vec![
        // Literals and variables
        Formula::Bool(true),
        Formula::Bool(false),
        Formula::Int(7),
        Formula::Int(-5),
        Formula::UInt(9),
        Formula::BitVec { value: 5, width: 8 },
        Formula::BitVec {
            value: -1,
            width: 8,
        },
        x(),
        Formula::SymVar(Symbol::intern("z"), Sort::Int),
        Formula::rat("1", "2").unwrap_or(Formula::Bool(false)),
        Formula::rat("-7", "3").unwrap_or(Formula::Bool(false)),
        Formula::rat_from_int(5),
        // Boolean connectives
        Formula::Not(bx(p())),
        Formula::And(vec![p(), q()]),
        Formula::And(vec![]),
        Formula::And(vec![p()]),
        Formula::Or(vec![p(), q()]),
        Formula::Or(vec![]),
        Formula::Or(vec![q()]),
        Formula::Implies(bx(p()), bx(q())),
        // Comparisons and integer arithmetic
        Formula::Eq(bx(x()), bx(y())),
        Formula::Lt(bx(x()), bx(y())),
        Formula::Le(bx(x()), bx(y())),
        Formula::Gt(bx(x()), bx(y())),
        Formula::Ge(bx(x()), bx(y())),
        Formula::Add(bx(x()), bx(y())),
        Formula::Sub(bx(x()), bx(y())),
        Formula::Mul(bx(x()), bx(Formula::Int(3))),
        Formula::Div(bx(x()), bx(Formula::Int(3))),
        Formula::Rem(bx(x()), bx(Formula::Int(-3))),
        Formula::Neg(bx(x())),
        // Bitvectors
        Formula::BvAdd(bx(a()), bx(b()), 8),
        Formula::BvSub(bx(a()), bx(b()), 8),
        Formula::BvMul(bx(a()), bx(b()), 8),
        Formula::BvUDiv(bx(a()), bx(b()), 8),
        Formula::BvSDiv(bx(a()), bx(b()), 8),
        Formula::BvURem(bx(a()), bx(b()), 8),
        Formula::BvSRem(bx(a()), bx(b()), 8),
        Formula::BvAnd(bx(a()), bx(b()), 8),
        Formula::BvOr(bx(a()), bx(b()), 8),
        Formula::BvXor(bx(a()), bx(b()), 8),
        Formula::BvNot(bx(a()), 8),
        Formula::BvShl(bx(a()), bx(b()), 8),
        Formula::BvLShr(bx(a()), bx(b()), 8),
        Formula::BvAShr(bx(a()), bx(b()), 8),
        Formula::BvULt(bx(a()), bx(b()), 8),
        Formula::BvULe(bx(a()), bx(b()), 8),
        Formula::BvSLt(bx(a()), bx(b()), 8),
        Formula::BvSLe(bx(a()), bx(b()), 8),
        Formula::BvToInt(bx(a()), 8, true),
        Formula::BvToInt(bx(a()), 8, false),
        Formula::IntToBv(bx(x()), 8),
        Formula::BvExtract {
            inner: bx(a()),
            high: 7,
            low: 4,
        },
        Formula::BvConcat(bx(a()), bx(b())),
        Formula::BvZeroExt(bx(a()), 8),
        Formula::BvSignExt(bx(a()), 8),
        // Floating point
        Formula::FpConst {
            bits: 0x3f80_0000,
            eb: 8,
            sb: 24,
        },
        Formula::FpNaN { eb: 8, sb: 24 },
        Formula::FpInf {
            neg: false,
            eb: 8,
            sb: 24,
        },
        Formula::FpInf {
            neg: true,
            eb: 8,
            sb: 24,
        },
        Formula::FpZero {
            neg: false,
            eb: 8,
            sb: 24,
        },
        Formula::FpZero {
            neg: true,
            eb: 8,
            sb: 24,
        },
        rne(),
        Formula::FpRoundingMode(RoundingMode::RTZ),
        Formula::FpAdd(bx(rne()), bx(fa()), bx(fb())),
        Formula::FpSub(bx(rne()), bx(fa()), bx(fb())),
        Formula::FpMul(bx(rne()), bx(fa()), bx(fb())),
        Formula::FpDiv(bx(rne()), bx(fa()), bx(fb())),
        Formula::FpFma(bx(rne()), bx(fa()), bx(fb()), bx(fc())),
        Formula::FpSqrt(bx(rne()), bx(fa())),
        Formula::FpRem(bx(fa()), bx(fb())),
        Formula::FpNeg(bx(fa())),
        Formula::FpAbs(bx(fa())),
        Formula::FpMin(bx(fa()), bx(fb())),
        Formula::FpMax(bx(fa()), bx(fb())),
        Formula::FpEq(bx(fa()), bx(fb())),
        Formula::FpLt(bx(fa()), bx(fb())),
        Formula::FpLe(bx(fa()), bx(fb())),
        Formula::FpGt(bx(fa()), bx(fb())),
        Formula::FpGe(bx(fa()), bx(fb())),
        Formula::FpIsNaN(bx(fa())),
        Formula::FpIsInfinite(bx(fa())),
        Formula::FpIsZero(bx(fa())),
        Formula::FpIsNormal(bx(fa())),
        Formula::FpIsSubnormal(bx(fa())),
        Formula::FpIsNegative(bx(fa())),
        Formula::FpIsPositive(bx(fa())),
        Formula::FpFromBits {
            bits: bx(w32()),
            eb: 8,
            sb: 24,
        },
        Formula::FpToSbv {
            rm: bx(rne()),
            value: bx(fa()),
            width: 32,
            eb: 8,
            sb: 24,
        },
        Formula::FpToUbv {
            rm: bx(rne()),
            value: bx(fa()),
            width: 8,
            eb: 8,
            sb: 24,
        },
        Formula::FpFromSbv {
            rm: bx(rne()),
            value: bx(w32()),
            eb: 8,
            sb: 24,
        },
        Formula::FpFromUbv {
            rm: bx(rne()),
            value: bx(a()),
            eb: 8,
            sb: 24,
        },
        Formula::FpConvert {
            rm: bx(rne()),
            value: bx(fa()),
            eb: 11,
            sb: 53,
        },
        Formula::FpToIeeeBv(bx(fa())),
        // Conditional, quantifiers, arrays
        Formula::Ite(bx(p()), bx(x()), bx(y())),
        Formula::Forall(
            vec![(k, Sort::Int)],
            bx(Formula::Or(vec![
                Formula::Lt(bx(kv()), bx(x())),
                Formula::Ge(bx(kv()), bx(x())),
            ])),
        ),
        Formula::Exists(
            vec![(k, Sort::Int)],
            bx(Formula::Eq(
                bx(kv()),
                bx(Formula::Add(bx(x()), bx(Formula::Int(1)))),
            )),
        ),
        Formula::Select(bx(arr()), bx(x())),
        Formula::Store(bx(arr()), bx(x()), bx(y())),
        Formula::const_array(Sort::Int, Sort::Int, Formula::Int(0)),
        Formula::const_array(Sort::BitVec(64), Sort::BitVec(8), a()),
        // Applications and datatype terms
        Formula::Pred(Symbol::intern("ready"), vec![x()]),
        Formula::Pred(Symbol::intern("flag"), vec![]),
        Formula::FnApp {
            func: "f".into(),
            args: vec![x()],
            sort: Sort::Int,
        },
        Formula::FnApp {
            func: "c".into(),
            args: vec![],
            sort: Sort::Int,
        },
        Formula::Ctor {
            ctor: "succ".into(),
            args: vec![lv()],
            sort: level_sort(),
        },
        Formula::Ctor {
            ctor: "zero".into(),
            args: vec![],
            sort: level_sort(),
        },
        Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_sort(),
            arg: bx(lv()),
        },
        Formula::IsCtor {
            datatype: "Level".into(),
            ctor: "succ".into(),
            arg: bx(lv()),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    /// The witnesses cover every variant the serde derive lists, and
    /// `variant_name` agrees with serde's own spelling of each.
    #[test]
    fn witnesses_cover_every_variant() {
        let names = formula_variant_names();
        assert!(
            !names.is_empty(),
            "the probe read the derive's variant list"
        );
        let witnessed: BTreeSet<&str> = witnesses().iter().map(variant_name).collect();
        let missing: Vec<&str> = names
            .iter()
            .copied()
            .filter(|n| !witnessed.contains(n))
            .collect();
        assert!(missing.is_empty(), "no witness for {missing:?}");
        for w in witnesses() {
            let json = serde_json::to_value(&w).expect("a witness serializes");
            let key = json
                .as_object()
                .and_then(|o| o.keys().next().cloned())
                .expect("externally tagged");
            assert_eq!(variant_name(&w), key, "serde's tag of {w:?}");
        }
    }
}
