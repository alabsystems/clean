// Serde helpers for 128-bit integer fields that must survive serde_json.
//
// serde_json (without `arbitrary_precision`) cannot represent an i128/u128
// outside the i64/u64 range: `serialize_i128`/`serialize_u128` fail with
// "number out of range". Any TrustIr type carrying a 128-bit literal — a
// `Constant::Int`/`Constant::U128`, a `ValueRange`/`KnownBits` proof annotation,
// a request-facts integer range — therefore could not be turned into JSON, which
// is exactly what the native verification bundle's transport path
// (`serde_json::to_value` on `NativeVerificationBundle`) requires. This mirrors
// the `Formula` fix in `trust-ir-contract`.
//
// The helpers keep every currently-working value byte-for-byte identical and
// only fix the previously-erroring tail:
//   * human-readable formats (serde_json): in-range values serialize as a bare
//     number exactly as the derive did; only values outside [i64::MIN, u64::MAX]
//     fall back to a decimal string; `deserialize_any` accepts either (valid
//     because JSON is self-describing).
//   * binary self-describing formats (bincode / MessagePack): always the native
//     128-bit path, so their bytes are unchanged for ALL values and
//     `deserialize_any` is never required.

pub(crate) mod wide_i128 {
    use core::fmt;
    use serde::de::{self, Visitor};
    use serde::{Deserializer, Serializer};

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

pub(crate) mod wide_u128 {
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
