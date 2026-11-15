// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native UInt64 string encoding and checked literal decoding.
//! Match Lean's UInt64 JSON instances and Syntax.decodeNatLitVal?.
use serde::de::Error;
use serde::{Deserialize, Deserializer, Serializer};

pub(super) fn serialize<S: Serializer>(value: &u64, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.collect_str(value)
}

pub(super) fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u64, D::Error> {
    let text = String::deserialize(deserializer)?;
    decode(&text).ok_or_else(|| D::Error::custom("expected a string-encoded UInt64 literal"))
}

fn decode(text: &str) -> Option<u64> {
    let bytes = text.as_bytes();
    let first = *bytes.first()?;
    let (radix, digits) = if first == b'0' {
        match bytes.get(1) {
            None => return Some(0),
            Some(b'x' | b'X') => (16_u64, &bytes[2..]),
            Some(b'b' | b'B') => (2_u64, &bytes[2..]),
            Some(b'o' | b'O') => (8_u64, &bytes[2..]),
            Some(b'0'..=b'9') => (10_u64, bytes),
            _ => return None,
        }
    } else if first.is_ascii_digit() {
        (10_u64, bytes)
    } else {
        return None;
    };
    digits.iter().try_fold(0_u64, |value, byte| {
        if *byte == b'_' {
            return Some(value);
        }
        let digit = match byte {
            b'0'..=b'9' => u64::from(byte - b'0'),
            b'a'..=b'f' => u64::from(byte - b'a') + 10,
            b'A'..=b'F' => u64::from(byte - b'A') + 10,
            _ => return None,
        };
        if digit >= radix {
            return None;
        }
        value.checked_mul(radix)?.checked_add(digit)
    })
}

// RpcRef.p is native USize, so its range follows the target pointer width.
pub(super) mod usize_ref {
    use serde::de::Error as _;
    use serde::ser::Error as _;
    use serde::{Deserializer, Serializer};

    pub(crate) fn serialize<S: Serializer>(value: &u64, serializer: S) -> Result<S::Ok, S::Error> {
        usize::try_from(*value)
            .map_err(|_| S::Error::custom("RPC reference exceeds native USize"))?;
        super::serialize(value, serializer)
    }

    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u64, D::Error> {
        let value = super::deserialize(deserializer)?;
        usize::try_from(value)
            .map_err(|_| D::Error::custom("RPC reference exceeds native USize"))?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Serialize;
    use serde_json::{json, Value};

    #[derive(Debug, Deserialize, Serialize)]
    struct Session {
        #[serde(with = "super")]
        id: u64,
    }

    #[test]
    fn exact_integer_boundaries_remain_strings_on_the_wire() {
        for id in [0, 1, (1_u64 << 53) - 1, 1_u64 << 53, u64::MAX] {
            let wire = serde_json::to_value(Session { id }).expect("encode exact ID");
            assert_eq!(wire, json!({"id": id.to_string()}));
            let decoded: Session = serde_json::from_value(wire).expect("decode exact ID");
            assert_eq!(decoded.id, id);
        }
    }

    #[test]
    fn native_literal_forms_preserve_integer_values() {
        for (text, expected) in [
            ("01", 1),
            ("1_0", 10),
            ("1__", 1),
            ("00_", 0),
            ("0x", 0),
            ("0x_", 0),
            ("0Xff", 255),
            ("0xffffffffffffffff", u64::MAX),
            ("0b101", 5),
            ("0o177", 127),
        ] {
            let decoded: Session =
                serde_json::from_value(json!({"id": text})).expect("native literal");
            assert_eq!(decoded.id, expected, "{text}");
        }
    }

    #[test]
    fn invalid_shapes_literals_and_overflow_refuse() {
        for value in [
            json!(1),
            json!(1.0),
            Value::Null,
            json!(true),
            json!([]),
            json!({}),
            json!(""),
            json!("-1"),
            json!("+1"),
            json!(" 1"),
            json!("1 "),
            json!("1.0"),
            json!("0_"),
            json!("0b2"),
            json!("0o8"),
            json!("18446744073709551616"),
            json!("0x10000000000000000"),
        ] {
            assert!(serde_json::from_value::<Session>(json!({"id": value})).is_err());
        }
    }

    #[test]
    fn opaque_reference_bounds_follow_the_native_pointer_width() {
        #[derive(Debug, Deserialize, Serialize)]
        struct Reference {
            #[serde(with = "super::usize_ref")]
            p: u64,
        }
        let largest = u64::try_from(usize::MAX).expect("supported native pointer width");
        let value = serde_json::to_value(Reference { p: largest }).expect("native reference bound");
        assert_eq!(value, json!({"p": largest.to_string()}));
        assert_eq!(
            serde_json::from_value::<Reference>(value)
                .expect("native reference")
                .p,
            largest
        );
        let overflow = (u128::from(largest) + 1).to_string();
        assert!(serde_json::from_value::<Reference>(json!({"p": overflow})).is_err());
        let next = largest.saturating_add(1);
        assert_eq!(
            serde_json::to_value(Reference { p: next }).is_err(),
            next > largest,
            "serialization must respect the native pointer bound"
        );
    }
}
