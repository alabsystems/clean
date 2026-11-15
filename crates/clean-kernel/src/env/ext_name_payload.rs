// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Versioned structural Name/priority transport for Clean persistent extensions.
//! This is not Lean's CompactedRegion encoding. A version marker never falls
//! back to the old display-string payload, including on malformed input.
use crate::name::{Name, NameInner};

const MAGIC: &[u8; 8] = b"\xffCleanNM";

pub(super) fn is_versioned(bytes: &[u8]) -> bool {
    bytes.starts_with(MAGIC)
        || (!bytes.is_empty() && bytes.len() < MAGIC.len() && MAGIC.starts_with(bytes))
}

pub(super) fn encode(name: &Name, priority: u32) -> Vec<u8> {
    enum Part<'a> {
        Str(&'a str),
        Num(u64),
    }
    let mut parts = Vec::new();
    let mut cursor = name;
    loop {
        match cursor.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, value) => {
                parts.push(Part::Str(value.as_ref()));
                cursor = parent;
            }
            NameInner::Num(parent, value) => {
                parts.push(Part::Num(*value));
                cursor = parent;
            }
        }
    }
    let mut bytes = MAGIC.to_vec();
    bytes.push(1);
    bytes.extend_from_slice(&priority.to_le_bytes());
    for part in parts.into_iter().rev() {
        match part {
            Part::Str(value) => {
                bytes.push(1);
                bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
                bytes.extend_from_slice(value.as_bytes());
            }
            Part::Num(value) => {
                bytes.push(2);
                bytes.extend_from_slice(&value.to_le_bytes());
            }
        }
    }
    bytes.push(0);
    bytes
}

pub(super) fn decode(bytes: &[u8]) -> Option<(Name, u32)> {
    let rest = bytes.strip_prefix(MAGIC)?;
    let (&version, rest) = rest.split_first()?;
    if version != 1 {
        return None;
    }
    let priority = u32::from_le_bytes(rest.get(..4)?.try_into().ok()?);
    let mut rest = rest.get(4..)?;
    let mut name = Name::anon();
    // Every successful iteration consumes bytes; allocation is bounded by the
    // supplied payload. No recursive parser or display-name reconstruction.
    loop {
        let (&tag, next) = rest.split_first()?;
        rest = next;
        match tag {
            0 => return rest.is_empty().then_some((name, priority)),
            1 | 2 => {
                let value = u64::from_le_bytes(rest.get(..8)?.try_into().ok()?);
                rest = rest.get(8..)?;
                if tag == 1 {
                    let length = usize::try_from(value).ok()?;
                    let component = std::str::from_utf8(rest.get(..length)?).ok()?;
                    name = name.str(component);
                    rest = rest.get(length..)?;
                } else {
                    name = name.num(value);
                }
            }
            _ => return None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_payload_preserves_all_name_constructors() {
        for name in [
            Name::anon(),
            Name::anon().str(""),
            Name::anon().str("x.y"),
            Name::anon().str("x").str("y"),
            Name::anon().str("07"),
            Name::anon().str("7"),
            Name::anon().num(7),
            Name::anon().num(u64::MAX),
        ] {
            for priority in [0, 255, 1000, u32::MAX] {
                assert_eq!(
                    decode(&encode(&name, priority)),
                    Some((name.clone(), priority))
                );
            }
        }
    }

    #[test]
    fn malformed_structural_payload_never_parses_a_prefix() {
        let bytes = encode(&Name::anon().str("a.b").num(7), 1000);
        for length in 0..bytes.len() {
            assert!(decode(&bytes[..length]).is_none());
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(decode(&trailing).is_none());
        for version in [0, 2, 255] {
            let mut changed = bytes.clone();
            changed[8] = version;
            assert!(decode(&changed).is_none());
        }
        let mut utf8 = encode(&Name::anon().str("a"), 0);
        utf8[22] = 255;
        assert!(decode(&utf8).is_none());
        let mut tag = bytes;
        tag[13] = 255;
        assert!(decode(&tag).is_none());
    }
}
