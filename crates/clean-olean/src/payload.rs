// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean-specific payload attached to .olean files.
//!
//! We append a small trailer to .olean files we generate to carry the actual
//! kernel objects serialized with `bincode`. This avoids having to fully
//! replicate Lean 4's ConstantInfo layout while still enabling dependent
//! modules to load and reuse definitions.

use crate::error::{OleanError, OleanResult};
use clean_kernel::env::ConstantInfo;
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use clean_kernel::name::Name;
use serde::{Deserialize, Serialize};
use std::mem::size_of;

/// Magic footer identifying clean payloads.
pub const CLEAN_PAYLOAD_MAGIC: &[u8; 8] = b"CLEANENV";
/// Version of the clean payload format.
pub const CLEAN_PAYLOAD_VERSION: u32 = 1;

/// Serialized kernel data embedded in a clean-generated `.olean`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CleanPayload {
    pub constants: Vec<ConstantInfo>,
    pub inductives: Vec<InductiveVal>,
    pub constructors: Vec<ConstructorVal>,
    pub recursors: Vec<RecursorVal>,
    pub structure_fields: Vec<(Name, Vec<Name>)>,
}

impl CleanPayload {
    /// Total number of constants represented (counts inductives/ctors/recs too).
    ///
    /// # REQUIRES
    /// - None.
    ///
    /// # ENSURES
    /// - Returns `constants.len() + inductives.len() + constructors.len() + recursors.len()`.
    /// - Deterministic for a given payload.
    pub fn total_constants(&self) -> usize {
        self.constants.len()
            + self.inductives.len()
            + self.constructors.len()
            + self.recursors.len()
    }
}

/// Encode a payload and append a footer for easy detection.
///
/// # REQUIRES
/// - `payload` must be a valid `CleanPayload` (no internal invariants violated).
///
/// # ENSURES
/// - Output bytes end with `CLEAN_PAYLOAD_MAGIC`, `CLEAN_PAYLOAD_VERSION`,
///   and the serialized payload length (u64, little-endian).
/// - Returns `OleanError::Serialization` if `bincode` serialization fails.
/// - Deterministic: same payload yields identical output bytes.
pub fn encode_clean_payload(payload: &CleanPayload) -> OleanResult<Vec<u8>> {
    let data =
        bincode::serde::encode_to_vec(payload, bincode::config::standard()).map_err(|e| {
            OleanError::Serialization(format!("failed to serialize clean payload: {e}"))
        })?;

    let mut out = Vec::with_capacity(data.len() + CLEAN_PAYLOAD_MAGIC.len() + size_of::<u32>() + 8);
    out.extend_from_slice(&data);
    out.extend_from_slice(CLEAN_PAYLOAD_MAGIC);
    out.extend_from_slice(&CLEAN_PAYLOAD_VERSION.to_le_bytes());
    out.extend_from_slice(&(data.len() as u64).to_le_bytes());
    Ok(out)
}

/// Attempt to decode a clean payload from the end of the provided bytes.
///
/// Returns `Ok(None)` if no payload footer is present.
///
/// # REQUIRES
/// - `bytes` must be the full .olean bytes (payload detection relies on the tail).
///
/// # ENSURES
/// - Returns `Ok(None)` when the footer magic is absent.
/// - Returns `Err(OleanError::UnsupportedPayloadVersion { .. })` on version mismatch.
/// - Returns `Err(OleanError::InvalidPayload(_))` on malformed footer or length.
/// - Returns `Ok(Some(payload))` when a valid payload is present and deserializes.
pub fn decode_clean_payload(bytes: &[u8]) -> OleanResult<Option<CleanPayload>> {
    let trailer_len = CLEAN_PAYLOAD_MAGIC.len() + size_of::<u32>() + 8;
    if bytes.len() < trailer_len {
        return Ok(None);
    }

    let len_offset = bytes.len() - 8;
    let version_offset = len_offset - size_of::<u32>();
    let magic_offset = version_offset - CLEAN_PAYLOAD_MAGIC.len();

    if &bytes[magic_offset..version_offset] != CLEAN_PAYLOAD_MAGIC {
        return Ok(None);
    }

    let version = u32::from_le_bytes(
        bytes[version_offset..len_offset]
            .try_into()
            .map_err(|_| OleanError::InvalidPayload("truncated payload footer".into()))?,
    );
    if version != CLEAN_PAYLOAD_VERSION {
        return Err(OleanError::UnsupportedPayloadVersion {
            expected: CLEAN_PAYLOAD_VERSION,
            actual: version,
        });
    }

    let payload_len = u64::from_le_bytes(
        bytes[len_offset..]
            .try_into()
            .map_err(|_| OleanError::InvalidPayload("truncated payload length".into()))?,
    ) as usize;
    if payload_len > magic_offset {
        return Err(OleanError::InvalidPayload(format!(
            "payload length {} exceeds available bytes {}",
            payload_len,
            bytes.len()
        )));
    }
    let start = magic_offset - payload_len;
    let data = &bytes[start..magic_offset];

    // bincode 2 `standard()` config (varint, little-endian) — must match the
    // `encode_to_vec(.., standard())` used in `encode_clean_payload`. `decode_from_slice`
    // is bounded by the input slice (here precisely `payload_len` bytes) and caps
    // container pre-allocation to the remaining input, so a tiny malformed input cannot
    // trigger the multi-GB allocation that motivated the old `with_limit` guard (#2421).
    let (payload, _consumed): (CleanPayload, usize) =
        bincode::serde::decode_from_slice(data, bincode::config::standard()).map_err(|e| {
            OleanError::Serialization(format!("failed to deserialize clean payload: {e}"))
        })?;

    Ok(Some(payload))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_decode_roundtrip() {
        let payload = CleanPayload {
            constants: vec![],
            inductives: vec![],
            constructors: vec![],
            recursors: vec![],
            structure_fields: vec![],
        };

        let encoded = encode_clean_payload(&payload).expect("encode");
        let decoded = decode_clean_payload(&encoded)
            .expect("decode result")
            .expect("payload missing");

        assert_eq!(decoded.total_constants(), 0);
    }

    #[test]
    fn decode_absent_payload_returns_none() {
        let bytes = vec![0u8; 16];
        let decoded = decode_clean_payload(&bytes).unwrap();
        assert!(
            decoded.is_none(),
            "zero-filled bytes should decode to None (absent payload)"
        );
    }

    /// Roundtrip with non-empty data to verify that `bincode::serde::encode_to_vec(, bincode::config::standard())`
    /// (encode) and `DefaultOptions::new().deserialize()` (decode) use
    /// compatible encoding formats.
    #[test]
    fn encode_decode_roundtrip_nonempty() {
        let payload = CleanPayload {
            constants: vec![],
            inductives: vec![],
            constructors: vec![],
            recursors: vec![],
            structure_fields: vec![
                (
                    Name::from_string("Foo"),
                    vec![Name::from_string("x"), Name::from_string("y")],
                ),
                (Name::from_string("Bar"), vec![Name::from_string("z")]),
            ],
        };

        let encoded = encode_clean_payload(&payload).expect("encode");
        let decoded = decode_clean_payload(&encoded)
            .expect("decode result")
            .expect("payload missing");

        assert_eq!(decoded.structure_fields.len(), 2);
        assert_eq!(decoded.structure_fields[0].0, Name::from_string("Foo"));
        assert_eq!(decoded.structure_fields[0].1.len(), 2);
        assert_eq!(decoded.structure_fields[1].0, Name::from_string("Bar"));
        assert_eq!(decoded.structure_fields[1].1.len(), 1);
    }

    /// Regression test for #2421: a malformed payload with an enormous length
    /// prefix inside the bincode data must return an error, not OOM.
    #[test]
    fn decode_malformed_huge_length_prefix_returns_error() {
        // Build a minimal valid footer that points to a small payload region
        // whose bincode content encodes a Vec length of u64::MAX.
        //
        // Vec<T> in bincode (fixint) is: u64 length, then T elements.
        // We craft a buffer where the length prefix is huge but the buffer is tiny.
        let huge_len: u64 = u64::MAX;
        let fake_payload = huge_len.to_le_bytes(); // 8 bytes claiming huge vec

        let mut bytes = Vec::new();
        bytes.extend_from_slice(&fake_payload);
        bytes.extend_from_slice(CLEAN_PAYLOAD_MAGIC);
        bytes.extend_from_slice(&CLEAN_PAYLOAD_VERSION.to_le_bytes());
        bytes.extend_from_slice(&(fake_payload.len() as u64).to_le_bytes());

        let result = decode_clean_payload(&bytes);
        assert!(
            result.is_err(),
            "huge length prefix must error, not OOM: {result:?}"
        );
    }
}
