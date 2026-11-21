// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
#[test]
fn old_version_and_trailing_payload_data_are_refused() {
    let encoded = encode_clean_payload(&CleanPayload::default()).expect("new payload");
    let version_at = encoded.len() - 12;
    let mut old = encoded.clone();
    old[version_at..version_at + 4].copy_from_slice(&7u32.to_le_bytes());
    assert!(matches!(
        decode_clean_payload(&old),
        Err(OleanError::UnsupportedPayloadVersion { actual: 7, .. })
    ));
    let trailer = CLEAN_PAYLOAD_MAGIC.len() + 12;
    let data_end = encoded.len() - trailer;
    let mut extended = encoded[..data_end].to_vec();
    extended.push(0);
    extended.extend_from_slice(CLEAN_PAYLOAD_MAGIC);
    extended.extend_from_slice(&CLEAN_PAYLOAD_VERSION.to_le_bytes());
    extended.extend_from_slice(&((data_end + 1) as u64).to_le_bytes());
    assert!(matches!(
        decode_clean_payload(&extended),
        Err(OleanError::InvalidPayload(_))
    ));
}
