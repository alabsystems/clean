//! Identity spelling shared by native body-WP producers and publication readers.
//! This formats an already computed canonical input digest; it is not admission,
//! source-generation authority, or proof validation.

use std::fmt::Write as _;

pub const NATIVE_BODY_WP_SCHEMA: &str = "trust-wp.trust-ir-body-wp.v2";

/// Bind the selected request to the IR owner's SHA-256 native-bundle digest.
/// Callers must compute the digest from the same original scoped input used by
/// verification and replay, without appending the output being checked.
pub fn native_body_wp_bundle_id(
    module_name: &str,
    request_id: u32,
    input_sha256: &[u8; 32],
) -> String {
    let mut id = format!(
        "{NATIVE_BODY_WP_SCHEMA}:trust-ir-native:{module_name}:trust-wp:{request_id}:input:sha256:"
    );
    for byte in input_sha256 {
        write!(&mut id, "{byte:02x}").expect("writing to String cannot fail");
    }
    id
}

/// Check only the versioned identifier shape and selected request number.
/// Publication still needs the exact canonical input digest and native claim;
/// this recognizer supplies no proof or source authority.
pub fn native_body_wp_id_selects_request(id: &str, request_id: u32) -> bool {
    let Some((head, digest)) = id.rsplit_once(":input:sha256:") else {
        return false;
    };
    head.starts_with(&format!("{NATIVE_BODY_WP_SCHEMA}:trust-ir-native:"))
        && head.ends_with(&format!(":trust-wp:{request_id}"))
        && digest.len() == 64
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_spelling_has_fixed_width_lowercase_digest() {
        let mut digest = [0; 32];
        digest[0] = 0xAB;
        digest[31] = 0xEF;
        assert_eq!(
            native_body_wp_bundle_id("m", 7, &digest),
            format!(
                "{NATIVE_BODY_WP_SCHEMA}:trust-ir-native:m:trust-wp:7:input:sha256:ab{}ef",
                "00".repeat(30)
            )
        );
    }

    #[test]
    fn module_request_and_every_digest_byte_participate() {
        let digest = [0; 32];
        let id = native_body_wp_bundle_id("m", 7, &digest);
        assert_ne!(id, native_body_wp_bundle_id("other", 7, &digest));
        assert_ne!(id, native_body_wp_bundle_id("m", 8, &digest));
        for index in 0..32 {
            let mut changed = digest;
            changed[index] = 1;
            assert_ne!(id, native_body_wp_bundle_id("m", 7, &changed));
        }
    }

    #[test]
    fn shape_recognizer_refuses_other_requests_versions_and_noncanonical_hashes() {
        let id = native_body_wp_bundle_id("namespace:module", 7, &[0xAB; 32]);
        assert!(native_body_wp_id_selects_request(&id, 7));
        assert!(!native_body_wp_id_selects_request(&id, 8));
        for changed in [
            id.replace(".v2:", ".v1:"),
            id.replace(":trust-wp:7:", ":trust-wp:07:"),
            id.replace("abab", "ABAB"),
            format!("{id}0"),
            id[..id.len() - 1].to_owned(),
        ] {
            assert!(!native_body_wp_id_selects_request(&changed, 7), "{changed}");
        }
    }
}
