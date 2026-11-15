// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Explicit LE64 tagged-UInt32 prefix semantics, distinct from ByteV1.
//!
//! The complete ByteConfig/world is retained. Two occurrence flags track the
//! wrapper's input slots, not allocation ownership or Rust ghost-frame IDs.
//! The fixed provider is a constructive tagged model, not a theorem about a
//! native import. Release is successful ONLY in this new profile; ByteV1's
//! unmodelled Release, its vocabulary identity and all default APIs stay intact.
//! Stopping at the next scalar call is not machine halt, return or a body license.

use crate::spec::{SpecError, Specification};

mod laws;
mod semantics;

/// Construct the checked, explicitly selected prefix vocabulary.
///
/// Every added declaration passes the ordinary kernel registration path; no
/// axiom, unsafe admission, arbitrary provider or caller environment is used.
/// This owner adds no authority to associate a context with a producer module.
pub fn build_tagged_u32_prefix_spec_v1_with_stack() -> Result<Specification, SpecError> {
    let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()?;
    semantics::install(&mut spec)?;
    laws::install(&mut spec)?;
    Ok(spec)
}

#[cfg(test)]
mod tests {
    #[test]
    fn tagged_prefix_is_checked_separate_vocabulary_with_no_axioms() {
        let spec = super::build_tagged_u32_prefix_spec_v1_with_stack().unwrap();
        for name in [
            "ir_clean_tag32_provider_v1",
            "ir_clean_tag32_step_v1",
            "ir_clean_tag32_run_v1",
            "ir_clean_tag32_run_zero_v1",
            "ir_clean_tag32_encoded_domain_v1",
            "ir_clean_tag32_encoded_pointer_v1",
            "ir_clean_tag32_provider_encoded_v1",
        ] {
            let name = clean_kernel::Name::from_string(name);
            assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
            assert!(spec
                .env()
                .foundational_axiom_deps(&name)
                .unwrap()
                .is_empty());
            assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
        }
        // Canonical Release is still the original unmodelled dispatcher.
        assert!(spec
            .env()
            .get_const(&clean_kernel::Name::from_string(
                "ir_byte_release_unmodelled_v1"
            ))
            .is_some());
    }
}
