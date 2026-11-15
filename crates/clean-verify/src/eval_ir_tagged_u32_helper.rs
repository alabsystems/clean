// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Explicit complete tagged-UInt32 helper semantics, separate from PrefixV1.
//!
//! The original prefix remains absorbing at pc4. This owner continues through
//! the actual scalar call, both returns and a constructive tagged box import.
//! Neither model is a Rust/native heap, ARC, ABI or body-permission theorem.

use crate::spec::{SpecError, Specification};
mod laws;
mod semantics;

/// Install the fixed complete-helper target through ordinary kernel checking.
/// It reuses the original prefix data and definitions without modifying them.
pub fn build_tagged_u32_helper_spec_v1_with_stack() -> Result<Specification, SpecError> {
    let mut spec = crate::eval_ir_tagged_u32_prefix::build_tagged_u32_prefix_spec_v1_with_stack()?;
    semantics::install(&mut spec)?;
    laws::install(&mut spec)?;
    Ok(spec)
}

#[cfg(test)]
mod tests {
    #[test]
    fn complete_helper_installs_checked_box_and_run_without_axioms() {
        let spec = super::build_tagged_u32_helper_spec_v1_with_stack().unwrap();
        for name in [
            "ir_clean_tag32_helper_provider_v1",
            "ir_clean_tag32_helper_step_v1",
            "ir_clean_tag32_helper_run_v1",
            "ir_clean_tag32_helper_box_v1",
            "ir_clean_tag32_run_v1",
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
    }
}
