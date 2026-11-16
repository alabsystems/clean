// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.7(b): the `clean_backend_tv` anchor environment has ONE Clean-side
//! spelling ([`crate::tv_anchor_environment`]), and it carries exactly the
//! vocabulary trust-ir-build's re-checker installs: the three Fragment-4 heap
//! combinators and the four WS1.15 S3 signed carrier aliases. Whether its
//! DIGEST equals the re-checker's is pinned where both are in scope — the
//! bound-certificate tests in clean-compiler's `emit_trust_ir_tv` suite, which
//! run the pinned trust-ir validator over a bound mint.

use clean_kernel::{ConstantKind, Expr, Name};

use crate::{
    signed_carrier_declarations, tv_anchor_environment, HEAP_HEMPTY, HEAP_HREAD, HEAP_HWRITE,
    SIGNED_CARRIER_ALIASES,
};

#[test]
fn anchor_environment_carries_the_heap_and_signed_carrier_vocabulary() {
    let env = tv_anchor_environment().expect("the anchor environment builds");
    for name in [HEAP_HEMPTY, HEAP_HWRITE, HEAP_HREAD] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("heap combinator `{name}` is installed"));
        assert!(info.value.is_some() && info.is_reducible, "`{name}`");
    }
    for (width, name) in SIGNED_CARRIER_ALIASES {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("signed carrier `{name}` (width {width}) is installed"));
        // A reducible DEFINITION of `Nat` at `Type` — never an axiom, so the
        // rooted audit of a certificate that mentions it sees no assumption.
        assert_eq!(info.kind, ConstantKind::Definition, "`{name}`");
        assert!(info.is_reducible, "`{name}` unfolds");
        assert_eq!(info.type_, Expr::type_(), "`{name}` : Type");
        assert_eq!(info.value, Some(Expr::const_str("Nat")), "`{name}` := Nat");
    }
}

/// The aliases are exactly the four widths, in width order, and each is
/// declared once.
#[test]
fn signed_carrier_aliases_are_the_four_fragment_widths() {
    let widths: Vec<u32> = SIGNED_CARRIER_ALIASES.iter().map(|(w, _)| *w).collect();
    assert_eq!(widths, [8, 16, 32, 64]);
    assert_eq!(signed_carrier_declarations().len(), 4);
}
