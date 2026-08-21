// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shape-totality checks for the A1 lane matrix.

use std::collections::BTreeSet;

use super::*;

/// **The lane list this matrix is stated in must be TOTAL over `Cfg`.**
///
/// `lanes()` is a hand-written enumeration, and a hand-written enumeration of a
/// struct's fields is a drift risk of the same shape as everything else here. So
/// it is checked against the struct: `Cfg`'s `Debug` output names every field
/// exactly once, and every name in it must appear in the list.
#[test]
fn every_cfg_field_is_a_named_lane() {
    let c = parse_emitted(&fixture("has_cubical_layer.trust-ir.txt"));
    let named: BTreeSet<&str> = lanes(&c).into_iter().map(|(ln, _)| ln).collect();
    let debug = format!("{c:?}");
    let mut fields: BTreeSet<String> = BTreeSet::new();
    for tok in debug.split(&[' ', ',', '{', '}'][..]) {
        if let Some(f) = tok.strip_suffix(':') {
            if !f.is_empty() && f.chars().all(|ch| ch.is_ascii_lowercase() || ch == '_') {
                fields.insert(f.to_string());
            }
        }
    }
    assert!(
        fields.len() >= 26,
        "the field scan must have found the whole struct: {fields:?}"
    );
    for f in &fields {
        assert!(
            named.contains(f.as_str()),
            "`Cfg::{f}` is a lane with no entry in `lanes()`, so the matrix above is stated over \
             fewer lanes than the shape has and every chain's row silently omits it."
        );
    }
    assert_eq!(
        fields.len(),
        named.len(),
        "the lane list and the struct must have the SAME number of entries: struct {fields:?} vs \
         list {named:?}"
    );
}

/// **The function signature, for all eleven chains in one place.**
///
/// `assert_entry_params` is called from each chain's own gate; this repeats it
/// across the whole set so a chain added later without the call is still
/// covered here.
#[test]
fn every_chain_pins_its_function_signature() {
    for ch in CHAINS {
        assert_entry_params(
            &fixture(ch.fixture),
            &clean_block_sources(ch.spec, ch.func_prefix),
            ch.who,
        );
    }
}
