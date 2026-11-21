// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

const DEFS: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/fixtures/olean/v4.36.0/module-ir/StableFixture/Defs.olean"
));

#[test]
fn equal_name_hashes_preserve_record_identity_and_first_refusal() {
    let string = Name::anon().str("x");
    // The numeric component is Lean String.hash "x". Name.hash combines its
    // parent's hash with the same word for these two different constructors.
    let numeric = Name::anon().num(16_562_859_848_569_467_201);
    assert_eq!(string.lean4_hash(), numeric.lean4_hash());
    assert!(numeric < string);

    let part = || {
        let mut part = parse_load_module(DEFS.to_vec()).unwrap();
        part.constants.retain(|c| c.kind == ConstantKind::Axiom);
        part.constants.truncate(2);
        assert_eq!(part.constants.len(), 2);
        part.constants[0].kernel_name = string.clone();
        part.constants[1].kernel_name = numeric.clone();
        part
    };
    let base = part();
    let mut later = part();
    let compare = |later: &LoadModule| {
        check_one_record_per_name(
            "Test",
            &[Some(&base), Some(later), None],
            StubRule::Restated,
        )
    };
    compare(&later).expect("distinct colliding declarations in each part");
    for c in &mut later.constants {
        c.kernel_level_params.push(Name::anon().str("changed"));
    }
    assert!(
        matches!(compare(&later), Err(ImportError::PartsDisagree { name, .. }) if name == numeric.to_string())
    );
    later.constants[0].kernel_name = numeric.clone();
    assert!(
        matches!(compare(&later), Err(ImportError::DuplicateDeclaration { name, .. }) if name == numeric.to_string())
    );

    let mut authoritative = part();
    authoritative.constants.remove(1);
    let placement = |private: &LoadModule| {
        refuse_misplaced_declarations(
            "Test",
            &base,
            Some(&later),
            Some(private),
            ArtifactDepth::Records,
        )
    };
    assert!(
        matches!(placement(&authoritative), Err(ImportError::MisplacedDeclaration { part: ".olean", name, .. }) if name == numeric.to_string())
    );
    authoritative.constants.clear();
    assert!(
        matches!(placement(&authoritative), Err(ImportError::MisplacedDeclaration { part: ".olean", name, .. }) if name == numeric.to_string())
    );
}
