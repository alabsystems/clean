// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn ordinary_keys_remain_compatible_without_numeric_reconstruction() {
    for (name, key) in [
        (Name::anon().str("Init").str("Core"), "Init.Core"),
        (Name::anon().str("07"), "07"),
        (Name::anon().str("7"), "7"),
    ] {
        assert_eq!(module_visit_key(&name).unwrap(), key);
    }
    assert!(module_visit_key(&Name::anon()).is_err());
    assert!(module_visit_key(&Name::anon().num(7)).is_err());
    assert!(module_visit_key(&Name::anon().num(7).str("tail")).is_err());
}

#[test]
fn quoted_dots_do_not_alias_hierarchical_completed_keys() {
    let quoted = module_visit_key(&Name::anon().str("Module.part")).unwrap();
    let nested = module_visit_key(&Name::anon().str("Module").str("part")).unwrap();
    assert_ne!(quoted, nested);
    assert_eq!(nested, "Module.part");
    assert!(quoted.starts_with('\0'));
}

#[test]
fn framing_is_injective_for_empty_unicode_marker_and_delimiter_parts() {
    let components = [
        "",
        ".",
        "a",
        "a.b",
        "0:",
        "1:a",
        "α.β",
        "\0",
        "\0clean.module.str/v1:3:a.b",
    ];
    let mut seen = std::collections::BTreeMap::new();
    for first in components {
        for second in std::iter::once(None).chain(components.into_iter().map(Some)) {
            let name = match second {
                Some(second) => Name::anon().str(first).str(second),
                None => Name::anon().str(first),
            };
            let key = module_visit_key(&name).unwrap();
            assert!(
                seen.insert(key, name.clone()).is_none(),
                "structural key collision at {name:?}"
            );
        }
    }
}
