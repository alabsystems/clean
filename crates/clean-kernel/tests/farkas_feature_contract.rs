// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guards the production closure of the `farkas-constructive` feature.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

fn configured_modules(source: &str, feature: &str) -> BTreeSet<String> {
    let mut modules = BTreeSet::new();
    let mut cfg = String::new();
    let mut reading_cfg = false;

    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[cfg(") {
            cfg.clear();
            cfg.push_str(trimmed);
            reading_cfg = !trimmed.ends_with(")]");
            continue;
        }
        if reading_cfg {
            cfg.push(' ');
            cfg.push_str(trimmed);
            reading_cfg = !trimmed.ends_with(")]");
            continue;
        }
        if let Some(module) = trimmed
            .strip_prefix("mod ")
            .and_then(|line| line.strip_suffix(';'))
        {
            if cfg.contains(&format!("feature = \"{feature}\"")) {
                modules.insert(module.to_owned());
            }
            cfg.clear();
        } else if !trimmed.is_empty() && !trimmed.starts_with("//") {
            cfg.clear();
        }
    }

    modules
}

#[test]
fn farkas_constructive_feature_matches_declared_contract() {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let manifest_text =
        fs::read_to_string(manifest_dir.join("Cargo.toml")).expect("read clean-kernel manifest");
    let manifest: toml::Value =
        toml::from_str(&manifest_text).expect("parse clean-kernel manifest");

    let feature = manifest["features"]["farkas-constructive"]
        .as_array()
        .expect("farkas-constructive feature must be an array");
    assert!(
        feature.is_empty(),
        "farkas-constructive must not acquire transitive Cargo features"
    );

    let declared = manifest["package"]["metadata"]["clean"]["feature-contracts"]
        ["farkas-constructive"]["modules"]
        .as_array()
        .expect("farkas-constructive module contract must be declared")
        .iter()
        .map(|value| {
            value
                .as_str()
                .expect("contract module names must be strings")
                .to_owned()
        })
        .collect::<BTreeSet<_>>();

    let env_source = fs::read_to_string(manifest_dir.join("src/env/mod.rs"))
        .expect("read clean-kernel env module registry");
    let configured = configured_modules(&env_source, "farkas-constructive");

    assert_eq!(
        configured, declared,
        "the production Farkas closure changed; review the trust boundary and update the explicit \
         package metadata contract in the same change"
    );
}
