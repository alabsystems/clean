// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C4: the per-function determinism digest. (environment, declaration, core
//! version, target) → Function: the same key gives the same Function digest
//! from a fresh environment; each key field moves the key; the Function
//! digest moves with the body and not with what the key excludes.

use super::*;
use crate::rust_abi::{compile_rust_abi, CoreFunctionDigest};

fn digest_of(
    env: &Environment,
    source_root: &str,
    module_name: &str,
    target: &TargetInfo,
) -> CoreFunctionDigest {
    let out = compile_rust_abi(
        env,
        &[Name::from_string(source_root)],
        &[],
        &PipelineConfig::default(),
        module_name,
        target,
    )
    .expect("compiles");
    out.rows.into_iter().next().expect("one row").digest
}

#[test]
fn c4_same_key_same_function_digest_from_a_fresh_environment() {
    let a = digest_of(&island_env(&[], WSUM), "cleanWsum", "m", &trust_target());
    let b = digest_of(&island_env(&[], WSUM), "cleanWsum", "m", &trust_target());
    assert_eq!(a, b, "two fresh elaborations of one island");
    for field in [&a.environment, &a.key, &a.function] {
        assert!(field.starts_with("sha256:"), "{field}");
    }
    assert!(
        !a.declaration.is_empty() && a.declaration.chars().all(|c| c.is_ascii_hexdigit()),
        "the declaration's environment-digest row: {}",
        a.declaration
    );
    assert!(a.core_version.contains("rust-abi/"), "{}", a.core_version);
    assert_eq!(a.target, "aarch64-apple-darwin");
}

#[test]
fn c4_each_key_field_moves_the_key() {
    let base = digest_of(&island_env(&[], WSUM), "cleanWsum", "m", &trust_target());

    // Declaration: same name, different body.
    let sub = digest_of(
        &island_env(&[], "def cleanWsum (a b : UInt64) : UInt64 := a - b\n"),
        "cleanWsum",
        "m",
        &trust_target(),
    );
    assert_ne!(sub.declaration, base.declaration);
    assert_ne!(sub.key, base.key);
    assert_ne!(
        sub.function, base.function,
        "a different body is a different Function"
    );

    // Environment: an unrelated declaration added; this one unchanged.
    let wider = digest_of(
        &island_env(&[], &format!("{WSUM}def other (a : UInt8) : UInt8 := a\n")),
        "cleanWsum",
        "m",
        &trust_target(),
    );
    assert_ne!(wider.environment, base.environment);
    assert_eq!(wider.declaration, base.declaration);
    assert_ne!(wider.key, base.key);
    assert_eq!(
        wider.function, base.function,
        "the Function itself did not change"
    );

    // Target.
    let mut x86 = trust_target();
    x86.triple = "x86_64-unknown-linux-gnu".to_string();
    let other_target = digest_of(&island_env(&[], WSUM), "cleanWsum", "m", &x86);
    assert_ne!(other_target.key, base.key);
    assert_eq!(other_target.declaration, base.declaration);
}

#[test]
fn c4_the_function_digest_ignores_the_module_name() {
    let env = island_env(&[], WSUM);
    let a = digest_of(
        &env,
        "cleanWsum",
        "clean-rust-abi::crate_a",
        &trust_target(),
    );
    let b = digest_of(
        &env,
        "cleanWsum",
        "clean-rust-abi::crate_b",
        &trust_target(),
    );
    assert_eq!(a, b);
}
