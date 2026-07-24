// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Round-trip + kernel-recheck tests for the `nnverify_ieee754` shard.

use super::*;
use clean_kernel::Name;

/// TEMP inventory probe (run once to confirm the published set matches what the
/// kernel registers): print every float-theory constant + its kind + axiom-dep
/// count. Ignored so it never runs in the normal suite.
#[test]
#[ignore = "inventory probe; run explicitly with --ignored"]
fn probe_ieee754_inventory() {
    let env = seed_ieee754_environment().expect("seed");
    let mut names: Vec<String> = env
        .constants()
        .map(|c| c.name.to_string())
        .filter(|n| {
            n.starts_with("NNVerify.FloatRational.")
                || n == "Float.toRatExact"
                || n == "Float.ulpExact"
                || n == "Rat.roundToNearestEven"
        })
        .collect();
    names.sort();
    for n in &names {
        let info = env.get_const(&Name::from_string(n)).unwrap();
        let deps = env
            .axiom_deps(&Name::from_string(n))
            .map(|d| d.len())
            .unwrap_or(usize::MAX);
        eprintln!("{:?}\t{}\tdeps={}", info.kind, n, deps);
    }
    eprintln!("TOTAL_FLOAT_CONSTANTS={}", names.len());
    eprintln!("PUBLISHED={}", NNVERIFY_IEEE754_DECLS.len());
}

/// Every published name in [`NNVERIFY_IEEE754_DECLS`] is actually registered by
/// the kernel after seeding — the published list cannot drift from the math.
#[test]
fn published_decls_all_registered() {
    let env = seed_ieee754_environment().expect("seed");
    for &name in NNVERIFY_IEEE754_DECLS {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} must be registered by init_nn_verify_float_rational"
        );
    }
    // The empty-closure theorem subset is also a subset of the published decls.
    for &thm in NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS {
        assert!(
            NNVERIFY_IEEE754_DECLS.contains(&thm),
            "{thm} must be published in the shard's decl list"
        );
    }
}

/// In the seeded environment, the empty-closure theorems already have an empty
/// non-foundational axiom closure (the property the shard preserves), and the
/// function-symbol axioms / domain axioms do NOT (they are the postulated
/// surface). This pins the partition the shard records.
#[test]
fn empty_closure_partition_is_honest() {
    let env = seed_ieee754_environment().expect("seed");
    for &thm in NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS {
        let deps = env
            .axiom_deps(&Name::from_string(thm))
            .unwrap_or_else(|| panic!("{thm}: axiom_deps None"));
        assert!(
            deps.is_empty(),
            "{thm} must have an empty non-foundational closure; got {deps:?}"
        );
    }
    // The six IEEE-754 domain axioms are genuinely axioms (NOT in the
    // empty-closure set) — the shard does not silently launder them.
    for axiom in [
        "NNVerify.FloatRational.float_to_rational_exact",
        "NNVerify.FloatRational.rounding_error_bound",
        "NNVerify.FloatRational.interval_contains_real",
        "NNVerify.FloatRational.matmul_error_bound",
        "NNVerify.FloatRational.ibp_float_sound",
        "NNVerify.FloatRational.error_propagation_linear",
    ] {
        assert!(
            !NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS.contains(&axiom),
            "{axiom} is a domain axiom and must NOT be claimed empty-closure"
        );
    }
}

/// The shard builds, every published declaration lands in it, and the in-memory
/// bytes round-trip through `ShardReader` with the expected constant count.
#[test]
fn shard_builds_and_round_trips() {
    let builder = build_nnverify_ieee754_shard().expect("build shard");
    assert_eq!(
        builder.entry_count(),
        NNVERIFY_IEEE754_DECLS.len(),
        "every published declaration must be added to the shard"
    );

    let bytes = builder.write_to_bytes().expect("serialize shard");
    let reader = crate::shard::ShardReader::from_bytes(&bytes).expect("read shard");
    assert_eq!(
        reader.constants.len(),
        NNVERIFY_IEEE754_DECLS.len(),
        "shard constant count must match published decls"
    );

    // Every published name resolves in the shard's string table / sorted index.
    for &name in NNVERIFY_IEEE754_DECLS {
        assert!(
            reader.lookup_name(name).is_some(),
            "{name} must be present in the written shard"
        );
    }
}

/// THE GATE: build → register → reload → kernel-re-check. Every constant
/// type-checks from the shard alone, the discharge + round/ulp theorems
/// re-verify with an EMPTY non-foundational axiom closure, and the manifest
/// entry carries a REAL blake3 hash + REAL header counts (no placeholders).
#[test]
fn shard_registers_and_kernel_rechecks_with_empty_closure() {
    let dir = tempfile::tempdir().expect("tempdir");
    let library_root = dir.path().join("mathverse-library");

    // --- register: write shard + manifest entry with real hash/counts ---
    let reg = register_nnverify_ieee754_shard(&library_root).expect("register shard");
    assert_eq!(reg.entry.source, NNVERIFY_IEEE754_SHARD_NAME);
    assert_eq!(
        reg.entry.path,
        format!("{NNVERIFY_IEEE754_SHARD_SUBDIR}/{NNVERIFY_IEEE754_SHARD_NAME}.mathverse")
    );
    assert_eq!(
        reg.entry.constant_count as usize,
        NNVERIFY_IEEE754_DECLS.len(),
        "manifest constant_count must be the real published count"
    );
    assert!(
        reg.entry.expr_count > 0,
        "manifest expr_count must be real, not 0"
    );
    // A real blake3 hex hash: 64 lowercase hex chars, not a placeholder.
    assert_eq!(
        reg.entry.content_hash.len(),
        64,
        "content_hash must be a real blake3 hex"
    );
    assert!(
        reg.entry
            .content_hash
            .chars()
            .all(|c| c.is_ascii_hexdigit()),
        "content_hash must be hex"
    );
    assert_ne!(reg.entry.content_hash, "deadbeef", "no placeholder hash");

    // --- the manifest on disk records the entry with matching counts ---
    let manifest_path = library_root.join("manifest.json");
    let manifest =
        crate::manifest::MathverseManifest::from_file(&manifest_path).expect("load manifest");
    let on_disk = manifest
        .base_shards
        .iter()
        .find(|e| e.source == NNVERIFY_IEEE754_SHARD_NAME)
        .expect("manifest must contain the nnverify_ieee754 entry");
    assert_eq!(on_disk.content_hash, reg.entry.content_hash);
    assert_eq!(on_disk.constant_count, reg.entry.constant_count);
    assert_eq!(on_disk.expr_count, reg.entry.expr_count);

    // The recorded hash matches a fresh hash of the on-disk shard bytes.
    let shard_path = library_root
        .join(NNVERIFY_IEEE754_SHARD_SUBDIR)
        .join(format!("{NNVERIFY_IEEE754_SHARD_NAME}.mathverse"));
    let on_disk_bytes = std::fs::read(&shard_path).expect("read shard bytes");
    assert_eq!(
        blake3::hash(&on_disk_bytes).to_hex().to_string(),
        reg.entry.content_hash,
        "manifest content_hash must hash the actual shard bytes"
    );

    // --- verify: reload + kernel-re-check every constant + empty closures ---
    let verify = verify_nnverify_ieee754_shard(&shard_path).expect("verify shard");
    assert!(
        verify.rejections.is_empty(),
        "no constant may be rejected on kernel re-check: {:?}",
        verify.rejections
    );
    assert_eq!(
        verify.kernel_rechecked,
        NNVERIFY_IEEE754_DECLS.len(),
        "every published constant must kernel-re-check from the shard"
    );
    assert_eq!(
        verify.empty_closure_verified.len(),
        NNVERIFY_IEEE754_EMPTY_CLOSURE_THEOREMS.len(),
        "every empty-closure theorem must re-verify with an empty axiom closure"
    );
    assert!(
        verify.is_clean(),
        "verification result must be fully clean: {verify:?}"
    );

    // Spot-check the load-bearing soundness theorems are among those verified.
    for &thm in &[
        "NNVerify.FloatRational.rounding_error_le_half_ulp",
        "NNVerify.FloatRational.rounding_error_le_half_ulp_denormal",
        "NNVerify.FloatRational.float_to_rat_exact_discharge_01",
    ] {
        assert!(
            verify.empty_closure_verified.iter().any(|n| n == thm),
            "{thm} must re-verify empty-closure from the shard"
        );
    }
}

/// Re-registering is idempotent: a second `register_*` call leaves exactly one
/// manifest entry for the shard (no duplicate accumulation).
#[test]
fn register_is_idempotent() {
    let dir = tempfile::tempdir().expect("tempdir");
    let library_root = dir.path().join("mathverse-library");

    let first = register_nnverify_ieee754_shard(&library_root).expect("first register");
    let second = register_nnverify_ieee754_shard(&library_root).expect("second register");
    // Deterministic build → identical bytes → identical hash.
    assert_eq!(first.entry.content_hash, second.entry.content_hash);

    let manifest =
        crate::manifest::MathverseManifest::from_file(library_root.join("manifest.json"))
            .expect("load manifest");
    let count = manifest
        .base_shards
        .iter()
        .filter(|e| e.source == NNVERIFY_IEEE754_SHARD_NAME)
        .count();
    assert_eq!(
        count, 1,
        "re-registration must not duplicate the manifest entry"
    );
}

/// MANUAL one-shot: write the shard + manifest entry into the REAL in-repo
/// library at `data/mathverse-library/`. Ignored so the normal suite never
/// mutates the repo; run explicitly to (re)generate the registered shard.
#[test]
#[ignore = "writes into data/mathverse-library; run explicitly to register"]
fn register_into_repo_library() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../data/mathverse-library");
    let reg = register_nnverify_ieee754_shard(&root).expect("register into repo library");
    let shard_path = root
        .join(NNVERIFY_IEEE754_SHARD_SUBDIR)
        .join(format!("{NNVERIFY_IEEE754_SHARD_NAME}.mathverse"));
    let verify = verify_nnverify_ieee754_shard(&shard_path).expect("verify");
    eprintln!(
        "REGISTERED path={} hash={} constants={} exprs={}",
        reg.entry.path, reg.entry.content_hash, reg.entry.constant_count, reg.entry.expr_count
    );
    eprintln!(
        "VERIFY total={} rechecked={} empty_closure_verified={} clean={}",
        verify.total,
        verify.kernel_rechecked,
        verify.empty_closure_verified.len(),
        verify.is_clean()
    );
    assert!(verify.is_clean());
}
