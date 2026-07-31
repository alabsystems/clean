// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Ledger burn-down retry** equivalence gate (`ISA_RETRY_LEDGER`, P-ledger of
//! the two-tier trusted-ledger lane; see
//! `designs/2026-07-17-isabelle-ledger-retry.md`).
//!
//! The contract under test: when a newly-landed prover arm can prove a line that a
//! prior grand could only *ledger* (or only kernel-check *modulo* the ledger =
//! tier-2), a `--retry-ledger` pass — re-attempting the non-KV lines against the
//! standing snapshot, NOT replaying the whole corpus — must reproduce a fresh
//! grand's classification of the whole corpus EXACTLY, while keeping tier-1
//! `KernelVerified` byte-invariant.
//!
//! # The deterministic "new arm" seam
//!
//! `ISA_WITHHOLD_DEF_CONSTS=isabelle.def.HOL.If` reproduces a *pre-registration*
//! translator build: without the `HOL.If` def-const, `Int.power_int_def`'s
//! reflexive `_def` proof cannot close, so under the ledger lane its STATEMENT
//! embeds but its PROOF fails → it is registered as the trusted-ledger axiom
//! `isabelle.trusted.s94308` (verified by `retry_parity_registration_altering_round_flips_dependent`
//! in `isabelle_snapshot_resume.rs`, which uses the same seam for the reject→KV
//! case). Dropping the withhold — the "new binary" — makes the same line KV. That
//! is a genuine ledger→KV flip, and its bare-`PThm` dependent flips tier-2→KV.

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::Mutex;

use clean_mathverse::hol::isabelle_pure_verify::{
    import_proven_theorems_retry, import_proven_theorems_streaming, PureVerifiedImport,
};
use clean_mathverse::shard::ShardWriter;

/// The real single-line `Int.power_int_def` export (serial 94308): KV under the
/// new arm, trusted-ledger under the withheld-`HOL.If` old arm.
const POWER_INT_DEF: &str = include_str!("fixtures/isabelle/power_int_def.json");
const POWER_INT_SERIAL: i64 = 94308;
const POWER_INT_NAME: &str = "Int.power_int_def";
const HOL_IF_DEF_CONST: &str = "isabelle.def.HOL.If";

/// A plain `a = a` proved by `HOL.refl a` (serial 94305) — KV under BOTH arms; the
/// byte-invariance witness (it is in the accepted KV prefix, never re-attempted).
const K_KV: &str = r#"{"name":"test.k_a_eq_a","serial":94305,"prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"HOL.bool","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}},"proof":{"k":"appt","f":{"k":"axm","name":"HOL.refl"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}}"#;

/// A PERMANENT trusted-ledger line (serial 94306): its statement `a = b` (two
/// DISTINCT free vars) embeds as a well-formed — though unprovable — Prop, so its
/// TYPE registers as the trusted-ledger axiom `isabelle.trusted.s94306`, but no arm
/// can prove it: it is not reflexive, so neither the recorded `HOL.refl a` proof
/// (which proves `a = a`) nor the translator's fabricated-`Eq.refl` fallback
/// type-checks against `a = b`. It therefore stays ledger under EVERY arm (the
/// case-(b) still-unprovable ledger entry). A single-free-var `a = a` will NOT do:
/// it is genuinely reflexive, so the fabricated `Eq.refl a` proves it (→ KV).
const Z_LEDGER: &str = r#"{"name":"test.z_still_ledger","serial":94306,"prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"HOL.bool","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'a"}}}},"proof":{"k":"appt","f":{"k":"axm","name":"HOL.refl"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}}"#;

const Z_SERIAL: i64 = 94306;
/// The tier-2 dependent (serial 94309): asserts `Int.power_int_def`'s statement,
/// proved by a bare `PThm` reference to serial 94308. Under the old arm 94308 is a
/// ledger axiom, so this kernel-checks *modulo* the ledger → tier-2; under the new
/// arm 94308 is KV, so the reference resolves against the KV closure → tier-1 KV
/// (a tier-2→KV promotion — the "support shrinks" case).
const D_SERIAL: i64 = 94309;
const D_NAME: &str = "test.power_int_dep";

/// Env choreography is process-global; serialize this binary's tests on one lock.
static ENV_LOCK: Mutex<()> = Mutex::new(());

fn write_lines(path: &PathBuf, lines: &[&str]) {
    let mut f = std::fs::File::create(path).expect("create corpus file");
    for l in lines {
        writeln!(f, "{l}").expect("write corpus line");
    }
}

/// Build the tier-2 dependent line: `Int.power_int_def`'s prop, proved by a bare
/// `PThm` reference to serial 94308.
fn build_dependent() -> String {
    let pdef: serde_json::Value =
        serde_json::from_str(POWER_INT_DEF.trim()).expect("parse power_int_def");
    let prop = pdef.get("prop").expect("power_int_def has a prop").clone();
    let d = serde_json::json!({
        "name": D_NAME,
        "serial": D_SERIAL,
        "prop": prop,
        "proof": {"k": "thm", "id": POWER_INT_SERIAL, "thy": "Int"},
    });
    serde_json::to_string(&d).expect("serialize dependent")
}

const TEST_ENV_VARS: &[&str] = &[
    "ISA_SNAPSHOT_IN",
    "ISA_SNAPSHOT_OUT",
    "ISA_ELIDE_PROOFS",
    "ISA_TRUSTED_LEDGER",
    "ISA_RETRY_LEDGER",
    "ISA_RETRY_SEED",
    "ISA_WITHHOLD_DEF_CONSTS",
    "ISA_RETRY_SKIP_REGISTRY_REFRESH",
    "ISA_SNAPSHOT_SKIP_PREFIX_HASH",
    "ISA_SNAPSHOT_ALLOW_MISMATCH",
    "ISA_SNAPSHOT_EVERY",
    "ISA_PROGRESS_EVERY",
];

fn clear_env() {
    for &v in TEST_ENV_VARS {
        clean_mathverse::process_env::remove_persistent(v);
    }
}

fn clear_scoped_env(env: &mut clean_mathverse::process_env::EnvEditor) {
    for &v in TEST_ENV_VARS {
        env.remove(v);
    }
}

/// The sorted KV name set + the sorted ledger serial set — the identity a ledger
/// retry must reproduce from a fresh grand.
fn identity(r: &PureVerifiedImport) -> (Vec<String>, Vec<i64>) {
    let mut names = r.names.clone();
    names.sort();
    let mut led: Vec<i64> = r.ledger.iter().map(|e| e.serial).collect();
    led.sort_unstable();
    (names, led)
}

#[test]
fn ledger_retry_flips_ledger_and_tier2_to_kv_matching_fresh_grand() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = std::env::temp_dir().join(format!("isa_ledger_retry_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("corpus.jsonl");
    let old_snap = dir.join("old_arm.snap");

    let dependent = build_dependent();
    // Serial-ascending (deps before uses): K(94305) Z(94306) power_int(94308) D(94309).
    write_lines(&corpus, &[K_KV, Z_LEDGER, POWER_INT_DEF.trim(), &dependent]);

    // === 1) FRESH GRAND under the NEW arm (HOL.If present) — the target. ===
    clear_env();
    clean_mathverse::process_env::set_persistent("ISA_TRUSTED_LEDGER", "1");
    let mut w = ShardWriter::new();
    let fresh = import_proven_theorems_streaming(&corpus, &mut w).expect("fresh grand");
    clear_env();

    eprintln!(
        "FRESH(new arm): KV={} tier2={} ledger={} rejected={} names={:?} ledger={:?}",
        fresh.kernel_verified,
        fresh.kernel_checked_ledger,
        fresh.ledger_size,
        fresh.rejected,
        fresh.names,
        fresh.ledger.iter().map(|e| e.serial).collect::<Vec<_>>(),
    );
    // Fresh: K, power_int, D all KV; Z ledger; nothing tier-2 or rejected.
    assert_eq!(fresh.kernel_verified, 3, "fresh: K + power_int + D are KV");
    assert_eq!(fresh.kernel_checked_ledger, 0, "fresh: no tier-2");
    assert_eq!(fresh.ledger_size, 1, "fresh: only Z ledgers");
    assert_eq!(fresh.rejected, 0, "fresh: nothing rejected");
    assert!(
        fresh.names.iter().any(|n| n == POWER_INT_NAME),
        "fresh: power_int_def is KV"
    );
    assert!(fresh.names.iter().any(|n| n == D_NAME), "fresh: D is KV");
    assert_eq!(
        fresh.ledger[0].serial, Z_SERIAL,
        "fresh: Z is the sole ledger entry"
    );

    // === 2) OLD-ARM snapshot (HOL.If withheld) — power_int ledgers, D tier-2. ===
    clean_mathverse::process_env::set_persistent("ISA_TRUSTED_LEDGER", "1");
    clean_mathverse::process_env::set_persistent("ISA_WITHHOLD_DEF_CONSTS", HOL_IF_DEF_CONST);
    clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &old_snap);
    let mut w = ShardWriter::new();
    let old = import_proven_theorems_streaming(&corpus, &mut w).expect("old-arm grand");
    clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
    clean_mathverse::process_env::remove_persistent("ISA_WITHHOLD_DEF_CONSTS");
    clear_env();
    assert!(old_snap.exists(), "old-arm snapshot written");

    eprintln!(
        "OLD(withheld arm): KV={} tier2={} ledger={} rejected={} ledger_serials={:?}",
        old.kernel_verified,
        old.kernel_checked_ledger,
        old.ledger_size,
        old.rejected,
        old.ledger.iter().map(|e| e.serial).collect::<Vec<_>>(),
    );
    assert_eq!(
        old.kernel_verified, 1,
        "old: only K is KV (power_int ledgers)"
    );
    assert_eq!(
        old.kernel_checked_ledger, 1,
        "old: D is tier-2 (references the power_int ledger axiom)"
    );
    assert_eq!(old.ledger_size, 2, "old: Z and power_int both ledger");
    assert_eq!(old.rejected, 0, "old: nothing is a bare reject");
    let old_led: Vec<i64> = {
        let mut v: Vec<i64> = old.ledger.iter().map(|e| e.serial).collect();
        v.sort_unstable();
        v
    };
    assert_eq!(
        old_led,
        vec![Z_SERIAL, POWER_INT_SERIAL],
        "old: ledger = {{Z, power_int}}"
    );

    // === 3) PLAIN retry (rejects-only) must flip NOTHING — the contrast. ===
    // The old snapshot has an empty reject index (every line is KV/ledger/tier-2),
    // so a rejects-only retry re-attempts zero lines and reproduces `old` exactly.
    for workers in [0usize, 4usize] {
        clean_mathverse::process_env::set_persistent("ISA_TRUSTED_LEDGER", "1");
        let mut w = ShardWriter::new();
        let plain = import_proven_theorems_retry(&corpus, &old_snap, &mut w, workers)
            .unwrap_or_else(|e| panic!("plain retry (workers={workers}) failed: {e}"));
        clear_env();
        assert_eq!(
            plain.kernel_verified, old.kernel_verified,
            "plain retry (workers={workers}) must not flip any ledger entry"
        );
        assert_eq!(
            plain.ledger_size, old.ledger_size,
            "plain retry (workers={workers}) must leave the ledger unchanged"
        );
    }

    // === 4) LEDGER retry (new arm) must reproduce the FRESH grand EXACTLY. ===
    let fresh_identity = identity(&fresh);
    for workers in [0usize, 4usize] {
        let new_snap = dir.join(format!("new_arm_{workers}.snap"));
        clean_mathverse::process_env::set_persistent("ISA_TRUSTED_LEDGER", "1");
        clean_mathverse::process_env::set_persistent("ISA_RETRY_LEDGER", "1");
        clean_mathverse::process_env::set_persistent("ISA_SNAPSHOT_OUT", &new_snap);
        let mut w = ShardWriter::new();
        let retried = import_proven_theorems_retry(&corpus, &old_snap, &mut w, workers)
            .unwrap_or_else(|e| panic!("ledger retry (workers={workers}) failed: {e}"));
        clean_mathverse::process_env::remove_persistent("ISA_SNAPSHOT_OUT");
        clear_env();

        eprintln!(
            "LEDGER-RETRY(workers={workers}): KV={} tier2={} ledger={} rejected={}",
            retried.kernel_verified,
            retried.kernel_checked_ledger,
            retried.ledger_size,
            retried.rejected,
        );

        // (a) Equivalence: the whole-corpus classification equals a fresh grand's.
        assert_eq!(
            retried.kernel_verified, fresh.kernel_verified,
            "ledger retry (workers={workers}) KV count must equal the fresh grand's"
        );
        assert_eq!(
            retried.kernel_checked_ledger, fresh.kernel_checked_ledger,
            "ledger retry (workers={workers}) tier-2 count must equal the fresh grand's"
        );
        assert_eq!(
            retried.ledger_size, fresh.ledger_size,
            "ledger retry (workers={workers}) ledger size must equal the fresh grand's"
        );
        assert_eq!(
            identity(&retried),
            fresh_identity,
            "ledger retry (workers={workers}) KV-name + ledger-serial identity must equal fresh"
        );

        // (a) The ledger primary flipped ledger→KV; its dependent flipped tier-2→KV.
        assert!(
            retried.names.iter().any(|n| n == POWER_INT_NAME),
            "ledger retry (workers={workers}): power_int_def flipped ledger→KV"
        );
        assert!(
            retried.names.iter().any(|n| n == D_NAME),
            "ledger retry (workers={workers}): dependent flipped tier-2→KV"
        );
        assert!(
            !retried.ledger.iter().any(|e| e.serial == POWER_INT_SERIAL),
            "ledger retry (workers={workers}): the power_int ledger axiom is gone (trust shrank)"
        );

        // (b) The still-unprovable ledger entry stays ledger.
        assert_eq!(
            retried.ledger.len(),
            1,
            "workers={workers}: one residual ledger"
        );
        assert_eq!(
            retried.ledger[0].serial, Z_SERIAL,
            "ledger retry (workers={workers}): Z stays ledger"
        );

        // (c) Tier-1 byte-invariance: K (KV in the OLD snapshot) is still KV, and
        //     the KV set only GREW (never lost a former-KV line).
        assert!(
            retried.names.iter().any(|n| n == "test.k_a_eq_a"),
            "ledger retry (workers={workers}): the pre-existing KV line K is preserved"
        );

        // The updated snapshot's KV closure holds the flipped serials (the
        // burn-down is durable for the next incremental pass).
        let new =
            clean_mathverse::hol::isabelle_pure_verify::snapshot::load_snapshot_retry(&new_snap)
                .expect("reload updated snapshot");
        assert!(
            new.closure.contains_key(&POWER_INT_SERIAL),
            "workers={workers}: power_int is in the updated KV closure"
        );
        assert!(
            new.closure.contains_key(&D_SERIAL),
            "workers={workers}: dependent is in the updated KV closure"
        );
        assert!(
            !new.closure.contains_key(&Z_SERIAL),
            "workers={workers}: the still-ledger Z is NOT in the KV closure"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// **Targeted re-attempt SEED (`ISA_RETRY_SEED`).** A seeded ledger retry
/// re-verifies ONLY the seeded serials; every OTHER non-KV line RETAINS its
/// snapshot verdict (ledger stays ledger, tier-2 stays tier-2). The efficiency
/// lever behind the v3.2 incident: rather than re-attempt all ~277k non-KV lines
/// to find the ~54 flips from one narrow arm, the seed bounds the attempt to just
/// the target family — a minutes operation instead of a 30h one — while proving
/// that family flips 0-loss at corpus scale.
///
/// Same old-arm snapshot as the full ledger-retry gate (power_int LEDGERs, its
/// dependent is tier-2, Z is a permanent ledger). The seed holds ONLY power_int's
/// serial, so:
///   * power_int (SEEDED, a ledger axiom) is re-attempted and flips ledger→KV;
///   * Z (UNSEEDED ledger) is untouched — stays ledger;
///   * the dependent (UNSEEDED tier-2) is NOT re-attempted — stays tier-2, even
///     though power_int is now KV (the contrast to the full retry, where it flips).
/// The seed file carries a `#` comment line to exercise comment stripping.
#[test]
fn seeded_ledger_retry_attempts_only_seed_and_leaves_unseeded_untouched() {
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clean_mathverse::process_env::with_env_edits(seeded_ledger_retry_with_env);
}

fn seeded_ledger_retry_with_env(env: &mut clean_mathverse::process_env::EnvEditor) {
    let dir = std::env::temp_dir().join(format!("isa_seed_retry_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk tmpdir");
    let corpus = dir.join("corpus.jsonl");
    let old_snap = dir.join("old_arm.snap");
    let seed_file = dir.join("family.seed");

    let dependent = build_dependent();
    // Serial-ascending: K(94305) Z(94306) power_int(94308) D(94309).
    write_lines(&corpus, &[K_KV, Z_LEDGER, POWER_INT_DEF.trim(), &dependent]);

    // Seed = ONLY power_int's serial (plus a comment + blank line to test parsing).
    std::fs::write(
        &seed_file,
        format!("# ISA_CLASS_OPERAND_ALIGN target family (test)\n\n{POWER_INT_SERIAL}\n"),
    )
    .expect("write seed file");

    // === OLD-ARM snapshot (HOL.If withheld): power_int ledgers, D tier-2. ===
    clear_scoped_env(env);
    env.set("ISA_TRUSTED_LEDGER", "1");
    env.set("ISA_WITHHOLD_DEF_CONSTS", HOL_IF_DEF_CONST);
    env.set("ISA_SNAPSHOT_OUT", &old_snap);
    let mut w = ShardWriter::new();
    let old = import_proven_theorems_streaming(&corpus, &mut w).expect("old-arm grand");
    clear_scoped_env(env);
    assert!(old_snap.exists(), "old-arm snapshot written");
    assert_eq!(old.kernel_verified, 1, "old: only K is KV");
    assert_eq!(old.ledger_size, 2, "old: Z and power_int both ledger");
    assert_eq!(old.kernel_checked_ledger, 1, "old: D is tier-2");

    // === SEEDED ledger retry (new arm) re-attempts ONLY power_int. ===
    for workers in [0usize, 4usize] {
        let new_snap = dir.join(format!("seeded_{workers}.snap"));
        clear_scoped_env(env);
        env.set("ISA_TRUSTED_LEDGER", "1");
        env.set("ISA_RETRY_LEDGER", "1");
        env.set("ISA_RETRY_SEED", &seed_file);
        env.set("ISA_SNAPSHOT_OUT", &new_snap);
        let mut w = ShardWriter::new();
        let seeded = import_proven_theorems_retry(&corpus, &old_snap, &mut w, workers)
            .unwrap_or_else(|e| panic!("seeded ledger retry (workers={workers}) failed: {e}"));
        clear_scoped_env(env);

        eprintln!(
            "SEEDED-RETRY(workers={workers}): KV={} tier2={} ledger={} names={:?} ledger_serials={:?}",
            seeded.kernel_verified,
            seeded.kernel_checked_ledger,
            seeded.ledger_size,
            seeded.names,
            seeded.ledger.iter().map(|e| e.serial).collect::<Vec<_>>(),
        );

        // The SEEDED line flipped ledger→KV.
        assert!(
            seeded.names.iter().any(|n| n == POWER_INT_NAME),
            "seeded retry (workers={workers}): power_int_def (seeded) flipped ledger→KV"
        );
        assert!(
            !seeded.ledger.iter().any(|e| e.serial == POWER_INT_SERIAL),
            "seeded retry (workers={workers}): the seeded power_int ledger axiom is gone (trust shrank)"
        );
        // Only power_int flipped: K (prefix) + power_int = 2 KV.
        assert_eq!(
            seeded.kernel_verified, 2,
            "seeded retry (workers={workers}): only the seeded line flips (K + power_int = 2 KV)"
        );

        // The UNSEEDED tier-2 dependent is UNTOUCHED — NOT re-attempted, so it
        // stays tier-2 even though power_int is now KV (the seed's whole point).
        assert!(
            !seeded.names.iter().any(|n| n == D_NAME),
            "seeded retry (workers={workers}): the UNSEEDED dependent must NOT be re-attempted \
             (stays tier-2, not KV)"
        );
        assert_eq!(
            seeded.kernel_checked_ledger, 1,
            "seeded retry (workers={workers}): the unseeded tier-2 dependent is retained (still tier-2)"
        );

        // The UNSEEDED permanent ledger Z is UNTOUCHED — still ledger.
        assert_eq!(
            seeded.ledger_size, 1,
            "seeded retry (workers={workers}): one residual ledger (the unseeded Z)"
        );
        assert!(
            seeded.ledger.iter().any(|e| e.serial == Z_SERIAL),
            "seeded retry (workers={workers}): the UNSEEDED ledger Z is retained untouched"
        );

        // The updated snapshot's KV closure holds ONLY the seeded flip — the
        // unseeded tier-2 dependent and ledger Z stay OUT of the KV closure.
        let new =
            clean_mathverse::hol::isabelle_pure_verify::snapshot::load_snapshot_retry(&new_snap)
                .expect("reload updated snapshot");
        assert!(
            new.closure.contains_key(&POWER_INT_SERIAL),
            "workers={workers}: the seeded power_int is in the updated KV closure"
        );
        assert!(
            !new.closure.contains_key(&D_SERIAL),
            "workers={workers}: the UNSEEDED dependent is NOT promoted to the KV closure"
        );
        assert!(
            !new.closure.contains_key(&Z_SERIAL),
            "workers={workers}: the UNSEEDED ledger Z is NOT in the KV closure"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
