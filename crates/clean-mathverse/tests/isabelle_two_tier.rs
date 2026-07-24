// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Two-tier trusted-ledger import regression (`ISA_TRUSTED_LEDGER`).
//!
//! Drives the REAL committed HOL foundational closure — augmented with one
//! synthetic dependent that references a known reject-but-embeddable primary —
//! through the batch verifier twice: once with the trusted-ledger lane OFF
//! (default), once with it ON. It asserts the binding soundness contract of the
//! two-tier importer:
//!
//!   1. **KernelVerified is invariant.** The set (and count) of tier-1
//!      `KernelVerified` theorems is identical between the two runs. The ledger
//!      lane only ever *reclassifies lines that would otherwise be rejected*; it
//!      can never promote a reject to KV nor demote a former KV. (CLAUDE.md
//!      strictly-additive discipline: 0 former-KV lost, same count as no-ledger.)
//!   2. **Default OFF is byte-identical.** With the flag unset all ledger
//!      counters are `0`/empty and the produced shard bytes match a second OFF
//!      run exactly.
//!   3. **Ledger populated + dependents tier-2.** With the flag ON the fixture's
//!      reject-but-embeddable primaries are registered as trusted-ledger axioms
//!      (`ledger_size >= 1`) and the synthetic dependent that references one of
//!      them kernel-checks *modulo the ledger* — `KernelCheckedConditional`
//!      (tier-2, `kernel_checked_ledger >= 1`), never `KernelVerified`.
//!   4. **Conservation.** In both runs
//!      `KernelVerified + KernelCheckedConditional + ledger + rejected == total`,
//!      and every reclassified line comes out of the reject bucket:
//!      `rejected(OFF) - rejected(ON) == ledger(ON) + tier2(ON)`.
//!   5. **Ledger axioms are restatements, never proofs** — counted in
//!      `ledger_size`, NOWHERE in `kernel_verified` (CLAUDE.md: `Theorem`
//!      wrapping `Axiom` is NOT a proof).
//!
//! The env var is process-global, so both directions run in this single test
//! (never split across two `#[test]`s that could race the shared variable).

use clean_mathverse::hol::isabelle_pure::{parse_proven_theorem, IsaProof, IsaProvenTheorem};
use clean_mathverse::hol::isabelle_pure_verify::{import_proven_theorems, PureVerifiedImport};
use clean_mathverse::shard::ShardWriter;

const FIXTURE: &str = include_str!("fixtures/isabelle/hol_foundational_closure.jsonl");

const LEDGER_ENV: &str = "ISA_TRUSTED_LEDGER";

/// A reject-but-embeddable primary in the committed closure: its proof
/// translates to a well-formed statement TYPE but the kernel rejects the proof
/// VALUE, so under the ledger lane it becomes `isabelle.trusted.s306`.
const LEDGERED_PRIMARY_SERIAL: i64 = 306;
/// The synthetic tier-2 dependent's own serial (disjoint from the fixture).
const DEPENDENT_SERIAL: i64 = 999_000;
const DEPENDENT_NAME: &str = "test.tier2_dependent";

/// Parse the committed closure and append one synthetic dependent whose whole
/// proof is a bare `PThm` reference to [`LEDGERED_PRIMARY_SERIAL`]. Under OFF
/// the primary is rejected, so the dependency is unresolved and the dependent
/// is rejected too; under ON the primary is ledgered, so the reference resolves
/// to the trusted-ledger axiom and the dependent kernel-checks as tier-2.
fn parse_augmented_corpus() -> Vec<IsaProvenTheorem> {
    let mut theorems: Vec<IsaProvenTheorem> = FIXTURE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| parse_proven_theorem(l).ok())
        .collect();
    assert!(
        theorems.len() >= 130,
        "fixture should parse the full closure, got {}",
        theorems.len()
    );
    let primary_prop = theorems
        .iter()
        .find(|t| t.serial == LEDGERED_PRIMARY_SERIAL)
        .unwrap_or_else(|| panic!("fixture must contain serial {LEDGERED_PRIMARY_SERIAL}"))
        .prop
        .clone();
    // The dependent asserts exactly the primary's statement, proved by a single
    // `PThm` reference to it — the minimal shape that puts the ledger axiom into
    // the dependent's transitive axiom closure.
    theorems.push(IsaProvenTheorem {
        name: DEPENDENT_NAME.to_string(),
        serial: DEPENDENT_SERIAL,
        prop: primary_prop,
        proof: IsaProof::Thm {
            id: LEDGERED_PRIMARY_SERIAL,
            thy: "HOL".to_string(),
            tyinst: Vec::new(),
            tminst: Vec::new(),
        },
    });
    theorems
}

/// Run one import pass, returning the summary plus the serialized shard bytes.
fn run_pass(theorems: &[IsaProvenTheorem]) -> (PureVerifiedImport, Vec<u8>) {
    let mut writer = ShardWriter::new();
    let result = import_proven_theorems(theorems, &mut writer);
    let mut bytes = Vec::new();
    writer.write(&mut bytes).expect("serialize shard");
    (result, bytes)
}

/// The KernelVerified name set, sorted — the tier-1 identity we conserve.
fn kv_names(result: &PureVerifiedImport) -> Vec<String> {
    let mut names = result.names.clone();
    names.sort();
    names
}

#[test]
fn two_tier_ledger_preserves_kernel_verified_and_is_off_by_default() {
    let theorems = parse_augmented_corpus();
    let total = theorems.len();

    // --- OFF run A (default): the historical single-tier importer. ---
    // The guard keeps LEDGER_ENV unset for both OFF runs and restores it on exit.
    let _g_ledger = clean_mathverse::process_env::ScopedEnvVar::unset(LEDGER_ENV);
    let (off_a, off_a_bytes) = run_pass(&theorems);

    // --- OFF run B: byte-identical determinism check. ---
    let (off_b, off_b_bytes) = run_pass(&theorems);
    assert_eq!(
        off_a_bytes, off_b_bytes,
        "two OFF runs must produce byte-identical shards (determinism)"
    );
    assert_eq!(off_a.kernel_verified, off_b.kernel_verified);

    // (2) Flag OFF => every ledger counter is inert.
    assert_eq!(off_a.kernel_checked_ledger, 0, "tier-2 must be 0 when OFF");
    assert_eq!(off_a.ledger_size, 0, "ledger must be 0 when OFF");
    assert!(off_a.ledger.is_empty(), "ledger records must be empty OFF");
    assert!(
        off_a.written_constants.is_empty(),
        "written_constants is a ledger-run artifact, empty OFF"
    );
    // Historical conservation invariant holds unchanged when OFF.
    assert_eq!(
        off_a.kernel_verified + off_a.rejected,
        total,
        "OFF: KV + rejected == total"
    );
    assert_eq!(
        off_a.kernel_verified,
        off_a.names.len(),
        "OFF: names track KV exactly"
    );

    // --- ON run: two-tier trusted-ledger lane. Scoped so LEDGER_ENV reverts to
    // the unset state above immediately after this run. ---
    let (on, _on_bytes) = {
        let _g_on = clean_mathverse::process_env::ScopedEnvVar::set(LEDGER_ENV, "1");
        run_pass(&theorems)
    };

    eprintln!(
        "TWO-TIER: total={total} | OFF: KV={} rejected={} | ON: KV={} tier2={} ledger={} rejected={}",
        off_a.kernel_verified,
        off_a.rejected,
        on.kernel_verified,
        on.kernel_checked_ledger,
        on.ledger_size,
        on.rejected,
    );

    // (1) KernelVerified is INVARIANT — same count AND same name set.
    assert_eq!(
        on.kernel_verified, off_a.kernel_verified,
        "ledger ON must not change the KernelVerified count (strictly additive)"
    );
    assert_eq!(
        kv_names(&on),
        kv_names(&off_a),
        "ledger ON must not change WHICH theorems are KernelVerified"
    );

    // (3) Ledger populated and at least one dependent is tier-2. These are
    // conservative lower bounds over the current committed fixture (raise them
    // as the bootstrap changes), exactly like `isabelle_closure_replay`.
    assert!(
        on.ledger_size >= 1,
        "ledger ON must register at least the reject-but-embeddable primaries, got {}",
        on.ledger_size
    );
    assert!(
        on.kernel_checked_ledger >= 1,
        "the synthetic dependent must be tier-2 (KernelCheckedConditional), got {}",
        on.kernel_checked_ledger
    );
    // (5) ledger_size mirrors the records vector exactly.
    assert_eq!(
        on.ledger_size,
        on.ledger.len(),
        "ledger_size must equal the number of ledger records"
    );
    // The known reject-but-embeddable primary is among the registered axioms.
    assert!(
        on.ledger.iter().any(|e| e.serial == LEDGERED_PRIMARY_SERIAL
            && e.axiom_name == format!("isabelle.trusted.s{LEDGERED_PRIMARY_SERIAL}")),
        "serial {LEDGERED_PRIMARY_SERIAL} must be registered as a trusted-ledger axiom"
    );

    // (4) Conservation with all three tiers.
    assert_eq!(
        on.kernel_verified + on.kernel_checked_ledger + on.ledger_size + on.rejected,
        total,
        "ON: KV + tier2 + ledger + rejected == total"
    );
    // Every reclassified line is drained out of the reject bucket — the ledger
    // lane never invents work, it only relabels former rejects.
    assert!(
        on.rejected <= off_a.rejected,
        "ledger ON can only shrink the reject bucket"
    );
    assert_eq!(
        off_a.rejected - on.rejected,
        on.ledger_size + on.kernel_checked_ledger,
        "reclassified rejects == ledger + tier-2"
    );

    // The tier-2 dependent is NEVER KernelVerified.
    assert!(
        !on.names.iter().any(|n| n == DEPENDENT_NAME),
        "the tier-2 dependent must never be counted KernelVerified"
    );
    // Tier-1 KV is DISJOINT from the trusted-ledger axiom namespace.
    for name in &on.names {
        assert!(
            !name.starts_with("isabelle.trusted."),
            "a trusted-ledger axiom ({name}) must never be counted KernelVerified"
        );
    }
}
