// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R1-MM — the Metamath two-pass exit theorem, as an ARTIFACT.
//!
//! The last production `add_decl_unchecked` call site
//! (`crates/clean-kernel/src/env/decl_add.rs`, the `mm_axiom_only()` arm of
//! `Environment::add_decl`) is sound today by a PROSE argument with three
//! mechanisms. This file mechanizes that argument. It also carried, for one
//! commit, a CHARACTERIZATION test for the one place where the code did NOT
//! support the prose; that gap is closed and the test is inverted (see HISTORY
//! below).
//!
//! * **(1) FAIL-CLOSED ENTRY.** The proof-drop arm fires only when an
//!   `MmAxiomOnlyGuard` is live (`mm_two_pass_active()`); the flag alone is not
//!   enough, and the guard forces the flag off on drop.
//!   → `test_axiom_only_proof_drop_is_gated_by_the_two_pass_sentinel`
//! * **(2) PASS-2 RE-VERIFICATION.** Nothing pass 1 registers is ever a
//!   verification result; every reported label was re-added through the CHECKED
//!   `add_decl`, which `infer_sort`s the type and `check_type`s the proof.
//!   → `test_pass1_alone_reports_no_verdict_at_all`,
//!     `test_pass1_type_export_never_reports_a_verdict`,
//!     `test_a_rejected_proof_is_never_verified_by_any_two_pass_range`
//! * **(3) DEPENDENCY-CLOSURE GATE.** Only labels whose transitive `$p`-closure is
//!   itself verified survive.
//!   → `test_gate_removes_the_dependent_of_a_failed_dependency`,
//!     `test_gate_cascades_transitively`,
//!     `test_gate_drops_labels_that_are_not_provables_of_this_database`
//!
//! * **(3b) REUSABILITY MARKING.** A dependency that verified only on the GROUND
//!   (non-reusable) fallback takes every dependent down with it, exactly as it does
//!   in the sequential verifier — the gate's predicate is "verified AND citable",
//!   not "verified". Losing the marking (a stale, unstamped labels file) fails
//!   CLOSED.
//!   → `test_gate_drops_the_dependent_of_a_ground_only_dependency`,
//!     `test_unmarked_labels_file_fails_closed_instead_of_reading_as_reusable`,
//!     `test_ground_only_marking_survives_the_wire_format_round_trip`
//!
//! and the count-equivalence claim the SOUNDNESS comment rests on
//! (two-pass + gate ≡ sequential), which HOLDS on every corpus here — the clean
//! one, the two whose divergence is a FAILED dependency, and the GROUND-FALLBACK
//! one — in the production split-range configuration.
//!   → `test_split_range_two_pass_plus_gate_equals_sequential_*`
//!
//! HISTORY. The ground-fallback corpus used to be a CHARACTERIZATION test
//! (`test_ground_fallback_dep_divergence_survives_the_gate_known_gap`) asserting
//! `gate(two-pass) ⊋ sequential`, with a doc requiring it to be INVERTED rather
//! than deleted when the gap closed. It is now
//! `test_ground_fallback_dep_no_longer_diverges_from_sequential` and asserts
//! EQUALITY, plus the two facts that make the equality non-vacuous: the raw
//! (ungated) union still reports the dependent, and the ground-only dependency
//! itself still survives. See
//! `docs/issues/2026-08-23-r1-mm-two-pass-theorem.md`.

use std::collections::BTreeSet;

use clean_olean::metamath::{
    dependency_closure_gate, ground_reuse_exposure, kernel_verify_database,
    kernel_verify_pass1_types, kernel_verify_two_pass_range, parse_database, parse_verified_labels,
    provable_dependencies, render_verified_labels, resolve_database, Database, KernelVerifyReport,
    ResolvedStatement, Reusability, VerifiedLabels, VERIFIED_FORMAT_HEADER,
};

// ---------------------------------------------------------------------------
// Corpora
// ---------------------------------------------------------------------------

/// The standard `demo0.mm` database: `th1 : |- t = t` over a tiny arithmetic /
/// propositional signature.
const DEMO0_DB: &str = "\
$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp $.
";

/// `th1`'s uncompressed proof, reused verbatim to build adversarial theorems that
/// claim a DIFFERENT conclusion (so the tree builds but the kernel rejects it).
const TH1_PROOF: &str = "tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp";

/// CLEAN corpus: `th2` reuses the verified `th1`. Everything verifies both ways.
fn clean_corpus() -> String {
    format!("{DEMO0_DB}th2 $p |- ( t + 0 ) = ( t + 0 ) $= tt tze tpl th1 $.\n")
}

/// ADVERSARIAL corpus: `bad` claims `|- t = 0` with `th1`'s proof, so the kernel
/// REJECTS it; `usebad` cites `bad`. In the sequential verifier `usebad` is
/// skipped ("reuses $p theorem bad that did not verify"). In the two-pass verifier
/// `usebad` type-checks against `bad`'s PASS-1 axiom type and is REPORTED
/// VERIFIED — the gate is what removes it.
fn failed_dep_corpus() -> String {
    format!(
        "{DEMO0_DB}\
bad $p |- t = 0 $= {TH1_PROOF} $.
usebad $p |- ( t + 0 ) = 0 $= tt tze tpl bad $.
"
    )
}

/// ADVERSARIAL corpus, two levels: `bad` is rejected, `mid` cites `bad`, `top`
/// cites `mid`. The gate must cascade — removing `mid` must then remove `top`.
fn cascade_corpus() -> String {
    format!(
        "{DEMO0_DB}\
bad $p |- t = 0 $= {TH1_PROOF} $.
mid $p |- ( t + 0 ) = 0 $= tt tze tpl bad $.
top $p |- ( ( t + 0 ) + 0 ) = 0 $= tt tze tpl mid $.
"
    )
}

/// GROUND-FALLBACK corpus. `gth` applies the `$d x ph`-bearing `ax5` but its own
/// frame declares no `$d`, so the schematic-`$d` route cannot discharge the guard
/// and the verifier falls back to the GROUND (non-reusable) shape. `gth` still
/// VERIFIES; `usegth`, which cites it, is SKIPPED by the sequential verifier and
/// still reported by the RAW two-pass union — the gate drops it only because
/// `gth` is marked ground-only. This was the R1-MM known-gap corpus; it is now
/// one of the equivalence corpora
/// (`test_ground_fallback_dep_no_longer_diverges_from_sequential`).
const GROUND_FALLBACK_DB: &str = "\
$c wff setvar |- A. ( -> ) $.
$v x ph $.
vx $f setvar x $.
wph $f wff ph $.
wal $a wff A. x ph $.
${
    $d x ph $.
    ax5 $a |- ( ph -> A. x ph ) $.
$}
gth $p |- ( ph -> A. x ph ) $= vx wph ax5 $.
usegth $p |- ( ph -> A. x ph ) $= vx wph gth $.
";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse(src: &str) -> Database {
    parse_database(src).expect("corpus must parse")
}

fn provable_count(db: &Database) -> usize {
    let resolved = resolve_database(db).expect("corpus must resolve");
    resolved
        .statements
        .iter()
        .filter(|s| matches!(s, ResolvedStatement::Assertion(a) if a.kind == "provable"))
        .count()
}

fn labels(report: &KernelVerifyReport) -> BTreeSet<String> {
    report.verified.iter().cloned().collect()
}

/// The SEQUENTIAL verifier's accepted set — the reference the two-pass output is
/// supposed to reproduce.
fn sequential(db: &Database) -> BTreeSet<String> {
    labels(&kernel_verify_database(db).expect("sequential verification must run"))
}

/// The PRODUCTION two-pass configuration: `scripts/mm_two_pass.sh` splits the
/// provable ordinals into DISJOINT ranges, one worker each, and unions the
/// verified labels. Every dependency outside a worker's own range therefore stands
/// in that worker's environment as its PASS-1 unchecked axiom type — which is the
/// whole reason the gate exists.
///
/// The union goes THROUGH THE WIRE FORMAT (`render_verified_labels` →
/// `parse_verified_labels`), so what these tests exercise is exactly what
/// `mm_verify_range` writes and `mm_gate` reads — not a privileged in-process
/// shortcut past the file the driver actually produces.
fn two_pass_split_union(db: &Database) -> VerifiedLabels {
    let n = provable_count(db);
    let mut union = VerifiedLabels::new();
    for i in 0..n {
        let report =
            kernel_verify_two_pass_range(db, i..i + 1, n).expect("two-pass verification must run");
        union.merge(&parse_verified_labels(&render_verified_labels(&report)));
    }
    union
}

/// Two-pass over the WHOLE prefix in one worker — the configuration the
/// count-equivalence claim was originally measured in.
fn two_pass_full_range(db: &Database) -> VerifiedLabels {
    let n = provable_count(db);
    let report = kernel_verify_two_pass_range(db, 0..n, n).expect("two-pass verification must run");
    parse_verified_labels(&render_verified_labels(&report))
}

fn gate(db: &Database, verified: &VerifiedLabels) -> BTreeSet<String> {
    let resolved = resolve_database(db).expect("corpus must resolve");
    dependency_closure_gate(&resolved, verified)
}

/// A verified set with every label marked reusable — the shape a corpus with no
/// ground-only theorem produces, and the only shape in which the gate's OLD
/// (verified-only) predicate and its new (verified-and-citable) predicate agree.
fn all_reusable<'a>(labels: impl IntoIterator<Item = &'a str>) -> VerifiedLabels {
    let mut out = VerifiedLabels::new();
    for l in labels {
        out.insert(l, Reusability::Reusable);
    }
    out
}

// ---------------------------------------------------------------------------
// MECHANISM (1) — fail-closed entry
// ---------------------------------------------------------------------------

/// Build `Π (p : Prop), p → p` (a genuine `Prop`) and the two candidate proofs:
/// `λ p h, h` (checks) and `λ p h, p` (does not — `p : Prop` is not a proof of `p`).
fn id_prop_theorem(good: bool) -> clean_kernel::Declaration {
    use clean_kernel::{BinderInfo, Expr, Level, Name};
    let prop = Expr::sort(Level::zero());
    let bd = BinderInfo::Default;
    // Π (p : Prop), p → p
    let type_ = Expr::pi(bd, prop.clone(), Expr::arrow(Expr::bvar(0), Expr::bvar(1)));
    // λ (p : Prop), λ (h : p), h   /   λ (p : Prop), λ (h : p), p
    let body = if good { Expr::bvar(0) } else { Expr::bvar(1) };
    let value = Expr::lam(bd, prop, Expr::lam(bd, Expr::bvar(0), body));
    clean_kernel::Declaration::Theorem {
        name: Name::from_string("r1mm.probe"),
        level_params: vec![],
        type_,
        value,
    }
}

/// MECHANISM (1) + the teeth of MECHANISM (2), on the kernel side, in four arms.
///
/// The whole soundness of the ratchet row is that the ONLY thing separating "the
/// proof is kernel-checked" from "the proof is dropped unexamined" is the pair
/// (axiom-only flag, two-pass sentinel) — and that the pair cannot be forged from
/// outside `kernel_verify_two_pass_range`. All four arms observe the environment
/// afterwards, so "fails closed" means "registered nothing", not merely "returned
/// an error".
#[test]
fn test_axiom_only_proof_drop_is_gated_by_the_two_pass_sentinel() {
    use clean_kernel::{ConstantKind, Environment, Name};

    let name = Name::from_string("r1mm.probe");

    // ARM A — the CHECKED path really runs `check_type`: a bad proof is rejected.
    let mut env = Environment::new();
    let err = env
        .add_decl(id_prop_theorem(false))
        .expect_err("the checked add_decl must reject a proof that does not have the stated type");
    assert!(
        !matches!(err, clean_kernel::EnvError::AxiomOnlyMisuse { .. }),
        "arm A must fail on the TYPE CHECK, not on the sentinel; got {err:?}"
    );
    assert!(
        env.get_const(&name).is_none(),
        "a rejected theorem must register nothing"
    );
    // …and the same declaration with the RIGHT proof is accepted, so arm A is not
    // vacuously red for an unrelated reason.
    env.add_decl(id_prop_theorem(true))
        .expect("the checked add_decl must accept `fun p h => h : forall p : Prop, p -> p`");
    assert_eq!(
        env.get_const(&name).map(|c| c.kind),
        Some(ConstantKind::Theorem),
        "the checked path registers a Theorem"
    );

    // ARM B — the FLAG ALONE does not authorize the proof drop. Outside a
    // sanctioned two-pass scope the arm fails closed: `EnvError::AxiomOnlyMisuse`
    // in release, and a `debug_assert!` panic in a debug build. Either way nothing
    // is registered, which is the property that matters.
    let mut env = Environment::new();
    clean_kernel::set_mm_axiom_only(true);
    assert!(
        !clean_kernel::mm_two_pass_active(),
        "no guard is live, so the sentinel must be off"
    );
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let payload = info.payload();
        let quiet = payload
            .downcast_ref::<&str>()
            .is_some_and(|m| m.contains("mm_axiom_only proof-drop reached"))
            || payload
                .downcast_ref::<String>()
                .is_some_and(|m| m.contains("mm_axiom_only proof-drop reached"));
        if !quiet {
            previous_hook(info);
        }
    }));
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        env.add_decl(id_prop_theorem(false))
    }));
    let _ = std::panic::take_hook();
    match outcome {
        // Release build: fails closed with the dedicated error.
        Ok(Err(clean_kernel::EnvError::AxiomOnlyMisuse { .. })) => {}
        // Debug build: the `debug_assert!` fires first. Also fails closed.
        Err(_) if cfg!(debug_assertions) => {}
        other => panic!(
            "the axiom-only proof drop must fail closed without the two-pass sentinel; got {other:?}"
        ),
    }
    assert!(
        env.get_const(&name).is_none(),
        "a sentinel-less proof drop must register nothing"
    );
    clean_kernel::set_mm_axiom_only(false);

    // ARM C — flag + LIVE GUARD is exactly the pass-1 regime: the proof is dropped
    // unexamined and the TYPE is registered as an Axiom with no value. This is the
    // counted bypass, reproduced in isolation.
    let mut env = Environment::new();
    {
        let _guard = clean_kernel::MmAxiomOnlyGuard::enter();
        clean_kernel::set_mm_axiom_only(true);
        assert!(clean_kernel::mm_two_pass_active());
        env.add_decl(id_prop_theorem(false))
            .expect("inside the two-pass, a Theorem's proof is dropped and its type registered");
        let info = env
            .get_const(&name)
            .expect("pass 1 registers the schematic TYPE");
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "pass 1 must register an AXIOM, never a Theorem"
        );
        assert!(
            info.value.is_none(),
            "pass 1 must drop the proof value entirely — an unchecked proof must not \
             survive anywhere in the environment"
        );
    }

    // ARM D — the RAII guard clears the flag on drop, so the bypass cannot leak
    // into later checked work on this thread.
    assert!(
        !clean_kernel::mm_two_pass_active(),
        "sentinel must be clear"
    );
    assert!(
        !clean_kernel::mm_axiom_only(),
        "the guard must force the axiom-only flag off on drop"
    );
    let mut env = Environment::new();
    env.add_decl(id_prop_theorem(false))
        .expect_err("after the guard drops, the checked path must be back in force");
    assert!(env.get_const(&name).is_none());
}

// ---------------------------------------------------------------------------
// MECHANISM (2) — pass 1 never contributes a verdict
// ---------------------------------------------------------------------------

/// PASS-1 CONTAINMENT. Running the two-pass verifier with an EMPTY pass-2 range
/// executes pass 1 over the whole prefix and proof-checks nothing. It must produce
/// no verdict of any kind — not verified, not failed, not skipped — even on a
/// corpus containing a theorem the kernel rejects. The pass-1 axioms exist only
/// inside the importer's in-process `Environment`.
#[test]
fn test_pass1_alone_reports_no_verdict_at_all() {
    for src in [clean_corpus(), failed_dep_corpus(), cascade_corpus()] {
        let db = parse(&src);
        let n = provable_count(&db);
        let report =
            kernel_verify_two_pass_range(&db, 0..0, n).expect("pass-1-only run must succeed");
        assert!(
            report.verified.is_empty(),
            "pass 1 must never mark anything verified; got {:?}",
            report.verified
        );
        assert!(
            report.failed.is_empty(),
            "pass 1 must never mark anything failed; got {:?}",
            report.failed
        );
        assert!(
            report.skipped.is_empty(),
            "pass 1 must never mark anything skipped; got {:?}",
            report.skipped
        );
    }
}

/// The Mathverse export path (`mm_export_verified` → `kernel_verify_pass1_types`)
/// is a PASS-1-ONLY run. It must report no verdict, and its type sink must fire
/// only for labels the caller already had in the gated verified set — never for a
/// dependency registered merely to build a wanted type.
#[test]
fn test_pass1_type_export_never_reports_a_verdict() {
    let db = parse(&clean_corpus());
    let n = provable_count(&db);
    let wanted: hashbrown::HashSet<String> = ["th2".to_string()].into_iter().collect();
    let mut emitted: Vec<String> = Vec::new();
    let report = kernel_verify_pass1_types(&db, n, &wanted, &mut |label, kernel_name, _ty| {
        assert_eq!(kernel_name, format!("mm.{label}"));
        emitted.push(label.to_string());
    })
    .expect("pass-1 type export must run");
    assert!(
        report.verified.is_empty() && report.failed.is_empty() && report.skipped.is_empty(),
        "a type-only export is not a verification and must carry no verdict; got {report:?}"
    );
    assert_eq!(
        emitted,
        vec!["th2".to_string()],
        "the sink must fire only for wanted labels — `th1` is registered as a \
         dependency type but must not be exported"
    );
}

/// PASS-2 RE-VERIFICATION HAS TEETH. `bad` claims `|- t = 0` with a proof of
/// `|- t = t`. Its pass-1 registration cannot save it: no two-pass range — the
/// whole prefix, its own singleton range, or a range that excludes it — may ever
/// report it verified.
#[test]
fn test_a_rejected_proof_is_never_verified_by_any_two_pass_range() {
    let db = parse(&failed_dep_corpus());
    let n = provable_count(&db);
    for start in 0..n {
        for end in start..=n {
            let report = kernel_verify_two_pass_range(&db, start..end, n)
                .expect("two-pass verification must run");
            assert!(
                !report.verified.iter().any(|l| l == "bad"),
                "a kernel-rejected proof must never be verified (range {start}..{end}); \
                 got {:?}",
                report.verified
            );
        }
    }
    assert!(
        !two_pass_split_union(&db).contains("bad"),
        "and not in the union of the production split ranges either"
    );
    // …and its own verification, wherever it is attempted, is never recorded as a
    // ground-only success either — a rejected proof produces no verdict at all.
    for start in 0..n {
        for end in start..=n {
            let report = kernel_verify_two_pass_range(&db, start..end, n)
                .expect("two-pass verification must run");
            assert!(
                !report.ground_only.iter().any(|l| l == "bad"),
                "ground_only is a SUBSET of verified, so a rejected proof is absent \
                 from it too (range {start}..{end}); got {:?}",
                report.ground_only
            );
        }
    }
}

/// FAIL-CLOSED BEFORE THE GATE. A dependency whose PROOF TREE is malformed
/// (`broken`'s proof underflows the stack) never reaches registration at all:
/// pass 1 `continue`s on the `build_tree` error, so `broken` is absent from
/// `cache` and `apply_label` refuses to build any dependent. This is the one
/// divergence class the two-pass verifier closes WITHOUT the gate's help — worth
/// pinning, because it is why "pass 1 registers everything" is not literally true.
#[test]
fn test_a_dependency_with_a_malformed_proof_tree_is_never_registered_in_pass1() {
    let src = format!(
        "{DEMO0_DB}\
broken $p |- t = t $= weq $.
usebroken $p |- ( t + 0 ) = ( t + 0 ) $= tt tze tpl broken $.
"
    );
    let db = parse(&src);

    let seq_report = kernel_verify_database(&db).expect("sequential verification must run");
    assert!(
        seq_report.failed.iter().any(|(l, _)| l == "broken"),
        "PRECONDITION: broken's proof tree must not build; got {:?}",
        seq_report.failed
    );

    let raw = two_pass_split_union(&db);
    assert!(
        !raw.contains("usebroken"),
        "a dependent of an unregistered theorem must fail closed in the RAW two-pass \
         union, before the gate ever runs; got {raw:?}"
    );
    assert_eq!(gate(&db, &raw), sequential(&db));
}

// ---------------------------------------------------------------------------
// MECHANISM (3) — the dependency-closure gate
// ---------------------------------------------------------------------------

/// The gate is LOAD-BEARING, not decorative. In the production split-range
/// configuration the raw two-pass union reports `usebad` verified — a theorem the
/// sequential verifier refuses to even build, because it rests on the rejected
/// `bad`. The gate removes it and restores equality with the sequential set.
#[test]
fn test_gate_removes_the_dependent_of_a_failed_dependency() {
    let db = parse(&failed_dep_corpus());

    let seq = sequential(&db);
    assert_eq!(
        seq,
        BTreeSet::from(["th1".to_string()]),
        "sequential must verify th1, reject bad, and skip usebad"
    );

    let raw = two_pass_split_union(&db);
    assert!(
        raw.contains("usebad"),
        "PRECONDITION of the whole gate: the raw two-pass union DOES report a \
         theorem resting on an unproven dependency; got {raw:?}"
    );

    let gated = gate(&db, &raw);
    assert!(
        !gated.contains("usebad"),
        "the gate must remove a theorem whose $p-dependency did not verify"
    );
    assert_eq!(gated, seq, "two-pass + gate must equal sequential here");
}

/// The fixpoint really iterates: removing `mid` (rests on the rejected `bad`) must
/// then remove `top` (rests on `mid`).
#[test]
fn test_gate_cascades_transitively() {
    let db = parse(&cascade_corpus());

    let raw = two_pass_split_union(&db);
    assert!(
        raw.contains("mid") && raw.contains("top"),
        "PRECONDITION: the raw union must contain both levels; got {raw:?}"
    );

    let gated = gate(&db, &raw);
    assert!(
        !gated.contains("mid") && !gated.contains("top"),
        "the gate must cascade through both levels; got {gated:?}"
    );
    assert_eq!(gated, sequential(&db));
}

/// FAIL-CLOSED INTAKE. A label that is not a `$p` theorem of this database — a
/// stale entry, a hand-edited file, an `$a` axiom name — must not survive the
/// gate. (The gate's dependency map has no row for it, so a passthrough would let
/// it out of the gate entirely unexamined.)
#[test]
fn test_gate_drops_labels_that_are_not_provables_of_this_database() {
    let db = parse(&clean_corpus());
    let mut verified = two_pass_split_union(&db);
    // Marked REUSABLE deliberately: the intake filter must drop them on the
    // "not a `$p` of this database" rule alone, not incidentally via citability.
    verified.insert("a1", Reusability::Reusable); // a `$a` axiom, not a `$p`
    verified.insert("no-such-label", Reusability::Reusable);
    verified.insert("mp", Reusability::Reusable); // an `$a` under a `${ … $}` block

    let gated = gate(&db, &verified);
    assert!(
        !gated.contains("a1") && !gated.contains("mp") && !gated.contains("no-such-label"),
        "only `$p` theorems of this database may survive the gate; got {gated:?}"
    );
    assert_eq!(gated, sequential(&db));
}

/// The dependency map itself: `$p` citations are dependencies, `$a` axioms and
/// `$f`/`$e` hypotheses are the trusted/local base and are not.
#[test]
fn test_provable_dependencies_counts_only_provable_citations() {
    let db = parse(&clean_corpus());
    let resolved = resolve_database(&db).expect("resolve");
    let deps = provable_dependencies(&resolved);

    assert_eq!(
        deps.keys().cloned().collect::<Vec<_>>(),
        vec!["th1".to_string(), "th2".to_string()],
        "every `$p` of the database is a key, so every `$p` is recognised"
    );
    assert!(
        deps["th1"].is_empty(),
        "th1 cites only `$a` axioms and `$f` hypotheses, so it has no $p-dependency"
    );
    assert_eq!(
        deps["th2"],
        BTreeSet::from(["th1".to_string()]),
        "th2 cites th1 (plus `$a`/`$f` labels, which are not dependencies)"
    );
}

/// The label reader shared by `mm_gate` and the two-pass driver accepts the bare
/// and the `V <label>` forms and drops the headers — and, WITHOUT the
/// `VERIFIED_FORMAT 2` stamp, refuses to claim anything about reusability.
#[test]
fn test_verified_label_reader_accepts_both_emitted_forms() {
    let parsed = parse_verified_labels("VERIFIED_COUNT 2\nV th1\n\n  th2  \n");
    assert_eq!(
        parsed.labels(),
        BTreeSet::from(["th1".into(), "th2".into()])
    );
    assert_eq!(
        parsed.reusability("th1"),
        Some(Reusability::Unmarked),
        "an UNSTAMPED stream states no reusability — reading it as Reusable is the \
         R1-MM gap"
    );
    assert_eq!(parsed.unmarked_count(), 2);

    let stamped = parse_verified_labels(&format!(
        "{VERIFIED_FORMAT_HEADER}\nVERIFIED_COUNT 2\nV th1\nV th2\nG th2\n"
    ));
    assert_eq!(
        stamped.labels(),
        BTreeSet::from(["th1".into(), "th2".into()])
    );
    assert_eq!(stamped.reusability("th1"), Some(Reusability::Reusable));
    assert_eq!(stamped.reusability("th2"), Some(Reusability::GroundOnly));
    assert_eq!(stamped.unmarked_count(), 0);
    assert!(stamped.is_citable("th1") && !stamped.is_citable("th2"));
    assert!(
        !stamped.is_citable("no-such-label"),
        "citability of an absent label is FALSE, never a panic or a default-true"
    );
}

/// FAIL-CLOSED ON A STALE LABELS FILE. The wire format is additive — a v1 reader
/// still sees the identical `V ` lines — so the ONLY thing separating "this stream
/// states reusability" from "it does not" is the `VERIFIED_FORMAT 2` stamp. Drop
/// the stamp and every label must become NON-citable, which under-approximates the
/// export. The one reading that must never happen is "unmarked ⇒ reusable": that is
/// the R1-MM gap, silently reintroduced.
#[test]
fn test_unmarked_labels_file_fails_closed_instead_of_reading_as_reusable() {
    let db = parse(&clean_corpus());
    let seq = sequential(&db);
    assert_eq!(seq, BTreeSet::from(["th1".into(), "th2".into()]));

    let stamped = render_verified_labels(
        &kernel_verify_database(&db).expect("sequential verification must run"),
    );
    assert!(stamped.starts_with(VERIFIED_FORMAT_HEADER));
    assert_eq!(
        gate(&db, &parse_verified_labels(&stamped)),
        seq,
        "PRECONDITION: with the stamp, the clean corpus gates to the sequential set"
    );

    // The SAME bytes with the stamp removed — a labels file from a pre-R1-MM
    // `mm_verify_range`, or `mm_gate`'s own bare-label output re-fed to it.
    let unstamped: String = stamped
        .lines()
        .filter(|l| !l.starts_with("VERIFIED_FORMAT"))
        .map(|l| format!("{l}\n"))
        .collect();
    let parsed = parse_verified_labels(&unstamped);
    assert_eq!(parsed.unmarked_count(), 2, "both labels read as Unmarked");
    assert_eq!(
        gate(&db, &parsed),
        BTreeSet::from(["th1".to_string()]),
        "th2 cites th1, whose citability is unknown, so th2 is DROPPED — the \
         unstamped read under-approximates and never over-approximates"
    );
}

/// The ground-only marking must survive the exact bytes `mm_verify_range` writes
/// and `mm_gate` reads. If it did not, the fix would hold in-process and evaporate
/// at the file boundary — which is where the production pipeline lives.
#[test]
fn test_ground_only_marking_survives_the_wire_format_round_trip() {
    let db = parse(GROUND_FALLBACK_DB);
    let report = kernel_verify_database(&db).expect("sequential verification must run");
    assert_eq!(
        report.ground_only,
        vec!["gth".to_string()],
        "PRECONDITION: gth verifies only on the GROUND fallback"
    );

    let wire = render_verified_labels(&report);
    assert!(
        wire.contains("\nV gth\n") && wire.contains("\nG gth\n"),
        "a ground-only label gets BOTH a `V ` line (so a v1 `/^V /` reader sees it) \
         and a `G ` line (so a v2 reader knows it is not citable); got:\n{wire}"
    );
    let parsed = parse_verified_labels(&wire);
    assert_eq!(parsed.reusability("gth"), Some(Reusability::GroundOnly));
    assert_eq!(
        parsed,
        VerifiedLabels::from_report(&report),
        "the wire round-trip must be lossless against the in-process form"
    );

    // UNION SEMANTICS: `G` is sticky. A second worker that reports the same label
    // as reusable must not be able to upgrade it.
    let mut union = parsed.clone();
    union.merge(&all_reusable(["gth"]));
    assert_eq!(
        union.reusability("gth"),
        Some(Reusability::GroundOnly),
        "the least-citable verdict wins, in either merge order"
    );
    let mut other_order = all_reusable(["gth"]);
    other_order.merge(&parsed);
    assert_eq!(
        other_order.reusability("gth"),
        Some(Reusability::GroundOnly)
    );
}

/// THE UNION LAW, on every ordered pair. `VerifiedLabels::insert` unions by `max`
/// over `Reusability`'s DERIVED `Ord`, so the whole fail-closed property rests on
/// the variants staying in increasing-severity declaration order. Reordering them
/// would make the union permissive and silently re-open R1-MM — and nothing else
/// in this suite would necessarily go red, because the corpora produce at most one
/// verdict per label. So pin the law directly.
#[test]
fn test_verified_label_union_always_keeps_the_least_citable_verdict() {
    use Reusability::{GroundOnly, Reusable, Unmarked};
    let severity = [Reusable, GroundOnly, Unmarked];
    for (i, &a) in severity.iter().enumerate() {
        for (j, &b) in severity.iter().enumerate() {
            let expected = severity[i.max(j)];
            let mut ab = VerifiedLabels::new();
            ab.insert("l", a);
            ab.insert("l", b);
            assert_eq!(
                ab.reusability("l"),
                Some(expected),
                "insert({a:?}) then insert({b:?}) must settle on the least citable"
            );
            let mut ba = VerifiedLabels::new();
            ba.insert("l", b);
            ba.insert("l", a);
            assert_eq!(
                ba.reusability("l"),
                Some(expected),
                "…and the union must be order-independent ({b:?} then {a:?})"
            );
        }
    }
    assert!(
        Reusable.is_citable() && !GroundOnly.is_citable() && !Unmarked.is_citable(),
        "only a schematically-verified dependency may be cited"
    );
}

/// THE R1-MM RULE, in isolation from the verifier. A ground-only dependency
/// SURVIVES the gate (the sequential verifier verifies it too) but nothing may
/// CITE it, and the removal cascades like any other.
#[test]
fn test_gate_drops_the_dependent_of_a_ground_only_dependency() {
    let db = parse(&cascade_corpus());

    // `bad`/`mid`/`top` used only for their citation shape here: pretend all three
    // verified, with `bad` ground-only. `mid` cites `bad`, `top` cites `mid`.
    let mut verified = all_reusable(["th1", "bad", "mid", "top"]);
    verified.insert("bad", Reusability::GroundOnly);

    let gated = gate(&db, &verified);
    assert_eq!(
        gated,
        BTreeSet::from(["th1".to_string(), "bad".to_string()]),
        "the ground-only theorem itself survives (it verified); its dependent `mid` \
         is dropped for citing it, and `top` cascades"
    );
}

// ---------------------------------------------------------------------------
// COUNT EQUIVALENCE — where it holds
// ---------------------------------------------------------------------------

/// Clean corpus, both configurations: full-range (the configuration the original
/// count-equivalence check used) and the production split ranges.
#[test]
fn test_split_range_two_pass_plus_gate_equals_sequential_clean_corpus() {
    let db = parse(&clean_corpus());
    let seq = sequential(&db);
    assert_eq!(
        seq,
        BTreeSet::from(["th1".to_string(), "th2".to_string()]),
        "PRECONDITION: the clean corpus verifies end to end"
    );

    assert_eq!(
        gate(&db, &two_pass_full_range(&db)),
        seq,
        "full-range two-pass + gate must equal sequential"
    );
    assert_eq!(
        gate(&db, &two_pass_split_union(&db)),
        seq,
        "split-range two-pass + gate must equal sequential"
    );
}

/// Adversarial corpora, production split-range configuration.
///
/// `GROUND_FALLBACK_DB` joined this list when R1-MM's gap closed: it is the corpus
/// whose divergence the `verified`-only predicate could not see, and the whole
/// point of the reusability marking is that it now belongs here beside the
/// failed-dependency corpora.
#[test]
fn test_split_range_two_pass_plus_gate_equals_sequential_adversarial_corpora() {
    for src in [
        failed_dep_corpus(),
        cascade_corpus(),
        GROUND_FALLBACK_DB.to_string(),
    ] {
        let db = parse(&src);
        assert_eq!(
            gate(&db, &two_pass_split_union(&db)),
            sequential(&db),
            "two-pass + gate must equal sequential on {src}"
        );
        assert_eq!(
            gate(&db, &two_pass_full_range(&db)),
            sequential(&db),
            "…and in the full-range configuration too, on {src}"
        );
    }
}

// ---------------------------------------------------------------------------
// COUNT EQUIVALENCE — the corpus where it used NOT to hold (the R1-MM finding)
// ---------------------------------------------------------------------------

/// THE INVERTED CHARACTERIZATION TEST (was
/// `test_ground_fallback_dep_divergence_survives_the_gate_known_gap`, whose doc
/// required it to be INVERTED rather than deleted when the gap closed).
///
/// `gth` applies the `$d x ph`-bearing `ax5` but declares no `$d` of its own, so
/// the schematic-`$d` route cannot discharge the guard and the verifier falls back
/// to the GROUND shape. A ground theorem is NOT reusable: the sequential verifier
/// leaves it out of its `cache`, so `build_tree` refuses to reuse it and `usegth`
/// is SKIPPED (`crates/clean-olean/src/metamath/kernel_verify.rs`, `apply_label`:
/// "unsupported: proof of … reuses $p theorem … that did not verify").
///
/// The two-pass verifier still does not reproduce that ON ITS OWN, and this test
/// asserts that it does not: PASS 1 registers `gth`'s LIGHT SCHEMATIC type as an
/// unchecked axiom and puts `gth` in `cache`/`sigs` unconditionally, so in any
/// worker whose pass-2 range excludes `gth` — every worker but one, in the
/// production split — `usegth` proof-checks against that pass-1 type and is
/// reported verified. What changed is the GATE: pass 2 now records that `gth`
/// verified only on the GROUND path (`report.ground_only`), `mm_verify_range`
/// emits it (`G gth`), and the gate drops every theorem citing a non-citable
/// dependency. So the exported set is the sequential one again.
///
/// The four assertions below are deliberately redundant, because equality alone
/// could be satisfied vacuously (e.g. if `usegth` stopped being verified at all,
/// or if `gth` were also dropped). They pin, in order: the sequential reference
/// and its REASON; that the raw union is still permissive (so the gate is still
/// load-bearing here); that the ground-only theorem itself SURVIVES; and equality.
///
/// The corpus is deliberately minimal and is itself Metamath-INVALID (`gth`
/// omits the `$d x ph` that its `ax5` step requires — that Clean's ground path
/// accepts it at all is a SEPARATE question, not this issue's). What it pins is
/// the two-pass mechanism, which is corpus-independent.
#[test]
fn test_ground_fallback_dep_no_longer_diverges_from_sequential() {
    let db = parse(GROUND_FALLBACK_DB);

    // (1) The sequential verifier accepts `gth` but SKIPS `usegth`, naming `gth` as
    // a theorem it may not reuse — the signature of a ground-only verification.
    let seq_report = kernel_verify_database(&db).expect("sequential verification must run");
    let seq = labels(&seq_report);
    assert_eq!(
        seq,
        BTreeSet::from(["gth".to_string()]),
        "PRECONDITION: sequential verifies gth and does not verify usegth"
    );
    assert!(
        seq_report
            .skipped
            .iter()
            .any(|(l, why)| l == "usegth" && why.contains("reuses $p theorem gth")),
        "PRECONDITION: usegth is skipped BECAUSE gth is not reusable; got {:?}",
        seq_report.skipped
    );

    // (2) The gate is still LOAD-BEARING here: the RAW split-range union still
    // reports both labels, exactly as it did when this was a known gap.
    let raw = two_pass_split_union(&db);
    assert!(
        raw.contains("gth") && raw.contains("usegth"),
        "PRECONDITION of the whole fix: the raw two-pass union still reports the \
         dependent of a ground-only dependency; got {raw:?}"
    );
    assert_eq!(
        raw.reusability("gth"),
        Some(Reusability::GroundOnly),
        "and the union carries WHY gth may not be cited — the fact the old gate \
         did not have; got {raw:?}"
    );

    // (3) The ground-only theorem itself is NOT collateral damage: it verified, the
    // sequential verifier verifies it too, and it must still export.
    let gated = gate(&db, &raw);
    assert!(
        gated.contains("gth"),
        "the ground-only dependency itself must survive — it is verified, it is \
         merely not citable; got {gated:?}"
    );
    assert!(
        !gated.contains("usegth"),
        "CLOSED: the gate must remove a dependent that rests on a ground-fallback \
         dependency's PASS-1 schematic type; got {gated:?}"
    );

    // (4) The inversion itself: equality, where this test used to assert `⊋`.
    assert_eq!(
        gated, seq,
        "two-pass + gate must now EQUAL the sequential set on the corpus that used \
         to be the R1-MM known gap"
    );
}

/// The EXPOSURE MEASUREMENT itself, mechanized. `ground_reuse_exposure` is the
/// harness `mm_kverify --exposure` runs over a real set.mm prefix to answer "does
/// the shipped export actually contain such a case?" — a question no box without
/// the corpus can answer. What CAN be pinned here is that the harness detects the
/// shape when it is present and stays silent when it is not, so the number it
/// reports on a corpus-bearing box is a measurement and not an artifact of a
/// detector that always says yes (or always says no).
#[test]
fn test_exposure_detector_finds_the_ground_only_reuse_and_only_that() {
    let ground = kernel_verify_database(&parse(GROUND_FALLBACK_DB))
        .expect("sequential verification must run");
    assert_eq!(
        ground_reuse_exposure(&ground),
        vec![("usegth".to_string(), "gth".to_string())],
        "EXPOSED: usegth is skipped for citing gth, and gth IS verified"
    );

    // A skip whose named dependency did NOT verify is the ORDINARY fail-closed
    // case the gate has always handled — it must not be reported as exposure.
    let failed = kernel_verify_database(&parse(&failed_dep_corpus()))
        .expect("sequential verification must run");
    assert!(
        failed
            .skipped
            .iter()
            .any(|(l, why)| l == "usebad" && why.contains("reuses $p theorem bad")),
        "PRECONDITION: usebad is skipped naming bad; got {:?}",
        failed.skipped
    );
    assert!(
        ground_reuse_exposure(&failed).is_empty(),
        "`bad` did not verify, so `usebad` is not R1-MM exposure; got {:?}",
        ground_reuse_exposure(&failed)
    );

    // A corpus with nothing to skip reports nothing.
    let clean =
        kernel_verify_database(&parse(&clean_corpus())).expect("sequential verification must run");
    assert!(ground_reuse_exposure(&clean).is_empty());
}
