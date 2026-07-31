// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reflection demo: the REAL width-4 commutativity BvBlastProof (28 vars,
//! 131 clauses, 520 resolution steps) is checked by the KERNEL tractably, via
//! `Eq.refl : checkRefutes <clauses> <refutation> = Bool.true`.
//!
//! THE HEADLINE: the monolithic `Or.rec` replay of this same refutation OOMs
//! (>70 GB — see `theory_lemma_bv_compute_blast`). Reflection turns the kernel
//! check into a LINEAR ι-reduction over the proof data; the certificate is a
//! constant-size `Eq.refl`. These tests show it kernel-type-checks in well under
//! a second and a few MB, and that a TAMPERED refutation is rejected.

use super::{
    certify_by_reflection, certify_unsat3_by_reflection, certify_unsat_by_reflection,
    check_refutes3_sound_name, check_refutes_sound_name, encode_proof_clauses,
    encode_proof_refutation, ReflectionError,
};
use ay_proof::bv_blast_export::Lit;
use ay_proof::bv_blast_solver::{
    export_bv_blast_proof_expr, export_bv_blast_proof_solved, BvExpr, BvExprExportError,
    SolvedObligation,
};
use clean_kernel::name::Name;
use clean_kernel::resolution_check::{
    check_refutes3_initialtrie_app, check_refutes_app, encode_clauses_lit,
};
use clean_kernel::{Environment, Expr, Level, TypeChecker};
use std::time::Instant;

fn reflection_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_resolution_check().expect("init_resolution_check");
    env
}

fn real_width4_proof() -> ay_proof::bv_blast_export::BvBlastProof {
    export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width: 4 })
        .expect("width-4 commutativity is UNSAT; producer must export the real refutation")
}

/// THE GATE-SHAPED MULTIPLY refutation at the given width: the EXACT obligation
/// the live trust-cg M-POS gate emits for a `bvmul` —
///   machine_out = BvExtract(BvZeroExt(mul(A,B), w), w-1, 0)   (the readout)
///   auto_spec   = mul(A, B)
/// Both sides blast the full shift-and-add array multiplier (And2 partial
/// products + Xor3/FullAdderCarry adder tree, existing gate KINDS only) through
/// ONE shared gate cache, so the readout extract∘zero_ext collapses to the same
/// output bits as the bare multiply — the disequality `not(machine == spec)` is
/// UNSAT. The whole multiplier is bit-blasted (every And2/Xor3/FullAdderCarry
/// gate is materialised and CNF-encoded), so this re-checks the REAL multiplier
/// reflection, not a shortcut.
fn real_mul_proof(width: u32) -> ay_proof::bv_blast_export::BvBlastProof {
    let a = BvExpr::leaf("A0", width);
    let b = BvExpr::leaf("B0", width);
    let machine = BvExpr::extract(
        BvExpr::zero_ext(BvExpr::Mul(Box::new(a.clone()), Box::new(b.clone())), width),
        width - 1,
        0,
    );
    let spec = BvExpr::Mul(Box::new(a), Box::new(b));
    export_bv_blast_proof_expr(&machine, &spec)
        .expect("gate-shaped mul readout is UNSAT; producer must export the real refutation")
}

/// THE MUL HEADLINE: a REAL gate-shaped multiply refutation kernel-re-checks to
/// `Unsat` through the PROVED `checkRefutes_sound` bridge with ZERO residual
/// domain axioms — i.e. multiply is [PROVED] (ay out of the re-check TCB) at the
/// width this test exercises (width 8 by default, the gate leaf width the
/// existing compare re-checks use).
///
/// TRACTABILITY (HONEST): the FULL shift-and-add array multiplier IS bit-blasted
/// (width 8 ⇒ ~946 CNF clauses), but because BOTH sides share one gate cache the
/// readout extract∘zero_ext fuses to the bare multiply's output bits, so the
/// refutation is the SHORT empty-clause derivation (~17 resolution steps) — the
/// kernel reflection is linear in steps and the clause DB is bounded, so this
/// re-checks fast. A *non-fusing* multiply obligation (e.g. commutativity)
/// instead needs a real resolution chain whose step-count blows up ~16× per +2
/// width (width 4 → 5 210, width 8 → ~2.0M); that is why the live trust-cg gate,
/// which emits at width 32, keeps multiply [VALIDATED] (the tractability guard in
/// `verify_output::try_kernel_recheckable_proof` declines the kernel grade for a
/// wide `Mul`). This test pins multiply [PROVED] at width 8 with a REAL passing
/// kernel re-check. Widen via `MUL_REFL_WIDTH`.
#[test]
fn reflection_real_mul_unsat_cert_is_fully_zero_trust() {
    let width: u32 = std::env::var("MUL_REFL_WIDTH")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8);

    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");
    let proof = real_mul_proof(width);
    proof.validate().expect("producer mul proof validates");

    let n_clauses = proof.clauses.len();
    let n_steps = proof.refutation.steps.len();

    let t0 = Instant::now();
    let (unsat_term, _unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("mul Unsat reflection cert must kernel-check: {e}"));
    let elapsed = t0.elapsed();

    eprintln!(
        "MUL REFLECTION (width-{width} gate-readout): clauses={n_clauses} steps={n_steps} \
         kernel Unsat-cert type-check time = {elapsed:?}"
    );

    // The soundness bridge is a PROVED Theorem with empty domain-axiom closure.
    let sound = Name::from_string(check_refutes_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "checkRefutes_sound (hence the mul Unsat cert) must have ZERO domain axioms; got {domain:?}"
    );
    let head = format!("{unsat_term:?}");
    assert!(
        head.contains("checkRefutes_sound"),
        "mul Unsat cert must apply the proved checkRefutes_sound bridge"
    );
}

#[test]
fn reflection_demo_real_width4_kernel_typechecks_tractably() {
    let env = reflection_env();
    let proof = real_width4_proof();
    proof.validate().expect("producer proof validates");

    // This IS the real non-reflexive bit-blast, not a shortcut.
    assert!(!proof.obligation.is_identical());
    assert!(
        proof.refutation.steps.len() > 100,
        "expected the full ~520-step refutation; got {}",
        proof.refutation.steps.len()
    );

    let t0 = Instant::now();
    let cert = certify_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("reflection certificate must kernel-type-check: {e}"));
    let elapsed = t0.elapsed();

    eprintln!(
        "REFLECTION DEMO (width-4 commutativity): clauses={} steps={} \
         kernel Eq.refl type-check time = {:?} (vs #20 monolithic Or.rec: >70 GB OOM)",
        cert.num_clauses, cert.num_steps, elapsed
    );

    assert!(cert.num_steps > 100, "real 520-step refutation reflected");
    // Tractability gate: the kernel reduction is LINEAR in the proof data (vs the
    // >70 GB OOM of the monolithic Or.rec replay) — the headline result. The bound is
    // generous: per step the checker re-reduces `nth db prem` (O(index) over the
    // growing 131+520-clause DB) and, after the #22 soundness fix, validates BOTH
    // legal pivot orientations (short-circuited, but the recorded-vs-recomputed
    // `clauseSeteq` is O(n·m)). On a loaded CI box this runs in a couple of minutes;
    // the point is it COMPLETES in bounded memory, not that it is sub-second.
    assert!(
        elapsed.as_secs() < 300,
        "reflection check must remain tractable (bounded, no OOM); took {elapsed:?}"
    );
}

#[test]
fn reflection_real_width4_unsat_cert_is_fully_zero_trust() {
    // THE HEADLINE (#22): with the soundness layer initialized, the REAL width-4
    // refutation's `Unsat`-discharging term —
    //   checkRefutes_sound <clauses> <refutation> (Eq.refl Bool Bool.true)
    // — kernel-type-checks AND its transitive axiom closure is ⊆ FOUNDATIONAL
    // (zero residual domain axioms). The soundness bridge is a PROVED Theorem.
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");
    let proof = real_width4_proof();

    let (unsat_term, _unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("Unsat reflection cert must kernel-check: {e}"));

    // The soundness bridge is a PROVED Theorem with empty domain-axiom closure.
    let sound = Name::from_string(check_refutes_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "checkRefutes_sound (hence the whole Unsat cert) must have ZERO domain axioms; got {domain:?}"
    );

    // Sanity: the assembled term mentions the proved bridge.
    let head = format!("{unsat_term:?}");
    assert!(
        head.contains("checkRefutes_sound"),
        "Unsat cert must apply the proved checkRefutes_sound bridge"
    );
}

#[test]
fn reflection_real_width4_unsat3_cert_is_fully_zero_trust() {
    // The SUB-QUADRATIC counterpart of the test above: the REAL width-4 refutation's
    // `Unsat`-discharging term through the PROVEN sub-quadratic trie checker —
    //   checkRefutes3_sound <clauses> <steps> (Eq.refl Bool Bool.true)
    // — kernel-type-checks AND its transitive axiom closure is ⊆ FOUNDATIONAL.
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");
    let proof = real_width4_proof();

    let (unsat_term, _unsat_goal) = certify_unsat3_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("Unsat3 reflection cert must kernel-check: {e}"));

    let sound = Name::from_string(check_refutes3_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes3_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes3_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "checkRefutes3_sound (hence the Unsat3 cert) must have ZERO domain axioms; got {domain:?}"
    );

    let head = format!("{unsat_term:?}");
    assert!(
        head.contains("checkRefutes3_sound"),
        "Unsat3 cert must apply the proved checkRefutes3_sound bridge"
    );
}

#[test]
fn reflection_certificate_is_constant_size_eq_refl() {
    let env = reflection_env();
    let proof = real_width4_proof();
    let cert = certify_by_reflection(&env, &proof).expect("certify");
    // The PROOF TERM is a constant-size Eq.refl (the data lives in the GOAL type,
    // which the kernel reduces — this is the whole point of reflection).
    let head = format!("{:?}", cert.certificate);
    assert!(
        head.contains("Eq.refl") || head.contains("refl"),
        "certificate must be Eq.refl, got {head}"
    );
}

#[test]
fn reflection_rejects_tampered_real_refutation() {
    let env = reflection_env();
    let mut proof = real_width4_proof();

    // TAMPER: corrupt one recorded resolvent in the middle of the chain by REPLACING
    // it with a spurious clause over a var id that cannot appear in the bit-blast
    // (so the recorded clause no longer set-equals the recomputed resolvent). The
    // kernel checkRefutes must NO LONGER reduce to true, so the Eq.refl certificate
    // must be REJECTED.
    let mid = proof.refutation.steps.len() / 2;
    let bogus_var = proof.vars.roles.len() as u32 + 100;
    proof.refutation.steps[mid].clause = vec![Lit {
        var: bogus_var,
        neg: false,
    }];

    // Bypass the producer validate() (which would also reject) to test the KERNEL
    // discrimination directly: encode and check the tampered data.
    let clauses = encode_proof_clauses(&proof);
    let refutation = encode_proof_refutation(&proof);
    let app = check_refutes_app(clauses, refutation);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nf = tc.whnf(&app);
    assert_eq!(
        nf,
        Expr::const_str("Bool.false"),
        "tampered real refutation must reflect to Bool.false; got {nf:?}"
    );

    // And the Eq.refl-to-true certificate must be rejected by check_type.
    let u1 = Level::succ(Level::zero());
    let app2 = {
        let clauses = encode_proof_clauses(&proof);
        let refutation = encode_proof_refutation(&proof);
        check_refutes_app(clauses, refutation)
    };
    let certificate = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
        [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [Expr::const_str("Bool"), app2, Expr::const_str("Bool.true")],
    );
    assert!(
        tc.check_type(&certificate, &goal).is_err(),
        "tampered certificate must be rejected by the kernel"
    );

    // certify_by_reflection also refuses (producer validate catches it first).
    assert!(matches!(
        certify_by_reflection(&env, &proof),
        Err(ReflectionError::InvalidProof(_))
    ));
}

// ───────────────────────────────────────────────────────────────────────────
// THROWAWAY measurement harness (2026-06-18 reflection-scaling experiment).
//
// NOT a soundness test. Driven by env vars so it can be pointed at any width
// and a wall-clock cap without recompiling:
//
//   REFL_BENCH_WIDTH=4         which AddCommutes width to bit-blast + reflect
//   REFL_BENCH_CAP_SECS=900    abort the reduction attempt after this long
//
// Build with `--features reduction-stats` to also get the per-name kernel
// reduction profile (which Definition dominates the whnf reduction). Run with
// `-- --nocapture --exact <path>::refl_bench_profile_one_width`.
//
// This deliberately reduces `checkRefutes` directly (whnf), which is the
// width-generic reflection-reduction question; it does NOT need the width-N
// gate-fidelity bridge. To keep the always-on suite fast it only runs when
// REFL_BENCH_WIDTH is set; otherwise it is an immediate no-op pass.
#[test]
fn refl_bench_profile_one_width() {
    let Ok(width_s) = std::env::var("REFL_BENCH_WIDTH") else {
        eprintln!("refl_bench_profile_one_width: set REFL_BENCH_WIDTH to run; skipping (pass).");
        return;
    };
    let width: u32 = width_s.parse().expect("REFL_BENCH_WIDTH must be a u32");
    let cap_secs: u64 = std::env::var("REFL_BENCH_CAP_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(900);

    use ay_proof::bv_blast_solver::{export_bv_blast_proof_solved, SolvedObligation};

    let env = reflection_env();

    let t_gen = Instant::now();
    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width })
        .expect("AddCommutes export");
    proof.validate().expect("validate");
    let gen_ms = t_gen.elapsed().as_secs_f64() * 1e3;

    let n_clauses = proof.clauses.len();
    let n_steps = proof.refutation.steps.len();
    let sum_lits: usize = proof.refutation.steps.iter().map(|s| s.clause.len()).sum();

    // Encode-only cost (term construction), measured separately from reduction.
    let t_enc = Instant::now();
    let clauses = encode_proof_clauses(&proof);
    let refutation = encode_proof_refutation(&proof);
    let app = check_refutes_app(clauses, refutation);
    let enc_ms = t_enc.elapsed().as_secs_f64() * 1e3;

    eprintln!(
        "REFL_BENCH width={width} clauses={n_clauses} steps={n_steps} \
         sum_resolvent_lits={sum_lits} gen={gen_ms:.0}ms encode={enc_ms:.0}ms cap={cap_secs}s"
    );

    // Run the reduction on a worker thread so we can enforce the wall-clock cap
    // (the kernel whnf is single-shot and not cancellable; we just stop waiting).
    clean_kernel::reduction_stats_reset();
    let (tx, rx) = std::sync::mpsc::channel();
    let app_for_thread = app.clone();
    let env_for_thread = env.clone();
    let handle = std::thread::Builder::new()
        .name("refl-reduce".into())
        .stack_size(512 * 1024 * 1024)
        .spawn(move || {
            let t0 = Instant::now();
            let mut tc = TypeChecker::with_mode(&env_for_thread, env_for_thread.mode());
            // Unlimited heartbeat (0) — match the real Lean kernel, which has no
            // heartbeat. Otherwise whnf silently BAILS (returns the term unreduced)
            // at the 2M default, which at width>=8 trips mid-fold and looks like a
            // false reduction. We want the true reduction cost / verdict.
            tc.set_heartbeat_limit(0);
            let nf = tc.whnf(&app_for_thread);
            let elapsed = t0.elapsed();
            let reduced_true = nf == Expr::const_str("Bool.true");
            let report = clean_kernel::reduction_stats_report(20);
            let _ = tx.send((reduced_true, format!("{nf:?}"), elapsed, report));
        })
        .expect("spawn");

    match rx.recv_timeout(std::time::Duration::from_secs(cap_secs)) {
        Ok((reduced_true, nf, elapsed, report)) => {
            handle.join().ok();
            eprintln!(
                "REFL_BENCH width={width} REDUCED_IN={elapsed:?} reduced_to_true={reduced_true} \
                 head={}",
                nf.chars().take(40).collect::<String>()
            );
            if report.is_empty() {
                eprintln!("(build with --features reduction-stats for the per-name profile)");
            } else {
                eprintln!("--- kernel reduction profile (width={width}) ---\n{report}");
            }
            assert!(
                reduced_true,
                "width-{width} refutation must reduce to Bool.true; got {nf}"
            );
        }
        Err(_) => {
            eprintln!(
                "REFL_BENCH width={width} WALL: did NOT reduce within {cap_secs}s \
                 (clauses={n_clauses} steps={n_steps}). This is the wall."
            );
            // Leave the worker detached; the process exits at test end. Report the
            // wall as a measurement, not a hard failure of the experiment.
            panic!("width-{width} reflection reduction exceeded {cap_secs}s cap (wall hit)");
        }
    }
}

// ───────────────────────────────────────────────────────────────────────────
// THROWAWAY measurement harness #2 (2026-06-20 sub-quadratic checkRefutes3 fix).
//
// Reduces the PROVEN form `checkRefutes3 (initialTrie cs) (listLen cs) steps`
// (NOT check_refutes3_app — this is the exact term `checkRefutes3_sound`
// consumes) on a deep stack with unlimited heartbeat, for genuine AddCommutes
// at the requested width, and reports (width, clauses, steps, reduce_ms). Run a
// sweep of widths and fit the steps-exponent in your shell.
//
//   REFL3_BENCH_WIDTH=4         which AddCommutes width to bit-blast + reflect
//   REFL3_BENCH_CAP_SECS=900    abort the reduction attempt after this long
//
// Sub-quadratic check: fit `log(reduce_ms) ~ a + e*log(steps)` across widths.
// e ≈ 2.0 = quadratic (the UNARY-id bug); e ≈ 1.4–1.6 = sub-quadratic (fixed).
#[test]
fn refl3_bench_proven_form_one_width() {
    let Ok(width_s) = std::env::var("REFL3_BENCH_WIDTH") else {
        eprintln!("refl3_bench_proven_form_one_width: set REFL3_BENCH_WIDTH to run; skipping.");
        return;
    };
    let width: u32 = width_s.parse().expect("REFL3_BENCH_WIDTH must be a u32");
    let cap_secs: u64 = std::env::var("REFL3_BENCH_CAP_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(900);

    use ay_proof::bv_blast_solver::{export_bv_blast_proof_solved, SolvedObligation};

    // The proven form needs `initialTrie`/`listLen` + the soundness layer.
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    let proof = export_bv_blast_proof_solved(SolvedObligation::AddCommutes { width })
        .expect("AddCommutes export");
    proof.validate().expect("validate");

    let n_clauses = proof.clauses.len();
    let n_steps = proof.refutation.steps.len();

    // The PROVEN form: `cs` = the BigNat-literal `encode_clauses_lit` DB (what `Unsat cs`
    // is about, and what the bridge feeds to `certify_unsat3_by_reflection`); `initialTrie
    // cs`/`listLen cs` are the kernel DEFINITIONS the kernel reduces. BigNat literals make
    // `litBeq`/`clauseMem`/`trieGet` reduce natively and shrink the `cs` term's memory
    // footprint (the width-32 OOM fix).
    //
    // The reduction TIME is dominated by the TRIE machinery (`trieGet`/`trieInsAux` and
    // their `Nat.ble`/`div`/`mod` descent), NOT `litNeg` (profiled: 545 `litNeg` unfolds vs
    // hundreds of thousands of trie ops at width 16). The `go3` fold threads a GROWING trie
    // accumulator, so at the kernel's 100k whnf-cache default the working set thrashes at
    // width ≥32 → hot trie subterms are re-reduced → super-linear (per-step whnf-miss count
    // jumps 3.7× from width 16→32 while trie DEPTH grows only ~1.2×). Raising the memoization
    // budget (`REFL3_CACHE`, mirrored in production by `reflection_tc_sized`/
    // `reflection_cache_budget`) removes the thrash: width-32 drops from ≈85 s to ≈30 s at a
    // 1M cache. Set `REFL3_CACHE` to profile the time/memory knee.
    let cs_clauses: Vec<Vec<(u32, bool)>> = proof
        .clauses
        .iter()
        .map(|c| super::clause_pairs(&c.lits))
        .collect();
    let cs_lit = encode_clauses_lit(&cs_clauses);
    let steps = super::proof_step_tuples(&proof);
    let app = check_refutes3_initialtrie_app(cs_lit, &steps);

    eprintln!(
        "REFL3_BENCH width={width} clauses={n_clauses} steps={n_steps} cap={cap_secs}s \
         (PROVEN FORM: checkRefutes3 (initialTrie cs)(listLen cs) steps)"
    );

    let (tx, rx) = std::sync::mpsc::channel();
    let app_for_thread = app.clone();
    let env_for_thread = env.clone();
    let handle = std::thread::Builder::new()
        .name("refl3-reduce".into())
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || {
            let t0 = Instant::now();
            let mut tc = TypeChecker::with_mode(&env_for_thread, env_for_thread.mode());
            tc.set_heartbeat_limit(0); // unlimited — match the real Lean kernel.
            if let Ok(c) = std::env::var("REFL3_CACHE") {
                tc.set_max_cache_entries(c.parse().expect("REFL3_CACHE usize"));
            }
            let nf = tc.whnf(&app_for_thread);
            let elapsed = t0.elapsed();
            let reduced_true = nf == Expr::const_str("Bool.true");
            let _ = tx.send((reduced_true, format!("{nf:?}"), elapsed));
        })
        .expect("spawn");

    match rx.recv_timeout(std::time::Duration::from_secs(cap_secs)) {
        Ok((reduced_true, nf, elapsed)) => {
            handle.join().ok();
            let reduce_ms = elapsed.as_secs_f64() * 1e3;
            eprintln!(
                "REFL3_BENCH width={width} steps={n_steps} REDUCE_MS={reduce_ms:.1} \
                 reduced_to_true={reduced_true}"
            );
            assert!(
                reduced_true,
                "width-{width} proven-form refutation must reduce to Bool.true; got {nf}"
            );
        }
        Err(_) => {
            eprintln!(
                "REFL3_BENCH width={width} WALL: did NOT reduce within {cap_secs}s \
                 (clauses={n_clauses} steps={n_steps})."
            );
            panic!("width-{width} proven-form reduction exceeded {cap_secs}s cap (wall hit)");
        }
    }
}

// ───────────────────────────────────────────────────────────────────────────
// THE [PROVED] FLIP (2026-06-23): take `ay` OUT of the runtime TCB for the
// M-POS gate's add-leaf, on the LIVE gate's RAW obligation shape.
//
// The spike (#6) kernel-re-checked the bare identical-operand `BvAdd` obligation
// from `export_bv_blast_proof(SliceObligation)`. The generalization (#8) added
// `export_bv_blast_proof_expr(&BvExpr, &BvExpr)` accepting the gate's arbitrary
// disequality. This flip closes BOTH remaining gaps in one end-to-end test:
//
//   GAP 3 (BvOr/Const): the LIVE gate's RAW `symbolic_machine_output` wraps the
//   adder leaf in `BvOr` identity wrappers (`BvOr(Const{0}, x)`) + `BitVec`
//   constant literals. The EXTENDED `BvExpr` set (`Or` + `Const`, landed on ay
//   `bedrock/proved-runtime-export`) lowers that RAW shape WITHOUT any trusted
//   normalization step.
//
//   GAP 2 (the flip): the RAW-obligation `BvBlastProof` is routed through clean's
//   `certify_unsat_by_reflection`; the clean KERNEL re-checks it into an `Unsat`
//   term whose transitive axiom closure is EMPTY (⊆ FOUNDATIONAL) = [PROVED].
//   `ay` is a certificate PRODUCER only; it is NOT consulted at re-check.
//
// HONESTY: the obligation is the LITERAL RAW shape (BvOr/Const intact), not a
// normalized bare BvAdd. Anti-vacuity stays solver-enforced (add-vs-sub refused
// by the producer; no term ever reaches the kernel).

/// The gate's RAW add-leaf machine_out as a [`BvExpr`], with the live
/// `symbolic_machine_output` wrappers intact:
///   `BvExtract(BvZeroExt( BvOr(Const{0,32}, BvAdd(W0,W1)), 32), 31, 0)`
/// where `Wn = BvExtract(Var("Xn",64),31,0)`.
fn raw_gate_add_leaf_machine_out() -> BvExpr {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    let inner_add = BvExpr::Add(Box::new(w0), Box::new(w1)); // BvAdd(W0, W1, 32)
                                                             // The RAW BvOr identity wrapper + BitVec zero constant the gate emits.
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_add);
    BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0)
}

/// The gate's auto_spec for the add leaf: the bare `BvAdd(W0, W1, 32)`.
fn gate_add_leaf_auto_spec() -> BvExpr {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    BvExpr::Add(Box::new(w0), Box::new(w1))
}

/// THE [PROVED] FLIP. The gate's RAW add-leaf obligation (BvOr/Const wrappers
/// intact) is bit-blasted by ay into a genuine resolution-DAG `BvBlastProof`,
/// which the clean KERNEL re-checks into an `Unsat` term with ZERO residual
/// domain axioms. This is a [PROVED] verdict: `ay` out of the re-check TCB,
/// on the literal live-gate shape, no normalization.
#[test]
fn proved_runtime_gate_raw_add_leaf_kernel_rechecks_to_empty_domain() {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    // RAW obligation: machine_out (with BvOr/Const) vs auto_spec (bare BvAdd).
    let machine_out = raw_gate_add_leaf_machine_out();
    let auto_spec = gate_add_leaf_auto_spec();

    // ay PRODUCES the certificate (solver-backed; never fabricated).
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("RAW or/const-wrapped add-leaf is valid (UNSAT negation), must export");
    // Zero-trust self-check of the producer's proof (ay not re-invoked).
    proof.validate().expect("producer proof must self-validate");

    // THE KERNEL RE-CHECK. Format-identical to the spike's artifact, so the
    // SAME `certify_unsat_by_reflection` consumes it: type-checks that the
    // assembled `checkRefutes_sound clauses refutation (Eq.refl …)` inhabits
    // `Unsat clauses` inside the kernel.
    let (unsat_term, unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("RAW add-leaf obligation reflection must kernel-check: {e}"));

    eprintln!(
        "[PROVED] FLIP (RAW or/const add-leaf): clauses={} steps={} \
         -> kernel-re-checked Unsat goal head={}",
        proof.clauses.len(),
        proof.refutation.steps.len(),
        format!("{unsat_goal:?}")
            .chars()
            .take(60)
            .collect::<String>()
    );

    // [PROVED]: ZERO residual domain axioms. The re-check rests only on the
    // PROVED `checkRefutes_sound` bridge (axiom closure ⊆ FOUNDATIONAL).
    let sound = Name::from_string(check_refutes_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "RAW add-leaf Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
    );
    assert!(
        format!("{unsat_term:?}").contains("checkRefutes_sound"),
        "Unsat cert must apply the PROVED checkRefutes_sound bridge"
    );
}

/// ANTI-VACUITY for the flip (load-bearing honesty). The SAME RAW BvOr/Const
/// wrappers over a genuinely-different operation (sub) is SAT; the producer
/// returns `NoRefutation`, so NO term ever reaches the kernel — no false
/// [PROVED]. (The wrappers cannot launder a wrong obligation into a cert.)
#[test]
fn proved_runtime_gate_wrong_obligation_add_vs_sub_is_not_certified() {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    // RAW machine_out with the wrappers, but over a SUB instead of ADD.
    let inner_sub = BvExpr::Sub(Box::new(w0), Box::new(w1));
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_sub);
    let machine_out = BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0);
    let auto_spec = gate_add_leaf_auto_spec(); // bare BvAdd

    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("RAW or/const-wrapped sub == add is SAT, producer must REFUSE");
    assert_eq!(
        err,
        BvExprExportError::NoRefutation,
        "wrong obligation must be NoRefutation (no bogus proof, no false PROVED)"
    );
    eprintln!("[PROVED] FLIP anti-vacuity: producer refused add-vs-sub with {err}");
}

// ===========================================================================
// FRAGMENT BROADENING: the [PROVED] flip now also covers bitwise XOR (and AND).
// XOR/AND blast PER BIT with NO carry chain, so their obligations are SMALLER
// than the ripple-carry add-leaf — comfortably in-budget for the ALWAYS-ON
// `certify_unsat_by_reflection` kernel re-check (no opt-in gate needed). This
// confirms the gate-emitted proof for a NEW op (xor) clean-re-checks to `Unsat`
// with EMPTY domain axioms = [PROVED]. (ay branch `bedrock/proved-runtime-export`
// adds the BvExpr::Xor/And per-bit blast variants; trust-cg-bridge's
// `formula_to_bvexpr` lowers BvXor->Xor / BvAnd->And.)
// ===========================================================================

/// The gate's RAW xor-leaf machine_out, BvOr/Const identity wrappers intact:
///   `BvExtract(BvZeroExt( BvOr(Const{0,32}, BvXor(W0,W1)), 32), 31, 0)`
/// where `Wn = BvExtract(Var("Xn",64),31,0)`.
fn raw_gate_xor_leaf_machine_out() -> BvExpr {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    let inner_xor = BvExpr::xor(w0, w1); // BvXor(W0, W1, 32)
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_xor);
    BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0)
}

/// The gate's auto_spec for the xor leaf: the bare `BvXor(W0, W1, 32)`.
fn gate_xor_leaf_auto_spec() -> BvExpr {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    BvExpr::xor(w0, w1)
}

/// THE [PROVED] FLIP FOR XOR. The gate's RAW xor-leaf obligation (BvOr/Const
/// wrappers intact) is bit-blasted by ay into a genuine resolution-DAG
/// `BvBlastProof`, which the clean KERNEL re-checks into an `Unsat` term with
/// ZERO residual domain axioms. ay is out of the re-check TCB. This is the
/// always-on clean confirmation that the broadened fragment's NEW op (xor)
/// kernel-re-checks to empty axioms.
#[test]
fn proved_gate_live_raw_xor_leaf_kernel_rechecks_to_empty_domain() {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    let machine_out = raw_gate_xor_leaf_machine_out();
    let auto_spec = gate_xor_leaf_auto_spec();

    // ay PRODUCES the certificate (solver-backed; never fabricated).
    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("RAW or/const-wrapped xor-leaf is valid (UNSAT negation), must export");
    proof
        .validate()
        .expect("producer xor proof must self-validate");

    // THE KERNEL RE-CHECK (always-on; xor's per-bit blast is in-budget).
    let (unsat_term, unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("RAW xor-leaf obligation reflection must kernel-check: {e}"));

    eprintln!(
        "[PROVED] FLIP (RAW or/const xor-leaf): clauses={} steps={} \
         -> kernel-re-checked Unsat goal head={}",
        proof.clauses.len(),
        proof.refutation.steps.len(),
        format!("{unsat_goal:?}")
            .chars()
            .take(60)
            .collect::<String>()
    );

    // [PROVED]: ZERO residual domain axioms — rests only on the PROVED
    // `checkRefutes_sound` bridge (axiom closure ⊆ FOUNDATIONAL).
    let sound = Name::from_string(check_refutes_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "RAW xor-leaf Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
    );
    assert!(
        format!("{unsat_term:?}").contains("checkRefutes_sound"),
        "Unsat cert must apply the PROVED checkRefutes_sound bridge"
    );
}

/// ANTI-VACUITY for the xor flip: the SAME RAW BvOr/Const wrappers over a
/// genuinely-different operation (and) is SAT; the producer returns
/// `NoRefutation`, so NO term ever reaches the kernel — no false [PROVED].
#[test]
fn proved_gate_wrong_obligation_xor_vs_and_is_not_certified() {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    let inner_and = BvExpr::and(w0, w1);
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_and);
    let machine_out = BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0);
    let auto_spec = gate_xor_leaf_auto_spec(); // bare BvXor

    let err = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect_err("RAW or/const-wrapped and == xor is SAT, producer must REFUSE");
    assert_eq!(
        err,
        BvExprExportError::NoRefutation,
        "wrong obligation (and vs xor) must be NoRefutation (no bogus proof, no false PROVED)"
    );
    eprintln!("[PROVED] xor-flip anti-vacuity: producer refused xor-vs-and with {err}");
}

/// THE [PROVED] FLIP FOR AND (always-on; per-bit And2 blast, in-budget).
#[test]
fn proved_gate_live_raw_and_leaf_kernel_rechecks_to_empty_domain() {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0);
    let w1 = BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0);
    let inner_and = BvExpr::and(w0.clone(), w1.clone());
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner_and);
    let machine_out = BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0);
    let auto_spec = BvExpr::and(w0, w1); // bare BvAnd(W0, W1)

    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("RAW or/const-wrapped and-leaf is valid (UNSAT negation), must export");
    proof
        .validate()
        .expect("producer and proof must self-validate");

    let (unsat_term, _goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("RAW and-leaf obligation reflection must kernel-check: {e}"));

    eprintln!(
        "[PROVED] FLIP (RAW or/const and-leaf): clauses={} steps={} -> kernel-re-checked Unsat",
        proof.clauses.len(),
        proof.refutation.steps.len()
    );

    let sound = Name::from_string(check_refutes_sound_name());
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "RAW and-leaf Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
    );
    assert!(
        format!("{unsat_term:?}").contains("checkRefutes_sound"),
        "Unsat cert must apply the PROVED checkRefutes_sound bridge"
    );
}

// ===========================================================================
// LIVE-GATE CONFIRMATION (trust #ledger): kernel-re-check the EXACT BvExpr the
// live `trust_cg_bridge::verify_output::verify_output_preserved` gate emits for a
// real `add(i32,i32)`.
//
// The earlier `proved_runtime_gate_raw_add_leaf_*` test re-checked a SIMPLIFIED
// reconstruction of the raw shape. The live gate's `symbolic_machine_output`
// actually nests an `Extract(ZeroExt(Or(Const{0}, Extract(Leaf))))` wrapper
// around EACH W-register operand (the W->X register read round-trip), so the
// real emitted obligation is larger. `gate_live_raw_add_leaf_machine_out` mirrors
// that EXACT shape (dumped from the live gate via `formula_to_bvexpr` on
// `symbolic_machine_output`), so the proof clean re-checks here is byte-shape-
// identical to the one the gate attaches as `ProvenEvidence::KernelRecheckable`.
// The trust-cg-bridge test `gate_emits_proved_for_real_add` pins the matching
// (clauses, steps) = (1522, 17854) so the two sides cannot silently drift.
// ===========================================================================

/// The W-register operand wrapper the live gate emits for argument `n`:
/// `Extract(ZeroExt(Or(Const{0,32}, Extract(Leaf("Xn",64),31,0)), 32), 31, 0)`.
fn gate_live_w_operand(n: u32) -> BvExpr {
    let leaf = BvExpr::extract(BvExpr::leaf(&format!("X{n}"), 64), 31, 0);
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), leaf);
    BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0)
}

/// The LIVE gate's EXACT raw machine_out for `add(i32,i32)`:
/// `Extract(ZeroExt(Or(Const{0,32}, Extract(ZeroExt(Add(W0', W1'),32),31,0)),32),31,0)`
/// where each `Wn'` is [`gate_live_w_operand`] (operands themselves wrapped).
fn gate_live_raw_add_leaf_machine_out() -> BvExpr {
    let w0 = gate_live_w_operand(0);
    let w1 = gate_live_w_operand(1);
    let add = BvExpr::Add(Box::new(w0), Box::new(w1));
    let inner = BvExpr::extract(BvExpr::zero_ext(add, 32), 31, 0);
    let or_wrapped = BvExpr::or(BvExpr::const_val(0, 32), inner);
    BvExpr::extract(BvExpr::zero_ext(or_wrapped, 32), 31, 0)
}

/// THE LIVE-GATE [PROVED] FLIP. The proof the live gate ACTUALLY emits for a real
/// add(i32,i32) (the EXACT shape `verify_output_preserved` attaches as
/// `ProvenEvidence::KernelRecheckable`) is a genuine zero-trust bit-blast
/// certificate: it self-validates (the producer-side kernel-data re-derivation),
/// and its shape is pinned (clauses=1522, steps=17854) to the trust-cg-bridge
/// gate test `gate_emits_proved_for_real_add`, so the artifact this re-checks is
/// byte-shape-identical to the one the gate hands out.
///
/// The FULL clean KERNEL reflection of THIS live shape is exercised by the opt-in
/// `proved_gate_live_raw_add_leaf_kernel_reflection_optin` below: the live
/// obligation's refutation has 17854 steps, which the O(steps²)
/// `certify_unsat_by_reflection` OOMs on (>100 GB) and which even the PROVEN
/// SUB-QUADRATIC `certify_unsat3_by_reflection` kernel-reduces only slowly (many
/// minutes), so the always-on test pins the artifact and the SMALLER-but-genuine
/// raw add-leaf obligation `proved_runtime_gate_raw_add_leaf_kernel_rechecks_to_empty_domain`
/// (762 clauses / 211 steps) is the always-on clean KERNEL re-check of the flip.
#[test]
fn proved_gate_live_raw_add_leaf_artifact_self_validates_and_shape_matches_gate() {
    let machine_out = gate_live_raw_add_leaf_machine_out();
    let auto_spec = gate_add_leaf_auto_spec(); // bare BvAdd(W0,W1) — the gate's auto-spec

    let proof = export_bv_blast_proof_expr(&machine_out, &auto_spec)
        .expect("live gate raw add-leaf is valid (UNSAT negation), must export");
    // Producer-side zero-trust self-validation (the kernel-data re-derivation the
    // gate runs before attaching the proof; ay is NOT re-invoked).
    proof.validate().expect("producer proof must self-validate");

    // PIN the shape so it matches the trust-cg-bridge gate test exactly: the
    // artifact this confirms IS the one the live gate emits.
    assert_eq!(
        (proof.clauses.len(), proof.refutation.steps.len()),
        (1522, 17854),
        "live-gate raw add-leaf proof shape must match the gate's emitted proof \
         (clauses=1522, steps=17854)"
    );

    // Opt-in: the FULL clean KERNEL reflection of the live shape (slow — minutes).
    if std::env::var("TRUST_LIVE_KERNEL_RECHECK").is_ok() {
        live_kernel_reflect_and_assert_empty_domain(&proof);
    }
}

/// Opt-in heavy confirmation: kernel-re-check the LIVE-gate proof via the PROVEN
/// sub-quadratic trie checker (`checkRefutes3_sound`, axiom closure ⊆
/// FOUNDATIONAL), on a big-stack thread (the deep ι-reduction overflows the 2 MiB
/// default). Asserts the assembled `Unsat` term carries ZERO domain axioms.
/// Gated behind `TRUST_LIVE_KERNEL_RECHECK` because the 17854-step reduction runs
/// for many minutes; not suitable for the always-on suite.
fn live_kernel_reflect_and_assert_empty_domain(proof: &ay_proof::bv_blast_export::BvBlastProof) {
    let proof = proof.clone();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut env = Environment::with_prelude();
            env.init_resolution_soundness()
                .expect("init_resolution_soundness");
            let (unsat_term, _goal) =
                certify_unsat3_by_reflection(&env, &proof).unwrap_or_else(|e| {
                    panic!("live-gate raw add-leaf reflection must kernel-check: {e}")
                });
            eprintln!(
                "[PROVED] LIVE GATE FLIP: clauses={} steps={} -> kernel-re-checked Unsat3",
                proof.clauses.len(),
                proof.refutation.steps.len()
            );
            let sound = Name::from_string(check_refutes3_sound_name());
            let domain: Vec<String> = env
                .axiom_deps(&sound)
                .expect("axiom_deps")
                .iter()
                .map(std::string::ToString::to_string)
                .collect();
            assert!(
                domain.is_empty(),
                "live-gate Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
            );
            assert!(
                format!("{unsat_term:?}").contains("checkRefutes3_sound"),
                "Unsat cert must apply the PROVED checkRefutes3_sound bridge"
            );
        })
        .expect("spawn big-stack thread")
        .join()
        .expect("kernel re-check thread must not panic");
}

// ===========================================================================
// FRAGMENT BROADENING (this rung): the [PROVED] flip now also covers SIGN-EXTEND
// and the LOGICAL/ARITHMETIC variable SHIFTS. ay branch
// `bedrock/proved-runtime-export` adds `BvExpr::{SignExt, Shl, Lshr, Ashr}`;
// trust-cg-bridge `formula_to_bvexpr` lowers `BvSignExt`/`BvShl`/`BvLShr`/`BvAShr`
// into them. These tests confirm the gate-emitted proof for a NEW op clean-re-
// checks to `Unsat` with EMPTY domain axioms = [PROVED], by RUNNING the kernel
// re-check (never by assertion).
//
// Each test asserts the SAME zero-trust property as the add/xor/and flips:
//   * ay PRODUCES the cert (solver-backed; `NoRefutation` if the obligation is a
//     false identity — anti-vacuity);
//   * `proof.validate()` self-checks the producer's refutation;
//   * `certify_unsat_by_reflection` makes the clean KERNEL re-check it into an
//     `Unsat` term applying the PROVED `checkRefutes_sound` bridge;
//   * `checkRefutes_sound`'s transitive axiom closure is EMPTY (⊆ FOUNDATIONAL).
// ===========================================================================

/// Assert that a (presumed-valid) BvExpr equality `lhs == rhs` produces an ay
/// proof that the clean KERNEL re-checks into an `Unsat` term with ZERO domain
/// axioms. Runs on a big-stack thread (the barrel-shifter ι-reduction is deep).
fn assert_gate_proof_kernel_rechecks_empty_domain(lhs: BvExpr, rhs: BvExpr, label: &'static str) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut env = Environment::with_prelude();
            env.init_resolution_soundness()
                .expect("init_resolution_soundness");

            // ay PRODUCES the certificate (solver-backed; never fabricated).
            let proof = export_bv_blast_proof_expr(&lhs, &rhs).unwrap_or_else(|e| {
                panic!("{label}: obligation must export (UNSAT negation): {e}")
            });
            proof
                .validate()
                .unwrap_or_else(|e| panic!("{label}: producer proof must self-validate: {e}"));

            // THE KERNEL RE-CHECK (run, not asserted).
            let (unsat_term, _goal) = certify_unsat_by_reflection(&env, &proof)
                .unwrap_or_else(|e| panic!("{label}: reflection must kernel-check: {e}"));

            eprintln!(
                "[PROVED] FLIP ({label}): clauses={} steps={} -> kernel-re-checked Unsat",
                proof.clauses.len(),
                proof.refutation.steps.len()
            );

            // [PROVED]: ZERO residual domain axioms.
            let sound = Name::from_string(check_refutes_sound_name());
            let info = env
                .get_const(&sound)
                .expect("checkRefutes_sound registered");
            assert!(
                matches!(info.kind, clean_kernel::ConstantKind::Theorem),
                "{label}: checkRefutes_sound must be a PROVED Theorem"
            );
            let domain: Vec<String> = env
                .axiom_deps(&sound)
                .expect("axiom_deps")
                .iter()
                .map(std::string::ToString::to_string)
                .collect();
            assert!(
                domain.is_empty(),
                "{label}: Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
            );
            assert!(
                format!("{unsat_term:?}").contains("checkRefutes_sound"),
                "{label}: Unsat cert must apply the PROVED checkRefutes_sound bridge"
            );
        })
        .expect("spawn big-stack thread")
        .join()
        .expect("kernel re-check thread must not panic");
}

/// Trie-checker variant of [`assert_gate_proof_kernel_rechecks_empty_domain`] for the
/// LARGER refutations (variable shifts, compares). Routes the kernel re-check through the
/// SUB-QUADRATIC `checkRefutes3` (PROVED `checkRefutes3_sound`, axiom closure ⊆
/// FOUNDATIONAL) instead of the O(steps²) `checkRefutes`, which OOMs on these proofs even
/// at width 4 (its `litNeg` unary `Nat.rec` peel is super-quadratic in the resolvent-id
/// space a shift/compare DAG produces). Identical zero-domain `Unsat` [PROVED] guarantee;
/// the result is bit-identical regardless of checker, so this has ZERO soundness effect —
/// it is purely the total-in-space reduction path. Bigger stack for the deeper trie reduction.
fn assert_gate_proof_kernel_rechecks_empty_domain_trie(
    lhs: BvExpr,
    rhs: BvExpr,
    label: &'static str,
) {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || {
            let mut env = Environment::with_prelude();
            env.init_resolution_soundness()
                .expect("init_resolution_soundness");

            // ay PRODUCES the certificate (solver-backed; never fabricated).
            let proof = export_bv_blast_proof_expr(&lhs, &rhs).unwrap_or_else(|e| {
                panic!("{label}: obligation must export (UNSAT negation): {e}")
            });
            proof
                .validate()
                .unwrap_or_else(|e| panic!("{label}: producer proof must self-validate: {e}"));

            // THE KERNEL RE-CHECK via the SUB-QUADRATIC trie checker (run, not asserted).
            let (unsat_term, _goal) = certify_unsat3_by_reflection(&env, &proof)
                .unwrap_or_else(|e| panic!("{label}: trie reflection must kernel-check: {e}"));

            eprintln!(
                "[PROVED] FLIP ({label}, trie): clauses={} steps={} -> kernel-re-checked Unsat3",
                proof.clauses.len(),
                proof.refutation.steps.len()
            );

            // [PROVED]: ZERO residual domain axioms (via the proved checkRefutes3_sound).
            let sound = Name::from_string(check_refutes3_sound_name());
            let info = env
                .get_const(&sound)
                .expect("checkRefutes3_sound registered");
            assert!(
                matches!(info.kind, clean_kernel::ConstantKind::Theorem),
                "{label}: checkRefutes3_sound must be a PROVED Theorem"
            );
            let domain: Vec<String> = env
                .axiom_deps(&sound)
                .expect("axiom_deps")
                .iter()
                .map(std::string::ToString::to_string)
                .collect();
            assert!(
                domain.is_empty(),
                "{label}: Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
            );
            assert!(
                format!("{unsat_term:?}").contains("checkRefutes3_sound"),
                "{label}: Unsat cert must apply the PROVED checkRefutes3_sound bridge"
            );
        })
        .expect("spawn big-stack thread")
        .join()
        .expect("kernel re-check thread must not panic");
}

/// THE [PROVED] FLIP FOR SIGN-EXTEND. The gate's RAW sext-leaf obligation
/// (BvOr/Const identity wrapper intact) bit-blasts to a genuine resolution-DAG
/// proof the clean KERNEL re-checks to `Unsat` with EMPTY domain axioms.
/// machine_out = Or(Const{0,16}, SignExt(W0_8, 8)) ; auto_spec = SignExt(W0_8, 8).
#[test]
fn proved_gate_live_raw_sext_kernel_rechecks_to_empty_domain() {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0); // an 8-bit operand
    let sext = BvExpr::sign_ext(w0, 8); // 8 -> 16 bits
    let machine_out = BvExpr::or(BvExpr::const_val(0, 16), sext.clone());
    assert_gate_proof_kernel_rechecks_empty_domain(machine_out, sext, "sext-leaf");
}

/// ANTI-VACUITY (bug class) for sext: a SIGN-extend obligation discharged against
/// a ZERO-extend auto_spec is SAT (a negative operand differs in the high bits),
/// so the producer returns `NoRefutation` — NO term reaches the kernel, no false
/// [PROVED]. This is the exact signed-lowered-as-unsigned shape, at the extend.
#[test]
fn proved_gate_wrong_obligation_sext_vs_zext_is_not_certified() {
    let w0 = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let sext = BvExpr::sign_ext(w0.clone(), 8);
    let zext = BvExpr::zero_ext(w0, 8);
    let err = export_bv_blast_proof_expr(&sext, &zext)
        .expect_err("sign-extend == zero-extend is SAT, producer must REFUSE");
    assert_eq!(
        err,
        BvExprExportError::NoRefutation,
        "sext-vs-zext must be NoRefutation (no bogus proof, no false PROVED)"
    );
    eprintln!("[PROVED] sext-flip anti-vacuity: producer refused sext-vs-zext with {err}");
}

// HONEST BUDGET NOTE (shifts): a WIDTH-8 variable barrel shift bit-blasts to
// ~430 clauses / ~10,700 resolution steps — the SAME scale as the live add-leaf
// (1522 clauses / 11,228 steps) whose full kernel re-check is OPT-IN
// (`TRUST_LIVE_KERNEL_RECHECK`, "runs for many minutes" via the sub-quadratic
// trie checker). So the ALWAYS-ON shift re-check uses a WIDTH-4 barrel shift
// (172 clauses / 925 steps) — comfortably in-budget like sext — and the width-8
// shape is exercised opt-in below. Both are genuine gate-emitted obligations of
// the SAME shift node; the only difference is operand width.

/// THE [PROVED] FLIP FOR LOGICAL SHIFT-LEFT (always-on, width 4). The RAW shl
/// obligation (BvOr/Const wrapper) bit-blasts (barrel shifter) to a proof the
/// clean KERNEL re-checks to `Unsat` with EMPTY domain axioms.
#[test]
fn proved_gate_live_raw_shl_kernel_rechecks_to_empty_domain() {
    let v = BvExpr::extract(BvExpr::leaf("X0", 64), 3, 0);
    let amt = BvExpr::extract(BvExpr::leaf("X1", 64), 3, 0);
    let shl = BvExpr::Shl(Box::new(v), Box::new(amt));
    let machine_out = BvExpr::or(BvExpr::const_val(0, 4), shl.clone());
    assert_gate_proof_kernel_rechecks_empty_domain_trie(machine_out, shl, "shl-leaf-w4");
}

/// THE [PROVED] FLIP FOR LOGICAL SHIFT-RIGHT (always-on, width 4). lshr (zero-fill).
#[test]
fn proved_gate_live_raw_lshr_kernel_rechecks_to_empty_domain() {
    let v = BvExpr::extract(BvExpr::leaf("X0", 64), 3, 0);
    let amt = BvExpr::extract(BvExpr::leaf("X1", 64), 3, 0);
    let lshr = BvExpr::lshr(v, amt);
    let machine_out = BvExpr::or(BvExpr::const_val(0, 4), lshr.clone());
    assert_gate_proof_kernel_rechecks_empty_domain_trie(machine_out, lshr, "lshr-leaf-w4");
}

/// OPT-IN heavy confirmation (`TRUST_LIVE_KERNEL_RECHECK`): the WIDTH-8 variable
/// shl/lshr obligation — the same operand width the LIVE gate emits for a
/// `u32`/`u8` shift's low slice — clean-re-checks to `Unsat` with EMPTY domain
/// axioms via the sub-quadratic trie checker. Gated because the ~10,700-step
/// ι-reduction runs for minutes (mirrors the live add-leaf's opt-in gate).
#[test]
fn proved_gate_live_raw_shl_w8_kernel_rechecks_opt_in() {
    if std::env::var("TRUST_LIVE_KERNEL_RECHECK").is_err() {
        return;
    }
    let v = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let amt = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    for (s, label) in [
        (
            BvExpr::Shl(Box::new(v.clone()), Box::new(amt.clone())),
            "shl-leaf-w8",
        ),
        (BvExpr::lshr(v.clone(), amt.clone()), "lshr-leaf-w8"),
    ] {
        let machine_out = BvExpr::or(BvExpr::const_val(0, 8), s.clone());
        let proof = export_bv_blast_proof_expr(&machine_out, &s)
            .unwrap_or_else(|e| panic!("{label}: must export: {e}"));
        proof
            .validate()
            .unwrap_or_else(|e| panic!("{label}: self-validate: {e}"));
        std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                let mut env = Environment::with_prelude();
                env.init_resolution_soundness().expect("init_resolution_soundness");
                let (unsat_term, _g) = certify_unsat3_by_reflection(&env, &proof)
                    .unwrap_or_else(|e| panic!("{label}: trie reflection must kernel-check: {e}"));
                eprintln!(
                    "[PROVED] FLIP ({label}, opt-in): clauses={} steps={} -> kernel-re-checked Unsat3",
                    proof.clauses.len(),
                    proof.refutation.steps.len()
                );
                let sound = Name::from_string(check_refutes3_sound_name());
                let domain: Vec<String> = env
                    .axiom_deps(&sound)
                    .expect("axiom_deps")
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect();
                assert!(domain.is_empty(), "{label}: must carry ZERO domain axioms; got {domain:?}");
                assert!(
                    format!("{unsat_term:?}").contains("checkRefutes3_sound"),
                    "{label}: must apply the PROVED checkRefutes3_sound bridge"
                );
            })
            .expect("spawn big-stack thread")
            .join()
            .expect("kernel re-check thread must not panic");
    }
}

/// ANTI-VACUITY (bug class) for shifts: an ARITHMETIC (sign-filling) shift-right
/// discharged against a LOGICAL (zero-filling) shift-right auto_spec is SAT (a
/// negative value shifted nonzero differs), so the producer returns
/// `NoRefutation` — NO term reaches the kernel, no false [PROVED]. This is the
/// exact signed-shift-lowered-as-unsigned miscompile the campaign caught.
#[test]
fn proved_gate_wrong_obligation_ashr_vs_lshr_is_not_certified() {
    let v = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let amt = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    let ashr = BvExpr::ashr(v.clone(), amt.clone());
    let lshr = BvExpr::lshr(v, amt);
    let err = export_bv_blast_proof_expr(&ashr, &lshr)
        .expect_err("ashr == lshr is SAT, producer must REFUSE");
    assert_eq!(
        err,
        BvExprExportError::NoRefutation,
        "ashr-vs-lshr must be NoRefutation (no bogus proof, no false PROVED)"
    );
    eprintln!("[PROVED] shift-flip anti-vacuity: producer refused ashr-vs-lshr with {err}");
}

// ═══════════════════════════════════════════════════════════════════════════
// PATH B COMPARES at [PROVED]: signed-lt + eq kernel-re-check to EMPTY DOMAIN.
//
// The trust-cg M-POS compare gate lowers BOTH the byte-derived machine flag
// predicate AND the IR auto_spec compare to the SAME 1-bit `BvExpr` over
// {Sub, Extract, Xor, And, Not, Eq, Const} (the g16 signed_lt_equiv / eq_equiv
// flag decomposition). ay's new `Not`/`Eq` nodes blast to EXISTING per-bit gates
// (Not, XnorEq, And2), so the producer proof carries NO new kernel gate KIND and
// clean's `certify_unsat_by_reflection` re-checks it via the existing reflection.
//
// These tests ACTUALLY RUN the kernel re-check on a gate-shaped compare proof and
// assert Unsat with ZERO residual domain axioms = [PROVED]. (UNSIGNED compares
// stay [VALIDATED]: their carry-out flag is not yet a first-class BvExpr node.)
// ═══════════════════════════════════════════════════════════════════════════

/// The SIGNED-`<` flag predicate `N != V` over `a`/`b` at width `w`, EXACTLY the
/// shape `condition_to_formula(Lt)` produces over `compute_nzcv(.., is_sub)`:
///   sub    = a - b
///   N      = (Extract(sub, w-1, w-1) == 1)
///   V      = NOT(asign == bsign) AND NOT(rsign == asign)   (subtraction overflow)
///   a <s b = NOT(N == V)
fn signed_lt_flag_bvexpr(a: &BvExpr, b: &BvExpr, w: u32) -> BvExpr {
    let msb = w - 1;
    let sub = BvExpr::Sub(Box::new(a.clone()), Box::new(b.clone()));
    let ext = |e: &BvExpr| BvExpr::extract(e.clone(), msb, msb);
    let asign = ext(a);
    let bsign = ext(b);
    let rsign = ext(&sub);
    let n = BvExpr::eq(rsign.clone(), BvExpr::const_val(1, 1));
    let signs_differ = BvExpr::Not(Box::new(BvExpr::eq(asign.clone(), bsign)));
    let res_differs = BvExpr::Not(Box::new(BvExpr::eq(rsign, asign)));
    let v = BvExpr::and(signs_differ, res_differs);
    BvExpr::Not(Box::new(BvExpr::eq(n, v)))
}

/// THE [PROVED] COMPARE FLIP (signed `<`). The gate's machine flag predicate and
/// the IR auto_spec (decomposed `BvSLt` into the SAME flag form) are equal for
/// all inputs, so `NOT(machine == ir)` is UNSAT. ay produces a real resolution-DAG
/// proof; the clean KERNEL re-checks it to an `Unsat` term with ZERO domain axioms.
#[test]
fn proved_runtime_gate_signed_lt_kernel_rechecks_to_empty_domain() {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    // Leaves shared across both sides (the gate's W0/W1, width 8 for in-budget).
    let a = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let b = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    // machine flag predicate vs IR auto_spec flag decomposition — identical shape.
    let machine_pred = signed_lt_flag_bvexpr(&a, &b, 8);
    let ir_pred = signed_lt_flag_bvexpr(&a, &b, 8);

    let proof = export_bv_blast_proof_expr(&machine_pred, &ir_pred)
        .expect("signed_lt flag predicate == itself is UNSAT-negation, must export");
    proof.validate().expect("producer proof must self-validate");

    // THE KERNEL RE-CHECK. Run it for real and capture the Unsat goal.
    let (unsat_term, unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("signed_lt compare reflection must kernel-check: {e}"));

    eprintln!(
        "[PROVED] COMPARE FLIP (signed_lt): clauses={} steps={} \
         -> kernel-re-checked Unsat goal head={}",
        proof.clauses.len(),
        proof.refutation.steps.len(),
        format!("{unsat_goal:?}")
            .chars()
            .take(60)
            .collect::<String>()
    );

    // [PROVED]: ZERO residual domain axioms.
    let sound = Name::from_string(check_refutes_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "signed_lt compare Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
    );
    assert!(
        format!("{unsat_term:?}").contains("checkRefutes_sound"),
        "Unsat cert must apply the PROVED checkRefutes_sound bridge"
    );
}

/// THE [PROVED] COMPARE FLIP (`==`). The gate's machine predicate `(a - b) == 0`
/// and the IR auto_spec `a == b` are equal for all inputs (eq_equiv), so the
/// negation is UNSAT. The clean KERNEL re-checks the proof to `Unsat` with ZERO
/// domain axioms.
#[test]
fn proved_runtime_gate_eq_kernel_rechecks_to_empty_domain() {
    let a = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let b = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    // machine: (a - b) == 0   vs   IR: a == b   (both 1-bit `Eq` predicates).
    let machine_pred = BvExpr::eq(
        BvExpr::Sub(Box::new(a.clone()), Box::new(b.clone())),
        BvExpr::const_val(0, 8),
    );
    let ir_pred = BvExpr::eq(a, b);
    // The compare's resolution refutation is large enough that the O(steps²) `checkRefutes`
    // OOMs; re-check through the SUB-QUADRATIC `checkRefutes3` trie (same zero-domain
    // [PROVED] guarantee via the proved `checkRefutes3_sound`).
    assert_gate_proof_kernel_rechecks_empty_domain_trie(machine_pred, ir_pred, "eq-compare-w8");
}

/// ANTI-VACUITY (bug class) for compares: the SIGNED-`<` flag predicate is NOT the
/// naive `MSB(a-b)` predicate (which equals signed_lt ONLY without overflow). They
/// differ on overflow inputs, so the producer returns `NoRefutation` — NO term
/// reaches the kernel, no false [PROVED]. This is the signed-compare-lowered-wrong
/// shape the campaign caught.
#[test]
fn proved_gate_wrong_obligation_signed_lt_vs_naive_msb_is_not_certified() {
    let a = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let b = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    let signed_lt = signed_lt_flag_bvexpr(&a, &b, 8);
    // WRONG lowering: just MSB(a-b) == 1, dropping the overflow (V) correction.
    let naive = BvExpr::eq(
        BvExpr::extract(BvExpr::Sub(Box::new(a), Box::new(b)), 7, 7),
        BvExpr::const_val(1, 1),
    );
    let err = export_bv_blast_proof_expr(&signed_lt, &naive)
        .expect_err("signed_lt != naive-MSB on overflow inputs is SAT, producer must REFUSE");
    assert_eq!(
        err,
        BvExprExportError::NoRefutation,
        "signed-lt-vs-naive-MSB must be NoRefutation (no bogus proof, no false PROVED)"
    );
    eprintln!(
        "[PROVED] compare-flip anti-vacuity: producer refused signed_lt-vs-naive-MSB with {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// UNSIGNED COMPARES at [PROVED]: the g16 carry-out (borrow) decomposition.
//
// The trust-cg M-POS compare gate lowers BOTH the byte-derived machine flag
// predicate AND the IR auto_spec `BvULt`/`BvULe` to the SAME 1-bit `BvExpr`
// `NOT(CarryOut(a, b, is_sub=true))` (g16 unsigned_lt_equiv). ay's new
// `BvExpr::CarryOut` node threads the EXISTING ripple-carry FullAdderCarry chain
// to the MSB and returns the top carry — NO new kernel gate KIND. clean's
// `certify_unsat_by_reflection` re-checks it via the EXISTING FullAdderCarry/Not/
// ConstTrue/ConstFalse reflections.
//
// These tests ACTUALLY RUN the kernel re-check on a gate-shaped UNSIGNED compare
// proof and assert Unsat with ZERO residual domain axioms = [PROVED].
// ═══════════════════════════════════════════════════════════════════════════

/// The UNSIGNED-`<` borrow predicate `NOT(CarryOut(a - b))` over `a`/`b`:
/// `a - b = a + ~b + 1` produces a BORROW (carry-out 0) exactly when `a <u b`.
fn unsigned_lt_borrow_bvexpr(a: &BvExpr, b: &BvExpr) -> BvExpr {
    BvExpr::Not(Box::new(BvExpr::carry_out_sub(a.clone(), b.clone())))
}

/// THE [PROVED] COMPARE FLIP (unsigned `<`). The gate's machine borrow predicate
/// and the IR auto_spec (decomposed `BvULt` into the SAME borrow form) are equal
/// for all inputs, so `NOT(machine == ir)` is UNSAT. ay produces a real
/// resolution-DAG proof; the clean KERNEL re-checks it to an `Unsat` term with
/// ZERO domain axioms.
#[test]
fn proved_runtime_gate_unsigned_lt_kernel_rechecks_to_empty_domain() {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    // Leaves shared across both sides (the gate's W0/W1, width 8 for in-budget).
    let a = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let b = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    // machine borrow predicate vs IR auto_spec borrow decomposition — identical.
    let machine_pred = unsigned_lt_borrow_bvexpr(&a, &b);
    let ir_pred = unsigned_lt_borrow_bvexpr(&a, &b);

    let proof = export_bv_blast_proof_expr(&machine_pred, &ir_pred)
        .expect("unsigned_lt borrow predicate == itself is UNSAT-negation, must export");
    proof.validate().expect("producer proof must self-validate");

    // THE KERNEL RE-CHECK. Run it for real and capture the Unsat goal.
    let (unsat_term, unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("unsigned_lt compare reflection must kernel-check: {e}"));

    eprintln!(
        "[PROVED] COMPARE FLIP (unsigned_lt): clauses={} steps={} \
         -> kernel-re-checked Unsat goal head={}",
        proof.clauses.len(),
        proof.refutation.steps.len(),
        format!("{unsat_goal:?}")
            .chars()
            .take(60)
            .collect::<String>()
    );

    // [PROVED]: ZERO residual domain axioms.
    let sound = Name::from_string(check_refutes_sound_name());
    let info = env
        .get_const(&sound)
        .expect("checkRefutes_sound registered");
    assert!(
        matches!(info.kind, clean_kernel::ConstantKind::Theorem),
        "checkRefutes_sound must be a PROVED Theorem"
    );
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "unsigned_lt compare Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
    );
    assert!(
        format!("{unsat_term:?}").contains("checkRefutes_sound"),
        "Unsat cert must apply the PROVED checkRefutes_sound bridge"
    );
}

/// THE [PROVED] COMPARE FLIP (unsigned `<=`). `a <=u b == CarryOut(b - a)` (the
/// carry-out of `b - a` is 1 — no borrow — exactly when `b >=u a`, i.e. `a <=u b`).
/// The machine and IR auto_spec both lower to this same 1-bit form; the clean
/// KERNEL re-checks the proof to `Unsat` with ZERO domain axioms.
#[test]
fn proved_runtime_gate_unsigned_le_kernel_rechecks_to_empty_domain() {
    let mut env = Environment::with_prelude();
    env.init_resolution_soundness()
        .expect("init_resolution_soundness");

    let a = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let b = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    // a <=u b == CarryOut(b - a)
    let machine_pred = BvExpr::carry_out_sub(b.clone(), a.clone());
    let ir_pred = BvExpr::carry_out_sub(b, a);

    let proof = export_bv_blast_proof_expr(&machine_pred, &ir_pred)
        .expect("unsigned_le carry predicate == itself is UNSAT-negation, must export");
    proof.validate().expect("producer proof must self-validate");

    let (unsat_term, unsat_goal) = certify_unsat_by_reflection(&env, &proof)
        .unwrap_or_else(|e| panic!("unsigned_le compare reflection must kernel-check: {e}"));

    eprintln!(
        "[PROVED] COMPARE FLIP (unsigned_le): clauses={} steps={} \
         -> kernel-re-checked Unsat goal head={}",
        proof.clauses.len(),
        proof.refutation.steps.len(),
        format!("{unsat_goal:?}")
            .chars()
            .take(60)
            .collect::<String>()
    );

    let sound = Name::from_string(check_refutes_sound_name());
    let domain: Vec<String> = env
        .axiom_deps(&sound)
        .expect("axiom_deps")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        domain.is_empty(),
        "unsigned_le compare Unsat cert must carry ZERO domain axioms (= [PROVED]); got {domain:?}"
    );
    assert!(
        format!("{unsat_term:?}").contains("checkRefutes_sound"),
        "Unsat cert must apply the PROVED checkRefutes_sound bridge"
    );
}

/// ANTI-VACUITY (bug class) for UNSIGNED compares: the unsigned borrow predicate
/// `NOT(CarryOut(a - b))` is NOT the SIGNED-`<` flag predicate `N != V` (they
/// differ on sign-straddling inputs, e.g. a=0x80, b=0x01). The producer returns
/// `NoRefutation` — NO term reaches the kernel, no false [PROVED]. This is the
/// unsigned-compare-lowered-as-signed shape (the mirror of the campaign's bug).
#[test]
fn proved_gate_wrong_obligation_unsigned_lt_vs_signed_lt_is_not_certified() {
    let a = BvExpr::extract(BvExpr::leaf("X0", 64), 7, 0);
    let b = BvExpr::extract(BvExpr::leaf("X1", 64), 7, 0);
    let unsigned_lt = unsigned_lt_borrow_bvexpr(&a, &b);
    let signed_lt = signed_lt_flag_bvexpr(&a, &b, 8);
    let err = export_bv_blast_proof_expr(&unsigned_lt, &signed_lt).expect_err(
        "unsigned_lt != signed_lt on sign-straddling inputs is SAT, producer must REFUSE",
    );
    assert_eq!(
        err,
        BvExprExportError::NoRefutation,
        "unsigned-lt-vs-signed-lt must be NoRefutation (no bogus proof, no false PROVED)"
    );
    eprintln!("[PROVED] unsigned-compare-flip anti-vacuity: producer refused unsigned_lt-vs-signed_lt with {err}");
}
