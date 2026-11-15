// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 stage 1 — level identity across the ElabCtx↔ProofState bridge
//! (docs/analysis/u2-implementation-plan-2026-08-24.md §1.3/§3, lane U2,
//! 2026-08-25).
//!
//! Fixture-driven from `tests/fixtures/universes/` — the same p41/p42 files
//! `scripts/u2_battery.sh` pins against the release binary; this module pins
//! them inside the lib suite so a binary-less `cargo test -p clean-elab`
//! still holds the line.
//!
//! What stage 1 fixed (all faces measured; the Mathlib-scale inventory is the
//! 5-file source-elab gate at `369ba0951`, sub-class A, 19 declarations —
//! `cast_heq_iff_heq`, `forall₂_true_iff`, `Subtype.mk_eq_mk`, …):
//!
//! 1. `elab_by_tactic` built its ProofState over `MetaState::new()` — an
//!    EMPTY universe world. `ProofState::fresh_universe_param` re-minted
//!    `u_0, u_1, …`, aliasing by STRING whatever the declaration's ElabCtx
//!    had minted under those names, and nothing was rigid inside the block.
//!    Fixed by `ProofState::seed_universe_world` (names + counter + rigid
//!    set, every enclosing level name rigid inside the block) plus entry-side
//!    `instantiate_levels` on the goal and locals.
//! 2. The ProofState kernel checks (`build_local_ctx`, `check_type_strict`,
//!    `infer_type[_strict]`, `is_def_eq`) instantiated expression metas only:
//!    the kernel — which has no level union-find — was handed raw
//!    `Level::Param`s the tactic's own unifier had already recorded equal and
//!    correctly rejected them
//!    (`TypeMismatch { expected: Sort(Param(u_X)), inferred: Sort(Param(u_0)) }`).
//!    Fixed by `ProofState::instantiate_for_kernel`.
//! 3. On success the exit path realized only the ELABCTX's level solutions;
//!    anything solved solely in `ps.metas` was dropped on the floor. Fixed by
//!    the `ps.metas.instantiate_levels(&proof)` exit resolution.
//! 4. The rw face additionally hit a matcher-gating defect: at a bare
//!    non-meta FVar node (exactly what a polymorphic goal has where a
//!    monomorphic one has `Const Nat`), the full-unifier fallback
//!    WHNF-collapsed a reducible const-headed pattern onto the FVar and
//!    committed a wrong-subterm match — surfacing as spurious
//!    `RewriteNoMatch`. Fixed in `rigid_const_head_mismatch`
//!    (`tactic/equality/rewrite.rs`).
//!
//! The MUST-FAIL twin pins the other half of the contract: a genuinely
//! conflicting tactic-level equation (`u := 1` against a declared rigid `u`)
//! still refuses LOUDLY, with the same rigid-refusal message the declaration
//! layer uses (p39 discipline) — never a silent solve, never an opaque
//! Sort-param mismatch.
//!
//! # U2 stage 3 (2026-08-25) — the residual stage 1 left, and its pins
//!
//! Stage 1a seeded the ProofState's counter with a `u64` SNAPSHOT of the
//! ElabCtx's. That closes the aliasing across a whole tactic block but not
//! WITHIN one: both authorities then start at the same value `N`, and a
//! single tactic step mints on both — its term arguments through the ElabCtx
//! (`elaborate_exact_term` / `elaborate_refine_term` / a `have`'s term, each
//! polymorphic head constant minting one level per declared level param in
//! `elab_app`), its lemma instances on the ProofState (`mk_const`,
//! `resolve_env_rewrite_equation`). The first mid-block mint on each side was
//! therefore the same string `u_N`, and level identity IS that string.
//!
//! MEASURED at HEAD before the fix, builtin prelude, no Mathlib: eight tactic
//! scripts over a `.{u}`-polymorphic `pid`/`pid_eq` pair; seven double-minted
//! `u_3` and in every one of the seven the two authorities held DIFFERENT
//! values for it at the bridge exit —
//! `elabctx=S(0) proofstate=u` (the `have`'s `Nat` instance vs the `rw`
//! lemma's instance of the declared `u`), `elabctx=S(0) proofstate=v`, and
//! `elabctx=u_3 proofstate=S(0)` (the ElabCtx's still ABSTRACT, awaiting
//! generalization at declaration close, against a concrete tactic-side
//! solution — the silent-monomorphization direction). The bridge's exit
//! `ps.metas.instantiate_levels(&proof)` runs immediately after that point,
//! so it realizes the ProofState's value into every occurrence of the name,
//! including the ElabCtx's unrelated one. The same hazard existed with no
//! ElabCtx involved at all: `create_sub_proof_state` COPIED the counter, so a
//! `have h : T := by …` sub-state and its parent minted the same names and
//! the sub-proof term was spliced into the parent's proof.
//!
//! The fix is [`crate::level_mint::LevelMint`]: one monotone counter, shared
//! by handle across the bridge and across sub-proof-states. Two mints can no
//! longer produce the same id, so they can no longer produce the same name;
//! re-running the same instrumentation on the fixed elaborator reports ZERO
//! double-minted names on the same eight scripts.
//!
//! NO VERDICT FLIPPED, and the pins are shaped accordingly. All eight scripts
//! kernel-check before and after: every ElabCtx→ProofState handoff eagerly
//! `instantiate_levels` what it hands over, so an already-SOLVED ElabCtx level
//! is substituted away before it can be conflated (unsolved ones pass through
//! unchanged — `adopt_residual_elab_metas`, `elaborate_refine_term`'s
//! pending-goal types — which was the surviving exposure). So the pins below
//! are STRUCTURAL: they assert the identity property, not a verdict, because
//! the property is what a future refactor would silently lose while every
//! end-to-end fixture stayed green. The five measured shapes are pinned as
//! `tests/fixtures/universes/p45_bridge_mint_registry.lean` (a regression pin
//! on the shapes, not a flip pin). Soundness posture is unchanged throughout:
//! `verify_tactic_proof` and the mandatory decl-close kernel re-check stand
//! behind every accepted proof, so a conflation was always a LOUD reject or a
//! wrong monomorphization, never an unsound accept.
//!
//! To reproduce the measurement: `CLEAN_U2_MINT_TRACE=1` (see
//! `crate::u2_histogram::u2_mint_trace`) prints one line per mint with its
//! authority; a double-mint is the same `name=u_N` under both
//! `site=elabctx` and `site=proofstate` inside one block.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE_DIR: &str = "../../tests/fixtures/universes";

fn read_fixture(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(file);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// Elaborate every declaration of a fixture against the kernel prelude and
/// return `(declaration name, verdict)` per leaf, in source order. A verdict
/// is `Ok(())` only when the declaration registered — i.e. the kernel accepted
/// the elaborated term; otherwise it is the verbatim error rendering.
fn elab_fixture(file: &str) -> Vec<(String, Result<(), String>)> {
    let src = read_fixture(file);
    let decls = parse_file(&src).unwrap_or_else(|e| panic!("{file} must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        other => panic!("{file}: unexpected leaf {other:?}"),
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), ToString::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    verdicts
}

/// The eight p41 declarations, in source order: the two `.{u}`-polymorphic
/// helpers plus the six probes (rw cross-universe, apply, cases, two worlds,
/// the simp control that never regressed, and the same-universe rw). Every
/// one was a loud reject or a spurious `RewriteNoMatch` before the bridge
/// fix; all eight are kernel-accepted after it.
#[test]
fn test_tactic_bridge_level_identity_fixture_all_accepted() {
    let verdicts = elab_fixture("p41_tactic_bridge_level_identity.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            "pid",
            "pid_eq",
            "probe_rw",
            "probe_apply",
            "probe_cases",
            "probe_two_worlds",
            "probe_simp_control",
            "probe_rw_same",
        ],
        "p41: declaration set moved — update the expected list deliberately"
    );
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, v)| v.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "p41: {} of {} declarations rejected:\n{}",
        failures.len(),
        verdicts.len(),
        failures.join("\n")
    );
}

/// The MUST-FAIL twin: the helper registers, the probe refuses with the
/// rigid-refusal message — the exact fragment `scripts/u2_battery.sh` pins.
/// If the message degrades into a raw `Sort(Param(..))` mismatch, the bridge
/// has regressed to level-blind checking; if the probe ever PASSES, a rigid
/// enclosing universe was silently solved inside a tactic block.
#[test]
fn test_tactic_bridge_rigid_conflict_still_refuses_loudly() {
    let verdicts = elab_fixture("p42_tactic_bridge_rigid_refusal_MUST_FAIL.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["tsymm", "probe_rigid_conflict"],
        "p42: declaration set moved — update the expected list deliberately"
    );
    assert!(
        verdicts[0].1.is_ok(),
        "p42: the Type-monomorphic helper must register: {:?}",
        verdicts[0].1
    );
    let err = verdicts[1].1.as_ref().expect_err(
        "p42: probe_rigid_conflict must be REJECTED — a rung flipped it; update deliberately",
    );
    assert!(
        err.contains("cannot assign rigid universe parameter u := 1"),
        "p42: refusal lost its pinned rigid-refusal fragment; got: {err}"
    );
}

// =============================================================================
// U2 stage 3 — the level-mint registry: two mints cannot alias
// =============================================================================

/// Replicates the bridge entry exactly as `ElabCtx::elab_by_tactic` performs
/// it, then interleaves a mid-block mint on each side — the measured
/// collision shape.
///
/// BEFORE stage 3 this returned the SAME `Name` twice (measured: both `u_2`,
/// same `lean4_hash`). It must now return two different names, forever: level
/// identity is the `u_N` string, so an equal name IS an equal level, and the
/// two mints stand for unrelated things.
#[test]
fn test_stage3_bridge_mints_cannot_alias_by_name() {
    use crate::infer::ElabCtx;
    use crate::tactic::ProofState;

    use clean_kernel::{Environment, Expr};

    let env = Environment::with_prelude();
    let mut elab = ElabCtx::new(&env);
    elab.set_decl_universe_params(&[clean_parser::SurfaceName::generated_path("u")]);
    // Header elaboration mints before the `by` block is entered.
    let header = [elab.fresh_universe_param(), elab.fresh_universe_param()];

    // --- the bridge entry, verbatim from `elab_by_tactic` ---
    let mut ps = ProofState::with_context(env.clone(), Expr::prop(), Vec::new());
    let mut tactic_rigid = elab.metas.rigid_level_params_snapshot();
    for name in &elab.universe_params {
        tactic_rigid.insert(name.name().clone());
    }
    ps.seed_universe_world(
        elab.universe_params.clone(),
        elab.level_mint.clone(),
        tactic_rigid,
    );

    // --- mid-block: one mint from each authority, in each order ---
    let elab_first = elab.fresh_universe_param();
    let ps_first = ps.fresh_universe_param();
    let ps_second = ps.fresh_universe_param();
    let elab_second = elab.fresh_universe_param();

    let minted = [
        header[0].clone(),
        header[1].clone(),
        elab_first,
        ps_first,
        ps_second,
        elab_second,
    ];
    for (i, a) in minted.iter().enumerate() {
        for (j, b) in minted.iter().enumerate() {
            assert!(
                i == j || a != b,
                "U2 stage 3: mints {i} and {j} ALIAS ({a:?}) — the ElabCtx and the \
                 ProofState are minting from different counters again"
            );
        }
    }
}

/// The structural invariant behind the pin above: after the bridge seeds it,
/// the ProofState draws ids from the ENCLOSING ElabCtx's counter, not from a
/// copy of its value. `elab_by_tactic` carries the same statement as a
/// `debug_assert!`.
#[test]
fn test_stage3_bridge_shares_the_mint_handle_not_a_snapshot() {
    use crate::infer::ElabCtx;
    use crate::tactic::ProofState;
    use clean_kernel::{Environment, Expr};

    let env = Environment::with_prelude();
    let mut elab = ElabCtx::new(&env);
    let mut ps = ProofState::with_context(env.clone(), Expr::prop(), Vec::new());
    assert!(
        !ps.level_mint.shares_counter_with(&elab.level_mint),
        "a standalone ProofState owns its own counter until the bridge seeds it"
    );
    ps.seed_universe_world(
        elab.universe_params.clone(),
        elab.level_mint.clone(),
        elab.metas.rigid_level_params_snapshot(),
    );
    assert!(
        ps.level_mint.shares_counter_with(&elab.level_mint),
        "U2 stage 3: seed_universe_world must hand over the MINT HANDLE"
    );
    // A sub-proof-state (`have h : T := by …`, `conv`) inherits it too — that
    // path COPIED the counter before stage 3, so a sub-proof and its parent
    // minted aliasing names into one spliced proof term.
    let sub = crate::tactic::builtins_phase3d_elab::create_sub_proof_state(&ps, Expr::prop());
    assert!(
        sub.level_mint.shares_counter_with(&elab.level_mint),
        "U2 stage 3: a sub-proof-state must inherit the parent's mint handle"
    );
    let _ = elab.fresh_universe_param();
}

/// The semantic consequence the shared counter removes.
///
/// The bridge's exit path realizes the TACTIC side's level solutions into the
/// assembled proof (`ps.metas.instantiate_levels(&proof)`). Before stage 3
/// that walk could rewrite an ElabCtx-owned level that merely shared a name:
/// measured `elabctx=u_3 proofstate=S(0)`, i.e. a genuinely polymorphic
/// occurrence awaiting generalization, silently monomorphized to `Sort 0` by
/// an unrelated tactic-side solve. With one counter the ElabCtx's level is
/// not a name the ProofState can hold an opinion about, so the occurrence
/// survives unchanged.
#[test]
fn test_stage3_tactic_exit_realization_leaves_elabctx_levels_alone() {
    use crate::infer::ElabCtx;
    use crate::tactic::ProofState;

    use clean_kernel::{Environment, Expr, Level};

    let env = Environment::with_prelude();
    let mut elab = ElabCtx::new(&env);
    let _header = elab.fresh_universe_param();

    let mut ps = ProofState::with_context(env.clone(), Expr::prop(), Vec::new());
    let mut tactic_rigid = elab.metas.rigid_level_params_snapshot();
    for name in &elab.universe_params {
        tactic_rigid.insert(name.name().clone());
    }
    ps.seed_universe_world(
        elab.universe_params.clone(),
        elab.level_mint.clone(),
        tactic_rigid,
    );

    // The ElabCtx mints a level for a term argument and leaves it ABSTRACT;
    // the assembled proof carries that occurrence.
    let elab_level = elab.fresh_universe_param();
    let proof = Expr::sort(elab_level.clone());

    // The tactic side mints for an unrelated lemma instance and solves it.
    let ps_level = ps.fresh_universe_param();
    assert_ne!(
        elab_level, ps_level,
        "U2 stage 3 precondition: the two mints must not alias"
    );
    let Level::Param(ps_name) = ps_level else {
        panic!("fresh_universe_param must return a Level::Param");
    };
    ps.metas
        .add_level_constraint(ps_name, Level::zero())
        .expect("a tactic-minted param is not rigid and must be assignable");

    assert_eq!(
        ps.metas.instantiate_levels(&proof),
        proof,
        "U2 stage 3: the bridge exit realized a TACTIC solution into an \
         ELABCTX-owned level — the two are aliasing again"
    );
}
