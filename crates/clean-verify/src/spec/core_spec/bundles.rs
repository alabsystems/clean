// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Centralized bundle planner for core-spec registration order.
//!
//! The core-spec registration DAG is the heart of the formal specification.
//! This module encodes the ordered stage list once, with bundle membership
//! as data, so the three public builders (`add_core_spec`,
//! `new_substitution_test_spec`, `new_implementation_soundness_test_spec`)
//! delegate here instead of maintaining three hand-copied call lists.
//!
//! Part of #2913. See also #461 (active soundness lane), #2894, #2765.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// Which bundle of the core spec to build.
///
/// All variants exist in all builds. Only the subset builders that construct
/// `Substitution` and `ImplementationSoundness` are gated behind
/// `#[cfg(any(test, feature = "test-utils"))]` — the planner itself is
/// unconditional so the stage table is always fully compiled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CoreSpecBundle {
    /// All core registration stages — used by `Specification::new()`.
    Full,
    /// First 32 stages (foundation through substitution_def_eq), minus
    /// pi_injectivity — used by substitution/WHNF helper tests.
    // 2026-07-31: only the `any(test, feature = "test-utils")` subset builders
    // construct this variant (see the enum's own doc note), so a plain build
    // sees it as never constructed. Gated to match those builders exactly.
    #[cfg_attr(not(any(test, feature = "test-utils")), allow(dead_code))]
    Substitution,
    /// Full minus three late-stage omissions — used by implementation-soundness
    /// tests.
    #[cfg_attr(not(any(test, feature = "test-utils")), allow(dead_code))]
    ImplementationSoundness,
    /// Foundation types (Nat) + interval arithmetic only — used by interval
    /// arithmetic promotion tests. Part of #3362.
    #[cfg_attr(not(any(test, feature = "test-utils")), allow(dead_code))]
    IntervalArith,
    /// Foundation types (Nat/Bool/Eq) + the `EvalIR` trust-ir semantics stage
    /// only — used by the EvalIR tests and by the vacuity firewall's audit of
    /// the EvalIR relations (crystal job C3).
    ///
    /// EvalIR deliberately depends on nothing else: it carries its own list and
    /// option families rather than reusing the `expr_model` / `rec_env` ones, so
    /// this bundle is two stages and builds in a fraction of the full spec's
    /// time.
    EvalIr,
}

/// One stage in the ordered core-spec registration plan.
type CoreSpecStageApply = fn(&mut Specification) -> Result<(), SpecError>;

struct CoreSpecStage {
    /// Registration function to call on the specification.
    apply: CoreSpecStageApply,
    /// Whether this stage is included in the Substitution bundle.
    in_substitution: bool,
    /// Whether this stage is included in the ImplementationSoundness bundle.
    in_impl_soundness: bool,
}

/// The ordered core-spec registration plan.
///
/// Each stage appears exactly once, in dependency order. Bundle membership is
/// encoded per-stage so that adding a new stage requires editing one entry
/// instead of three separate builder functions.
///
/// Ordering constraints documented inline where they exist:
/// - Local check bridge must register before the app packet.
/// - Dispatch registers after app/lam/pi case wrappers.
/// - Global check theorem layers on top of the registered infer theorem.
const STAGES: &[CoreSpecStage] = &[
    // Foundation types: Eq, ProdType, Nat, Bool, AndType
    CoreSpecStage {
        apply: Specification::add_foundation_types,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_foundation_arith_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_foundation_arith_witnesses,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_foundation_arith_positivity,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_foundation_arith_transport,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Expression model: KExpr, lift, instantiate
    CoreSpecStage {
        apply: Specification::add_expr_model,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Recursor environment model (#2859 computational-iota/delta track, Increment B):
    // OptionType + RecRule/RecRules/RecMeta/RecEnv + option_some_inj. Additive
    // substrate for the computational iota_step; depends only on expr_model
    // (KExpr/Name) + foundation (Bool/Nat/Eq/Eq.cong).
    CoreSpecStage {
        apply: Specification::add_rec_env,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Computational iota_step substrate (#2859 track, Increment C): list/spine
    // helpers, then iota_reduct + iota_step + determinism. Depends on rec_env
    // (RecEnv/lookups) + expr_model (kapp_fn) + foundation (ListType/Nat/Bool).
    CoreSpecStage {
        apply: Specification::add_iota_step,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // ── church_rosser_whnf retirement track: the δ/env substrate is pulled EARLY
    // (before the reduction families) so the families can be tightened to pin their
    // operational step to the single distinguished env `the_red_env`. ──
    // Core δ substrate (DefEnv / defval_for / delta_reduct / delta_step graph);
    // needs only rec_env lookups + the iota_step substrate above. The δ keystones
    // that need the CPS inverter stay in the later add_delta_step stage.
    CoreSpecStage {
        apply: Specification::add_delta_step_core,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // RedEnv = RecEnv × DefEnv + red_rec / red_def projections (split out of
    // add_par_reduces_cd so it precedes the families). Needs RecEnv (add_rec_env)
    // + DefEnv (add_delta_step_core).
    CoreSpecStage {
        apply: Specification::add_red_env,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // REFLECTED FOUNDATION-CORE ENV (Front #1 Stage 2 artifact, now the
    // Stage-3 VALUE SUBSTRATE): kernel_core_red_env — the real kernel
    // environment's foundation core (19 recursors with their REAL RecMeta
    // counts + REAL rule rhss, level-erased; 50 real definition values)
    // mechanically reflected into a value-ful RedEnv literal by the
    // red_env_reflect generator, under three documented trust edges
    // (injective name interning / level erasure / coverage-with-skips ledger)
    // and pinned 1:1 to the live kernel env by
    // tests/kernel_core_red_env_fidelity.rs. Registers the generated def
    // script (kcre_nat_*/kcre_name_* atoms + the env term). MOVED EARLY (was
    // full-bundle-only after add_env_closed_checkers) for Front #1 Stage 3:
    // the_red_env (next stage) is now a value-level ALIAS of it, so every
    // bundle containing the_red_env must register the script first.
    // Dependencies are all earlier stages (RedEnv/RecEnv/DefEnv ctors,
    // KExpr/Name/Level/ListType, Nat/Bool). Census-neutral (value-ful
    // Definitions only).
    CoreSpecStage {
        apply: Specification::add_kernel_core_red_env,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // the_red_env: the single distinguished reduction env DefEq is relative to
    // (deletion-plan choice 3c). SWAPPED (Front #1 Stage 3): a value-level
    // alias of kernel_core_red_env (previous stage — the fidelity-gated
    // reflection of the real kernel foundation core) + two refl non-vacuity
    // witnesses regenerated against the REAL env (a Nat.rec iota fire on the
    // Nat.zero rule; a delta unfold of the outermost DefEnv entry). Needs
    // kernel_core_red_env (previous stage), RedEnv/red_rec/red_def
    // (add_red_env), DefEnv + delta_step (add_delta_step_core), iota_step
    // (add_iota_step), RecEnv ctors (add_rec_env). Placed here so the Brick-4
    // family tightening (later) can pin to it.
    CoreSpecStage {
        apply: Specification::add_the_red_env,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // RecEnvClosed faithful-interface predicate (#2859 track, Increment E):
    // every looked-up rule's rhs is closed (instantiate_at-invariant). E-core
    // consumes its projector. Depends only on rec_env (recrule_for/recrule_rhs)
    // + expr_model (instantiate_at) + foundation.
    CoreSpecStage {
        apply: Specification::add_rec_env_closed,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_discrimination,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_lam_discrimination,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_pi_discrimination,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Let-promotion discrimination/injectivity family (task #28): the
    // let_-headed no-confusion + component-recovery lemmas consumed by the
    // par-reduction inversion towers. Must precede add_par_reduction.
    CoreSpecStage {
        apply: Specification::add_expr_model_let_discrimination,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_lift_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_lift_compose,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_lift_shift,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_lift_shift_gen,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_subst_lift_gen,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Typing and definitional equality
    CoreSpecStage {
        apply: Specification::add_typing_universe_levels,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // δ/ι reduction witness families (delta_reduces / iota_reduces) run BEFORE
    // add_typing_def_eq: DefEq is now a genuine `add_inductive` whose `delta` /
    // `iota` constructors reference `delta_reduces` / `iota_reduces` in their
    // field types, so those inductives must already be in the env when the DefEq
    // inductive is elaborated. (Previously DefEq's type + non-δ/ι constructors
    // were hand-axioms registered first, and DefEq.delta/.iota/.rec were split
    // into a LATER `add_typing_def_eq_delta_iota_rec` stage precisely to bridge
    // this ordering gap; folding all of DefEq's constructors into one real
    // inductive removes that split — there were nine at the fold, twelve today
    // after zeta / let_cong / proj_cong joined.)
    // reduction_families only needs delta_step / iota_step /
    // the_red_env (all registered far earlier) — never Typing/DefEq — so the swap
    // is dependency-safe. Part of the DefEq inductive-encoding drain.
    CoreSpecStage {
        apply: Specification::add_typing_def_eq_reduction_families,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_typing_def_eq,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // iota_step -> iota_reduces bridge (#2859 track, Increment D): RecEnvWellformed
    // faithful-interface predicate + iota_step_to_reduces. Must run after
    // iota_reduces (reduction_families) + DefEq/Typing (typing_def_eq); iota_step
    // itself is registered earlier (add_iota_step).
    CoreSpecStage {
        apply: Specification::add_iota_step_bridge,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_typing_def_eq_delta_iota_rec,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_typing_def_eq_typed_support,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Derived rules and WHNF
    CoreSpecStage {
        apply: Specification::add_derived_rules,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_whnf_reduction,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_whnf_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // iota_reduct substitution-commutation substrate (#2859 track, Increment E):
    // list_map + instantiate_at_apply_spine + ... Must run after add_whnf_lemmas
    // (consumes instantiate_at_app/_const) and after add_iota_step (the spine
    // substrate + C.4-C.6 unfolds).
    CoreSpecStage {
        apply: Specification::add_iota_subst,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Const-head-guarded commutations (#2859 track, Increment E crux): kapp_fn /
    // kapp_args commute with instantiate_at on a const-headed (redex) spine.
    // After add_iota_subst (option_none_ne_some, list_map_append).
    CoreSpecStage {
        apply: Specification::add_iota_subst_const,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // E-core assembly (#2859 track, Increment E): iota_reduct_some_inv (the CPS
    // inverter) + iota_subst_commutes. After add_iota_subst_const (the const-head
    // commutes) + add_iota_subst (opt_bind_some_inv, list_map commutes).
    CoreSpecStage {
        apply: Specification::add_iota_core,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Computational delta_step substrate (#2859 track, Increment G): DefEnv +
    // defval_for + delta_reduct + delta_step + determinism + the CPS inverter
    // (delta_reduct_some_inv) + delta_step_head_none_absurd. The δ analogue of
    // iota_step; reuses the iota_step substrate (opt_bind/kapp_fn/kapp_args/
    // apply_spine/kexpr_const_name) + rec_env lookups (name_eqb/opt_pick) + the
    // CPS inverter machinery (opt_bind_some_inv/option_none_ne_some from
    // add_iota_subst), so it runs AFTER add_iota_core.
    CoreSpecStage {
        apply: Specification::add_delta_step,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Computational delta substitution/lift commutation substrate (#2859 track,
    // Increment G): DefEnvClosed / DefEnvLiftClosed faithful interfaces + the
    // delta reduct equations (delta_reduct_inst_eq / delta_reduct_lift_eq) + the
    // delta E-core keystones (delta_subst_commutes / delta_lift_commutes). The δ
    // analogue of iota_subst_commutes / iota_lift_commutes; reuses the landed
    // inst/lift apply_spine + kapp_args + const-name-survival substrate from
    // add_iota_subst / add_iota_subst_const / add_iota_core, so it runs AFTER
    // add_delta_step (DefEnv/defval_for/delta_reduct/delta_reduct_some_inv) and
    // AFTER add_iota_core (the commutation substrate + opt_bind_some_intro).
    CoreSpecStage {
        apply: Specification::add_delta_subst,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // lift_instantiate_swap (gap form, #2859 Wave 129): the load-bearing
    // lift/substitution interchange for the iota-free confluence skeleton.
    // Must precede add_par_reduction because the latter's par_lift_bd proof
    // term (Wave 130) references lift_instantiate_swap. Its own dependencies
    // (instantiate_at_app/lam/pi from add_whnf_lemmas, lift_at_app/lam/pi from
    // the structural lift lemmas, lift_at_lift_at_exchange from
    // add_expr_model_subst_lift_gen, and the foundation arith positivity
    // helpers) are all registered in earlier stages, so this slot is sound.
    CoreSpecStage {
        apply: Specification::add_expr_model_lift_instantiate_swap,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Pi injectivity (add_pi_injectivity_def_eq) is MOVED to after
    // add_par_reduces_cd_sound (church_rosser_whnf retirement): it is re-pointed
    // through the confluence route (join_to_def_eq ∘ par_cd_pi_injectivity ∘
    // def_eq_joinable), so it must follow that machinery. add_pi_injectivity_confluence
    // (which defined the deleted church_rosser_whnf + pi_def_eq_eq) is retired.
    // Lift cancellation and substitution interchange
    CoreSpecStage {
        apply: Specification::add_expr_model_lift_cancel,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // de Bruijn keystone (Stage-0 Brick 1): bvar_ceiling + inst_above_ceiling_id
    // (instantiate_at is the identity above the free-variable ceiling). Placed
    // AFTER add_expr_model_lift_cancel and after foundation_arith_positivity /
    // iota_core / expr_model / whnf_lemmas so all deps exist (Le helpers from
    // iota_core, nat_sub_pos_succ / nat_pos_witness_from_succ_eq from
    // foundation_arith_positivity, instantiate_at_* unfoldings from whnf_lemmas,
    // instantiate_bvar_at_below from expr_model). Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_expr_model_inst_ceiling,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // General instantiate-after-lift cancellation (additive de Bruijn brick):
    // instantiate_lift_cancel_general (+ _bvar helper). Placed right after
    // add_expr_model_inst_ceiling: every dependency exists by here — the
    // lift/instantiate constructor unfoldings (expr_model / whnf_lemmas /
    // expr_model_lift_lemmas), the bvar reducers instantiate_bvar_at_above /
    // _below / lift_at_bvar_geq / _below (expr_model / bvar_cases), and the Nat
    // arith toolbox (foundation_arith_positivity/transport/witnesses:
    // nat_sub_zero_of_sub_pos, nat_sub_zero_succ_gap_to_add,
    // nat_sub_zero_add_monotone, nat_sub_pos_witness, nat_sub_pos_add_right,
    // nat_add_assoc, nat_succ_add, nat_add_succ_right, nat_sub_succ_one). Purely
    // additive — nothing downstream consumes it yet — so the slot is unconstrained
    // beyond dependency availability. Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_expr_model_instantiate_lift_cancel_general,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_subst_lift_interchange,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_subst_lift_interchange_bvar_helpers,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_subst_lift_interchange_bvar_cases,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_subst_lift_interchange_bvar,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_expr_model_subst_lift_interchange_gen,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Substitution commutation and def-eq bridge
    CoreSpecStage {
        apply: Specification::add_substitution_commutation_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_substitution_commutation_nested_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Parallel reduction (#2859 Packet 1): par_reduces inductive +
    // beta_reduces_star + subsumption lemmas, and the iota-free Route B
    // confluence skeleton (par_reduces_bd, par_lift_bd, par_subst_refl_bd,
    // par_subst_bd). Placed AFTER the substitution-commutation lemmas because
    // par_subst_bd's beta/let_ contraction arms consume
    // instantiate_nested_commutes_zero_subst (from
    // add_substitution_commutation_nested_lemmas), and par_lift_bd consumes
    // lift_instantiate_swap. Nothing in the intervening stages references
    // par_reduces, so this relocation is sound.
    CoreSpecStage {
        apply: Specification::add_par_reduction,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Computational parallel-reduction sibling (#2859 track, Increment F):
    // par_reduces_c (iota ctor carries iota_step) + par_strips_witness_c +
    // par_strips_iota_iota_c (the (iota,iota) determinism join). After
    // add_par_reduction (forall_/let_/instantiate) + add_iota_step (iota_step,
    // iota_step_deterministic).
    CoreSpecStage {
        apply: Specification::add_par_reduces_c,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // δ-extended computational parallel reduction par_reduces_cd (#2859 track,
    // Increment H): RedEnv = RecEnv × DefEnv product + red_rec/red_def projections,
    // the RecEnvDefEnvDisjoint name-disjointness faithful interface (mirror of
    // RecEnvCtorRecDisjoint), the 11-ctor par_reduces_cd relation (the 10
    // par_reduces_c ctors over red_rec env + a delta ctor carrying delta_step
    // (red_def env)) + par_strips_witness_cd + the (δ,δ) determinism cross-join.
    // After add_par_reduces_c (par_strips pattern) and add_delta_subst (DefEnv /
    // defval_for / delta_step / delta_step_deterministic).
    CoreSpecStage {
        apply: Specification::add_par_reduces_cd,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // delta_step -> delta_reduces faithful-interface bridge (church_rosser_whnf
    // retirement track): DefEnvWellformed (the δ mirror of RecEnvWellformed) +
    // delta_step_to_reduces (the δ analogue of iota_step_to_reduces). Indexed by
    // RedEnv (reads red_def env), so it MUST run after add_par_reduces_cd
    // (RedEnv / red_def). Consumes delta_step (add_delta_step) + delta_reduces.mk
    // (add_typing_def_eq_reduction_families) + DefEq/Typing/instantiate_at, all
    // registered in earlier stages.
    CoreSpecStage {
        apply: Specification::add_delta_step_bridge,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Env-GENERIC iota/delta DefEq rules from wellformedness (Stage-0 Brick 2):
    // DefEq.iota_gen / DefEq.delta_gen. Additive (new DerivedProved decls, zero
    // axioms). Specializes WF_SUBST (projected from the carried RecEnvWellformed /
    // DefEnvWellformed) down to a bare DefEq e e' by instantiating at a depth above
    // both bvar ceilings, where the Brick-1 keystone inst_above_ceiling_id collapses
    // the instantiation. Placed RIGHT AFTER add_delta_step_bridge: every dependency
    // (add_expr_model_inst_ceiling keystone/bvar_ceiling/le_add_self_right;
    // add_iota_step_bridge RecEnvWellformed; add_delta_step_bridge DefEnvWellformed;
    // add_typing_def_eq DefEq; add_iota_step / add_delta_step_core / add_red_env;
    // add_iota_core le_add_self_left) is an earlier stage, and the brick needs
    // NOTHING from the later par_reduces confluence lane — so it sits before it.
    // Full bundle only (no consumers in the subset bundles yet); the dedicated
    // build_defeq_iota_delta_gen_prefix builder validates it in isolation.
    CoreSpecStage {
        apply: Specification::add_defeq_iota_delta_gen,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // PROPER (Takahashi) parallel reduction par_reduces_p (#2859 Increment F+):
    // the parallel-iota sibling whose iota ctor bakes in subterm reduction, giving
    // the STRONG single-step diamond. After add_par_reduces_c (par_reduces_c +
    // par_reduces_c_star + the _star congruences the embeddings consume).
    CoreSpecStage {
        apply: Specification::add_par_reduces_p,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Complete development cd (#2859 Increment F+): the Takahashi `*` operation the
    // strong single-step diamond's triangle needs. Structural KExpr.rec; only needs
    // iota_reduct/instantiate (earlier stages).
    CoreSpecStage {
        apply: Specification::add_complete_development,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // par_reduces_p0 (#2859 Increment G, the literal-scrutinee development track): the
    // in-tree analogue of the blueprint's Par0 — a sibling of par_reduces_p whose iota
    // constructor fires on the LITERAL source redex (matching dev0), so the development
    // triangle dev0_triangle has no fire-vs-development iota wall (design §18). After
    // add_complete_development (needs dev0) and add_par_reduces_p (needs par_reduces_p +
    // the iota commutation lemmas iota_lift_commutes / iota_subst_commutes).
    CoreSpecStage {
        apply: Specification::add_par_reduces_p0,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // topIotaStar head-iota developer (#2859 Increment F+++, the corrected
    // confluence-route port of the verified app-spine blueprint onto
    // par_reduces_p): topIotaStar (single-fire collapse of the blueprint's
    // head-iota chain firer) + the RecEnvReductNotRedex faithful interface (a
    // carried hypothesis, NOT an axiom — the reduct is never itself a top redex)
    // + par_topIotaStar / topIotaStar_no_redex / topIotaStar_step. The chain
    // absorbers the open iota_p arm of cd_triangle consumes. After
    // add_par_reduces_p0 (needs opt_default/cd substrate, par_reduces_p.iota_p,
    // iota_step/iota_reduct).
    CoreSpecStage {
        apply: Specification::add_par_reduces_p_topdev,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // MARKED / fuel-counted parallel reduction par_reduces_pL (#2859 Increment F++,
    // the Tait–Martin-Löf labeled-development crack of the double-iota wall): a
    // Nat-fuel-indexed sibling of par_reduces_p whose fuel COUNTS the contractions
    // (beta+iota fires) in the derivation — the decreasing measure the unlabeled
    // cd_triangle iota arm provably lacks. After add_complete_development (needs
    // par_reduces_p + iota_step + Nat.add).
    CoreSpecStage {
        apply: Specification::add_par_reduces_p_marked,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // STEP-5 (#2859 church_rosser_whnf-deletion): pi shape-inversion + injectivity
    // tower for par_reduces_p / par_reduces_p_star (verbatim p-side mirror of the
    // Wave-142/143 _bd tower). After add_complete_development (par_reduces_p_lam_inv
    // + its prerequisite shapes) and add_par_reduces_p (par_reduces_p_star substrate
    // + par_strips_witness_p_star). Independent of the marked/keystone work.
    CoreSpecStage {
        apply: Specification::add_par_reduces_p_injectivity,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // PROPER (Takahashi) 3-way (β+ι+δ) parallel reduction par_reduces_pd (#2859
    // Increment H+, delta increment Stage 3): the parallel-iota/parallel-delta
    // sibling of par_reduces_cd over RedEnv, whose iota_p / delta_p ctors bake in
    // the subterm reduction (the route to the strong 3-way diamond). Layer 1: the
    // relation + par_reduces_pd_star + the join witnesses + basic combinators + the
    // par_reduces_cd ⊆ par_reduces_pd embedding. After add_par_reduces_p_topdev (the
    // whole β+ι development) and add_par_reduces_cd (RedEnv / red_rec / red_def /
    // par_reduces_cd) and add_delta_step (delta_step (red_def env)).
    CoreSpecStage {
        apply: Specification::add_par_reduces_pd,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // δ-ONLY single-position reduction delta_cong + delta_cong_star (#2859 Increment
    // H++, delta increment Stage 4, the HINDLEY-ROSEN redirect): the `→₂` of the
    // Hindley-Rosen route to β+ι+δ Church-Rosser. The congruence closure of the
    // deterministic head step delta_step (red_def env); ORTHOGONAL, so its single-step
    // diamond is direct (no developer, no topDeltaStar, no WF-recursion — sidestepping
    // the Stage-3 combined-diamond wall). Layer 1: the relation + RT-closure + join
    // witness + the two basic combinators. After add_par_reduces_pd (RedEnv / red_rec /
    // red_def / delta_step / the par_strips_witness pattern).
    CoreSpecStage {
        apply: Specification::add_par_reduces_d,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // δ CONFLUENCE via Huet strong confluence (#2859 Increment H++, delta increment
    // Stage 4, the HINDLEY-ROSEN redirect): par_strong_join_d (the SC join witness,
    // mirror of par_strong_join_c) + delta_strips_semi_strip_of_strong (the semi-strip,
    // parameterized on the SC hypothesis) + delta_cong_star_diamond_of_strong (THE
    // tiling brick: SC ⟹ delta_cong_star Church-Rosser). Verbatim δ mirror of the
    // c-track strong-confluence tiling (par_reduces_c.rs); reduces δ CR to exactly the
    // single-step strong diamond of delta_cong. After add_par_reduces_d (delta_cong /
    // delta_cong_star / delta_cong_star_trans / delta_cong_subsumes_star /
    // par_strips_witness_d_star).
    CoreSpecStage {
        apply: Specification::add_par_reduces_d_conf,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // δ single-step STRONG diamond delta_cong_diamond + the UNCONDITIONAL δ CR
    // delta_cong_star_diamond (#2859 Increment H++, delta increment Stage 4). Proves
    // the SC obligation that add_par_reduces_d_conf left as a bound hypothesis (the
    // single-step strong diamond of delta_cong, by structural KExpr.rec on the term)
    // and feeds it into delta_cong_star_diamond_of_strong to land δ Church-Rosser
    // unconditionally. After add_par_reduces_d_conf (par_strong_join_d + its nine
    // congruence lifts (incl. the let_t/let_v/let_b trio, task #28) +
    // delta_step_app_inv + delta_cong_star_diamond_of_strong).
    CoreSpecStage {
        apply: Specification::add_par_reduces_d_diamond,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Abstract HINDLEY-ROSEN tiling par_reduces_cd_hr (#2859 Increment H++, delta
    // increment Stage 4 — Hindley-Rosen assembly): the macro-step relation m_step
    // (= par_reduces_c_star ∪ delta_cong_star) + m_star + the join witnesses + the
    // abstract combinators m_diamond_of / m_strip_of / mstar_confluent_of, each
    // parameterized on the three corner join-lemmas (β+ι CR / δ CR / the β+ι/δ
    // commutation) as BOUND HYPOTHESES (not axioms). Composes into the 3-way β+ι+δ
    // Church-Rosser. After add_par_reduces_d_diamond (par_reduces_c_star /
    // delta_cong_star / par_strips_witness_c_star / par_strips_witness_d_star /
    // par_reduces_c_star_diamond / delta_cong_star_diamond).
    CoreSpecStage {
        apply: Specification::add_par_reduces_cd_hr,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // β+ι/δ COMMUTATION star-tiling par_reduces_cd_commute (#2859 Increment H++, delta
    // increment Stage 4 — Hindley-Rosen assembly): the single-step strong-commutation
    // witness par_delta_sc_witness + the two-level tiling par_delta_commute_one_of_sc /
    // par_delta_commute_of_sc (blueprint commute_one / commute), each parameterized on
    // the single-step strong commutation SC as a BOUND HYPOTHESIS. Isolates the β+ι/δ
    // commutation (the COMM corner) to exactly the single-step SC. After
    // add_par_reduces_cd_hr (par_delta_commute_witness).
    CoreSpecStage {
        apply: Specification::add_par_reduces_cd_commute,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Hindley-Rosen closure-coincidence SANDWICH + composition par_reduces_cd_hr_compose
    // (#2859 Increment H++, delta increment Stage 4 — Hindley-Rosen assembly): the
    // macro congruences m_star_{app,lam,pi}, the two-direction sandwich (m_star ↔
    // par_reduces_cd_star), and par_reduces_cd_star_diamond_of_commute — the 3-way
    // (β+ι+δ) Church-Rosser modulo the commutation (discharges the landed β+ι/δ CRs,
    // carries the commutation as the sole bound hypothesis). After
    // add_par_reduces_cd_hr (the abstract combinators).
    CoreSpecStage {
        apply: Specification::add_par_reduces_cd_hr_compose,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // cd-relation JOIN-WITNESS -> INJECTIVITY (I-half) par_reduces_cd_injectivity
    // (#2859 church_rosser_whnf-deletion): the pi/lam/sort shape-inversion + injectivity
    // tower over par_reduces_cd / par_reduces_cd_star — mirrors the landed p-side
    // par_p_pi_injectivity_* onto the δ-carrying cd relation (needed because the p-side
    // I-half does NOT compose with the cd-relation CR, cd carrying δ). The structural
    // confluence CONSEQUENCE half (join witness -> injectivity), NOT soundness-sensitive.
    // After add_par_reduces_cd_hr_compose (par_strips_witness_cd_star) and
    // add_par_reduces_pd (par_reduces_cd_star + trans + par_subsumes_par_cd_star).
    CoreSpecStage {
        apply: Specification::add_par_reduces_cd_injectivity,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // delta-SUBSTITUTION TOWER par_reduces_delta_sc (#2859 Increment H++, delta
    // increment Stage 4 — Hindley-Rosen assembly): brick 1 of the single-step strong
    // commutation SC (= par_delta_sc). delta_lift_cong / delta_subst_cong /
    // delta_substStar_body — the congruence lemmas lifting the directed delta
    // commutation keystones (delta_subst_commutes / delta_lift_commutes) over
    // delta_cong / delta_cong_star. After add_par_reduces_d (delta_cong /
    // delta_cong_star) and add_delta_subst (delta_subst_commutes / delta_lift_commutes).
    CoreSpecStage {
        apply: Specification::add_par_reduces_delta_sc,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // ι×δ COMMUTATION par_reduces_iota_delta (#2859 Increment H++, delta increment
    // Stage 4 — Hindley-Rosen assembly): the iota arm of the single-step strong
    // commutation par_delta_sc. Brick A = the delta_cong_star_list spine machinery
    // (apply_spine_delta_cong_star, list_{tail,drop,take}_delta_cong, kapp_args_delta_cong),
    // verbatim δ* mirrors of the par_reduces_c_list spine congruences. After
    // add_par_reduces_delta_sc (delta_cong_star_app / the δ-subst tower) and
    // add_par_reduces_cd (the (δ,ι) disjointness primitives).
    CoreSpecStage {
        apply: Specification::add_par_reduces_iota_delta,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // REAL-ENV DISCHARGE (Bricks R0 + R1, church_rosser_whnf/def_eq_to_eq
    // metatheory becoming UNCONDITIONAL): the FAITHFUL kernel-environment model
    // faithful_red_env (real recursor metadata + closed-lambda rule rhs + a real
    // definition; non-vacuous — iota + delta fire) and the three cheapest faithful
    // interfaces over it (i2 RecEnvCtorNoRecMeta, i7 RecEnvDefEnvDisjoint, i8
    // RecEnvCtorNoDefVal), discharged as real DerivedProved name-disjointness terms
    // (zero new axioms). Also registers the confluence-independent decidable-name-
    // equality soundness tower (name_eqb_eq) it consumes. After
    // add_par_reduces_iota_delta (RecEnvCtorNoDefVal) — and so after rec_env_closed
    // (RecEnvCtorNoRecMeta) and par_reduces_cd (RecEnvDefEnvDisjoint) — and after
    // add_iota_subst (option_none_ne_some / opt_bind_some_inv).
    CoreSpecStage {
        apply: Specification::add_faithful_red_env,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // ENV-CLOSURE CHECKERS (Front #1 Stage 1, the_red_env discharge program):
    // the Bool closure checkers (rec_env_closed_b / rec_env_lift_closed_b /
    // def_env_closed_b / def_env_lift_closed_b + the rec_rules_closed_b leg)
    // and the GENERIC checker-soundness lemmas (*_of_b) that convert
    // `checker env = true` into RecEnvClosed / RecEnvLiftClosed / DefEnvClosed
    // / DefEnvLiftClosed for ANY env — so a concrete env discharges each
    // closure interface by a single Eq.refl Bool Bool.true (the kernel
    // whnf-evaluates the checker fold). Plus the both-toys regression demo
    // (the_red_env AND faithful_red_env, all four interfaces each). AFTER
    // add_faithful_red_env: consumes its decidable-eq tower
    // (nat_eqb_eq/band_eq_true_left/right) + opt_pick_some_inv, the keystones
    // inst_above_ceiling_id/lift_ceiling_id (add_expr_model_inst_ceiling),
    // le_zero_n (add_iota_core), opt_bind_some_inv/option_none_ne_some
    // (add_iota_subst), the interfaces (add_rec_env_closed / add_delta_subst),
    // and both toy envs (add_the_red_env / add_faithful_red_env). Purely
    // additive; ZERO new axioms (census stays 11); all lemmas DerivedProved
    // with empty closures.
    CoreSpecStage {
        apply: Specification::add_env_closed_checkers,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // (Front #1 Stage 3 NOTE: add_kernel_core_red_env used to sit HERE as a
    // full-bundle-only parallel constant; it is MOVED EARLY — immediately
    // before add_the_red_env — because the swapped the_red_env is now a
    // value-level alias of it.)
    // Strong normalization of the IOTA-FREE beta relation beta_reduces_bd for
    // well-typed terms (the beta-only leg of whnf_terminates_well_typed; the
    // kernel-checked port of proofs/lean-aristotle/beta_sn_kexpr.lean). Purely
    // additive, zero new axioms, all DerivedProved with empty debt. Placed
    // right after add_faithful_red_env because it reuses the decidable-eq
    // tower's nat_add_eq_zero_left/right; its other dependencies —
    // beta_reduces_bd (add_par_reduction), bvar_ceiling/inst_above_ceiling_id
    // (add_expr_model_inst_ceiling), nat_strong_rec/lt_trans/size_*/le_zero_n
    // (add_iota_core), Typing.rec (add_typing_def_eq_typed_support), expr_size
    // (add_whnf_reduction) — are all earlier stages in both subset bundles.
    // Nothing downstream consumes it yet.
    CoreSpecStage {
        apply: Specification::add_beta_bd_sn,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // MODEL-side WHNF progress / exit-shape brick (Front-2 recursive-grounding
    // FIRST BRICK): whnf_progress_bd — every const-free bvar-free KExpr exposes a
    // whnf exit (is_whnf value / iota-free beta_reduces_bd step / stuck non-lambda
    // application). The PROGRESS mirror of the landed add_beta_bd_sn TERMINATION,
    // so it is placed immediately after it. Reuses is_whnf/is_neutral
    // (add_whnf_reduction), KExpr/KExpr.rec (add_expr_model), bvar_ceiling
    // (add_expr_model_inst_ceiling), beta_reduces_bd (add_par_reduction),
    // nat_zero_ne_succ (add_iota_core), nat_add_eq_zero_left (add_faithful_red_env),
    // Empty/AndType (foundation layer) — all earlier stages. Purely additive; zero
    // new axioms; all DerivedProved with empty debt. Nothing downstream consumes it
    // yet. The naive 2-shape progress is FALSE on this fragment (app (sort 0)(sort 0)
    // is const-free, bvar-free, not is_whnf, and takes no step), so the witness
    // carries an explicit, honestly-named `stuck` exit.
    CoreSpecStage {
        apply: Specification::add_whnf_progress,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // MODEL-side WHNF normalization brick (Front-2 recursive-grounding, T3): the
    // completion of the exit-shape spec the future literal whnf VC cites.
    // whnf_normalizes_bd composes the landed PROGRESS half (whnf_progress_bd,
    // above) with the landed TERMINATION half (beta_bd_sn_has_type,
    // add_beta_bd_sn) via beta_bd_acc.rec: a well-typed const-free term reduces
    // (zero-or-more iota-free beta_reduces_bd steps) to a WHNF-OR-STUCK normal
    // form (beta_bd_normal = is_whnf OR whnf_stuck_head, in the stuck-aware
    // closure beta_bd_to). Placed immediately after add_whnf_progress since it
    // consumes both it and add_beta_bd_sn. Also registers const_free_preserved_bd
    // (a bd step keeps a const-free bvar-free term const-free, mirroring
    // beta_bd_step_preserves_ceiling_zero) and the closure cons
    // whnf_normalizes_prepend. Reuses is_whnf (add_whnf_reduction),
    // beta_reduces_bd (add_par_reduction), AndType/Eq.subst/Eq.substType/Eq.symm
    // (foundation layer), nat_add_eq_zero_left/right (add_faithful_red_env) — all
    // earlier stages. Purely additive; zero new axioms; all DerivedProved with
    // empty debt. HONEST: the normal form is WHNF-OR-STUCK, not a bare is_whnf
    // (app (sort 0)(sort 0) is a stuck normal form; concluding is_whnf would be
    // false). Nothing downstream consumes it yet.
    CoreSpecStage {
        apply: Specification::add_whnf_normalizes,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // whnf_terminates_well_typed RETIREMENT: converts the census axiom
    // (has_type e T -> terminates_whnf e, formerly whnf_lemmas.rs) into a genuine
    // DerivedProved theorem. Placed AFTER add_whnf_normalizes because it consumes
    // const_free_preserved_bd from that stage (plus const_free / whnf_progress from
    // add_whnf_progress, beta_bd_acc / beta_bd_sn_has_type / typable_bvar_ceiling_zero
    // / beta_bd_step_preserves_ceiling_zero from add_beta_bd_sn, the reverse step
    // bridges delta/iota_reduces_to_step from add_delta_step_bridge /
    // add_iota_step_bridge, and the head-none absurdities
    // iota_step_head_none_absurd_type / delta_step_head_none_absurd_type from
    // add_par_reduces_c / add_par_reduces_d_diamond — all earlier stages). The FULL
    // whnf_step = beta_reduces ∪ delta_reduces union is discharged: on the spec's
    // context-free (bvar-free + const-free) Typing fragment the δ and ι legs are
    // vacuous and each β step strictly shrinks, so accessibility transports off the
    // landed beta_bd_acc. HONEST: SN for the DEGENERATE context-free has_type — a
    // genuine proof of the axiom AS STATED, NOT full dependent-CIC SN. Purely
    // additive; REMOVES one census axiom (64 -> 63).
    CoreSpecStage {
        apply: Specification::add_whnf_terminates_well_typed,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // BRICK 2 (fidelity re-architecture): the rich-model dependent judgment
    // `TypingCtx` (context-indexed, WITH de Bruijn `var` + `const` rules) + its
    // `ctx_lookup` + non-vacuity witnesses. Registered ALONGSIDE (not replacing)
    // the degenerate `Typing` above, so the census-16 degenerate SN lane stays
    // green. Depends only on expr_model (KExpr/lift_at/instantiate),
    // typing_universe_levels (imax_nat) and foundation types — all far-earlier
    // stages — so it may sit anywhere after them; placed here to keep the fidelity
    // work adjacent to the SN lane it will eventually re-state. Census-NEUTRAL:
    // add_inductive lowers to Inductive/Constructor/Recursor, no new axioms. See
    // designs/2026-07-06-fidelity-rearchitecture.md.
    //
    // Nat.rec OBJECT prefix (task #30, Batch 0 ordering split): names/consts/
    // recursor-type/natREnv/natRecApp/NatRecContract/NatRecEnvOK, moved AHEAD of
    // add_dependent_sn_richmodel so the CandModel redNatRec field (N3/N4, added in
    // add_dependent_sn_richmodel) can reference them. Consumes only early stages
    // (add_rec_env, add_iota_step); the relation/β-chain half stays in add_natrec
    // (later, needs the psubst calculus). Census-NEUTRAL pure reorder.
    CoreSpecStage {
        apply: Specification::add_natrec_objects,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // SnSchema OBJECT prefix (task #32, Brick 1): the signature-schema leaf
    // layer (sigNat/sigLength, generic names/consts/motive/metadata) + the
    // rfl-at-Nat validation bridges. Placed AFTER add_natrec_objects so the
    // *_nat bridges can reference natName/…/natRecMeta; before
    // add_dependent_sn_richmodel (no CandModel dependency in Brick 1).
    // Census-neutral (all defs; Eq.refl bridges have foundational-only closure).
    CoreSpecStage {
        apply: Specification::add_snschema_objects,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // W-type (Acc / higher-order fields) OBJECT prefix: names/consts/types/
    // rule-rhs/wREnv/wRecApp/wContractum/WRecContract/WFresh/WRecEnvOK + the rfl
    // validations, moved AHEAD of add_dependent_sn_richmodel so a CandModel
    // redRecW field can reference them — the stage-ordering prerequisite for
    // W-type recursor adequacy (acc_wtype.rs previously deferred it). Same idiom
    // as add_natrec_objects / add_snschema_objects; consumes only expr_model,
    // rec_env, iota_step and delta_step. Census-NEUTRAL pure reorder.
    CoreSpecStage {
        apply: Specification::add_acc_wtype_objects,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Mutual-block OBJECT layer, split out of add_mutual_schema (which stays
    // late at its old slot) and moved AHEAD of add_dependent_sn_richmodel so a
    // CandModel redRecMut field can reference mutRecApp / MutFresh /
    // MutRecEnvOK / MutRecContract. Same idiom as the three *_objects stages
    // above. Mechanical dependency check: max external stage consumed is 76
    // (add_snschema_objects), nothing at >= 78. Census-NEUTRAL pure reorder.
    CoreSpecStage {
        apply: Specification::add_mutual_schema_objects,
        in_substitution: true,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_dependent_sn_richmodel,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Stratified Hurkens/Girard BLOCK (stratified_hurkens_block.rs): port of
    // the corpus rung Stratified/Blocking.lean to the reflected CONV-FREE
    // TypingCtx — Hurkens' powerful universe U0 exists one (semantic) level up
    // (typingctx_U0_formable + hk_level_val pins) and can NEVER be small
    // (typingctx_U0_not_small), by structural rule inversion + Level-literal
    // no-confusion (the pi rule's conclusion carries a literal Level.imax,
    // never Level.zero; level_imax_ne_zero). Consumes only earlier stages:
    // foundation types (Eq/Nat/Empty/OptionType/ListType/Name), expr_model
    // (KExpr/Level/lift_at/instantiate), typing_universe_levels
    // (imax_nat/sort_universe_consistency), whnf_progress (ConstFreeUnit) and
    // TypingCtx/ctx_lookup (add_dependent_sn_richmodel, directly above). The
    // TypingCtxConv variant is NOT covered — it needs the DefEq-level sort
    // no-confusion (def_eq_joinable + par_cd_sort_injectivity under a
    // RedEnvFaithful discharge), which registers at later stages. Census-
    // NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_stratified_hurkens_block,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R0 (candmodel_construct_r0.rs): the
    // candidate-SET interface IsCandSet (AndType-packaged cr1/cr2/cr3 over an
    // arbitrary S : KExpr -> Type), its base instance isCand_whnfAcc (the
    // whole-SN set), the floor cand_var_mem (every variable in every candidate
    // set), and the two hand-registered discriminating witnesses of
    // designs/2026-08-23-spec-candmodel-port.md §6.1 — cand_var_witness
    // (whnf_acc (bvar 0) THROUGH the cr3 face) and cand_excludes_omega (no
    // candidate set contains the untyped self-application loop omegaLoop,
    // which beta-steps to itself; cr1 genuinely excludes). Port of
    // Stratified/Cand.lean IsCand/isCand_SN/IsCand.var_mem (rung
    // stratified-sn). NOT a CandModel instance and no claim on the M
    // hypothesis: IsCandSet deliberately has no red_sort/pi_elim/... faces.
    // Consumes only earlier stages: foundation types (Eq/Nat/Empty/AndType),
    // expr_model (KExpr/Level/instantiate), whnf_reduction
    // (beta_reduces/whnf_step/whnf_acc), whnf_progress (ConstFreeUnit) and
    // Neutral/no_whnf_step_bvar (add_dependent_sn_richmodel). Census-NEUTRAL:
    // every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r0,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R1 (candmodel_construct_r1.rs): the Tait
    // head-expansion ENGINE layer. The beta engine candExp_beta — any
    // candidate set is closed under beta-expansion at the (Neutral) redex
    // app (lam ty b) a, with the contractum-family premise of
    // CandModel.redAbstraction extended over betaStar developments of the
    // body (the honest R1 interface: the corpus's single-contractum spelling
    // needs iota-under-psubst substitution transport over the real env, an
    // R2+ build item) — plus the zeta engine whnfAcc_zeta_expand at the base
    // whole-SN set, the app-/lam-/let-headed CPS step inversions they run on
    // (15-arm beta_reduces.rec + whnf_step.rec wrappers; head-iota/delta arms
    // killed computationally via kexpr_const_name (kapp_fn ..) = none), the
    // betaStar/whnfStar closures, and the §6.1 discriminating witnesses:
    // candExp_beta_base_witness (a concrete redex through the engine),
    // appOmega_arg_acc_necessary (contractum acc, redex NOT acc — the
    // argument premise is load-bearing), and zeta_expansion_not_generic (the
    // let_-headed engine of candExp_beta's EXACT shape is REFUTED via the
    // reachability-complement candidate set zetaGuardSet — Neutral (let_) =
    // Empty is a real loss, not a spelling choice). Port of Stratified/
    // Cand.lean candExp + LetDeltaSN reducible_letE_expand (design §5 R1).
    // Consumes only earlier stages: R0 (IsCandSet/whnfAcc_inv_step/omega),
    // dependent_sn_richmodel (Neutral/no_whnf_step_bvar/whnfAcc_sort),
    // discrimination + inj lemmas, iota/delta bridges + head-none absurdities,
    // lift_at_amount_zero, whnf_reduction, whnf_progress, expr_model.
    // Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r1,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R2 (candmodel_construct_r2.rs): the
    // delta/const head-expansion engine candExp_delta — any candidate set
    // absorbs a bare const whose the_red_env delta-unfolding lands in the set
    // (cr3 at the NEUTRAL const + the complete reduct classification
    // constRedex_whnf_inv: a bare const's only whnf_step IS the deterministic
    // root delta, since a bare const never beta/zeta/iota-fires and delta has
    // no congruence) — rank-free by structure, with the corpus konst_red_aux
    // WfEnv/EnvAcyclic rank recursion honestly deferred to the iterated
    // env-closure capstone (R5/R6-era; rank as explicit premise, nothing
    // registered today). Plus the SUBSTITUTION-TRANSPORT UNLOCK
    // betaRed_inst_transport (one full beta_reduces step — iota arm included,
    // via iota_subst_commutes under the CARRIED RecEnvClosed premise —
    // commutes with instantiate_at), its whnf-level wrapper (delta leg via
    // delta_subst_commutes under carried DefEnvClosed), and the DERIVED
    // corpus-spelling single-contractum engine candExp_beta_subst (from R1's
    // candExp_beta by composition through betaStar_inst_transport +
    // candSet_betaStar_closed). Witnesses: candExp_delta_witness (whnf_acc of
    // the REAL reflected constant def_env_lift_closed_b THROUGH the engine,
    // consuming the Guard-4 step witness), constAcc_body_acc (the body
    // premise is FORCED), betaRed_inst_witness (a transported step computing
    // by refl). Local re-mints r2_const_ne_let/proj + r2_const_no_beta_reduces
    // (natrec's originals live outside this bundle). Consumes only earlier
    // stages: R0/R1, par_reduces_d_diamond discriminators + delta Type
    // substrate, par_reduces_p_topdev (iota_reduct_const_none), par_reduces_c
    // (option_none_ne_some_type + iota absurdity), iota_core/delta_subst
    // commutations, iota/delta bridges, whnf_lemmas unfoldings,
    // substitution_commutation_nested, rec_env_closed, kernel_core_red_env +
    // the_red_env witnesses. Census-NEUTRAL: every constant value-bearing,
    // ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r2,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R3 (candmodel_construct_r3.rs): the APPLIED
    // const spine. (A) The applied-DELTA transport delta_app_lift — delta
    // genuinely fires under an application spine, because delta_reduct looks
    // the definition name up at kapp_fn e (the SPINE HEAD) and re-applies
    // kapp_args e; R2's "delta fires only at the ROOT" means only that delta
    // has no congruence into a NON-spine subterm. Proved by OptionType.rec
    // case analysis on defval_for, generic in the DefEnv, and consumed by the
    // engine candExp_delta_app (cr3 at the Neutral spine + one Acc induction
    // on the argument + the complete one-argument classification
    // constApp1_beta_inv/constApp1_whnf_inv, whose delta leg is LIVE and whose
    // iota leg is a carried deadness premise since a generic head may be a
    // recursor). (B) The IOTA ENGINE candExp_iota_natrec_zero for the REAL
    // reflected Nat.rec at the canonical Nat.zero major: a triple nested Acc
    // induction over motive and both minors, running on the four-argument
    // spine classification natRecSpine1..4_beta_inv / natRecSpine4_whnf_inv
    // (short spines kill iota computationally — the major slot is none below
    // arity 4; arity 4 keeps it LIVE; the delta leg dies by the refl fact
    // natRecSpine4_delta_none, since Nat.rec has no defval_for entry), with
    // the fire natRecZ_iota_fires one Eq.refl over the real env, generic in
    // all three arguments, and its contractum RHS PROJECTED out of the
    // generated Guard-4 reduct rather than hand-copied. Also lands the
    // successor-major FIRE (natRecS_iota_fires + the numeral instance
    // natRecSuccZero_iota_fires) but not its engine (the successor major
    // itself steps — a fourth Acc layer, R4). §6.1 witnesses: the
    // UNCONDITIONAL natRecStuck_cand_mem / natRecStuck_witness (a real
    // four-argument Nat.rec spine in every candidate set through the CR3-
    // NEUTRAL route, with the iota continuation REFUTED by natRecV_iota_none —
    // a stuck major does not fire), the forced-premise guards
    // natRecZ_contract_acc_necessary and appConstAcc_reduct_acc, the real-env
    // applied-delta step r3_appliedDelta_witness, and the two CONDITIONAL
    // concrete engine runs (natRecZ_engine_concrete, r3_deltaApp_concrete)
    // whose single carried hypothesis is SN of the contractum — a
    // fundamental-theorem obligation of design rungs R5/R6, stated not hidden.
    // Consumes only earlier stages: R0/R1/R2 (IsCandSet + projections,
    // betaStar + betaStar_bvar_collapse + cand_var_witness,
    // r2_const_no_beta_reduces + delta_step_to_reduces/delta_reduces_to_step),
    // the app/lam/pi/let/proj discrimination + injectivity lemmas, iota/delta
    // bridges, delta_step_deterministic, option_some_inj /
    // option_none_ne_some_type, kernel_core_red_env + the_red_env witnesses.
    // No new inductives and no new plain defs, so the measured
    // uniform-leading-argument recursor-promotion hazard cannot fire.
    // Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r3,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // CandModel construction ladder R4 (candmodel_construct_r4.rs): ONE
    // four-argument const-spine iota engine (candExp_iota_spine4) — generic in
    // the head constant, in the contractum FAMILY and in all four arguments —
    // proved over four plain whnf_acc.rec layers on a GENERIC-HEAD reduct
    // classification (constSpine2/3/4_beta_inv + constSpine4_whnf_inv, R3's
    // 15-arm scaffold lifted off the concrete kcre_name_27 head, with the
    // shorter spines' iota-deadness entering as hypotheses because a generic
    // head's real-env metadata is unknown, and a LIVE delta leg because a
    // generic head may be defined). Two instantiations: (A) the SUCCESSOR-major
    // Nat.rec engine candExp_iota_natrec_succ — R3's promised fourth Acc layer,
    // over the MAJOR (matching the CandModel fields' whnf_acc t), consuming
    // R3's natRecS_iota_fires through the development-shape lemma
    // succApp_betaStar_shape; and (B) the GENERIC-RECURSOR direction
    // candExp_iota_genRec2, redRecGen's conclusion for a candidate-set-valued
    // Red at two-minor signature families (genRecApp IS a four-argument const
    // spine by rfl). B is NOT a discharge of the redRecGen FIELD, and R4
    // registers the reason mechanically: r4_genFresh_empty (the freshness
    // premise holds at DefEnv.empty for EVERY fam/sig, so it constrains
    // nothing about the fixed env) plus the two aliasing witnesses
    // r4_genRecName_aliases_deltaHead / r4_genRecHead_delta_live and
    // r4_genRecName_aliases_natRec / r4_genRecC_iota_fires_natRec (the schema
    // name Name.str fam (sigLength sig) collides with the reflected atoms
    // Name.str Name.anonymous k, so a family the field accepts can have a
    // recursor constant that is delta-LIVE, or that fires the REAL Nat.rec
    // rule, in the_red_env). §6.1 witnesses: natRecS_engine_concrete (one
    // conditional numeral run), the necessity guards
    // natRecS_major_acc_necessary — with the measured note that the same
    // statement for the NUMERAL is unprovable, delta having no congruence —
    // and natRecS_contract_acc_necessary, and the non-degeneracy cross-check
    // r4_natrecZ_via_spine4 (R3's zero engine re-derived through the generic
    // one at the LIVE reflected Nat.rec). Consumes only earlier stages: R0-R3,
    // the schema OBJECT layer (genRecApp/genRecC/genRecName/GenFresh, all
    // add_snschema_objects, substitution-bundle), DefEnv/Name/delta+iota
    // bridges and the_red_env witnesses. No new inductives and no new plain
    // defs. Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r4,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R5 (candmodel_construct_r5.rs) — the PAYOFF
    // rung: (A) the Pi-CANDIDATE PiSet over reflected KExpr (corpus
    // Stratified/Cand.lean PiSet/isCand_piSet) with cr1/cr2 UNRESTRICTED and
    // cr3 at the HEAD-FREE face, packaged as isCandHF_piSet over the weakened
    // interface IsCandHF (cr1 + cr2 + candCr3HF, whose cr3 additionally
    // assumes kexpr_const_name (kapp_fn e) = none). The restriction is forced
    // and the forcing is REGISTERED, not asserted:
    // piSet_cr3_headFree_necessary exhibits Nat.rec (bvar 0) (bvar 0) (bvar 0)
    // over the REAL reflected env as Neutral, NOT head-free, taking NO
    // whnf_step at all (so cr3's premise is satisfied vacuously) and yet
    // iota-firing once applied to Nat.zero — so an unrestricted cr3 for PiSet
    // would have to produce membership of the real Nat.rec zero contractum
    // from nothing. Structural cause: spec eliminators are const-headed
    // SPINES, so applying a neutral can create a fresh redex, where corpus
    // eliminators are saturated constructors and cannot. New infrastructure:
    // r5_spine_snoc, deltaReduct_app_gen + deltaStep_app_gen (a delta step
    // lifts under ANY application — R3's delta_app_lift generalized off the
    // bare-const head), whnfStep_app_left (beta AND delta legs) and
    // whnfAcc_app_left (the corpus sn_app_left). (B) The type interpretation
    // candInterp by KExpr.rec — every non-pi former to the top candidate
    // (red_sort definitional), pi A B to PiSet (candInterp A) (fun _ =>
    // candInterp B) — with candInterp_isCandHF at EVERY untyped T (the corpus
    // isCand_cval needs CWK); NON-DEPENDENT codomain, stated as the scope
    // limit. (C) The shaped fragment judgment FragTy (sortMem/var/app/lam),
    // its fundamental theorem fragTy_interp and the UNCONDITIONAL capstone
    // fragTy_sn : FragTy T e -> whnf_acc e — no CandModel, no RecEnvClosed, no
    // carried premise of any kind (the lam rule takes R1's development-family
    // premise precisely so R2's corpus-spelling engine's RecEnvClosed is not
    // imported). candExpHF_beta is R1's Tait engine at the weaker interface,
    // derived by textual weakening of R1's own builder. (D) Witnesses:
    // fragTy_sn_witness (a beta redex whose SN comes THROUGH the capstone),
    // r5_interp_pi_proper + fragTy_not_total (the interpretation and the
    // judgment are PROPER subsets of the top set — the micro_has_type trap
    // guard), and the necessity guard above. HONESTY: fragTy_sn is SN for
    // FragTy, NOT for TypingCtx; nothing here discharges or advances
    // M : CandModel tenv. Consumes only earlier stages: R0-R4,
    // dependent_sn_richmodel, whnf_reduction, iota_step/delta_step cores and
    // bridges, expr_model. Census-NEUTRAL: every constant value-bearing, ZERO
    // new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r5,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R6 (candmodel_construct_r6.rs) — the
    // SYNTACTIC rung. R5's fragTy_sn was unconditional but over a
    // SEMANTIC-PREMISE judgment (FragTy's app/lam rules mention candInterp).
    // R6 lands a real context-indexed typing judgment SynTy : ListType KExpr
    // -> KExpr -> KExpr -> Type whose four rules — var by ctx_lookup, sort at
    // the successor universe, app by pi-elim, lam by pi-intro in the extended
    // context — mention NO candInterp at all (pinned by a shape guard), the
    // closing-substitution interface SubstOK with its nil/idsubst/extend
    // builders, and the Tait fundamental theorem over it. The tower is the
    // guide's own Models / fundamental_* / fundamental_general development
    // (dependent_sn_richmodel.rs:3283/4052) re-run with candInterp in place of
    // cm_Red tenv M and R5's landed THEOREMS in place of the CandModel LAW
    // PROJECTIONS — which is the point: there the laws are fields of the
    // hypothesis M, here every one is proved. Capstones: synTy_fundamental,
    // synTy_sn_subst (SN of EVERY closing instance — content R5 had no
    // analogue for), synTy_sn (SN at an ARBITRARY context, since idsubst
    // models every context via candInterp_var) and the closed-term corollary
    // synTy_sn_closed. All UNCONDITIONAL: no CandModel, no RecEnvClosed, no
    // DefEnvClosed, no acyclicity (premise-freedom shape guard).
    // TWO SYNTACTIC SIDE CONDITIONS ON THE LAM RULE, stated honestly and
    // guarded: (1) SimpleTy A — the syntactic sort/pi type class, whose
    // psubst-inertness (simpleTy_psubst) makes R5's NON-DEPENDENT Pi clause
    // EXACT rather than approximate (on a closed codomain instantiate B a = B,
    // so the dependent and non-dependent readings coincide and no
    // psubst_instantiate reshaping appears anywhere in the tower); (2) the
    // development-closure premise `forall s b2, betaStar (psubst (up s) b) b2
    // -> SynTy (cons A G) b2 B`. (2) is the HOISTED form of the two facts the
    // Tait engine needs and that are BLOCKED at this stage position:
    // substitution transport for beta_reduces (R2's betaRed_inst_transport
    // carries RecEnvClosed (red_rec the_red_env)) and lift transport for
    // whnf_acc (RecEnvLiftClosed) — whose checker discharges register only in
    // add_the_red_env_faithful_discharge, AFTER the whole candmodel ladder.
    // Hoisting it into the RULE is what keeps the capstones premise-free;
    // r6_subst_creates_redex proves the weaker spelling (developments of b
    // alone) is strictly insufficient, and r6_lam_body_acc_necessary proves
    // the body's SN obligation is real. B (the dependent Pi clause) is
    // OBSTRUCTED and the obstruction is PROVED, not described:
    // r6_dependent_pi_self_argument + r6_dependent_pi_self_reachable exhibit
    // T := pi (sort 0) (bvar 0), for which the dependent clause's recursive
    // call at the REACHABLE domain member a := T is candInterp T itself —
    // non-terminating on any recursion measured by the type, which is why the
    // corpus needs the shape/denotation split (Shapes.lean Sk/VD/Val/cval).
    // Witnesses: synTy_id, synTy_app_
    // witness (a genuine beta redex), synTy_sn_witness (SN obtained THROUGH
    // the capstone), synTy_not_total + simpleTy_not_total (the micro_has_type
    // trap guards). HONESTY: synTy_sn is SN for SynTy, NOT for TypingCtx —
    // SynTy has no const, no let_, no pi formation, simple types only, plus
    // the two lam side conditions; nothing here discharges or advances
    // M : CandModel tenv. Consumes only earlier stages: R0-R5,
    // dependent_sn_richmodel (ctx_lookup, the psubst calculus, whnfAcc_sort,
    // whnfAcc_pi, option_some_inj), whnf_reduction, par_reduces_c
    // (option_none_ne_some_type) and expr_model. Census-NEUTRAL: every
    // constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r6,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Nat.rec spec port (task #30): the concrete Nat recursor + iota-fire fidelity
    // + the Nat.rec reduction relation (natStep/natSteps) + the beta-chain
    // (natRecContract_steps via betaReduces_psubst). Placed AFTER
    // add_dependent_sn_richmodel because the beta-chain uses the psubst calculus
    // (psubst/scons/up/psubst_scons_instantiate). Also needs rec_env + iota_step +
    // whnf_reduction (beta_reduces), all earlier. Full-bundle only.
    CoreSpecStage {
        apply: Specification::add_natrec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // DEPTH-AWARE ENV-CLOSURE CHECKERS (Front #1 Stage 3/4 prerequisite): the
    // standard de Bruijn closedness decision closed_at_b (+ nat_lt_b, the Bool
    // mirror of Lt) and the b2 env folds (rec_env_closed_b2 /
    // rec_env_lift_closed_b2 / def_env_closed_b2 / def_env_lift_closed_b2 +
    // the rec_rules_closed_b2 leg), their soundness (closed_at_b_sound ->
    // is_closed_at), the instantiate/lift INVARIANCE BRIDGE
    // (inst_closed_at_id / lift_closed_at_id — the identity direction the
    // in-tree closedness bundle lacks), and the generic *_of_b2 interface
    // discharge — so a concrete env whose rule RHSs are REAL closed LAMBDAS
    // (which the Stage-1 ceiling-0 test measurably rejects: 0/86 real rule
    // RHSs are bvar-free) discharges each closure interface by a single
    // Eq.refl Bool Bool.true. Plus the faithful_red_env regression demo. The
    // Stage-1 checkers are KEPT (Stage-2 reflection allowlist + demos). AFTER
    // add_dependent_sn_richmodel: consumes its lt_to_le_succ (which is
    // substitution-bundle-only, hence in_impl_soundness: false here); other
    // deps — is_closed_at (add_whnf_reduction), inst_bvar_lt/lift_bvar_lt
    // (add_expr_model_inst_ceiling), the instantiate_at_*/lift_at_* unfoldings
    // (add_whnf_lemmas / add_expr_model_lift_lemmas), le_zero_n/le_succ_succ/
    // le_trans (add_iota_core), the decidable-eq tower + opt_pick_some_inv
    // (add_faithful_red_env), opt_bind_some_inv/option_none_ne_some
    // (add_iota_subst), the interfaces (add_rec_env_closed / add_delta_subst)
    // — are all earlier stages. Purely additive; ZERO new axioms (census
    // stays 11); all lemmas DerivedProved with empty closures.
    CoreSpecStage {
        apply: Specification::add_env_closed_checkers_depth,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // THE PAYOFF WITNESSES (Front #1 Stage-4 feasibility gate): all FOUR
    // closure interfaces discharged over the MECHANICALLY REFLECTED REAL env
    // kernel_core_red_env by the single-rfl depth-aware route
    // (<interface>_of_b2 (red_* kernel_core_red_env) (Eq.refl Bool
    // Bool.true)) — the kernel whnf-evaluates closed_at_b over all real rule
    // RHSs (field-binding lambdas) and def values to Bool.true at
    // registration. Nothing carried is discharged (the swap is Stage 4
    // proper). AFTER add_kernel_core_red_env (the reflected env) and
    // add_env_closed_checkers_depth (the *_of_b2 route). FULL bundle only:
    // kernel_core_red_env itself is full-bundle-only.
    CoreSpecStage {
        apply: Specification::add_kernel_core_red_env_closed_witnesses,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // infer_terminates RETIREMENT: converts the SN-pillar census axiom
    // (forall e, terminates_infer e, formerly a HelperAxiom in whnf_lemmas.rs)
    // into a genuine DerivedProved theorem. Placed AFTER add_whnf_progress (which
    // registers ConstFreeUnit / ConstFreeUnit.triv, the leaf bundle of the childAcc
    // motive) and add_whnf_reduction (subexpr_step / infer_acc / the reducible
    // terminates_infer alias); AndType + its projectors come from the foundation
    // layer. terminates_infer := infer_acc := Acc(subexpr_step) is the standard
    // well-founded accessibility of KExpr under the strict-subexpression relation,
    // discharged by structural KExpr.rec (the six subexpr_step constructors invert
    // uniformly through the childAcc-keyed subexpr_step_acc_inv). HONEST: this is
    // infer's STRUCTURAL child-recursion pillar — NOT the WHNF reductions infer
    // performs on types (that SN is the separate whnf_terminates_well_typed above),
    // and NOT Godel-blocked as the axiom's original phrasing implied. Purely
    // additive; REMOVES one census axiom (63 -> 62).
    CoreSpecStage {
        apply: Specification::add_infer_terminates_proof,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // def_eq_joinable: DefEq -> the 3-way (β+ι+δ) join witness, by DefEq.rec.
    // AFTER add_par_reduces_iota_delta (lands the diamond par_reduces_cd_star_diamond)
    // and the reverse step bridges (delta/iota_reduces_to_step, landed earlier by
    // add_delta_step_bridge / add_iota_step_bridge). Brick 6 of the
    // church_rosser_whnf retirement track.
    CoreSpecStage {
        apply: Specification::add_def_eq_joinable,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // par_reduces_cd_sound / _star_sound / join_to_def_eq: the S-half (par-step ->
    // DefEq) of the church_rosser_whnf retirement. AFTER add_def_eq_joinable so all
    // of par_reduces_cd / _star / par_strips_witness_cd_star + the step bridges exist.
    CoreSpecStage {
        apply: Specification::add_par_reduces_cd_sound,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // REAL-ENV DISCHARGE (Bricks R2 + R3 + R4): the remaining FIVE faithful
    // interfaces over faithful_red_env — i1 RecEnvReductNotRedex, i3 RecEnvClosed,
    // i4 RecEnvLiftClosed, i5 DefEnvClosed, i6 DefEnvLiftClosed — discharged as real
    // DerivedProved terms (rule rhs / def value are the CLOSED lambda LAM, fixed by
    // inst/lift and binder-headed so never an iota redex), AND the full bundle
    // faithful_red_env_faithful : RedEnvFaithful faithful_red_env assembled via
    // RedEnvFaithful.mk from all eight honest witnesses. MUST follow
    // add_par_reduces_cd_sound — which registers RedEnvFaithful / RedEnvFaithful.mk
    // (the bundle type) — and so also follows rec_env_closed (RecEnvClosed/
    // RecEnvLiftClosed), delta_subst (DefEnvClosed/DefEnvLiftClosed),
    // par_reduces_p_topdev (RecEnvReductNotRedex) and iota_core (iota_reduct_some_inv).
    // Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_faithful_red_env_bundle,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // FAITHFUL-INTERFACE CHECKERS (Front #1 Stage 3/4, faithful_checkers.rs):
    // the Bool checkers + generic checker-soundness lemmas for the four
    // remaining RedEnvFaithful interfaces — i1 rec_env_reduct_not_redex_of_b,
    // i2 rec_env_ctor_no_recmeta_of_b, i7 red_env_disjoint_of_b, i8
    // red_env_ctor_no_defval_of_b — so a concrete env discharges each by a
    // single Eq.refl Bool Bool.true (the Aristotle-farmed FaithfulCheckers
    // port). Plus the faithful_red_env regression probes. AFTER
    // add_faithful_red_env_bundle: consumes its kapp_fn_apply_spine /
    // iota_reduct_head_none; other deps — the interfaces
    // (add_rec_env_closed / add_par_reduces_cd / add_par_reduces_p_topdev /
    // add_par_reduces_iota_delta), iota_reduct_some_inv (add_iota_core), the
    // decidable-eq tower + opt_pick_some_inv (add_faithful_red_env),
    // opt_bind_some_inv / option_none_ne_some (add_iota_subst) — are all
    // earlier stages in both subset bundles. Purely additive; ZERO new axioms
    // (census stays 11).
    CoreSpecStage {
        apply: Specification::add_faithful_checkers,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // THE STAGE-4 DISCHARGE (Front #1): all EIGHT faithful interfaces over
    // the SWAPPED the_red_env (= kernel_core_red_env, the fidelity-gated
    // reflection of the real kernel foundation core) by the single-rfl
    // route — i3..i6 via the depth-aware *_of_b2 closedness lemmas
    // (add_env_closed_checkers_depth), i1/i2/i7/i8 via the faithful checkers
    // (previous stage) — assembled into the_red_env_faithful : RedEnvFaithful
    // the_red_env via RedEnvFaithful.mk (add_par_reduces_cd_sound). The
    // honest DerivedProved bundle witness over the metatheory's REAL
    // distinguished environment; the carried-hypothesis decls stay parametric
    // (instantiation is follow-up). NOT in the ImplementationSoundness bundle:
    // the *_of_b2 route lives in add_env_closed_checkers_depth, which is
    // substitution/full-only. ZERO new axioms (census stays 11).
    CoreSpecStage {
        apply: Specification::add_the_red_env_faithful_discharge,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R7 (candmodel_construct_r7.rs) — the
    // TEXTBOOK rung, and the ONE stage of the ladder that is deliberately NOT
    // adjacent to the others. R6 landed synTy_sn unconditionally but paid for
    // it in the RULE: SynTy.lam carries the hoisted development-closure
    // premise `forall s b2, betaStar (psubst (up s) b) b2 -> SynTy (cons A G)
    // b2 B`, because the Tait engine's development family needs the
    // substitution transport `beta_reduces b' b2 -> beta_reduces (instantiate
    // b' a) (instantiate b2 a)` and the only spec-side transport — R2's
    // betaRed_inst_transport / betaStar_inst_transport — CARRIES RecEnvClosed
    // (red_rec the_red_env) through its iota arm. That premise's discharge,
    // the_red_env_rec_closed_via_checker_b2, is registered by the PREVIOUS
    // stage. So R7 sits HERE, nine stages after the ladder's R0-R6 block,
    // precisely so it may APPLY the discharge instead of hoisting its
    // consequence: betaRed_inst_transport_env / betaStar_inst_transport_env
    // are R2's transports with the argument supplied and therefore carry
    // NOTHING, candInterp_betaStar_closed lifts R5's isCandHF_cr2 along a
    // development, and the two together turn R6's premise into the THEOREM
    // r7_dev_family_derived. SynTyT is then the ordinary judgment — var by
    // ctx_lookup, sort at the successor universe, app by pi-elim, and lam by
    // pi-intro with a SINGLE sub-derivation SynTyT (cons A G) b B; the shape
    // guard refuses `betaStar`, `psubst` and `up ` anywhere in its source.
    // Capstones synTyT_fundamental / synTyT_sn_subst / synTyT_sn (arbitrary
    // context) / synTyT_sn_closed stay UNCONDITIONAL — no CandModel, no
    // RecEnvClosed, no RecEnvLiftClosed, no DefEnvClosed, no acyclicity — and
    // a second guard REQUIRES that the discharged witness is consumed in the
    // unlock's proof values, so the premise cannot silently return to the rule.
    // RecEnvLiftClosed, the other blocker R6 named, is NOT needed: the body's
    // SN comes from the IH at the fresh variable (scons (bvar 0) s, closed by
    // substOK_extend on candInterp_var) reshaped by psubst_scons_instantiate
    // and unwound by whnfAcc_of_instantiate_bvar0 — the landed fundamental_pi
    // idiom — so R7 never lifts. BRIDGE: synTy_to_synTyT subsumes R6 (its lam
    // premise at s := idsubst and the reflexive development, collapsed by
    // psubst_up_idsubst), and synTy_sn_via_synTyT re-derives R6's own capstone
    // through R7's. The CONVERSE is not claimed: it would need subject
    // reduction for SynTyT plus substitution stability, and SynTyT is
    // genuinely wider. Witnesses: synTyT_id / synTyT_sort_witness /
    // synTyT_app_witness (also the premise-satisfiability supply for SynTyT,
    // which constructors do not provide), synTyT_lam_redex_witness +
    // r7_redex_body_fires + r7_textbook_admits_redex_body (a lambda whose BODY
    // IS A LIVE BETA REDEX — one SynTyT.lam here, an inversion over the
    // developments of a firing body under R6's rule), synTyT_sn_witness (SN of
    // a redex UNDER A BINDER, obtained THROUGH the capstone) and
    // synTyT_not_total (the micro_has_type trap guard: widening the lam rule
    // did not widen the judgment to the total relation). HONESTY: synTyT_sn is
    // SN for SynTyT, NOT for TypingCtx — no const, no let_, no pi formation,
    // SimpleTy domains only; nothing here discharges or advances M : CandModel
    // tenv. SimpleTy A stays on the lam rule and is NOT a stage-position
    // artifact: R5's candInterp has a non-dependent Pi clause and the
    // dependent one is proved non-portable (r6_dependent_pi_self_reachable).
    // Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r7,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R8 (candmodel_construct_r8.rs) — the
    // CONVERGENCE rung, registered immediately after R7 because it consumes
    // R7's already-discharged substitution transport. R7's own closing list of
    // what separated SynTyT from the spec's TypingCtx was: no const rule, no
    // let_ rule, no pi FORMATION rule, SimpleTy domains only, and a var rule
    // that does NOT lift where TypingCtx.var concludes at lift_at A 0 (i+1).
    // R8 closes the var gap and the pi gap outright and the let_ gap at a named
    // fragment. THE VAR GAP, and a measured correction: R7 predicted it needs
    // RecEnvLiftClosed. It does not. That discharge is what a TERM lift needs
    // (whnf_acc e -> whnf_acc (lift_at e 0 1), blocked at its iota arm); the
    // var gap is a TYPE lift, where the term is unmoved, and R5's candInterp
    // reads nothing of a type but its Pi-skeleton — which lift_at preserves.
    // So the whole gap is candInterp_lift_eq : candInterp (lift_at T d k) =
    // candInterp T, one KExpr.rec whose ten arms are eight Eq.refls (both sides
    // are the top candidate), a two-case Nat.rec in the bvar arm (lift_bvar_at
    // is stuck on Nat.sub d i) and two Eq.congs through PiSet in the pi arm. It
    // is an equality of the two KExpr -> Type PREDICATES on purpose: PiSet is
    // contravariant in its domain, so implications would have to be carried
    // both ways at once, whereas function equality congruences in one step and
    // needs no funext. RecEnvLiftClosed therefore stays untouched by the whole
    // ladder, now for a stated reason. Because R6's SubstOK is reused
    // UNCHANGED, R8 adds NO substitution infrastructure: the lift is paid in
    // the var ARM of the fundamental theorem, for an arbitrary looked-up type.
    // THE PI ARM is the landed fundamental_pi with the CandModel law
    // projections swapped for R5 theorems (red_sort -> candInterp_sort_mem, CR1
    // -> candInterp_cr1, red_var -> candInterp_var, models_extend ->
    // substOK_extend), and the rule carries TypingCtx.pi's LITERAL raw
    // Level.imax. THE LETTY ARM is R1's base-set whnfAcc_zeta_expand — which is
    // exactly what candInterp at a sort IS — with the contractum family built
    // from the body IH at scons v2 s (closable only because candInterp (sort n)
    // v2 reduces to whnf_acc v2, which is why the annotation must be a literal
    // sort) and carried along the development by R7's DISCHARGED
    // betaStar_inst_transport_env. The Pi-typed zeta clause is NOT landed and
    // its obstruction is PROVED and LOCATED: r8_let_not_neutral (cr3 is
    // inapplicable at the redex, Neutral (let_ ..) = Empty) beside
    // r8_zeta_spine_is_neutral (cr3 IS applicable one layer out, at the app
    // spine where PiSet membership actually lives), so the missing engine is
    // named — a five-fold nested Acc induction over the reducts of an
    // app-headed zeta redex, which R1 PROVED cannot be obtained
    // per-candidate-set. Capstones synTyL_fundamental / synTyL_sn_subst /
    // synTyL_sn (arbitrary context) / synTyL_sn_closed stay UNCONDITIONAL —
    // no CandModel, no RecEnvClosed, no RecEnvLiftClosed, no DefEnvClosed, no
    // acyclicity — and the shape guard pins both the premise freedom and the
    // consumption of the discharge. BRIDGE: synTyT_to_synTyL subsumes R7 over
    // SIMPLE contexts (CtxSimple G), the hypothesis being the honest price of
    // the faithful var rule — the two judgments assign genuinely different
    // types to the same variable, and simpleTy_lift is what reconciles them
    // where the entry is closed. The CONVERSE is FALSE and is proved so:
    // synTyT_no_pi_formation shows no SynTyT derivation concludes at a pi
    // expression in any context at any type, while synTyL_pi_formation_witness
    // is one. Witnesses: synTyL_id / synTyL_sort_witness (premise
    // satisfiability, which constructors do not supply),
    // synTyL_var_lift_witness (bvar 1 typed at bvar 2 in [sort 0 ; bvar 0] —
    // the lift made VISIBLE, stated literally so the kernel must compute it),
    // synTyL_pi_formation_witness + synTyL_sn_witness (SN of a pi EXPRESSION
    // through the capstone), synTyL_let_witness + r8_let_body_fires +
    // synTyL_let_sn_witness (SN of a LIVE zeta redex through the capstone), and
    // synTyL_not_total (the micro_has_type trap guard). HONESTY: synTyL_sn is
    // SN for SynTyL, NOT for TypingCtx. What still separates them after this
    // rung: no const rule (the delta/redConst rung, needing the WfEnv/EnvAcyclic
    // rank witness for the real reflected env), a NON-DEPENDENT app and a
    // SimpleTy lam domain (both forced by R5's non-dependent Pi clause, whose
    // dependent version is PROVED non-portable), the sort-annotated-only let_,
    // and no conversion rule. Census-NEUTRAL: every constant value-bearing,
    // ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r8,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R9 (candmodel_construct_r9.rs) — the DELTA
    // rung, registered immediately after R8 because SynTyC is SynTyL plus two
    // rules and the bridge synTyL_to_synTyC consumes SynTyL.rec directly.
    //
    // BUILD ITEM B3, LANDED AND *COMPUTED*. R2, R4, R7 and R8 each closed with
    // the same sentence — the delta/redConst rung "needs a WfEnv/EnvAcyclic rank
    // witness for the real reflected env" — and R2 specified the shape it would
    // have to be CARRIED in: delta_step (red_def the_red_env) (const c us) body
    // -> const_occurs c2 body -> Lt (rk c2) (rk c). It does not have to be
    // carried. the_red_env is kernel_core_red_env: a concrete, fixed, finite
    // reflected environment, so the rank is computable for the ACTUAL
    // environment and the decrease provable by kernel computation, exactly the
    // way R3/R4 proved iota- and delta-deadness at concrete heads. Measured on
    // the generated env: the DefEnv is a 50-entry addDef chain over 127 interned
    // names, its delta graph has 67 edges, it is ACYCLIC, and its longest chain
    // is 7 — and it is acyclic for a structural reason worth recording, that the
    // reflection compiles every recursive kernel definition through the matching
    // .rec, so not one of the 50 bodies mentions its own name. The route is the
    // established one-rfl checker pattern rather than a 50-way case analysis:
    // rk (a 127-entry rank TABLE indexed by the interned numeral, a list walk
    // rather than a name_eqb cascade because the checker evaluates rk once per
    // const occurrence and there are 963 of them), const_occurs (the corpus's
    // Tm.mentions, which no core_spec module had — occurs_in is about de Bruijn
    // self-reference, not const names), rank_dominates_b, def_env_ranked_b, and
    // the_red_env_ranked : def_env_ranked_b (red_def the_red_env) = true by ONE
    // Eq.refl. Two generic soundness lemmas (def_env_ranked_b_sound by
    // DefEnv.rec — def_env_closed_b_sound's shape plus a name transport, because
    // the per-entry test mentions the entry's OWN name — and
    // rank_dominates_occurs by KExpr.rec) plus the bare-const inversion
    // delta_step_defval_inv compose that into
    // the_red_env_delta_rank_decrease: R2's statement character for character,
    // DISCHARGED. the_red_env_no_delta_cycle is what it buys — EnvAcyclic for
    // the real kernel foundation core, proved.
    //
    // THE CONST RULE, AND THE BLOCKER THAT WAS NEVER THE RANK. The engine lands:
    // candInterp_delta_expand_sort is R2's candExp_delta at a SORT-typed slot,
    // legitimate for exactly R8's candInterp_zeta_expand_sort reason (candInterp
    // at a sort REDUCES to whnf_acc, the base whole-SN set, which IS an
    // IsCandSet). At a PI-typed slot it is BLOCKED, and not by acyclicity: R5's
    // interpretation is only IsCandHF, whose cr3 additionally demands HeadFree,
    // and R5 already PROVED that restriction necessary at the real env
    // (piSet_cr3_headFree_necessary, a stuck Nat.rec counterexample). A bare
    // const is the canonical non-head-free term — r9_const_is_neutral shows
    // unrestricted cr3 would apply, r9_const_headfree_absurd shows the head-free
    // face does not, r9_const_obstruction_located pairs them. So SynTyC carries
    // the const rule in two clauses: konstDead types const c us at any sort when
    // defval_for (red_def the_red_env) c = none — such a const is whnf-STUCK
    // (whnfAcc_const_dead over R2's complete constRedex_whnf_inv
    // classification), and over the real env that is every name outside the 50
    // entries, i.e. every reflected inductive type, constructor and recursor —
    // while konstDelta types it from a derivation of its real unfolding.
    // konstDelta is SOUND and is the deliverable four rungs asked for, and it is
    // VACUOUS over THIS environment, PROVED rather than asserted: all 50 real
    // definition bodies are KExpr.lam (r9_the_red_env_all_lam, one Eq.refl) and
    // the judgment types no lam at a sort (synTyC_no_lam_at_sort), which compose
    // into r9_konstDelta_no_real_instance. That is the design's section 6.3
    // labeled by-design vacuity, measured in the wf/ac tradition. The two
    // obstructions are the same wall from two sides: reaching a real defined
    // constant means typing its body, a lambda, hence at a PI type, where the
    // const clause cannot go.
    //
    // Capstones synTyC_fundamental / synTyC_sn_subst / synTyC_sn (arbitrary
    // context) / synTyC_sn_closed stay UNCONDITIONAL — no CandModel, no
    // RecEnvClosed, no RecEnvLiftClosed, no DefEnvClosed and, the one that
    // matters here, NO EnvAcyclic: the acyclicity B3 establishes is a discharged
    // theorem about a fixed environment, never a hypothesis. The shape guard
    // refuses all of those names in the statements and in SynTyC's own source,
    // and additionally refuses rank_dominates_b / def_env_ranked_b there, so the
    // rank cannot creep back in as a rule premise. SynTyC does mention
    // the_red_env, through defval_for and delta_step, and that is unavoidable
    // rather than sloppy — delta is env-relative — with both side conditions
    // discharged per-constant by Eq.refl.
    //
    // BRIDGE: synTyL_to_synTyC subsumes R8 with NO hypothesis (R8's own bridge
    // needed CtxSimple because R8 CHANGED a rule; R9 changes none, it only
    // adds), and synTyL_sn_via_synTyC re-derives R8's capstone through R9's. The
    // CONVERSE IS FALSE and proved: synTyL_no_const shows no SynTyL derivation
    // concludes at a const EXPRESSION in any context at any type, which is the
    // precise sense in which "no const rule" was the ladder's outstanding gap.
    // Witnesses: synTyC_id / synTyC_sort_witness (premise satisfiability, which
    // constructors do not supply), synTyC_konst_dead_witness (the REAL reflected
    // name kcre_name_12 typed, over a kernel-COMPUTED lookup — the first time
    // the ladder's judgment reaches a KExpr.const at all) + synTyC_sn_konst_
    // witness (its SN THROUGH the capstone), r9_rank_decrease_witness and
    // r9_rank_decrease_witness_undefined (the decrease at a real kcre_* pair,
    // obtained THROUGH the theorem and reusing R2's Guard-4 delta step),
    // r9_konstDead_premise_necessary + r9_live_const_not_dead (the side
    // condition's necessity, at a live redex), and synTyC_not_total (the
    // micro_has_type trap guard). HONESTY: synTyC_sn is SN for SynTyC, NOT for
    // TypingCtx. What still separates them: TypingCtx.const reads a DECLARED
    // type off a tenv at ANY type, Pi types included, while SynTyC has no tenv
    // and reaches a const only at a SORT and only when it is delta-DEAD (plus a
    // delta clause vacuous over this env); app is NON-DEPENDENT and lam carries
    // SimpleTy A; the let_ rule is the sort-annotated fragment; there is no
    // conversion rule; and — named for the first time here — no rule reaches a
    // const at a PI type at all, which is the same head-free wall rather than a
    // rank problem. Census-NEUTRAL: every constant value-bearing, ZERO new
    // axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r9,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R10 (candmodel_construct_r10.rs) — the
    // KEYSTONE rung, registered immediately after R9 because it consumes R9's
    // const machinery (whnfAcc_const_dead, r9_const_delta_dead,
    // r9_const_headfree_absurd) and closes the gap R9 named last.
    //
    // THE SETTLEMENT. R5 proved the head-free restriction on the Pi-candidate's
    // cr3 NECESSARY for its own proof and left the full law open, suggesting it
    // be supplied from outside cr3 once the fundamental theorem gives SN of
    // real-env iota contracta; R1, R8 and R9 all recorded the same wall from
    // other sides, and R9's computed delta rank was expected to be the tool that
    // broke the apparent circularity. It is not a circularity.
    // r10_piSet_cr3_unrestricted_refuted proves the UNRESTRICTED cr3 face FALSE
    // at the real reflected environment: instantiate CA := whnf_acc and
    // CB := fun _ => candInterp (pi (sort 0) (sort 0)) — every side condition
    // isCandHF_piSet asks for holds — at the Neutral, STEP-FREE three-argument
    // spine Nat.rec (bvar 0) omegaLam (bvar 0), so cr3's reduct premise is
    // vacuous and free; then applying it to the real Nat.zero fires the real
    // zero rule, and one more argument diverges (r10_appStuck_not_whnfAcc walks
    // the five-step chain to app omegaLam omegaLam). The SN of real-env iota
    // contracta is therefore not merely unavailable early in the dependency
    // order, it is NOT A THEOREM, and no stratification supplies it. Membership
    // of an iota contractum must come from an iota-EXPANSION engine (R2/R3's
    // candExp_iota_natrec_zero shape), never from cr3. Three structural facts
    // came out of it and are worth keeping: the DELTA leg was never the problem
    // (R5's deltaReduct_app_gen already factors it through the head), the ZERO
    // rule alone is harmless (its contractum is a subterm of a step-free spine)
    // and only becomes fatal because PiSet is a set of FUNCTIONS so the minor
    // may be applied, and the rank plays no part because there is no delta
    // anywhere in the counterexample.
    //
    // THE HONEST STRONGEST FORM. HeadInert is a two-constructor Type-valued
    // inductive — head-free, or a spine head that is a constant with neither a
    // definitional value nor recursor metadata in the real environment — and it
    // is HEREDITARY under application for the same definitional reason
    // head-freeness is (kapp_fn (app e a) reduces to kapp_fn e), which is what
    // lets piSet_cr3HI_aux be R5's proof weakened through hi_weaken rather than
    // retyped — with ONE non-textual site, measured 2026-08-27: HeadFree is a
    // def unfolding to an Eq about kapp_fn, so HeadFree e and HeadFree (app e a)
    // are the same type and R5 passes hhf straight through, while HeadInert is
    // an inductive FAMILY and needs headInert_app applied. It is STRICTLY weaker
    // than HeadFree
    // (r10_headInert_strictly_weaker, at a real reflected constant) and the
    // widening is TIGHT: r10_natRec3_not_headInert shows every three-argument
    // Nat.rec spine — R5's own exhibit and this rung's counterexample alike — is
    // excluded, by feeding the real zero-rule fire to
    // iota_step_no_recmeta_absurd without ever naming the recursor metadata.
    // The payoff is R9's item 5: r10_interp_const_pi_witness puts a REAL
    // reflected constant in candInterp (pi (sort 0) (sort 0)), the first time
    // the ladder reaches a const at a PI type, and r10_const_unlock_proper pins
    // that the interpretation did not become total (omegaLam is still out).
    // Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r10,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R11 (candmodel_construct_r11.rs) — the rung
    // that WIRES R10's semantic const-at-a-Pi-type into the judgment and SETTLES
    // the conversion rule. Registered immediately after R10 because the const
    // rule's fundamental-theorem arm IS r10_deadConst_cand_mem at
    // candInterp_isCandHI, and therefore after R0-R9; it additionally needs
    // DefEq (add_typing_def_eq, far earlier) for the conversion counterexample.
    //
    // THE DELIVERABLE. SynTyP is R9's SynTyC with all eight rules textually
    // unchanged plus konstInert — a constant that the REAL reflected
    // environment gives neither a definitional value nor recursor metadata is
    // typed at ANY A, Pi types included, which is TypingCtx.const's shape minus
    // the tenv lookup. R10 reached that constant SEMANTICALLY and named wiring
    // it in as R11's job; synTyP_konst_pi_witness is the derivation and
    // synTyP_sn_konst_pi_witness takes its SN THROUGH the capstone. The
    // capstone chain (synTyP_fundamental / synTyP_sn_subst / synTyP_sn /
    // synTyP_sn_closed) carries ZERO premises, guarded exactly as R6-R10 guard
    // theirs, and the fundamental theorem is R9's own recursor term with the
    // judgment renamed and two minors spliced in front of the indices, so the
    // eight shared arms cannot drift.
    //
    // THE CONVERSION SETTLEMENT. TypingCtxConv.conv converts along DefEq, which
    // for this ladder would need DefEq A B -> candInterp A e -> candInterp B e.
    // It is FALSE, and the counterexample is one type-level beta redex:
    // candInterp is defined by KExpr.rec ON THE TYPE, every non-Pi former goes
    // to the top candidate and only pi produces a PiSet, so at
    // A := app (lam (sort 0) (bvar 0)) (pi (sort 0) (sort 0)) and its
    // contractum B := pi (sort 0) (sort 0) the interpretation collapses from
    // the top candidate to a proper subset while DefEq.beta relates them.
    // r11_candInterp_conv_refuted, its equality form
    // r11_candInterp_conv_eq_refuted (the shape R8 needed for lifting, since
    // PiSet is contravariant in its domain) and the sharpest form
    // r11_candInterp_step_conv_refuted — not even ONE whnf_step of the type may
    // be transported — pin it. The abstract statement
    // r11_conv_top_proper_incompatible carries it at an ARBITRARY
    // I : KExpr -> KExpr -> Type, so this is not an anecdote about one
    // definition; the candInterp result is registered as its INSTANCE. SCOPE,
    // stated because two different claims are in play: this refutes
    // conversion-invariance of candInterp, NOT the corpus's general
    // impossibility (no_conv_invariant_substitutive_interpretation,
    // Stratified/SubstConvWall.lean), whose hypotheses — environment indexing, a
    // variable clause, lambda-body uniformity, a substitution law — candInterp
    // does not satisfy. The two are independent.
    //
    // THE ACT ON THE REFUTATION. SynTyP.convI converts along equality of the two
    // types' INTERPRETATIONS instead, sound by one Eq.substType
    // (r11_interpEq_conv) and NOT Eq.refl decoration: R8's candInterp_lift_eq
    // holds at an arbitrary type, so r11_synTyP_unlift_type /
    // r11_synTyP_lift_type make the judgment closed under lifting the TYPE both
    // ways — the conversion TypingCtx.var's lifted conclusion needs.
    // The bridge synTyC_to_synTyP is hypothesis-free and STRICT:
    // synTyC_no_const_at_pi proves no SynTyC derivation concludes at a const
    // expression with a pi type, in any context at any A B.
    // Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r11,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // Candidate-model construction R12 (candmodel_construct_r12.rs) — THE SHAPE
    // / DENOTATION SPLIT, the rung R6's and R11's walls both point at.
    // Registered immediately after R11 because the conversion contrast carries
    // r11_candInterp_step_conv_refuted itself, and therefore after R0-R10; it
    // additionally needs R10's IsCandHI interface (isCandHI_intro/_cr1/_cr2/
    // _cr3/isCandHI_whnfAcc/isCandHI_piSet/isCandHI_weaken), R5's PiSet,
    // candHF_var_mem, r5_omegaLam, r5_whnfAcc_omegaLam and
    // r5_omegaV_not_whnfAcc.
    //
    // A — THE SHAPE DOMAIN. Sk (ty / kd s / arr d c), domSk, piShape, and the
    // large elimination VD : Sk -> Type 1 with VD (arr d c) = VD d -> VD c —
    // the definition that makes a SEMANTIC FUNCTION representable at all, since
    // an inductive SVal | fn : (SVal -> SVal) -> SVal is not strictly positive.
    // vcarD reads the candidate out, mkTyD packages one at a Pi-shape
    // (vcarD_mkTyD), junkD/goodD_junkD make GoodD inhabited at every shape, and
    // Val/valS/valD/valCar/valGood are the corpus's packaged Sigma s : Sk, VD s.
    // GoodSet is a one-line Type 1 lift of IsCandHI (no new inductive), forced
    // because GoodD's arr clause quantifies over VD d : Type 1 and the kernel is
    // NON-CUMULATIVE. The dependent valuation VEnvD D := forall i, VD (D i)
    // deletes MatchEnv, coeD and the decidable equality on Sk that the corpus's
    // total interpretation needs.
    //
    // B — THE INTERPRETATION. WK is the corpus's shape typing on KExpr/Level
    // (levels semantically INERT: every sort gets kd ty, which is why Level's
    // param/max/imax trees cost this route nothing). sval recurses on the SHAPE
    // DERIVATION; lam denotes a semantic function and app semantic application.
    // (i) candidate-hood: sval_good, through R10's LANDED isCandHI_piSet with
    // candStepInv discharged by the identity. (ii) CONVERSION-INVARIANCE
    // ACHIEVED: r12_sval_beta is Eq.refl at every shape-typed redex and every
    // valuation, and r12_sval_beta_contractum states it at the SYNTACTIC
    // contractum. r12_conv_contrast pairs r11_candInterp_step_conv_refuted with
    // the same whnf_step transported through sval, in ONE kernel-checked
    // constant — same calculus, same real environment, one interpretation
    // refuted and the other proved.
    //
    // C — THE DEPENDENT PI CLAUSE, what R6 proved non-portable for candInterp:
    // wkPiDep interprets the codomain in the valuation EXTENDED BY THE
    // ARGUMENT'S OWN VALUE, so R6's unmeasurable candInterp (instantiate B a)
    // becomes an environment extension on the structurally smaller B.
    // isCandHI_wkPiDep proves it a candidate and wkPiDep_elim is the DEPENDENT
    // elimination. It is a construction ON TOP of sval and not a clause of
    // sval's own recursion, forced by two PROVED obstructions: the UNIVERSE horn
    // (piCandV, the corpus's value-quantified clause, is registered at its true
    // KExpr -> Type 1 — one above VD Sk.ty — because Type is PREDICATIVE where
    // the corpus's Prop is impredicative, and shifting does not close it; the
    // kernel refuses the same clause at KExpr -> Type) and the RECURSION horn
    // (the Type-0 derivation-indexed replacement calls sval at derivations of
    // unrelated terms, so it is not structural).
    //
    // HONESTY: no SN capstone — WK is a SHAPE system and sval_good gives
    // candidate-hood, not whnf_acc of the term. No semantic substitution lemma
    // and no general one-step invariance: both are funext applications in the
    // corpus (val_psub/val_lift/piVal_congr/lamVal_congr) and the spec has NO
    // funext by design. [SUPERSEDED 2026-08-27 by the R13 stage immediately
    // below: funext IS derivable here, is registered as spec_funext with zero
    // new axioms, and the congruence lemmas have landed. What blocks
    // val_psub/val_lift now is the absence of a substitution/weakening
    // OPERATION on WK derivations.] sval is PARTIAL where candInterp is total — R11's own
    // redex is not shape-typed — so nothing here advances
    // whnf_terminates_well_typed_dependent or discharges M : CandModel tenv.
    // Non-degeneracy: r12_sval_pi_proper (r5_omegaLam is OUT) paired with
    // r12_sval_pi_var_witness (bvar 0 is IN).
    // Census-NEUTRAL: every constant value-bearing, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r12,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // R13 — funext, DERIVED, and R12's wall comes down.
    //
    // R12 recorded "the spec has NO funext — by design", citing
    // dependent_sn_richmodel.rs:664. That was true of what was REGISTERED and
    // false of what is DERIVABLE. spec_fneq quotients the dependent function
    // space by pointwise equality, spec_fnapp extracts an application map with
    // Quot.lift (its respect obligation at the point x IS the pointwise
    // hypothesis at x), and spec_funext pushes Quot.sound through that map with
    // the spec's explicit-argument Eq.cong; both sides reduce back to the
    // functions by quotient iota (quot.rs:598, wired at tc/whnf.rs:712), beta
    // and function eta (tc/eta.rs). Lean 4 core's proof, in the spec's own
    // source language.
    //
    // It survives a Type-valued candidate calculus because Quot's relation
    // argument is fixed at Prop and the spec's Eq is Prop-valued at EVERY
    // domain sort, so `forall (x : A), Eq (B x) (f x) (g x)` lands in
    // Sort (imax u 0) = Prop however big u is. Nothing asks a Type to be a
    // Prop — which is exactly what propext would have required, and why R12 was
    // right that propext is unusable here.
    //
    // This stage calls Environment::init_funext FIRST. The Substitution bundle
    // starts from a bare Environment::new() and reaches init_quot only in the
    // FULL bundle, transitively through add_boolean_analysis_spec -> init_rat
    // (the live Rat IS a quotient), a stage that is in_substitution: false;
    // init_quot itself is pub(crate) to clean-kernel and init_funext is the
    // public entry point that reaches it. It is idempotent, so the later
    // init_rat is a no-op on the quotient side.
    //
    // CENSUS-NEUTRAL: Quot.sound and the Quot/Quot.mk/Quot.lift/Quot.ind
    // formers are already five of the live census's eleven entries and all sit
    // in the kernel's FOUNDATIONAL_AXIOMS (env/axiom_audit.rs:32-75), so
    // Environment::axiom_deps filters them and computed_axiom_closure is EMPTY
    // for every R13 constant. `funext` itself is a value-bearing
    // Declaration::Theorem — axiom_audit.rs:57-67 records its demotion OUT of
    // FOUNDATIONAL_AXIOMS when it stopped being an axiom — and never was a
    // census entry. ZERO new axioms.
    //
    // PART B, what it knocks out: r13_vd_arr_funext (semantic functions at an
    // arrow shape), r13_venvD_funext (valuations; VEnvD D is a DEPENDENT
    // function space so this needs dependent funext), r13_sval_env_congr (the
    // payoff — the interpretation respects pointwise-equal valuations at every
    // shape environment, term, shape and derivation), r13_vconsD_env_congr,
    // r13_piCandDep_fn_congr and r13_wkPiDep_env_congr (the piB congruence
    // cases, which need no propext at all: the congruence is one Eq.cong in the
    // FUNCTION argument, never a biimplication between two Types).
    //
    // HONESTY: R12's TWO HORNS are untouched and still stand — HORN 1 is
    // predicativity (piCandV lands one universe above the candidates, offset
    // invariant under shifting) and HORN 2 is that the derivation-indexed
    // clause calls sval at derivations of unrelated terms, so it is not
    // structural. Extensionality is neither. val_psub / val_lift are still NOT
    // registered and the reason CHANGED: R12 built no substitution or weakening
    // OPERATION on WK derivations and the corpus lemmas are statements about
    // one — R13 lands the congruence engine those proofs consume, not the
    // proofs. No SN capstone, sval is still PARTIAL, nothing here advances
    // whnf_terminates_well_typed_dependent or discharges M : CandModel tenv.
    // Non-degeneracy is a MEASUREMENT: spec_funext_witness equates
    // `fun n => Nat.add Nat.zero n` with `fun n => n` (not definitionally
    // equal — Nat.add recurses on its SECOND argument) and two refusal tests
    // assert the kernel REJECTS Eq.refl at that statement and at the general
    // one with the pointwise hypothesis in hand.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r13,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // CANDIDATE-MODEL LADDER R14 (`candmodel_construct_r14.rs`): THE WEAKENING
    // AND SUBSTITUTION OPERATIONS ON `WK` DERIVATIONS, and the semantic lemmas
    // they exist for. MUST follow add_candmodel_construct_r12 (Sk / skcons / WK
    // / sval / VD / VEnvD / vconsD / junkD / domSk / piShape / mkTyD / vcarD /
    // PiSet / r12_piEnv / r12_beta_contractum_is_arg) and
    // add_candmodel_construct_r13 (r13_venvD_funext, r13_vd_arr_funext — every
    // valuation law and both lam cases run on them). Also consumes
    // add_expr_model (lift_at / lift_bvar_at / instantiate),
    // add_dependent_sn_richmodel (psubst / up / scons / idsubst /
    // instantiate_eq_psubst), add_whnf_reduction (whnf_step / beta_reduces) and
    // add_foundation_arith_lemmas (nat_sub_zero_left / nat_sub_succ_succ).
    //
    // R13 named the binding constraint exactly: "R12 built no substitution or
    // weakening OPERATION on WK derivations, and the corpus lemmas are
    // statements about one." This is that operation pair — wk_lift (corpus
    // FWK.lean:109) with wk_lift0, wk_up and wk_psub (FWK.lean:149) with
    // wk_inst — and then val_lift / val_psub / val_inst / val_beta, the four
    // constants R13 recorded as not registered.
    //
    // The design decision that pays for the rung: `skins` recurses on the
    // CUTOFF, not on a decidable comparison, so skins (succ c) t (skcons s D)
    // is DEFINITIONALLY skcons s (skins c t D) and every binder case of wk_lift
    // is transport-free. The whole rung has three transport sites, and
    // r14_skins_zero / r14_skins_succ are Eq.refl GUARDS over that.
    //
    // Two pieces of machinery are new: r14_sval_cast_term / r14_sval_cast_shape
    // (sval recurses on the DERIVATION, so a transported derivation does not
    // reduce; both are based Eq.rec with a PROOF-DEPENDENT motive) and
    // r14_vdCast_refl / r14_vdCast_irrel / r14_cast_idx. Two elaborator facts
    // were MEASURED building them: Eq.substType does NOT delta-unfold, so every
    // transport a later proof must reduce through goes through a def over a
    // bare Eq.rec (r14_wkCastT / r14_wkCastS / r14_vdCast); and a proof-
    // irrelevance step must be a STANDALONE constant the proof term applies,
    // because the elaborator's unifier refused the identical step written
    // inline as an Eq.rec minor (fvar mismatch between the proof binders) while
    // the kernel accepts it as its own declaration. r14_vdCast_refl separately
    // records that a cast along a stuck REFLEXIVE proof computes at all, which
    // is K-like reduction of Eq and not irrelevance.
    //
    // 47 constants: 16 add_recursive_def and 31 value-bearing theorems.
    //
    // HONESTY: this is NOT val_step and NOT val_conv. R14 lands val_step's BETA
    // arm at the real whnf_step (r14_beta_step + r14_val_beta +
    // r14_sval_transports_real_beta) plus the congruence COMBINATORS its other
    // arms consume; the arms themselves need wk_step (subject reduction for
    // shapes), which needs inversion of the spec's NINE-constructor whnf_step —
    // delta, iota, zeta, let_, proj, forall_ — not the corpus's five-
    // constructor Step. R12's two horns (predicativity, structural recursion)
    // and R10/R11's refutations are untouched. No SN capstone; sval is still
    // PARTIAL; nothing here discharges M : CandModel tenv. Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r14,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // CANDIDATE-MODEL LADDER R15 (`candmodel_construct_r15.rs`): SUBJECT
    // REDUCTION FOR SHAPES (`wk_step`) and the `val_step` arms it unlocks. MUST
    // follow add_candmodel_construct_r12 (Sk / skcons / WK / sval / VD / VEnvD /
    // vconsD / junkD / domSk / piShape / mkTyD / vcarD / r12_betaEnv /
    // r12_betaRedex / r12_betaDeriv / r12_betaJunkEnv / r12_candInterpStepConv),
    // add_candmodel_construct_r13 (r13_vd_arr_funext) and
    // add_candmodel_construct_r14 (wk_inst, r14_wkCastT, r14_sval_cast_term,
    // r14_sval_pi_congr, r14_vapply_congr, r14_val_inst, r14_val_beta,
    // r14_beta_step). Also consumes add_candmodel_construct_r1 (whnfStar),
    // add_candmodel_construct_r5 (HeadFree / headFree_app),
    // add_candmodel_construct_r11 (r11_candInterp_step_conv_refuted),
    // add_dependent_sn_richmodel (ConstFreeUnit), add_whnf_reduction
    // (whnf_step / beta_reduces), add_par_reduces_c
    // (iota_step_head_none_absurd_type) and add_par_reduces_d_diamond
    // (delta_step_head_none_absurd_type).
    //
    // R14 named the single remaining gap exactly: "the piA/piB/lamA/lamB/appL/
    // appR arms of val_step, and val_conv. They need wk_step (subject reduction
    // for shapes), which needs inversion of the spec's whnf_step over delta /
    // iota / zeta / let_ / proj / forall_ across NINE KExpr constructors." This
    // is that rung. wk_step : WK D e s -> whnf_step e e2 -> WK D e2 s,
    // unconditional and total, registered as a def so a later rung can reduce
    // through it.
    //
    // THE IDIOM THAT PAID FOR IT: every inversion is a COMPUTED MOTIVE — a
    // KExpr.rec on the SUBJECT (nested with an Sk.rec on the shape where
    // needed) that maps each head constructor to the continuation-passing
    // statement it deserves and every other head to ConstFreeUnit. That is
    // R12's Neutral read as an inversion principle, and it deletes the whole
    // X_ne_Y / X_inj_* scaffold R1/R3/R5's beta_inv_body needs: fourteen of
    // beta_reduces' fifteen arms are ONE token (ConstFreeUnit.triv for the
    // let_/proj heads, one continuation call with Eq.refl for the live ones).
    // The iota arm is the only one whose subject is a variable and so the only
    // one computation cannot discharge; r15_headFree_wk kills it and whnf_step's
    // delta leg with the same fact — WK has no const constructor, so no
    // shape-typed term is a delta or iota redex.
    //
    // PART B: the six named val_step arms at given derivations
    // (r15_val_step_piA/piB/lamA/lamB/appL/appR — lamA needs NO hypothesis, the
    // annotation is semantically inert), then r15_val_step_sem, the FUSED
    // theorem carrying subject reduction and semantic invariance in one WK.rec,
    // r15_val_star_sem over whole reduction sequences, and
    // r15_sval_transports_any_step / r15_sval_transports_congr_step /
    // r15_conv_contrast — R11's refutation paired with a transport across a REAL
    // congruence step, which is the class R14 could not touch.
    //
    // HONESTY: the FORALL-form of val_step and val_conv are NOT claimed. Both
    // need sval DERIVATION IRRELEVANCE, and r15_val_conv_from_irrel proves
    // kernel-checked that it is the ONLY missing ingredient (confluence is not
    // additionally needed for the joinable form). R12's two horns and R10/R11's
    // refutations are untouched; no SN capstone; sval is still PARTIAL. Zero new
    // axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r15,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // CANDIDATE-MODEL LADDER R16 (`candmodel_construct_r16.rs`): SVAL DERIVATION
    // IRRELEVANCE — the single ingredient R15 proved val_conv and the FORALL-form
    // of val_step were missing — and the two payoffs it unlocks. MUST follow
    // add_candmodel_construct_r12 (Sk / skcons / WK / sval / VD / VEnvD / domSk /
    // piShape / vcarD / r12_betaEnv / r12_betaRedex / r12_betaDeriv /
    // r12_betaJunkEnv / r12_candInterpStepConv), add_candmodel_construct_r14
    // (r14_beta_step) and add_candmodel_construct_r15 (r15_val_step_sem,
    // r15_val_star_sem, r15_val_conv_from_irrel, r15_instDeriv,
    // r15_wk_step_witness, r15_wk_step_sort). Also consumes
    // add_candmodel_construct_r1 (whnfStar), add_candmodel_construct_r11
    // (r11_candInterp_step_conv_refuted), add_whnf_reduction (whnf_step /
    // beta_reduces) and the foundation's Eq / Eq.rec / AndType / Empty.
    //
    // R15 named the gap as a kernel-checked constant rather than as prose:
    // r15_val_conv_from_irrel proves val_conv follows from
    // `forall (h1 h2 : WK D e s) r, sval h1 r = sval h2 r` and from nothing else.
    // This rung discharges it — and lands a STRONGER statement than R15's route
    // asked for, because shape uniqueness makes it reachable:
    // r16_wk_deriv_unique says WK IS A SUBSINGLETON (any two derivations of one
    // term at one shape are EQUAL, since shape assignment is syntax-directed and
    // its shapes are unique), after which r16_sval_irrel is ONE Eq.cong. R15
    // budgeted five sval-valued inversions; ONE derivation inversion sufficed,
    // and R13's funext / R14's sval congruences were not needed at all.
    //
    // THE IDIOM IS R15's, CARRIED FORWARD: r16_wkT is a computed motive — a
    // KExpr.rec on the SUBJECT sending each head to the CPS case analysis its WK
    // rule deserves and const/let_/proj/lit to r16_propUnit, so those four arms
    // die by COMPUTATION. Every live arm of r16_wk_inv hands its own constructor
    // fields to the continuation with Eq.refl and the reflexive shape cast
    // computes away by plain iota, so THE INVERSION ITSELF USES NO K. Shape
    // uniqueness goes through a term-recursive r16_shapeOf rather than through
    // five CPS inversions, and Sk.arr's second-component injectivity is one
    // Eq.cong through the computed r16_arrCod — no discrimination lemma anywhere.
    //
    // THE ONE K STEP IS QUARANTINED. After the based path inductions in
    // r16_pi_align / r16_lam_align the leftover shape equation is REFLEXIVE but
    // is a variable proof, so plain iota does not fire; Eq is K-like in this
    // kernel, so the cast computes away. That reliance lives in exactly one
    // constant, r16_wkCastS_refl, never inlined as a recursor minor, and it is a
    // kernel REDUCTION RULE rather than an axiom — computed_axiom_closure is
    // empty for all 22 headline constants. r16_app_align needs neither a J pair
    // nor a cast: WK.app carries the codomain shape as a bare index.
    //
    // PAYOFF: r16_val_conv (val_conv UNCONDITIONALLY), r16_val_step /
    // r16_val_step_star (the FORALL-form of val_step, R15's obstruction 2, closed
    // — PropBox is the non-cumulativity bridge, since R15's fused theorems
    // quantify over C : Type and an Eq is a Prop), and r16_conv_contrast: R11's
    // refutation paired with unconditional conversion-invariance for sval at a
    // pair that CONVERTS without either side reducing to the other. R12's two
    // horns and R10/R11's refutations are untouched; no SN capstone; sval is
    // still PARTIAL. Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r16,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // CANDIDATE-MODEL LADDER R17 (`candmodel_construct_r17.rs`): THE CONSTRUCTOR
    // GAP — `const` and `let_` land on the WK/sval lineage, with every operation
    // R14-R16 built extended to them, and the conversion-rule question SETTLED.
    // MUST follow add_candmodel_construct_r12 (Sk / skcons / domSk / piShape /
    // VD / VEnvD / vconsD / vcarD / mkTyD / PiSet / junkD / r12_piEnv /
    // r12_betaEnv / r12_junkEnv / r12_betaJunkEnv), add_candmodel_construct_r14
    // (skins / r14_wkpos / r14_skins_idx / r14_lift_at_bvar_wkpos),
    // add_candmodel_construct_r15 (r15_whnf_stepT_inv, r15_instDeriv) and
    // add_candmodel_construct_r16 (r16_arrCod, r16_propUnit, r16_shapeOf,
    // r16_shape_correct, PropBox / r16_propBox_intro). Also consumes
    // add_candmodel_construct_r1 (letRedex_whnf_inv),
    // add_candmodel_construct_r2 (constRedex_whnf_inv),
    // add_candmodel_construct_r10 (HeadInert / headInert_app /
    // inertConst_headInert), add_the_red_env (the_red_env_delta_nonvacuous,
    // kcre_name_12, kcre_witness_delta_head / _value),
    // add_par_reduces_iota_delta (delta_reduct_eq_none_of_defval_none),
    // add_whnf_reduction (whnf_step / beta_reduces / whnf_acc) and the
    // foundation's Eq / Eq.rec / AndType / Empty / ConstFreeUnit.
    //
    // R16 closed with a verdict rather than a handoff: "the next question is the
    // four missing constructors and the conversion rule themselves, not another
    // WK metatheorem." This rung moves TWO of the four onto the lineage that has
    // the metatheory, and carries the metatheory with them.
    //
    // WKC is R12's WK verbatim in its five landed constructors plus konst (an
    // INERT constant — R10's two side conditions, spelled as Eq's so proof
    // irrelevance keeps the system a subsingleton — at Sk.ty) and let_ (three
    // premises, binder slot carrying the shape of the VALUE). xval is the
    // seven-clause interpretation. Both restrictions are PROVED rather than
    // argued: r17_unrestricted_konst_refuted pairs a REAL delta step out of a
    // REAL reflected constant (the_red_env_delta_nonvacuous, whose target is a
    // lam — R9's finding about every real body in the_red_env) with
    // r17_lam_never_ty, so a Sk.ty-valued rule at a delta-ACTIVE constant loses
    // subject reduction outright.
    //
    // LANDED, at seven constructors: wkc_lift / wkc_lift0 / wkc_up / wkc_psub /
    // wkc_inst (R14's five), wkc_step (R15's subject reduction),
    // r17_shape_correct / r17_wkc_shape_unique / r17_wkc_deriv_unique /
    // r17_xval_irrel (R16's stack). THE SUBSINGLETON SURVIVES — both new rules
    // are keyed by the subject's head constructor, konst's only freedom is in
    // Prop, and let_'s two existential shapes are pinned by shape uniqueness —
    // so r17_xval_irrel is still ONE Eq.cong.
    //
    // THE STRUCTURAL FACT that kept subject reduction cheap:
    // r17_headFree_wkc_arr. Adding const re-opens delta and iota, which R15 had
    // closed by proving WK never types a const-headed spine; the replacement is
    // that WKC never types one AT AN ARROW SHAPE (WKC.konst concludes at Sk.ty
    // and nowhere else, and WKC.app's function premise is at an arrow).
    // Consequence: R15's r15_whnf_stepT_inv is reused VERBATIM in five of
    // wkc_step's seven arms, R1's letRedex_whnf_inv covers the sixth and
    // r17_const_no_step refutes the seventh — R10's HeadInert INVERSION
    // machinery is not needed by subject reduction at all. r17_headInert_wkc is
    // registered anyway, because that is where the konst rule's SECOND premise
    // earns its place.
    //
    // r17_xval_zeta is Eq.refl: SEMANTIC ZETA IS DEFINITIONAL, the analogue of
    // R12's r12_sval_beta. R1's refutation of the generic per-set zeta ENGINE
    // does NOT transfer — R1 is about candidate SETS closing under expansion for
    // an arbitrary S, xval is an INTERPRETATION reading a valuation.
    //
    // THE CONVERSION RULE IS SETTLED AND DELIBERATELY NOT BUILT. On WKV (two
    // leaf rules plus conv at the FINEST possible relation, Eq Sk):
    // r17_conv_shape_unique proves shape assignment SURVIVES, and
    // r17_conv_breaks_subsingleton proves derivation uniqueness does NOT.
    // r17_conv_verdict pairs them. So adding conv to WKC would keep the shapes
    // and lose R16's one-line route to interpretation irrelevance.
    //
    // NOT LANDED: proj and lit (r17_wkcT's dead arms drop 4 -> 2 and those two
    // are what is left), and no xval-side re-derivation of R14/R15's SEMANTIC
    // lemmas — what transfers today is r17_wk_wkc and r17_shapeOf_agrees_on_wk.
    // R10's cr3 refutation, R11's candInterp conversion refutation and R12's two
    // horns are untouched; no SN capstone. Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_candmodel_construct_r17,
        in_substitution: true,
        in_impl_soundness: false,
    },
    // REAL-ENV CONFLUENCE DISCHARGE: the hypothesis-free Church-Rosser corollaries
    // (par_reduces_c_star_diamond_faithful / par_reduces_p_star_diamond_faithful) —
    // the generic star-diamonds (add_par_reduces_p_topdev) instantiated at
    // env := red_rec faithful_red_env with the four interface hypotheses discharged
    // by the honest DerivedProved witnesses (add_faithful_red_env_bundle: i1
    // faithful_red_env_reduct_not_redex, i3 faithful_rec_env_closed, i4
    // faithful_rec_env_lift_closed; add_faithful_red_env: i2
    // faithful_rec_env_ctor_no_recmeta). MUST follow BOTH add_par_reduces_p_topdev
    // (both star-diamonds) and add_faithful_red_env_bundle (all four witnesses).
    // Pure application; zero new axioms.
    CoreSpecStage {
        apply: Specification::add_faithful_confluence,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // UNIQUE NORMAL FORMS of par_reduces_c_star (Aristotle port-back, Item 3):
    // is_normal_c ("reduces only to itself" — the honest normality for the
    // REFLEXIVE par_reduces_c) + normal_c_star_eq + unique_normal_forms_c (via
    // the proved par_reduces_c_star_diamond, carrying its four faithful
    // interfaces) + the hypothesis-free unique_normal_forms_c_faithful over
    // faithful_red_env. MUST follow add_par_reduces_p_topdev (the diamond) and
    // add_faithful_red_env_bundle / add_faithful_red_env (the four witnesses).
    // Pure corollary layer; zero new axioms.
    CoreSpecStage {
        apply: Specification::add_unique_normal_forms_c,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Canonical forms at Pi for the CONTEXT-INDEXED, SYNTAX-DIRECTED (conv-free)
    // CtxTyping fragment (Aristotle port-back, Item 4): new object-of-study
    // inductives (CtxLookup / CtxTyping / CanonAt / IsLamShape — real
    // add_inductive registrations, NOT census axioms) + the canonical-forms
    // ladder over beta_reduces_bd normality. DISTINCT from the spec's
    // context-free Typing; no bridge is registered. Depends only on earlier
    // stages: expr_model (KExpr/ListType/lift_at/instantiate), foundation
    // (Nat/Bool/Empty/Eq), typing_universe_levels (imax_nat),
    // expr_model_pi_discrimination (sort_ne_pi), par_reduction
    // (beta_reduces_bd), complete_development (kexpr_is_lam). Zero new axioms.
    CoreSpecStage {
        apply: Specification::add_ctx_canonical_forms,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // Pi injectivity at DefEq level, re-pointed through confluence (carries the
    // RedEnvFaithful the_red_env hypothesis). MUST follow add_par_reduces_cd_sound
    // (join_to_def_eq) + add_par_reduces_cd_injectivity (par_cd_pi_injectivity) +
    // add_def_eq_joinable. Replaces the former church_rosser_whnf-backed derivation.
    CoreSpecStage {
        apply: Specification::add_pi_injectivity_def_eq,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_reduction_witnesses,
        in_substitution: true,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_substitution_def_eq_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // DefEq lift/instantiate argument congruence (depends on substitution_def_eq)
    CoreSpecStage {
        apply: Specification::add_def_eq_lift_congr_lemmas,
        in_substitution: true,
        in_impl_soundness: true,
    },
    // === Substitution bundle ends here (33 stages) ===
    // Type preservation and micro-checker
    CoreSpecStage {
        apply: Specification::add_type_preservation,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Weakening / lift preservation over the reflected Typing judgment (the third
    // structural metatheorem, alongside substitution_typing and forward subject
    // reduction). ADDITIVE, ZERO new axioms: depends on Typing.rec + the Typing.*
    // constructors (add_typing_def_eq, earlier), the lift structural lemmas
    // (add_expr_model_lift_lemmas, earlier), lift_instantiate_swap
    // (add_expr_model_lift_instantiate_swap, earlier), nat_zero_add (foundation
    // arith, earlier), and def_eq_respects_lift_at_gen (add_def_eq_lift_congr_lemmas,
    // earlier). Genuinely DerivedProved with empty non-foundational debt (the conv
    // arm's def_eq_respects_lift_at_gen is itself empty-debt DerivedProved).
    CoreSpecStage {
        apply: Specification::add_type_preservation_weakening,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_type_preservation_raw_bridge,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Forward subject reduction over beta_reduces / whnf_to (the church_rosser_whnf
    // retirement keystone). ADDITIVE: depends on the generation lemmas +
    // beta_preservation + lam_typing_dom_sort + def_eq_instantiate_arg_congr (all
    // registered by add_type_preservation) and delta/iota_type_preservation_fwd
    // (add_reduction_witnesses, earlier) + the beta_reduces/whnf_step/whnf_to
    // inductives (add_whnf_reduction, earlier). ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_beta_reduces_preserves_typing,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_micro_checker,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_micro_soundness,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Faithful micro-checker verification relation, Brick 1
    // (micro_verifies_r0.rs): the FRESH-NAME context-indexed MicroVerifies
    // (sort + bvar arms ONLY, arm-for-arm with micro/checker.rs::verify_impl),
    // the ctx_lookup/translation commutation, the per-arm kernel agreement
    // theorems (bvar via the already-proved kernel_to_micro_lift_commute),
    // ground positive witnesses, a lift-arithmetic pin, and the empty-context
    // bvar REJECTION witness. Never re-points any existing producer (the
    // Brick-6 fresh-names constraint, micro_soundness.rs:33-38). FULL-ONLY:
    // it consumes the micro band (add_micro_checker / add_micro_soundness,
    // directly above — ImplementationSoundness-only) AND ctx_lookup /
    // option_none_ne_some_type-side vocabulary whose home stage
    // add_dependent_sn_richmodel is Substitution-only, so the only bundle
    // containing its whole dependency closure is Full — same pattern as
    // add_closedness_bundle. Census-NEUTRAL: one genuine inductive, four
    // value-bearing defs, seven kernel-checked theorems, ZERO new axioms.
    CoreSpecStage {
        apply: Specification::add_micro_verifies_r0,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_env_extensions,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Implementation soundness core
    CoreSpecStage {
        apply: Specification::add_implementation_soundness,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Faithful KernelInferAccepts + KernelCheckAccepts inductives (Steps 3+4)
    // + the 10 infer-band skolems their constructor fields apply + the master
    // inversion. Must come directly after the core stage (KernelWhnfAccepts /
    // KernelDefEqAccepts / KernelStateEnvValid / KernelInputAdmissible are
    // registered there) and before the infer_refinement band whose six
    // flipped per-case lemmas project from kernel_infer_inversion.
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_accepts,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_admissibility,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // De Bruijn closedness bundle (census-11 drain, Stage 2A): the PROVED
    // lift/instantiate/beta_reduces closedness lemmas ported from
    // scratch/aristotle-harvest/aristotle-debruijn-lt/aristotle-debruijn-lt_aristotle/DeBruijnLt.lean.
    // Needs the is_closed_at
    // body/type inversions (add_implementation_soundness_admissibility, above)
    // plus the Lt/Le arithmetic (add_dependent_sn_richmodel, earlier).
    // NOT in the ImplementationSoundness subset bundle: it depends on the
    // NatLtLeDichotomy / Lt-Le arithmetic from add_dependent_sn_richmodel,
    // which is Full-only (in_impl_soundness: false) — including it there broke
    // the subset builder ("Unknown identifier: NatLtLeDichotomy.rec"; 10 lib
    // tests, latent since Stage 2A landed with in_impl_soundness: true). Its
    // only consumers are the Stage-2B iota closedness bundle (below) and
    // tc_infer_soundness (type_checker_spec, registered by
    // Specification::new() only), so Full-only is the honest slot.
    CoreSpecStage {
        apply: Specification::add_closedness_bundle,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Iota/whnf/infer closedness bundle (census-11 drain, Stage 2B): hiota
    // (iota-reduction preserves closedness) + its ~8 structural helpers, then
    // (Stage 2B-ii) whnf/infer closedness preservation. Needs the closedness
    // bundle (above), the iota CPS inverter (add_iota_core), the RecEnvClosed/
    // RecEnvLiftClosed interfaces (add_rec_env_closed), iota_reduces_to_step
    // (add_iota_step_bridge), and KernelWhnfAccepts/KernelInferAccepts
    // (add_implementation_soundness / add_implementation_soundness_infer_accepts)
    // — all earlier stages. Full-only for the same reason as the closedness
    // bundle above (dependent_sn_richmodel arithmetic + the bundle itself);
    // its sole downstream consumer is tc_infer_soundness (Full-only).
    CoreSpecStage {
        apply: Specification::add_iota_closedness_bundle,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_whnf_decomposition,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Subject reduction for the context-indexed TypingCtxConv judgment
    // (Aristotle SubjRed.lean port): the TypingEnvCoherent labeled-hypothesis
    // interface, the CtxWk weakening tower, def_eq_psubst, the psubst-general
    // substitution lemma, context conversion, CPS generation lemmas, and the
    // delta/beta/whnf-step preservation theorems. Placed HERE because it
    // consumes: TypingCtxConv + the psubst calculus (add_dependent_sn_richmodel,
    // Full+Substitution only), pi_injectivity_def_eq_dom/_cod
    // (add_pi_injectivity_def_eq, Full+ImplSoundness only),
    // def_eq_respects_lift_at_gen (add_def_eq_lift_congr_lemmas),
    // def_eq_instantiate_arg_congr (add_type_preservation), and the UNTYPED
    // beta_reduces_preserves_def_eq (add_implementation_soundness_whnf_decomposition,
    // directly above). Full-only: it needs stages excluded from both subset
    // bundles. Purely additive; zero new axioms (all hypotheses carried:
    // TypingEnvCoherent + RedEnvFaithful/DefEnvWellformed/RecEnvWellformed).
    CoreSpecStage {
        apply: Specification::add_subject_reduction_bundle,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Wall-A completeness statement machinery (Aristotle WallA.lean port):
    // the HeadMatch inductive (success condition of one kernel structural
    // def-eq comparison round on two whnf results) + non-vacuity witnesses +
    // the head_match_reflects soundness anchor. The mirror's
    // def_eq_joinable_mirror is the LANDED in-tree def_eq_joinable (mapped,
    // not re-ported); the def_eq_whnf_complete completeness theorem is a
    // noted follow-up (needs par_reduces_cd_star head-rigidity inversion,
    // which does not exist in-tree yet). Needs only DefEq/const_whnf
    // (typing_def_eq / whnf_reduction, far earlier); placed alongside the
    // subject-reduction port for review locality. Full-only; zero new axioms.
    CoreSpecStage {
        apply: Specification::add_wall_a_headmatch,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Wall-A COMPLETION (Aristotle WallAIota port): the iota-aware WHNF
    // vocabulary (iota_immune/iota_neutral/iota_whnf — PARALLEL predicates,
    // trusted is_neutral/is_whnf untouched), the whnf_to->cd_star bridge, the
    // const/neutral head-rigidity star-inversion family, and
    // def_eq_whnf_complete itself. Needs HeadMatch (previous stage),
    // def_eq_joinable, the landed cd_star diamond + sort/lam/pi star
    // inversions, and join_to_def_eq (all far earlier). Full-only; zero new
    // axioms.
    CoreSpecStage {
        apply: Specification::add_wall_a_completeness,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_defeq_decomposition,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Register the local check bridge before the app packet so app-case
    // infer soundness can reuse it without depending on the global infer
    // theorem.
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_check_decomposition,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement_app,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // app_sound registers infer_sound_at_app, which the dispatch stage
    // references in kernel_infer_returns_well_typed's KExpr.rec invocation.
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement_app_sound,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement_binder,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement_binder_typing,
        in_substitution: false,
        in_impl_soundness: true,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement_binder_sound,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // Dispatch now carries a real KExpr.rec proof term, so it must register
    // after the app/lam/pi case wrappers it references.
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_infer_refinement_dispatch,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // The global check theorem is layered on top of the local bridge and the
    // now-registered infer theorem.
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_check_sound,
        in_substitution: false,
        in_impl_soundness: true,
    },
    // simulation and env_preservation are Full-only
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_simulation,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_implementation_soundness_env_preservation,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // SAT verification: CDCL invariant specifications (S01-S06).
    // Uses only Nat and Eq from foundation types, so can go at the end.
    CoreSpecStage {
        apply: Specification::add_cdcl_sat_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_proof_complexity_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_interpolation_sat_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // GF(2) Polynomial Calculus: clause-poly, Tseitin separation, Groebner (GF01-GF03).
    CoreSpecStage {
        apply: Specification::add_gf2_polynomial_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Proof-guided CDCL: width-size trade-off, restart optimality,
    // space-width, and restart satisfiability preservation (PG01-PG04).
    // PG04 is the soundness/completeness acceptance criterion for #3343.
    CoreSpecStage {
        apply: Specification::add_proof_guided_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Boolean analysis: KKL inequality chain (S41-S43, S46, S50).
    // Kernel axioms registered as spec definitions for proof library tracking.
    CoreSpecStage {
        apply: Specification::add_boolean_analysis_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Bootstrap trust chain: model fidelity and type preservation transfer.
    CoreSpecStage {
        apply: Specification::add_bootstrap_trust_chain_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Interval arithmetic: containment, structural, width, algebraic (T01-T20).
    CoreSpecStage {
        apply: Specification::add_interval_arith_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Zonotope soundness: T01-T08 + Minkowski sub-claims (#3363).
    CoreSpecStage {
        apply: Specification::add_zonotope_spec,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // SnSchema LEMMA half (task #32, Brick 4b+): env-lookup lemmas
    // (genREnv_meta_rec/genRecRules_lookup/genREnv_ok), the object-level iota
    // realization (genRecContract_steps), and the §10a' Nat→Gen bridges.
    // Placed LAST: a terminal SnSchema lemma layer that nothing depends on, so
    // ALL machinery it consumes (name_eqb_refl from kexpr_beq, the psubst
    // β-chain, the Nat contract, option/list helpers) is guaranteed registered.
    // Full-bundle only.
    CoreSpecStage {
        apply: Specification::add_snschema,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Universe-polymorphism rung (7th fragment increment, opener): semantic
    // Level theory — evalL/substL, the semantic order levelLeqSem/levelEqSem,
    // evalL_substL, and the substitution-stability theorems, ported from the
    // Aristotle-proven r3-univ-poly guide. Terminal lemma layer (consumes only
    // foundation Nat/Bool/Le + Level + Eq machinery). Full-bundle only.
    CoreSpecStage {
        apply: Specification::add_univ_poly,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Mutual-inductive schema rung (8th increment), Brick M1: FamSpec block
    // element + block arithmetic + per-family recursor names/consts/motives.
    // Ported from the Aristotle-proven r3-mutual-schema guide. Terminal layer.
    CoreSpecStage {
        apply: Specification::add_mutual_schema,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Higher-order-fields (W-type/Acc) rung, object layer + rfl validations.
    // Ported from the Aristotle-proven w5-acc-wtype guide. Terminal layer.
    CoreSpecStage {
        apply: Specification::add_acc_wtype,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Nested-inductive (rose-tree) rung, object layer + rfl gates + SN one-liner.
    // Ported from the Aristotle-proven nested-rose guide. Terminal layer.
    CoreSpecStage {
        apply: Specification::add_rose_schema,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // EvalIR: the Clean-side executable semantics for trust-ir (crystal job C3).
    // Position is nearly free — the stage's only prerequisites are Nat, Bool and
    // Eq from add_foundation_types, and every name it registers is IR*/ir_*
    // prefixed, so it collides with nothing. It sits here rather than early so a
    // failure in it cannot mask a failure in the metatheory lane, and BEFORE the
    // kexpr_beq block below, which must stay last for the dedupe-guard reason
    // documented there.
    CoreSpecStage {
        apply: Specification::add_eval_ir,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Crystal A2 and A4's prerequisites. `add_eval_ir_steps` and
    // `add_eval_ir_activation` are ALSO in EVAL_IR_STAGE_APPLY (they need only
    // Nat/Bool/Eq); the other two are Full-only.
    //
    // They cannot go in EVAL_IR_STAGE_APPLY: that bundle is deliberately scoped
    // to Nat/Bool/Eq, and these stages need `Level` (from add_expr_model) and
    // `level_is_zero` (from add_env_extensions). Hence a Full-bundle stage,
    // positioned immediately after add_eval_ir so the IR* names it depends on
    // are live.
    //
    // Registering them HERE is what puts them under the gates. They were
    // previously reachable only from `new_eval_ir_prelude_spec`, so a single
    // unit test elaborated and kernel-checked them, but `Specification::new()`
    // did not contain them — which meant the axiom_ratchet census never counted
    // them and, worse, the VACUITY FIREWALL never audited A2's two new inductive
    // relations. The standing rule is that the firewall runs on every generated
    // relation; a relation that is well-typed but empty passes every axiom gate
    // silently, which is precisely the failure this programme keeps hitting.
    CoreSpecStage {
        apply: Specification::add_eval_ir_repr,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_eval_ir_fuel,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_eval_ir_steps,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Option B's exact step counts for the designated target. AFTER
    // add_eval_ir_steps and for the same reason as in EVAL_IR_STAGE_APPLY:
    // `ir_steps` is registered there, and `add_eval_ir_lzb_module` (which
    // registers the module these cost) runs inside add_eval_ir, well before it.
    // Placed with the module, the missing head surfaces as a BOGUS ARITY ERROR
    // rather than an unknown identifier -- the trap this file warns about above.
    CoreSpecStage {
        apply: Specification::add_eval_ir_lzb_steps,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_eval_ir_cost,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_eval_ir_activation,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Option B's activation lemmas and the three recursive segment lemmas.
    // AFTER add_eval_ir_activation, for the names given above.
    CoreSpecStage {
        apply: Specification::add_eval_ir_lzb_activation,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // kexpr_beq CORE + its soundness, wired LIVE (step 2a of
    // docs/plans/DEFEQ_COMPLETENESS_PROGRAM_2026-07-25.md). Both modules were
    // proven but reachable only from #[cfg(test)] builders, so the LIVE spec had
    // no Bool-valued comparison on KExpr at all, and `kexpr_beq_eq` — the leaf
    // lemma a conversion-algorithm soundness proof needs — was absent too.
    //
    // NOT in the ImplementationSoundness bundle — this FIXES a pre-existing
    // break. `add_defeq_fuel` registers `opt_rec_bool_true_inv`, whose proof term
    // applies `bool_false_ne_true_t`, and the ONLY registrar of that lemma is
    // `add_env_closed_checkers_depth` (this file, ~:897), which is
    // `in_impl_soundness: false` because IT depends in turn on
    // `add_dependent_sn_richmodel`'s `lt_to_le_succ` — also excluded. So the
    // subset spec failed to elaborate with `Unknown identifier:
    // bool_false_ne_true_t`, breaking all 6 tests in
    // implementation_soundness_{admissibility,check_decomposition}_tests.rs.
    //
    // Fixed from the CONSUMER side rather than by dragging the Girard SN lane into
    // the subset: no implementation-soundness test references `kexpr_beq`,
    // `defeq_fuel`, `def_eq_fuel_sound`, `opt_rec_bool_true_inv` or
    // `level_is_zero` (grep over the two files that call
    // build_implementation_soundness_spec_with_stack), so these three terminal
    // defeq-completeness stages were never needed there. Flipping them keeps the
    // subset MINIMAL, which is its whole purpose, and avoids widening it by the
    // whole SN dependency closure. The Full bundle is unaffected —
    // `run_bundle`'s `Full => true` arm ignores these flags.
    //
    // THESE MUST RUN LAST, structurally rather than incidentally. Five of their
    // names are also registered by modules already live here; all five were
    // compared pairwise and are genuine duplicates, so they are skipped via the
    // *_if_absent guards. That guard keeps the FIRST registration, so the guarded
    // module must run SECOND — and the other registrants are spread across the
    // list (add_env_extensions for level_eqb / level_is_zero,
    // add_iota_closedness_bundle for kexpr_bvar_inj, add_snschema for
    // nat_eqb_refl / name_eqb_refl). Any position earlier than the LAST of them
    // loses the race and the kernel rejects the other module's add_decl.
    CoreSpecStage {
        apply: Specification::add_kexpr_beq_core,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_kexpr_beq_sound,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Step 2b/3: the conversion ALGORITHM and its soundness. Must follow
    // add_kexpr_beq_sound directly — it consumes kexpr_beq and kexpr_beq_eq,
    // which only became live in the stage above.
    CoreSpecStage {
        apply: Specification::add_defeq_fuel,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // ── C1 / the crystal: the layer-1 ImplInfer lane ────────────────────
    // designs/2026-07-29-unified-implinfer-relation.md, migration steps M2/M3/M5.
    // A NEW LATE STAGE, deliberately terminal: the lane is PURELY ADDITIVE
    // (it introduces `ImplExpr` and never touches `KExpr`), so nothing earlier
    // can depend on it, and running it last keeps every existing stage's
    // registration order — and every existing `KExpr.rec` proof term —
    // byte-identical. It consumes `nat_eqb` / `name_eqb` / `nat_is_zero`
    // (add_rec_env), `Bool` + `Empty` (foundation), and
    // `le_trans` (add_iota_core) and `Le` (foundation) — all live well before here.
    //
    // NOT in the Substitution or ImplementationSoundness bundles. Those are
    // MINIMAL subset builders for focused tests, and no spec declaration outside
    // this lane references any of its names — the only consumers are this stage
    // table and the lane's own test module. (The `run_impl_infer` hits in
    // `validate/mod.rs` are an unrelated pre-existing Rust method, not these
    // declarations.) Including the lane would add ~154 kernel declarations of
    // build cost to tests that cannot observe any of them — counted, not
    // estimated: 14 inductive types + their 14 recursors + 71 constructors + 40
    // `add_recursive_def` + 15 `add_definition`-family.
    //
    // Measured aside, recorded because it is easy to misattribute to this lane:
    // the ImplementationSoundness bundle is ALREADY BROKEN at HEAD, independently
    // of this stage group. `add_defeq_fuel` (in_impl_soundness: true) registers
    // `opt_rec_bool_true_inv`, whose proof term needs `bool_false_ne_true_t`,
    // which only `add_env_closed_checkers_depth` registers — and that stage is
    // `in_impl_soundness: false`. So the subset spec fails to elaborate with
    // `Unknown identifier: bool_false_ne_true_t`. Verified by running
    // `cargo test --release -p clean-verify --lib implementation_soundness_admissibility`
    // at this lane's parent commit (3 failed, 98.41s, same error) and again with
    // the lane present (3 failed, 100.43s, same error) — identical either way.
    // Fixing it means giving that bundle `add_env_closed_checkers_depth`, which is
    // a separate change with its own dependency closure to check; it is NOT done
    // here so this commit stays scoped to C1.
    CoreSpecStage {
        apply: Specification::add_impl_infer_syntax,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // M3: the relation + the bvar refutation. Needs the M2 syntax above.
    CoreSpecStage {
        apply: Specification::add_impl_infer,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // C1's acceptance gate: a non-vacuity witness per rule, including the
    // identity lambda `KernelInferAccepts` provably cannot represent.
    CoreSpecStage {
        apply: Specification::add_impl_infer_witnesses,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // M5: the mode-gate side lemma + the 24-arm coverage ledger.
    CoreSpecStage {
        apply: Specification::add_impl_infer_mode_gate,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // ── C4 / the crystal: the CtxRep bridge ─────────────────────────────
    // designs/2026-07-29-crystal-deployed-kernel-bridge.md §1.1. Registered
    // AFTER the ImplInfer stages because it consumes their syntax (ImplExpr,
    // LCtx, LocalDecl, lctx_lookup, ImplConstInfo, impl_inst_levels) and joins
    // it to layer 2 (KExpr, ctx_lookup, lift_at, lift_at_compose,
    // KernelInfers — all live since add_dependent_sn_richmodel / the expr_model
    // lift stages) plus option_some_inj (add_rec_env) and
    // option_none_ne_some_type (add_par_reduces_c). Terminal for the same
    // reason the C1 stages are: purely additive, so nothing earlier can depend
    // on it and no existing registration order moves.
    //
    // Same bundle policy as C1: NOT in Substitution or ImplementationSoundness,
    // because no declaration outside this lane references any of its names and
    // those bundles are minimal subset builders.
    CoreSpecStage {
        apply: Specification::add_ctx_rep,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // ── M4 / the crystal: impl_infer_sound ──────────────────────────────
    // designs/2026-07-29-unified-implinfer-relation.md step M4. Runs AFTER
    // add_ctx_rep because it consumes C4's representation apparatus verbatim
    // (`to_kexpr_at`, `rho_index`) rather than re-deriving it, and joins it to
    // the layer-2 lift calculus (`lift_at`, add_expr_model) and the Nat
    // arithmetic tower (`nat_add_assoc` / `nat_add_comm` / `nat_succ_add`,
    // add_foundation_arith_lemmas; `nat_sub_self_add_zero`, add_snschema).
    // Terminal and Full-only for the same reasons as C1/C4: purely additive.
    CoreSpecStage {
        apply: Specification::add_impl_infer_sound,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Crystal A4 and A5. LAST, and the position is load-bearing: A5 composes
    // with `level_is_zero_sound` and `level_eval`, which the kexpr_beq_sound
    // stage registers well after `add_eval_ir`. Placed with the other EvalIR
    // stages it elaborated fine in the scratchpad -- which builds the whole
    // spec and only THEN adds candidates, so it cannot see a stage-ordering
    // fault at all -- and then failed the real build with an unknown
    // identifier surfacing as a bogus arity error.
    CoreSpecStage {
        apply: Specification::add_eval_ir_correct,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The designated target's MINTED module is registered inside add_eval_ir
    // (EvalIr bundle, `eval_ir_level_minted.rs`); THIS stage is the theorem
    // that A4 is FALSE over it, which needs `level_is_zero`, `ir_lzm_cost`,
    // `EncodesLiveLevelRef` and `ir_outcome_is_ret` -- hence AFTER
    // add_eval_ir_correct, and Full-only for the same reason the cost stage is.
    CoreSpecStage {
        apply: Specification::add_eval_ir_level_minted_refutation,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // Option B: A4 and A5 for the designated target over the emitted body plus
    // a labelled deref model. Deliberately AFTER the refutation, so the three
    // stages read in the order the argument runs: the hand model's A4/A5, the
    // kernel-checked fact that the same sentence is FALSE over the minted
    // module, and then the sentence that IS true once the one callee the
    // artifact cannot carry a body for is supplied as a stated assumption.
    CoreSpecStage {
        apply: Specification::add_eval_ir_lzb_correct,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The width-one chain retargeted to CleanMode::has_cubical_layer, a SHIPPED
    // kernel function already in the class the compiler flips.
    //
    // AFTER add_eval_ir_correct, and the order is load-bearing: its A5-analogue
    // consumes `ir_outcome_bool`, which that stage registers.
    //
    // That justification was briefly FALSE and nothing noticed. `9c37f0ef0`
    // deleted the A5-analogue during a re-authoring, leaving this comment
    // explaining the ordering by a dependency that no longer existed, for two
    // days. Restored 2026-08-12 as `ir_h2_machine_sound` (+ witness, +
    // `ir_h2_never_faults`), and `eval_ir_mode.rs`'s
    // `test_a5_is_present_and_composes` now fails if it goes missing again.
    //
    // Placed earlier it
    // elaborates fine in the scratchpad -- which builds the whole spec and only
    // THEN appends candidates, so it is structurally blind to stage ordering --
    // and then fails the real build with an unknown identifier surfacing as a
    // bogus arity error. Same trap that cost a cycle on A5.
    CoreSpecStage {
        apply: Specification::add_eval_ir_mode,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The SECOND complete width-one chain: `level::Level::kind_ord`, chosen by
    // whole-crate measurement rather than by taste (see the module doc's
    // candidate table). Structurally the most different fully-chainable body in
    // clean-kernel: 7 blocks, a four-case switch plus a reachable default, five
    // distinct integer answers through a u8 join-block parameter, over the
    // payload-bearing recursive `Level` rather than a fieldless enum.
    //
    // AFTER add_eval_ir_correct AND add_eval_ir_mode, and the order is
    // load-bearing in three separate ways, every one of them a name this stage
    // would otherwise not find:
    //   * `ir_outcome_is_ret` (add_eval_ir_correct) — `ir_ko_never_faults`;
    //   * `level_is_zero_sound` / `level_eval` (add_kexpr_beq_sound) — the A5
    //     that reaches a denotational conclusion;
    //   * `EncodesLevelArc` (add_eval_ir_repr) — the bridge lemma.
    // The scratchpad CANNOT see any of that: it builds the whole spec and only
    // then appends candidates, so a stage-ordering fault is invisible there and
    // surfaces in the real build as an unknown identifier or a bogus arity
    // error. Same trap that cost a cycle on A5 and on add_premise_witnesses.
    CoreSpecStage {
        apply: Specification::add_eval_ir_kind_ord,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The THIRD complete width-one chain: `mode::CleanMode::from_source_system`
    // — rank 2 in the 2026-08-12 candidate measurement, and recorded there as
    // NOT chainable because every arm emits `const enum.13 { k }`, a
    // `trust_ir::Constant::Aggregate`, and `IRConst` had no aggregate form. The
    // build item that closes it (the `IRConst` inline element spine plus
    // `ir_const_agg_eval`) landed in `eval_ir_syntax.rs` / `eval_ir_ops.rs`,
    // per the standing rule that a lowering gap is a build item and never a
    // reason to retarget the proof.
    //
    // AFTER add_eval_ir_correct AND add_eval_ir_mode AND add_eval_ir_kind_ord,
    // and the order is load-bearing in three ways, each a name this stage would
    // otherwise not find:
    //   * `ir_outcome_is_ret` (add_eval_ir_correct) — `ir_fs_never_faults`;
    //   * `CleanModeR` / `clean_mode_tag` / `clean_mode_has_cubical`
    //     (add_eval_ir_mode) — the RESULT type of this body is CleanMode, so
    //     this chain's theorem is stated in the first chain's vocabulary and
    //     its A5 composes with the first chain's reflected predicate;
    //   * `ir_scalar_nat` (add_eval_ir_kind_ord) — `ir_spine_head_nat`.
    // The scratchpad CANNOT see any of that: it builds the whole spec and only
    // then appends candidates, so a stage-ordering fault is invisible there and
    // surfaces in the real build as an unknown identifier or a bogus arity
    // error. Same trap that cost a cycle on A5 and on add_premise_witnesses.
    CoreSpecStage {
        apply: Specification::add_eval_ir_from_source,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The FOURTH and FIFTH chains: `flat::types::FlatFlags::contains` and
    // `expr::bvar_in_range` — the first two chained bodies that COMPUTE their
    // answer (a `binop`+`icmp`, and four `icmp`s through two `condbr`s) rather
    // than select a materialised constant, and the first two whose
    // `markers_exact: true` compares a NON-EMPTY marker sequence (8 and 21
    // lines, against `0 marker line(s)` on all three chains above).
    //
    // AFTER add_eval_ir_correct, and that is load-bearing for both: their A4
    // theorems are stated over `ir_eval` with a `Le` fuel premise and go through
    // `ir_run_le_ret`, and their corollaries need `ir_outcome_bool` /
    // `ir_outcome_is_ret`. In the dependency-scoped EvalIr bundle those names do
    // not exist, which is exactly why the 2026-08-13 probe could reach only 45
    // of the 63 declarations there and why this is the position, not the order
    // the modules happen to be written in.
    //
    // Registered 2026-08-13 (lane 3) after the ONE blocker was settled by
    // measurement rather than assumed. `ir_br_exact` had run 3.5 minutes without
    // returning, and the cause was NOT the `condbr`, the nine-step run, or the
    // size of the stuck term: it was a single `Nat` comparison. The reflected
    // predicate named the sentinel (`ir_wrap ir_d32 ir_br_umax` for
    // `ir_br_umax := 4294967295`) where the machine materialises the literal,
    // and against two syntactically different arguments the kernel reduces both
    // `ir_wrap` applications — a width-w residue is ~2^w `Nat.rec` unfoldings
    // (measured on that shape: 0.021 / 0.431 / 6.586 s at w = 8 / 12 / 16, so
    // w = 32 is about five days). `ir_br_c1` and `ir_br_m1` now carry the
    // literal the emitted `IRInst.const_` carries, which is also the more
    // faithful transcription, and the chain checks in milliseconds.
    //
    // `ir_br_exact` additionally goes through `ir_run_steps_split` (a general
    // lemma of the semantics) plus `ir_br_two_steps`, which stops before the
    // branch. That is not what unblocked it — the one-liner also checks, in
    // 0.010 s — it is what makes the bound structural instead of empirical. The
    // statement of `ir_br_exact` is unchanged.
    CoreSpecStage {
        apply: Specification::add_eval_ir_contains,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The WITH chain (flat::types::FlatFlags::with) — or / const-struct /
    // insertfield. AFTER add_eval_ir_contains, and the order is load-bearing
    // rather than alphabetical: this stage REUSES `FlatFlagsR` /
    // `flat_flags_bits` / `flat_flags_contains` / `EncodesFlatFlags` / `ir_vl2`
    // / `ir_fc_tflags` / `ir_fc_val` / `ir_fc_module` / `ir_fc_correct`
    // (add_eval_ir_contains), `ir_run_le_ret` (add_eval_ir_fuel),
    // `ir_outcome_is_ret` (add_eval_ir_correct) and `ir_outcome_disc`
    // (add_eval_ir_from_source). Re-declaring any of them is the eighth
    // chain's one recorded error; none is re-declared.
    CoreSpecStage {
        apply: Specification::add_eval_ir_flat_flags_with,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // place in STAGES after the add_eval_ir_priority stage (bundles.rs ~line 1924) — any point after add_eval_ir_contains satisfies the dependencies
    CoreSpecStage {
        apply: Specification::add_eval_ir_bvar_range,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // W2a — the synthetic micro-module lane (select / undef / unreachable /
    // extractelement / unop; plan §5 W2a). Reuses ONLY `add_eval_ir` names —
    // the IR syntax families, the ir_d numerals, the ir_nd/ir_bd/ir_blk/ir_nl/
    // ir_vl1 builders, ir_mem0, and the machine (`ir_eval`, IROutcome,
    // IRFault) — deliberately nothing from any chain stage, so the semdiff
    // battery can register the same module lines standalone into the minimal
    // EvalIr-bundle spec (`ir_w2a_*_module_defs` re-exports). Any point after
    // add_eval_ir therefore satisfies the dependencies; placed here with the
    // other post-chain EvalIR stages.
    CoreSpecStage {
        apply: Specification::add_eval_ir_w2a_synth,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // W2b — the synthetic lane's MEMORY tranche (alloca / ptrdata /
    // ptrmetadata / ptrfromparts; plan §5 W2b). Same dependency posture as
    // W2a: reuses ONLY `add_eval_ir` names (syntax families, ir_d numerals,
    // builders, ir_mem0, the memory lane's evaluators and the machine), so
    // the semdiff battery can register the `ir_w2b_*_module_defs` lines
    // standalone into the minimal EvalIr-bundle spec. Any point after
    // add_eval_ir satisfies the dependencies; placed beside W2a.
    CoreSpecStage {
        apply: Specification::add_eval_ir_w2b_synth,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // W2c — the synthetic lane's CALL+MODULE tranche (callindirect /
    // globaladdr; plan §5 W2c — the FINAL synthetic tranche: after it only
    // `overflow` (W3) and `fcmp` (W4) lack battery rows). Same dependency
    // posture as W2a/W2b: reuses ONLY `add_eval_ir` names (syntax families
    // incl. IRGlobal/IRConst, ir_d numerals, builders, ir_mem0,
    // ir_globaladdr_eval and the machine), so the semdiff battery can register
    // the `ir_w2c_*_module_defs` lines standalone into the minimal
    // EvalIr-bundle spec. Any point after add_eval_ir satisfies the
    // dependencies; placed beside W2a/W2b.
    CoreSpecStage {
        apply: Specification::add_eval_ir_w2c_synth,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // W3 — the OVERFLOW value domain's synthetic lane (plan §5 W3,
    // 2026-08-25). Unlike W2a-c this wave changed the semantics itself: the
    // overflow dispatch arm computes (ir_overflow_exec, two-result bind
    // through ir_bind2) where it was the tagged unmodelled outcome, so only
    // `fcmp` (W4) remained tagged — until the W4 stage below retired it the
    // same day. Same dependency posture as the W2 tranches:
    // reuses ONLY `add_eval_ir` names (syntax families incl. IROverflowOp,
    // ir_d numerals, builders, ir_mem0, ir_overflow_exec and the machine), so
    // the semdiff battery can register the `ir_w3_*_module_defs` lines
    // standalone into the minimal EvalIr-bundle spec. Any point after
    // add_eval_ir satisfies the dependencies; placed beside the W2 stages.
    CoreSpecStage {
        apply: Specification::add_eval_ir_w3_synth,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // W4 — the FLOAT-COMPARISON lane (plan §5 W4, 2026-08-25) — the LAST
    // lane: with it every one of the 28 IRInst constructors has battery rows.
    // Like W3 this wave changed the semantics itself: the fcmp dispatch arm
    // computes (ir_fcmp_eval, 12 real predicates over the classified binary64
    // substrate — eval_ir_fcmp.rs, registered inside add_eval_ir_ops), so
    // ZERO ir_exec arms remain tagged unmodelled. Same dependency posture as
    // the W2/W3 tranches: reuses ONLY `add_eval_ir` names (syntax families
    // incl. IRFCmpOp, ir_d numerals, builders, ir_mem0, ir_fcmp_eval and the
    // machine), so the semdiff battery can register the `ir_w4_fc_module_defs`
    // lines standalone into the minimal EvalIr-bundle spec. Any point after
    // add_eval_ir satisfies the dependencies; placed beside the other
    // synthetic stages.
    CoreSpecStage {
        apply: Specification::add_eval_ir_w4_synth,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The FLOAT-RESIDUE synthetic lane (evalir_w4.PENDING.md delta 5's wave,
    // 2026-08-25): three micro-modules putting the seven newly-answering
    // residue operators (fneg/fabs, ffloor/fceil/ftrunc, fmin/fmax) under
    // battery measurement. Like W3/W4 the wave changed the semantics itself —
    // ir_unop_eval/ir_binop_eval's residue arms now dispatch into
    // eval_ir_float_res's tables (registered inside add_eval_ir_ops), with
    // frem/fsqrt/the fp casts/fdiv-finite staying as DATED refusals carried
    // by universal kernel witnesses. Same dependency posture as the other
    // synthetic stages: reuses ONLY `add_eval_ir` names, so the semdiff
    // battery can register the `ir_fr*_module_defs` lines standalone into the
    // minimal EvalIr-bundle spec. Any point after add_eval_ir satisfies the
    // dependencies; placed beside the other synthetic stages.
    CoreSpecStage {
        apply: Specification::add_eval_ir_wfr_synth,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The SIXTH and SEVENTH chains: `env::native_reducers_char::is_valid_char`
    // and `<tc::expr_location::ExprPathStep as Clone>::clone` — the two bodies
    // the 2026-08-13 census named as the remaining candidates, re-derived from a
    // fresh whole-crate dump before either was written.
    //
    // `is_valid_char` is the SECOND and LAST condbr-carrying chainable body in
    // the crate, and it is at width **64**. That is only affordable because the
    // residue cost law on record was wrong: `ir_wrap w n` costs O(n) in the
    // DIVIDEND and is independent of the WIDTH (re-measured here: 1.322 s at
    // w = 64 / n = 7000 against 1.356 s at w = 8 / n = 7000; and 1.322 →
    // 2.644 → 5.399 s as n doubles). The 2026-08-13 "×15.3 per four bits, so
    // 2^W" reading varied width and dividend together — its dividend was
    // `2^W - 1` at each point — and would have refused this body on sight.
    //
    // `ExprPathStep::clone` needed NO build item: the `IRConst` aggregate spine
    // the THIRD chain landed is exactly the construct it emits, which is why
    // the 2026-08-12 candidate measurement recorded both bodies as refused for
    // the same reason and the same shape (`const enum.13 { k }` /
    // `const enum.181 { k }`).
    //
    // AFTER add_eval_ir_from_source, and that is load-bearing rather than
    // alphabetical: `ir_ep_machine_sound` reads the tag out of the returned
    // AGGREGATE with `ir_outcome_disc`, which that stage registers, and both
    // chains' A4 go through `ir_run_le_ret` / `ir_outcome_is_ret` from
    // add_eval_ir_fuel and add_eval_ir_correct.
    CoreSpecStage {
        apply: Specification::add_eval_ir_valid_char,
        in_substitution: false,
        in_impl_soundness: false,
    },
    CoreSpecStage {
        apply: Specification::add_eval_ir_path_step,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The EIGHTH chain, 2026-08-15:
    // `env::native_reducers_float::reduce_float_div::{closure#0}` — the first
    // over FLOAT ARITHMETIC, and the ground the 2026-08-15 lane-8 census
    // recorded as covered by no chain (`unclaimed_ground_recorded_not_chained`
    // in `data/crystal_flip_census_lane8_2026-08-15.json`: a cast, and float
    // arithmetic).
    //
    // It needed a BUILD ITEM and it is the whole reason to do it: until this
    // lane every float-domain operation in the semantics was the single verdict
    // `ir_float_fault`, so link 3 did not hold for any float body. The binary64
    // value domain (`add_eval_ir_float`, registered inside `add_eval_ir_ops`
    // because `ir_binop_eval` dispatches into it) is that item.
    //
    // AFTER add_eval_ir_path_step, and load-bearing rather than alphabetical:
    // this stage needs `ir_vl2` (add_eval_ir_contains), `ir_outcome_is_ret`
    // (add_eval_ir_correct), `ir_run_steps_split` (add_eval_ir_steps) and
    // `ir_outcome_fuelout_ne_ret_prop` (add_eval_ir_fuel) — the last of which it
    // extends, because its A4 conclusion is not an `IROutcome.ret` and the
    // ret-only fuel monotonicity therefore does not apply to it.
    CoreSpecStage {
        apply: Specification::add_eval_ir_float_div,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The float ADD chain, 2026-08-20: `env::native_reducers_float::
    // reduce_float_add::{closure#0}` — the `fadd` row of the 2026-08-19 width
    // tranche (`data/crystal_width_tranche_2026-08-19.json`). AFTER
    // add_eval_ir_float_div and load-bearing rather than alphabetical: it reuses
    // that chain's EncodesF64Val / ir_outcome_fuelout_ne_unmodelled_prop /
    // ir_option_is_some / ir_outcome_is_trap. What it adds: the fin/fin cell ANSWERS (ir_f64_add_fin), so this chain returns computed values on exactly the inputs the eighth registers as refused.
    CoreSpecStage {
        apply: Specification::add_eval_ir_float_add,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The float SUB chain, 2026-08-20: `env::native_reducers_float::
    // reduce_float_sub::{closure#0}` — the `fsub` row of the 2026-08-19 width
    // tranche (`data/crystal_width_tranche_2026-08-19.json`). AFTER
    // add_eval_ir_float_div and load-bearing rather than alphabetical: it reuses
    // that chain's EncodesF64Val / ir_outcome_fuelout_ne_unmodelled_prop /
    // ir_option_is_some / ir_outcome_is_trap. What it adds: non-commutative on the value axis; its symbolic-A5 corollaries are split into abstract-o lemmas + concrete instantiations (see the module doc for the measured defeq wall).
    CoreSpecStage {
        apply: Specification::add_eval_ir_float_sub,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The strict_monads chain, 2026-08-20: `env::Environment::
    // set_lean4_core_strict_monads` — the first chained body that MUTATES
    // memory: the first `store`, the first `insertfield` a lane could compare
    // (the insertfields/stores write lanes landed ahead of it), and the first
    // VOID return. A4 splits into an outcome half (void, at ir_eval) and a
    // heap half (the 3-step configuration's memory IS ir_mem_update at the
    // receiver with field 81 rewritten), because the machine's ret discards
    // the heap; A5 holds FULLY SYMBOLICALLY at both — the float trio's defeq
    // wall does not apply, since ir_vals_set on a symbolic spine is inert
    // (measured in the EvalIR scratchpad, 61/61 PASS, ~5.5 s declaration
    // time). The producer's interpreter differential is NOT-RUN on this body
    // (0 samples) and nothing in the stage claims it.
    //
    // AFTER add_eval_ir_priority, and load-bearing rather than alphabetical:
    // this stage REUSES `ir_vl2` (add_eval_ir_contains), `ir_run_le_ret`
    // (add_eval_ir_fuel), `ir_outcome_is_ret` (add_eval_ir_correct),
    // `ir_cfg_mach` (add_eval_ir_bvar_range) and `ir_cell` / `ir_sp0` /
    // `ir_mem0` (add_eval_ir). Re-declaring any of them is the eighth
    // chain's one real error. Must stay BEFORE add_premise_witnesses, which
    // is genuinely last.
    CoreSpecStage {
        apply: Specification::add_eval_ir_strict_monads,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // ^ insert into STAGES in crates/clean-verify/src/spec/core_spec/bundles.rs, after the add_eval_ir_priority stage (currently ends line ~1928) and before the `── premise-satisfiability witnesses ──` block
    // The float MUL chain, 2026-08-20: `env::native_reducers_float::
    // reduce_float_mul::{closure#0}` — the `fmul` row of the 2026-08-19 width
    // tranche (`data/crystal_width_tranche_2026-08-19.json`). AFTER
    // add_eval_ir_float_div and load-bearing rather than alphabetical: it reuses
    // that chain's EncodesF64Val / ir_outcome_fuelout_ne_unmodelled_prop /
    // ir_option_is_some / ir_outcome_is_trap. What it adds: the sign-XOR lane, contrasted in-file with addition's sign-AND.
    CoreSpecStage {
        apply: Specification::add_eval_ir_float_mul,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The NINTH chain, 2026-08-16:
    // `env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}` — the
    // first over a CAST, and the other half of the ground the 2026-08-15 lane-8
    // census recorded as unclaimed (`unclaimed_ground_recorded_not_chained.cast`
    // in `data/crystal_flip_census_lane8_2026-08-15.json`).
    //
    // It needed NO build item on the semantics side, and that is a measurement
    // rather than a hope: `IRInst.cast` has been a constructor since the syntax
    // was written, `IRCastOp` carries 17/17 of `trust_ir::CastOp`,
    // `ir_cast_eval` dispatches all seventeen arms with exact `ir_trunc_eval` /
    // `ir_zext_eval` / `ir_sext_eval` evaluators, and `ir_step` has always had a
    // case for the instruction. The build item was in the GATE — a cast was in
    // no CFG lane at all, so a body whose whole content is `trunc` + `ret`
    // parsed to an EMPTY `Cfg` on both sides, and two empty CFGs compare equal.
    //
    // AFTER add_eval_ir_valid_char and add_eval_ir_bvar_range, and load-bearing
    // rather than alphabetical: this stage REUSES `EncodesU64Val` and
    // `ir_vc_tu64` (sixth chain), `ir_br_tu32` (fifth), `ir_outcome_nat`
    // (second), `ir_run_le_ret` (add_eval_ir_fuel) and `ir_outcome_is_ret`
    // (add_eval_ir_correct). Re-declaring any of them is the eighth chain's one
    // real error, which elaborated cleanly in every fast gate and failed only in
    // the full `Specification::new()`.
    CoreSpecStage {
        apply: Specification::add_eval_ir_trunc,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The zext chain, 2026-08-20: `cert::builder::state::NodeId::index` — the
    // opcode lane the ninth chain measured and deferred, owing "only the
    // transcription and a decision about `usize`". The decision: ir_ni_tusize
    // := IRTy.uint_ ir_d64, a TARGET assumption anchored to the recorded
    // aarch64-apple-darwin producer, applied once in the gate
    // (tests/crystal_a1_lineage/node_id_index.rs), which asserts the raw
    // `?usize` token FIRST. Interpreter differential NOT-RUN (0 samples): the
    // evidence is agreed + markers_exact + flip-lineage equality only.
    //
    // AFTER add_eval_ir_priority, and load-bearing rather than alphabetical:
    // this stage REUSES ir_d32/ir_br_tu32 (fifth chain), ir_d64 (sixth),
    // ir_tU8 (crystal), ir_outcome_nat (second), ir_outcome_is_ret
    // (add_eval_ir_correct), ir_run_le_ret (add_eval_ir_fuel) and
    // ir_cast_eval/ir_sext_value (add_eval_ir_ops). Its premise witness
    // (encodes_node_id_inhabited) is registered IN the stage, beside the
    // relation, so the premise-witness ratchet needs no baseline change.
    CoreSpecStage {
        apply: Specification::add_eval_ir_node_id_index,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // placement: crates/clean-verify/src/spec/core_spec/bundles.rs, in STAGES after the
    // add_eval_ir_priority stage and BEFORE add_premise_witnesses (which must stay last).
    // MUST land in the same commit as the mod.rs line: either alone leaves dead_code
    // warnings that fail the -D warnings gates.
    // The TENTH chain, 2026-08-16:
    // `tc::local_context::LocalContext::push_low_local::META_TAG` — the first
    // over a PANIC ARM and the first over a CTFE FLIP. Both were unclaimed for
    // the same reason: `docs/analysis/frontier-2026-08-16.md` §2 records that
    // "panic arms 0" is a statement about CODEGEN flips only — 21 of the crate's
    // 32 CTFE flips carry an `Inst::Assert` and 0 of its 178 codegen flips do,
    // and all nine earlier chains are over codegen flips.
    //
    // The ASSERT needed NO build item: `IRInst.assert` has been a constructor
    // since the syntax was written and `ir_assert_exec` -> `ir_assert_b` was
    // already exact, with `ub assert_failed` on false and `type_error not_bool`
    // on a non-Bool. The semantics build item was `IRCastOp.bitcast`, which was
    // a blanket `ir_width_fault`: `ir_bitcast_eval` (registered inside
    // `add_eval_ir_ops`, because `ir_cast_eval` dispatches into it) decides
    // exactly the same-width integer-to-integer fragment the original refusal's
    // stated reason does not cover, and leaves width mismatches, floats,
    // pointers and `transmute` refused. The gate build item was the assert lane
    // plus two holes it exposed — see `tests/crystal_a1_lineage/emitted_cfg.rs`.
    //
    // AFTER add_eval_ir_trunc, and load-bearing rather than alphabetical: this
    // stage REUSES `ir_vc_tu64` (sixth chain), `ir_br_tu32` (fifth),
    // `ir_outcome_nat` (second), `ir_outcome_is_ret` (add_eval_ir_correct),
    // `ir_run_le_ret` (add_eval_ir_fuel) and `ir_run_steps_split` /
    // `ir_run_halted` (add_eval_ir_steps).
    CoreSpecStage {
        apply: Specification::add_eval_ir_meta_tag,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The ELEVENTH chain, 2026-08-20: `env::types::SimpPriority::value` — the
    // FIRST chained body that COMPUTES AN ADDRESS AND DEREFERENCES IT. Its
    // Custom arm materialises a byte offset, `gep`s the receiver by it, and
    // loads through the RESULT; every earlier chain reads memory at most
    // through the pointer it was handed, and six of the eleven read no memory
    // at all.
    //
    // It exists because the frontier table was STALE. `gep` and `call` were
    // recorded at zero deployed-profile flips on 2026-08-16 and quoted for four
    // days; re-measured at HEAD after waves GS/CP/DR/W3/W3b, `gep` flips 4 times
    // at -O3 and `call` twice (data/crystal_frontier_census_2026-08-20.json,
    // re-derivable by scripts/crystal_frontier_census.py). Two of the four gep
    // flips are Level::is_zero and is_nonzero, whose closure is not bodyful; of
    // the other two, `Reducibility::height` is rejected because the switch-map
    // perturbation records applications=0 on it — a fail-closed control that
    // cannot reach the body it controls is not a control.
    //
    // AFTER add_eval_ir_meta_tag, and load-bearing rather than alphabetical:
    // this stage REUSES `ir_d32` (add_eval_ir_bvar_range), `ir_d64`
    // (add_eval_ir_valid_char), `ir_cfg_mach` (add_eval_ir_bvar_range),
    // `ir_outcome_nat` (add_eval_ir_kind_ord), `ir_outcome_is_ret`
    // (add_eval_ir_correct), `ir_run_le_ret` (add_eval_ir_fuel) and `ir_steps`
    // (add_eval_ir_steps). Re-declaring any of them is the eighth chain's one
    // real error, which elaborated cleanly in every fast gate and failed only
    // in the full `Specification::new()`. The scratchpad CANNOT see a
    // stage-ordering fault at all: it builds the whole spec and only then
    // appends candidates.
    CoreSpecStage {
        apply: Specification::add_eval_ir_priority,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // The CALL chain, 2026-08-21: `expr::meta::ExprMeta::has_loose_bvars`
    // CALLING `expr::meta::ExprMeta::loose_bvar_range` — the first chain over
    // a body with a `call`, the first two-function module, and the first A4
    // composed across the call boundary (split at the call step, frame-generic
    // callee activation, seam lemma abstracted over the callee's answer).
    // Caller evidence: agreed + markers_exact over 4 real lines + flip with
    // lineage == coverage row, deferred_to_seam=true recorded; callee: shim-
    // refused differential, evidence is the pinned IR + the reflected lemma.
    //
    // AFTER add_eval_ir_priority, and load-bearing rather than alphabetical:
    // this stage REUSES ir_br_tu32/ir_d32 (fifth chain), ir_vc_tu64/ir_d64
    // (sixth), ir_mt_bd9 and ir_ret_int_inj (tenth), ir_bd3 (crystal),
    // ir_run_le_ret (add_eval_ir_fuel), ir_run_steps_split / ir_run_of_steps /
    // ir_config_outcome (add_eval_ir_steps), ir_outcome_bool /
    // ir_outcome_is_ret (add_eval_ir_correct) and ir_outcome_nat
    // (add_eval_ir_kind_ord). Re-declaring any of them is the eighth chain's
    // recorded error, which only the full Specification::new() catches.
    CoreSpecStage {
        apply: Specification::add_eval_ir_has_loose_bvars,
        in_substitution: false,
        in_impl_soundness: false,
    },
    // ── premise-satisfiability witnesses ────────────────────────────────
    // GENUINELY LAST, and it has to be: these witness predicates from four
    // lanes (EvalIR syntax/state, the eval_ir MODE lane, the ImplInfer mode
    // gate, faithful-whnf), so the stage must run after every one of them.
    // Measured, not assumed — placed after add_impl_infer_sound it failed
    // with "Unknown identifier: CleanModeR", which add_eval_ir_mode registers
    // further down this very list. Purely additive; nothing references these
    // names.
    CoreSpecStage {
        apply: Specification::add_premise_witnesses,
        in_substitution: false,
        in_impl_soundness: false,
    },
];

const INTERVAL_ARITH_STAGE_APPLY: &[CoreSpecStageApply] = &[
    Specification::add_foundation_types,
    Specification::add_interval_arith_spec,
];

/// Foundation types + the EvalIR stage. Nothing else: the EvalIR stage's only
/// prerequisites are `Nat`, `Bool` (both from `add_foundation_types`) and `Eq`.
const EVAL_IR_STAGE_APPLY: &[CoreSpecStageApply] = &[
    Specification::add_foundation_types,
    Specification::add_eval_ir,
    // The machine-level crystal lemmas also belong to this dependency-scoped
    // bundle, because they genuinely need nothing but Nat/Bool/Eq and the IR
    // types: `ir_steps` and its faithfulness equation, and the activation
    // lemma's leaf arms, which take a raw `ir_mem_lookup` equation and never
    // mention `Level` or `EncodesLevelArc`.
    //
    // Being here is what makes them cheap to iterate on. The remaining A4 work
    // is machine-shape reasoning, and this bundle builds in a fraction of the
    // full spec's time. `add_eval_ir_repr` and `add_eval_ir_cost` stay
    // Full-only: they need `Level` and `level_is_zero` respectively.
    Specification::add_eval_ir_steps,
    // MUST follow add_eval_ir_steps: these are the designated target's exact
    // step counts and they are the only lzb declarations naming `ir_steps`.
    Specification::add_eval_ir_lzb_steps,
    Specification::add_eval_ir_activation,
    // MUST follow add_eval_ir_activation: the segment lemmas name
    // `ir_frames_tail` / `ir_config_frames` from that stage, and `ir_steps_add`
    // from add_eval_ir_steps.
    Specification::add_eval_ir_lzb_activation,
];

/// Apply the ordered stages for the requested bundle to the specification.
pub(super) fn run_bundle(
    spec: &mut Specification,
    bundle: CoreSpecBundle,
) -> Result<(), SpecError> {
    for stage in STAGES {
        let include = match bundle {
            CoreSpecBundle::Full => true,
            CoreSpecBundle::Substitution => stage.in_substitution,
            CoreSpecBundle::ImplementationSoundness => stage.in_impl_soundness,
            CoreSpecBundle::IntervalArith => {
                // Include only foundation types (Nat, Eq) + interval arithmetic.
                // Foundation stages register Nat which IvArithOp/IvStructOp/etc.
                // are parameterized over. Part of #3362.
                INTERVAL_ARITH_STAGE_APPLY
                    .iter()
                    .any(|apply| std::ptr::fn_addr_eq(*apply, stage.apply))
            }
            CoreSpecBundle::EvalIr => EVAL_IR_STAGE_APPLY
                .iter()
                .any(|apply| std::ptr::fn_addr_eq(*apply, stage.apply)),
        };
        if include {
            (stage.apply)(spec)?;
        }
    }
    Ok(())
}

/// Build the minimal stage prefix needed to validate Stage-0 Brick 2
/// (`DefEq.iota_gen` / `DefEq.delta_gen`): every stage in dependency order up to
/// and INCLUDING `add_defeq_iota_delta_gen`, then stop.
///
/// The brick sits right after `add_delta_step_bridge` and depends on nothing in
/// the later `par_reduces_*` confluence lane, so this prefix deliberately halts
/// before that machinery. That keeps Brick-2 validation independent of the
/// confluence stages (which carry concurrent in-progress work), while still
/// exercising the real kernel type-check of both proof terms against the actual
/// `RecEnvWellformed` / `DefEnvWellformed` / keystone definitions.
#[cfg(any(test, feature = "test-utils"))]
pub(super) fn build_defeq_iota_delta_gen_prefix(spec: &mut Specification) -> Result<(), SpecError> {
    let last = Specification::add_defeq_iota_delta_gen as CoreSpecStageApply;
    for stage in STAGES {
        (stage.apply)(spec)?;
        if std::ptr::fn_addr_eq(stage.apply, last) {
            return Ok(());
        }
    }
    // Brick-2 stage was not found in the plan — fail loudly rather than silently
    // validating an incomplete prefix.
    Err(SpecError::ParseError(
        "build_defeq_iota_delta_gen_prefix: add_defeq_iota_delta_gen stage missing from STAGES"
            .to_string(),
    ))
}
