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
    CoreSpecStage {
        apply: Specification::add_eval_ir_bvar_range,
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
    Specification::add_eval_ir_activation,
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
