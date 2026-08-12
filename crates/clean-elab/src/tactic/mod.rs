// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic framework
//!
//! Provides a proof state and basic tactics for interactive theorem proving.
//! Tactics operate on goals (holes in a proof term) and produce proof terms.
//!
//! # Architecture
//!
//! The tactic framework uses a goal-based approach:
//! - A `Goal` represents an unproven proposition with local context
//! - A `ProofState` maintains a list of goals and metavariable assignments
//! - `Tactic`s transform proof states, closing goals or creating new ones
//!
//! # Basic Tactics
//!
//! - `exact e` - Provide an exact proof term `e` for the goal
//! - `intro x` - For goal `∀ (x : A), B`, introduce `x` and change goal to `B`
//! - `apply f` - For goal `B`, if `f : A → B`, change goal to `A`

// Re-export kernel types needed by tests and submodules
#[cfg(test)]
pub(crate) use clean_kernel::cert::ProofCert;
#[cfg(test)]
pub(crate) use clean_kernel::name::Name;
#[cfg(test)]
pub(crate) use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

// Submodules (alphabetically ordered). `pub mod` only for verified cross-crate access.
pub(crate) mod abs_cases;
pub(crate) mod ac_rfl;
pub(crate) mod algebra;
pub(crate) mod arith_field_simp;
mod arith_field_simp_proof;
pub(crate) mod arith_linarith;
pub(crate) mod arith_linarith_chain;
pub(crate) mod arith_linarith_close;
pub(crate) mod arith_linarith_farkas_goal;
pub(crate) mod arith_linarith_int_eq;
pub(crate) mod arith_linarith_kernel;
pub(crate) mod arith_linarith_nat_direct;
pub(crate) mod arith_linarith_nat_eq;
pub(crate) mod arith_linarith_proof;
pub(crate) mod arith_linarith_rat_downcast;
pub(crate) mod arith_linarith_real_downcast;
pub(crate) mod arith_linarith_real_downcast_additive;
pub(crate) mod arith_linarith_scale;
pub(crate) mod arith_mathverse_parse;
pub(crate) mod arith_mathverse_proof;
pub(crate) mod arith_mathverse_proof_builders;
pub(crate) mod arith_nlinarith;
pub(crate) mod arith_norm_cast;
pub(crate) mod arith_push_neg;
pub(crate) mod arithmetic;
pub(crate) mod auto_cascade;
pub(crate) mod blast;
pub mod builtins;
pub(crate) mod builtins_compound;
pub(crate) mod builtins_handlers;
pub(crate) mod builtins_phase3d;
pub(crate) mod builtins_phase3d_conv;
pub(crate) mod builtins_phase3d_elab;
pub(crate) mod builtins_phase3d_intro;
pub(crate) mod builtins_phase3d_loc;
pub(crate) mod builtins_phase3d_match;
pub(crate) mod builtins_phase3d_rewrite;
pub(crate) mod builtins_wave3;
pub(crate) mod bvar_ops;
pub(crate) mod calc;
#[cfg(test)]
mod calc_tests;
pub(crate) mod calc_trans;
pub(crate) mod calc_trans_match;
#[cfg(test)]
mod case_binder_rename_cache_tests;
pub(crate) mod cases;
#[cfg(test)]
mod cases_tests;
pub(crate) mod cast;
pub(crate) mod cc;
pub(crate) mod cert_simp;
pub(crate) mod combinator;
pub(crate) mod omega_tactic;
// contradiction: enhanced contradiction/exfalso/absurd with extra patterns (#3082)
mod combinator_solve;
pub(crate) mod combinators;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod combinators_ext;
#[cfg(test)]
mod combinators_ext_tests;
#[cfg(test)]
mod combinators_tests;
pub(crate) mod congr_obtain;
pub(crate) mod connective;
#[cfg(test)]
mod connective_and_intros_tests;
#[cfg(test)]
mod connective_split_ite_tests;
pub(crate) mod contradiction;
#[cfg(test)]
mod contradiction_tests;
pub(crate) mod conv;
pub(crate) mod conv_congr_recombine;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod conv_deep;
#[cfg(test)]
mod conv_deep_tests;
pub(crate) mod conv_ext;
pub(crate) mod conv_proof;
pub(crate) mod convert;
mod core;
pub(crate) mod debug;
pub(crate) mod decide;
pub(crate) mod decide_eq;
pub(crate) mod decide_eq_noconfusion;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod decide_ext;
#[cfg(test)]
mod decide_ext_tests;
#[cfg(test)]
mod decide_tests;
pub(crate) mod discr_tree;
pub(crate) mod display;
#[cfg(test)]
mod display_tests;
pub mod domain_profile;
pub mod drat;
pub(crate) mod elim_info;
#[cfg(test)]
mod elim_info_tests;
pub(crate) mod eq_goal_solver;
pub(crate) mod equality;
pub(crate) mod existential;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod exists_use;
#[cfg(test)]
mod exists_use_tests;
pub(crate) mod extensionality;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod extensionality_config;
pub(crate) mod field;
pub(crate) mod field_denom;
pub(crate) mod field_tactic;
#[cfg(test)]
mod field_tests;
pub(crate) mod finite_cases;
pub(crate) mod finite_cases_proof;
pub(crate) mod forward;
pub(crate) mod gcongr;
#[cfg(test)]
mod gcongr_discharge_tests;
pub(crate) mod generalize;
pub(crate) mod goal;
pub(crate) mod grind;
pub(crate) mod grind_config;
pub(crate) mod groebner_basis;
pub(crate) mod have_let;
pub(crate) mod hypothesis;
pub(crate) mod induction;
pub(crate) mod induction_elim;
#[cfg(test)]
mod induction_elim_tests;
pub(crate) mod inductive_reasoning;
// injection: TacticCtx wrappers + classify_constructor_equality helper (#3082)
pub(crate) mod injection;
pub(crate) mod instance;
pub(crate) mod interval_cases;
pub(crate) mod library_search;
// Unwired roadmap prototype (2026-08-04): compiled only with its unit tests until the live
// pipeline owns it. Mirrors the pattern already used for pattern_match_ext / error_recovery*.
#[cfg(test)]
pub(crate) mod library_search_ext;
#[cfg(test)]
mod library_search_ext_tests;
pub(crate) mod llm_oracle;
pub(crate) mod mathverse_env;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod mathverse_ext;
#[cfg(test)]
mod mathverse_ext_tests;
pub(crate) mod mathverse_use;
#[cfg(test)]
mod mathverse_use_tests;
pub(crate) mod monad_pres;
pub(crate) mod nat_expr_eval;
pub(crate) mod native_decide_eval;
pub(crate) mod nn_verify;
pub(crate) mod norm;
pub(crate) mod norm_num;
pub(crate) mod norm_num_ext;
#[cfg(test)]
mod norm_num_ext_tests;
pub(crate) mod norm_num_kernel;
#[cfg(test)]
mod norm_num_tests;
pub(crate) mod op_projection;
pub(crate) mod options;
pub(crate) mod oracle;
pub(crate) mod pattern;
pub(crate) mod polynomial;
pub(crate) mod polyrith;
pub(crate) mod positivity;
pub(crate) mod project_mathverse;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod proof_cert_verify;
#[cfg(test)]
mod proof_cert_verify_tests;
pub(crate) mod proof_manipulation;
pub(crate) mod proof_term;
pub(crate) mod proof_term_cert;
#[cfg(test)]
mod rcases_alternation_field_tests;
pub(crate) mod registry;
pub(crate) mod ring;
pub(crate) mod ring_helpers;
pub(crate) mod ring_literals;
pub(crate) mod ring_proof;
pub(crate) mod ring_proof_carry;
pub(crate) mod ring_proof_fuse;
pub(crate) mod ring_proof_sort;
pub(crate) mod ring_proof_surface;
pub mod script_runner;
pub(crate) mod search;
pub(crate) mod simp;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod simp_all;
#[cfg(test)]
mod simp_all_tests;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod simp_index;
#[cfg(test)]
mod simp_index_tests;
pub mod smt;
#[cfg(any(feature = "ay-smt", test))]
pub(crate) mod smt_translate;
pub(crate) mod specialize_generalize;
#[cfg(test)]
mod specialize_generalize_tests;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod state_ser;
#[cfg(test)]
mod state_ser_tests;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod suggest;
#[cfg(test)]
mod suggest_tests;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
// DELETION CANDIDATE (2026-07-30): the tactic_doc/entries.rs doc tables have no
// production caller anywhere in the crate; a future owner pass should decide keep-vs-delete.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tactic_doc;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tactic_doc_ext;
#[cfg(test)]
#[path = "tactic_doc_ext_tests.rs"]
mod tactic_doc_ext_tests;
pub(crate) mod tactic_interp;
pub use tactic_interp::{
    proof_state_for_tactic_target, run_tactic_script_with_snapshots, TacticGoalSnapshot,
    TacticPostSnapshotRange, TacticScriptSnapshotRun,
};
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod tactic_interp_ext;
#[cfg(test)]
#[path = "tactic_interp_ext_tests.rs"]
mod tactic_interp_ext_tests;
pub mod tactic_registry;
pub mod tacticm;
pub(crate) mod tauto;
pub(crate) mod tc_app;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod term_builder;
pub(crate) mod term_close;
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) mod trace;
#[cfg(test)]
mod trace_tests;
pub(crate) mod unfold;
pub(crate) mod unification_hint;
pub(crate) mod wlog;

// Re-exports
pub use core::{
    Goal, LocalDecl, ProofState, ProofTrustLedger, RewriteCandidate, SmtRecoveryLedger,
    TacticError, TacticResult, TrustedArithProvenanceLedger, TrustedAyProvenanceLedger,
};

pub use abs_cases::{abs_cases, abs_cases_with_config, AbsCasesConfig};
pub use algebra::{abel, abel_with_config, group, group_with_config, AbelConfig, GroupConfig};
pub(crate) use algebra::{is_pi_expr, match_eq_simple};
pub use arith_linarith::{
    linarith, linarith_prove, CertifiedConstraint, FMCertifiedResult, FMResult, LinarithCertificate,
};
pub use arithmetic::{LinearConstraint, LinearExpr};
pub use auto_cascade::auto_cascade;

pub use arith_field_simp::{field_simp, get_app_fn, make_equality};
pub use arith_nlinarith::{nlinarith, nlinarith_with_config, positivity, NlinarithConfig};
pub use arith_norm_cast::{exprs_syntactically_equal, is_cast_function, norm_cast};
pub use arith_push_neg::{
    contrapose, contrapose_hyp, is_false, match_and, match_eq, match_ge, match_gt, match_iff,
    match_le, match_lt, match_not, match_or, push_neg,
};
pub use omega_tactic::{
    omega, CertifiedMathverseConstraint, MathverseCertificate, MathverseCertifiedResult,
    MathverseContradictionType, OmegaConstraint,
};

pub use blast::{blast, blast_with_config, BlastConfig};
pub use cast::{
    assumption_mod_cast, exact_mod_cast, lift, lift_with_config, push_cast, qify, zify, CastConfig,
    LiftConfig,
};

pub use cc::{cc, cc_with_config, CCConfig};
pub(crate) use combinator::try_tactic_preserving_state;
pub use combinator::{
    all_goals, any_goals, first_tactic, focus, focus_and_done, repeat_tactic, trivial, try_tactic,
    Tactic,
};
pub use combinator_solve::solve_by_elim;

pub use combinators::{
    eval_all_goals as eval_all_goals_fn, eval_any_goals as eval_any_goals_fn,
    eval_first as eval_first_fn, eval_focus as eval_focus_fn, eval_repeat as eval_repeat_fn,
    eval_rotate as eval_rotate_fn, eval_swap as eval_swap_fn, eval_try as eval_try_fn,
    CombinatorConfig, TacticCtx, TacticFn,
};

pub use congr_obtain::{congr, obtain, revert};
pub use connective::{and_intros, by_contra, contradiction, exfalso, left_, right_, split_};
pub use contradiction::{eval_absurd, eval_contradiction, eval_exfalso};

pub use injection::{eval_discriminate, eval_discriminate_str, eval_injection, eval_injection_str};
// Re-export conv tactics
pub use conv::{conv_arg, conv_lhs, conv_rhs, conv_rw, ConvPath, ConvPosition, ConvState};
pub use conv_ext::{conv_change, conv_congr, conv_ext, eval_conv};

// Re-export convert/calc tactics
pub use calc::{
    calc_block, calc_eq, calc_rel_from_name, CalcJustification, CalcRel, CalcState, CalcStep,
};
pub use convert::{convert, convert_hyp};

// Re-export debug/utility tactics
pub use debug::{
    bound, clean, itauto, itauto_with_config, substs, trace, trace_expr, trace_state,
    trace_with_level, ITautoConfig, TraceLevel, TraceOutput,
};

// Re-export decide tactics
pub use decide::eval_decide;

// Re-export decide_eq tactics
pub use decide_eq::decide_eq;

// Re-export equality tactics
pub use equality::{
    calc_trans, rewrite, rewrite_at, rewrite_at_with_proof, rewrite_ltr, rewrite_rtl,
    rewrite_with_proof, subst, subst_vars, symm, trans,
};
pub(crate) use equality::{
    contains_expr, match_equality, replace_expr, rewrite_candidate_summaries,
};
#[cfg(test)]
pub(crate) use equality::{rewrite_chain, RewriteDirection, RewriteRule};
#[cfg(test)]
pub(crate) use extensionality_config::{congr_depth, congr_with_config, ext_multi, ExtConfig};

// Re-export existential tactics (existsi, by_cases, classical)
pub use existential::{by_cases, classical, existsi};

// Re-export enhanced exists/constructor tactics

// Re-export extensionality tactics
pub use extensionality::{funext, propext, quot_ext, set_ext};

// Re-export finite_cases tactics
pub(crate) use finite_cases::extract_nat_literal;
pub use finite_cases::fin_cases;
pub(crate) use interval_cases::expr_to_int;
pub use interval_cases::interval_cases;

// Re-export forward reasoning tactics (have, let, suffices)
pub use forward::{have_, suffices_};
pub use have_let::let_;

// Re-export gcongr tactic
pub use gcongr::gcongr;

// Re-export generalize tactics
pub use generalize::{ext, generalize, generalize_eq};

// Re-export grind tactics
pub use grind::{grind, grind_with_config, GrindConfig};

// Re-export goal management tactics
pub use goal::{goal_count, pick_goal, rotate, rotate_back, swap};

// Re-export hypothesis tactics
pub use hypothesis::{
    apply_fun, apply_fun_goal, clear, clear_all_unused, clear_except, duplicate, rename,
    rename_all, replace, replace_hyp, specialize,
};

// Re-export inductive reasoning tactics
pub use inductive_reasoning::{discriminate, injection, rcases};

// Re-export instance tactics
pub use instance::{have_i, infer_i, let_i};

// Re-export library_search tactics
pub use library_search::{
    library_search, library_search_and_apply, library_search_show, library_search_with_config,
    LibrarySearchConfig, LibrarySearchMatchKind, LibrarySearchResult,
};

// Re-export suggest tactics (exact?, apply?)

// Re-export LLM proof oracle helpers
pub use llm_oracle::{
    extract_proof_from_response, LlmHypothesis, LlmOracle, LlmOracleError, LlmProofRequest,
    LlmProofResponse, MockLlmOracle,
};

pub use ac_rfl::ac_rfl;
// Re-export monad preservation tactic (#3403)
pub use arith_linarith_kernel::{
    linarith_kernel_proof, linarith_kernel_theorem, LinarithKernelError,
};
pub(crate) use monad_pres::monad_pres;
pub use nn_verify::nn_verify;
pub use norm::norm_num;
pub use norm_num::eval_norm_num;
pub use norm_num_ext::eval_norm_num_ext;
pub use norm_num_kernel::{
    norm_num_kernel_proof_only, norm_num_kernel_theorem, NormNumKernelError,
};

// Re-export mathverse_use / mathverse_suggest public API (feature-gated)
#[cfg(feature = "mathverse-library")]
pub use mathverse_use::{clear_mathverse_library, run_strict_mathverse_use, set_mathverse_library};

pub use oracle::{build_oracle_request, oracle_suggest};

// Re-export tactic-script execution helpers shared with clean-server/oracle replay
pub use script_runner::{execute_simple_tactic, parse_tactic_script, ElabOracleCandidateRunner};

// Re-export options tactics
pub use options::{set_option, set_options, OptionValue, ProofOptions, SetOptionConfig};

// Re-export pattern/monotonicity tactics
pub(crate) use pattern::contains_unassigned_meta;
pub(crate) use pattern::exprs_equal;
pub use pattern::{
    choose, choose_simple, continuity, continuity_with_config, destruct_named_hypothesis, dsimp,
    dsimp_all, dsimp_at, dsimp_with_config, infer_instance, infer_instance_with_config,
    linear_combination, linear_combination_simple, linear_combination_with_config, measurability,
    measurability_with_config, mono, mono_with_config, nontriviality, nontriviality_of,
    nontriviality_with_config, peel, rintro, rintro_patterns, simpa, simpa_only, simpa_with_config,
    split_ifs, split_ifs_with_config, split_ifs_with_names, ChooseConfig, ContinuityConfig,
    DsimpConfig, InferInstanceConfig, LinearCoeff, LinearCombinationConfig, MeasurabilityConfig,
    MonoConfig, MonoStep, NontrivialityConfig, RIntroPattern, SplitIfsConfig,
};

// Re-export polyrith tactics
pub use polyrith::{
    is_polynomial_expr, polyrith, polyrith_with_config, Polynomial, PolyrithCertificate,
    PolyrithConfig,
};

// Re-export positivity tactics
pub use positivity::{positivity_at, positivity_at_with_config, PositivityAtConfig};

// Re-export project mathverse wrapper
pub use project_mathverse::{
    cert_mathverse, cert_mathverse_with_config, cert_mathverse_with_report, BlockerOrigin,
    MathverseBlocker, MathverseBlockerKind, NatCoercionPolicy, ProjectMathverseConfig,
    ProjectMathverseOutcome, ProjectMathverseReport,
};

// Re-export certificate simplifier
pub use cert_simp::{cert_simp, CertSimpConfig};

// Re-export proof_manipulation tactics (cases) and induction (split to induction.rs, #307)
pub use cases::{eval_cases, eval_rcases, eval_rcases_depth, RCasesPattern};
pub use induction::{induction, induction_using, induction_using_alts};
pub use proof_manipulation::cases;

// Re-export proof_term tactics (exact, intro, apply, assumption, constructor, rfl)
pub use proof_term::{apply, assumption, constructor, exact, intro, intros, reduce_eq, rfl};

// Re-export certified variants
pub use proof_term_cert::{
    apply_with_cert, assumption_with_cert, exact_with_cert, intro_with_cert, CertifiedTacticResult,
};

// Re-export registry types
pub use registry::{
    BoundValue, CompoundTacticEntry, CompoundTacticHandler, TacticArgPattern, TacticEntry,
    TacticEval, TacticHandler, TacticPatterns, TacticRegistry,
};

// Re-export ring tactics
pub use ring::{ring, ring_nf};

// Re-export field tactics
pub(crate) use field_tactic::field_normalize_tactic;

// Re-export search tactics
pub use search::{
    aesop, aesop_with_config, apply_search, apply_search_and_apply, exact_search,
    exact_search_and_apply, hint, rewrite_search, rewrite_search_and_apply, suggest, AesopConfig,
    AesopRule, AesopRuleKind, AesopSearchState, RuleAttempt, SearchResult, TacticSuggestion,
};
pub(crate) use search::{can_apply_to_produce, types_unify};

// Re-export simp tactics
pub(crate) use simp::simp_all_with_config;
#[cfg(test)]
pub(crate) use simp::substitute_bvar;
pub use simp::{
    extract_equality_from_type, simp, simp_all, simp_at, simp_at_all, simp_default, simp_only,
    simp_only_at, simp_rw, simp_rw_hyps, squeeze_simp, squeeze_simp_and_apply,
    squeeze_simp_with_config, SimpConfig, SimpIndexMode, SimpLemma, SqueezeSimpConfig,
    SqueezeSimpResult,
};

// Re-export specialize_generalize tactics (multi-arg, at-hypothesis, dependency-aware)

// Re-export SMT tactics
pub use smt::{
    ay_bv, ay_decide, ay_decide_with_lrat_proof, ay_decide_with_proof, ay_lra, ay_omega, ay_smt,
    decide, AyConfig, AyProofConfig,
};

pub use arith_linarith::{arith_proof_count, reset_arith_counter};
pub use smt::{
    assert_no_sorry, enable_sorry_location_tracking, reset_sorry_counter, reset_sorry_locations,
    sorry_count, sorry_locations,
};
pub use smt::{ay_proof_count, reset_ay_counter};

// Re-export create_sorry_term from kernel for internal test helpers.
#[cfg(test)]
pub(crate) use clean_kernel::sorry::create_sorry_term;

// Re-export DRAT/LRAT verifier types
pub use drat::{
    verify_and_reconstruct_drat, verify_and_reconstruct_lrat, verify_lrat_streaming, CnfFormula,
    DratError, DratOp, DratProof, DratProofResult, DratVerifier, LratCheckpoint, LratOp, LratProof,
    LratVerifier, ProofReconstructor, StepResult, StreamingLratVerifier,
};

pub use tauto::tauto;

// Re-export term_close tactics
pub use term_close::{
    admit, assert_, assert_after, change, change_at, dec_trivial, native_decide, norm_beta, refine,
    refine_placeholder, rfl_closure, show, sorry, use_, use_single,
};

// Re-export unfold tactics
pub(crate) use unfold::collect_consts;
pub use unfold::{delta, reduce, unfold, unfold_at, whnf};
// Re-export wlog tactics
pub use wlog::{norm_num_at, push_neg_at, suffices_to_show, wlog};
#[cfg(test)]
mod tests;
