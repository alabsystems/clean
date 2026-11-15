// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **One process for every test that builds a `Specification`.**
//!
//! `Specification::new()` costs about fifteen minutes
//! (`crates/clean-verify/tests/fixtures/is_valid_char.lineage.json` records
//! 1,604.7 s mean over four replicates), and `test_utils::shared_spec` already
//! builds it ONCE PER PROCESS behind a `OnceLock`. That cache cannot cross a
//! process boundary, so cargo's one-binary-per-`tests/*.rs` rule was paying the
//! build once per FILE: of the 56 files below, 47 reach `FULL_SPEC` and 7 reach
//! `SUBSTITUTION_SPEC`, and together they cost AT LEAST 12.59 measured hours of
//! rebuilding two immutable objects -- a floor, because six of the 56 carry no
//! recorded duration and are counted at zero.
//!
//! This target is that boundary removed. Every file below is `#[path]`-included
//! as a module and is compiled and run EXACTLY as it was — same tests, same
//! assertions, same `tests/` location, so every in-repo citation of these paths
//! still resolves. What changes is that they share one process, so each
//! specification flavour is built once for all of them.
//!
//! **Adding a test file:** `crates/clean-verify/Cargo.toml` sets
//! `autotests = false`, so a new `tests/*.rs` is compiled only if it is listed
//! here or declared as its own `[[test]]`. That is a real hazard — a test
//! nobody builds is a test that cannot fail — so
//! `scripts/check_test_target_coverage.py` refuses any `tests/*.rs` that is
//! neither, and it is wired into the local gate.
//!
//! **What deliberately stays a separate target**, and why:
//!
//! * `crystal_a1_lineage` — its own 24-submodule aggregation already, and its
//!   own 9 GB gate weight, which is most of this box's 16 GB budget; folding
//!   that into a target that also holds a `Specification` is how a lane gets
//!   refused admission rather than scheduled. (Its recorded ERROR is NOT a
//!   failure: `heavy_gate REFUSED 9 GB; target NOT run`.)
//! * `crystal_a3_semdiff` — owned by another lane, which sharded its W1 gate
//!   per chain on 2026-09-20; `w1_get_char_val_trunc` still runs past 26 min.
//!   Not ours to move.
//! * `eval_ir` — the EvalIR flavour only (7.1 s to build), 51 s end to end.
//! * `evalir_scratchpad`, `spec_scratchpad` — a scratchpad exists to iterate in
//!   seconds; sharing a process with a 1,605 s build would destroy that.
//! * `fidelity_gate_lane` — 3.7 s. Nothing to win.

// The CFG comparator and its parsers, ONCE. Seventeen mint chains each used to
// `#[path]`-include this cluster, which was free while each chain was its own
// crate and is `clippy::duplicate_mod` now that they share one: the same seven
// files compiled seventeen times, and their four self-tests RUN seventeen
// times. Nothing is lost by sharing one copy -- measured before moving it, the
// cluster's every `super::` reference points inside itself, never at a chain's
// `PREFIX` / `tags()` / `IR_*_CORE`, so the copies were identical rather than
// per-chain. Items are `pub(crate)`, so they stay reachable from every chain,
// and a chain that reaches the cluster only through its own submodules
// (`crystal_a2_mint_lzc`) still resolves `super::emitted_cfg` through its
// `use`.
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

#[path = "acceptance_cdp_in_census.rs"]
mod acceptance_cdp_in_census;
#[path = "accepts_tc_native_fold_census.rs"]
mod accepts_tc_native_fold_census;
#[path = "accepts_tc_string_literal_census.rs"]
mod accepts_tc_string_literal_census;

#[path = "axiom_ratchet.rs"]
mod axiom_ratchet;

#[path = "axiom_refutation_gate.rs"]
mod axiom_refutation_gate;

#[path = "beta_reduces_binder_congruence.rs"]
mod beta_reduces_binder_congruence;

#[path = "beta_reduces_extended_constructors.rs"]
mod beta_reduces_extended_constructors;

#[path = "beta_reduces_rec_blocker.rs"]
mod beta_reduces_rec_blocker;

#[path = "byte_memory_stale_proof.rs"]
mod byte_memory_stale_proof;

#[path = "complete_development_model.rs"]
mod complete_development_model;

#[path = "crystal_a2_mint.rs"]
mod crystal_a2_mint;

#[path = "crystal_a2_mint_br.rs"]
mod crystal_a2_mint_br;

#[path = "crystal_a2_mint_ep.rs"]
mod crystal_a2_mint_ep;

#[path = "crystal_a2_mint_fc.rs"]
mod crystal_a2_mint_fc;

#[path = "crystal_a2_mint_fng.rs"]
mod crystal_a2_mint_fng;

#[path = "crystal_a2_mint_fbq.rs"]
mod crystal_a2_mint_fbq;

#[path = "crystal_a2_mint_floats.rs"]
mod crystal_a2_mint_floats;

#[path = "crystal_a2_mint_fs.rs"]
mod crystal_a2_mint_fs;

#[path = "crystal_a2_mint_fw.rs"]
mod crystal_a2_mint_fw;

#[path = "crystal_a2_mint_gc.rs"]
mod crystal_a2_mint_gc;

#[path = "crystal_a2_mint_hlb.rs"]
mod crystal_a2_mint_hlb;

#[path = "crystal_a2_mint_it.rs"]
mod crystal_a2_mint_it;

#[path = "crystal_a2_mint_its.rs"]
mod crystal_a2_mint_its;

#[path = "crystal_a2_mint_ko.rs"]
mod crystal_a2_mint_ko;

#[path = "crystal_a2_mint_lz.rs"]
mod crystal_a2_mint_lz;

#[path = "crystal_a2_mint_lzc.rs"]
mod crystal_a2_mint_lzc;

#[path = "crystal_a2_mint_mt.rs"]
mod crystal_a2_mint_mt;

#[path = "crystal_a2_mint_ni.rs"]
mod crystal_a2_mint_ni;

#[path = "crystal_a2_mint_pv.rs"]
mod crystal_a2_mint_pv;

#[path = "crystal_a2_mint_sm.rs"]
mod crystal_a2_mint_sm;

#[path = "crystal_a2_mint_vc.rs"]
mod crystal_a2_mint_vc;

#[path = "def_eq_joinable.rs"]
mod def_eq_joinable;

#[path = "definitional_extension_provenance.rs"]
mod definitional_extension_provenance;

#[path = "delta_step_bridge.rs"]
mod delta_step_bridge;

#[path = "delta_step_keystone.rs"]
mod delta_step_keystone;

#[path = "delta_subst_keystone.rs"]
mod delta_subst_keystone;

#[path = "eval_ir_its_census.rs"]
mod eval_ir_its_census;
// The frame-stacking / module-extension families' census: registration of the
// hand-authored foundation (eval_ir_stack.rs) and the 103 minted declarations
// (eval_ir_stack_minted.rs), empty axiom closures, abstract-module shape witness.
#[path = "eval_ir_bmem_census.rs"]
mod eval_ir_bmem_census;
#[path = "eval_ir_ctr_census.rs"]
mod eval_ir_ctr_census;

#[path = "eval_ir_stack_census.rs"]
mod eval_ir_stack_census;
// The assume-guarantee activation's census: the A4-SHAPED statement about
// infer_type, and the assertions that stop its NAME outrunning its premises.
#[path = "eval_ir_itf_census.rs"]
mod eval_ir_itf_census;

#[path = "instantiate_at_diagnostic.rs"]
mod instantiate_at_diagnostic;

#[path = "instantiate_at_refl_blockers.rs"]
mod instantiate_at_refl_blockers;

#[path = "iota_step_bridge.rs"]
mod iota_step_bridge;

#[path = "iota_step_keystone.rs"]
mod iota_step_keystone;

#[path = "kapp_spine_recognizers.rs"]
mod kapp_spine_recognizers;

#[path = "kernel_core_red_env_fidelity.rs"]
mod kernel_core_red_env_fidelity;

#[path = "par_reduces_c_model.rs"]
mod par_reduces_c_model;

#[path = "par_reduces_d_model.rs"]
mod par_reduces_d_model;

#[path = "par_reduces_p_model.rs"]
mod par_reduces_p_model;

#[path = "par_reduces_pd_model.rs"]
mod par_reduces_pd_model;

#[path = "premise_witness_gate.rs"]
mod premise_witness_gate;

#[path = "proof_status_invariants.rs"]
mod proof_status_invariants;

#[path = "rec_env_model.rs"]
mod rec_env_model;

#[path = "spec_add_inductive_eq_regression.rs"]
mod spec_add_inductive_eq_regression;

#[path = "spec_axiom_closure_honesty.rs"]
mod spec_axiom_closure_honesty;

#[path = "subst_commutes_bvar_bridge.rs"]
mod subst_commutes_bvar_bridge;

#[path = "subst_commutes_bvar_shift.rs"]
mod subst_commutes_bvar_shift;

#[path = "subst_commutes_bvar_shift_above.rs"]
mod subst_commutes_bvar_shift_above;

#[path = "subst_commutes_nested.rs"]
mod subst_commutes_nested;

#[path = "substitution_def_eq_axiom_deps.rs"]
mod substitution_def_eq_axiom_deps;

#[path = "native_fold_canon_spec.rs"]
mod native_fold_canon_spec;

#[path = "the_red_env.rs"]
mod the_red_env;

#[path = "type_preservation_provenance.rs"]
mod type_preservation_provenance;

#[path = "vacuity_firewall.rs"]
mod vacuity_firewall;

#[path = "whnf_lemma_wrapper_defs.rs"]
mod whnf_lemma_wrapper_defs;
