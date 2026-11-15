// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Handler test modules

use crate::handlers::ServerState;

/// A state whose file methods are confined to the system's temporary
/// directory, where these tests read and write: `ServerState::new` confines
/// them to the directory the test runs in (`trust_boundary::confine`).
pub(super) fn temp_rooted_state() -> ServerState {
    ServerState::new().with_workspace_root(&std::env::temp_dir())
}

/// `state`'s launch token, as `loadEnvironment` with `replace_unchecked`
/// carries it in `params.token`.
pub(super) fn launch_token_of(state: &ServerState) -> Option<String> {
    state.launch_token().map(|t| t.as_str().to_string())
}

mod archive;
mod ay_contract_ratchet;
mod check_declarations;
mod compose_proof;
mod concurrent_writers;
mod contract_shape_ratchet;
mod core;
mod dict;
mod environment;
mod exact_parsing;
mod external_cert;
mod external_cert_alethe;
mod external_cert_fixtures;
mod fill_sorries;
pub(crate) mod free_gate;
#[cfg(unix)]
mod import_module_confinement;
mod metrics;
mod minif2f_bench;
mod misc;
mod parse;
mod premises;
mod proof;
mod proof_state;
mod proof_trust;
mod proof_trust_batch;
mod prove_contract;
mod prove_smt;
mod request_bounds;
mod request_deadline;
mod request_work;
mod runtime_frees;
mod runtime_residuals;
mod save_file;
mod search_proof;
mod swarm;
mod tactics;
mod trusted_arith_provenance;
mod verify_c;
mod verify_cert;
mod verify_file;
mod verify_request_trust;
mod widget;
mod writer_turns;
