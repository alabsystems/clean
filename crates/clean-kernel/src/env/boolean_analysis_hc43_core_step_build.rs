// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// The `hc43_core_step` proof-term builder (S1 → S2 → close). `include!`d into
// `boolean_analysis_hc43_core_step.rs`. Split across <500-line files.

/// Build the type + proof of `hc43_core_step`.
fn build_hc43_step(c: &Hc43StepConsts) -> (Expr, Expr) {
    let ty = build_hc43_step_ty(c);
    let value = build_hc43_step_value(c);
    (ty, value)
}

include!("boolean_analysis_hc43_core_step_chain.rs");
