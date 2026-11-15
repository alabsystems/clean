// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `ir_steps` reduction ladder. SCRATCH: it PRINTS a table and asserts only that
//! the module itself elaborates — the rungs are the measurement.

use super::*;
use crate::test_utils::{build_eval_ir_spec_with_stack, parse_check, run_with_stack};
use std::time::Instant;

#[test]
fn eval_ir_steps_scaling_ladder() {
    run_with_stack(|| {
        let mut spec = build_eval_ir_spec_with_stack();
        let mut rows: Vec<String> = Vec::new();
        let mut module_ok = true;
        for (name, src) in Specification::eval_ir_steps_scaling_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            let t0 = Instant::now();
            let res = spec.add_recursive_def(&src, "ir_steps scaling probe");
            let dt = t0.elapsed().as_secs_f64();
            match res {
                Ok(()) => rows.push(format!("  {name:<16} OK      {dt:8.3}s")),
                Err(e) => {
                    // The FULL text: a refusal with a shape is readable, a truncated one is not.
                    let short: String = e.to_string().chars().take(600).collect();
                    rows.push(format!("  {name:<16} REFUSED {dt:8.3}s  {short}"));
                    if !name.starts_with("ir_sc_run_") {
                        module_ok = false;
                    }
                }
            }
        }
        eprintln!("=== ir_steps reduction ladder ===");
        for r in &rows {
            eprintln!("{r}");
        }
        assert!(
            module_ok,
            "the loop MODULE did not elaborate, so the ladder measures nothing:\n{}",
            rows.join("\n")
        );
    });
}
