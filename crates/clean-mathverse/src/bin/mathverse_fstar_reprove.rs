// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Re-prove F* facts directly in Clean's kernel and report the verdict.
//!
//! Unlike importing (which yields assumed axioms), every fact here is proven by
//! construction in Clean's CIC, so it reduces to the foundational axioms
//! (`propext` / `Quot.sound` / `Classical.choice`) — genuine bedrock.
//!
//! Usage: mathverse_fstar_reprove

use std::process::exit;

use clean_kernel::Environment;
use clean_mathverse::fstar_reproof::reprove_all;

fn main() {
    let mut env = match Environment::try_with_prelude() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("failed to build kernel prelude environment: {e}");
            exit(1);
        }
    };
    let results = reprove_all(&mut env);
    let checked = results.iter().filter(|r| r.kernel_checked).count();
    let bedrock = results.iter().filter(|r| r.bedrock).count();

    println!("=== F* facts re-proven in Clean's kernel ===");
    println!("  candidates:      {}", results.len());
    println!("  kernel-checked:  {checked}");
    println!(
        "  BEDROCK:         {bedrock}  (axiom_deps ⊆ propext / Quot.sound / Classical.choice)"
    );
    println!("\n  sample of re-proven F* facts:");
    for r in results.iter().filter(|r| r.bedrock).take(10) {
        println!("    {:<26} {}", r.name, r.fstar);
    }
    // Kernel-checked-but-not-bedrock: honest — a prelude constant in the
    // statement transitively rests on a non-foundational Clean constant.
    let near = checked - bedrock;
    if near > 0 {
        println!(
            "\n  {near} kernel-checked but NOT bedrock (statement rests on a \
             non-foundational prelude constant) — honestly not counted."
        );
    }
    if bedrock == 0 {
        exit(1);
    }
}
