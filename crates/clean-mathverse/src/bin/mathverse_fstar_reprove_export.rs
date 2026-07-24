// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Admit the re-proven F* facts INTO a Mathverse shard as `KernelVerified`
//! theorems, each carrying its real kernel proof term.
//!
//! Unlike importing (which yields assumed axioms), every theorem here is proven
//! by construction in Clean's CIC and reduces to the foundational axioms
//! (`propext` / `Quot.sound` / `Classical.choice`). The emitted `.mathverse`
//! shard re-verifies at 100% `KernelVerified` (see the
//! `admitted_fstar_proofs_are_100pct_kernel_verified` test).
//!
//! Usage: mathverse_fstar_reprove_export <out.mathverse>

use std::process::exit;

use clean_kernel::Environment;
use clean_mathverse::fstar_reproof::export_reproven_shard;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let Some(out) = args.get(1) else {
        eprintln!("usage: mathverse_fstar_reprove_export <out.mathverse>");
        exit(2);
    };

    let mut env = match Environment::try_with_prelude() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("failed to build kernel prelude environment: {e}");
            exit(1);
        }
    };

    let (builder, admitted, skipped) = export_reproven_shard(&mut env);
    if let Err(e) = builder.write_to_file(out) {
        eprintln!("failed to write shard {out}: {e}");
        exit(1);
    }

    println!("=== F* re-proven facts admitted into Mathverse ===");
    println!("  admitted (KernelVerified theorems): {admitted}");
    println!("  skipped (not bedrock):              {skipped}");
    println!("  shard:                              {out}");
    println!(
        "  every admitted theorem carries a real proof term and re-verifies as \
         KernelVerified (reduces to propext / Quot.sound / Classical.choice)."
    );
    if admitted == 0 {
        exit(1);
    }
}
