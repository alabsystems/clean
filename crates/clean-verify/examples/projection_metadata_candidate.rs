// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Diagnostic candidate from the production reflector, for independent proof
//! development when a later full-specification declaration prevents publication.
//! This validates only the artifact-independent seed and generated definitions.
//! It never replaces committed artifacts or certifies the complete corpus.

use std::io::Write;

use clean_verify::red_env_reflect::reflect_foundation_core;
use clean_verify::Specification;

fn candidate() -> Result<(), String> {
    let spec = Specification::new_red_env_reflection_seed()
        .map_err(|error| format!("reflection seed: {error:?}"))?;
    let reflection = reflect_foundation_core(spec.env()).map_err(|error| error.to_string())?;
    let script = reflection.def_script().map_err(|error| error.to_string())?;
    Specification::validate_red_env_reflection_script(&script)
        .map_err(|error| format!("candidate definitions: {error:?}"))?;
    eprintln!(
        "CANDIDATE ONLY: production reflection and seed checks passed; \
         full specification, independent replay, and publication NOT performed"
    );
    std::io::stdout()
        .lock()
        .write_all(script.as_bytes())
        .map_err(|error| error.to_string())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let result = std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(candidate)?
        .join()
        .map_err(|_| std::io::Error::other("candidate generation thread panicked"))?;
    result.map_err(std::io::Error::other)?;
    Ok(())
}
