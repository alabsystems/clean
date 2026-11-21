// Copyright 2026 Andrew Yates. Apache-2.0.
//! Actual fixed-cohort baseline qualification; no source/model authority claim.
use std::error::Error;
use std::path::Path;

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    if arguments.len() < 4 {
        return Err(
            "usage: check_fixed_source_context DIRECTORY MANIFEST SCHEMA SOURCE_MODULE...".into(),
        );
    }
    let manifest = std::fs::read_to_string(&arguments[1])?;
    let sources = arguments[3..]
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let context = clean_olean::fixed_cohort::open_source_context(
        Path::new(&arguments[0]),
        &manifest,
        &arguments[2],
        &sources,
        &[
            "PProd",
            "PProd.fst",
            "PProd.snd",
            "Eq",
            "False",
            "True",
            "Iff",
        ],
    )?;
    println!("CHECKED_FIXED_SOURCE_CONTEXT modules={} roots={} declarations={} identity={} reference={:?}", context.modules().len(), context.roots().len(), context.environment().num_constants(), context.identity(), context.reference_digest());
    for name in ["List.takeWhile", "Eq", "False.rec", "Iff.rec", "True.rec"] {
        if context
            .environment()
            .get_const(&clean_kernel::Name::from_string(name))
            .is_none()
        {
            return Err(format!(
                "checked source context lacks required original library declaration {name}"
            )
            .into());
        }
    }
    for name in ["SemR.runBlob", "SemR.BoolBody.checked_blob"] {
        if context
            .environment()
            .get_const(&clean_kernel::Name::from_string(name))
            .is_some()
        {
            return Err(format!("source context contains model declaration {name}").into());
        }
    }
    Ok(())
}
