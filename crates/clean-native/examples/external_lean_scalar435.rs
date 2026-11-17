// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Exercise an original external Lean4.35 scalar entry through the maintained
//! owned-source/replay/runtime-closure/TrustCG/in-process callable route.
//! The input is a diagnostic request, never an admission certificate. Keep
//! model-specific query construction and independent expected values in the
//! consuming frontend (for example TY's original Ring scalar facade).

use anyhow::{bail, Context};
use clean_kernel::{LeanWorld, Name};
use clean_native::external_lean::{
    ExternalLeanInput, ExternalLeanProgram, ExternalLeanScopedProgram,
};
use serde::Deserialize;
use std::io::Write;
use std::path::PathBuf;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    file: PathBuf,
    module: String,
    declaration: String,
    imports: Vec<String>,
    search_paths: Vec<PathBuf>,
    inspect: Vec<String>,
    cases: Vec<Case>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    arguments: (u32, u32, u64, u64),
    expected: u64,
}

fn main() -> anyhow::Result<()> {
    let mut arguments = std::env::args_os().skip(1);
    let mut scoped = false;
    let mut world = LeanWorld::Lean435;
    let mut capture_json = None;
    let mut request_path = None;
    while let Some(argument) = arguments.next() {
        if argument == "--scoped-runtime" {
            scoped = true;
        } else if argument == "--world" {
            world = match arguments
                .next()
                .context("expected exact world tag")?
                .to_str()
            {
                Some("v4.35.0") => LeanWorld::Lean435,
                Some("v4.30.0-rc2") => LeanWorld::ORACLE,
                _ => bail!("expected v4.35.0 or v4.30.0-rc2"),
            };
        } else if argument == "--capture-json" {
            capture_json = Some(PathBuf::from(
                arguments.next().context("expected capture JSON path")?,
            ));
        } else if request_path.replace(PathBuf::from(argument)).is_some() {
            bail!("expected exactly one request JSON path");
        }
    }
    let request_path = request_path.context("expected request JSON path")?;
    if capture_json.is_some() && !scoped {
        bail!("--capture-json requires --scoped-runtime");
    }
    let request: Request = serde_json::from_slice(&std::fs::read(&request_path)?)?;
    if request.imports.is_empty() || request.cases.is_empty() {
        bail!("explicit imports and nonempty observation cases are required");
    }
    let names: Vec<_> = request
        .imports
        .iter()
        .map(|s| Name::from_string(s))
        .collect();
    let module = Name::from_string(&request.module);
    let root = Name::from_string(&request.declaration);
    eprintln!(
        "phase=elaborate world={} source={}",
        world.tag(),
        request.file.display()
    );
    let input = || ExternalLeanInput {
        file: &request.file,
        module: &module,
        imports: &names,
        search_paths: &request.search_paths,
        world,
    };
    let mut callable = if scoped {
        eprintln!("capture=explicit-runtime-scope root={root:?}");
        let program = ExternalLeanScopedProgram::elaborate(input(), std::slice::from_ref(&root))?;
        eprintln!(
            "global_capture_errors={} global_digest={} scoped_members={} scoped_digest={}",
            program.source_capture().errors.len(),
            program.source_capture().snapshot_blake3.is_some(),
            program.scoped_capture().members().len(),
            program.scoped_capture().snapshot_blake3().is_some()
        );
        if let Some(path) = &capture_json {
            write_capture(&program, path)?;
        }
        for declaration in &request.inspect {
            eprintln!("phase=inspect declaration={declaration}");
            let inspected = program.inspect_owned_declaration(&Name::from_string(declaration))?;
            eprintln!(
                "replayed={declaration} closure_digest={:02x?}",
                inspected.closure_digest()
            );
        }
        eprintln!("phase=select declaration={}", request.declaration);
        let selected = program.select_in_runtime_closure(&root, 0)?;
        eprintln!(
            "phase=load selected_bodies={}",
            selected.declarations().len()
        );
        selected.load_scalar_call()?
    } else {
        let program = ExternalLeanProgram::elaborate(input())?;
        for declaration in &request.inspect {
            eprintln!("phase=inspect declaration={declaration}");
            let inspected = program.inspect_owned_declaration(&Name::from_string(declaration))?;
            eprintln!(
                "replayed={declaration} closure_digest={:02x?}",
                inspected.closure_digest()
            );
        }
        eprintln!("phase=select declaration={}", request.declaration);
        let selected = program.select_in_runtime_closure(&root, 0)?;
        eprintln!(
            "phase=load selected_bodies={}",
            selected.declarations().len()
        );
        selected.load_scalar_call()?
    };
    for (index, case) in request.cases.iter().enumerate() {
        let (a, b, c, d) = case.arguments;
        let actual = callable.call(a, b, c, d);
        println!(
            "{}",
            serde_json::json!({"case": index, "arguments": case.arguments,
            "actual": actual, "expected": case.expected, "matches": actual == case.expected})
        );
        if actual != case.expected {
            bail!(
                "scalar observation mismatch at case {index}: expected {}, actual {actual}",
                case.expected
            );
        }
    }
    eprintln!("phase=complete cases={} route=owned-source/replay/runtime-closure/TrustIR/TrustCG/in-process clean-compiler-unvalidated; no binary proof", request.cases.len());
    Ok(())
}

fn write_capture(
    program: &ExternalLeanScopedProgram,
    path: &std::path::Path,
) -> anyhow::Result<()> {
    let global = program.source_capture();
    let scope = program.scoped_capture();
    let inputs: Vec<_> = program
        .inputs()
        .iter()
        .map(|r| (&r.path, r.sha256, r.bytes))
        .collect();
    let failures: Vec<_> = global
        .row_failures
        .iter()
        .map(|r| (r.phase, &r.name, &r.reason))
        .collect();
    let capture = serde_json::json!({
        "world": program.world().tag(), "inputs": inputs,
        "global": { "errors": global.errors, "row_failures": failures,
            "delta_complete": global.delta_complete, "snapshot_blake3": global.snapshot_blake3,
            "before_rows": global.before.len(), "after_rows": global.after.len(),
            "limitations": global.limitations },
        "scope": { "roots": scope.roots(), "members": scope.members(),
            "sources": scope.sources(), "before": scope.before(), "after": scope.after(),
            "errors": scope.errors(), "snapshot_blake3": scope.snapshot_blake3(),
            "complete": scope.is_complete() },
        "claim": "actual local observations only; no source, binary or model admission certificate"
    });
    let file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(path)?;
    let mut output = std::io::BufWriter::new(file);
    serde_json::to_writer(&mut output, &capture)?;
    output.flush()?;
    Ok(())
}
