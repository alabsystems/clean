// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit checked runtime closure over full official Lean4.35 imports.
//! This program exercises records, functions, a captured closure and a runtime
//! implementation different from its logical body. No Veil/Ring or proof claim.

use clean_compiler::cli::EmitFormat;
use clean_kernel::{LeanWorld, Name};
use clean_native::external_lean::{ExternalLeanInput, ExternalLeanProgram};
use sha2::{Digest, Sha256};
use std::path::Path;
use std::process::Command;

const SOURCE: &str = "import Lean\n\
inductive RuntimeFlag where\n | off\n | on\n\
structure RuntimePair where\n left : RuntimeFlag\n right : RuntimeFlag\n\
def runtimeMake (x : RuntimeFlag) : RuntimePair := RuntimePair.mk x RuntimeFlag.on\n\
def runtimeApply (f : RuntimeFlag → RuntimeFlag) (x : RuntimeFlag) : RuntimeFlag := f x\n\
def runtimeFast (x : RuntimeFlag) : RuntimeFlag := runtimeApply (fun _ => (runtimeMake x).left) RuntimeFlag.off\n\
@[implemented_by runtimeFast] def runtimeSlow (_ : RuntimeFlag) : RuntimeFlag := RuntimeFlag.off\n\
def handoff435 (x : RuntimeFlag) : RuntimeFlag := runtimeSlow x\n";

fn digest(path: &Path) -> anyhow::Result<String> {
    Ok(Sha256::digest(std::fs::read(path)?)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn main() -> anyhow::Result<()> {
    let dir = tempfile::tempdir()?;
    let source = dir.path().join("Runtime435.lean");
    std::fs::write(&source, SOURCE)?;
    let module = Name::from_string("Runtime435");
    let root = Name::from_string("handoff435");
    let program = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &source,
        module: &module,
        imports: &[Name::from_string("Lean")],
        search_paths: &[],
        world: LeanWorld::Lean435,
    })?;
    let legacy = match program.select(&root, 0) {
        Err(error) => error,
        Ok(_) => anyhow::bail!("legacy whole-environment refusal was lost"),
    };
    anyhow::ensure!(
        legacy.to_string().contains("native-implemented-by-order"),
        "{legacy}"
    );
    println!(
        "world={} legacy-selection=REFUSED retained-policy={legacy}",
        program.world().tag()
    );
    let selected = program.select_in_runtime_closure(&root, 0)?;
    anyhow::ensure!(
        selected
            .declarations()
            .iter()
            .any(|decl| decl.name == Name::from_string("runtimeFast")),
        "runtime implementation was not selected"
    );
    anyhow::ensure!(
        !selected
            .declarations()
            .iter()
            .any(|decl| decl.name == Name::from_string("runtimeSlow")),
        "logical implementation body was selected"
    );
    let c = selected.emit(EmitFormat::C)?;
    let c_driver = "int main(void) { for (unsigned tag=0;tag<2;++tag) { clean_obj* result=l_handoff435(clean_box(tag)); if (clean_obj_tag(result)!=tag) return 1; } return 0; }";
    let c_binary =
        clean_native::native_build::build_extract_executable(dir.path(), "", &c, c_driver)?;
    let status = Command::new(&c_binary).status()?;
    anyhow::ensure!(status.success(), "actual435 C execution: {status}");
    println!("world={} route=owned-source/full-imports/replay/checked-runtime-closure/L5CNF/L5IR/C record/function/capture/implemented-by cases=2 {status}; source SHA256={}; experimental/unverified; no binary proof",program.world().tag(), digest(&source)?);
    #[cfg(feature = "trust-ir-backend")]
    {
        let ir = selected.emit(EmitFormat::Trustir)?;
        for expected in [
            "fn @handoff435(",
            "fn @clean_alloc_ctor(",
            "fn @clean_alloc_closure(",
        ] {
            anyhow::ensure!(
                ir.contains(expected),
                "missing actual ExternCalls operation: {expected}"
            );
        }
        let object = dir.path().join("handoff435.o");
        selected.emit_object(&object)?;
        clean_native::native_runtime::materialize(dir.path(), false, &mut Vec::new())?;
        let driver = dir.path().join("driver.c");
        std::fs::write(&driver,"#include \"clean_runtime.h\"\nextern clean_obj* handoff435(clean_obj*);\nint main(void) { for (unsigned tag=0;tag<2;++tag) { clean_obj* result=handoff435(clean_box(tag)); if (clean_obj_tag(result)!=tag) return 1; } return 0; }\n")?;
        let binary = dir.path().join("native435");
        let output = Command::new("/usr/bin/cc")
            .args(["-O2", "-std=c11", "-I"])
            .arg(dir.path())
            .arg(&driver)
            .arg(&object)
            .arg(dir.path().join("libclean_runtime.a"))
            .args(["-lm", "-o"])
            .arg(&binary)
            .output()?;
        anyhow::ensure!(
            output.status.success(),
            "actual435 full runtime link: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let status = Command::new(&binary).status()?;
        anyhow::ensure!(
            status.success(),
            "actual435 TrustCG runtime execution: {status}"
        );
        println!("world={} route=checked-runtime-closure/ExternCalls/checked-object/TrustCG/complete-runtime record/function/capture/implemented-by cases=2 {status}; clean-compiler-unvalidated; no binary proof; binary SHA256={} object={} runtime={} driver={}",program.world().tag(),digest(&binary)?,digest(&object)?,digest(&dir.path().join("libclean_runtime.a"))?,digest(&driver)?);
    }
    Ok(())
}
