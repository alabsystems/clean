// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! External backend invocation and requested diagnostic capture.

use std::path::{Path, PathBuf};
use std::process::Command;

use super::{serialize_tmbc, LaneError, Module, ScratchRetention, TrustCg, LOWERED};

pub(super) fn compile_object_with_cli(
    tcg: &TrustCg,
    target: &str,
    module: &Module,
    dir: &Path,
) -> Result<PathBuf, LaneError> {
    compile_object_with_cli_recording(tcg, target, module, dir, None).map(|(path, _)| path)
}

pub(super) fn compile_object_with_cli_recording(
    tcg: &TrustCg,
    target: &str,
    module: &Module,
    dir: &Path,
    observation: Option<&crate::primitive_uses::NativeRecorder>,
) -> Result<(PathBuf, Option<crate::primitive_uses::NativeArtifactId>), LaneError> {
    let tmbc = dir.join("module.tmbc");
    let object = dir.join("module.o");
    let bytes = serialize_tmbc(module).map_err(|e| LaneError::core("serialize")(e.into()))?;
    std::fs::write(&tmbc, &bytes)
        .map_err(|e| LaneError::TrustCg(format!("could not write {}: {e}", tmbc.display())))?;
    let args = [
        "-c",
        "--target",
        target,
        "--recognize-authority",
        LOWERED,
        "--refuse-unlicensed",
        "-o",
    ];
    if tcg.retention == ScratchRetention::Keep {
        let command = serde_json::json!({
            "schema": "clean-run-trustcg-command/v1",
            "program": tcg.path,
            "version": tcg.version,
            "arguments": args,
            "object": object,
            "input": tmbc,
            "claim": "diagnostic invocation only; no binary claim"
        });
        let bytes = serde_json::to_vec_pretty(&command)
            .map_err(|e| LaneError::TrustCg(format!("could not render diagnostic command: {e}")))?;
        retain(dir, "trust-cg-command.json", &bytes)?;
    }
    let mut command = Command::new(&tcg.path);
    command.args(args).arg(&object).arg(&tmbc);
    let invocation =
        observation.and_then(|observer| observer.before_backend(&command, &tmbc, bytes));
    let out = command
        .output()
        .map_err(|e| LaneError::TrustCg(format!("could not run {}: {e}", tcg.path.display())))?;
    let object_artifact =
        observation.and_then(|observer| observer.after_backend(invocation.as_ref(), &object, &out));
    let diagnostics = if tcg.retention == ScratchRetention::Keep {
        retain(dir, "trust-cg.stdout", &out.stdout)
            .and_then(|()| retain(dir, "trust-cg.stderr", &out.stderr))
            .and_then(|()| {
                retain(
                    dir,
                    "trust-cg-status.json",
                    serde_json::json!({"success":out.status.success(),"exit_code":out.status.code()})
                        .to_string()
                        .as_bytes(),
                )
            })
    } else {
        Ok(())
    };
    if !out.status.success() {
        let cause = stderr_head(&String::from_utf8_lossy(&out.stderr), out.status.code());
        return Err(LaneError::TrustCg(match diagnostics {
            Ok(()) => cause,
            Err(error) => format!("{cause}; diagnostic retention also failed: {error}"),
        }));
    }
    diagnostics?;
    if !object.is_file() {
        return Err(LaneError::TrustCg(
            "trust-cg exited 0 but wrote no object".to_owned(),
        ));
    }
    Ok((object, object_artifact))
}

fn retain(dir: &Path, name: &str, bytes: &[u8]) -> Result<(), LaneError> {
    let path = dir.join(name);
    std::fs::write(&path, bytes)
        .map_err(|e| LaneError::TrustCg(format!("could not retain {}: {e}", path.display())))
}

/// Preserve the tool's error lines and exit status for the original refusal.
pub(crate) fn stderr_head(stderr: &str, code: Option<i32>) -> String {
    let errors: Vec<&str> = stderr
        .lines()
        .map(str::trim)
        .filter(|l| l.to_ascii_lowercase().contains("error"))
        .take(3)
        .collect();
    let head = if errors.is_empty() {
        stderr
            .lines()
            .map(str::trim)
            .rfind(|l| !l.is_empty())
            .unwrap_or("<empty stderr>")
            .to_owned()
    } else {
        errors.join(" | ")
    };
    match code {
        Some(code) => format!("{head} (exit {code})"),
        None => format!("{head} (killed by a signal)"),
    }
}
