// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared owned frontend/import capture; native readiness is checked separately.

use std::path::Path;
use std::process::Command;
use std::sync::Arc;

use clean_compiler::runtime_lcnf::RuntimeSourceRecord;
use clean_kernel::Environment;
use clean_olean::ImportWorld;

use super::{snapshot, Custody, ExternalLeanError, ExternalLeanInput, ExternalLeanProgram};

impl ExternalLeanProgram {
    pub(super) fn capture(input: ExternalLeanInput<'_>) -> Result<Self, ExternalLeanError> {
        let decision = clean_olean::source_world_for_file(input.file, Some(input.world))
            .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let Ok(ImportWorld::Explicit { lib, .. }) = decision.imports() else {
            return Err(ExternalLeanError::Input(
                "explicit Lean world required".into(),
            ));
        };
        let lean = lib
            .parent()
            .and_then(Path::parent)
            .ok_or_else(|| ExternalLeanError::Input("invalid installed Lean library path".into()))?
            .join("bin/lean");
        let snapshot = tempfile::tempdir()?;
        let root = snapshot.path();
        let mut files = snapshot::Files::default();
        // Additional observation only: compatibility capture keeps its existing
        // canonicalization/error behavior below.
        let original_before =
            super::primary_artifact::PrimaryArtifactCapture::canonical_observation(input.file);
        files.observe(input.file)?;
        let source_path = snapshot::module_path(root, input.module, "lean")?;
        if let Some(parent) = source_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        files.copy(input.file, &source_path)?;
        let sdk_before =
            super::primary_artifact::PrimaryArtifactCapture::canonical_observation(&source_path);
        let source = std::fs::read_to_string(&source_path)?;
        files.observe(&lean)?;
        // Shared libraries are part of the frontend TCB, never proof evidence.
        snapshot::observe_frontend_libraries(lib, &mut files)?;
        files.observe(&source_path)?;
        let mut search_paths = input.search_paths.to_vec();
        search_paths.push(lib.clone());
        let mut base = Environment::for_lean_replay();
        clean_olean::declare_environment_world(&mut base, input.world.tag())
            .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let mut world_scope = clean_olean::LeanWorldScope::of_environment(&base);
        snapshot::capture_imports(
            input.imports,
            &search_paths,
            root,
            &mut files,
            &mut world_scope,
        )?;
        let output_path = snapshot::module_path(root, input.module, "olean")?;
        if output_path.exists() {
            return Err(ExternalLeanError::Input(
                "source module redeclares a captured import".into(),
            ));
        }
        let output = Command::new(&lean)
            .current_dir(root)
            // Ambient Lean/sysroot/plugin/loader variables must not redirect
            // this explicitly selected frontend into another installation.
            .env_clear()
            .env("LEAN_PATH", root)
            .arg("--root")
            .arg(root)
            .arg("-o")
            .arg(&output_path)
            .arg(&source_path)
            .output()?;
        files.check()?;
        if !output.status.success() {
            return Err(ExternalLeanError::Elaboration(format!(
                "{}: {}{}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )));
        }
        snapshot::observe_output(&output_path, &mut files, &mut world_scope)?;
        let mut env = base.clone();
        clean_olean::load_typed_module_with_deps_bounded(
            &mut env,
            input.module,
            &[root.to_path_buf()],
            4096,
        )
        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        files.check()?;
        let mut artifact = clean_olean::read_artifact(
            &format!("{:?}", input.module),
            &output_path,
            clean_olean::ArtifactDepth::Records,
        )
        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let original_after = std::fs::canonicalize(input.file)?;
        let sources = vec![RuntimeSourceRecord {
            module: input.module.to_string(),
            path: original_after.display().to_string(),
            source,
        }];
        let parts =
            super::primary_artifact::PrimaryArtifactCapture::recorded_parts(&output_path, &files);
        let sdk_after =
            super::primary_artifact::PrimaryArtifactCapture::canonical_observation(&source_path);
        let original_end =
            super::primary_artifact::PrimaryArtifactCapture::canonical_observation(input.file);
        // Membership and source observations were read after loading. Close
        // that entire read interval, not only the loader's earlier reads.
        files.check()?;
        let inputs = files.into_observations();
        let module_names = std::mem::take(&mut artifact.names).into_iter().collect();
        let primary_artifact = super::primary_artifact::PrimaryArtifactCapture::bind(
            input.module,
            artifact,
            input.file,
            original_before,
            original_after,
            original_end,
            &source_path,
            sdk_before,
            sdk_after,
            &inputs,
            parts,
        );
        let env = Arc::new(env);
        let base = Arc::new(base);
        Ok(Self {
            env: Arc::clone(&env),
            base: Arc::clone(&base),
            module_names,
            usage: super::inspection::Usage::Inspection,
            custody: Arc::new(Custody {
                world: input.world,
                source: env,
                base,
                sources,
                global_observation: Default::default(),
                inputs,
                primary_artifact,
                _snapshot: snapshot,
            }),
        })
    }
}
