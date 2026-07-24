// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::io;
use std::path::PathBuf;

use crate::math_project::MathProjectError;

#[derive(Debug, thiserror::Error)]
pub(crate) enum MathError {
    #[error(transparent)]
    Project(#[from] MathProjectError),
    #[error(transparent)]
    Factory(#[from] crate::factory::FactoryOpsError),
    #[error("failed to serialize math command output: {0}")]
    Serialize(#[from] serde_json::Error),
    #[error("failed to write math command output: {0}")]
    Io(#[from] io::Error),
    #[error("proof artifact error at {path}: {source}")]
    Artifact {
        path: PathBuf,
        source: clean_verify::proof_artifact_v1::ProofArtifactV1Error,
    },
    #[error("math command failed closed: {0}")]
    Failed(String),
}
