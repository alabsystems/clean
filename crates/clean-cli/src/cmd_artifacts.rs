// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean artifacts ...` command group — generic release-artifact logistics
//! (v0 of the artifact system, `designs/2026-06-09-master-design-v2.md` §5.6).
//!
//! Verbs: `list` (release/asset discovery), `get` (download with mandatory
//! fail-closed blake3 manifest verification), `verify` (re-verify a directory
//! against its manifest), `extract` (unpack an archive and verify the
//! extracted tree). The library layer lives in `clean_mathverse::artifacts`;
//! this module owns the clap surface, the publish-after-verify discipline,
//! and the JSON reports.

mod args;
mod features;
mod handlers;

pub(crate) use args::ArtifactsCommands;
pub(crate) use features::FEATURES;
pub(crate) use handlers::handle_artifacts_command;
