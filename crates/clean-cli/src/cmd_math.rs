// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean math ...` project framework command group.

mod args;
mod artifact;
mod error;
mod features;
mod handlers;
mod output;
mod proof_state;
mod theorem_index;

pub(crate) use args::MathCommands;
pub(crate) use error::MathError;
pub(crate) use features::FEATURES;
pub(crate) use handlers::handle_math_command;
