// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

pub(super) use super::{Interpreter, SourceError, SourceProgram, Value};
pub(super) use clean_rust_sem::expr::Item;
pub(super) use clean_rust_sem::types::ReceiverMode;
pub(super) use clean_rust_sem::RustType;

#[path = "self_type_context/parsing.rs"]
mod parsing;
#[path = "self_type_context/runtime.rs"]
mod runtime;
