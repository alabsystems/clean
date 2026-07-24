// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for macro invocation support in source ingestion.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceError, SourceProgram, Value};

#[path = "source_macro_ingestion/asm.rs"]
mod asm;
#[path = "source_macro_ingestion/asserts.rs"]
mod asserts;
#[path = "source_macro_ingestion/compile_env.rs"]
mod compile_env;
#[path = "source_macro_ingestion/dbg.rs"]
mod dbg;
#[path = "source_macro_ingestion/format_string.rs"]
mod format_string;
#[path = "source_macro_ingestion/io.rs"]
mod io;
#[path = "source_macro_ingestion/logging.rs"]
mod logging;
#[path = "source_macro_ingestion/matches.rs"]
mod matches;
#[path = "source_macro_ingestion/misc.rs"]
mod misc;
#[path = "source_macro_ingestion/vec.rs"]
mod vec;
