// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceError, SourceProgram, Value};
use tempfile::NamedTempFile;

#[path = "source_ingestion/basic.rs"]
mod basic;
#[path = "source_ingestion/callable_coercions.rs"]
mod callable_coercions;
#[path = "source_ingestion/const_static.rs"]
mod const_static;
#[path = "source_ingestion/control_flow.rs"]
mod control_flow;
#[path = "source_ingestion/discriminants.rs"]
mod discriminants;
#[path = "source_ingestion/generics.rs"]
mod generics;
#[path = "source_ingestion/item_support.rs"]
mod item_support;
#[path = "source_ingestion/macro_item_skip.rs"]
mod macro_item_skip;
#[path = "source_ingestion/paths.rs"]
mod paths;
#[path = "source_ingestion/prescan.rs"]
mod prescan;
#[path = "source_ingestion/self_type_context.rs"]
mod self_type_context;
#[path = "source_ingestion/stacked_borrows.rs"]
mod stacked_borrows;
#[path = "source_ingestion/trait_behaviors.rs"]
mod trait_behaviors;
#[path = "source_ingestion/trait_bounds.rs"]
mod trait_bounds;
#[path = "source_ingestion/trait_constants.rs"]
mod trait_constants;
#[path = "source_ingestion/trait_definitions.rs"]
mod trait_definitions;
#[path = "source_ingestion/trait_impls.rs"]
mod trait_impls;
#[path = "source_ingestion/turbofish.rs"]
mod turbofish;
