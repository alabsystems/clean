// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for source-to-VIR loop cleanup lowering.

#[path = "source_to_vir_loop_cleanup/backedge.rs"]
mod backedge;
#[path = "source_to_vir_loop_cleanup/for_loop.rs"]
mod for_loop;
#[path = "source_to_vir_loop_cleanup/post_loop.rs"]
mod post_loop;
#[path = "source_to_vir_loop_cleanup/support.rs"]
mod support;
