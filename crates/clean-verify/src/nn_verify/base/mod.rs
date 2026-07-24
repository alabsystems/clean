// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Foundation types for NN verification proofs.
//!
//! Provides `Vec`, `Mat`, `IntervalBounds`, and `Fin.sum` lemmas that all
//! subsequent NN verification proofs depend on.

pub mod fin_sum;
pub mod interval;
pub mod mat;
pub mod norms;
pub mod vec;

pub use interval::{IntervalBounds, IntervalContainment};
pub use mat::Mat;
pub use norms::{NormError, NormKind};
pub use vec::Vec;
