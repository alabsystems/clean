// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise Selection for Automated Theorem Proving
//!
//! Implements two complementary selection strategies from Isabelle:
//!
//! ## MePo (Meng-Paulson) - Symbol-Based Relevance
//! Ranks premises by symbol overlap with the goal. Rare symbols get higher weight.
//! Fast, interpretable, and effective for goals with distinctive constants.
//!
//! ## MaSh (Machine-learning for Sledgehammer) - Feature-Based Learning
//! Extracts features from terms and uses k-NN / Naive Bayes to predict
//! which premises are likely useful based on past proof attempts.
//!
//! # References
//! - "Lightweight Relevance Filtering for Machine-Generated Resolution Problems" (Meng & Paulson, 2009)
//! - "MaSh: Machine Learning for Sledgehammer" (Kühlwein et al., 2013)

mod database;
mod feature;
mod selector;

pub use database::*;
pub(crate) use feature::*;
pub use selector::*;

// Re-import for test visibility (private items visible to descendant modules)
#[cfg(test)]
use selector::cmp_score_desc_then_id;

#[cfg(test)]
mod tests;
