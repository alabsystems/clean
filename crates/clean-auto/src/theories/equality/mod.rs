// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality theory solver using E-graphs

mod theory;

pub(crate) use theory::EqualityTheory;
#[cfg(test)]
pub(crate) use theory::ExplanationStats;

#[cfg(test)]
mod tests;
