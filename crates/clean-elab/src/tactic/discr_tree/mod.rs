// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod key;
mod path;
mod query;
mod trie;

#[cfg(test)]
mod tests;

#[cfg(test)]
pub(crate) use key::DiscrKey;
pub(crate) use key::IndexMode;
pub(crate) use path::{mk_path, query_path_is_too_generic};
pub(crate) use query::DiscrTree;
