// trust-ir-contract/block: basic-block identifier
//
// Moved out of trust-types' model.rs so the translation-validation data records
// (which key on BlockId) form a self-contained leaf cluster. trust-types
// re-exports `BlockId` so every existing `trust_types::BlockId` use is unchanged.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// Block identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BlockId(pub usize);
