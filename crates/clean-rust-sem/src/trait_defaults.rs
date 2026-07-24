// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Default trait method body storage
//!
//! When a trait method provides a default implementation, the body is stored
//! in [`DefaultMethodBody`] so it can be used as a fallback when an impl block
//! doesn't override it.

use crate::expr::Expr;
use crate::types::RustType;
use serde::{Deserialize, Serialize};

/// Default method body for a trait method with a provided implementation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefaultMethodBody {
    /// Parameter names and types (including self)
    pub params: Vec<(String, RustType)>,
    /// Return type
    pub ret_ty: RustType,
    /// Body expression
    pub body: Expr,
}
