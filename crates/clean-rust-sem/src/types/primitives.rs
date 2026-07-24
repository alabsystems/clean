// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Primitive numeric type definitions: unsigned integers, signed integers,
//! and floating-point types with platform-aware size queries.

use serde::{Deserialize, Serialize};

/// Unsigned integer types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UintType {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

impl UintType {
    /// Size in bytes (assumes 64-bit platform for `usize`)
    pub fn size(&self) -> usize {
        match self {
            UintType::U8 => 1,
            UintType::U16 => 2,
            UintType::U32 => 4,
            UintType::U64 | UintType::Usize => 8,
            UintType::U128 => 16,
        }
    }
}

/// Signed integer types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IntType {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

impl IntType {
    /// Size in bytes (assumes 64-bit platform for `isize`)
    pub fn size(&self) -> usize {
        match self {
            IntType::I8 => 1,
            IntType::I16 => 2,
            IntType::I32 => 4,
            IntType::I64 | IntType::Isize => 8,
            IntType::I128 => 16,
        }
    }
}

/// Floating point types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FloatType {
    F32,
    F64,
}

impl FloatType {
    pub fn size(&self) -> usize {
        match self {
            FloatType::F32 => 4,
            FloatType::F64 => 8,
        }
    }
}
