// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for norm computations on vectors and matrices.
//!
//! Provides [`NormKind`] (L1, L2, Linf), [`Vector`], and [`Matrix`] types
//! parameterized over the scalar type. Used in NN verification proofs where
//! concrete norm bounds are needed.

use std::fmt;

/// Which norm to compute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NormKind {
    /// L1 (Manhattan/taxicab): sum of absolute values.
    L1,
    /// L2 (Euclidean): square root of sum of squares.
    L2,
    /// Linf (Chebyshev/max): maximum absolute value.
    Linf,
}

impl fmt::Display for NormKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NormKind::L1 => write!(f, "L1"),
            NormKind::L2 => write!(f, "L2"),
            NormKind::Linf => write!(f, "L\u{221e}"),
        }
    }
}

/// A dense column vector of dimension `n`.
///
/// Stores elements in a contiguous `Vec<T>`. This is a concrete computational
/// type, not a kernel `Expr` — it is used to evaluate norm bounds that feed
/// into proof obligations.
#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T> {
    data: Vec<T>,
}

impl<T> Vector<T> {
    /// Create a vector from raw data. Dimension is `data.len()`.
    pub fn new(data: Vec<T>) -> Self {
        Self { data }
    }

    /// Dimension (number of elements).
    #[must_use]
    pub fn dim(&self) -> usize {
        self.data.len()
    }

    /// Borrow the underlying slice.
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }

    /// Consume and return the underlying storage.
    #[must_use]
    pub fn into_inner(self) -> Vec<T> {
        self.data
    }
}

impl<T> From<Vec<T>> for Vector<T> {
    fn from(v: Vec<T>) -> Self {
        Self::new(v)
    }
}

/// A dense matrix stored in row-major order.
///
/// Dimensions: `rows x cols`. Element `(i, j)` is at index `i * cols + j`.
#[derive(Debug, Clone, PartialEq)]
pub struct Matrix<T> {
    data: Vec<T>,
    rows: usize,
    cols: usize,
}

/// Error constructing a [`Matrix`] when `data.len() != rows * cols`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("matrix dimension mismatch: expected {rows}x{cols}={expected} elements, got {actual}")]
pub struct MatrixDimError {
    rows: usize,
    cols: usize,
    expected: usize,
    actual: usize,
}

impl<T> Matrix<T> {
    /// Create a matrix from row-major data.
    ///
    /// Returns an error if `data.len() != rows * cols`.
    pub fn new(data: Vec<T>, rows: usize, cols: usize) -> Result<Self, MatrixDimError> {
        let expected = rows * cols;
        if data.len() != expected {
            return Err(MatrixDimError {
                rows,
                cols,
                expected,
                actual: data.len(),
            });
        }
        Ok(Self { data, rows, cols })
    }

    /// Number of rows.
    #[must_use]
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Number of columns.
    #[must_use]
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// Borrow the underlying row-major slice.
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }

    /// Get element at `(row, col)`. Panics on out-of-bounds.
    #[must_use]
    pub fn get(&self, row: usize, col: usize) -> &T {
        assert!(
            row < self.rows && col < self.cols,
            "matrix index out of bounds"
        );
        &self.data[row * self.cols + col]
    }

    /// Iterator over row slices. Returns an empty iterator for 0x0 matrices.
    pub fn row_iter(&self) -> impl Iterator<Item = &[T]> {
        // chunks(0) panics, so guard against zero-column matrices.
        if self.cols == 0 {
            // Return an empty chunks iterator by slicing an empty range.
            [].chunks(1)
        } else {
            self.data.chunks(self.cols)
        }
    }
}
