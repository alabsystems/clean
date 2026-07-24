// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compiler Probing Infrastructure
//!
//! Provides composable analysis functions for examining LCNF code.
//! Based on Lean 4's `src/Lean/Compiler/LCNF/Probing.lean` (Henrik Böving).
//!
//! # Overview
//!
//! Probes are composable functions that transform arrays of declarations
//! for analysis. They support:
//! - Extracting specific constructs (let values, join points)
//! - Filtering by code patterns
//! - Counting and statistics
//! - Sorting and limiting results
//!
//! # Example
//!
//! ```text
//! use clean_compiler::probing::*;
//! use clean_compiler::Decl;
//!
//! fn analyze(decls: &[Decl]) {
//!     // Sort declarations by code size
//!     let sorted = sorted_by_size(decls);
//!
//!     // Count unique let values
//!     let let_values = get_let_values(decls);
//!     let counts = count_unique(&let_values);
//!
//!     // Filter by code patterns
//!     let with_jps = filter_by_jp(decls, |jp| jp.params.len() > 2);
//! }
//! ```
//!
//! Part of #1092 - Compiler probing infrastructure.

use crate::code_visitor::CodeVisitor;
use crate::lcnf::{Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use clean_kernel::FVarId;
use std::collections::HashMap;
use std::hash::Hash;

/// A probe transforms a slice of items into a new collection.
///
/// Unlike Lean 4's monadic version, this is a simple function type.
/// Probes can be composed using standard function composition.
pub type Probe<A, B> = fn(&[A]) -> Vec<B>;

// =============================================================================
// Core Combinators
// =============================================================================

/// Map a function over each element.
pub fn map<A, B, F>(items: &[A], f: F) -> Vec<B>
where
    F: Fn(&A) -> B,
{
    items.iter().map(f).collect()
}

/// Filter items by a predicate.
pub fn filter<A, F>(items: &[A], f: F) -> Vec<A>
where
    A: Clone,
    F: Fn(&A) -> bool,
{
    items.iter().filter(|x| f(x)).cloned().collect()
}

/// Sort items by a key.
pub fn sorted_by<A, K, F>(items: &[A], key_fn: F) -> Vec<A>
where
    A: Clone,
    K: Ord,
    F: Fn(&A) -> K,
{
    let mut result: Vec<A> = items.to_vec();
    result.sort_by_key(key_fn);
    result
}

/// Sort items in place (for items that implement Ord).
pub fn sorted<A>(items: &[A]) -> Vec<A>
where
    A: Clone + Ord,
{
    let mut result: Vec<A> = items.to_vec();
    result.sort();
    result
}

/// Take the first n items.
pub fn head<A: Clone>(items: &[A], n: usize) -> Vec<A> {
    items.iter().take(n).cloned().collect()
}

/// Take the last n items.
pub fn tail<A: Clone>(items: &[A], n: usize) -> Vec<A> {
    let len = items.len();
    if n >= len {
        items.to_vec()
    } else {
        items[len - n..].to_vec()
    }
}

/// Count total items.
pub fn count<A>(items: &[A]) -> usize {
    items.len()
}

/// Sum numeric items.
pub fn sum(items: &[usize]) -> usize {
    items.iter().sum()
}

// =============================================================================
// Counting and Statistics
// =============================================================================

/// Count unique occurrences of each item.
pub fn count_unique<A>(items: &[A]) -> Vec<(A, usize)>
where
    A: Clone + Eq + Hash,
{
    let mut counts: HashMap<A, usize> = HashMap::new();
    for item in items {
        *counts.entry(item.clone()).or_insert(0) += 1;
    }
    counts.into_iter().collect()
}

/// Count unique occurrences, sorted by count (ascending).
pub fn count_unique_sorted<A>(items: &[A]) -> Vec<(A, usize)>
where
    A: Clone + Eq + Hash,
{
    let mut counts = count_unique(items);
    counts.sort_by_key(|(_, count)| *count);
    counts
}

// =============================================================================
// Declaration Analysis
// =============================================================================

/// Sort declarations by code size.
pub fn sorted_by_size(decls: &[Decl]) -> Vec<(usize, Decl)> {
    let mut result: Vec<(usize, Decl)> = decls.iter().map(|d| (code_size(d), d.clone())).collect();
    result.sort_by(|(sz1, d1), (sz2, d2)| {
        if sz1 == sz2 {
            d1.name.to_string().cmp(&d2.name.to_string())
        } else {
            sz1.cmp(sz2)
        }
    });
    result
}

/// Compute the size of a declaration's code (number of nodes).
pub fn code_size(decl: &Decl) -> usize {
    match &decl.body {
        DeclValue::Code(code) => code_size_impl(code),
        DeclValue::Extern(_) => 0,
    }
}

struct CodeSizeVisitor;

impl CodeVisitor for CodeSizeVisitor {
    type Result = usize;

    fn combine(&self, a: usize, b: usize) -> usize {
        a + b
    }

    fn visit_let(&mut self, _decl: &LetDecl, body: &Code) -> usize {
        1 + self.visit_code(body)
    }

    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) -> usize {
        1 + self.visit_code(&decl.body) + self.visit_code(body)
    }

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) -> usize {
        1 + self.visit_code(&decl.body) + self.visit_code(body)
    }

    fn visit_cases(&mut self, cases: &crate::lcnf::Cases) -> usize {
        1 + cases
            .alts
            .iter()
            .map(|alt| self.visit_alt(alt))
            .sum::<usize>()
    }

    fn visit_return(&mut self, _fvar: FVarId) -> usize {
        1
    }

    fn visit_jmp(&mut self, _jp: FVarId, _args: &[Arg]) -> usize {
        1
    }

    fn visit_unreachable(&mut self, _ty: &clean_kernel::Expr) -> usize {
        1
    }
}

fn code_size_impl(code: &Code) -> usize {
    CodeSizeVisitor.visit_code(code)
}

/// Extract declaration names.
pub fn decl_names(decls: &[Decl]) -> Vec<String> {
    decls.iter().map(|d| d.name.to_string()).collect()
}

// =============================================================================
// Let Value Extraction
// =============================================================================

/// Extract all let-bound values from declarations.
pub fn get_let_values(decls: &[Decl]) -> Vec<LetValue> {
    let mut collector = LetValueCollector { values: Vec::new() };
    for decl in decls {
        if let DeclValue::Code(code) = &decl.body {
            collector.visit_code(code);
        }
    }
    collector.values
}

struct LetValueCollector {
    values: Vec<LetValue>,
}

impl CodeVisitor for LetValueCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_let(&mut self, decl: &LetDecl, body: &Code) {
        self.values.push(decl.value.clone());
        self.visit_code(body);
    }
}

// =============================================================================
// Join Point Extraction
// =============================================================================

/// Extract all join points from declarations.
pub fn get_join_points(decls: &[Decl]) -> Vec<FunDecl> {
    let mut collector = JoinPointCollector { jps: Vec::new() };
    for decl in decls {
        if let DeclValue::Code(code) = &decl.body {
            collector.visit_code(code);
        }
    }
    collector.jps
}

struct JoinPointCollector {
    jps: Vec<FunDecl>,
}

impl CodeVisitor for JoinPointCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) {
        self.jps.push(decl.clone());
        self.visit_code(&decl.body);
        self.visit_code(body);
    }
}

// =============================================================================
// Filtering by Code Patterns
// =============================================================================

/// Filter declarations that contain a let value matching the predicate.
pub fn filter_by_let<F>(decls: &[Decl], f: F) -> Vec<Decl>
where
    F: Fn(&LetDecl) -> bool,
{
    filter(decls, |decl| {
        if let DeclValue::Code(code) = &decl.body {
            HasLetMatching { pred: &f }.visit_code(code)
        } else {
            false
        }
    })
}

struct HasLetMatching<'a, F> {
    pred: &'a F,
}

impl<F: Fn(&LetDecl) -> bool> CodeVisitor for HasLetMatching<'_, F> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_let(&mut self, decl: &LetDecl, body: &Code) -> bool {
        (self.pred)(decl) || self.visit_code(body)
    }
}

/// Filter declarations that contain a nested function matching the predicate.
pub fn filter_by_fun<F>(decls: &[Decl], f: F) -> Vec<Decl>
where
    F: Fn(&FunDecl) -> bool,
{
    filter(decls, |decl| {
        if let DeclValue::Code(code) = &decl.body {
            HasFunMatching { pred: &f }.visit_code(code)
        } else {
            false
        }
    })
}

struct HasFunMatching<'a, F> {
    pred: &'a F,
}

impl<F: Fn(&FunDecl) -> bool> CodeVisitor for HasFunMatching<'_, F> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) -> bool {
        (self.pred)(decl) || self.visit_code(&decl.body) || self.visit_code(body)
    }
}

/// Filter declarations that contain a join point matching the predicate.
pub fn filter_by_jp<F>(decls: &[Decl], f: F) -> Vec<Decl>
where
    F: Fn(&FunDecl) -> bool,
{
    filter(decls, |decl| {
        if let DeclValue::Code(code) = &decl.body {
            HasJpMatching { pred: &f }.visit_code(code)
        } else {
            false
        }
    })
}

struct HasJpMatching<'a, F> {
    pred: &'a F,
}

impl<F: Fn(&FunDecl) -> bool> CodeVisitor for HasJpMatching<'_, F> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) -> bool {
        (self.pred)(decl) || self.visit_code(&decl.body) || self.visit_code(body)
    }
}

/// Filter declarations that contain a jump matching the predicate.
pub fn filter_by_jmp<F>(decls: &[Decl], f: F) -> Vec<Decl>
where
    F: Fn(FVarId, &[Arg]) -> bool,
{
    filter(decls, |decl| {
        if let DeclValue::Code(code) = &decl.body {
            HasJmpMatching { pred: &f }.visit_code(code)
        } else {
            false
        }
    })
}

struct HasJmpMatching<'a, F> {
    pred: &'a F,
}

impl<F: Fn(FVarId, &[Arg]) -> bool> CodeVisitor for HasJmpMatching<'_, F> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_jmp(&mut self, jp: FVarId, args: &[Arg]) -> bool {
        (self.pred)(jp, args)
    }
}

/// Filter declarations that contain a return matching the predicate.
pub fn filter_by_return<F>(decls: &[Decl], f: F) -> Vec<Decl>
where
    F: Fn(FVarId) -> bool,
{
    filter(decls, |decl| {
        if let DeclValue::Code(code) = &decl.body {
            HasReturnMatching { pred: &f }.visit_code(code)
        } else {
            false
        }
    })
}

struct HasReturnMatching<'a, F> {
    pred: &'a F,
}

impl<F: Fn(FVarId) -> bool> CodeVisitor for HasReturnMatching<'_, F> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_return(&mut self, fvar: FVarId) -> bool {
        (self.pred)(fvar)
    }
}

#[cfg(test)]
mod tests;
