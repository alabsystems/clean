// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression-level source locations for kernel type checking errors.
//!
//! When `add_decl` fails, the error message says WHAT went wrong but not WHERE
//! in the term. For large declarations, this makes errors unactionable. This
//! module provides breadcrumb trails through expression trees so errors can
//! point to the specific sub-expression that caused the failure.
//!
//! Part of #3425.

use crate::name::Name;
use std::fmt;

/// A single step in the path from the root expression to a sub-expression.
///
/// Each variant represents a descent into a child of a composite expression.
///
/// # Discriminants are PINNED
///
/// See [`crate::mode::CleanMode`]. The derived `Clone` for this enum is a
/// registered crystal chain: the emitted body switches on the discriminant
/// (`switch %3 [ 0: bb1 … 9: bb10 default: bb11 ]`) and materialises
/// `const enum.181 { k }` in each arm, so the numbers below are the ones the
/// registered module in `eval_ir_path_step.rs` proves about.
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(u8)]
#[non_exhaustive]
pub enum ExprPathStep {
    /// In the function position of App(fn, arg)
    AppFn = 0,
    /// In the argument position of App(fn, arg)
    AppArg = 1,
    /// In the body of a Lambda binder
    LamBody = 2,
    /// In the type annotation of a Lambda binder
    LamType = 3,
    /// In the domain type of a Pi binder
    PiDom = 4,
    /// In the codomain/body of a Pi binder
    PiBody = 5,
    /// In the type annotation of a Let binding
    LetType = 6,
    /// In the value expression of a Let binding
    LetVal = 7,
    /// In the body of a Let binding
    LetBody = 8,
    /// In the inner expression of MData
    MDataExpr = 9,
    /// In the expression being projected
    ProjExpr = 10,
}

impl fmt::Display for ExprPathStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprPathStep::AppFn => write!(f, "function of application"),
            ExprPathStep::AppArg => write!(f, "argument of application"),
            ExprPathStep::LamBody => write!(f, "body of lambda"),
            ExprPathStep::LamType => write!(f, "type annotation of lambda"),
            ExprPathStep::PiDom => write!(f, "domain of Pi"),
            ExprPathStep::PiBody => write!(f, "codomain of Pi"),
            ExprPathStep::LetType => write!(f, "type of let binding"),
            ExprPathStep::LetVal => write!(f, "value of let binding"),
            ExprPathStep::LetBody => write!(f, "body of let binding"),
            ExprPathStep::MDataExpr => write!(f, "inner expression of metadata"),
            ExprPathStep::ProjExpr => write!(f, "expression of projection"),
        }
    }
}

/// Location trail from root to the problematic sub-expression.
///
/// Built up during type checking by pushing steps as the checker descends
/// into sub-expressions. When an error occurs, the current trail is attached
/// to the error, giving the user a breadcrumb path from the declaration root
/// to the exact sub-expression that failed.
///
/// Performance: only materialized when errors occur (errors are rare). The
/// `ExprLocation` stored in `TypeChecker` is a lightweight `Vec<ExprPathStep>`
/// that is pushed/popped during traversal. No allocation on the success path
/// beyond the initial empty Vec.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExprLocation {
    /// The name of the declaration being checked (if known).
    pub decl_name: Option<Name>,
    /// Path steps from root to the error site, outermost first.
    pub steps: Vec<ExprPathStep>,
}

impl ExprLocation {
    /// Create a new empty location with no declaration name.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new location with a declaration name.
    #[must_use]
    pub fn with_decl_name(name: Name) -> Self {
        Self {
            decl_name: Some(name),
            steps: Vec::new(),
        }
    }

    /// Push a step onto the trail (descending into a child).
    pub(crate) fn push(&mut self, step: ExprPathStep) {
        self.steps.push(step);
    }

    /// Pop the last step from the trail (ascending back to parent).
    pub(crate) fn pop(&mut self) {
        self.steps.pop();
    }

    /// Returns true if this location has any path steps.
    #[must_use]
    pub fn has_steps(&self) -> bool {
        !self.steps.is_empty()
    }

    /// Returns a snapshot of the current location for attaching to errors.
    ///
    /// Returns `None` if the location is empty (no steps and no decl name),
    /// avoiding allocation of empty ExprLocations on error paths that don't
    /// have location tracking.
    #[must_use]
    pub(crate) fn snapshot(&self) -> Option<Box<ExprLocation>> {
        if self.decl_name.is_none() && self.steps.is_empty() {
            None
        } else {
            Some(Box::new(self.clone()))
        }
    }
}

impl fmt::Display for ExprLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref name) = self.decl_name {
            write!(f, "in declaration '{name}'")?;
            if !self.steps.is_empty() {
                write!(f, ", ")?;
            }
        }

        if !self.steps.is_empty() {
            write!(f, "at ")?;
            for (i, step) in self.steps.iter().enumerate() {
                if i > 0 {
                    write!(f, " > ")?;
                }
                write!(f, "{step}")?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_location_empty_display() {
        let loc = ExprLocation::new();
        assert_eq!(loc.to_string(), "");
    }

    #[test]
    fn test_expr_location_decl_name_only() {
        let loc = ExprLocation::with_decl_name(Name::from_string("Nat.add"));
        assert_eq!(loc.to_string(), "in declaration 'Nat.add'");
    }

    #[test]
    fn test_expr_location_steps_only() {
        let mut loc = ExprLocation::new();
        loc.push(ExprPathStep::AppFn);
        loc.push(ExprPathStep::LamBody);
        assert_eq!(
            loc.to_string(),
            "at function of application > body of lambda"
        );
    }

    #[test]
    fn test_expr_location_full() {
        let mut loc = ExprLocation::with_decl_name(Name::from_string("Nat.add"));
        loc.push(ExprPathStep::AppArg);
        loc.push(ExprPathStep::PiDom);
        assert_eq!(
            loc.to_string(),
            "in declaration 'Nat.add', at argument of application > domain of Pi"
        );
    }

    #[test]
    fn test_expr_location_push_pop() {
        let mut loc = ExprLocation::new();
        loc.push(ExprPathStep::AppFn);
        loc.push(ExprPathStep::LamBody);
        assert_eq!(loc.steps.len(), 2);
        loc.pop();
        assert_eq!(loc.steps.len(), 1);
        assert_eq!(loc.steps[0], ExprPathStep::AppFn);
    }

    #[test]
    fn test_expr_location_snapshot_empty_is_none() {
        let loc = ExprLocation::new();
        assert!(loc.snapshot().is_none());
    }

    #[test]
    fn test_expr_location_snapshot_with_steps() {
        let mut loc = ExprLocation::new();
        loc.push(ExprPathStep::AppFn);
        let snap = loc.snapshot();
        assert!(snap.is_some());
        let snap = snap.unwrap();
        assert_eq!(snap.steps.len(), 1);
        assert_eq!(snap.steps[0], ExprPathStep::AppFn);
    }

    #[test]
    fn test_expr_location_snapshot_with_decl_name() {
        let loc = ExprLocation::with_decl_name(Name::from_string("test"));
        let snap = loc.snapshot();
        assert!(snap.is_some());
    }

    #[test]
    fn test_expr_path_step_display() {
        assert_eq!(ExprPathStep::AppFn.to_string(), "function of application");
        assert_eq!(ExprPathStep::AppArg.to_string(), "argument of application");
        assert_eq!(ExprPathStep::LamBody.to_string(), "body of lambda");
        assert_eq!(
            ExprPathStep::LamType.to_string(),
            "type annotation of lambda"
        );
        assert_eq!(ExprPathStep::PiDom.to_string(), "domain of Pi");
        assert_eq!(ExprPathStep::PiBody.to_string(), "codomain of Pi");
        assert_eq!(ExprPathStep::LetType.to_string(), "type of let binding");
        assert_eq!(ExprPathStep::LetVal.to_string(), "value of let binding");
        assert_eq!(ExprPathStep::LetBody.to_string(), "body of let binding");
        assert_eq!(
            ExprPathStep::MDataExpr.to_string(),
            "inner expression of metadata"
        );
        assert_eq!(
            ExprPathStep::ProjExpr.to_string(),
            "expression of projection"
        );
    }

    #[test]
    fn test_expr_location_has_steps() {
        let mut loc = ExprLocation::new();
        assert!(!loc.has_steps());
        loc.push(ExprPathStep::AppFn);
        assert!(loc.has_steps());
        loc.pop();
        assert!(!loc.has_steps());
    }

    #[test]
    fn test_expr_location_deep_nesting() {
        let mut loc = ExprLocation::with_decl_name(Name::from_string("deep.fn"));
        loc.push(ExprPathStep::AppFn);
        loc.push(ExprPathStep::AppFn);
        loc.push(ExprPathStep::LamBody);
        loc.push(ExprPathStep::PiDom);
        loc.push(ExprPathStep::AppArg);
        assert_eq!(
            loc.to_string(),
            "in declaration 'deep.fn', at function of application > function of application > body of lambda > domain of Pi > argument of application"
        );
    }
}
