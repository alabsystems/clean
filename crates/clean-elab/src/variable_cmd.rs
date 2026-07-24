// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Variable command elaboration and automatic section variable binding.
//!
//! Lean 4's `variable` command declares variables that persist within a
//! section (or file). When a subsequent `def` or `theorem` references a
//! section variable, the variable is automatically included as a binder
//! parameter in the declaration.
//!
//! # Example
//!
//! ```text
//! section
//! variable {α : Type} [DecidableEq α]
//!
//! def contains (xs : List α) (x : α) : Bool := ...
//! -- elaborates as:  def contains {α : Type} [DecidableEq α] (xs : List α) ...
//! end
//! ```
//!
//! # Architecture
//!
//! [`VariableDecl`] stores declared variable groups.
//! [`auto_bind_variables`] scans a kernel expression for constant references
//! matching section variable names and prepends the appropriate binders.
//!
//! # Lean 4 Reference
//!
//! See `src/Lean/Elab/Command.lean` — `elabVariable` and
//! `includeUsedSectionVars`.

use clean_kernel::expr::visitor::ExprVisitor;
use clean_kernel::expr::{BinderInfo, LevelVec};
use clean_kernel::name::Name;
use clean_kernel::Expr;

/// A group of variable declarations from a single `variable` command.
///
/// A `variable` command can declare multiple names at once:
/// ```text
/// variable {α β : Type} [inst : Add α]
/// ```
/// This produces one `VariableDecl` per binder group.
#[derive(Debug, Clone)]
pub(crate) struct VariableDecl {
    /// The variable names declared in this group.
    pub(crate) names: Vec<Name>,
    /// The type shared by all names in this group.
    pub(crate) type_: Expr,
    /// How the variable binds (explicit, implicit, instance, etc.).
    pub(crate) binder_info: BinderInfo,
}

impl VariableDecl {
    /// Create a new variable declaration for a single name.
    #[must_use]
    pub(crate) fn new(name: Name, type_: Expr, binder_info: BinderInfo) -> Self {
        Self {
            names: vec![name],
            type_,
            binder_info,
        }
    }

    /// Create a new variable declaration for multiple names sharing a type.
    #[must_use]
    pub(crate) fn multi(names: Vec<Name>, type_: Expr, binder_info: BinderInfo) -> Self {
        Self {
            names,
            type_,
            binder_info,
        }
    }
}

/// Visitor that collects all constant names from an expression.
///
/// Uses the kernel's `ExprVisitor` trait to traverse all expression variants
/// (including cubical, ZFC, etc.) without needing to match every variant.
struct ConstNameCollector {
    names: Vec<Name>,
}

impl ExprVisitor for ConstNameCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.names.push(name.clone());
    }
}

/// Collect all constant names referenced in a kernel expression.
///
/// Traverses the expression tree and accumulates `Name` values from
/// `Expr::Const` nodes. This is used to determine which section
/// variables are referenced by a definition body or type.
///
/// # ENSURES
/// - Returns a vector of unique constant names found in the expression
/// - Order is deterministic (depth-first left-to-right traversal)
fn collect_const_names(expr: &Expr) -> Vec<Name> {
    let mut collector = ConstNameCollector { names: Vec::new() };
    collector.visit_expr(expr);
    // Deduplicate while preserving first-occurrence order
    let mut seen = std::collections::HashSet::new();
    collector.names.retain(|n| seen.insert(n.clone()));
    collector.names
}

/// Scan an expression for references to section variables and prepend binders.
///
/// Given a kernel expression and a list of section variable declarations, this
/// function:
/// 1. Collects all constant names referenced in `expr`
/// 2. Identifies which section variables are referenced
/// 3. Prepends Pi binders for each referenced variable (in declaration order)
/// 4. Returns the wrapped expression and the list of bound variable names
///
/// The returned expression has additional outermost binders for each
/// referenced section variable, making the expression self-contained.
///
/// # Example
///
/// ```text
/// // section variable: {α : Type}
/// // expr: List α → Bool
/// auto_bind_variables(expr, &[decl_for_alpha])
/// // => ({α : Type} → List α → Bool, [α])
/// ```
///
/// # REQUIRES
/// - `expr` is a well-formed kernel expression
/// - `section_vars` are valid variable declarations from active sections
///
/// # ENSURES
/// - Returns `(wrapped_expr, bound_names)` where:
///   - `wrapped_expr` has one extra outermost Pi binder per referenced variable
///   - `bound_names` lists the names of variables that were bound (in order)
/// - Variables not referenced in `expr` are not included
/// - Variable binding order matches declaration order in `section_vars`
/// - If no section variables are referenced, returns `expr` unchanged
pub(crate) fn auto_bind_variables(expr: &Expr, section_vars: &[VariableDecl]) -> (Expr, Vec<Name>) {
    let referenced_names = collect_const_names(expr);

    // Collect section variables that are referenced, in declaration order.
    let mut bound_vars: Vec<(Name, Expr, BinderInfo)> = Vec::new();
    let mut bound_names: Vec<Name> = Vec::new();

    for var_decl in section_vars {
        for var_name in &var_decl.names {
            if referenced_names.iter().any(|n| n == var_name) {
                bound_vars.push((
                    var_name.clone(),
                    var_decl.type_.clone(),
                    var_decl.binder_info,
                ));
                bound_names.push(var_name.clone());
            }
        }
    }

    if bound_vars.is_empty() {
        return (expr.clone(), Vec::new());
    }

    // Wrap the expression in Pi binders from outermost (first declared)
    // to innermost (last declared). We fold right-to-left so the first
    // variable becomes the outermost binder.
    let wrapped = bound_vars
        .iter()
        .rev()
        .fold(expr.clone(), |inner, (_name, ty, bi)| {
            Expr::pi(*bi, ty.clone(), inner)
        });

    (wrapped, bound_names)
}

#[cfg(test)]
#[path = "variable_cmd_tests.rs"]
mod tests;
