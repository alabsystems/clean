// Added in Clean (not part of upstream Carcara). See third-party/carcara/DOWNSTREAM.md.
//
//! Scoping of the variables that anchors bind.
//!
//! A step inside an anchor with arguments is a statement about the anchor's variables: every
//! fixed variable `(y S)` is universally quantified, and every assignment `(:= (x S) s)` is a
//! variable constrained by `x = s`. The names of these variables shadow the same names outside
//! the anchor. Upstream Carcara identifies variables by name only, so nothing stopped a
//! statement from crossing the anchor boundary with its names silently reinterpreted:
//!
//! - a step inside the anchor could use a premise proved outside it, where `x` meant the outer
//!   `x`;
//! - the rule that closes the anchor could export a term mentioning the constrained `x`, which the
//!   enclosing proof then reads as its own `x`;
//! - an assigned value could mention a name that the same anchor (or a nested one) binds, so the
//!   context substitution silently moved the value into a different scope.
//!
//! The checks here reject all three. The closing rules check the export condition for their own
//! conclusion (`check_not_exported`).

use super::error::CheckerError;
use super::rules::{Premise, RuleResult};
use crate::ast::{
    pool::{first_free_var, FreeVars, TermPool},
    AnchorArg, ContextStack, Rc, Term,
};
use std::collections::HashSet;

/// The name bound by an anchor argument.
pub fn arg_name(arg: &AnchorArg) -> &str {
    match arg {
        AnchorArg::Variable((name, _)) | AnchorArg::Assign((name, _), _) => name,
    }
}

/// An assignment `(:= (x S) x)`, which constrains `x` to its own value. Such an assignment is
/// equivalent to the fixed variable `(x S)`.
pub fn is_identity_assign(arg: &AnchorArg) -> bool {
    match arg {
        AnchorArg::Assign((name, _), value) => value.as_var() == Some(name.as_str()),
        AnchorArg::Variable(_) => false,
    }
}

/// Modified in Clean: the name of a free variable of `term` that is one of `names`, if there is
/// one.
///
/// This used to collect the names of the free variables into a `HashSet` and take the first one
/// in `names` that iterating it met, an order that changed from run to run; when several are, it
/// is now the one `first_free_var` chooses. It looks up the names in the term's free variables, or
/// the free variables in the names, whichever are fewer, so it costs no more than the set it read.
pub fn free_var_named(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    names: &HashSet<&str>,
) -> Option<String> {
    let free = pool.free_vars(term);
    let candidates = if free.len() <= names.len() {
        free.filter(|var| var.as_var().is_some_and(|name| names.contains(name)))
    } else {
        let mut candidates = FreeVars::default();
        for name in names {
            for var in free.named(name) {
                candidates = candidates.union(&FreeVars::singleton(var));
            }
        }
        candidates
    };
    first_free_var(pool, term, &candidates).map(|var| var.as_var().unwrap().to_owned())
}

fn context_args(context: &ContextStack, index: usize) -> Result<Vec<AnchorArg>, CheckerError> {
    context.args_at(index).ok_or_else(|| {
        CheckerError::Explanation(format!(
            "the context of subproof depth {} is missing",
            index + 1
        ))
    })
}

/// A premise and the step that uses it must read every name the same way. They are nested in the
/// same subproofs except for the anchors between the premise's depth and the level of the step
/// (for the last step of a subproof, the level is the enclosing depth). No name that one of those
/// anchors binds may occur free in the premise.
pub fn check_premise_scoping(
    premises: &[Premise],
    context: &ContextStack,
    pool: &mut dyn TermPool,
    is_end_step: bool,
) -> RuleResult {
    let depth = context.len();
    let level = if is_end_step {
        depth.saturating_sub(1)
    } else {
        depth
    };
    for premise in premises {
        let premise_depth = premise.index.0;
        let crossed = if premise_depth <= level {
            premise_depth + 1..=level
        } else {
            level + 1..=premise_depth
        };
        for anchor_depth in crossed {
            if anchor_depth > depth {
                return Err(CheckerError::Explanation(format!(
                    "premise '{}' is not in scope",
                    premise.id
                )));
            }
            let args = context_args(context, anchor_depth - 1)?;
            if args.is_empty() {
                continue;
            }
            let bound: HashSet<&str> = args.iter().map(arg_name).collect();
            for literal in premise.clause {
                if let Some(name) = free_var_named(pool, literal, &bound) {
                    return Err(CheckerError::Explanation(format!(
                        "premise '{}' mentions '{}', which an anchor between the premise and this \
                         step binds",
                        premise.id, name
                    )));
                }
            }
        }
    }
    Ok(())
}

/// The anchor being closed must give every assigned value a single reading:
///
/// - a value may not mention a name that the same anchor binds at or after the assignment (an
///   identity assignment `(:= (x S) x)` is exempt);
/// - no value assigned by an enclosing anchor may mention a name that this anchor binds, since the
///   cumulative substitution carries that value into this anchor's scope.
pub fn check_anchor_scoping(context: &ContextStack, pool: &mut dyn TermPool) -> RuleResult {
    let depth = context.len();
    if depth == 0 {
        return Ok(());
    }
    let current = context_args(context, depth - 1)?;
    for (i, arg) in current.iter().enumerate() {
        let AnchorArg::Assign((name, _), value) = arg else {
            continue;
        };
        if is_identity_assign(arg) {
            continue;
        }
        let later: HashSet<&str> = current[i..].iter().map(arg_name).collect();
        if let Some(var) = free_var_named(pool, value, &later) {
            return Err(CheckerError::Explanation(format!(
                "the value assigned to '{}' mentions '{}', which the same anchor binds",
                name, var
            )));
        }
    }
    let bound: HashSet<&str> = current.iter().map(arg_name).collect();
    for outer in 0..depth - 1 {
        for arg in context_args(context, outer)? {
            let AnchorArg::Assign((name, _), value) = &arg else {
                continue;
            };
            if is_identity_assign(&arg) {
                continue;
            }
            if let Some(var) = free_var_named(pool, value, &bound) {
                return Err(CheckerError::Explanation(format!(
                    "the value assigned to '{}' by an enclosing anchor mentions '{}', which this \
                     anchor binds",
                    name, var
                )));
            }
        }
    }
    Ok(())
}

/// The term a closing rule exports is read outside the anchor, so it may not mention a variable
/// that the anchor constrains by an assignment (identity assignments constrain nothing).
pub fn check_not_exported(
    pool: &mut dyn TermPool,
    args: &[AnchorArg],
    exported: &Rc<Term>,
) -> RuleResult {
    let free = pool.free_vars(exported);
    for arg in args {
        if let AnchorArg::Assign((name, _), _) = arg {
            if !is_identity_assign(arg) && free.contains_name(name) {
                return Err(CheckerError::Explanation(format!(
                    "'{}' is assigned by the anchor, so it cannot occur free in the exported term \
                     '{}'",
                    name, exported
                )));
            }
        }
    }
    Ok(())
}
