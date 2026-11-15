// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Refuse to compile a structural recursion that reads the fields of an
//! argument it has already generalized away.
//!
//! Measured 2026-09-25 through `clean run` (CLAUDE.md frontend class 54, the
//! audit's `q14_recfirst`), against pinned Lean v4.30.0-rc2:
//!
//! ```text
//! def recFirst : P2 → Nat → Nat
//!   | ⟨x, _⟩, 0 => x
//!   | ⟨x, y⟩, n + 1 => recFirst ⟨y, x⟩ n
//! #eval recFirst ⟨3, 4⟩ 1   -- Lean: 4.  clean run: 3, exit 0.
//! ```
//!
//! The elaborated value has this shape:
//!
//! ```text
//! fun p n => P2.casesOn p (fun x y =>
//!   Nat.rec (motive := fun _ => P2 → Nat)
//!     (fun p' => x)                        -- reads the OUTER x
//!     (fun k ih p' => ih ⟨y, x⟩)           -- reads the OUTER x, y
//!     n p)
//! ```
//!
//! The recursion generalizes the structure argument (its motive is
//! `P2 → Nat`, and the IH is applied to the new value `⟨y, x⟩`), but the split
//! of that argument into `x`, `y` happened OUTSIDE the recursor, so every level
//! reads the fields of the ORIGINAL argument and the generalized value is
//! dropped. Lean splits the argument inside each recursion step.
//!
//! CLOSED IN THE ELABORATOR (class 54): 0ffcbd885 lowers the decreasing column
//! outermost and refuses a minor that reads an outer split
//! (`check_recursive_minors_closed`), and 5809a76e8 hoists the rest into the
//! match's arms, so `recFirst` now elaborates with the split inside the
//! recursion and computes Lean's value (`rfl` value pins in
//! `crates/clean-elab/tests/recursion_scope_and_pattern_names.rs`; printed
//! bytes in the native battery's `q14_recfirst`). This audit stays as the
//! native path's second line: no elaborated value reaches it today, and its
//! refusal is tested on the old value itself.
//!
//! The refused shape, stated over the kernel value: an eliminator application
//! (a `<I>.casesOn`, or a `<I>.rec` over a non-recursive inductive) whose
//! major premise is a bound variable `v`, inside one of whose minor premises a
//! recursor application is OVER-applied to that same `v` (the generalized
//! argument), while that recursor's minor premises read a field the outer
//! split bound. A recursion that splits its generalized argument inside itself
//! never has this shape; one that merely passes an unsplit argument along
//! does not either.

use clean_kernel::{Environment, Expr, ExprKind, Name, RecursorArgOrder};

use crate::native_eager_io::spine;

/// Why the native path refuses a recursion.
#[derive(Debug, thiserror::Error)]
#[error(
    "native build refuses `{decl}`: its structural recursion generalizes an argument whose \
     fields were split OUTSIDE the recursor, so every recursive level reads the original \
     argument's fields and the value passed to the recursive call is dropped. Clean's \
     elaborator once produced this shape for a recursion Lean evaluates differently \
     (`recFirst ⟨3, 4⟩ 1` is 4 in Lean), so the native path refuses it wherever it appears. \
     Split that argument inside the recursion, or make it a fixed parameter \
     (native-recursion-split)."
)]
pub(crate) struct RecursionSplitRefusal {
    /// The declaration being audited.
    decl: String,
}

/// Audit one declaration's value.
pub(crate) fn check_recursion_split(
    env: &Environment,
    decl: &Name,
    value: &Expr,
) -> Result<(), RecursionSplitRefusal> {
    let mut walker = Walker {
        env,
        splits: Vec::new(),
    };
    if walker.walk(value, 0) {
        Err(RecursionSplitRefusal {
            decl: decl.to_string(),
        })
    } else {
        Ok(())
    }
}

/// An active split: the binder LEVEL (absolute de Bruijn level) of the
/// eliminated variable, and the levels of the field binders its minor bound.
struct Split {
    major: u32,
    fields: Vec<u32>,
}

struct Walker<'a> {
    env: &'a Environment,
    splits: Vec<Split>,
}

/// The absolute binder level a `BVar(idx)` at binder depth `depth` names.
fn level_of(idx: u32, depth: u32) -> Option<u32> {
    depth.checked_sub(idx + 1)
}

/// Does `e` (sitting at binder depth `depth`) mention the binder at `level`?
fn mentions_level(e: &Expr, depth: u32, level: u32) -> bool {
    // Loose variables of `e` are BVar(0..range); the binder at `level` is
    // BVar(depth - 1 - level). Nothing reaches it unless the range covers it.
    let Some(idx) = level_of(level, depth) else {
        return false;
    };
    if e.loose_bvar_range() <= idx {
        return false;
    }
    match e.kind() {
        ExprKind::BVar(i) => *i == idx,
        ExprKind::App(f, a) => mentions_level(f, depth, level) || mentions_level(a, depth, level),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_level(ty, depth, level) || mentions_level(body, depth + 1, level)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_level(ty, depth, level)
                || mentions_level(val, depth, level)
                || mentions_level(body, depth + 1, level)
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => {
            mentions_level(inner, depth, level)
        }
        // Forms this walker does not model count as a mention: over-refusal
        // is the safe direction for an audit.
        _ => true,
    }
}

impl Walker<'_> {
    /// Walk `e` at binder depth `depth`; `true` means the refused shape was
    /// found.
    fn walk(&mut self, e: &Expr, depth: u32) -> bool {
        match e.kind() {
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.walk(ty, depth) || self.walk(body, depth + 1)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                self.walk(ty, depth) || self.walk(val, depth) || self.walk(body, depth + 1)
            }
            ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => self.walk(inner, depth),
            ExprKind::App(..) => self.walk_app(e, depth),
            _ => false,
        }
    }

    fn walk_app(&mut self, e: &Expr, depth: u32) -> bool {
        let (head, args) = spine(e);
        if let ExprKind::Const(name, _) = head.kind() {
            if self.generalizes_a_split_variable(name, &args, depth) {
                return true;
            }
            if let Some((major_idx, minors)) = self.split_layout(name, args.len()) {
                if let ExprKind::BVar(i) = args[major_idx].strip_mdata().kind() {
                    if let Some(major) = level_of(*i, depth) {
                        return self.walk_split(&args, major, &minors, depth);
                    }
                }
            }
        }
        self.walk(head, depth) || args.iter().any(|a| self.walk(a, depth))
    }

    /// Walk an eliminator whose major is the variable at `major`, recording
    /// each minor's field binders as a split of that variable while its body
    /// is walked.
    fn walk_split(
        &mut self,
        args: &[&Expr],
        major: u32,
        minors: &[(usize, usize)],
        depth: u32,
    ) -> bool {
        for (i, arg) in args.iter().enumerate() {
            let Some(&(_, binders)) = minors.iter().find(|(idx, _)| *idx == i) else {
                if self.walk(arg, depth) {
                    return true;
                }
                continue;
            };
            // Peel the minor's field binders.
            let mut body = arg.strip_mdata();
            let mut fields = Vec::new();
            let mut d = depth;
            for _ in 0..binders {
                let ExprKind::Lam(_, ty, inner) = body.kind() else {
                    break;
                };
                if self.walk(ty, d) {
                    return true;
                }
                fields.push(d);
                d += 1;
                body = inner.as_ref().strip_mdata();
            }
            self.splits.push(Split { major, fields });
            let found = self.walk(body, d);
            self.splits.pop();
            if found {
                return true;
            }
        }
        false
    }

    /// Is `name args` a recursor application over-applied to a variable an
    /// enclosing split eliminated, whose minors read that split's fields?
    fn generalizes_a_split_variable(&self, name: &Name, args: &[&Expr], depth: u32) -> bool {
        let Some(rec) = self.env.get_recursor(name) else {
            return false;
        };
        if rec.arg_order != RecursorArgOrder::MajorAfterMinors {
            return false;
        }
        let first_minor = (rec.num_params + rec.num_motives) as usize;
        let arity = first_minor + (rec.num_minors + rec.num_indices) as usize + 1;
        if args.len() <= arity {
            return false;
        }
        let minors = &args[first_minor..first_minor + rec.num_minors as usize];
        args[arity..].iter().any(|extra| {
            let ExprKind::BVar(i) = extra.strip_mdata().kind() else {
                return false;
            };
            let Some(level) = level_of(*i, depth) else {
                return false;
            };
            self.splits
                .iter()
                .filter(|split| split.major == level)
                .any(|split| {
                    split
                        .fields
                        .iter()
                        .any(|&field| minors.iter().any(|m| mentions_level(m, depth, field)))
                })
        })
    }

    /// For a `<I>.casesOn` application, or a `<I>.rec` over a NON-recursive
    /// inductive, of exactly its arity: the major's argument index and each
    /// minor's (argument index, field-binder count).
    fn split_layout(&self, name: &Name, nargs: usize) -> Option<(usize, Vec<(usize, usize)>)> {
        let full = name.to_string();
        if let Some(ind_name) = full.strip_suffix(".casesOn") {
            let ind = self.env.get_inductive(&Name::from_string(ind_name))?;
            let (np, ni) = (ind.num_params as usize, ind.num_indices as usize);
            let major = np + 1 + ni;
            if nargs != major + 1 + ind.constructor_names.len() {
                return None;
            }
            let minors = ind
                .constructor_names
                .iter()
                .enumerate()
                .map(|(k, c)| {
                    let fields = self.env.get_constructor(c).map_or(0, |cv| cv.num_fields);
                    (major + 1 + k, fields as usize)
                })
                .collect();
            return Some((major, minors));
        }
        let rec = self.env.get_recursor(name)?;
        if rec.num_motives != 1
            || rec.arg_order != RecursorArgOrder::MajorAfterMinors
            || rec
                .rules
                .iter()
                .any(|rule| rule.recursive_fields.iter().any(|r| *r))
        {
            return None;
        }
        let first_minor = (rec.num_params + 1) as usize;
        let major = first_minor + (rec.num_minors + rec.num_indices) as usize;
        if nargs != major + 1 {
            return None;
        }
        let minors = rec
            .rules
            .iter()
            .enumerate()
            .map(|(k, rule)| (first_minor + k, rule.num_fields as usize))
            .collect();
        Some((major, minors))
    }
}

#[cfg(test)]
#[path = "native_rec_split_audit_tests.rs"]
mod tests;
