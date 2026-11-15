// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which parameter of a whole-body pattern match does a recursive definition
//! descend on — read off the rows, not guessed from spellings.
//!
//! Lean 4.8.0 elaborates structural recursion by TRYING each parameter in
//! turn (`Lean.Elab.Structural.findRecArg`, left to right past the fixed
//! prefix) and keeping the first one for which every recursive call passes a
//! structurally smaller argument. Clean's recursor lowering commits to ONE
//! position before elaborating: the name heuristic
//! (`detect::find_decreasing_arg`) picks the first position where every call
//! passes a variable spelled differently from the parameter. That heuristic
//! is blind to WHERE the variable comes from. `match c, b with | a+1, b+1 =>
//! f 4 c a | _, _ => 109` passes `c` at position 1 (spelled unlike `b`), so
//! position 1 was chosen, no call passes a child of `b` there, and the
//! definition was refused as recursion outside the fragment — although every
//! call passes `a`, the immediate predecessor of `c`, at position 2, which is
//! exactly the argument Lean 4.8.0 recurses on.
//!
//! This module answers the question the heuristic approximates, for the rows
//! of a whole-body match (a multi-discriminant `match x, y with` over the
//! definition's own parameters, or the arms of an equation-form definition):
//! does every recursive call pass, at position `p`, a variable that the row's
//! own pattern for `p`'s column binds at a RECURSIVE field of the matched
//! constructor — the only arguments the recursor lowering holds an induction
//! hypothesis for?
//!
//! The answer is ROUTING ONLY. It decides which column the equation
//! normalizers put outermost and which parameter `setup_recursion` recurses
//! on; it never admits a definition by itself. The lowering still resolves
//! every self-call against a real induction hypothesis (and fails loud when
//! there is none), the kernel re-checks the term, and
//! `ElabCtx::check_structural_recursion_sites` refuses any lowering whose
//! recursor does not compute the whole definition.

use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::{SurfaceExpr, SurfaceName, SurfacePattern};

use super::detect::{recursive_calls_in, scoped_recursive_calls, ScopedArg};
use super::pattern_binds_name;

/// The verdict for one candidate position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Descent {
    /// Every recursive call passes, at this position, a variable bound at a
    /// recursive field of the constructor its row matches in this column —
    /// the recursor lowering holds an induction hypothesis for each of them.
    Valid,
    /// Some call certainly passes something else there: a variable that is
    /// not such a field (a parameter, a global, a variable bound by another
    /// column, the whole column value, a non-recursive or deeper field), a
    /// term that is not a variable, or no argument; or the call has a named
    /// argument. Recursing on this position cannot resolve that call.
    Invalid,
    /// Neither can be shown from the surface (a parenthesized variable, a
    /// variable a binder around the call rebinds, an `as`/`or` pattern, a
    /// constructor that does not resolve, a body form whose binders are not
    /// tracked, no call at all).
    Unknown,
}

/// One row of a whole-body match: its pattern per column and its body.
pub(crate) struct DescentRow<'a> {
    pub(crate) pats: &'a [SurfacePattern],
    pub(crate) body: &'a SurfaceExpr,
}

/// Classify recursion on the parameter that matrix column `column` scrutinizes
/// and that recursive calls pass at argument position `call_pos`.
///
/// `column_inductive` is the inductive the column's declared domain names
/// (`Nat`, `List` for `List Nat`), when it can be read off the surface.
pub(crate) fn classify_descent(
    env: &Environment,
    func_name: &SurfaceName,
    rows: &[DescentRow<'_>],
    column: usize,
    column_inductive: Option<&Name>,
    call_pos: usize,
) -> Descent {
    let short = func_name.last_component();
    let mut saw_call = false;
    let mut unknown = false;
    for row in rows {
        // A row whose pattern rebinds the function's own name hides every
        // call below it; the detector would not count them either.
        if row.pats.iter().any(|p| pattern_binds_name(p, &short)) {
            return Descent::Unknown;
        }
        // The calls with their enclosing binders; the count must agree with
        // the detector's, so no call the lowering will see goes unjudged.
        let Some(calls) = scoped_recursive_calls(func_name, row.body) else {
            return Descent::Unknown;
        };
        if calls.len() != recursive_calls_in(func_name, row.body).len() {
            return Descent::Unknown;
        }
        if calls.is_empty() {
            continue;
        }
        saw_call = true;
        let Some(pat) = row.pats.get(column) else {
            return Descent::Unknown;
        };
        let children = direct_recursive_children(env, pat, column_inductive);
        for scoped in &calls {
            // Named recursive arguments are not lowered. A direct field or
            // a function field applied to indices must resolve to that field's
            // actual induction hypothesis (`try_elab_recursive_call`).
            if scoped.named {
                return Descent::Invalid;
            }
            match scoped.args.get(call_pos) {
                None | Some(ScopedArg::NonVar) => return Descent::Invalid,
                Some(ScopedArg::ParenVar(_)) => unknown = true,
                Some(ScopedArg::Var(v) | ScopedArg::AppliedField(v)) => {
                    // A binder between the row's pattern and the call may
                    // rebind the name.
                    if scoped.enclosing.contains(v) {
                        unknown = true;
                        continue;
                    }
                    match &children {
                        Some(children) if children.contains(v) => {}
                        Some(_) => return Descent::Invalid,
                        None => unknown = true,
                    }
                }
            }
        }
    }
    if !saw_call || unknown {
        Descent::Unknown
    } else {
        Descent::Valid
    }
}

/// Choose the decreasing position among `candidates` (call-argument
/// positions, in parameter order).
///
/// `current` is the position the pre-existing routing chose. It is kept
/// unless it is certainly [`Descent::Invalid`] AND some candidate is
/// certainly [`Descent::Valid`]; then the FIRST valid candidate is chosen, as
/// Lean 4.8.0 keeps the first parameter structural recursion succeeds on.
/// Every definition the pre-existing routing lowered therefore keeps its
/// lowering: only a position whose recursion could not resolve some call is
/// ever replaced.
pub(crate) fn choose_decreasing_position(
    current: Option<usize>,
    candidates: &[usize],
    classify: impl Fn(usize) -> Descent,
) -> Option<usize> {
    if let Some(pos) = current {
        if classify(pos) != Descent::Invalid {
            return current;
        }
    }
    candidates
        .iter()
        .copied()
        .find(|&pos| classify(pos) == Descent::Valid)
        .or(current)
}

/// The variables a column pattern binds at a RECURSIVE field of the
/// constructor it matches: `n` in `n + 1` / `Nat.succ n`, `xs` in `x :: xs`.
/// `Some(vec![])` when the pattern binds none (a wildcard, a whole-value
/// variable, a literal, a deeper `n + 2`); `None` when the surface cannot say
/// (an unresolved constructor, an `as`/`or`/inaccessible pattern).
fn direct_recursive_children(
    env: &Environment,
    pat: &SurfacePattern,
    column_inductive: Option<&Name>,
) -> Option<Vec<SurfaceName>> {
    match pat {
        SurfacePattern::Wildcard
        | SurfacePattern::Ellipsis
        | SurfacePattern::Var(_)
        | SurfacePattern::Lit(_) => Some(Vec::new()),
        SurfacePattern::NumeralAdd(inner, k) => {
            let nat = Name::from_string("Nat");
            if column_inductive.is_some_and(|ind| *ind != nat) {
                return None;
            }
            match (inner.as_ref(), *k) {
                // `v + 1` is `Nat.succ v`: `v` is the immediate predecessor.
                (SurfacePattern::Var(v), 1) => Some(vec![v.clone()]),
                // `v + 0` is `v` itself; `v + k` (k ≥ 2) binds a deeper
                // predecessor. Neither is a recursive field.
                (SurfacePattern::Var(_), _) => Some(Vec::new()),
                (SurfacePattern::Wildcard, _) => Some(Vec::new()),
                _ => None,
            }
        }
        SurfacePattern::Ctor(name, subs) => {
            let ctor = resolve_ctor(env, name, column_inductive)?;
            let info = env.get_constructor(&ctor)?;
            if column_inductive.is_some_and(|ind| *ind != info.inductive_name) {
                return None;
            }
            let flags = recursive_field_flags(env, &info.inductive_name, &ctor)?;
            if subs.len() != flags.len() {
                return None;
            }
            let mut out = Vec::new();
            for (sub, recursive) in subs.iter().zip(flags) {
                match sub {
                    SurfacePattern::Var(v) if recursive => out.push(v.clone()),
                    SurfacePattern::As(..) | SurfacePattern::Or(..) if recursive => return None,
                    _ => {}
                }
            }
            Some(out)
        }
        SurfacePattern::As(..)
        | SurfacePattern::Or(..)
        | SurfacePattern::StructInst { .. }
        | SurfacePattern::Inaccessible(_)
        | SurfacePattern::QPattern(_) => None,
    }
}

/// The kernel constructor a pattern head names: an exact constructor name,
/// else `I.<last>` for the column's inductive `I` (relative `.c` / bare `c`).
fn resolve_ctor(
    env: &Environment,
    name: &SurfaceName,
    column_inductive: Option<&Name>,
) -> Option<Name> {
    let raw = name.name();
    if !name.is_relative_constructor() && env.get_constructor(raw).is_some() {
        return Some(raw.clone());
    }
    let last = raw.last_component()?;
    let qualified = column_inductive?.clone().str(&last);
    env.get_constructor(&qualified)
        .is_some()
        .then_some(qualified)
}

/// Which fields of `ctor` the inductive's recursor gives an induction
/// hypothesis for — the recursor's own rule, so this agrees with the lowering.
fn recursive_field_flags(env: &Environment, inductive: &Name, ctor: &Name) -> Option<Vec<bool>> {
    let rec = env.get_recursor(&inductive.clone().str("rec"))?;
    rec.rules
        .iter()
        .find(|rule| &rule.constructor_name == ctor)
        .map(|rule| rule.recursive_fields.clone())
}
