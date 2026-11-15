// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `#print axioms c`: Lean 4.8.0's axiom census and the message it prints.
//!
//! Ground truth is the pinned toolchain's `Lean/Elab/Print.lean`
//! (`CollectAxioms.collect`, `printAxiomsOf`) and `Lean/Util/FoldConsts.lean`
//! (`Expr.getUsedConstants`). The ORDER of the list is part of the message —
//! Lean 4.8.0 prints the axioms in the order its depth-first walk first meets
//! them, not sorted (sorting arrived in a later Lean) — and a
//! `#guard_msgs` audit compares the message byte for byte after whitespace
//! normalization. So the walk is ported exactly:
//!
//! * a constant is visited once; an axiom is recorded and its type is NOT
//!   walked;
//! * a definition, theorem or opaque walks the constants of its type, then
//!   those of its value; an inductive walks its type, then each constructor;
//!   a constructor or recursor walks its type; a quotient primitive walks
//!   nothing (`Quot.sound` is an axiom in Lean, not a quotient primitive);
//! * the constants of an expression are taken in `FoldConstsImpl.fold`'s
//!   pre-order (function before argument, binder domain before body, `let`
//!   type, value, body, a projection's operand only), each once.
//!
//! Clean's environment is not Lean's, so the census answers for what Clean
//! actually checked: a constant Clean's prelude states as an axiom is listed,
//! and a declaration whose value Clean did not retain (proof-value elision of
//! an import) makes the census refuse rather than under-report.

use std::collections::HashSet;

use clean_kernel::env::ConstantKind;
use clean_kernel::name::NameInner;
use clean_kernel::{Environment, Expr, ExprKind, Name, QuotKind};

/// What `#print axioms c` printed: one information message per constant the
/// identifier resolved to (Lean's `cs.forM printAxiomsOf`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrintAxiomsResult {
    /// The message texts, in the order Lean logs them.
    pub messages: Vec<String>,
}

impl std::fmt::Display for PrintAxiomsResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.messages.join("\n"))
    }
}

/// Why the census could not be taken.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AxiomCensusRefusal {
    /// The constant `#print axioms` was asked about.
    pub(crate) root: Name,
    /// A constant in its closure whose value is not in the environment.
    pub(crate) missing_value: Name,
}

impl std::fmt::Display for AxiomCensusRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot list the axioms of '{}': the value of '{}' was not retained in this \
             environment (proof-value elision), so the constants it uses are unknown",
            lean_name_to_string(&self.root),
            lean_name_to_string(&self.missing_value)
        )
    }
}

/// Lean's `Format` default width (`Std.Format.defWidth`): the list of axioms
/// stays on one line exactly when the whole message fits in it.
const LEAN_FORMAT_WIDTH: usize = 120;

/// `Expr.getUsedConstants`: every constant of `expr`, once, in the order
/// `FoldConstsImpl.fold` first reaches it.
///
/// The walk memoizes on node identity like Lean's pointer cache, so a shared
/// subterm is walked once; that cannot change the order, because pre-order
/// finishes a subterm before it can meet the same node again.
#[must_use]
pub(crate) fn used_constants_in_order(expr: &Expr) -> Vec<Name> {
    let mut seen_nodes: HashSet<usize> = HashSet::new();
    let mut seen: HashSet<Name> = HashSet::new();
    let mut out = Vec::new();
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        if !seen_nodes.insert(std::ptr::from_ref(e) as usize) {
            continue;
        }
        match e.kind() {
            ExprKind::Const(name, _) => {
                if seen.insert(name.clone()) {
                    out.push(name.clone());
                }
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            // Children are pushed in reverse so the first is popped first.
            ExprKind::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(body);
                stack.push(ty);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(body);
                stack.push(val);
                stack.push(ty);
            }
            // Lean's fold visits the operand only, not the structure name.
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            // Clean's non-Lean expression forms never occur in a Lean term;
            // their constants are still reported (in a fixed order) so the
            // census can only over-report on them, never miss one.
            _ => {
                let mut extra = HashSet::new();
                e.collect_constants_into(&mut extra);
                let mut extra: Vec<Name> =
                    extra.into_iter().filter(|n| !seen.contains(n)).collect();
                extra.sort_by_key(Name::to_unambiguous_string);
                for name in extra {
                    seen.insert(name.clone());
                    out.push(name);
                }
            }
        }
    }
    out
}

/// How `CollectAxioms.collect` treats one constant.
enum Visit {
    /// Record it; walk nothing.
    Axiom,
    /// Walk these constants, in order.
    Walk(Vec<Name>),
    /// Walk nothing (a quotient primitive, or a name not in the environment —
    /// Lean's `none => pure ()`).
    Nothing,
    /// A declaration whose value Clean does not hold.
    ValueUnavailable,
}

fn classify(env: &Environment, name: &Name) -> Visit {
    if let Some(quot) = env.get_quot(name) {
        return if quot.kind == QuotKind::Sound {
            Visit::Axiom
        } else {
            Visit::Nothing
        };
    }
    if let Some(ind) = env.get_inductive(name) {
        let mut names = used_constants_in_order(&ind.type_);
        names.extend(ind.constructor_names.iter().cloned());
        return Visit::Walk(names);
    }
    if let Some(ctor) = env.get_constructor(name) {
        return Visit::Walk(used_constants_in_order(&ctor.type_));
    }
    // A value-bearing constant first: Clean files `casesOn` / `recOn` (Lean
    // definitions) in its recursor table too.
    if let Some(info) = env.get_const(name) {
        if let Some(value) = &info.value {
            let mut names = used_constants_in_order(&info.type_);
            names.extend(used_constants_in_order(value));
            return Visit::Walk(names);
        }
    }
    if let Some(rec) = env.get_recursor(name) {
        return Visit::Walk(used_constants_in_order(&rec.type_));
    }
    match env.get_const(name) {
        Some(info) if info.kind == ConstantKind::Axiom => Visit::Axiom,
        Some(_) => Visit::ValueUnavailable,
        None => Visit::Nothing,
    }
}

/// `CollectAxioms.collect root`: the axioms `root` depends on, in the order
/// Lean 4.8.0 records them.
///
/// # Errors
///
/// [`AxiomCensusRefusal`] when a definition, theorem or opaque in the closure
/// has no value in `env`: its dependencies are unknown, and listing the rest
/// would present a partial census as the whole one.
pub(crate) fn collect_axioms(
    env: &Environment,
    root: &Name,
) -> Result<Vec<Name>, AxiomCensusRefusal> {
    collect_axioms_of_all(env, root, vec![root.clone()])
}

/// [`collect_axioms`] over several roots with one visited set: every axiom
/// any of `roots` depends on, in the order the walk first reaches it (what
/// `#eval` needs to know about a whole term; `reported` names it in a
/// refusal).
pub(crate) fn collect_axioms_of_all(
    env: &Environment,
    reported: &Name,
    roots: Vec<Name>,
) -> Result<Vec<Name>, AxiomCensusRefusal> {
    let root = reported;
    let mut visited: HashSet<Name> = HashSet::new();
    let mut axioms = Vec::new();
    // Each frame is the rest of one constant's walk list; the depth-first
    // recursion of `collect` becomes this explicit stack, so a deep
    // dependency chain cannot exhaust the native stack.
    let mut frames: Vec<std::vec::IntoIter<Name>> = vec![roots.into_iter()];
    while let Some(frame) = frames.last_mut() {
        let Some(name) = frame.next() else {
            frames.pop();
            continue;
        };
        if !visited.insert(name.clone()) {
            continue;
        }
        match classify(env, &name) {
            Visit::Axiom => axioms.push(name),
            Visit::Walk(names) => frames.push(names.into_iter()),
            Visit::Nothing => {}
            Visit::ValueUnavailable => {
                return Err(AxiomCensusRefusal {
                    root: root.clone(),
                    missing_value: name,
                })
            }
        }
    }
    Ok(axioms)
}

/// `printAxiomsOf`'s message for `constant`, laid out as `Format.pretty`
/// lays out `m!"'{c}' depends on axioms: {axioms.toList}"`: the list is a
/// `sbracket` group of `,`+`line`-separated names, flat when the whole line
/// fits in [`LEAN_FORMAT_WIDTH`] columns and otherwise broken at every
/// separator with the group's one-column nest.
#[must_use]
pub(crate) fn axioms_message(constant: &Name, axioms: &[Name]) -> String {
    let constant = lean_name_to_string(constant);
    if axioms.is_empty() {
        return format!("'{constant}' does not depend on any axioms");
    }
    let names: Vec<String> = axioms.iter().map(lean_name_to_string).collect();
    let prefix = format!("'{constant}' depends on axioms: ");
    let flat = format!("{prefix}[{}]", names.join(", "));
    if flat.chars().count() <= LEAN_FORMAT_WIDTH {
        flat
    } else {
        format!("{prefix}[{}]", names.join(",\n "))
    }
}

// --- Lean 4.8.0 `Name.toString` (`Init/Meta.lean`) ---------------------------

/// `isLetterLike` as of Lean 4.8.0 (no Latin-1 ranges yet).
fn is_letter_like(c: char) -> bool {
    let v = u32::from(c);
    ((0x3b1..=0x3c9).contains(&v) && v != 0x3bb)
        || ((0x391..=0x3a9).contains(&v) && v != 0x3a0 && v != 0x3a3)
        || (0x3ca..=0x3fb).contains(&v)
        || (0x1f00..=0x1ffe).contains(&v)
        || (0x2100..=0x214f).contains(&v)
        || (0x1d49c..=0x1d59f).contains(&v)
}

/// `isSubScriptAlnum` as of Lean 4.8.0.
fn is_subscript_alnum(c: char) -> bool {
    let v = u32::from(c);
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
}

/// `isIdFirst` (`Char.isAlpha` is ASCII-only).
fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// `isIdRest`.
fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_letter_like(c)
        || is_subscript_alnum(c)
}

/// `Name.escapePart`.
fn escape_part(s: &str) -> Option<String> {
    let mut chars = s.chars();
    if chars.next().is_some_and(is_id_first) && chars.all(is_id_rest) {
        Some(s.to_owned())
    } else if s.contains('»') {
        None
    } else {
        Some(format!("«{s}»"))
    }
}

fn is_inaccessible_user_name(n: &Name) -> bool {
    match n.inner() {
        NameInner::Str(_, s) => s.contains('✝') || s.as_ref() == "_inaccessible",
        NameInner::Num(p, _) => is_inaccessible_user_name(p),
        NameInner::Anon => false,
    }
}

fn has_macro_scopes(n: &Name) -> bool {
    match n.inner() {
        NameInner::Str(_, s) => s.as_ref() == "_hyg",
        NameInner::Num(p, _) => has_macro_scopes(p),
        NameInner::Anon => false,
    }
}

/// `maybePseudoSyntax`: the root component starts with `#` or `?`.
fn maybe_pseudo_syntax(n: &Name) -> bool {
    let mut current = n;
    loop {
        match current.inner() {
            NameInner::Str(p, _) | NameInner::Num(p, _) if !p.is_anon() => current = p,
            NameInner::Str(_, s) => return s.starts_with('#') || s.starts_with('?'),
            _ => return false,
        }
    }
}

fn to_string_with_sep(n: &Name, escape: bool, out: &mut String) {
    let part = |s: &str| {
        if escape {
            escape_part(s).unwrap_or_else(|| s.to_owned())
        } else {
            s.to_owned()
        }
    };
    match n.inner() {
        NameInner::Anon => out.push_str("[anonymous]"),
        NameInner::Str(p, s) if p.is_anon() => out.push_str(&part(s)),
        NameInner::Num(p, v) if p.is_anon() => out.push_str(&v.to_string()),
        NameInner::Str(p, s) => {
            to_string_with_sep(p, escape, out);
            out.push('.');
            out.push_str(&part(s));
        }
        NameInner::Num(p, v) => {
            to_string_with_sep(p, escape, out);
            out.push('.');
            out.push_str(&v.to_string());
        }
    }
}

/// Lean 4.8.0 `Name.toString` with `escape := true`: what `MessageData.ofName`
/// prints.
#[must_use]
pub(crate) fn lean_name_to_string(n: &Name) -> String {
    let escape = !is_inaccessible_user_name(n) && !has_macro_scopes(n) && !maybe_pseudo_syntax(n);
    let mut out = String::new();
    to_string_with_sep(n, escape, &mut out);
    out
}

#[cfg(test)]
#[path = "print_axioms_tests.rs"]
mod tests;
