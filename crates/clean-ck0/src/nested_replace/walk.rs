// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The walks the nested rewrites make over a term (R176). Each looks at a
//! node of the term's tree a bounded number of times, or is charged for what
//! it looks at before it looks: marking the nodes that mention a constant,
//! taking an application spine apart, and comparing two terms.
//!
//! A test can narrow the hashes the comparison fast-rejects on and the
//! occurrence index keys by (`narrow_hashes`), so that distinct terms
//! collide and what a whole hash would hide is reached: the comparison's
//! own walk, and the index's candidates past the first.

#[cfg(test)]
use std::cell::Cell;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::sync::Arc;

use super::Charge;
use crate::name::Name;
use crate::nested::NestedError;
use crate::term::{Term, TermKind};

/// The children of a node, in the order the rewrites take them.
fn children(t: &Term) -> [Option<&Term>; 3] {
    match t.kind() {
        TermKind::App(a, b) | TermKind::Lam(_, a, b) | TermKind::Pi(_, a, b) => {
            [Some(a), Some(b), None]
        }
        TermKind::Let(a, b, c) => [Some(a), Some(b), Some(c)],
        TermKind::Proj(_, _, a) => [Some(a), None, None],
        TermKind::BVar(_)
        | TermKind::Sort(_)
        | TermKind::Const(_)
        | TermKind::Elim(_)
        | TermKind::Lit(_) => [None, None, None],
    }
}

/// The nodes of one term that mention a constant, found by one walk that
/// looks at each node of the term's tree once (R176).
///
/// A node is named by its address. Every node of the term stays allocated
/// while the term is borrowed, and `'t` makes the borrow checker hold that
/// borrow while the set exists, so no other live node has one of these
/// addresses while it is in use. The addresses are compared, never followed.
/// Only nodes of that term may be asked about.
pub(crate) struct Mentions<'t> {
    nodes: HashSet<*const TermKind>,
    term: PhantomData<&'t Term>,
}

impl<'t> Mentions<'t> {
    /// The nodes of `t` that mention `Const(name)`: `name` itself and every
    /// node above one. Each node is popped once to be looked at and, when it
    /// has children, once more to be decided after them.
    pub(crate) fn of(t: &'t Term, name: &Name) -> Mentions<'t> {
        Self::of_many(t, std::slice::from_ref(name))
    }

    pub(crate) fn of_many(t: &'t Term, names: &[Name]) -> Mentions<'t> {
        let names: HashSet<_> = names.iter().collect();
        let mut nodes: HashSet<*const TermKind> = HashSet::new();
        let mut stack: Vec<(&'t Term, bool)> = vec![(t, false)];
        while let Some((node, decide)) = stack.pop() {
            if decide {
                let mentions = children(node)
                    .into_iter()
                    .flatten()
                    .any(|c| nodes.contains(&Arc::as_ptr(&c.kind)));
                if mentions {
                    nodes.insert(Arc::as_ptr(&node.kind));
                }
                continue;
            }
            #[cfg(test)]
            crate::term::walk_step();
            match node.kind() {
                TermKind::Const(c) => {
                    if names.contains(c.name()) {
                        nodes.insert(Arc::as_ptr(&node.kind));
                    }
                }
                TermKind::BVar(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
                TermKind::App(..)
                | TermKind::Lam(..)
                | TermKind::Pi(..)
                | TermKind::Let(..)
                | TermKind::Proj(..) => {
                    stack.push((node, true));
                    stack.extend(children(node).into_iter().flatten().map(|c| (c, false)));
                }
            }
        }
        Mentions {
            nodes,
            term: PhantomData,
        }
    }

    /// Whether `node`, a node of the term the set was made from, mentions
    /// the constant.
    pub(crate) fn contains(&self, node: &Term) -> bool {
        self.nodes.contains(&Arc::as_ptr(&node.kind))
    }
}

/// An application spine `head a_1 … a_k`, as references into the term
/// (R176): `apps[i]` is `head` applied to `args[..=i]`, so the term itself
/// is last. A term that is not an application is its own head, with no
/// arguments.
pub(crate) struct Spine<'t> {
    pub(crate) head: &'t Term,
    pub(crate) apps: Vec<&'t Term>,
    pub(crate) args: Vec<&'t Term>,
}

impl<'t> Spine<'t> {
    /// Take `t` apart, one step per application node.
    pub(crate) fn of(t: &'t Term) -> Spine<'t> {
        let mut apps = Vec::new();
        let mut args = Vec::new();
        let mut head = t;
        while let TermKind::App(f, a) = head.kind() {
            #[cfg(test)]
            crate::term::walk_step();
            apps.push(head);
            args.push(a);
            head = f;
        }
        apps.reverse();
        args.reverse();
        Spine { head, apps, args }
    }
}

/// Whether `a == b`, as [`Term`]'s equality decides it, charging each pair
/// of nodes before it looks at it (R176). It takes the pairs in that
/// equality's order and stops where it stops, so it charges one per call
/// the recursive equality makes. It fast-rejects on [`narrowed`] hashes,
/// which outside tests are the hashes themselves.
pub(crate) fn same_term(a: &Term, b: &Term, charge: &mut Charge<'_>) -> Result<bool, NestedError> {
    let mut stack: Vec<(&Term, &Term)> = vec![(a, b)];
    let mut seen = HashSet::new();
    while let Some((x, y)) = stack.pop() {
        #[cfg(test)]
        crate::term::walk_step();
        charge(1)?;
        if Arc::ptr_eq(&x.kind, &y.kind) {
            continue;
        }
        if narrowed(x.hash) != narrowed(y.hash) {
            return Ok(false);
        }
        if !seen.insert((Arc::as_ptr(&x.kind), Arc::as_ptr(&y.kind))) {
            continue;
        }
        let same = match (x.kind(), y.kind()) {
            (TermKind::BVar(i), TermKind::BVar(j)) => i == j,
            (TermKind::Sort(l), TermKind::Sort(m)) => l == m,
            (TermKind::Const(c), TermKind::Const(d)) => c == d,
            (TermKind::Elim(e), TermKind::Elim(f)) => e == f,
            (TermKind::Lit(p), TermKind::Lit(q)) => p == q,
            (TermKind::App(f1, a1), TermKind::App(f2, a2)) => {
                stack.push((a1, a2));
                stack.push((f1, f2));
                true
            }
            (TermKind::Lam(b1, t1, x1), TermKind::Lam(b2, t2, x2))
            | (TermKind::Pi(b1, t1, x1), TermKind::Pi(b2, t2, x2)) => {
                stack.push((x1, x2));
                stack.push((t1, t2));
                b1 == b2
            }
            (TermKind::Let(t1, v1, x1), TermKind::Let(t2, v2, x2)) => {
                stack.push((x1, x2));
                stack.push((v1, v2));
                stack.push((t1, t2));
                true
            }
            (TermKind::Proj(n1, i1, e1), TermKind::Proj(n2, i2, e2)) => {
                stack.push((e1, e2));
                n1 == n2 && i1 == i2
            }
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether `xs == ys`, as `Vec<Term>`'s equality decides it: the lengths,
/// then each pair in turn with [`same_term`], stopping at the first that
/// differs.
pub(crate) fn same_args(
    xs: &[Term],
    ys: &[Term],
    charge: &mut Charge<'_>,
) -> Result<bool, NestedError> {
    if xs.len() != ys.len() {
        return Ok(false);
    }
    for (x, y) in xs.iter().zip(ys) {
        if !same_term(x, y, charge)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// A cached term hash as [`same_term`] fast-rejects on it and the index
/// keys by it: the hash itself.
#[cfg(not(test))]
pub(super) fn narrowed(hash: u64) -> u64 {
    hash
}

/// A cached term hash as [`same_term`] fast-rejects on it and the index
/// keys by it: the hash itself, or, while a test narrows this thread's
/// hashes, the hash folded onto that many values (R176).
#[cfg(test)]
pub(super) fn narrowed(hash: u64) -> u64 {
    HASH_VALUES
        .with(Cell::get)
        .and_then(|values| hash.checked_rem(values))
        .unwrap_or(hash)
}

#[cfg(test)]
thread_local! {
    /// How many values [`narrowed`] folds this thread's hashes onto, or
    /// `None` to leave them whole.
    static HASH_VALUES: Cell<Option<u64>> = const { Cell::new(None) };
}

/// Fold the hashes [`same_term`] and the occurrence index use on this
/// thread onto `values` values (`None`: leave them whole) while the guard
/// lives, so that distinct terms collide (R176).
#[cfg(test)]
pub(crate) fn narrow_hashes(values: Option<u64>) -> NarrowedHashes {
    NarrowedHashes {
        before: HASH_VALUES.with(|v| v.replace(values)),
    }
}

/// While it lives, this thread's hashes are narrowed; dropped, even by a
/// panic, they are as they were.
#[cfg(test)]
#[must_use = "the hashes are narrowed only while the guard lives"]
pub(crate) struct NarrowedHashes {
    before: Option<u64>,
}

#[cfg(test)]
impl Drop for NarrowedHashes {
    fn drop(&mut self) {
        HASH_VALUES.with(|v| v.set(self.before));
    }
}

#[cfg(test)]
mod tests;
