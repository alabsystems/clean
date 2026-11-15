// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The one pass of strict positivity (R176). A constructor's field, or a
//! container constructor's, is walked once, children before parents, on an
//! explicit stack: each subterm in a strictly-positive position pushes
//! whether it mentions the target, and its parent applies the polarity rule
//! to its children's answers. The rules before R176 asked an argument of a
//! foreign application whether it mentions the target by a walk of its own and
//! then walked it again, so a chain of `d` applications cost about `d` times
//! the chain.
//!
//! A domain to the left of an arrow, and an argument of a block type's own
//! application, are only asked whether they mention the target, by the walk
//! the rules used; nothing else walks inside them, so no node is walked twice.
//! A leaf answers from the shape the pass read, so each node is read once,
//! except a head that is not a constant (twice: once to see that it is not
//! one). With each container slot scanned once (`variance`), a check reads
//! no more than the rules did on a constructor both admit
//! (`tests/differential.rs`).

use super::variance::Obligations;
use super::{bvar_mentions, term_mentions_any};
use crate::name::Name;
use crate::term::{Term, TermKind};

/// What a pass looks for.
#[derive(Clone, Copy)]
pub(super) enum Target<'a> {
    /// A constant naming a type of the block being admitted.
    Block(&'a [Name]),
    /// The variable a container constructor's parameter `p` binds, read as
    /// `bvar_mentions` reads it: at binder depth `d` from the constructor's
    /// top it is `BVar(d - 1 - p)`, and at `d <= p` nothing mentions it. That
    /// reading also takes a binder inside the type of a parameter `q <= p` for
    /// the parameter; R176 keeps it (`tests/pins.rs` pins it both ways).
    Param(usize),
}

impl Target<'_> {
    /// Whether a subterm at binder depth `depth` can mention the target.
    fn read_at(self, depth: usize) -> bool {
        match self {
            Target::Block(_) => true,
            Target::Param(p) => depth > p,
        }
    }

    /// Whether `t`, at binder depth `depth`, mentions the target: the walk the
    /// rules before R176 used.
    fn mentioned_in(self, t: &Term, depth: usize) -> bool {
        match self {
            Target::Block(names) => term_mentions_any(t, names),
            Target::Param(p) => bvar_mentions(t, p, depth),
        }
    }

    /// Whether the constant `c` is a block type: a leaf `c` mentions the
    /// target, and an application headed by `c` is a block type's.
    fn is_block_type(self, c: &Name) -> bool {
        match self {
            Target::Block(names) => names.iter().any(|n| n == c),
            Target::Param(_) => false,
        }
    }

    /// Whether the variable `BVar(i)`, at binder depth `depth`, is the target,
    /// as `bvar_mentions` reads a variable: `BVar(depth - 1 - p)` for
    /// `Param(p)`, and nothing at `depth <= p`.
    fn is_variable(self, i: u32, depth: usize) -> bool {
        match self {
            Target::Block(_) => false,
            Target::Param(p) => depth
                .checked_sub(p)
                .and_then(|x| x.checked_sub(1))
                .is_some_and(|at| usize::try_from(i).is_ok_and(|iv| iv == at)),
        }
    }
}

/// One step of the pass. Each `Visit` leaves exactly one answer on the answer
/// stack once the steps it pushes are done.
enum Step {
    /// Check `.0`, at binder depth `.1`, in a strictly-positive position.
    Visit(Term, usize),
    /// A binder or projection node at `depth`: its `children` answers are on
    /// top; it mentions the target if one of them does and `depth` reads it.
    Join { children: usize, depth: usize },
    /// `container a0 … a(arity-1)`, a constant that is not a block type: the
    /// arguments' answers are on top, in order. A mentioning `ai` makes slot
    /// `i` of `container` an obligation.
    Container {
        container: Name,
        arity: usize,
        depth: usize,
    },
    /// `h a0 … a(arity-1)`, `h` not a constant: `h`'s answer and then the
    /// arguments' are on top. No argument may mention the target.
    Applied { arity: usize, depth: usize },
}

/// Check each Π domain of `ctor_ty`'s telescope strictly positive (the final
/// codomain permits any occurrence). Domain `k` sits at binder depth `k`.
pub(super) fn scan_telescope(
    ctor_ty: &Term,
    target: Target<'_>,
    obligations: &mut Obligations<'_>,
) -> Result<(), ()> {
    let mut cur = ctor_ty.clone();
    let mut depth: usize = 0;
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        strict_mentions(dom, depth, target, obligations)?;
        // AUDIT: saturating; a binder depth is below the term's height.
        depth = depth.saturating_add(1);
        cur = codom.clone();
    }
    Ok(())
}

/// Check `t`, at binder depth `depth`, in a strictly-positive position, and
/// return whether it mentions the target. `Err(())` on the first violation.
fn strict_mentions(
    t: &Term,
    depth: usize,
    target: Target<'_>,
    obligations: &mut Obligations<'_>,
) -> Result<bool, ()> {
    let mut steps: Vec<Step> = vec![Step::Visit(t.clone(), depth)];
    let mut answers: Vec<bool> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(t, depth) => visit(&t, depth, target, &mut steps, &mut answers)?,
            Step::Join { children, depth } => {
                let at = top(&answers, children)?;
                let any = answers.drain(at..).any(|m| m);
                answers.push(any && target.read_at(depth));
            }
            Step::Container {
                container,
                arity,
                depth,
            } => {
                let at = top(&answers, arity)?;
                let mut any = false;
                for (slot, mentions) in answers.drain(at..).enumerate() {
                    if mentions {
                        obligations.require(&container, slot);
                        any = true;
                    }
                }
                answers.push(any && target.read_at(depth));
            }
            Step::Applied { arity, depth } => {
                // AUDIT: checked; `arity` counts the arguments of a term in memory.
                let at = top(&answers, arity.checked_add(1).ok_or(())?)?;
                let (head, args) = {
                    let mut parts = answers.drain(at..);
                    (parts.next(), parts.any(|m| m))
                };
                let head = head.ok_or(())?;
                if args {
                    // A head that is not a constant with the target in an
                    // argument: covariance cannot be established ⇒ fail-closed.
                    return Err(());
                }
                answers.push(head && target.read_at(depth));
            }
        }
    }
    match answers.as_slice() {
        [mentions] => Ok(*mentions),
        // Each visit leaves one answer: any other count is a defect of this
        // pass, refused rather than read (fail-closed).
        _ => Err(()),
    }
}

/// Where the top `n` answers start, or a refusal when there are fewer (a
/// defect of the pass; fail-closed).
fn top(answers: &[bool], n: usize) -> Result<usize, ()> {
    // AUDIT: checked; an underflow is refused.
    answers.len().checked_sub(n).ok_or(())
}

/// Apply the polarity rule at `t`: refuse, answer a leaf, or push the steps
/// that answer its children and then combine them.
fn visit(
    t: &Term,
    depth: usize,
    target: Target<'_>,
    steps: &mut Vec<Step>,
    answers: &mut Vec<bool>,
) -> Result<(), ()> {
    // AUDIT: saturating; a binder depth is below the term's height.
    let under = depth.saturating_add(1);
    match t.kind() {
        TermKind::Pi(_, dom, codom) => {
            // (A -> B): no target may appear in A; B continues
            // strict-positive.
            if target.mentioned_in(dom, depth) {
                return Err(());
            }
            steps.push(Step::Join { children: 1, depth });
            steps.push(Step::Visit(codom.clone(), under));
        }
        TermKind::App(_, _) => {
            let (head, args) = t.unfold_apps();
            match head.kind() {
                TermKind::Const(c) if target.is_block_type(c.name()) => {
                    // A block type applied to args: each arg must contain no
                    // occurrence of any block type.
                    if args.iter().any(|a| target.mentioned_in(a, depth)) {
                        return Err(());
                    }
                    answers.push(true);
                }
                TermKind::Const(c) => {
                    steps.push(Step::Container {
                        container: c.name().clone(),
                        arity: args.len(),
                        depth,
                    });
                    steps.extend(args.into_iter().rev().map(|a| Step::Visit(a, depth)));
                }
                _ => {
                    steps.push(Step::Applied {
                        arity: args.len(),
                        depth,
                    });
                    steps.extend(args.into_iter().rev().map(|a| Step::Visit(a, depth)));
                    steps.push(Step::Visit(head.clone(), depth));
                }
            }
        }
        TermKind::Lam(_, ty, body) => {
            steps.push(Step::Join { children: 2, depth });
            steps.push(Step::Visit(body.clone(), under));
            steps.push(Step::Visit(ty.clone(), depth));
        }
        TermKind::Let(ty, val, body) => {
            steps.push(Step::Join { children: 3, depth });
            steps.push(Step::Visit(body.clone(), under));
            steps.push(Step::Visit(val.clone(), depth));
            steps.push(Step::Visit(ty.clone(), depth));
        }
        TermKind::Proj(_, _, e) => steps.push(Step::Visit(e.clone(), depth)),
        // A leaf answers from the shape just read, as `mentioned_in`'s walk
        // would: asking the walk read each leaf twice, more than the rules
        // did on a wide container (`tests.rs`).
        TermKind::BVar(i) => answers.push(target.is_variable(*i, depth)),
        TermKind::Const(c) => answers.push(target.is_block_type(c.name())),
        TermKind::Sort(_) | TermKind::Lit(_) | TermKind::Elim(_) => answers.push(false),
    }
    Ok(())
}
