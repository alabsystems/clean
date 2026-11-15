// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How many term nodes a nested inductive's rewrite may build (R172).

use super::NestedError;
use crate::inductive::{AdmitError, InductiveDecl};
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};

/// The most term nodes the rewrite of one nested inductive is charged for: the
/// rewritten and auxiliary types it returns, a shared subterm counted at each
/// occurrence (R172), and, to match a site with an occurrence, each node
/// lowering builds and each pair of nodes a comparison looks at (R174, R176).
/// Substituting an occurrence's arguments for a container's parameters copies
/// an argument at every use of its parameter, and rewriting a self-reference
/// applies the auxiliary to every parameter of the parent, so these types can
/// be far larger than the declarations they come from, and admission walks
/// each of them by its tree. Real nested inductives hold a few thousand nodes.
pub const MAX_AUX_SIZE: u64 = 1 << 24;

/// Where the rewrite charges [`MAX_AUX_SIZE`], named in a refusal (R174).
pub(super) enum At<'a> {
    /// A parent constructor, before phase 3 rewrites it.
    ParentCtor(&'a Name),
    /// An auxiliary type, before it is built.
    AuxType,
    /// An auxiliary constructor, before it is built from the container's.
    AuxCtor(&'a Name),
    /// The nodes built and the pairs of nodes compared to match sites with
    /// occurrences, in a constructor, each before it is built or compared
    /// (R176).
    Matching(&'a Name),
}

/// What is left of a nested inductive's [`MAX_AUX_SIZE`]. Each type is
/// charged an upper bound on its size before it is built.
pub(super) struct Room(u64);

impl Room {
    pub(super) fn new() -> Room {
        Room(MAX_AUX_SIZE)
    }

    /// The nodes of `term`, a shared subterm counted at each occurrence, or
    /// more than what is left: the walk stops once the count passes it, so it
    /// costs at most one step more than what is left.
    pub(super) fn measure(&self, term: &Term) -> u64 {
        size_within(term, self.0)
    }

    /// The nodes that prepending the parent's parameter binders adds to a
    /// type: one Π node for each binder, and its type (R174).
    pub(super) fn binders(&self, param_binders: &[(BinderInfo, Term)]) -> u64 {
        param_binders
            .iter()
            .map(|(_, ty)| self.measure(ty).saturating_add(1))
            .fold(0, u64::saturating_add)
    }

    /// Take `nodes` from what is left, or refuse `ind` when they do not fit,
    /// naming where.
    pub(super) fn take(
        &mut self,
        nodes: u64,
        decl: &InductiveDecl,
        ind: &Name,
        at: At<'_>,
    ) -> Result<(), NestedError> {
        if nodes > self.0 {
            let site = match at {
                At::ParentCtor(c) => format!("the parent constructor `{c}`"),
                At::AuxType => format!("the auxiliary type `{ind}`"),
                At::AuxCtor(c) => format!("the auxiliary constructor copied from `{c}`"),
                At::Matching(c) => {
                    format!("the nodes built and compared to match nested sites in `{c}`")
                }
            };
            return Err(NestedError::Aux {
                ind: decl.name.clone(),
                source: AdmitError::Derivation {
                    ind: ind.clone(),
                    detail: format!(
                        "the block's rewrite could build more than {MAX_AUX_SIZE} term nodes, past the budget at {site}"
                    ),
                },
            });
        }
        // AUDIT: saturating; a count compared with a bound, never a value.
        self.0 = self.0.saturating_sub(nodes);
        Ok(())
    }
}

/// How many nodes the self-reference rewrite can make of one: a matched
/// site's head constant becomes the auxiliary applied to the parent's
/// `num_params` parameters, `2·num_params + 1` nodes, the container's
/// parameter arguments are dropped, and every other node is kept.
pub(super) fn rewrite_growth(num_params: u32) -> u64 {
    // AUDIT: saturating; a count compared with a bound, never a value.
    u64::from(num_params).saturating_mul(2).saturating_add(1)
}

/// The nodes of `term`, or `cap + 1` once the count passes `cap`.
fn size_within(term: &Term, cap: u64) -> u64 {
    let mut nodes: u64 = 0;
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        // AUDIT: saturating; a count compared with a bound, never a value.
        nodes = nodes.saturating_add(1);
        if nodes > cap {
            break;
        }
        match t.kind() {
            TermKind::App(a, b) | TermKind::Lam(_, a, b) | TermKind::Pi(_, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            TermKind::Let(a, b, c) => {
                stack.push(a);
                stack.push(b);
                stack.push(c);
            }
            TermKind::Proj(_, _, a) => stack.push(a),
            TermKind::BVar(_)
            | TermKind::Sort(_)
            | TermKind::Const(_)
            | TermKind::Elim(_)
            | TermKind::Lit(_) => {}
        }
    }
    nodes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::minimal_env::MinimalEnv;
    use crate::rawexpr::{RawExpr, RawLevel};

    /// `(A : Type) (f : Type → Type)`: 1 + 1 nodes, then 3 + 1.
    #[test]
    fn test_room_binders_count_a_pi_node_and_the_type_of_each() {
        let ty = || RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)));
        let arrow = RawExpr::Pi(BinderInfo::Default, Box::new(ty()), Box::new(ty()));
        let closed =
            |raw: &RawExpr| Term::validate_closed(&MinimalEnv::new(), raw).expect("a closed term");
        let binders = [
            (BinderInfo::Default, closed(&ty())),
            (BinderInfo::Default, closed(&arrow)),
        ];
        assert_eq!(Room::new().binders(&binders), 6);
    }
}
