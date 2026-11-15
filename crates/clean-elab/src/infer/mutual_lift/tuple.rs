// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tuples of motive bodies (design §5.4, brick B2).
//!
//! A recursor slot several members own carries all of their results at once:
//! its motive is a right-nested tuple of the owners' motive bodies, its minor
//! the tuple of their specialized minors, and each owner reads its component
//! back by projection. A transparent intermediate slot (`String × T`) carries
//! the tuple of its fields' induction hypotheses the same way.
//!
//! The tuple is `PProd` when the block's motive universe is `Sort ≥ 1` and
//! `And` when it is `Prop` (every owner a theorem). One component is the
//! component itself; there is no empty tuple (a slot with no component is not
//! a tuple slot).

use clean_kernel::{Expr, Level, Name};

/// The tuple former of one lifted block.
#[derive(Debug, Clone)]
pub(super) enum TupleKind {
    /// `And A (And B C)`; components are proofs, projections `.1`/`.2`.
    And,
    /// `PProd.{l,l} A (PProd.{l,l} B C)` at the block's motive level `l`,
    /// which the caller checked satisfies `Sort (max 1 l) ≡ Sort l`.
    PProd(Level),
}

impl TupleKind {
    fn struct_name(&self) -> Name {
        match self {
            Self::And => Name::from_string("And"),
            Self::PProd(_) => Name::from_string("PProd"),
        }
    }

    fn former(&self) -> Expr {
        match self {
            Self::And => Expr::const_(Name::from_string("And"), vec![]),
            Self::PProd(level) => Expr::const_(
                Name::from_string("PProd"),
                vec![level.clone(), level.clone()],
            ),
        }
    }

    fn intro(&self) -> Expr {
        match self {
            Self::And => Expr::const_(Name::from_string("And.intro"), vec![]),
            Self::PProd(level) => Expr::const_(
                Name::from_string("PProd.mk"),
                vec![level.clone(), level.clone()],
            ),
        }
    }

    /// The tuple type of `tys` (non-empty).
    pub(super) fn ty(&self, tys: &[Expr]) -> Expr {
        match tys {
            [] => Expr::prop(),
            [one] => one.clone(),
            [first, rest @ ..] => Expr::apps(self.former(), [first.clone(), self.ty(rest)]),
        }
    }

    /// The tuple of `vals`, whose types are `tys` (same length, non-empty).
    pub(super) fn val(&self, tys: &[Expr], vals: &[Expr]) -> Expr {
        match (tys, vals) {
            ([first_ty, rest_tys @ ..], [first, rest @ ..]) if !rest.is_empty() => Expr::apps(
                self.intro(),
                [
                    first_ty.clone(),
                    self.ty(rest_tys),
                    first.clone(),
                    self.val(rest_tys, rest),
                ],
            ),
            (_, [one]) => one.clone(),
            _ => Expr::prop(),
        }
    }

    /// Component `index` of a tuple of `count` components.
    pub(super) fn project(&self, tuple: Expr, index: usize, count: usize) -> Expr {
        if count <= 1 {
            return tuple;
        }
        let name = self.struct_name();
        let mut cur = tuple;
        for _ in 0..index.min(count - 1) {
            cur = Expr::proj(name.clone(), 1, cur);
        }
        if index < count - 1 {
            cur = Expr::proj(name, 0, cur);
        }
        cur
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    #[test]
    fn test_tuple_project_paths_cover_every_component() {
        let kind = TupleKind::And;
        let t = c("t");
        assert_eq!(kind.project(t.clone(), 0, 1), t);
        let and = Name::from_string("And");
        assert_eq!(
            kind.project(t.clone(), 0, 2),
            Expr::proj(and.clone(), 0, t.clone())
        );
        assert_eq!(
            kind.project(t.clone(), 1, 2),
            Expr::proj(and.clone(), 1, t.clone())
        );
        assert_eq!(
            kind.project(t.clone(), 1, 3),
            Expr::proj(and.clone(), 0, Expr::proj(and.clone(), 1, t.clone()))
        );
        assert_eq!(
            kind.project(t.clone(), 2, 3),
            Expr::proj(and.clone(), 1, Expr::proj(and, 1, t))
        );
    }

    #[test]
    fn test_tuple_type_and_value_are_right_nested() {
        let kind = TupleKind::PProd(Level::succ(Level::zero()));
        let tys = [c("A"), c("B"), c("C")];
        let vals = [c("a"), c("b"), c("c")];
        let ty = kind.ty(&tys);
        let inner = kind.ty(&tys[1..]);
        assert_eq!(ty, Expr::apps(kind.former(), [c("A"), inner.clone()]));
        let val = kind.val(&tys, &vals);
        assert_eq!(
            val,
            Expr::apps(
                kind.intro(),
                [c("A"), inner, c("a"), kind.val(&tys[1..], &vals[1..])]
            )
        );
        assert_eq!(kind.val(&tys[2..], &vals[2..]), c("c"));
    }
}
