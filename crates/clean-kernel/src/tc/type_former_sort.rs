// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The result sort of an inductive type former, read the way Lean's kernel
//! reads it.
//!
//! Lean's `check_inductive_types` (`src/kernel/inductive.cpp@v4.30.0-rc2`,
//! lines 211-256) whnf's the type former, then walks its binders, whnf-ing
//! again after each one, and finally calls `ensure_sort`. The level it finds
//! there, `m_result_level`, is the ONE fact every later step reads: the
//! per-field universe bound (`check_constructors`), whether the family may
//! eliminate only into `Prop` (`elim_only_at_universe_zero`, through
//! `m_is_not_zero`), and whether it is a K target (`init_K_target`).
//!
//! A purely syntactic read (`get_return_type` + a `Sort` match) disagrees with
//! that loop whenever the codomain is a sort only up to reduction:
//! `def MyProp : Type := Prop; inductive B : MyProp | t | f`. Lean's level for
//! `B` is `0`, so `B.rec` eliminates only into `Prop`; a syntactic read sees no
//! `Sort` at all. Clean's elimination analysis used to answer "large
//! elimination allowed" for such a head, while proof irrelevance (which does
//! whnf) still treated `B` as a proposition, so `B.t ≡ B.f` and a
//! `B.rec`-into-`Bool` derived `False`.

use super::TypeChecker;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// What Lean's `check_inductive_types` loop reads off one type former.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeFormerSort {
    /// The level `l` of the final `Sort l`, found up to whnf.
    pub(crate) level: Level,
    /// The binders the loop walked (parameters plus indices, as Lean counts
    /// them), including any a definition hides.
    pub(crate) arity: u32,
}

impl TypeFormerSort {
    /// The syntactic read, when it is exact: a `Pi` telescope that ends in a
    /// `Sort` is in whnf at every step of Lean's loop (whnf leaves a `Pi` and a
    /// `Sort` head alone, and opening a binder with a local does not change the
    /// head of its body), so the loop would return exactly this.
    pub(crate) fn syntactic(ty: &Expr) -> Option<Self> {
        let mut cur = ty;
        let mut arity = 0u32;
        while let ExprKind::Pi(_, _, body) = cur.kind() {
            cur = body;
            arity += 1;
        }
        match cur.kind() {
            ExprKind::Sort(level) => Some(Self {
                level: level.clone(),
                arity,
            }),
            _ => None,
        }
    }
}

impl TypeChecker<'_> {
    /// The result sort of the type former `ty`, by Lean's loop: whnf, then
    /// whnf between binders, then require a `Sort`. `None` when the type does
    /// not reduce to a telescope ending in a `Sort` (Lean's `ensure_sort`
    /// throws there).
    ///
    /// The syntactic fast path is exact (see [`TypeFormerSort::syntactic`]),
    /// so a type former that already ends in a `Sort` costs no reduction.
    pub(crate) fn type_former_result_sort(&self, ty: &Expr) -> Option<TypeFormerSort> {
        if let Some(sort) = TypeFormerSort::syntactic(ty) {
            return Some(sort);
        }
        let mut current = self.whnf(ty);
        let mut depth = 0u32;
        let result = loop {
            match current.kind() {
                ExprKind::Pi(bd, domain, body) => {
                    let fvar = self.ctx_push(Name::anon(), domain.as_ref().clone(), *bd);
                    let opened = self.open_bvar(body, fvar);
                    depth += 1;
                    current = self.whnf(&opened);
                }
                ExprKind::Sort(level) => {
                    break Some(TypeFormerSort {
                        level: level.clone(),
                        arity: depth,
                    })
                }
                _ => break None,
            }
        };
        for _ in 0..depth {
            self.ctx_pop();
        }
        result
    }
}
