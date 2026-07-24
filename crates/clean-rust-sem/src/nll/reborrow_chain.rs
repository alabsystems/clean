// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reborrow-chain resolution for NLL conflict checking.
//!
//! When a borrow is created by reborrowing a reference local (e.g.
//! `_2 = &(*_3)` where `_3` was previously `&c.value`), the borrow's
//! `borrowed_place` is `Deref(Local(_3))` — syntactically distinct from
//! the original `c.value`. The NLL conflict checker compares
//! `borrowed_place` values via `Place::conflicts_with`, which is purely
//! prefix-based; without resolving the reborrow chain, a conflict
//! between `Deref(Local(_3))` and `Local(c)` (or `Field(Local(c), ...)`)
//! is missed even though both ultimately refer to overlapping memory
//! rooted at `c`.
//!
//! This module precomputes the map `ref_local -> borrowed_place` from
//! the body's `Rvalue::Ref` assignments and exposes a `resolve_place`
//! helper that rewrites a place by inlining each `Deref(Local(L))`
//! occurrence with the resolved place that `L` was assigned to ref.
//!
//! The resolution is conservative: only reborrow assignments observed
//! directly (an `Rvalue::Ref { place, .. }` to a `Place::Local(ref_local)`)
//! participate; locals assigned from other rvalues (e.g. function
//! return values, copies of references) leave the `Deref` un-resolved
//! and the conflict check falls back to the pre-existing prefix
//! comparison. This means resolution can only *narrow* a place toward
//! its true memory location, never invent a spurious conflict.

use crate::ownership::Place;
use crate::vir::{Body, LocalId, Rvalue, Stmt};
use std::collections::HashMap;

/// Maps a reference local to the place it borrowed at its (unique)
/// `Rvalue::Ref` assignment. Locals with multiple ref-assigns are
/// excluded — resolving them would be ambiguous, so the checker
/// falls back to the un-resolved place.
#[derive(Debug, Default, Clone)]
pub(crate) struct ReborrowMap {
    direct: HashMap<LocalId, Place>,
}

impl ReborrowMap {
    /// Build the reborrow map by scanning all `Rvalue::Ref` assignments
    /// in the body. If a local is assigned more than once with
    /// `Rvalue::Ref`, drop it from the map: it is reassigned mid-flow
    /// and resolution would be unsound.
    pub(crate) fn from_body(body: &Body) -> Self {
        let mut direct: HashMap<LocalId, Place> = HashMap::new();
        let mut excluded = std::collections::HashSet::<LocalId>::new();

        for block in &body.blocks {
            for stmt in &block.statements {
                if let Stmt::Assign {
                    place: Place::Local(ref_local),
                    rvalue: Rvalue::Ref { place, .. },
                } = stmt
                {
                    if excluded.contains(ref_local) {
                        continue;
                    }
                    if direct.contains_key(ref_local) {
                        // Reassigned: ambiguous, drop from map.
                        direct.remove(ref_local);
                        excluded.insert(*ref_local);
                        continue;
                    }
                    direct.insert(*ref_local, place.clone());
                }
            }
        }

        Self { direct }
    }

    /// Resolve a place by inlining each `Deref(Local(L))` with the
    /// place that `L` borrowed at its ref-assignment, recursively.
    ///
    /// Cycle-safe: a `visited` set guards against the (degenerate)
    /// case of a local that transitively reborrows itself.
    pub(crate) fn resolve(&self, place: &Place) -> Place {
        let mut visited = std::collections::HashSet::new();
        self.resolve_inner(place, &mut visited)
    }

    /// True if `place` syntactically dereferences `target_local` at any
    /// nesting level — that is, the borrow whose place is `place` is a
    /// reborrow chain starting from `target_local`'s referent. Used to
    /// suppress reborrow-vs-parent conflict reports.
    pub(crate) fn place_reborrows_local(&self, place: &Place, target_local: LocalId) -> bool {
        let mut visited = std::collections::HashSet::new();
        self.place_reborrows_local_inner(place, target_local, &mut visited)
    }

    fn place_reborrows_local_inner(
        &self,
        place: &Place,
        target_local: LocalId,
        visited: &mut std::collections::HashSet<LocalId>,
    ) -> bool {
        match place {
            Place::Local(_) | Place::Static(_) => false,
            Place::Field { base, .. }
            | Place::Index { base, .. }
            | Place::Downcast { base, .. } => {
                self.place_reborrows_local_inner(base, target_local, visited)
            }
            Place::Deref(base) => {
                if let Place::Local(local) = base.as_ref() {
                    if *local == target_local {
                        return true;
                    }
                    if !visited.contains(local) {
                        if let Some(borrowed) = self.direct.get(local) {
                            visited.insert(*local);
                            let recurse =
                                self.place_reborrows_local_inner(borrowed, target_local, visited);
                            visited.remove(local);
                            return recurse;
                        }
                    }
                }
                self.place_reborrows_local_inner(base, target_local, visited)
            }
        }
    }

    fn resolve_inner(
        &self,
        place: &Place,
        visited: &mut std::collections::HashSet<LocalId>,
    ) -> Place {
        match place {
            Place::Local(_) | Place::Static(_) => place.clone(),
            Place::Field { base, field } => Place::Field {
                base: Box::new(self.resolve_inner(base, visited)),
                field: field.clone(),
            },
            Place::Index { base, index } => Place::Index {
                base: Box::new(self.resolve_inner(base, visited)),
                index: index.clone(),
            },
            Place::Downcast { base, variant } => Place::Downcast {
                base: Box::new(self.resolve_inner(base, visited)),
                variant: variant.clone(),
            },
            Place::Deref(base) => {
                // If the deref'd place is exactly a Local, and that
                // local is in the reborrow map, splice the borrowed
                // place in (recursively resolved).
                if let Place::Local(local) = base.as_ref() {
                    if !visited.contains(local) {
                        if let Some(borrowed) = self.direct.get(local) {
                            visited.insert(*local);
                            let resolved = self.resolve_inner(borrowed, visited);
                            visited.remove(local);
                            return resolved;
                        }
                    }
                }
                Place::Deref(Box::new(self.resolve_inner(base, visited)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Mutability as TyMut, RustType, UintType};
    use crate::vir::{BasicBlock, BorrowKind, LocalDecl, Rvalue, Stmt as VirStmt, Term};

    fn u32_local(body: &mut Body, name: &str) -> LocalId {
        body.add_local(
            LocalDecl::new(RustType::Uint(UintType::U32), TyMut::Mutable).with_name(name),
        )
    }

    fn ref_local(body: &mut Body, name: &str) -> LocalId {
        body.add_local(
            LocalDecl::new(
                RustType::Reference {
                    lifetime: crate::types::Lifetime::Anonymous(0),
                    mutability: TyMut::Shared,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                },
                TyMut::Mutable,
            )
            .with_name(name),
        )
    }

    #[test]
    fn resolve_identity_for_non_deref_place() {
        let map = ReborrowMap::default();
        let place = Place::Field {
            base: Box::new(Place::Local(7)),
            field: "x".into(),
        };
        assert_eq!(map.resolve(&place), place);
    }

    #[test]
    fn resolve_splices_single_deref_into_borrowed_place() {
        let mut body = Body::new();
        let x = u32_local(&mut body, "x");
        let r = ref_local(&mut body, "r");
        let mut bb0 = BasicBlock::new(Term::Return);
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Local(x),
            },
        });
        body.add_block(bb0);

        let map = ReborrowMap::from_body(&body);
        // `Deref(Local(r))` should resolve to `Local(x)`.
        let deref_r = Place::Deref(Box::new(Place::Local(r)));
        assert_eq!(map.resolve(&deref_r), Place::Local(x));
    }

    #[test]
    fn resolve_splices_field_through_deref() {
        let mut body = Body::new();
        let c = u32_local(&mut body, "c");
        let r = ref_local(&mut body, "r");
        let mut bb0 = BasicBlock::new(Term::Return);
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Field {
                    base: Box::new(Place::Local(c)),
                    field: "value".into(),
                },
            },
        });
        body.add_block(bb0);

        let map = ReborrowMap::from_body(&body);
        // Reborrow chain `_2 = &(*r)` looks like `Deref(Local(r))`;
        // after resolution it should equal `Field(Local(c), "value")`.
        let deref_r = Place::Deref(Box::new(Place::Local(r)));
        let expected = Place::Field {
            base: Box::new(Place::Local(c)),
            field: "value".into(),
        };
        assert_eq!(map.resolve(&deref_r), expected);
    }

    #[test]
    fn resolve_recursive_through_reborrow_chain() {
        // _3 = &c.value, _2 = &(*_3). Resolving Deref(_2) should reach
        // c.value through both hops.
        let mut body = Body::new();
        let c = u32_local(&mut body, "c");
        let r3 = ref_local(&mut body, "r3");
        let r2 = ref_local(&mut body, "r2");
        let mut bb0 = BasicBlock::new(Term::Return);
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r3),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Field {
                    base: Box::new(Place::Local(c)),
                    field: "value".into(),
                },
            },
        });
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r2),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Deref(Box::new(Place::Local(r3))),
            },
        });
        body.add_block(bb0);

        let map = ReborrowMap::from_body(&body);
        let deref_r2 = Place::Deref(Box::new(Place::Local(r2)));
        let expected = Place::Field {
            base: Box::new(Place::Local(c)),
            field: "value".into(),
        };
        assert_eq!(map.resolve(&deref_r2), expected);
    }

    #[test]
    fn resolve_leaves_unknown_deref_untouched() {
        // Local 99 is not in the map; resolution must not invent.
        let body = Body::new();
        let map = ReborrowMap::from_body(&body);
        let deref = Place::Deref(Box::new(Place::Local(99)));
        assert_eq!(map.resolve(&deref), deref);
    }

    #[test]
    fn place_reborrows_local_direct() {
        let body = Body::new();
        let map = ReborrowMap::from_body(&body);
        let deref_5 = Place::Deref(Box::new(Place::Local(5)));
        assert!(map.place_reborrows_local(&deref_5, 5));
        assert!(!map.place_reborrows_local(&deref_5, 6));
    }

    #[test]
    fn place_reborrows_local_through_chain() {
        // _3 = &x, _4 = &mut (*_3). place_reborrows_local for the
        // place Deref(Local(4)) and target_local=3 must be true,
        // because 4 reborrows from 3.
        let mut body = Body::new();
        let x = u32_local(&mut body, "x");
        let r3 = ref_local(&mut body, "r3");
        let r4 = ref_local(&mut body, "r4");
        let mut bb0 = BasicBlock::new(Term::Return);
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r3),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Local(x),
            },
        });
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r4),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Deref(Box::new(Place::Local(r3))),
            },
        });
        body.add_block(bb0);

        let map = ReborrowMap::from_body(&body);
        let deref_r4 = Place::Deref(Box::new(Place::Local(r4)));
        assert!(map.place_reborrows_local(&deref_r4, r3));
        // r4 does NOT borrow through some unrelated local.
        assert!(!map.place_reborrows_local(&deref_r4, 99));
    }

    #[test]
    fn resolve_drops_local_with_multiple_ref_assignments() {
        // If `r` is reassigned with a different rvalue::Ref, drop it
        // from the map — resolution would be ambiguous.
        let mut body = Body::new();
        let x = u32_local(&mut body, "x");
        let y = u32_local(&mut body, "y");
        let r = ref_local(&mut body, "r");
        let mut bb0 = BasicBlock::new(Term::Return);
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Local(x),
            },
        });
        bb0.add_statement(VirStmt::Assign {
            place: Place::Local(r),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: Place::Local(y),
            },
        });
        body.add_block(bb0);

        let map = ReborrowMap::from_body(&body);
        let deref_r = Place::Deref(Box::new(Place::Local(r)));
        // Multiple assignments: resolution must NOT splice.
        assert_eq!(map.resolve(&deref_r), deref_r);
    }
}
