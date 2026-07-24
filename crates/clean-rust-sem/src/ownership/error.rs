// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::Place;
use crate::stacked_borrows::{AccessKind, BorrowTag, StackedBorrowsError};
use crate::types::Lifetime;
use thiserror::Error;

/// Borrow check errors (Rust ownership violations)
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum BorrowError {
    /// Attempted to move value while an outstanding borrow exists
    #[error("cannot move out of `{place:?}`: value is borrowed")]
    MoveWhileBorrowed {
        /// The place being moved
        place: Place,
    },

    /// Attempted to create mutable borrow while shared borrows exist
    #[error("cannot borrow `{place:?}` as mutable: already borrowed as immutable")]
    MutBorrowWhileSharedBorrow {
        /// The place being borrowed
        place: Place,
    },

    /// Attempted to create second mutable borrow (violates exclusive access)
    #[error("cannot borrow `{place:?}` as mutable: already borrowed as mutable")]
    MutBorrowWhileMutBorrow {
        /// The place being borrowed
        place: Place,
    },

    /// Attempted to create shared borrow while mutable borrow exists
    #[error("cannot borrow `{place:?}` as immutable: already borrowed as mutable")]
    SharedBorrowWhileMutBorrow {
        /// The place being borrowed
        place: Place,
    },

    /// Attempted to use value after ownership was transferred
    #[error("use of moved value: `{place:?}`")]
    UseAfterMove {
        /// The moved place
        place: Place,
    },

    /// Attempted to use value before initialization
    #[error("use of uninitialized value: `{place:?}`")]
    UseOfUninitialized {
        /// The uninitialized place
        place: Place,
    },

    /// Attempted to assign to immutable binding or through shared reference
    #[error("cannot assign to `{place:?}`: not mutable")]
    AssignToImmutable {
        /// The immutable place
        place: Place,
    },

    /// Attempted to assign while an outstanding borrow exists
    #[error("cannot assign to `{place:?}`: borrowed")]
    AssignWhileBorrowed {
        /// The borrowed place
        place: Place,
    },

    /// Reference lifetime does not satisfy outlives requirement
    #[error("lifetime `{lifetime:?}` does not outlive `{required:?}`")]
    LifetimeTooShort {
        /// The actual lifetime of the reference
        lifetime: Lifetime,
        /// The required lifetime (e.g., from function signature)
        required: Lifetime,
    },

    /// Attempted to return reference to stack-allocated local
    #[error("cannot return reference to local variable")]
    ReturnLocalRef {
        /// The local variable place
        place: Place,
    },

    /// Attempted to use a place without a stacked-borrows root.
    #[error("stacked borrows does not track `{place:?}`")]
    AliasingLocationMissing {
        /// The missing place.
        place: Place,
    },

    /// Attempted to derive a borrow tag from a missing parent tag.
    #[error("cannot retag `{place:?}` from missing parent {parent:?}")]
    AliasingParentMissing {
        /// The place being retagged.
        place: Place,
        /// The missing parent tag.
        parent: BorrowTag,
    },

    /// Attempted to access a place with a tag that is no longer live.
    #[error("tag {tag:?} is not live for `{place:?}`")]
    AliasingUnknownTag {
        /// The accessed place.
        place: Place,
        /// The unknown tag.
        tag: BorrowTag,
    },

    /// Attempted an access that the tag's permission does not allow.
    #[error("tag {tag:?} cannot perform {access:?} on `{place:?}`")]
    AliasingInvalidAccess {
        /// The accessed place.
        place: Place,
        /// The accessing tag.
        tag: BorrowTag,
        /// The rejected access kind.
        access: AccessKind,
    },

    /// Attempted an access that would invalidate a protected tag.
    #[error(
        "tag {tag:?} cannot perform {access:?} on `{place:?}` because protected tag {blocked_by:?} would be invalidated"
    )]
    AliasingProtected {
        /// The accessed place.
        place: Place,
        /// The accessing tag.
        tag: BorrowTag,
        /// The rejected access kind.
        access: AccessKind,
        /// The protected tag that blocked the access.
        blocked_by: BorrowTag,
    },
}

pub(crate) fn map_aliasing_error(error: StackedBorrowsError<Place>) -> BorrowError {
    match error {
        StackedBorrowsError::UnknownLocation { location } => {
            BorrowError::AliasingLocationMissing { place: location }
        }
        StackedBorrowsError::UnknownTag { location, tag } => BorrowError::AliasingUnknownTag {
            place: location,
            tag,
        },
        StackedBorrowsError::MissingParent { location, parent } => {
            BorrowError::AliasingParentMissing {
                place: location,
                parent,
            }
        }
        StackedBorrowsError::IncompatibleAccess {
            location,
            tag,
            access,
        } => BorrowError::AliasingInvalidAccess {
            place: location,
            tag,
            access,
        },
        StackedBorrowsError::ProtectedConflict {
            location,
            tag,
            access,
            blocked_by,
        } => BorrowError::AliasingProtected {
            place: location,
            tag,
            access,
            blocked_by,
        },
    }
}
