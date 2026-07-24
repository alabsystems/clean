// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Ownership and Borrowing Model
//!
//! This module formalizes Rust's ownership system, which is central to
//! memory safety without garbage collection.
//!
//! ## Core Rules
//!
//! 1. **Ownership**: Each value has exactly one owner
//! 2. **Move Semantics**: When ownership is transferred, the source is invalidated
//! 3. **Borrowing**: References can borrow values temporarily
//! 4. **Borrow Rules**:
//!    - Any number of shared references (&T), OR
//!    - Exactly one mutable reference (&mut T)
//!    - References cannot outlive the referent
//!
//! ## Places and Projections
//!
//! A "place" is a location in memory that can hold a value:
//! - Local variables
//! - Static variables
//! - Heap allocations
//! - Fields of structs
//! - Elements of arrays/vectors

use crate::stacked_borrows::{
    AccessKind, AliasingDiscipline, BorrowPermission, BorrowStackEntry, BorrowTag, ProtectorId,
    StackedBorrows,
};
use crate::types::{Lifetime, Mutability};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

mod analysis;
mod error;
#[cfg(test)]
mod tests;

pub use analysis::{BorrowChecker, DropElaborator, MoveAnalysis};
use error::map_aliasing_error;
pub use error::BorrowError;

/// Runtime aliasing model variant (Stacked Borrows vs Tree Borrows).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AliasingModel {
    #[default]
    StackedBorrows,
    TreeBorrows,
}

impl AliasingModel {
    fn discipline(self) -> AliasingDiscipline {
        match self {
            AliasingModel::StackedBorrows => AliasingDiscipline::StackedBorrows,
            AliasingModel::TreeBorrows => AliasingDiscipline::TreeBorrows,
        }
    }
}

/// A place expression (lvalue) representing a memory location
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Place {
    /// Local variable by index
    Local(u32),
    /// Static variable by name
    Static(String),
    /// Field projection: base.field
    Field { base: Box<Place>, field: String },
    /// Array/slice index: `base[index]`
    Index { base: Box<Place>, index: Box<Place> },
    /// Dereference: *base
    Deref(Box<Place>),
    /// Downcast enum variant: base as Variant
    Downcast { base: Box<Place>, variant: String },
}

impl Place {
    /// Create a local variable place
    pub fn local(index: u32) -> Self {
        Place::Local(index)
    }

    /// Create a field projection
    #[must_use]
    pub fn field(self, name: &str) -> Self {
        Place::Field {
            base: Box::new(self),
            field: name.to_string(),
        }
    }

    /// Create a dereference
    #[must_use]
    pub fn deref(self) -> Self {
        Place::Deref(Box::new(self))
    }

    /// Get the base place (without projections)
    pub fn base(&self) -> &Place {
        match self {
            Place::Local(_) | Place::Static(_) => self,
            Place::Field { base, .. }
            | Place::Index { base, .. }
            | Place::Deref(base)
            | Place::Downcast { base, .. } => base.base(),
        }
    }

    /// Check if this place is a prefix of another within the same memory object.
    ///
    /// Prefix relationships stop at dereference boundaries: `p` and `*p`
    /// refer to different memory objects, while `*p` and `(*p).field` share
    /// the same referent.
    pub fn is_prefix_of(&self, other: &Place) -> bool {
        if self == other {
            return true;
        }
        match other {
            Place::Field { base, .. }
            | Place::Index { base, .. }
            | Place::Downcast { base, .. } => self.is_prefix_of(base),
            Place::Deref(other_base) => match self {
                Place::Deref(self_base) => self_base.is_prefix_of(other_base),
                _ => false,
            },
            _ => false,
        }
    }

    /// Check if two places conflict (overlap in memory)
    pub fn conflicts_with(&self, other: &Place) -> bool {
        self.is_prefix_of(other) || other.is_prefix_of(self)
    }
}

/// Borrow information
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Borrow {
    /// The place being borrowed
    pub place: Place,
    /// Whether the borrow is mutable
    pub mutability: Mutability,
    /// Lifetime of the borrow
    pub lifetime: Lifetime,
    /// Point in the program where borrow was created
    pub origin: u32,
    /// Runtime borrow-stack tag created for this borrow.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tag: Option<BorrowTag>,
    /// Protector token if this borrow is protected for a call frame.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub protector: Option<ProtectorId>,
}

/// Ownership state for a single place
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PlaceState {
    /// Place is owned and valid
    Owned,
    /// Place has been moved out
    Moved,
    /// Place is partially moved (some fields moved)
    PartiallyMoved,
    /// Place is borrowed (immutably)
    SharedBorrowed,
    /// Place is borrowed (mutably)
    MutBorrowed,
    /// Place is uninitialized
    Uninitialized,
}

/// State of all places and borrows at a program point
#[derive(Debug, Clone, Default)]
pub struct OwnershipState {
    /// State of each place
    place_states: HashMap<Place, PlaceState>,
    /// Active borrows
    active_borrows: Vec<Borrow>,
    /// Counter for borrow origins
    borrow_counter: u32,
    /// Stacked-borrows runtime state keyed by semantic place.
    stacked_borrows: StackedBorrows<Place>,
    /// Root owner tag for each tracked place.
    place_roots: HashMap<Place, BorrowTag>,
    /// Current active tag for each tracked place.
    place_tags: HashMap<Place, BorrowTag>,
    /// Active aliasing discipline applied to access validation.
    aliasing_model: AliasingModel,
}

impl OwnershipState {
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark a place as owned
    pub fn mark_owned(&mut self, place: Place) {
        let root = self.ensure_root_tag(&place);
        self.place_tags.insert(place.clone(), root);
        self.place_states.insert(place, PlaceState::Owned);
    }

    /// Mark a place as moved
    pub fn mark_moved(&mut self, place: Place) {
        self.place_states.insert(place, PlaceState::Moved);
    }

    /// Mark a place as uninitialized
    pub fn mark_uninitialized(&mut self, place: Place) {
        self.place_states.insert(place, PlaceState::Uninitialized);
    }

    /// Check if a place is owned
    pub fn is_owned(&self, place: &Place) -> bool {
        matches!(self.place_states.get(place), Some(PlaceState::Owned))
    }

    /// Check if a place is moved
    pub fn is_moved(&self, place: &Place) -> bool {
        matches!(self.place_states.get(place), Some(PlaceState::Moved))
    }

    /// Check if a place is borrowed (either shared or mutable)
    pub fn is_borrowed(&self, place: &Place) -> bool {
        matches!(
            self.place_states.get(place),
            Some(PlaceState::SharedBorrowed | PlaceState::MutBorrowed)
        )
    }

    /// Check if a place is initialized and accessible
    pub fn is_accessible(&self, place: &Place) -> bool {
        matches!(
            self.place_states.get(place),
            Some(PlaceState::Owned | PlaceState::SharedBorrowed)
        )
    }

    /// Add a borrow
    pub fn add_borrow(
        &mut self,
        place: Place,
        mutability: Mutability,
        lifetime: Lifetime,
    ) -> Result<BorrowTag, BorrowError> {
        self.add_borrow_with_protector(place, mutability, lifetime, None)
    }

    /// Add a protected borrow that cannot be invalidated until its protector is released.
    pub fn add_borrow_with_protector(
        &mut self,
        place: Place,
        mutability: Mutability,
        lifetime: Lifetime,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, BorrowError> {
        let tag = self.retag_place(
            &place,
            match mutability {
                Mutability::Shared => BorrowPermission::SharedReadOnly,
                Mutability::Mutable => BorrowPermission::Unique,
            },
            protector,
        )?;
        let borrow = Borrow {
            place: place.clone(),
            mutability,
            lifetime,
            origin: self.borrow_counter,
            tag: Some(tag),
            protector,
        };
        self.borrow_counter += 1;

        let new_state = match mutability {
            Mutability::Shared => PlaceState::SharedBorrowed,
            Mutability::Mutable => PlaceState::MutBorrowed,
        };
        self.place_states.insert(place, new_state);
        self.active_borrows.push(borrow);
        Ok(tag)
    }

    /// End borrows with the given lifetime
    pub fn end_borrows(&mut self, lifetime: &Lifetime) {
        let ended: Vec<_> = self
            .active_borrows
            .iter()
            .filter(|b| &b.lifetime == lifetime)
            .cloned()
            .collect();

        self.active_borrows.retain(|b| &b.lifetime != lifetime);

        let mut ended_places = HashSet::new();
        for borrow in &ended {
            ended_places.insert(borrow.place.clone());
            if let Some(protector) = borrow.protector {
                self.stacked_borrows.release_protector(protector);
            }
        }

        // Restore owned state and current tags for places whose borrows ended.
        for place in ended_places {
            if let Some(active) = self.active_borrows.iter().rev().find(|b| b.place == place) {
                let state = match active.mutability {
                    Mutability::Shared => PlaceState::SharedBorrowed,
                    Mutability::Mutable => PlaceState::MutBorrowed,
                };
                self.place_states.insert(place.clone(), state);
                if let Some(tag) = active.tag {
                    self.place_tags.insert(place, tag);
                }
            } else {
                self.place_states.insert(place.clone(), PlaceState::Owned);
                if let Some(root) = self.place_roots.get(&place).copied() {
                    self.place_tags.insert(place, root);
                }
            }
        }
    }

    /// Return the current borrow-stack tag for a place.
    pub fn borrow_tag(&self, place: &Place) -> Option<BorrowTag> {
        self.place_tags.get(place).copied()
    }

    /// Return the current tag for a place, falling back to its root tag.
    ///
    /// This is useful for direct owner writes to a place that has tracked
    /// descendants but has not itself been explicitly retagged yet.
    pub fn current_or_root_tag(&mut self, place: &Place) -> BorrowTag {
        self.borrow_tag(place)
            .unwrap_or_else(|| self.ensure_root_tag(place))
    }

    /// Return the owner/root tag for a place.
    pub fn root_tag(&self, place: &Place) -> Option<BorrowTag> {
        self.place_roots.get(place).copied()
    }

    /// View the current stacked-borrows stack for a place.
    pub fn borrow_stack(&self, place: &Place) -> Option<&[BorrowStackEntry]> {
        self.stacked_borrows.stack(place)
    }

    /// Allocate a fresh protector token.
    pub fn new_protector(&mut self) -> ProtectorId {
        self.stacked_borrows.new_protector()
    }

    /// Protect an existing tag from invalidation.
    pub fn protect_tag(
        &mut self,
        place: &Place,
        tag: BorrowTag,
        protector: ProtectorId,
    ) -> Result<(), BorrowError> {
        self.stacked_borrows
            .protect_tag(place, tag, protector)
            .map_err(map_aliasing_error)
    }

    /// Release a protector token on all tracked borrows.
    pub fn release_protector(&mut self, protector: ProtectorId) {
        self.stacked_borrows.release_protector(protector);
    }

    /// Retag a place under stacked borrows and make the new tag current.
    pub fn retag_place(
        &mut self,
        place: &Place,
        permission: BorrowPermission,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, BorrowError> {
        let parent = self
            .borrow_tag(place)
            .unwrap_or_else(|| self.ensure_root_tag(place));
        let tag = self
            .stacked_borrows
            .retag(place, parent, permission, protector)
            .map_err(map_aliasing_error)?;
        self.place_tags.insert(place.clone(), tag);
        Ok(tag)
    }

    /// Validate a concrete access and update the current tag to the accessor.
    pub fn access_place(
        &mut self,
        place: &Place,
        tag: BorrowTag,
        access: AccessKind,
    ) -> Result<(), BorrowError> {
        self.access_place_exact(place, tag, access)
    }

    /// Validate an access against the exact tracked place only.
    fn access_place_exact(
        &mut self,
        place: &Place,
        tag: BorrowTag,
        access: AccessKind,
    ) -> Result<(), BorrowError> {
        self.stacked_borrows
            .access_with_model(place, tag, access, self.aliasing_model.discipline())
            .map_err(map_aliasing_error)?;
        self.place_tags.insert(place.clone(), tag);
        Ok(())
    }

    /// Validate an access that semantically writes the entire place.
    ///
    /// Whole-place writes must also invalidate derived tags on tracked
    /// descendants such as `s.x` when writing `s`.
    pub fn access_whole_place(
        &mut self,
        place: &Place,
        tag: BorrowTag,
        access: AccessKind,
    ) -> Result<(), BorrowError> {
        let mut preview = self.clone();
        preview.access_place_exact(place, tag, access)?;

        if access == AccessKind::Write {
            let descendants: Vec<_> = self
                .place_roots
                .keys()
                .filter(|candidate| **candidate != *place && place.is_prefix_of(candidate))
                .cloned()
                .collect();
            for descendant in descendants {
                // A whole-place overwrite must invalidate any derived
                // descendant reborrows, so the descendant access uses its
                // owner/root capability rather than the current derived tag.
                let descendant_tag = preview
                    .root_tag(&descendant)
                    .unwrap_or_else(|| preview.ensure_root_tag(&descendant));
                preview.access_place_exact(&descendant, descendant_tag, access)?;
            }
        }

        *self = preview;
        Ok(())
    }

    fn ensure_root_tag(&mut self, place: &Place) -> BorrowTag {
        let root = self.stacked_borrows.ensure_base(place.clone());
        self.place_roots.entry(place.clone()).or_insert(root);
        root
    }

    /// Get all active borrows of a place
    pub fn borrows_of(&self, place: &Place) -> Vec<&Borrow> {
        self.active_borrows
            .iter()
            .filter(|b| b.place.conflicts_with(place))
            .collect()
    }

    /// Check if a mutable borrow is active on a place
    pub fn has_mutable_borrow(&self, place: &Place) -> bool {
        self.active_borrows
            .iter()
            .any(|b| b.mutability == Mutability::Mutable && b.place.conflicts_with(place))
    }

    /// Check if any borrow is active on a place
    pub fn has_any_borrow(&self, place: &Place) -> bool {
        self.active_borrows
            .iter()
            .any(|b| b.place.conflicts_with(place))
    }

    /// Set the active aliasing model used by access validation.
    ///
    /// Under [`AliasingModel::TreeBorrows`] a write through a raw-pointer
    /// capability keeps sibling raw pointers live (see
    /// [`StackedBorrows::access_with_model`]); under
    /// [`AliasingModel::StackedBorrows`] every conflicting entry above the
    /// writer is invalidated.
    pub fn set_aliasing_model(&mut self, model: AliasingModel) {
        self.aliasing_model = model;
    }

    /// Return the active aliasing model.
    pub fn aliasing_model(&self) -> AliasingModel {
        self.aliasing_model
    }

    /// Reserve a two-phase mutable borrow on a place.
    pub fn reserve_mut_place(
        &mut self,
        place: &Place,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, BorrowError> {
        self.retag_place(place, BorrowPermission::Unique, protector)
    }

    /// Activate a previously reserved two-phase mutable borrow.
    pub fn activate_mut_place(
        &mut self,
        place: &Place,
        _reservation_tag: BorrowTag,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, BorrowError> {
        self.retag_place(place, BorrowPermission::Unique, protector)
    }

    /// Query the permission held by a tag on a place, if any.
    pub fn borrow_permission(&self, place: &Place, tag: BorrowTag) -> Option<BorrowPermission> {
        self.stacked_borrows.permission(place, tag)
    }

    /// Retag a place starting from a specific parent tag.
    pub fn retag_place_from_tag(
        &mut self,
        place: &Place,
        parent: BorrowTag,
        permission: BorrowPermission,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, BorrowError> {
        let tag = self
            .stacked_borrows
            .retag(place, parent, permission, protector)
            .map_err(map_aliasing_error)?;
        self.place_tags.insert(place.clone(), tag);
        Ok(tag)
    }
}
