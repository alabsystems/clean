// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stacked Borrows aliasing model primitives.
//!
//! This models the core runtime alias discipline from Stacked Borrows:
//! per-location borrow stacks, retagging, incompatible-access popping, and
//! protectors that block invalidation while a call is active.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use thiserror::Error;

#[cfg(test)]
mod tests;

/// Fresh identity for a borrow stack item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BorrowTag(pub u64);

/// Protector token for function-call style protected borrows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProtectorId(pub u64);

/// Access kind validated against a borrow stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AccessKind {
    Read,
    Write,
}

/// Aliasing discipline applied when validating an access.
///
/// The borrow stack representation is shared between disciplines; the variant
/// only changes which sibling entries a write invalidates (see
/// [`StackedBorrows::access_with_model`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AliasingDiscipline {
    /// Standard Stacked Borrows: a write pops every conflicting entry above
    /// the writer.
    StackedBorrows,
    /// Tree Borrows: a write through a raw-pointer (`SharedReadWrite`)
    /// capability keeps sibling raw-pointer entries live.
    TreeBorrows,
}

/// Permission carried by a stacked-borrows item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BorrowPermission {
    /// Exclusive reference or owner capability.
    Unique,
    /// Raw-pointer-style shared read/write capability.
    SharedReadWrite,
    /// Shared reference capability.
    SharedReadOnly,
    /// Revoked capability — the tag persists on the stack but cannot perform
    /// any access.  Used when a foreign read demotes a `Unique` entry instead
    /// of popping it outright (Miri semantics), and for two-phase borrow
    /// reservations that have been deactivated.
    Disabled,
}

impl BorrowPermission {
    /// Whether this permission supports writes by the tagged capability itself.
    pub fn allows_write(self) -> bool {
        matches!(self, Self::Unique | Self::SharedReadWrite)
    }

    /// Whether this permission supports reads by the tagged capability itself.
    pub fn allows_read(self) -> bool {
        !matches!(self, Self::Disabled)
    }

    fn conflicts_with(self, access: AccessKind) -> bool {
        match access {
            // Disabled entries do not conflict — they are already dead and
            // need not be popped again.
            AccessKind::Read => matches!(self, Self::Unique),
            AccessKind::Write => !matches!(self, Self::Disabled),
        }
    }
}

/// One item in a location's borrow stack.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BorrowStackEntry {
    pub tag: BorrowTag,
    pub permission: BorrowPermission,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub protector: Option<ProtectorId>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent: Option<BorrowTag>,
}

impl BorrowStackEntry {
    fn root(tag: BorrowTag) -> Self {
        Self {
            tag,
            permission: BorrowPermission::Unique,
            protector: None,
            parent: None,
        }
    }
}

#[derive(Debug, Clone, Default)]
struct BorrowStack {
    entries: Vec<BorrowStackEntry>,
}

impl BorrowStack {
    fn root_tag(&self) -> Option<BorrowTag> {
        self.entries.first().map(|entry| entry.tag)
    }

    fn contains_tag(&self, tag: BorrowTag) -> bool {
        self.entries.iter().any(|entry| entry.tag == tag)
    }

    fn find_index(&self, tag: BorrowTag) -> Option<usize> {
        self.entries.iter().position(|entry| entry.tag == tag)
    }

    fn entry_mut(&mut self, tag: BorrowTag) -> Option<&mut BorrowStackEntry> {
        self.entries.iter_mut().find(|entry| entry.tag == tag)
    }

    fn items(&self) -> &[BorrowStackEntry] {
        &self.entries
    }

    fn tag_permission(&self, tag: BorrowTag) -> Option<BorrowPermission> {
        self.entries
            .iter()
            .find(|entry| entry.tag == tag)
            .map(|entry| entry.permission)
    }
}

/// Errors from stacked-borrows validation.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum StackedBorrowsError<L: Debug> {
    #[error("location {location:?} does not have a borrow stack")]
    UnknownLocation { location: L },

    #[error("tag {tag:?} does not exist in location {location:?}")]
    UnknownTag { location: L, tag: BorrowTag },

    #[error("cannot derive a new tag from parent {parent:?} at location {location:?}")]
    MissingParent { location: L, parent: BorrowTag },

    #[error("tag {tag:?} cannot perform {access:?} at location {location:?}")]
    IncompatibleAccess {
        location: L,
        tag: BorrowTag,
        access: AccessKind,
    },

    #[error(
        "tag {tag:?} cannot perform {access:?} at location {location:?} because protected tag {blocked_by:?} would be invalidated"
    )]
    ProtectedConflict {
        location: L,
        tag: BorrowTag,
        access: AccessKind,
        blocked_by: BorrowTag,
    },
}

/// Per-location stacked-borrows state.
#[derive(Debug, Clone)]
pub struct StackedBorrows<L> {
    locations: HashMap<L, BorrowStack>,
    next_tag: u64,
    next_protector: u64,
}

impl<L> StackedBorrows<L>
where
    L: Clone + Debug + Eq + Hash,
{
    pub fn new() -> Self {
        Self {
            locations: HashMap::new(),
            next_tag: 1,
            next_protector: 1,
        }
    }

    /// Ensure a location has a root tag and return it.
    pub fn ensure_base(&mut self, location: L) -> BorrowTag {
        if let Some(stack) = self.locations.get(&location) {
            return stack
                .root_tag()
                .expect("invariant: non-empty borrow stack has a root tag");
        }

        let tag = self.fresh_tag();
        self.locations.insert(
            location,
            BorrowStack {
                entries: vec![BorrowStackEntry::root(tag)],
            },
        );
        tag
    }

    /// Return the root tag for a location if it exists.
    pub fn root_tag(&self, location: &L) -> Option<BorrowTag> {
        self.locations.get(location).and_then(BorrowStack::root_tag)
    }

    /// Return the current stack for a location.
    pub fn stack(&self, location: &L) -> Option<&[BorrowStackEntry]> {
        self.locations.get(location).map(BorrowStack::items)
    }

    /// Look up the permission of a specific tag on a location, if live.
    pub fn permission(&self, location: &L, tag: BorrowTag) -> Option<BorrowPermission> {
        self.locations
            .get(location)
            .and_then(|stack| stack.tag_permission(tag))
    }

    /// Check whether a given tag is still live in the stack for a location.
    pub fn contains_tag(&self, location: &L, tag: BorrowTag) -> bool {
        self.locations
            .get(location)
            .is_some_and(|stack| stack.contains_tag(tag))
    }

    /// Allocate a fresh protector token.
    pub fn new_protector(&mut self) -> ProtectorId {
        let protector = ProtectorId(self.next_protector);
        self.next_protector += 1;
        protector
    }

    /// Add a protector to an existing tag.
    pub fn protect_tag(
        &mut self,
        location: &L,
        tag: BorrowTag,
        protector: ProtectorId,
    ) -> Result<(), StackedBorrowsError<L>> {
        let location_key = location.clone();
        let stack = self.locations.get_mut(location).ok_or_else(|| {
            StackedBorrowsError::UnknownLocation {
                location: location_key.clone(),
            }
        })?;
        let entry = stack
            .entry_mut(tag)
            .ok_or_else(|| StackedBorrowsError::UnknownTag {
                location: location_key,
                tag,
            })?;
        entry.protector = Some(protector);
        Ok(())
    }

    /// Remove a protector token from every stack item that carries it.
    pub fn release_protector(&mut self, protector: ProtectorId) {
        for stack in self.locations.values_mut() {
            for entry in &mut stack.entries {
                if entry.protector == Some(protector) {
                    entry.protector = None;
                }
            }
        }
    }

    /// Derive a new tag from an existing parent.
    ///
    /// Following Miri's Stacked Borrows semantics, retagging invalidates
    /// entries above the parent that are incompatible with the new permission:
    /// - `Unique` retag: pop all entries above the parent.
    /// - `SharedReadOnly` retag: pop all `Unique` entries above the parent.
    /// - `SharedReadWrite` retag: no invalidation.
    ///
    /// Protected entries cannot be invalidated; attempting to do so returns
    /// a `ProtectedConflict` error.
    pub fn retag(
        &mut self,
        location: &L,
        parent: BorrowTag,
        permission: BorrowPermission,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, StackedBorrowsError<L>> {
        let location_key = location.clone();
        let Some(stack) = self.locations.get(location) else {
            return Err(StackedBorrowsError::UnknownLocation {
                location: location_key,
            });
        };

        let parent_idx =
            stack
                .find_index(parent)
                .ok_or_else(|| StackedBorrowsError::MissingParent {
                    location: location.clone(),
                    parent,
                })?;

        // Determine which entries above the parent must be invalidated.
        let to_pop: Vec<BorrowTag> = match permission {
            BorrowPermission::Unique => {
                let mut popped = Vec::new();
                for entry in stack.entries.iter().skip(parent_idx + 1) {
                    if entry.protector.is_some() {
                        return Err(StackedBorrowsError::ProtectedConflict {
                            location: location.clone(),
                            tag: parent,
                            access: AccessKind::Write,
                            blocked_by: entry.tag,
                        });
                    }
                    popped.push(entry.tag);
                }
                popped
            }
            BorrowPermission::SharedReadOnly => {
                let mut popped = Vec::new();
                for entry in stack.entries.iter().skip(parent_idx + 1) {
                    if entry.permission == BorrowPermission::Unique {
                        if entry.protector.is_some() {
                            return Err(StackedBorrowsError::ProtectedConflict {
                                location: location.clone(),
                                tag: parent,
                                access: AccessKind::Read,
                                blocked_by: entry.tag,
                            });
                        }
                        popped.push(entry.tag);
                    }
                }
                popped
            }
            BorrowPermission::SharedReadWrite | BorrowPermission::Disabled => Vec::new(),
        };

        let tag = self.fresh_tag();
        let stack = self
            .locations
            .get_mut(location)
            .expect("invariant: location existence was checked above");
        stack.entries.retain(|entry| !to_pop.contains(&entry.tag));
        stack.entries.push(BorrowStackEntry {
            tag,
            permission,
            protector,
            parent: Some(parent),
        });
        Ok(tag)
    }

    /// Validate an access and invalidate incompatible items above the accessed tag.
    ///
    /// For write accesses, incompatible entries above the writer are popped.
    /// For read accesses, `Unique` entries above the reader are transitioned
    /// to `Disabled` (following Miri semantics) rather than being popped
    /// outright — the tag persists on the stack but can no longer access memory.
    pub fn access(
        &mut self,
        location: &L,
        tag: BorrowTag,
        access: AccessKind,
    ) -> Result<(), StackedBorrowsError<L>> {
        self.access_with_model(location, tag, access, AliasingDiscipline::StackedBorrows)
    }

    /// Validate an access under a chosen aliasing discipline.
    ///
    /// Under [`AliasingDiscipline::StackedBorrows`] this is identical to
    /// [`Self::access`]. Under [`AliasingDiscipline::TreeBorrows`] a single
    /// relaxation applies: a write performed *through* a `SharedReadWrite`
    /// (raw-pointer) capability does not invalidate sibling `SharedReadWrite`
    /// entries above it. This models the Tree Borrows rule that multiple raw
    /// pointers derived from the same mutable parent are mutually compatible
    /// read/write aliases — writing through one keeps the others live.
    ///
    /// The relaxation is deliberately narrow: it never preserves a `Unique`
    /// (`&mut`) or `SharedReadOnly` (`&`) entry above the writer, and it does
    /// not apply when the writer itself holds an exclusive `Unique`
    /// capability (a `&mut` write still asserts exclusivity by popping every
    /// child). Protected entries continue to block invalidation in both
    /// disciplines, so genuinely-unsound aliasing is still rejected.
    pub fn access_with_model(
        &mut self,
        location: &L,
        tag: BorrowTag,
        access: AccessKind,
        discipline: AliasingDiscipline,
    ) -> Result<(), StackedBorrowsError<L>> {
        let location_key = location.clone();
        let stack = self.locations.get_mut(location).ok_or_else(|| {
            StackedBorrowsError::UnknownLocation {
                location: location_key.clone(),
            }
        })?;

        let index = stack
            .find_index(tag)
            .ok_or_else(|| StackedBorrowsError::UnknownTag {
                location: location_key.clone(),
                tag,
            })?;
        let permission = stack.entries[index].permission;

        match access {
            AccessKind::Write if !permission.allows_write() => {
                return Err(StackedBorrowsError::IncompatibleAccess {
                    location: location_key,
                    tag,
                    access,
                });
            }
            AccessKind::Read if !permission.allows_read() => {
                return Err(StackedBorrowsError::IncompatibleAccess {
                    location: location_key,
                    tag,
                    access,
                });
            }
            _ => {}
        }

        // Tree Borrows keeps sibling raw pointers live across writes through
        // one another, but only when the writer is itself a raw-pointer
        // (`SharedReadWrite`) capability.
        let relax_shared_rw = discipline == AliasingDiscipline::TreeBorrows
            && access == AccessKind::Write
            && permission == BorrowPermission::SharedReadWrite;

        // Collect tags that conflict with this access.
        let mut conflicting = Vec::new();
        for entry in stack.entries.iter().skip(index + 1) {
            if !entry.permission.conflicts_with(access) {
                continue;
            }
            if relax_shared_rw && entry.permission == BorrowPermission::SharedReadWrite {
                // Sibling raw pointer: under Tree Borrows it stays live.
                continue;
            }
            if entry.protector.is_some() {
                return Err(StackedBorrowsError::ProtectedConflict {
                    location: location.clone(),
                    tag,
                    access,
                    blocked_by: entry.tag,
                });
            }
            conflicting.push(entry.tag);
        }

        match access {
            AccessKind::Write => {
                // Writes pop conflicting entries entirely.
                stack
                    .entries
                    .retain(|entry| !conflicting.contains(&entry.tag));
            }
            AccessKind::Read => {
                // Reads transition conflicting Unique entries to Disabled.
                for entry in &mut stack.entries {
                    if conflicting.contains(&entry.tag) {
                        entry.permission = BorrowPermission::Disabled;
                    }
                }
            }
        }
        Ok(())
    }

    fn fresh_tag(&mut self) -> BorrowTag {
        let tag = BorrowTag(self.next_tag);
        self.next_tag += 1;
        tag
    }
}

impl<L> Default for StackedBorrows<L>
where
    L: Clone + Debug + Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}
