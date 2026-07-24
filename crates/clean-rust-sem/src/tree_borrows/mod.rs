// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tree Borrows aliasing model primitives.
//!
//! This models a single permission tree per allocation. Accesses traverse the
//! tree from the root to the accessing tag, updating ancestor permissions on
//! the path and applying foreign-access effects to every off-path subtree.

use crate::stacked_borrows::{AccessKind, BorrowPermission, BorrowTag, ProtectorId};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use thiserror::Error;

#[cfg(test)]
mod tests;

/// Runtime Tree Borrows permission for a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Permission {
    Reserved,
    Active,
    Frozen,
    Disabled,
}

/// Back-compat alias for the old public name.
pub type TreeBorrowState = Permission;

/// One node in a per-allocation Tree Borrows state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreeBorrowNode {
    pub tag: BorrowTag,
    pub permission: Permission,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub protector: Option<ProtectorId>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent: Option<BorrowTag>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub children: Vec<BorrowTag>,
}

impl TreeBorrowNode {
    fn root(tag: BorrowTag) -> Self {
        Self {
            tag,
            permission: Permission::Active,
            protector: None,
            parent: None,
            children: Vec::new(),
        }
    }
}

/// Tree Borrows state for one allocation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreeBorrowsState {
    root: BorrowTag,
    nodes: HashMap<BorrowTag, TreeBorrowNode>,
}

impl TreeBorrowsState {
    fn new(root: BorrowTag) -> Self {
        let mut nodes = HashMap::new();
        nodes.insert(root, TreeBorrowNode::root(root));
        Self { root, nodes }
    }

    pub fn root_tag(&self) -> BorrowTag {
        self.root
    }

    pub fn contains_tag(&self, tag: BorrowTag) -> bool {
        self.nodes.contains_key(&tag)
    }

    pub fn node(&self, tag: BorrowTag) -> Option<&TreeBorrowNode> {
        self.nodes.get(&tag)
    }

    pub fn permission(&self, tag: BorrowTag) -> Option<Permission> {
        self.node(tag).map(|node| node.permission)
    }

    fn node_mut(&mut self, tag: BorrowTag) -> Option<&mut TreeBorrowNode> {
        self.nodes.get_mut(&tag)
    }

    fn path_to(&self, tag: BorrowTag) -> Option<Vec<BorrowTag>> {
        let mut path = Vec::new();
        let mut current = Some(tag);
        while let Some(node_tag) = current {
            let node = self.node(node_tag)?;
            path.push(node_tag);
            current = node.parent;
        }
        path.reverse();
        Some(path)
    }
}

/// Errors from tree-borrows validation.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum TreeBorrowsError<L: Debug> {
    #[error("location {location:?} does not have a borrow tree")]
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

/// Per-location Tree Borrows runtime state.
#[derive(Debug, Clone)]
pub struct TreeBorrows<L> {
    locations: HashMap<L, TreeBorrowsState>,
    next_tag: u64,
    next_protector: u64,
}

impl<L> TreeBorrows<L>
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

    /// Ensure a location has a root node and return its tag.
    pub fn ensure_base(&mut self, location: L) -> BorrowTag {
        if let Some(state) = self.locations.get(&location) {
            return state.root_tag();
        }

        let root = self.fresh_tag();
        self.locations.insert(location, TreeBorrowsState::new(root));
        root
    }

    pub fn root_tag(&self, location: &L) -> Option<BorrowTag> {
        self.locations.get(location).map(TreeBorrowsState::root_tag)
    }

    /// Return the full per-allocation permission tree.
    pub fn state(&self, location: &L) -> Option<&TreeBorrowsState> {
        self.locations.get(location)
    }

    pub fn contains_tag(&self, location: &L, tag: BorrowTag) -> bool {
        self.locations
            .get(location)
            .is_some_and(|state| state.contains_tag(tag))
    }

    pub fn node(&self, location: &L, tag: BorrowTag) -> Option<&TreeBorrowNode> {
        self.locations
            .get(location)
            .and_then(|state| state.node(tag))
    }

    pub fn permission(&self, location: &L, tag: BorrowTag) -> Option<Permission> {
        self.locations
            .get(location)
            .and_then(|state| state.permission(tag))
    }

    pub fn new_protector(&mut self) -> ProtectorId {
        let protector = ProtectorId(self.next_protector);
        self.next_protector += 1;
        protector
    }

    pub fn protect_tag(
        &mut self,
        location: &L,
        tag: BorrowTag,
        protector: ProtectorId,
    ) -> Result<(), TreeBorrowsError<L>> {
        let location_key = location.clone();
        let state =
            self.locations
                .get_mut(location)
                .ok_or_else(|| TreeBorrowsError::UnknownLocation {
                    location: location_key.clone(),
                })?;
        let node = state
            .node_mut(tag)
            .ok_or_else(|| TreeBorrowsError::UnknownTag {
                location: location_key,
                tag,
            })?;
        node.protector = Some(protector);
        Ok(())
    }

    pub fn release_protector(&mut self, protector: ProtectorId) {
        for state in self.locations.values_mut() {
            for node in state.nodes.values_mut() {
                if node.protector == Some(protector) {
                    node.protector = None;
                }
            }
        }
    }

    pub fn retag(
        &mut self,
        location: &L,
        parent: BorrowTag,
        permission: BorrowPermission,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, TreeBorrowsError<L>> {
        self.retag_with_permission(
            location,
            parent,
            Self::initial_permission(permission),
            protector,
        )
    }

    pub fn reserve(
        &mut self,
        location: &L,
        parent: BorrowTag,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, TreeBorrowsError<L>> {
        self.retag_with_permission(location, parent, Permission::Reserved, protector)
    }

    pub fn activate(&mut self, location: &L, tag: BorrowTag) -> Result<(), TreeBorrowsError<L>> {
        let location_key = location.clone();
        let state =
            self.locations
                .get_mut(location)
                .ok_or_else(|| TreeBorrowsError::UnknownLocation {
                    location: location_key.clone(),
                })?;
        let node = state
            .node_mut(tag)
            .ok_or_else(|| TreeBorrowsError::UnknownTag {
                location: location_key,
                tag,
            })?;

        match node.permission {
            Permission::Reserved => {
                node.permission = Permission::Active;
                Ok(())
            }
            Permission::Active => Ok(()),
            Permission::Frozen | Permission::Disabled => {
                Err(TreeBorrowsError::IncompatibleAccess {
                    location: location.clone(),
                    tag,
                    access: AccessKind::Write,
                })
            }
        }
    }

    /// Validate an access and update permissions across the whole tree.
    ///
    /// Ancestors on the path to the accessing tag are updated to reflect a
    /// child access. Every off-path node is treated as a foreign access:
    /// foreign reads freeze active permissions, while foreign writes disable
    /// them. Protected nodes only block disabling transitions, which makes
    /// foreign reads more permissive than Stacked Borrows.
    pub fn access(
        &mut self,
        location: &L,
        tag: BorrowTag,
        access: AccessKind,
    ) -> Result<(), TreeBorrowsError<L>> {
        let location_key = location.clone();
        let state =
            self.locations
                .get(location)
                .ok_or_else(|| TreeBorrowsError::UnknownLocation {
                    location: location_key.clone(),
                })?;
        let path = state
            .path_to(tag)
            .ok_or_else(|| TreeBorrowsError::UnknownTag {
                location: location_key.clone(),
                tag,
            })?;
        let current = state.permission(tag).expect("path implies node exists");
        let next = Self::self_permission_after(current, access).ok_or_else(|| {
            TreeBorrowsError::IncompatibleAccess {
                location: location_key.clone(),
                tag,
                access,
            }
        })?;

        let mut updates = Vec::new();
        if next != current {
            updates.push((tag, next));
        }

        for (other_tag, node) in &state.nodes {
            if *other_tag == tag {
                continue;
            }

            let next_permission = if path[..path.len() - 1].contains(other_tag) {
                Self::ancestor_permission_after(node.permission, access)
            } else {
                Self::foreign_permission_after(node.permission, access)
            };

            if access == AccessKind::Write
                && node.permission != Permission::Disabled
                && next_permission == Permission::Disabled
                && node.protector.is_some()
            {
                return Err(TreeBorrowsError::ProtectedConflict {
                    location: location.clone(),
                    tag,
                    access,
                    blocked_by: *other_tag,
                });
            }

            if next_permission != node.permission {
                updates.push((*other_tag, next_permission));
            }
        }

        let state = self
            .locations
            .get_mut(location)
            .expect("location existence checked above");
        for (updated_tag, permission) in updates {
            state
                .node_mut(updated_tag)
                .expect("tag existence checked above")
                .permission = permission;
        }
        Ok(())
    }

    fn retag_with_permission(
        &mut self,
        location: &L,
        parent: BorrowTag,
        permission: Permission,
        protector: Option<ProtectorId>,
    ) -> Result<BorrowTag, TreeBorrowsError<L>> {
        let location_key = location.clone();
        let Some(state) = self.locations.get(location) else {
            return Err(TreeBorrowsError::UnknownLocation {
                location: location_key,
            });
        };
        if !state.contains_tag(parent) {
            return Err(TreeBorrowsError::MissingParent {
                location: location.clone(),
                parent,
            });
        }

        let tag = self.fresh_tag();
        let state = self
            .locations
            .get_mut(location)
            .expect("location existence checked above");
        state
            .node_mut(parent)
            .expect("parent existence checked above")
            .children
            .push(tag);
        state.nodes.insert(
            tag,
            TreeBorrowNode {
                tag,
                permission,
                protector,
                parent: Some(parent),
                children: Vec::new(),
            },
        );
        Ok(tag)
    }

    fn initial_permission(permission: BorrowPermission) -> Permission {
        match permission {
            BorrowPermission::Unique | BorrowPermission::SharedReadWrite => Permission::Active,
            BorrowPermission::SharedReadOnly => Permission::Frozen,
            BorrowPermission::Disabled => Permission::Disabled,
        }
    }

    fn self_permission_after(permission: Permission, access: AccessKind) -> Option<Permission> {
        match access {
            AccessKind::Read => (permission != Permission::Disabled).then_some(permission),
            AccessKind::Write => match permission {
                Permission::Reserved | Permission::Active => Some(Permission::Active),
                Permission::Frozen | Permission::Disabled => None,
            },
        }
    }

    fn ancestor_permission_after(permission: Permission, access: AccessKind) -> Permission {
        match access {
            AccessKind::Read => match permission {
                Permission::Reserved => Permission::Reserved,
                Permission::Active => Permission::Frozen,
                Permission::Frozen => Permission::Frozen,
                Permission::Disabled => Permission::Disabled,
            },
            AccessKind::Write => match permission {
                Permission::Disabled => Permission::Disabled,
                Permission::Reserved | Permission::Active | Permission::Frozen => {
                    Permission::Frozen
                }
            },
        }
    }

    fn foreign_permission_after(permission: Permission, access: AccessKind) -> Permission {
        match access {
            AccessKind::Read => Self::ancestor_permission_after(permission, access),
            AccessKind::Write => match permission {
                Permission::Disabled => Permission::Disabled,
                Permission::Reserved | Permission::Active | Permission::Frozen => {
                    Permission::Disabled
                }
            },
        }
    }

    fn fresh_tag(&mut self) -> BorrowTag {
        let tag = BorrowTag(self.next_tag);
        self.next_tag += 1;
        tag
    }
}

impl<L> Default for TreeBorrows<L>
where
    L: Clone + Debug + Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}
