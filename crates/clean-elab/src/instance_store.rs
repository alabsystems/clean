// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0's INSTANCE STATE for the module being elaborated, modeled
//! exactly.
//!
//! # What Lean keeps
//!
//! `Lean.Meta.instanceExtension` is a `SimpleScopedEnvExtension` whose state
//! is `Instances` (`Lean/Meta/Instances.lean`):
//!
//! * `discrTree` — every entry ever inserted into this state. A leaf holds
//!   its entries in an array: `DiscrTree.insertVal` PUSHES a new entry and
//!   REPLACES an equal one (the same instance constant) in place, so a
//!   re-inserted instance keeps its position and takes the new priority;
//! * `instanceNames` — the instances that are in force;
//! * `erased` — names `attribute [-instance]` removed. `eraseCore` only adds
//!   the name here (and drops it from `instanceNames`); the tree entry stays,
//!   and `addInstanceEntry` removes the name from `erased` again. So an
//!   erased and re-added instance is where it always was — only an instance
//!   that is not in the tree at all is appended as the newest.
//!
//! `SynthInstance.getInstances` reads the tree's matches, stable-sorts them by
//! priority, drops the erased ones and tries the LAST first: priority
//! descending, then position descending.
//!
//! The extension keeps one such state per open scope
//! (`ScopedEnvExtension.StateStack`, `Lean/ScopedEnvExtension.lean`):
//!
//! * `pushScope` (`section`, each component of `namespace`, `open … in`)
//!   pushes a COPY of the innermost state; `popScope` drops it;
//! * a global entry (`instance`, `attribute [instance]`) is added to EVERY
//!   state of the stack and exported;
//! * a local entry (`local instance`, `attribute [local instance]`) is added
//!   to the innermost state only and never exported;
//! * a scoped entry (`scoped instance`, `attribute [scoped instance]`) is
//!   appended to `scopedEntries[ns]`, exported, and added to every state
//!   whose `activeScopes` contains `ns`;
//! * `activateScoped ns` (`namespace`, `open ns`, `open scoped ns`) adds
//!   `scopedEntries[ns]` to the innermost state, in order, unless `ns` is
//!   already active there;
//! * `erase` changes the innermost state only and is never exported.
//!
//! An importer starts from the replay of every imported module's GLOBAL
//! entries, in import order, with its own `scopedEntries` from their scoped
//! ones.
//!
//! # How Clean holds it
//!
//! The environment's instance table is the GLOBAL replay: global entries
//! only (an instance whose entries are all `local` or all `scoped` is marked
//! so, and is in no state until an entry adds it), in Lean's order, with each
//! entry's position (`Environment::instance_seq`). That is what an importer
//! starts from, and every state of the stack holds every global entry: a
//! state pushed later is a copy of one that held them.
//!
//! Each state of this module's stack is therefore that table plus an
//! [`InstanceFrame`]: the entries of the state's tree that differ from the
//! table (a local or scoped entry, or an in-place priority change the table
//! does not have), its `erased` set and its `activeScopes`. No change is
//! approximated or refused: every command applies Lean's operation to every
//! state it touches.

use std::collections::{HashMap, HashSet};

use clean_kernel::{Environment, Name};

/// An entry of a state's tree that differs from the environment's global
/// table: its priority and its position in the leaf.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FrameEntry {
    pub(crate) priority: u32,
    pub(crate) seq: u64,
}

/// One state of Lean's per-scope instance state, over the environment's
/// global table (see the module documentation).
#[derive(Debug, Clone, Default)]
pub(crate) struct InstanceFrame {
    /// Tree entries that differ from the global table.
    overlay: HashMap<Name, FrameEntry>,
    /// Lean's `erased`.
    erased: HashSet<Name>,
    /// Lean's `activeScopes`.
    active: HashSet<Name>,
}

/// Lean's instance-state stack for one module.
#[derive(Debug, Clone, Default)]
pub(crate) struct InstanceStore {
    /// The file-level state, which is never popped (the bottom of Lean's
    /// stack). Held apart from [`Self::scopes`] so the stack is non-empty by
    /// construction rather than by an invariant a caller could break.
    file: InstanceFrame,
    /// The states `push_scope` opened above the file-level one, innermost
    /// last.
    scopes: Vec<InstanceFrame>,
    /// See [`Self::global_readds`].
    global_readds: Vec<Name>,
}

/// Whether `name` has a GLOBAL entry, i.e. is in the environment's global
/// table (see [`clean_olean::has_global_instance_entry`]).
pub(crate) fn has_global_entry(env: &Environment, name: &Name) -> bool {
    clean_olean::has_global_instance_entry(env, name)
}

/// `scopedEntries[ns]` for the instance extension, in Lean's order: the
/// ordered entries elaboration recorded, preceded by any `.olean`-imported
/// scoped instance of `ns` that has none (those were loaded before any source
/// module, oldest position first, at their registered priority).
pub(crate) fn scoped_entries_of(env: &Environment, ns: &Name) -> Vec<(Name, u32)> {
    let Some(state) =
        env.get_ext_state::<clean_olean::ScopedInstanceState>(clean_olean::scoped_instance_idx())
    else {
        return Vec::new();
    };
    let recorded: Vec<(Name, u32)> = state
        .entries
        .iter()
        .filter(|(entry_ns, _, _)| entry_ns == ns)
        .map(|(_, name, priority)| (name.clone(), *priority))
        .collect();
    let mut loaded: Vec<(u64, Name, u32)> = state
        .scope_of
        .iter()
        .filter(|(name, scope)| {
            *scope == ns && !state.entries.iter().any(|(_, entry, _)| entry == *name)
        })
        .filter_map(|(name, _)| {
            let seq = env.instance_seq(name)?;
            let priority = env.instance_priority(name)?;
            Some((seq, name.clone(), priority))
        })
        .collect();
    loaded.sort();
    loaded
        .into_iter()
        .map(|(_, name, priority)| (name, priority))
        .chain(recorded)
        .collect()
}

/// Lean's `addInstanceEntry` into ONE state: insert into the tree (in place
/// when it is already there, pushed as the newest otherwise) and take the
/// name out of `erased`.
fn insert_into(frame: &mut InstanceFrame, env: &mut Environment, name: &Name, priority: u32) {
    if let Some(entry) = frame.overlay.get_mut(name) {
        entry.priority = priority;
    } else if has_global_entry(env, name) {
        let seq = env.instance_seq(name).unwrap_or(0);
        frame
            .overlay
            .insert(name.clone(), FrameEntry { priority, seq });
    } else {
        let seq = env.alloc_instance_seq();
        frame
            .overlay
            .insert(name.clone(), FrameEntry { priority, seq });
    }
    frame.erased.remove(name);
}

impl InstanceStore {
    fn top(&self) -> &InstanceFrame {
        self.scopes.last().unwrap_or(&self.file)
    }

    fn top_mut(&mut self) -> &mut InstanceFrame {
        match self.scopes.last_mut() {
            Some(frame) => frame,
            None => &mut self.file,
        }
    }

    /// Every state on the stack, file-level first.
    fn frames_mut(&mut self) -> impl Iterator<Item = &mut InstanceFrame> {
        std::iter::once(&mut self.file).chain(self.scopes.iter_mut())
    }

    /// Lean's `pushScope`: a copy of the innermost state.
    pub(crate) fn push_scope(&mut self) {
        let copy = self.top().clone();
        self.scopes.push(copy);
    }

    /// Lean's `popScope`. The file-level state is never popped.
    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// Whether `name` is in the innermost state's tree.
    fn in_tree(&self, env: &Environment, name: &Name) -> bool {
        self.top().overlay.contains_key(name) || has_global_entry(env, name)
    }

    /// Lean's `instanceNames.contains name` for the innermost state: in its
    /// tree and not erased.
    #[must_use]
    pub(crate) fn in_force(&self, env: &Environment, name: &Name) -> bool {
        self.in_tree(env, name) && !self.top().erased.contains(name)
    }

    /// A GLOBAL entry for `name` — an instance the environment already
    /// registers — with `priority` (`attribute [instance p] name`): added to
    /// every state, and to the environment's global table, which is what an
    /// importer replays. The caller registers a name that is not yet an
    /// instance itself (a fresh push everywhere).
    pub(crate) fn add_global(&mut self, env: &mut Environment, name: &Name, priority: u32) {
        let had_global_entry = has_global_entry(env, name);
        for frame in self.frames_mut() {
            // In a state whose tree already holds it through a local or
            // scoped entry, in place; everywhere else the table's entry
            // below is the state's (in place if the table had it, pushed if
            // not).
            if let Some(entry) = frame.overlay.get_mut(name) {
                entry.priority = priority;
            }
            frame.erased.remove(name);
        }
        if had_global_entry {
            // Exported as a re-insertion: an importer that holds the
            // instance replaces it in place too.
            self.global_readds.push(name.clone());
        }
        clean_olean::add_global_instance_entry(env, name, priority);
    }

    /// The instances that already had a global entry when this module gave
    /// them another (`attribute [instance p] x` on an imported or earlier
    /// global instance), in order: Lean exports each such entry, and an
    /// importer's replay re-inserts it in place (`clean lake build` writes
    /// them into the module's artifact).
    #[must_use]
    pub(crate) fn global_readds(&self) -> &[Name] {
        &self.global_readds
    }

    /// A LOCAL entry (`local instance`, `attribute [local instance p]`): the
    /// innermost state only. A name that was not an instance must already be
    /// registered and marked local by the caller.
    pub(crate) fn add_local(&mut self, env: &mut Environment, name: &Name, priority: u32) {
        insert_into(self.top_mut(), env, name, priority);
    }

    /// A SCOPED entry in namespace `ns` (`scoped instance`, `attribute
    /// [scoped instance p]`): appended to `scopedEntries[ns]` (exported with
    /// the environment) and added to every state where `ns` is active. A name
    /// that was not an instance must already be registered and marked
    /// scoped-only by the caller.
    pub(crate) fn add_scoped(
        &mut self,
        env: &mut Environment,
        ns: &Name,
        name: &Name,
        priority: u32,
    ) {
        env.get_ext_state_mut::<clean_olean::ScopedInstanceState>(
            clean_olean::scoped_instance_idx(),
        )
        .entries
        .push((ns.clone(), name.clone(), priority));
        for frame in self.frames_mut() {
            if frame.active.contains(ns) {
                insert_into(frame, env, name, priority);
            }
        }
    }

    /// `attribute [-instance] name`: Lean's `Instances.erase` on the innermost
    /// state. Fails, as Lean does, when the instance is not in force there.
    pub(crate) fn erase(&mut self, env: &Environment, name: &Name) -> Result<(), String> {
        if !self.in_force(env, name) {
            return Err(format!("'{name}' does not have [instance] attribute"));
        }
        self.top_mut().erased.insert(name.clone());
        Ok(())
    }

    /// Lean's `activateScoped ns` on the innermost state: unless `ns` is
    /// already active there, mark it active and add its scoped entries in
    /// order.
    pub(crate) fn activate(&mut self, env: &mut Environment, ns: &Name) {
        if !self.top_mut().active.insert(ns.clone()) {
            return;
        }
        let entries = scoped_entries_of(env, ns);
        if entries.is_empty() {
            return;
        }
        let top = self.top_mut();
        for (name, priority) in entries {
            insert_into(top, env, &name, priority);
        }
    }

    /// The innermost state, for an elaboration context
    /// ([`crate::ElabCtx::set_instance_view`]).
    #[must_use]
    pub(crate) fn view(&self, env: &Environment) -> InstanceView {
        let top = self.top();
        let mut absent: HashSet<Name> = env
            .local_instance_names()
            .filter(|name| !top.overlay.contains_key(*name))
            .cloned()
            .collect();
        if let Some(state) = env
            .get_ext_state::<clean_olean::ScopedInstanceState>(clean_olean::scoped_instance_idx())
        {
            absent.extend(
                state
                    .scope_of
                    .keys()
                    .filter(|name| !top.overlay.contains_key(*name))
                    .cloned(),
            );
        }
        InstanceView {
            overrides: top.overlay.clone(),
            absent,
            erased: top.erased.clone(),
            active: top.active.clone(),
            next_local_seq: u64::MAX / 2,
        }
    }
}

/// The innermost instance state as an elaboration context needs it: which
/// registered instances resolution may pick, and the priority and position
/// of those whose entry differs from the environment's global table.
#[derive(Debug, Clone, Default)]
pub(crate) struct InstanceView {
    /// Tree entries that differ from the global table.
    pub(crate) overrides: HashMap<Name, FrameEntry>,
    /// Registered instances not in the state's tree.
    pub(crate) absent: HashSet<Name>,
    /// Lean's `erased`.
    pub(crate) erased: HashSet<Name>,
    /// Lean's `activeScopes`.
    pub(crate) active: HashSet<Name>,
    /// Positions for entries an `open … in` inside the declaration pushes:
    /// after every position of the environment's counter, since nothing is
    /// registered while a declaration elaborates.
    next_local_seq: u64,
}

impl InstanceView {
    /// Whether resolution may pick instance `name`.
    #[must_use]
    pub(crate) fn in_force(&self, name: &Name) -> bool {
        !self.absent.contains(name) && !self.erased.contains(name)
    }

    /// The names resolution may not pick.
    #[must_use]
    pub(crate) fn hidden(&self) -> HashSet<Name> {
        self.absent.union(&self.erased).cloned().collect()
    }

    /// Lean's `activateScoped ns` inside a declaration (`open ns in e`,
    /// `open ns in cmd`), on this view. Returns the instances whose entry
    /// changed, whose classes the caller re-sorts.
    pub(crate) fn activate(&mut self, env: &Environment, ns: &Name) -> Vec<Name> {
        if !self.active.insert(ns.clone()) {
            return Vec::new();
        }
        let mut changed = Vec::new();
        for (name, priority) in scoped_entries_of(env, ns) {
            if let Some(entry) = self.overrides.get_mut(&name) {
                entry.priority = priority;
            } else if !self.absent.contains(&name) {
                let seq = env.instance_seq(&name).unwrap_or(0);
                self.overrides
                    .insert(name.clone(), FrameEntry { priority, seq });
            } else {
                let seq = self.next_local_seq;
                self.next_local_seq += 1;
                self.overrides
                    .insert(name.clone(), FrameEntry { priority, seq });
                self.absent.remove(&name);
            }
            self.erased.remove(&name);
            changed.push(name);
        }
        changed
    }
}
