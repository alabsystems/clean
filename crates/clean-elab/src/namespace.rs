// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Namespace manipulation for `open` and `export` commands.
//!
//! In Lean 4, `open Nat in expr` brings names from `Nat` into scope for `expr`,
//! while `open Nat` does so for the rest of the file. `export Nat (add mul)`
//! re-exports selected names from `Nat` into the current namespace.
//!
//! # Architecture
//!
//! [`NamespaceState`] tracks which namespaces are opened and what aliases
//! exist. The elaborator queries it during name resolution via
//! [`NamespaceState::resolve`], which returns the fully-qualified [`Name`]
//! for a short identifier if one is in scope.
//!
//! Scoped opens (`open Foo in ...`) are handled via the scope stack:
//! [`NamespaceState::push_scope`] / [`NamespaceState::pop_scope`].

use clean_kernel::expr::BinderInfo;
use clean_kernel::name::{Name, NameInner};
use clean_kernel::Expr;
use std::collections::HashMap;
use std::sync::Arc;

/// Errors that can occur during namespace operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum NamespaceError {
    /// The namespace referenced by an `open` or `export` command does not
    /// exist in the environment (no constants have that prefix).
    #[error("unknown namespace: {0}")]
    UnknownNamespace(String),

    /// An `export` command listed a name that does not exist in the source
    /// namespace.
    #[error("name '{name}' not found in namespace '{namespace}'")]
    NameNotFound { namespace: String, name: String },

    /// Attempted to exit a namespace/section when none was active.
    #[error("no active {0} to exit")]
    NoActiveScope(String),

    /// Attempted to exit a named scope with a mismatched name.
    #[error("expected end of {kind} '{expected}', found '{found}'")]
    ScopeMismatch {
        kind: String,
        expected: String,
        found: String,
    },
}

/// A single alias mapping a short name to a fully-qualified name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Alias {
    /// The short name used in source code (e.g., `add`).
    pub(crate) short: Name,
    /// The fully-qualified name in the environment (e.g., `Nat.add`).
    pub(crate) target: Name,
}

/// A variable declared within a `section` block via `variable (x : Nat)`.
///
/// Section variables are automatically included as parameters in definitions
/// and theorems within the section that reference them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SectionVariable {
    /// The variable name (e.g., `x`).
    pub name: Name,
    /// The variable's type expression.
    pub type_: Expr,
    /// How the variable binds: explicit, implicit, instance, etc.
    pub binder_info: BinderInfo,
}

/// A saved frame when entering a `section` block.
///
/// When the section ends, the namespace state is restored to the snapshot
/// captured when the section was entered.
#[derive(Debug, Clone)]
pub struct SectionFrame {
    /// Section name, if given (e.g., `section MySection`). Anonymous
    /// sections have `None`.
    pub name: Option<Name>,
    /// The namespace that was current when this section was opened.
    namespace_at_entry: Name,
    /// Section-scoped variables declared via `variable`.
    variables: Vec<SectionVariable>,
    /// The list of opened namespaces at section entry, for restoration.
    open_namespaces_at_entry: Vec<Name>,
    /// The `hiding` lists in force at section entry, restored with them.
    open_hidden_at_entry: HashMap<Name, Vec<Name>>,
    /// The `enter_namespace` frames in force at section entry. Restored
    /// alongside `namespace_at_entry` so the two never disagree about which
    /// prefix a later `exit_namespace` must restore.
    namespace_frames_at_entry: Vec<Name>,
    /// The activated scoped namespaces at section entry, restored at `end`.
    scoped_active_at_entry: Vec<Name>,
}

/// Tracks opened namespaces, aliases, scope boundaries, and the current
/// namespace/section stack.
///
/// Used by the elaborator during name resolution. When a bare identifier
/// like `add` is encountered, the elaborator calls [`NamespaceState::resolve`]
/// to check whether any open namespace provides a match (e.g., `Nat.add`).
#[derive(Debug, Clone)]
pub struct NamespaceState {
    /// Active aliases: short name -> fully-qualified target (the latest).
    aliases: HashMap<Name, Name>,
    /// The OTHER targets a short name still has: Lean keeps every `open`
    /// declaration and every alias (`OpenDecl` list, `aliasExtension`), so
    /// two opens or aliases giving one short name different targets make it
    /// ambiguous — there is no shadowing among them. An entry is added when
    /// [`Self::aliases`] is overwritten with a different target, and rolled
    /// back with the scope that added it. Read through
    /// [`Self::resolve_all`].
    alias_others: HashMap<Name, Vec<Name>>,
    /// Scope stack for `open ... in ...` (scoped opens).
    /// Each entry records the number of aliases that existed before the
    /// scope was entered, allowing efficient rollback.
    scope_stack: Vec<ScopeFrame>,
    /// Exported names: maps (current_namespace_prefix + short) -> target.
    /// Populated by `export` commands. These become permanent aliases
    /// visible outside the current file/section.
    exports: Vec<Alias>,
    /// The current namespace prefix (e.g., `Foo.Bar` inside
    /// `namespace Foo / namespace Bar`).
    current_namespace: Name,
    /// The prefix that was current before each still-open [`enter_namespace`],
    /// innermost last.
    ///
    /// `namespace Alpha.Beta` is ONE `enter_namespace` that pushes TWO
    /// components, and Lean's `end Alpha.Beta` closes both — so the matching
    /// [`exit_namespace`] must drop two, not one. Recording the prefix to
    /// RESTORE (rather than a count to drop) makes the pair exactly inverse by
    /// construction, whatever the entered name looked like.
    ///
    /// [`enter_namespace`]: NamespaceState::enter_namespace
    /// [`exit_namespace`]: NamespaceState::exit_namespace
    namespace_frames: Vec<Name>,
    /// Namespaces currently opened via `open` (not scoped `open ... in`).
    /// These are the namespace prefixes themselves (e.g., `Nat`), not the
    /// individual aliases they contribute.
    open_namespaces: Vec<Name>,
    /// The `hiding` list each entry of `open_namespaces` was opened with,
    /// parallel-keyed by namespace. `open Foo hiding z` must stop a bare `z`
    /// resolving to `Foo.z`, and the live open-namespace walk in the
    /// elaborator is the only resolution route that consults these prefixes
    /// directly (the alias table applies the filter itself at build time). An
    /// absent key means "opened with no hiding list".
    open_hidden: HashMap<Name, Vec<Name>>,
    /// Stack of active section frames for `section ... end` scoping.
    section_stack: Vec<SectionFrame>,
    /// Namespaces whose `scoped` entries are ACTIVE — Lean's per-scope
    /// `activeScopes`. A namespace is activated by `namespace Foo` (each
    /// component entered), a simple `open Foo`, `open Foo hiding …` and
    /// `open scoped Foo` (measured on Lean 4.8.0: `open Foo (x)` and
    /// `open Foo renaming …` activate nothing). Rolled back with the alias
    /// scope that was innermost when it was activated, as Lean pops the
    /// scope. Gates `scoped instance`s: [`crate::infer::ElabCtx`]'s
    /// `instance_visible`.
    scoped_active: Vec<Name>,
    /// What each free reference of a `notation` template resolved to where
    /// the template was declared ([`TemplateResolution`]). Not scoped: a
    /// notation declared inside a `section` or under an `open` stays usable
    /// after them, with its declaration-time meaning.
    template_sites: HashMap<clean_parser::TemplateSiteId, Arc<HashMap<Name, TemplateResolution>>>,
    /// The module this file IS (Lean's `env.mainModule`) with its private
    /// prefix `_private.<module>.0` (G21,
    /// `designs/2026-10-08-private-name-mangling.md`). `Some` only when the
    /// driver named the module ([`crate::FileContext::set_main_module`]):
    /// then a `private` theorem or axiom is registered under
    /// [`crate::private_names::mk_private_name`] and its plain name resolves
    /// through [`Self::private_name`] in this module only. `None` keeps the
    /// plain-name regime (`docs/DECISIONS.md`, 2026-10-08).
    main_module: Option<(Name, Name)>,
    /// Every `OpenDecl.explicit openedId resolvedId` in force, oldest first:
    /// one per name of `open Foo (x y)` and per pair of `open Foo renaming x
    /// → y`. The alias table above holds them too, but merged with simple
    /// opens and exports, and Lean reads an explicit open in one more way
    /// than an alias: `openedId` may be a PREFIX of the written name
    /// ([`Self::explicit_open_prefix_targets`]). Rolled back with the scope
    /// that recorded it.
    explicit_opens: Vec<(Name, Name)>,
}

/// What a notation template's free reference spelling denoted as a GLOBAL at
/// the template's declaration: Lean pre-resolves the identifiers of a syntax
/// quotation there (`Lean/Elab/Quotation.lean`), with the declaration's
/// namespace, `open`s and environment, and a use of the notation reads that
/// resolution, not one made with the `open`s where it is used. Resolving at
/// the use site made `section open A notation "KK" => k end; open B` read
/// `KK` as `B.k` (`KK = 2` accepted; Lean 4.8.0: `A.k = 1`, measured
/// 2026-09-26).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TemplateResolution {
    /// The spelling as the template wrote it, with its `TemplateOrigin`: what
    /// the resolution is made from, and made again from when the declaration
    /// saw an incomplete environment (`crate::module_batch`'s plan phase).
    pub(crate) spelling: clean_parser::SurfaceName,
    /// The identifier resolver's global answer for the spelling.
    pub(crate) ident: TemplateGlobal,
    /// The dotted-chain resolver's answer (`resolve_qualified_chain`).
    pub(crate) chain: Option<Name>,
    /// Whether the spelling denoted a value (`ident_resolves_to_value`).
    pub(crate) is_value: bool,
    /// Whether it denoted a type former (`ident_resolves_to_type_former`).
    pub(crate) is_type_former: bool,
}

/// The global part of `infer::IdentTarget`: what a spelling resolves to
/// when no local is consulted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TemplateGlobal {
    /// A global constant, inductive, constructor, recursor or alias target.
    Global(Name),
    /// The prelude combinator `id`.
    BuiltinId,
    /// The prelude combinator `cond`.
    BuiltinCond,
    /// A root export registered under its qualified name.
    Redirect(&'static str),
    /// Nothing global of that spelling existed at the declaration.
    Unresolved,
    /// More than one distinct global did (`infer::IdentTarget::Ambiguous`):
    /// every use is ambiguous, as in Lean.
    Ambiguous(Vec<Name>),
}

impl Default for NamespaceState {
    fn default() -> Self {
        Self {
            aliases: HashMap::new(),
            alias_others: HashMap::new(),
            scope_stack: Vec::new(),
            exports: Vec::new(),
            current_namespace: Name::anon(),
            namespace_frames: Vec::new(),
            open_namespaces: Vec::new(),
            open_hidden: HashMap::new(),
            section_stack: Vec::new(),
            template_sites: HashMap::new(),
            scoped_active: Vec::new(),
            main_module: None,
            explicit_opens: Vec::new(),
        }
    }
}

/// A saved scope frame for scoped opens.
#[derive(Debug, Clone)]
struct ScopeFrame {
    /// Every alias insertion made in this scope, in order, with the value
    /// the key had before it (`None`: absent). Undone in REVERSE order when
    /// the scope ends, which restores the table exactly: undoing the keys
    /// first and the overwrites after re-inserted an alias the scope itself
    /// had added (measured: `namespace N; open N; open N; end N` left `x ↦
    /// N.x` in force after `end N`, where Lean 4.8.0 has no `x`).
    undo: Vec<(Name, Option<Name>)>,
    /// Targets moved to [`NamespaceState::alias_others`] in this scope (for
    /// rollback).
    others_added: Vec<(Name, Name)>,
    /// `hiding` lists of namespaces opened before this scope that an `open`
    /// in it changed, with their previous value (for rollback).
    hidden_changed: Vec<(Name, Option<Vec<Name>>)>,
    /// Namespaces recorded as opened in this scope via
    /// [`NamespaceState::open_namespace_scoped_hiding`] (for rollback of the
    /// `open_namespaces` diagnostic list when the scope ends).
    opened_namespaces: Vec<Name>,
    /// Namespaces whose scoped entries were activated in this scope
    /// ([`NamespaceState::activate_scoped`]), deactivated when it ends.
    activated_scopes: Vec<Name>,
    /// How many [`NamespaceState::explicit_opens`] were in force when the
    /// scope began; the ones recorded in it are dropped when it ends.
    explicit_opens_before: usize,
}

impl NamespaceState {
    /// Create an empty namespace state.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Name the module this file is (see [`Self::main_module`]).
    pub(crate) fn set_main_module(&mut self, module: Name) {
        let prefix = crate::private_names::private_prefix_of(&module);
        self.main_module = Some((module, prefix));
    }

    /// The module this file is, when the driver named it.
    #[must_use]
    pub(crate) fn main_module(&self) -> Option<&Name> {
        self.main_module.as_ref().map(|(module, _)| module)
    }

    /// Lean's `mkPrivateName env n` for this module: the name a private
    /// declaration whose user-facing name is `user` is registered under, and
    /// the candidate Lean's private step tries after `user` itself. `None`
    /// without a named module.
    #[must_use]
    pub(crate) fn private_name(&self, user: &Name) -> Option<Name> {
        let (_, prefix) = self.main_module.as_ref()?;
        Some(crate::private_names::mk_private_name_with_prefix(
            prefix, user,
        ))
    }

    /// Resolve a short identifier against opened namespaces.
    ///
    /// Returns the fully-qualified [`Name`] if the identifier matches an
    /// alias from an `open` command, or `None` if no open namespace
    /// provides this name.
    ///
    /// # Example
    ///
    /// After `open Nat`, resolving `"add"` returns `Some(Name("Nat.add"))`.
    #[must_use]
    pub fn resolve(&self, short: &Name) -> Option<&Name> {
        self.aliases.get(short)
    }

    /// Record the declaration-time resolutions of a notation template's
    /// free references ([`TemplateResolution`]). The templates of one
    /// declaration (the arms of a `macro_rules`) share its site, so their
    /// resolutions are merged.
    pub(crate) fn record_template_site(
        &mut self,
        site: clean_parser::TemplateSiteId,
        resolutions: HashMap<Name, TemplateResolution>,
    ) {
        Arc::make_mut(self.template_sites.entry(site).or_default()).extend(resolutions);
    }

    /// Every resolution recorded for the template declared at `site`. The
    /// record is shared copy-on-write ([`Self::record_template_site`]), so
    /// while a clone of this `Arc` is held, a later record is a different
    /// `Arc`: the holder can tell whether one was made since.
    pub(crate) fn template_site(
        &self,
        site: clean_parser::TemplateSiteId,
    ) -> Option<&Arc<HashMap<Name, TemplateResolution>>> {
        self.template_sites.get(&site)
    }

    /// Replace every resolution recorded for the template declared at `site`
    /// with `resolutions`, made again against a more complete environment
    /// (`crate::module_batch`).
    pub(crate) fn replace_template_site(
        &mut self,
        site: clean_parser::TemplateSiteId,
        resolutions: HashMap<Name, TemplateResolution>,
    ) {
        self.template_sites.insert(site, Arc::new(resolutions));
    }

    /// The declaration-time resolution of `spelling` in the template declared
    /// at `site`, if that declaration was elaborated in this file.
    pub(crate) fn template_resolution(
        &self,
        site: clean_parser::TemplateSiteId,
        spelling: &Name,
    ) -> Option<&TemplateResolution> {
        self.template_sites.get(&site)?.get(spelling)
    }

    /// Every target `short` has (see [`Self::alias_others`]), the latest
    /// first. More than one is ambiguous to Lean.
    #[must_use]
    pub(crate) fn resolve_all(&self, short: &Name) -> Vec<&Name> {
        let mut all: Vec<&Name> = self.aliases.get(short).into_iter().collect();
        if let Some(others) = self.alias_others.get(short) {
            for other in others {
                if !all.contains(&other) {
                    all.push(other);
                }
            }
        }
        all
    }

    /// Check whether any namespaces are currently opened.
    #[must_use]
    pub fn has_opens(&self) -> bool {
        !self.aliases.is_empty()
    }

    /// Return all current aliases (for diagnostics / testing).
    #[must_use]
    pub fn aliases(&self) -> &HashMap<Name, Name> {
        &self.aliases
    }

    /// Return all exports (for diagnostics / testing).
    #[must_use]
    // Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
    // production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn exports(&self) -> &[Alias] {
        &self.exports
    }

    /// Push a new scope for `open ... in ...`.
    ///
    /// Aliases added after this call can be rolled back with [`pop_scope`].
    pub fn push_scope(&mut self) {
        self.scope_stack.push(ScopeFrame {
            undo: Vec::new(),
            others_added: Vec::new(),
            hidden_changed: Vec::new(),
            opened_namespaces: Vec::new(),
            activated_scopes: Vec::new(),
            explicit_opens_before: self.explicit_opens.len(),
        });
    }

    /// Pop the most recent scope, restoring aliases to their prior state.
    ///
    /// No-op if the scope stack is empty.
    pub fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            // Undo this scope's insertions, newest first.
            for (key, previous) in frame.undo.into_iter().rev() {
                match previous {
                    Some(value) => {
                        self.aliases.insert(key, value);
                    }
                    None => {
                        self.aliases.remove(&key);
                    }
                }
            }
            for (ns, previous) in frame.hidden_changed.into_iter().rev() {
                match previous {
                    Some(hidden) => {
                        self.open_hidden.insert(ns, hidden);
                    }
                    None => {
                        self.open_hidden.remove(&ns);
                    }
                }
            }
            // And drop the other targets recorded while they were.
            for (key, target) in frame.others_added.into_iter().rev() {
                if let Some(others) = self.alias_others.get_mut(&key) {
                    if let Some(pos) = others.iter().rposition(|t| t == &target) {
                        others.remove(pos);
                    }
                    if others.is_empty() {
                        self.alias_others.remove(&key);
                    }
                }
            }
            // Un-record namespaces opened within this scope.
            for ns in frame.opened_namespaces {
                self.open_namespaces.retain(|n| n != &ns);
                self.open_hidden.remove(&ns);
            }
            for ns in frame.activated_scopes {
                self.scoped_active.retain(|n| n != &ns);
            }
            self.explicit_opens.truncate(frame.explicit_opens_before);
        }
    }

    /// Record `OpenDecl.explicit opened resolved` ([`Self::explicit_opens`]).
    pub(crate) fn record_explicit_open(&mut self, opened: Name, resolved: Name) {
        self.explicit_opens.push((opened, resolved));
    }

    /// Lean's `resolveOpenDecls` for an `OpenDecl.explicit openedId
    /// resolvedId` whose `openedId` is a PROPER prefix of `id`: the
    /// candidate `id.replacePrefix openedId resolvedId` (`Lean/ResolveName.lean`;
    /// lean4 `tests/elab/explicitOpenDeclIssue.lean`). After `open Foo (Bar)`,
    /// `Bar.a` names `Foo.Bar.a` when that declaration exists; the caller
    /// checks existence. The exact case (`openedId == id`) is the alias table's.
    #[must_use]
    pub(crate) fn explicit_open_prefix_targets(&self, id: &Name) -> Vec<Name> {
        let mut targets: Vec<Name> = Vec::new();
        for (opened, resolved) in &self.explicit_opens {
            if opened.is_anon() {
                continue;
            }
            if let Some(rest) = strip_name_prefix(id, opened) {
                let candidate = append_names(resolved, &rest);
                if !targets.contains(&candidate) {
                    targets.push(candidate);
                }
            }
        }
        targets
    }

    /// Whether namespace `ns`'s `scoped` entries are active here: it was
    /// activated ([`Self::activate_scoped`]) in a scope still open, or it is
    /// the current namespace or one of its ancestors (entering a namespace
    /// activates it).
    #[must_use]
    pub(crate) fn is_scope_active(&self, ns: &Name) -> bool {
        if self.scoped_active.contains(ns) {
            return true;
        }
        let current = &self.current_namespace;
        if current == ns {
            return true;
        }
        !ns.is_anon() && name_has_prefix(current, ns)
    }

    /// The namespaces activated so far (see [`Self::scoped_active`]), in
    /// activation order.
    #[must_use]
    pub(crate) fn activated_scopes(&self) -> &[Name] {
        &self.scoped_active
    }

    /// The namespaces activated since `before` (an earlier
    /// [`Self::activated_scopes`]) that were not already active through the
    /// current namespace — the ones whose scoped entries Lean adds now.
    #[must_use]
    pub(crate) fn newly_activated(&self, before: &[Name]) -> Vec<Name> {
        self.scoped_active
            .iter()
            .filter(|ns| {
                !before.contains(ns)
                    && *ns != &self.current_namespace
                    && !name_has_prefix(&self.current_namespace, ns)
            })
            .cloned()
            .collect()
    }

    /// Activate namespace `ns`'s `scoped` entries for the rest of the
    /// innermost alias scope (Lean's `activateScoped`). Returns `true` when
    /// it was not already active, i.e. when Lean would add its scoped entries
    /// to the state now.
    pub(crate) fn activate_scoped(&mut self, ns: Name) -> bool {
        if self.is_scope_active(&ns) {
            // Record it anyway so a later `exit_namespace` (which moves the
            // current namespace) does not deactivate an explicit `open`.
            if !self.scoped_active.contains(&ns) {
                if let Some(frame) = self.scope_stack.last_mut() {
                    frame.activated_scopes.push(ns.clone());
                }
                self.scoped_active.push(ns);
            }
            return false;
        }
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.activated_scopes.push(ns.clone());
        }
        self.scoped_active.push(ns);
        true
    }

    /// Insert a single alias, tracking it for scope rollback.
    ///
    /// Public within the crate for use by `namespace_open` module.
    pub(crate) fn insert_alias_pub(&mut self, short: Name, target: Name) {
        self.insert_alias(short, target);
    }

    /// Insert an alias that SURVIVES scope pops (`export` semantics).
    ///
    /// Lean records `export` aliases in the environment's permanent alias
    /// table (`Lean/Elab/BuiltinCommand.lean` `elabExport` → `addAlias`), so
    /// an export made inside a `namespace`/`section` block outlives the block.
    /// This bypasses the scope-frame bookkeeping that [`insert_alias_pub`]
    /// uses, so `pop_scope` will not remove the key.
    ///
    /// [`insert_alias_pub`]: Self::insert_alias_pub
    pub(crate) fn insert_alias_unscoped(&mut self, short: Name, target: Name) {
        if let Some(old) = self.aliases.get(&short) {
            if *old != target {
                let old = old.clone();
                let others = self.alias_others.entry(short.clone()).or_default();
                if !others.contains(&old) {
                    others.push(old);
                }
            }
        }
        self.aliases.insert(short, target);
    }

    /// Append an export record (used by `namespace_open` module).
    pub(crate) fn push_export(&mut self, alias: Alias) {
        self.exports.push(alias);
    }

    /// Insert a single alias, tracking it for scope rollback.
    fn insert_alias(&mut self, short: Name, target: Name) {
        let old = self.aliases.get(&short).cloned();
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.undo.push((short.clone(), old.clone()));
        }
        // A different target does not shadow the earlier one: both stay
        // candidates (Lean's open declarations are all consulted).
        if let Some(old) = old {
            if old != target {
                let others = self.alias_others.entry(short.clone()).or_default();
                if !others.contains(&old) {
                    others.push(old.clone());
                    if let Some(frame) = self.scope_stack.last_mut() {
                        frame.others_added.push((short.clone(), old));
                    }
                }
            }
        }
        self.aliases.insert(short, target);
    }

    // =========================================================================
    // Namespace management
    // =========================================================================

    /// Get the current namespace prefix.
    ///
    /// Returns `Name::anon()` when at the root namespace.
    #[must_use]
    pub fn current_namespace(&self) -> &Name {
        &self.current_namespace
    }

    /// Enter a namespace, extending the current prefix.
    ///
    /// For example, if the current namespace is `Foo` and we enter `Bar`,
    /// the new namespace becomes `Foo.Bar`.
    ///
    /// A DOTTED `ns` (`namespace Alpha.Beta`) pushes every one of its
    /// components — Lean's `elabNamespace` pushes one scope per component and
    /// `end Alpha.Beta` pops them all — so the width is recorded and the
    /// matching [`exit_namespace`] drops exactly that many again.
    ///
    /// [`exit_namespace`]: Self::exit_namespace
    pub fn enter_namespace(&mut self, ns: Name) {
        self.enter_resolved_namespace(append_names(&self.current_namespace, &ns));
    }

    /// Enter an already resolved exact namespace, retaining the whole outer prefix.
    pub fn enter_resolved_namespace(&mut self, ns: Name) {
        self.namespace_frames.push(self.current_namespace.clone());
        self.current_namespace = ns;
    }

    /// Exit the current namespace, restoring the prefix that was current
    /// before the matching [`enter_namespace`].
    ///
    /// This drops as many components as that `enter_namespace` pushed: after
    /// `enter_namespace("Alpha.Beta")` from the root, exiting yields the root
    /// again — NOT `Alpha`. Leaving `Alpha` behind is what made a later
    /// `namespace Gamma` register its declarations as `Alpha.Gamma.*`, a name
    /// no importing module can address.
    ///
    /// With no recorded frame (a state whose namespace was set by some other
    /// route, e.g. `module_batch::exec::set_current_namespace` draining a
    /// cloned base) it falls back to dropping ONE component. That fallback is
    /// what keeps such a drain loop terminating: each call either pops a frame
    /// or strictly shortens the prefix, so `while !is_anon() { exit() }` always
    /// finishes.
    ///
    /// [`enter_namespace`]: Self::enter_namespace
    pub fn exit_namespace(&mut self) {
        self.current_namespace = self
            .namespace_frames
            .pop()
            .unwrap_or_else(|| parent_name(&self.current_namespace));
    }

    // =========================================================================
    // Open namespace tracking
    // =========================================================================

    /// Get the list of currently opened namespaces.
    #[must_use]
    pub fn open_namespaces(&self) -> &[Name] {
        &self.open_namespaces
    }

    /// The opened namespaces paired with the `hiding` list each was opened
    /// with (empty when there was none).
    ///
    /// Resolution against an open prefix must skip a hidden suffix, exactly as
    /// the alias table does when it is built. Lean's `elabOpenHiding` removes
    /// the hidden idents outright; this is the same rule for the route that
    /// walks the prefixes live instead of reading the frozen table.
    #[must_use]
    // pub(crate): every caller is in this crate and lib.rs does not re-export it;
    // a bare `pub` here is what moved paragon's bare_pub_non_lib 1371 -> 1372.
    pub(crate) fn open_namespaces_with_hidden(&self) -> Vec<(&Name, &[Name])> {
        self.open_namespaces
            .iter()
            .map(|ns| (ns, self.open_hidden.get(ns).map_or(&[][..], Vec::as_slice)))
            .collect()
    }

    /// Record that a namespace has been opened (for name resolution).
    ///
    /// This tracks the namespace prefix itself, separate from the individual
    /// aliases that `process_open` creates.
    pub fn open_namespace(&mut self, ns: Name) {
        // A simple open also activates the namespace's scoped entries.
        self.activate_scoped(ns.clone());
        if !self.open_namespaces.contains(&ns) {
            self.open_namespaces.push(ns);
        }
    }

    /// Record an opened namespace WITH scope rollback: when the innermost
    /// alias scope (a `namespace`/`section` block or `open … in`) pops, the
    /// record is removed again. Used by simple `open` processing so
    /// diagnostics ("`x` is protected; use `Foo.x`") only fire while the open
    /// is actually in force. Carries the `hiding` list so the live resolution
    /// walk can apply it (an `open` with nothing hidden passes an empty list;
    /// the no-`hiding` wrapper this once had acquired no caller and was
    /// removed 2026-09-20 as a dead-code clippy red). The list is the SUFFIXES
    /// named by `open Foo hiding a b`, not their full paths.
    pub(crate) fn open_namespace_scoped_hiding(&mut self, ns: Name, hiding: Vec<Name>) {
        if self.open_namespaces.contains(&ns) {
            // Lean keeps each `open` as its own declaration: a name that one
            // of the opens of `ns` does not hide stays reachable, so the
            // hidden set is what EVERY open hides (it used to grow with each
            // `open ns hiding x`, hiding a name an earlier plain `open ns`
            // still reaches).
            let previous = self.open_hidden.get(&ns).cloned();
            let next: Vec<Name> = previous
                .iter()
                .flatten()
                .filter(|h| hiding.contains(h))
                .cloned()
                .collect();
            if next != previous.clone().unwrap_or_default() {
                if let Some(frame) = self.scope_stack.last_mut() {
                    frame.hidden_changed.push((ns.clone(), previous));
                }
                if next.is_empty() {
                    self.open_hidden.remove(&ns);
                } else {
                    self.open_hidden.insert(ns, next);
                }
            }
            return;
        }
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.opened_namespaces.push(ns.clone());
        }
        if !hiding.is_empty() {
            self.open_hidden.insert(ns.clone(), hiding);
        }
        self.open_namespaces.push(ns);
    }

    /// Remove a namespace from the open list.
    pub fn close_namespace(&mut self, ns: &Name) {
        self.open_namespaces.retain(|n| n != ns);
        self.open_hidden.remove(ns);
    }

    // =========================================================================
    // Section management
    // =========================================================================

    /// Enter a new section, saving current state for later restoration.
    ///
    /// `name` is `Some` for named sections (`section Foo`) and `None` for
    /// anonymous sections (`section`).
    pub fn enter_section(&mut self, name: Option<Name>) {
        self.section_stack.push(SectionFrame {
            name,
            namespace_at_entry: self.current_namespace.clone(),
            variables: Vec::new(),
            open_namespaces_at_entry: self.open_namespaces.clone(),
            open_hidden_at_entry: self.open_hidden.clone(),
            namespace_frames_at_entry: self.namespace_frames.clone(),
            scoped_active_at_entry: self.scoped_active.clone(),
        });
    }

    /// Exit the most recent section, restoring namespace and open state.
    ///
    /// Returns `Err` if no section is active.
    pub fn exit_section(&mut self) -> Result<(), NamespaceError> {
        let frame = self
            .section_stack
            .pop()
            .ok_or_else(|| NamespaceError::NoActiveScope("section".to_string()))?;
        self.current_namespace = frame.namespace_at_entry;
        self.namespace_frames = frame.namespace_frames_at_entry;
        self.open_namespaces = frame.open_namespaces_at_entry;
        self.open_hidden = frame.open_hidden_at_entry;
        self.scoped_active = frame.scoped_active_at_entry;
        Ok(())
    }

    /// Add a section variable to the current (innermost) section.
    ///
    /// No-op if no section is active (variables declared outside sections
    /// are file-scoped and tracked by `FileContext`).
    pub fn add_section_variable(&mut self, var: SectionVariable) {
        if let Some(frame) = self.section_stack.last_mut() {
            frame.variables.push(var);
        }
    }

    /// Get all section variables from all active section frames,
    /// innermost last.
    ///
    /// Variables from outer sections appear before variables from inner
    /// sections, matching Lean 4's scoping behavior.
    #[must_use]
    pub fn get_section_variables(&self) -> Vec<&SectionVariable> {
        self.section_stack
            .iter()
            .flat_map(|frame| frame.variables.iter())
            .collect()
    }

    /// Get the current section depth (number of active sections).
    #[must_use]
    pub fn section_depth(&self) -> usize {
        self.section_stack.len()
    }

    /// Check whether we are inside a section.
    #[must_use]
    pub fn in_section(&self) -> bool {
        !self.section_stack.is_empty()
    }

    /// Resolve a short name against the current namespace, returning the
    /// qualified form.
    ///
    /// If the current namespace is non-anonymous, prepends it. Otherwise
    /// returns the name unchanged.
    #[must_use]
    pub fn resolve_name(&self, short: &Name) -> Name {
        append_names(&self.current_namespace, short)
    }
}

/// Structural qualification shared by source declaration/reference consumers.
pub(crate) fn append_names(prefix: &Name, suffix: &Name) -> Name {
    let mut parts = Vec::new();
    let mut current = suffix;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            inner @ (NameInner::Str(parent, _) | NameInner::Num(parent, _)) => {
                parts.push(inner);
                current = parent;
            }
        }
    }
    let mut result = prefix.clone();
    for part in parts.into_iter().rev() {
        result = match part {
            NameInner::Str(_, text) => result.str(text.as_ref()),
            NameInner::Num(_, number) => result.num(*number),
            NameInner::Anon => result,
        };
    }
    result
}

/// The components of `name` after the structural prefix `prefix`, when
/// `prefix` is a PROPER prefix of it (at least one component remains).
pub(crate) fn strip_name_prefix(name: &Name, prefix: &Name) -> Option<Name> {
    let mut parts = Vec::new();
    let mut current = name;
    while current != prefix {
        match current.inner() {
            NameInner::Anon => return None,
            inner @ (NameInner::Str(parent, _) | NameInner::Num(parent, _)) => {
                parts.push(inner);
                current = parent;
            }
        }
    }
    if parts.is_empty() {
        return None;
    }
    let mut rest = Name::anon();
    for part in parts.into_iter().rev() {
        rest = match part {
            NameInner::Str(_, text) => rest.str(text.as_ref()),
            NameInner::Num(_, number) => rest.num(*number),
            NameInner::Anon => rest,
        };
    }
    Some(rest)
}

/// Remove exactly one structural component, never a dot inside a string.
pub(crate) fn parent_name(name: &Name) -> Name {
    match name.inner() {
        NameInner::Anon => Name::anon(),
        NameInner::Str(parent, _) | NameInner::Num(parent, _) => parent.as_ref().clone(),
    }
}

/// A namespace prefix is a structural ancestor, not a display-text prefix.
pub(crate) fn name_has_prefix(name: &Name, prefix: &Name) -> bool {
    let mut current = name;
    loop {
        if current == prefix {
            return true;
        }
        match current.inner() {
            NameInner::Anon => return false,
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent,
        }
    }
}

// Re-export open/export processing from the split-out module for backward
// compatibility. All call sites use `crate::namespace::process_open` etc.
pub(crate) use crate::namespace_open::{open_activations, process_open_scoped};
pub use crate::namespace_open::{process_export, process_open};

#[cfg(test)]
#[path = "namespace_tests.rs"]
mod tests;
