// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source compilation-point state for compiler simplification.
//! Kernel checking/reduction never consult this state. Portable snapshots carry
//! resolved per-body rules, never offsets into a source session event stream.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use super::{
    register_persistent_ext, EnvExtensionEntry, EnvExtensionEntryData, Environment, ExtensionIdx,
    PersistentExtEntry, PersistentExtState,
};
use crate::{Expr, ExprKind, Level, Name};
use sha2::{Digest, Sha256};

/// A checked equality's compiler replacement, including its evidence identity.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Rule {
    /// Registered equality declaration used as the compiler rule.
    pub theorem: Name,
    /// Constant replaced in compiled code.
    pub from: Name,
    /// Constant used by compiled code in its place.
    pub to: Name,
}

/// Compiler inline modes, in the order used by Lean's InlineAttributeKind.
/// These are compiler metadata, never instructions for kernel reduction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum InlineMode {
    /// Ordinary compiler inlining.
    Inline,
    /// Disable ordinary compiler inlining.
    NoInline,
    /// Expand the definition before runtime availability checking.
    MacroInline,
    /// Inline when reduction exposes an application.
    InlineIfReduce,
    /// Always inline in the ordinary compiler phase.
    AlwaysInline,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct InlineRecord {
    name: Name,
    mode: InlineMode,
    module: Option<Name>,
    ordinal: usize,
}
type InlineView = BTreeMap<Name, InlineMode>;

// The ordinal distinguishes deliberate repeated registrations of one theorem.
// Importing a dependency through multiple paths must not replay its registration.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct GlobalRecord {
    rule: Rule,
    module: Option<Name>,
    ordinal: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct ScopedRecord {
    namespace: Name,
    rule: Rule,
    module: Option<Name>,
    ordinal: usize,
}
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct Snapshot {
    version: u32,
    globals: Vec<GlobalRecord>,
    scoped: Vec<ScopedRecord>,
    bodies: BTreeMap<Name, Vec<Rule>>,
    modules: BTreeMap<Name, Vec<Name>>,
    inline: Vec<InlineRecord>,
    body_inline: BTreeMap<Name, usize>,
    inline_views: Vec<InlineView>,
    body_modules: BTreeMap<Name, Option<Name>>,
    identities: BTreeMap<Name, [u8; 32]>,
    invalid: bool,
}

/// Lean's structural constant-replacement recognizer; it does not unfold types.
pub fn constant_replacement(ty: &Expr) -> Option<(Name, Name)> {
    if !matches!(ty.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq")) {
        return None;
    }
    let args = ty.get_app_args();
    if args.len() != 3 {
        return None;
    }
    let (ExprKind::Const(from, us), ExprKind::Const(to, vs)) = (args[1].kind(), args[2].kind())
    else {
        return None;
    };
    if us != vs {
        return None;
    }
    let mut seen = HashSet::new();
    for u in us {
        let Level::Param(n) = u else {
            return None;
        };
        if !seen.insert(n) {
            return None;
        }
    }
    Some((from.clone(), to.clone()))
}

/// Opaque identity for a local registration. Never reused after rollback.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalRule(u64);

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Inline {
        name: Name,
        mode: InlineMode,
        module: Option<Name>,
    },
    Activate {
        rule: Rule,
        local: Option<LocalRule>,
        module: Option<Name>,
    },
    Retire(LocalRule),
}
#[derive(Clone, Debug)]
enum Entry {
    Event(Event),
    Compiled(Name),
    Identity(Name, [u8; 32]),
    Scoped(Name, Rule),
    ImportedScoped(Name, Rule, Name),
    Module(Name, Vec<Name>),
    ImportedModule(Name, Vec<Name>),
    Portable(Snapshot),
    Invalid,
}
impl PersistentExtEntry for Entry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        if let Self::Portable(snapshot) = self {
            return EnvExtensionEntry {
                name: Name::from_string("snapshot.v2"),
                // Serialization failure is an invalid payload, never missing evidence.
                data: EnvExtensionEntryData::Object(
                    bincode::serde::encode_to_vec(snapshot, bincode::config::standard())
                        .unwrap_or_default(),
                ),
            };
        }
        let name = match self {
            Self::Event(Event::Activate { rule, .. }) => rule.theorem.clone(),
            Self::Event(Event::Retire(_)) => Name::anon(),
            Self::Event(Event::Inline { name, .. }) => name.clone(),
            Self::Compiled(name) | Self::Identity(name, _) => name.clone(),
            Self::Scoped(_, rule) | Self::ImportedScoped(_, rule, _) => rule.theorem.clone(),
            Self::Module(module, _) | Self::ImportedModule(module, _) => module.clone(),
            Self::Portable(_) | Self::Invalid => Name::anon(),
        };
        EnvExtensionEntry {
            name,
            data: EnvExtensionEntryData::Scalar(0),
        }
    }
    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {
        let decoded = match &entry.data {
            EnvExtensionEntryData::Object(bytes)
                if entry.name == Name::from_string("snapshot.v2") =>
            {
                bincode::serde::decode_from_slice::<Snapshot, _>(
                    bytes,
                    bincode::config::standard().with_limit::<{ 256 * 1024 * 1024 }>(),
                )
                .ok()
                .filter(|(snapshot, consumed)| snapshot.version == 2 && *consumed == bytes.len())
                .map(|(snapshot, _)| snapshot)
            }
            _ => None,
        };
        Some(decoded.map(Self::Portable).unwrap_or(Self::Invalid))
    }
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct View {
    module: Option<Name>,
    visible: HashSet<Name>,
}
impl View {
    fn for_module(module: &Name, imports: &[Name], modules: &HashMap<Name, Arc<View>>) -> Self {
        let mut visible = HashSet::from([module.clone()]);
        for import in imports {
            visible.insert(import.clone());
            if let Some(view) = modules.get(import) {
                visible.extend(view.visible.iter().cloned());
            }
        }
        Self {
            module: Some(module.clone()),
            visible,
        }
    }

    fn permits(&self, module: &Option<Name>, local: bool) -> bool {
        match module {
            None => !local || self.module.is_none(),
            Some(origin) if local => self.module.as_ref() == Some(origin),
            // A programmatic environment has no source module restricting its
            // imported globals. Local activations still require their owner.
            Some(origin) => self.module.is_none() || self.visible.contains(origin),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct InlineAt {
    point: usize,
    mode: InlineMode,
    module: Option<Name>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct State {
    events: Arc<Vec<Event>>,
    inline_index: Arc<HashMap<Name, Arc<Vec<InlineAt>>>>,
    imported_bodies: Arc<HashMap<Name, Vec<Rule>>>,
    imported_body_inline: Arc<HashMap<Name, Arc<InlineView>>>,
    imported_body_modules: Arc<HashMap<Name, Option<Name>>>,
    identities: Arc<HashMap<Name, [u8; 32]>>,
    imported_inline: Arc<HashMap<(Option<Name>, Name, usize), InlineMode>>,
    imported_globals: Arc<HashMap<(Option<Name>, Name, usize), Rule>>,
    imported_scoped: Arc<HashMap<(Option<Name>, Name, Name, usize), Rule>>,
    invalid: bool,
    cutoffs: Arc<HashMap<Name, (usize, Arc<View>)>>,
    view: Arc<View>,
    modules: Arc<HashMap<Name, Arc<View>>>,
    scoped: Arc<Vec<(Name, Rule, Option<Name>)>>,
}
impl PersistentExtState for State {
    type Entry = Entry;
    fn add_entry(&mut self, entry: &Entry) {
        match entry {
            Entry::Invalid => self.invalid = true,
            Entry::Identity(name, digest) => {
                if let Some(previous) =
                    Arc::make_mut(&mut self.identities).insert(name.clone(), *digest)
                {
                    self.invalid |= previous != *digest;
                }
            }
            Entry::Portable(snapshot) => self.import(snapshot),
            Entry::Event(event) => self.push_event(event.clone()),
            Entry::Scoped(namespace, rule) => Arc::make_mut(&mut self.scoped).push((
                namespace.clone(),
                rule.clone(),
                self.view.module.clone(),
            )),
            Entry::ImportedScoped(namespace, rule, module) => Arc::make_mut(&mut self.scoped)
                .push((namespace.clone(), rule.clone(), Some(module.clone()))),
            Entry::Module(module, imports) | Entry::ImportedModule(module, imports) => {
                let view = Arc::new(View::for_module(module, imports, &self.modules));
                if matches!(entry, Entry::ImportedModule(..)) {
                    if let Some(previous) = self.modules.get(module) {
                        self.invalid |= previous.visible != view.visible;
                    }
                }
                if matches!(entry, Entry::Module(..)) {
                    self.view = view.clone();
                }
                Arc::make_mut(&mut self.modules).insert(module.clone(), view);
            }
            Entry::Compiled(name) => {
                Arc::make_mut(&mut self.cutoffs)
                    .entry(name.clone())
                    .or_insert_with(|| (self.events.len(), self.view.clone()));
            }
        }
    }
    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        vec![Entry::Portable(self.snapshot()).to_env_entry()]
    }
}
impl State {
    fn push_event(&mut self, event: Event) {
        if let Event::Inline { name, mode, module } = &event {
            let index = Arc::make_mut(&mut self.inline_index);
            let entries = index.entry(name.clone()).or_default();
            let ordinal = entries.iter().filter(|e| e.module == *module).count();
            Arc::make_mut(&mut self.imported_inline)
                .insert((module.clone(), name.clone(), ordinal), *mode);
            Arc::make_mut(entries).push(InlineAt {
                point: self.events.len(),
                mode: *mode,
                module: module.clone(),
            });
        }
        Arc::make_mut(&mut self.events).push(event);
    }
    fn inline_before(&self, name: &Name, cutoff: usize, view: &View) -> Option<InlineMode> {
        let entries = self.inline_index.get(name)?;
        entries
            .iter()
            .rev()
            .find(|entry| entry.point < cutoff && view.permits(&entry.module, false))
            .map(|entry| entry.mode)
    }

    fn body_inline(&self, name: &Name) -> Arc<InlineView> {
        if let Some(modes) = self.imported_body_inline.get(name) {
            return modes.clone();
        }
        let Some((cutoff, view)) = self.cutoffs.get(name) else {
            return Arc::new(InlineView::new());
        };
        Arc::new(select_inline(&self.events[..*cutoff], view))
    }
    fn body_rules(&self, name: &Name) -> Vec<Rule> {
        if let Some(rules) = self.imported_bodies.get(name) {
            return rules.clone();
        }
        let Some((cutoff, view)) = self.cutoffs.get(name) else {
            return Vec::new();
        };
        select(&self.events[..*cutoff], view)
    }
    fn snapshot(&self) -> Snapshot {
        let mut globals = Vec::new();
        let mut ordinals = HashMap::new();
        for event in self.events.iter() {
            if let Event::Activate {
                rule,
                module,
                local: None,
            } = event
            {
                let ordinal = ordinals
                    .entry((module.clone(), rule.theorem.clone()))
                    .or_insert(0);
                globals.push(GlobalRecord {
                    rule: rule.clone(),
                    module: module.clone(),
                    ordinal: *ordinal,
                });
                *ordinal += 1;
            }
        }
        let mut scoped = Vec::new();
        let mut ordinals = HashMap::new();
        for (namespace, rule, module) in self.scoped.iter() {
            let ordinal = ordinals
                .entry((module.clone(), namespace.clone(), rule.theorem.clone()))
                .or_insert(0);
            scoped.push(ScopedRecord {
                namespace: namespace.clone(),
                rule: rule.clone(),
                module: module.clone(),
                ordinal: *ordinal,
            });
            *ordinal += 1;
        }
        let mut bodies: BTreeMap<_, _> = self
            .imported_bodies
            .iter()
            .map(|(n, r)| (n.clone(), r.clone()))
            .collect();
        for name in self.cutoffs.keys() {
            bodies
                .entry(name.clone())
                .or_insert_with(|| self.body_rules(name));
        }
        let mut inline = Vec::new();
        let mut ordinals = HashMap::new();
        for event in self.events.iter() {
            if let Event::Inline { name, mode, module } = event {
                let ordinal = ordinals.entry((module.clone(), name.clone())).or_insert(0);
                inline.push(InlineRecord {
                    name: name.clone(),
                    mode: *mode,
                    module: module.clone(),
                    ordinal: *ordinal,
                });
                *ordinal += 1;
            }
        }
        let mut inline_views = Vec::new();
        let mut interned = HashMap::new();
        let mut body_inline = BTreeMap::new();
        let mut body_modules = BTreeMap::new();
        let mut contexts = HashMap::new();
        for name in bodies.keys() {
            let modes = if let Some(modes) = self.imported_body_inline.get(name) {
                body_modules.insert(
                    name.clone(),
                    self.imported_body_modules
                        .get(name)
                        .cloned()
                        .unwrap_or(None),
                );
                modes.clone()
            } else if let Some((cutoff, view)) = self.cutoffs.get(name) {
                body_modules.insert(name.clone(), view.module.clone());
                contexts
                    .entry((*cutoff, Arc::as_ptr(view) as usize))
                    .or_insert_with(|| self.body_inline(name))
                    .clone()
            } else {
                Arc::new(InlineView::new())
            };
            let next = inline_views.len();
            let id = *interned.entry(modes.clone()).or_insert_with(|| {
                inline_views.push(modes.as_ref().clone());
                next
            });
            body_inline.insert(name.clone(), id);
        }
        let modules = self
            .modules
            .iter()
            .map(|(name, view)| {
                let mut visible: Vec<_> = view.visible.iter().cloned().collect();
                visible.sort();
                (name.clone(), visible)
            })
            .collect();
        Snapshot {
            version: 2,
            globals,
            scoped,
            bodies,
            modules,
            inline,
            body_inline,
            inline_views,
            body_modules,
            identities: self
                .identities
                .iter()
                .map(|(name, digest)| (name.clone(), *digest))
                .collect(),
            invalid: self.invalid,
        }
    }
    fn import(&mut self, snapshot: &Snapshot) {
        self.invalid |= snapshot.invalid;
        if !snapshot.valid_shape() {
            self.invalid = true;
            return;
        }
        for (name, digest) in &snapshot.identities {
            if let Some(previous) =
                Arc::make_mut(&mut self.identities).insert(name.clone(), *digest)
            {
                self.invalid |= previous != *digest;
            }
        }
        let views: Vec<_> = snapshot
            .inline_views
            .iter()
            .cloned()
            .map(Arc::new)
            .collect();
        for (name, id) in &snapshot.body_inline {
            let modes = &views[*id];
            if self.cutoffs.contains_key(name) && self.body_inline(name) != *modes {
                self.invalid = true;
            }
            let bodies = Arc::make_mut(&mut self.imported_body_inline);
            if let Some(previous) = bodies.get(name) {
                self.invalid |= previous != modes;
            } else {
                bodies.insert(name.clone(), modes.clone());
            }
            let module = snapshot.body_modules.get(name).cloned().unwrap_or(None);
            if let Some(previous) =
                Arc::make_mut(&mut self.imported_body_modules).insert(name.clone(), module.clone())
            {
                self.invalid |= previous != module;
            }
        }
        let mut ordinals = HashMap::new();
        for record in &snapshot.inline {
            let ordinal = ordinals
                .entry((record.module.clone(), record.name.clone()))
                .or_insert(0);
            if record.ordinal != *ordinal {
                self.invalid = true;
            }
            *ordinal += 1;
            let key = (record.module.clone(), record.name.clone(), record.ordinal);
            if let Some(previous) = self.imported_inline.get(&key) {
                self.invalid |= *previous != record.mode;
            } else {
                self.push_event(Event::Inline {
                    name: record.name.clone(),
                    mode: record.mode,
                    module: record.module.clone(),
                });
            }
        }
        for (name, rules) in &snapshot.bodies {
            if self.cutoffs.contains_key(name) && self.body_rules(name) != *rules {
                self.invalid = true;
            }
            let bodies = Arc::make_mut(&mut self.imported_bodies);
            if let Some(previous) = bodies.get(name) {
                self.invalid |= previous != rules;
            } else {
                bodies.insert(name.clone(), rules.clone());
            }
        }
        for record in &snapshot.globals {
            let key = (
                record.module.clone(),
                record.rule.theorem.clone(),
                record.ordinal,
            );
            let globals = Arc::make_mut(&mut self.imported_globals);
            if let Some(previous) = globals.get(&key) {
                self.invalid |= previous != &record.rule;
            } else {
                globals.insert(key, record.rule.clone());
                Arc::make_mut(&mut self.events).push(Event::Activate {
                    rule: record.rule.clone(),
                    local: None,
                    module: record.module.clone(),
                });
            }
        }
        for record in &snapshot.scoped {
            let key = (
                record.module.clone(),
                record.namespace.clone(),
                record.rule.theorem.clone(),
                record.ordinal,
            );
            let scoped = Arc::make_mut(&mut self.imported_scoped);
            if let Some(previous) = scoped.get(&key) {
                self.invalid |= previous != &record.rule;
            } else {
                scoped.insert(key, record.rule.clone());
                Arc::make_mut(&mut self.scoped).push((
                    record.namespace.clone(),
                    record.rule.clone(),
                    record.module.clone(),
                ));
            }
        }
        for (name, order) in &snapshot.modules {
            let visible: HashSet<_> = order.iter().cloned().collect();
            if !visible.contains(name) || visible.len() != order.len() {
                self.invalid = true;
            }
            let view = Arc::new(View {
                module: Some(name.clone()),
                visible,
            });
            let modules = Arc::make_mut(&mut self.modules);
            if let Some(previous) = modules.get(name) {
                self.invalid |= previous.visible != view.visible;
            } else {
                modules.insert(name.clone(), view);
            }
        }
    }
}
fn select_inline(events: &[Event], view: &View) -> InlineView {
    events
        .iter()
        .filter_map(|event| match event {
            Event::Inline { name, mode, module } if view.permits(module, false) => {
                Some((name.clone(), *mode))
            }
            _ => None,
        })
        .collect()
}

/// Record an inline mode at the same compiler event clock as checked bodies.
pub fn register_inline_mode(env: &mut Environment, name: Name, mode: InlineMode) {
    record_identity(env, &name);
    let module = current_module(env);
    env.add_ext_entry::<State>(index(), &Entry::Event(Event::Inline { name, mode, module }));
}

/// Restore a genuine artifact's inline mode without changing the caller view.
pub fn import_inline_mode(env: &mut Environment, module: Name, name: Name, mode: InlineMode) {
    record_identity(env, &name);
    env.add_ext_entry::<State>(
        index(),
        &Entry::Event(Event::Inline {
            name,
            mode,
            module: Some(module),
        }),
    );
}

/// Inline mode visible when the owner compiled; unnamed expressions compile now.
pub fn inline_mode_at(env: &Environment, owner: Option<&Name>, name: &Name) -> Option<InlineMode> {
    let state = env.get_ext_state::<State>(index())?;
    match owner {
        Some(owner) => {
            if let Some(modes) = state.imported_body_inline.get(owner) {
                return modes.get(name).copied();
            }
            let (cutoff, view) = state.cutoffs.get(owner)?;
            state.inline_before(name, *cutoff, view)
        }
        None => state.inline_before(name, state.events.len(), &state.view),
    }
}

/// Whether canonical metadata owns this hint, including an invisible sibling.
/// `Some(false)` prevents an old raw registry set leaking across module views.
pub fn inline_attribute_status(env: &Environment, name: &Name, mode: InlineMode) -> Option<bool> {
    let state = env.get_ext_state::<State>(index())?;
    let known = state.inline_index.contains_key(name);
    known.then(|| inline_mode_at(env, None, name) == Some(mode))
}

fn select(events: &[Event], view: &View) -> Vec<Rule> {
    let mut selected = BTreeMap::new();
    for (rule, _) in active(events, view) {
        selected.insert(rule.from.clone(), rule.clone());
    }
    selected.into_values().collect()
}
/// Malformed or conflicting compiler metadata must refuse compilation.
pub fn has_invalid_metadata(env: &Environment) -> bool {
    env.get_ext_state::<State>(index())
        .is_some_and(|s| s.invalid)
}
/// The extension's registry name; `fact_delta` lists it as a carried state.
pub(crate) const CSIMP_SOURCE_EXTENSION: &str = "Clean.compiler.csimpSource";

fn index() -> ExtensionIdx {
    static INDEX: OnceLock<ExtensionIdx> = OnceLock::new();
    *INDEX
        .get_or_init(|| register_persistent_ext::<State>(Name::from_string(CSIMP_SOURCE_EXTENSION)))
}

/// The typed state, an empty one when the extension holds nothing, or `Err`
/// while imported entries are still unfolded (the typed state would then
/// not say what the environment holds).
fn folded<'a>(env: &'a Environment, empty: &'a State) -> Result<&'a State, &'static str> {
    match env.get_ext_state::<State>(index()) {
        Some(state) => Ok(state),
        None if env.has_unfolded_extension_entries(CSIMP_SOURCE_EXTENSION) => {
            Err("the csimp source state's imported entries are not folded")
        }
        None => Ok(empty),
    }
}

/// The rules a recorded body resolves to, or `None` for a name with no
/// compilation point. The elaboration record digests this per name.
pub(crate) fn recorded_body_rules(env: &Environment, name: &Name) -> Option<Vec<Rule>> {
    let state = env.get_ext_state::<State>(index())?;
    (state.cutoffs.contains_key(name) || state.imported_bodies.contains_key(name))
        .then(|| state.body_rules(name))
}

/// The compilation points `after` recorded since `before`, each with the
/// rules its body resolves to, when recording them is the ONLY change to the
/// csimp state: `before`'s state plus [`record_compiled`] of those names must
/// equal `after`'s state in every field (events, imports, views, modules,
/// scoped rules, validity, and each cutoff's position and view). Any other
/// change (a rule event, a module or scoped entry, an import) is `Err`: a
/// local fact delta carries compilation points and nothing else.
pub(crate) fn compiled_since(
    before: &Environment,
    after: &Environment,
) -> Result<Vec<(Name, Vec<Rule>)>, &'static str> {
    let empty = State::default();
    let (was, now) = (folded(before, &empty)?, folded(after, &empty)?);
    let mut names: Vec<Name> = now
        .cutoffs
        .keys()
        .filter(|name| !was.cutoffs.contains_key(*name))
        .cloned()
        .collect();
    names.sort();
    let mut expected = was.clone();
    for name in &names {
        if was.imported_bodies.contains_key(name) {
            return Err("a compilation point shadows an imported body");
        }
        expected.add_entry(&Entry::Compiled(name.clone()));
    }
    if expected != *now {
        return Err("the csimp state changed by more than compilation points");
    }
    Ok(names
        .into_iter()
        .map(|name| {
            let rules = now.body_rules(&name);
            (name, rules)
        })
        .collect())
}

/// Whether recording `compiled` here gives each body the rules the producing
/// elaboration resolved: the name has no compilation point or imported body
/// yet, and the rules visible here now are the carried ones.
pub(crate) fn compiled_fits(
    env: &Environment,
    compiled: &[(Name, Vec<Rule>)],
) -> Result<(), String> {
    if compiled.is_empty() {
        return Ok(());
    }
    let empty = State::default();
    let state = folded(env, &empty).map_err(str::to_string)?;
    let visible = select(&state.events, &state.view);
    for (name, rules) in compiled {
        if state.cutoffs.contains_key(name) || state.imported_bodies.contains_key(name) {
            return Err(format!(
                "`{name}` already has a csimp compilation point here"
            ));
        }
        if *rules != visible {
            return Err(format!(
                "the csimp rules visible to `{name}` are different here"
            ));
        }
    }
    Ok(())
}

fn rule(env: &Environment, theorem: &Name) -> Option<Rule> {
    let (from, to) = constant_replacement(&env.get_const(theorem)?.type_)?;
    Some(Rule {
        theorem: theorem.clone(),
        from,
        to,
    })
}
/// Validate a registered declaration and activate a global replacement.
pub fn register(env: &mut Environment, theorem: &Name) -> bool {
    let Some(rule) = rule(env, theorem) else {
        return false;
    };
    env.register_csimp(theorem.clone());
    env.add_ext_entry::<State>(
        index(),
        &Entry::Event(Event::Activate {
            rule,
            local: None,
            module: current_module(env),
        }),
    );
    true
}
/// Activate a local replacement, returning the identity to retire at scope end.
pub fn register_local(env: &mut Environment, theorem: &Name) -> Option<LocalRule> {
    activate_rule(env, rule(env, theorem)?)
}

fn activate_rule(env: &mut Environment, rule: Rule) -> Option<LocalRule> {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    let token = LocalRule(
        NEXT.try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .ok()?,
    );
    env.add_ext_entry::<State>(
        index(),
        &Entry::Event(Event::Activate {
            rule,
            local: Some(token),
            module: current_module(env),
        }),
    );
    Some(token)
}
/// Store a namespace-scoped rule without activating it outside that namespace.
pub fn define_scoped(env: &mut Environment, namespace: &Name, theorem: &Name) -> bool {
    if namespace.is_anon() {
        return false;
    }
    let Some(rule) = rule(env, theorem) else {
        return false;
    };
    env.add_ext_entry::<State>(index(), &Entry::Scoped(namespace.clone(), rule));
    true
}
/// Activate the definitions of a namespace in original registration order.
pub fn activate_namespace(env: &mut Environment, namespace: &Name) -> Option<Vec<LocalRule>> {
    let rules: Vec<_> = env
        .get_ext_state::<State>(index())
        .map(|s| {
            s.scoped
                .iter()
                .filter(|(ns, _, origin)| ns == namespace && s.view.permits(origin, false))
                .map(|(_, r, _)| r.clone())
                .collect()
        })
        .unwrap_or_default();
    let mut tokens = Vec::new();
    for rule in rules {
        match activate_rule(env, rule) {
            Some(token) => tokens.push(token),
            None => {
                for token in tokens {
                    retire_local(env, token);
                }
                return None;
            }
        }
    }
    Some(tokens)
}

/// End one local activation; earlier compiled bodies retain their prior view.
pub fn retire_local(env: &mut Environment, token: LocalRule) {
    env.add_ext_entry::<State>(index(), &Entry::Event(Event::Retire(token)));
}

fn active<'a>(
    events: &'a [Event],
    view: &'a View,
) -> impl Iterator<Item = (&'a Rule, Option<LocalRule>)> {
    let retired: HashSet<_> = events
        .iter()
        .filter_map(|e| match e {
            Event::Retire(t) => Some(*t),
            _ => None,
        })
        .collect();
    events.iter().filter_map(move |e| match e {
        Event::Activate {
            rule,
            local,
            module,
        } if local.is_none_or(|t| !retired.contains(&t))
            && view.permits(module, local.is_some()) =>
        {
            Some((rule, *local))
        }
        _ => None,
    })
}
/// Attribute visibility when this source/compiler metadata owns the marker.
/// Unknown legacy markers remain the environment registry's responsibility.
pub fn attribute_status(env: &Environment, theorem: &Name) -> Option<bool> {
    let state = env.get_ext_state::<State>(index())?;
    let known = state
        .events
        .iter()
        .any(|event| matches!(event, Event::Activate { rule, .. } if rule.theorem == *theorem))
        || state
            .scoped
            .iter()
            .any(|(_, rule, _)| rule.theorem == *theorem);
    known.then(|| active(&state.events, &state.view).any(|(rule, _)| rule.theorem == *theorem))
}

/// Record successful source admission once; later attributes cannot move it.
pub fn record_compiled(env: &mut Environment, declarations: impl IntoIterator<Item = Name>) {
    for name in declarations {
        // Proofs are erased, and axioms/family packets have no runtime body.
        // Binding their proof values/origins would reject Lean's legitimate
        // same-statement theorem restatements across artifact boundaries.
        if !env.get_const(&name).is_some_and(|info| {
            matches!(
                info.kind,
                super::ConstantKind::Definition | super::ConstantKind::Opaque
            ) && info.value.is_some()
        }) {
            continue;
        }
        record_identity(env, &name);
        env.add_ext_entry::<State>(index(), &Entry::Compiled(name));
    }
}

/// Rules visible to a compiled source body. Unnamed expressions compile now;
/// declarations not admitted by this source run precede its new rule events.
/// Imported bodies carry their original resolved rule snapshot.
pub fn rules_for(env: &Environment, owner: Option<&Name>) -> Vec<Rule> {
    let Some(state) = env.get_ext_state::<State>(index()) else {
        return Vec::new();
    };
    match owner {
        Some(name) => state.body_rules(name),
        None => select(&state.events, &state.view),
    }
}

impl State {
    fn replacement_sources(&self) -> impl Iterator<Item = &Name> {
        self.imported_bodies
            .values()
            .flatten()
            .map(|rule| &rule.from)
            .chain(self.events.iter().filter_map(|event| match event {
                Event::Activate { rule, .. } => Some(&rule.from),
                Event::Inline { .. } | Event::Retire(_) => None,
            }))
    }
}

/// Sources replaced at any recorded compilation point, including retired
/// local rules that can still apply to previously compiled bodies.
pub fn replacement_sources(env: &Environment) -> HashSet<Name> {
    env.get_ext_state::<State>(index())
        .into_iter()
        .flat_map(State::replacement_sources)
        .cloned()
        .collect()
}

/// Prevent optimizations from manufacturing a call that bypasses this boundary.
pub fn has_replacement(env: &Environment, name: &Name) -> bool {
    env.get_ext_state::<State>(index())
        .is_some_and(|state| state.replacement_sources().any(|source| source == name))
}

fn current_module(env: &Environment) -> Option<Name> {
    env.get_ext_state::<State>(index())
        .and_then(|s| s.view.module.clone())
}

/// Record an artifact's import graph without changing the caller's source view.
pub fn record_imported_module(env: &mut Environment, module: Name, imports: Vec<Name>) {
    env.add_ext_entry::<State>(index(), &Entry::ImportedModule(module, imports));
}

/// Register an artifact's checked compiler equality with its original owner.
/// Preloading a sibling must not activate its rules in the caller's module.
pub fn import_rule(
    env: &mut Environment,
    module: &Name,
    namespace: Option<&Name>,
    theorem: &Name,
) -> bool {
    if module.is_anon() || namespace.is_some_and(Name::is_anon) {
        return false;
    }
    let Some(rule) = rule(env, theorem) else {
        return false;
    };
    match namespace {
        Some(namespace) => env.add_ext_entry::<State>(
            index(),
            &Entry::ImportedScoped(namespace.clone(), rule, module.clone()),
        ),
        None => {
            env.register_csimp(theorem.clone());
            env.add_ext_entry::<State>(
                index(),
                &Entry::Event(Event::Activate {
                    rule,
                    local: None,
                    module: Some(module.clone()),
                }),
            );
        }
    }
    true
}

/// Enter a source module after its imports have been elaborated. Compiler rules
/// from sibling modules remain stored, but are excluded from this module's view.
pub fn begin_source_module(env: &mut Environment, module: Name, imports: Vec<Name>) {
    if env.get_ext_state::<State>(index()).is_some_and(|s| {
        s.view.module.as_ref() == Some(&module)
            && s.view.visible == View::for_module(&module, &imports, &s.modules).visible
    }) {
        return;
    }
    env.add_ext_entry::<State>(index(), &Entry::Module(module, imports));
}

fn record_identity(env: &mut Environment, name: &Name) {
    if let Some(digest) = env.compiler_declaration_digest(name) {
        env.add_ext_entry::<State>(index(), &Entry::Identity(name.clone(), digest));
    }
}

/// Portable Clean-artifact compiler context. This is not a Lean object layout;
/// callers carry these bytes in Clean's versioned payload, not raw Lean objects.
pub fn export_compilation_snapshot(env: &Environment) -> Vec<EnvExtensionEntry> {
    env.get_ext_state::<State>(index())
        .map(PersistentExtState::export_entries)
        .unwrap_or_default()
}

/// [`export_compilation_snapshot`] less every record `base` already holds,
/// for a module elaborated over `base`, an imported closure every importer
/// loads itself (genuine Init, which the artifact records as an import).
/// The importer rebuilds those records from its own load of `base`'s
/// modules. Repeating them in every artifact only adds bytes: Init's module
/// views alone were about 6 MB per module. Any record that differs from
/// `base`'s, and every record `base` lacks, is kept, so an importer whose
/// `base` disagrees still meets the conflict at import.
pub fn export_compilation_snapshot_over(
    env: &Environment,
    base: &Environment,
) -> Vec<EnvExtensionEntry> {
    let Some(state) = env.get_ext_state::<State>(index()) else {
        return Vec::new();
    };
    let mut snapshot = state.snapshot();
    if let Some(base) = base.get_ext_state::<State>(index()) {
        let base = base.snapshot();
        snapshot.globals.retain(|r| !base.globals.contains(r));
        snapshot.scoped.retain(|r| !base.scoped.contains(r));
        let body_inline = &snapshot.body_inline;
        let inline_views = &snapshot.inline_views;
        let body_modules = &snapshot.body_modules;
        let identities = &snapshot.identities;
        snapshot.bodies.retain(|name, rules| {
            base.bodies.get(name) != Some(rules)
                || base.body_modules.get(name) != body_modules.get(name)
                || base.identities.get(name) != identities.get(name)
                || base
                    .body_inline
                    .get(name)
                    .and_then(|id| base.inline_views.get(*id))
                    != body_inline.get(name).and_then(|id| inline_views.get(*id))
        });
        snapshot
            .body_inline
            .retain(|name, _| snapshot.bodies.contains_key(name));
        snapshot
            .body_modules
            .retain(|name, _| snapshot.bodies.contains_key(name));
        // Keep the owners and inline registrations needed to validate a
        // retained body's captured view, even if that view mentions Init.
        let owners: HashSet<_> = snapshot.body_modules.values().flatten().collect();
        snapshot.modules.retain(|name, visible| {
            owners.contains(name) || base.modules.get(name) != Some(visible)
        });
    }
    vec![Entry::Portable(snapshot).to_env_entry()]
}
/// Split the portable snapshot into independently accumulating semantic records.
/// A whole-session blob cannot be compared as one module contribution: sibling
/// modules legitimately add other bodies and module views. Ordered rule vectors
/// remain intact within their owning module/namespace, and each body's resolved
/// rule order remains part of its record. Malformed snapshots retain their raw
/// bytes so the ordinary fail-closed effect comparison still sees them.
pub(super) fn effect_entries(entries: &[EnvExtensionEntry]) -> Vec<EnvExtensionEntry> {
    #[derive(serde::Serialize)]
    enum Record {
        Globals(Option<Name>, Vec<GlobalRecord>),
        Scoped(Option<Name>, Name, Vec<ScopedRecord>),
        Body(Name, Vec<Rule>),
        Module(Name, Vec<Name>),
        Inline(Option<Name>, Vec<InlineRecord>),
        BodyInline(Name, [u8; 32], Option<Name>),
        InlineView([u8; 32], InlineView),
        Identity(Name, [u8; 32]),
        Invalid,
    }
    let mut result = Vec::new();
    for entry in entries {
        let Some(Entry::Portable(snapshot)) = Entry::from_env_entry(entry) else {
            return entries.to_vec();
        };
        if !snapshot.valid_shape() {
            return entries.to_vec();
        }
        let mut records = Vec::new();
        let mut globals = BTreeMap::<_, Vec<_>>::new();
        for record in snapshot.globals {
            globals
                .entry(record.module.clone())
                .or_default()
                .push(record);
        }
        records.extend(
            globals
                .into_iter()
                .map(|(module, rules)| Record::Globals(module, rules)),
        );
        let mut scoped = BTreeMap::<_, Vec<_>>::new();
        for record in snapshot.scoped {
            scoped
                .entry((record.module.clone(), record.namespace.clone()))
                .or_default()
                .push(record);
        }
        records.extend(
            scoped
                .into_iter()
                .map(|((module, namespace), rules)| Record::Scoped(module, namespace, rules)),
        );
        records.extend(
            snapshot
                .bodies
                .into_iter()
                .map(|(name, rules)| Record::Body(name, rules)),
        );
        records.extend(
            snapshot
                .modules
                .into_iter()
                .map(|(name, visible)| Record::Module(name, visible)),
        );
        let mut inline = BTreeMap::<_, Vec<_>>::new();
        for record in snapshot.inline {
            inline
                .entry(record.module.clone())
                .or_default()
                .push(record);
        }
        records.extend(
            inline
                .into_iter()
                .map(|(module, modes)| Record::Inline(module, modes)),
        );
        let mut views = Vec::new();
        let mut seen_views = HashSet::new();
        for view in &snapshot.inline_views {
            let Ok(bytes) = bincode::serde::encode_to_vec(view, bincode::config::standard()) else {
                return entries.to_vec();
            };
            let mut hasher = Sha256::new();
            hasher.update(b"Clean compiler inline view v2\0");
            hasher.update(&bytes);
            let digest: [u8; 32] = hasher.finalize().into();
            if seen_views.insert(digest) {
                records.push(Record::InlineView(digest, view.clone()));
            }
            views.push(digest);
        }
        records.extend(snapshot.body_inline.into_iter().map(|(name, id)| {
            let owner = snapshot.body_modules.get(&name).cloned().unwrap_or(None);
            Record::BodyInline(name, views[id], owner)
        }));
        records.extend(
            snapshot
                .identities
                .into_iter()
                .map(|(name, digest)| Record::Identity(name, digest)),
        );
        if snapshot.invalid {
            records.push(Record::Invalid);
        }
        for record in records {
            let Ok(bytes) = bincode::serde::encode_to_vec(&record, bincode::config::standard())
            else {
                return entries.to_vec();
            };
            result.push(EnvExtensionEntry {
                name: Name::from_string("effect.v2"),
                data: EnvExtensionEntryData::Object(bytes),
            });
        }
    }
    result
}
impl Snapshot {
    fn needed_identities(&self) -> HashSet<Name> {
        self.inline
            .iter()
            .map(|r| r.name.clone())
            .chain(self.bodies.keys().cloned())
            .chain(
                self.inline_views
                    .iter()
                    .flat_map(|view| view.keys().cloned()),
            )
            .collect()
    }
    fn valid_shape(&self) -> bool {
        if self.version != 2
            || self.invalid
            || self.bodies.keys().ne(self.body_inline.keys())
            || self.bodies.keys().ne(self.body_modules.keys())
            || self
                .needed_identities()
                .iter()
                .any(|name| !self.identities.contains_key(name))
        {
            return false;
        }
        for (module, order) in &self.modules {
            if module.is_anon()
                || !order.contains(module)
                || order.iter().collect::<HashSet<_>>().len() != order.len()
            {
                return false;
            }
        }
        let visible_modules: HashMap<_, HashSet<_>> = self
            .modules
            .iter()
            .map(|(module, names)| (module.clone(), names.iter().cloned().collect()))
            .collect();
        let mut ordinals = HashMap::new();
        let mut registrations: HashMap<_, HashSet<_>> = HashMap::new();
        for record in &self.inline {
            let ordinal = ordinals
                .entry((record.module.clone(), record.name.clone()))
                .or_insert(0);
            if record.ordinal != *ordinal {
                return false;
            }
            *ordinal += 1;
            registrations
                .entry((record.name.clone(), record.mode))
                .or_default()
                .insert(record.module.clone());
        }
        // Interned contexts are shared by many bodies. Backing/visibility is
        // the same for one (context, owner), so judge it once, not per body.
        let mut checked = HashSet::new();
        for (body, id) in &self.body_inline {
            let Some(view) = self.inline_views.get(*id) else {
                return false;
            };
            let module = &self.body_modules[body];
            let visible = match module {
                Some(owner) => match visible_modules.get(owner) {
                    Some(names) => Some(names),
                    None => return false,
                },
                None => None,
            };
            if !checked.insert((*id, module.clone())) {
                continue;
            }
            for (name, mode) in view {
                let Some(origins) = registrations.get(&(name.clone(), *mode)) else {
                    return false;
                };
                if !origins.iter().any(|origin| {
                    origin
                        .as_ref()
                        .is_none_or(|origin| visible.is_none_or(|v| v.contains(origin)))
                }) {
                    return false;
                }
            }
        }
        true
    }
    fn matches_environment(&self, env: &Environment, require_origins: bool) -> bool {
        if !self.valid_shape()
            || self.identities.iter().any(|(name, expected)| {
                env.compiler_declaration_digest(name).as_ref() != Some(expected)
            })
        {
            return false;
        }
        if !require_origins {
            return true;
        }
        let origin_matches =
            |name: &Name, owner: &Option<Name>| match (owner, env.get_constant_origin(name)) {
                (
                    Some(owner),
                    Some(
                        super::ConstantOrigin::Olean {
                            module: Some(origin),
                            ..
                        }
                        | super::ConstantOrigin::CleanPayload {
                            module: Some(origin),
                            ..
                        },
                    ),
                ) => {
                    let origin = origin
                        .strip_suffix("._server")
                        .or_else(|| origin.strip_suffix("._private"))
                        .unwrap_or(origin);
                    *owner == Name::from_string(origin)
                }
                (None, Some(super::ConstantOrigin::Kernel { .. })) => true,
                _ => false,
            };
        self.inline
            .iter()
            .all(|r| origin_matches(&r.name, &r.module))
            && self
                .body_modules
                .iter()
                .all(|(name, owner)| origin_matches(name, owner))
    }
}

fn import_snapshot(
    env: &mut Environment,
    entries: &[EnvExtensionEntry],
    require_origins: bool,
    required: &[(Name, Name, [u8; 32])],
) {
    let decoded: Option<Vec<_>> = entries
        .iter()
        .map(|entry| match Entry::from_env_entry(entry) {
            Some(Entry::Portable(snapshot))
                if snapshot.matches_environment(env, require_origins) =>
            {
                Some(snapshot)
            }
            _ => None,
        })
        .collect();
    let Some(snapshots) = decoded else {
        env.add_ext_entry::<State>(index(), &Entry::Invalid);
        return;
    };
    // Coverage is required by a source-built payload, not inferred from the
    // rows it happened to include. Otherwise an empty or truncated snapshot
    // would validate vacuously and erase a deferred macro's execution policy.
    if required.iter().any(|(owner, name, digest)| {
        !snapshots.iter().any(|snapshot| {
            snapshot.bodies.contains_key(name)
                && snapshot.body_modules.get(name).and_then(Option::as_ref) == Some(owner)
                && snapshot.identities.get(name) == Some(digest)
        })
    }) {
        env.add_ext_entry::<State>(index(), &Entry::Invalid);
        return;
    }
    let mut trial = env
        .get_ext_state::<State>(index())
        .cloned()
        .unwrap_or_default();
    for snapshot in &snapshots {
        trial.add_entry(&Entry::Portable(snapshot.clone()));
    }
    if trial.invalid {
        env.add_ext_entry::<State>(index(), &Entry::Invalid);
        return;
    }
    for snapshot in snapshots {
        env.add_ext_entry::<State>(index(), &Entry::Portable(snapshot));
    }
}
/// Untrusted producers that deliberately rewrite runtime bodies must rebind
/// their metadata identities to those new constants. This does not check the
/// constants or replay their compilation: the ordinary import/kernel gates
/// must still judge the resulting artifact.
pub fn refresh_compilation_identities(
    entries: &[EnvExtensionEntry],
    constants: &[super::ConstantInfo],
) -> Result<Vec<EnvExtensionEntry>, String> {
    let replacements: HashMap<_, _> = constants
        .iter()
        .map(|info| (info.name.clone(), info.compiler_identity_digest()))
        .collect();
    entries
        .iter()
        .map(|entry| {
            let Some(Entry::Portable(mut snapshot)) = Entry::from_env_entry(entry) else {
                return Err("malformed compiler snapshot".into());
            };
            if !snapshot.valid_shape() {
                return Err("malformed compiler snapshot".into());
            }
            for (name, digest) in &mut snapshot.identities {
                if let Some(replacement) = replacements.get(name) {
                    *digest = *replacement;
                }
            }
            Ok(Entry::Portable(snapshot).to_env_entry())
        })
        .collect()
}

/// Merge portable compiler context, binding it to actual declarations and
/// rejecting stale, malformed, or conflicting evidence without changing values.
pub fn import_compilation_snapshot(env: &mut Environment, entries: &[EnvExtensionEntry]) {
    import_snapshot(env, entries, false, &[]);
}
/// Artifact import also requires each hint/body to belong to its recorded
/// defining module. Locally seeded context must still name a kernel resident.
pub fn import_artifact_compilation_snapshot(env: &mut Environment, entries: &[EnvExtensionEntry]) {
    import_snapshot(env, entries, true, &[]);
}

/// Import a source producer's compiler context with complete coverage of its
/// own body-bearing definitions. These are advisory source-time records, not
/// evidence that native code or a mathematical proof has been verified.
pub fn import_artifact_source_compilation_snapshot(
    env: &mut Environment,
    entries: &[EnvExtensionEntry],
    module: &Name,
    constants: &[super::ConstantInfo],
) {
    let required: Vec<_> = constants
        .iter()
        .filter(|info| {
            info.value.is_some()
                && matches!(
                    info.kind,
                    super::ConstantKind::Definition | super::ConstantKind::Opaque
                )
        })
        .map(|info| {
            (
                module.clone(),
                info.name.clone(),
                info.compiler_identity_digest(),
            )
        })
        .collect();
    import_snapshot(env, entries, true, &required);
}

/// A body has an actual source-time compiler context. Presence alone is not
/// proof of executable code; absence must never grant code to an imported body.
pub fn has_compilation_context(env: &Environment, name: &Name) -> bool {
    env.get_ext_state::<State>(index()).is_some_and(|state| {
        !state.invalid
            && (state.cutoffs.contains_key(name) || state.imported_bodies.contains_key(name))
    })
}

#[cfg(test)]
mod effect_tests {
    use super::*;

    fn declare(env: &mut Environment, name: &str) {
        env.add_decl(crate::Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        })
        .expect("genuine logical definition");
    }
    fn module(env: &mut Environment, name: &str) {
        begin_source_module(env, Name::from_string(name), vec![]);
        declare(env, &format!("{name}.body"));
        record_compiled(env, [Name::from_string(&format!("{name}.body"))]);
    }

    #[test]
    fn exported_compiler_delta_keeps_inherited_inline_backing() {
        let n = Name::from_string;
        let mut base = Environment::new();
        begin_source_module(&mut base, n("Init"), vec![]);
        declare(&mut base, "Init.helper");
        base.register_macro_inline(n("Init.helper"));
        record_compiled(&mut base, [n("Init.helper")]);

        let mut source = base.clone();
        begin_source_module(&mut source, n("Caller"), vec![n("Init")]);
        declare(&mut source, "Caller.body");
        record_compiled(&mut source, [n("Caller.body")]);

        let entries = export_compilation_snapshot_over(&source, &base);
        let Some(Entry::Portable(snapshot)) = Entry::from_env_entry(&entries[0]) else {
            panic!("expected a portable compiler snapshot");
        };
        assert!(snapshot.valid_shape());
        assert!(!snapshot.bodies.contains_key(&n("Init.helper")));
        assert!(!snapshot.body_inline.contains_key(&n("Init.helper")));
        assert!(!snapshot.body_modules.contains_key(&n("Init.helper")));
        let view = &snapshot.inline_views[snapshot.body_inline[&n("Caller.body")]];
        assert_eq!(view.get(&n("Init.helper")), Some(&InlineMode::MacroInline));
        assert_eq!(snapshot.body_modules[&n("Caller.body")], Some(n("Caller")));
    }

    #[test]
    fn imported_module_graph_preserves_caller_and_sibling_visibility() {
        let n = Name::from_string;
        let mut env = Environment::new();
        begin_source_module(&mut env, n("Caller"), vec![]);
        record_imported_module(&mut env, n("B"), vec![]);
        record_imported_module(&mut env, n("C"), vec![n("B")]);
        let replacement = Rule {
            theorem: n("B.eq"),
            from: n("f"),
            to: n("g"),
        };
        env.add_ext_entry::<State>(
            index(),
            &Entry::Event(Event::Activate {
                rule: replacement.clone(),
                local: None,
                module: Some(n("B")),
            }),
        );
        assert!(
            rules_for(&env, None).is_empty(),
            "preloading must not switch Caller to B"
        );
        begin_source_module(&mut env, n("UsesC"), vec![n("C")]);
        assert_eq!(rules_for(&env, None), vec![replacement.clone()]);
        begin_source_module(&mut env, n("Sibling"), vec![]);
        assert!(rules_for(&env, None).is_empty());
        let snapshot = export_compilation_snapshot(&env);
        let mut restored = Environment::new();
        import_compilation_snapshot(&mut restored, &snapshot);
        import_compilation_snapshot(&mut restored, &snapshot);
        begin_source_module(&mut restored, n("UsesC"), vec![n("C")]);
        assert_eq!(rules_for(&restored, None), vec![replacement]);
        begin_source_module(&mut restored, n("Sibling"), vec![]);
        assert!(rules_for(&restored, None).is_empty());
    }

    #[test]
    fn imported_scoped_rules_require_their_owner_before_namespace_activation() {
        let n = Name::from_string;
        let mut env = Environment::new();
        record_imported_module(&mut env, n("B"), vec![]);
        let replacement = Rule {
            theorem: n("B.eq"),
            from: n("f"),
            to: n("g"),
        };
        env.add_ext_entry::<State>(
            index(),
            &Entry::ImportedScoped(n("N"), replacement.clone(), n("B")),
        );
        begin_source_module(&mut env, n("Sibling"), vec![]);
        assert!(activate_namespace(&mut env, &n("N")).unwrap().is_empty());
        assert!(rules_for(&env, None).is_empty());
        begin_source_module(&mut env, n("UsesB"), vec![n("B")]);
        assert!(rules_for(&env, None).is_empty());
        let tokens = activate_namespace(&mut env, &n("N")).unwrap();
        assert_eq!(tokens.len(), 1);
        assert_eq!(rules_for(&env, None), vec![replacement]);
        retire_local(&mut env, tokens[0]);
        assert!(rules_for(&env, None).is_empty());
    }

    #[test]
    fn independent_sibling_compilation_records_agree() {
        let base = Environment::new();
        let mut own = base.clone();
        module(&mut own, "Q");
        let mut stranger = base.clone();
        module(&mut stranger, "P");
        let mut shared = stranger.clone();
        module(&mut shared, "Q");
        assert_eq!(
            own.effect_since(&base)
                .disagreement(&shared.effect_since(&stranger), &shared),
            None
        );
    }

    #[test]
    fn changed_compilation_rules_still_disagree() {
        let base = Environment::new();
        let mut own = base.clone();
        module(&mut own, "Q");
        let mut stranger = base.clone();
        module(&mut stranger, "P");
        let mut shared = stranger.clone();
        begin_source_module(&mut shared, Name::from_string("Q"), vec![]);
        shared.add_ext_entry::<State>(
            index(),
            &Entry::Event(Event::Activate {
                rule: Rule {
                    theorem: Name::from_string("replacement"),
                    from: Name::from_string("f"),
                    to: Name::from_string("g"),
                },
                local: None,
                module: Some(Name::from_string("Q")),
            }),
        );
        record_compiled(&mut shared, [Name::from_string("Q.body")]);
        assert!(own
            .effect_since(&base)
            .disagreement(&shared.effect_since(&stranger), &shared)
            .is_some());
    }

    #[test]
    fn malformed_compilation_effect_retains_raw_evidence() {
        let entries = vec![EnvExtensionEntry {
            name: Name::from_string("snapshot.v2"),
            data: EnvExtensionEntryData::Object(vec![255]),
        }];
        assert_eq!(effect_entries(&entries), entries);
    }
    #[test]
    fn inline_modes_preserve_body_time_and_survive_portable_replay() {
        let n = Name::from_string;
        let mut env = Environment::new();
        begin_source_module(&mut env, n("A"), vec![]);
        for name in ["before", "during", "after", "helper"] {
            declare(&mut env, name);
        }
        record_compiled(&mut env, [n("before")]);
        env.register_macro_inline(n("helper"));
        record_compiled(&mut env, [n("during")]);
        env.register_noinline(n("helper"));
        record_compiled(&mut env, [n("after")]);
        assert!(!env.is_macro_inline(&n("helper")));
        assert!(env.is_noinline(&n("helper")));
        let snapshot = export_compilation_snapshot(&env);
        // Replaying an own snapshot or a diamond must not duplicate events.
        let events = env
            .get_ext_state::<State>(index())
            .expect("state")
            .events
            .len();
        import_compilation_snapshot(&mut env, &snapshot);
        import_compilation_snapshot(&mut env, &snapshot);
        assert_eq!(
            env.get_ext_state::<State>(index())
                .expect("state")
                .events
                .len(),
            events
        );
        assert!(!has_invalid_metadata(&env));
        let mut restored = Environment::new();
        for name in ["before", "during", "after", "helper"] {
            declare(&mut restored, name);
        }
        import_compilation_snapshot(&mut restored, &snapshot);
        import_compilation_snapshot(&mut restored, &snapshot);
        for env in [&env, &restored] {
            assert_eq!(inline_mode_at(env, Some(&n("before")), &n("helper")), None);
            assert_eq!(
                inline_mode_at(env, Some(&n("during")), &n("helper")),
                Some(InlineMode::MacroInline)
            );
            assert_eq!(
                inline_mode_at(env, Some(&n("after")), &n("helper")),
                Some(InlineMode::NoInline)
            );
            assert!(!has_invalid_metadata(env));
        }
    }

    #[test]
    fn inline_sibling_visibility_is_independent_of_preload_order() {
        let n = Name::from_string;
        for preload in [["B", "C"], ["C", "B"]] {
            let mut env = Environment::new();
            for name in ["B.helper", "C.helper", "UsesB.body"] {
                declare(&mut env, name);
            }
            for module in preload {
                record_imported_module(&mut env, n(module), vec![]);
                import_inline_mode(
                    &mut env,
                    n(module),
                    n(&format!("{module}.helper")),
                    InlineMode::MacroInline,
                );
            }
            begin_source_module(&mut env, n("UsesB"), vec![n("B")]);
            assert!(env.is_macro_inline(&n("B.helper")));
            assert!(!env.is_macro_inline(&n("C.helper")));
            record_compiled(&mut env, [n("UsesB.body")]);
            let mut restored = Environment::new();
            for name in ["B.helper", "C.helper", "UsesB.body"] {
                declare(&mut restored, name);
            }
            import_compilation_snapshot(&mut restored, &export_compilation_snapshot(&env));
            assert!(!has_invalid_metadata(&restored));
            assert_eq!(
                inline_mode_at(&restored, Some(&n("UsesB.body")), &n("B.helper")),
                Some(InlineMode::MacroInline)
            );
            assert_eq!(
                inline_mode_at(&restored, Some(&n("UsesB.body")), &n("C.helper")),
                None
            );
            begin_source_module(&mut restored, n("OnlyC"), vec![n("C")]);
            assert!(!restored.is_macro_inline(&n("B.helper")));
            assert!(restored.is_macro_inline(&n("C.helper")));
        }
    }

    #[test]
    fn every_inline_mode_replaces_the_previous_mode() {
        let n = Name::from_string;
        let mut env = Environment::new();
        declare(&mut env, "f");
        for mode in [
            InlineMode::Inline,
            InlineMode::NoInline,
            InlineMode::MacroInline,
            InlineMode::InlineIfReduce,
            InlineMode::AlwaysInline,
        ] {
            register_inline_mode(&mut env, n("f"), mode);
            assert_eq!(env.is_inline(&n("f")), mode == InlineMode::Inline);
            assert_eq!(env.is_noinline(&n("f")), mode == InlineMode::NoInline);
            assert_eq!(
                env.is_macro_inline(&n("f")),
                mode == InlineMode::MacroInline
            );
            assert_eq!(
                env.is_inline_if_reduce(&n("f")),
                mode == InlineMode::InlineIfReduce
            );
            assert_eq!(
                env.is_always_inline(&n("f")),
                mode == InlineMode::AlwaysInline
            );
        }
    }

    #[test]
    fn stale_and_conflicting_inline_snapshots_are_invalid() {
        let n = Name::from_string;
        let mut original = Environment::new();
        begin_source_module(&mut original, n("A"), vec![]);
        declare(&mut original, "f");
        declare(&mut original, "A.body");
        original.register_macro_inline(n("f"));
        record_compiled(&mut original, [n("A.body")]);
        let snapshot = original
            .get_ext_state::<State>(index())
            .expect("state")
            .snapshot();
        for corrupt in 0..5 {
            let mut altered = snapshot.clone();
            match corrupt {
                0 => {
                    altered.body_inline.clear();
                }
                1 => {
                    altered.inline[0].mode = InlineMode::NoInline;
                }
                2 => {
                    altered.inline[0].ordinal = 1;
                }
                3 => {
                    altered.modules.insert(n("A"), vec![n("A"), n("A")]);
                }
                _ => {
                    altered.version = 1;
                }
            }
            let mut restored = Environment::new();
            declare(&mut restored, "f");
            declare(&mut restored, "A.body");
            import_compilation_snapshot(
                &mut restored,
                &[Entry::Portable(snapshot.clone()).to_env_entry()],
            );
            import_compilation_snapshot(&mut restored, &[Entry::Portable(altered).to_env_entry()]);
            assert!(has_invalid_metadata(&restored), "corruption {corrupt}");
        }
        let mut restored = Environment::new();
        import_compilation_snapshot(
            &mut restored,
            &[EnvExtensionEntry {
                name: n("snapshot.v1"),
                data: EnvExtensionEntryData::Object(vec![]),
            }],
        );
        assert!(has_invalid_metadata(&restored));
    }
    #[test]
    fn inline_contexts_are_interned_and_have_bounded_transport_growth() {
        let mut env = Environment::new();
        begin_source_module(&mut env, Name::from_string("Many"), vec![]);
        for i in 0..128 {
            let name = format!("Many.helper{i}");
            declare(&mut env, &name);
            env.register_macro_inline(Name::from_string(&name));
        }
        for i in 0..128 {
            let name = format!("Many.body{i}");
            declare(&mut env, &name);
            record_compiled(&mut env, [Name::from_string(&name)]);
        }
        let snapshot = env
            .get_ext_state::<State>(index())
            .expect("state")
            .snapshot();
        assert!(snapshot.valid_shape());
        assert_eq!(snapshot.inline_views.len(), 1);
        let bytes = bincode::serde::encode_to_vec(&snapshot, bincode::config::standard())
            .expect("serialize context");
        assert!(
            bytes.len() < 60_000,
            "shared compiler contexts must not grow as bodies times hints: {}",
            bytes.len()
        );
        let effects = effect_entries(&[Entry::Portable(snapshot).to_env_entry()]);
        let total: usize = effects
            .iter()
            .map(|entry| match &entry.data {
                EnvExtensionEntryData::Object(bytes) => bytes.len(),
                _ => 0,
            })
            .sum();
        assert!(
            total < 60_000,
            "effect normalization must retain shared contexts: {total}"
        );
    }

    #[test]
    fn inline_snapshot_requires_real_identity_and_backing_mode_records() {
        let n = Name::from_string;
        let mut original = Environment::new();
        declare(&mut original, "f");
        declare(&mut original, "caller");
        original.register_macro_inline(n("f"));
        record_compiled(&mut original, [n("caller")]);
        let snapshot = original
            .get_ext_state::<State>(index())
            .expect("state")
            .snapshot();
        let mut malformed_order = snapshot.clone();
        malformed_order.inline[0].ordinal = 1;
        let mut fresh_order = Environment::new();
        declare(&mut fresh_order, "f");
        declare(&mut fresh_order, "caller");
        import_compilation_snapshot(
            &mut fresh_order,
            &[Entry::Portable(malformed_order).to_env_entry()],
        );
        assert!(has_invalid_metadata(&fresh_order));
        assert!(
            !fresh_order.is_macro_inline(&n("f")),
            "a rejected first import must not install its marker"
        );
        let mut phantom = snapshot.clone();
        phantom.inline.clear();
        let mut fresh = Environment::new();
        declare(&mut fresh, "f");
        declare(&mut fresh, "caller");
        import_compilation_snapshot(&mut fresh, &[Entry::Portable(phantom).to_env_entry()]);
        assert!(has_invalid_metadata(&fresh));
        assert!(!fresh.is_macro_inline(&n("f")));
        let mut shadowed = Environment::new();
        shadowed
            .add_decl(crate::Declaration::Axiom {
                name: n("f"),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())),
            })
            .expect("different resident");
        declare(&mut shadowed, "caller");
        import_compilation_snapshot(&mut shadowed, &[Entry::Portable(snapshot).to_env_entry()]);
        assert!(has_invalid_metadata(&shadowed));
        assert!(!shadowed.is_macro_inline(&n("f")));
        assert_eq!(inline_mode_at(&shadowed, Some(&n("caller")), &n("f")), None);
    }
    #[test]
    fn source_header_refresh_is_allowed_and_earlier_bodies_keep_their_view() {
        let n = Name::from_string;
        let mut env = Environment::new();
        for name in ["B.helper", "Caller.before", "Caller.after"] {
            declare(&mut env, name);
        }
        record_imported_module(&mut env, n("B"), vec![]);
        import_inline_mode(&mut env, n("B"), n("B.helper"), InlineMode::MacroInline);
        begin_source_module(&mut env, n("Caller"), vec![]);
        record_compiled(&mut env, [n("Caller.before")]);
        begin_source_module(&mut env, n("Caller"), vec![n("B")]);
        record_compiled(&mut env, [n("Caller.after")]);
        assert!(!has_invalid_metadata(&env));
        assert_eq!(
            inline_mode_at(&env, Some(&n("Caller.before")), &n("B.helper")),
            None
        );
        assert_eq!(
            inline_mode_at(&env, Some(&n("Caller.after")), &n("B.helper")),
            Some(InlineMode::MacroInline)
        );
    }

    #[test]
    fn compiler_identity_works_for_lazy_constants_and_ignores_reducibility() {
        #[derive(Debug)]
        struct Lazy(crate::env::ConstantInfo);
        impl crate::env::ConstantSource for Lazy {
            fn get(&self, name: &Name) -> Option<&crate::env::ConstantInfo> {
                (name == &self.0.name).then_some(&self.0)
            }
            fn contains(&self, name: &Name) -> bool {
                name == &self.0.name
            }
        }
        let name = Name::from_string("f");
        let mut eager = Environment::new();
        declare(&mut eager, "f");
        let digest = eager
            .compiler_declaration_digest(&name)
            .expect("eager identity");
        let mut lazy = Environment::new();
        lazy.set_constant_source(Arc::new(Lazy(
            eager.get_const(&name).expect("definition").clone(),
        )));
        assert_eq!(lazy.compiler_declaration_digest(&name), Some(digest));
        lazy.register_macro_inline(name.clone());
        record_compiled(&mut lazy, [name.clone()]);
        assert!(lazy
            .get_ext_state::<State>(index())
            .expect("state")
            .snapshot()
            .valid_shape());
        assert!(eager.set_reducibility(&name, super::super::Reducibility::Irreducible));
        assert_eq!(eager.compiler_declaration_digest(&name), Some(digest));
    }

    #[test]
    fn compiler_effects_bind_body_origin_and_declaration_identity() {
        let n = Name::from_string;
        let mut env = Environment::new();
        declare(&mut env, "f");
        begin_source_module(&mut env, n("A"), vec![]);
        env.register_macro_inline(n("f"));
        record_compiled(&mut env, [n("f")]);
        let snapshot = env
            .get_ext_state::<State>(index())
            .expect("state")
            .snapshot();
        let effects = effect_entries(&[Entry::Portable(snapshot.clone()).to_env_entry()]);
        let mut changed = snapshot.clone();
        changed.identities.get_mut(&n("f")).expect("identity")[0] ^= 1;
        assert_ne!(
            effects,
            effect_entries(&[Entry::Portable(changed).to_env_entry()])
        );
        let mut changed = snapshot;
        changed.body_modules.insert(n("f"), None);
        assert_ne!(
            effects,
            effect_entries(&[Entry::Portable(changed).to_env_entry()])
        );
    }
    #[test]
    fn source_payload_requires_context_for_every_own_definition_before_hint_replay() {
        let n = Name::from_string;
        let mut source = Environment::new();
        begin_source_module(&mut source, n("M"), vec![]);
        declare(&mut source, "f");
        declare(&mut source, "g");
        source.register_macro_inline(n("f"));
        record_compiled(&mut source, [n("f")]);
        let partial = export_compilation_snapshot(&source);
        record_compiled(&mut source, [n("g")]);
        let complete = export_compilation_snapshot(&source);
        let constants: Vec<_> = ["f", "g"]
            .iter()
            .map(|name| source.get_const(&n(name)).expect("source constant").clone())
            .collect();
        let mut empty = Environment::new();
        begin_source_module(&mut empty, n("M"), vec![]);
        let empty = export_compilation_snapshot(&empty);
        for (entries, accepted) in [
            (vec![], false),
            (empty, false),
            (partial, false),
            (complete, true),
        ] {
            let mut loaded = Environment::new();
            for name in ["f", "g"] {
                declare(&mut loaded, name);
                assert!(loaded.set_constant_origin(
                    n(name),
                    super::super::ConstantOrigin::clean_payload(Some("M".into()))
                ));
            }
            import_artifact_source_compilation_snapshot(&mut loaded, &entries, &n("M"), &constants);
            assert_eq!(!has_invalid_metadata(&loaded), accepted);
            assert_eq!(
                loaded.is_macro_inline(&n("f")),
                accepted,
                "incomplete context must not apply its hint"
            );
        }
    }

    #[test]
    fn shared_inline_view_still_checks_each_distinct_owner() {
        let n = Name::from_string;
        let mut env = Environment::new();
        begin_source_module(&mut env, n("M"), vec![]);
        declare(&mut env, "helper");
        declare(&mut env, "A.body");
        env.register_macro_inline(n("helper"));
        record_compiled(&mut env, [n("A.body")]);
        begin_source_module(&mut env, n("N"), vec![]);
        declare(&mut env, "Z.body");
        record_compiled(&mut env, [n("Z.body")]);
        let mut snapshot = env
            .get_ext_state::<State>(index())
            .expect("state")
            .snapshot();
        assert!(snapshot.valid_shape());
        let view = snapshot.body_inline[&n("A.body")];
        snapshot.body_inline.insert(n("Z.body"), view);
        assert!(
            !snapshot.valid_shape(),
            "sharing a view cannot grant another owner an invisible hint"
        );
    }
}
