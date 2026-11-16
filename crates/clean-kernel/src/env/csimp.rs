// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source compilation-point state for compiler simplification.
//! Kernel checking/reduction never consult this state. Portable snapshots carry
//! resolved per-body rules, never offsets into a source session event stream.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use super::{
    register_persistent_ext, EnvExtensionEntry, EnvExtensionEntryData, Environment, ExtensionIdx,
    PersistentExtEntry, PersistentExtState,
};
use crate::{Expr, ExprKind, Level, Name};

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
    bodies: std::collections::BTreeMap<Name, Vec<Rule>>,
    modules: std::collections::BTreeMap<Name, Vec<Name>>,
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
                name: Name::from_string("snapshot.v1"),
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
            Self::Compiled(name) => name.clone(),
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
                if entry.name == Name::from_string("snapshot.v1") =>
            {
                bincode::serde::decode_from_slice::<Snapshot, _>(
                    bytes,
                    bincode::config::standard().with_limit::<{ 256 * 1024 * 1024 }>(),
                )
                .ok()
                .filter(|(snapshot, consumed)| snapshot.version == 1 && *consumed == bytes.len())
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct State {
    events: Arc<Vec<Event>>,
    imported_bodies: Arc<HashMap<Name, Vec<Rule>>>,
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
            Entry::Portable(snapshot) => self.import(snapshot),
            Entry::Event(event) => Arc::make_mut(&mut self.events).push(event.clone()),
            Entry::Scoped(namespace, rule) => Arc::make_mut(&mut self.scoped).push((
                namespace.clone(),
                rule.clone(),
                self.view.module.clone(),
            )),
            Entry::ImportedScoped(namespace, rule, module) => Arc::make_mut(&mut self.scoped)
                .push((namespace.clone(), rule.clone(), Some(module.clone()))),
            Entry::Module(module, imports) | Entry::ImportedModule(module, imports) => {
                let mut visible = HashSet::from([module.clone()]);
                for import in imports {
                    visible.insert(import.clone());
                    if let Some(view) = self.modules.get(import) {
                        visible.extend(view.visible.iter().cloned());
                    }
                }
                let view = Arc::new(View {
                    module: Some(module.clone()),
                    visible,
                });
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
        let mut bodies: std::collections::BTreeMap<_, _> = self
            .imported_bodies
            .iter()
            .map(|(n, r)| (n.clone(), r.clone()))
            .collect();
        for name in self.cutoffs.keys() {
            bodies
                .entry(name.clone())
                .or_insert_with(|| self.body_rules(name));
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
            version: 1,
            globals,
            scoped,
            bodies,
            modules,
            invalid: self.invalid,
        }
    }
    fn import(&mut self, snapshot: &Snapshot) {
        self.invalid |= snapshot.invalid;
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
        for (name, visible) in &snapshot.modules {
            let view = Arc::new(View {
                module: Some(name.clone()),
                visible: visible.iter().cloned().collect(),
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
fn select(events: &[Event], view: &View) -> Vec<Rule> {
    let mut selected = std::collections::BTreeMap::new();
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

/// Prevent optimizations from manufacturing a call that bypasses this boundary.
pub fn has_replacement(env: &Environment, name: &Name) -> bool {
    env.get_ext_state::<State>(index()).is_some_and(|s| {
        s.imported_bodies
            .values()
            .any(|rules| rules.iter().any(|r| r.from == *name))
            || s.events
                .iter()
                .any(|e| matches!(e, Event::Activate { rule, .. } if rule.from == *name))
    })
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
        let mut visible = HashSet::from([module.clone()]);
        for import in &imports {
            visible.insert(import.clone());
            if let Some(view) = s.modules.get(import) {
                visible.extend(view.visible.iter().cloned());
            }
        }
        s.view.module.as_ref() == Some(&module) && s.view.visible == visible
    }) {
        return;
    }
    env.add_ext_entry::<State>(index(), &Entry::Module(module, imports));
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
        snapshot
            .bodies
            .retain(|name, rules| base.bodies.get(name) != Some(rules));
        snapshot
            .modules
            .retain(|name, visible| base.modules.get(name) != Some(visible));
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
        Invalid,
    }
    let mut result = Vec::new();
    for entry in entries {
        let Some(Entry::Portable(snapshot)) = Entry::from_env_entry(entry) else {
            return entries.to_vec();
        };
        let mut records = Vec::new();
        let mut globals = std::collections::BTreeMap::<_, Vec<_>>::new();
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
        let mut scoped = std::collections::BTreeMap::<_, Vec<_>>::new();
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
        if snapshot.invalid {
            records.push(Record::Invalid);
        }
        for record in records {
            let Ok(bytes) = bincode::serde::encode_to_vec(&record, bincode::config::standard())
            else {
                return entries.to_vec();
            };
            result.push(EnvExtensionEntry {
                name: Name::from_string("effect.v1"),
                data: EnvExtensionEntryData::Object(bytes),
            });
        }
    }
    result
}
/// Merge portable compiler context without replaying source event offsets.
pub fn import_compilation_snapshot(env: &mut Environment, entries: &[EnvExtensionEntry]) {
    for entry in entries {
        let decoded = Entry::from_env_entry(entry).unwrap_or(Entry::Invalid);
        env.add_ext_entry::<State>(index(), &decoded);
    }
}

#[cfg(test)]
mod effect_tests {
    use super::*;

    fn module(env: &mut Environment, name: &str) {
        begin_source_module(env, Name::from_string(name), vec![]);
        record_compiled(env, [Name::from_string(&format!("{name}.body"))]);
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
            name: Name::from_string("snapshot.v1"),
            data: EnvExtensionEntryData::Object(vec![255]),
        }];
        assert_eq!(effect_entries(&entries), entries);
    }
}
