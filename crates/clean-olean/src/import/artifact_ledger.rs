// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which ARTIFACT declared each imported name, and the three rules that
//! depend on it — for every artifact kind, Lean-built `.olean` records and
//! Clean payloads alike:
//!
//! 1. **One name, one declaration.** An artifact part that declares a name
//!    twice is refused ([`ImportError::DuplicateDeclaration`]); a record whose
//!    name a *different* artifact already declared is refused unless it is
//!    a second proof, or axiom stub, of the same statement
//!    ([`ImportError::ConflictingDeclaration`]), as Lean refuses the import
//!    (`environment already contains 'D.v' from Z`). Before module-trust
//!    round 29 this held for Clean payloads only: two Lean-built modules, or a
//!    Clean-built module imported before a Lean-built one, still let the
//!    FIRST loaded declaration win silently (N3, N3p), and one Lean-built
//!    part declaring a name twice let the later record win (N2r).
//! 2. **Closed over its imports.** A name an artifact referenced while no
//!    artifact had declared it may not be supplied afterwards by a different
//!    artifact ([`ImportError::ForwardReference`]): every Lean artifact is
//!    built against its imports, which are loaded before it.
//! 3. **No declaration depends on itself.** A definitional dependency cycle
//!    among safe declarations is refused ([`ImportError::DefinitionalCycle`]):
//!    Lean's kernel admits no such declaration, and unfolding one loops (C1:
//!    `V0.v := Nat.succ V0.v` hung `clean check` in `reduce_nat` before any
//!    re-check could refuse it).
//!
//! 4. **One artifact, one meaning.** A later part of an artifact that
//!    names a declaration an earlier part already holds must say the same
//!    thing about it as that part did ([`ImportError::PartsDisagree`]); the
//!    only exception is Lean's module-system stub, a value-free record a later
//!    part completes, which the kernel re-checks at the upgrade. Before
//!    module-trust round 30 the later record was dropped unread: a genuine
//!    Lean-built `D.olean` saying `D.e := 1` beside a `D.olean.private` whose
//!    record said `D.e := 0` let `D.e = 1` pass, while `lean` reads that
//!    module as `D.e := 0` (X1).
//!
//!    Rule 4 covers every elaborator table Clean reads from an artifact as
//!    well — instances, classes, simp lemmas, aliases, structure tables, and
//!    a Clean-built artifact's named entries ([`ImportError::PartsDisagreeOnEntry`]),
//!    after Lean's levels: a module-system artifact's `.olean` states what
//!    it exports, the `.olean.server` states that again and more, and the
//!    `.olean.private` states everything (each level's entries include the
//!    previous level's); a consumer that is not itself a `module` — every
//!    file Clean checks — reads the private part's. Any other artifact is
//!    read through its `.olean` alone, so a companion part of it states
//!    nothing the `.olean` does not. Before module-trust round 31 the tables
//!    of every part were merged: a server part alone naming another
//!    instance, or a base part raising one's priority, decided `I.C.val`
//!    where `lean` reads the private part.
//!
//!    And a load of an artifact met before is held to the one meaning the
//!    environment already has for it, by the same rule as the parts of one
//!    load: a value-free record of a name that has a value is the stub of a
//!    later part of the SAME load, which must state that value; one no later
//!    part completes refuses the import when the load ends. (Round 30 accepted
//!    such a stub on a second load while refusing it within one.)
//!
//! An artifact is a module: its `.olean`, `.olean.server` and `.olean.private`
//! parts are loaded under the labels `M`, `M._server` and `M._private` but
//! are ONE artifact. The part → artifact binding is recorded here rather
//! than read back from the label, because a module literally named
//! `M._private` is a different artifact that would carry the same label; a
//! label bound to two artifacts is refused
//! ([`ImportError::AmbiguousModuleLabel`]).

use super::ImportError;
use crate::module::typed_extensions::{TypedExtension, TypedExtensionEntry};
use clean_kernel::env::ConstantInfo;
use clean_kernel::env::{
    register_persistent_ext, ConstantOrigin, EnvExtensionEntry, EnvExtensionEntryData, Environment,
    ExtensionIdx, PersistentExtEntry, PersistentExtState,
};
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use clean_kernel::name::Name;
use hashbrown::{HashMap, HashSet};

#[path = "artifact_axioms.rs"]
mod axioms;
#[path = "artifact_ledger_graph.rs"]
mod graph;
pub use axioms::is_authoritative_lean_axiom;
pub(super) use axioms::observe_authoritative_axioms;
use graph::{first_cycle, references};

/// The artifact a part belongs to: its base module's name.
pub(crate) type ArtifactKey = Option<String>;

/// No entries: the ledger is in-process state, never exported or imported.
#[derive(Clone, Debug)]
pub(crate) struct NoLedgerEntry;

impl PersistentExtEntry for NoLedgerEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: Name::anon(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

/// Per-environment record of the artifacts loaded so far.
#[derive(Clone, Debug, Default)]
pub(crate) struct ArtifactLedger {
    /// Origin label (a part's module name) → the artifact it belongs to.
    parts: HashMap<Option<String>, ArtifactKey>,
    /// Original axiom signatures observed at whole-artifact completion.
    axioms: axioms::ImportedAxioms,
    /// Names some artifact referenced while nothing declared them, and the
    /// first artifact that did.
    unresolved: HashMap<Name, ArtifactKey>,
    /// The artifact whose parts are being loaded, and the names its earlier
    /// parts added — a later part of the SAME artifact may supply a name an
    /// earlier part referenced, so a cycle may span its parts.
    current: Option<(ArtifactKey, Vec<Name>)>,
    /// The artifact whose parts are being loaded, and every declaration its
    /// parts so far declared, AS READ — before anything registration does to
    /// the environment's copy afterwards (imported reducibility attributes,
    /// re-checks) — so a later part is compared with what an earlier part
    /// said, not with what the environment has since made of it.
    records: Option<(ArtifactKey, HashMap<Name, PartRecord>)>,
    /// Artifact → digest of every part of it loaded so far, so a part met
    /// again byte for byte (a second `load_module_with_deps` into one
    /// environment re-reads `Init`) is known to state nothing new.
    part_digests: HashMap<ArtifactKey, HashSet<[u8; 32]>>,
    /// The load of an artifact in progress: its parts' tables and the stubs
    /// a later part of it must complete.
    load: Option<ArtifactLoad>,
}

/// One entry of an elaborator table as Clean reads it: the extension and
/// the decoded record its registrar uses.
type EntryKey = (Name, TypedExtensionEntry);

/// The load of one artifact's parts, from its first part to its last.
#[derive(Clone, Debug)]
struct ArtifactLoad {
    artifact: ArtifactKey,
    /// Whether its first part is a module-system part (`isModule`).
    module_system: bool,
    /// Per part loaded so far, in order: the table entries Clean reads.
    entry_parts: Vec<HashSet<EntryKey>>,
    /// Value-free records of names the environment holds WITH a value (an
    /// earlier load of this artifact stated it), each of which a later part
    /// of this load must complete with that value.
    pending_stubs: HashSet<Name>,
}

/// One declaration as one part of an artifact states it.
#[derive(Clone, Debug)]
pub(crate) enum PartRecord {
    /// A definition, theorem, opaque or axiom, with the declaration safety
    /// the part gives it (`None` where the record carries none).
    Constant {
        /// The declaration.
        info: ConstantInfo,
        /// `safe` / `unsafe` / `partial`, as the record says.
        safety: Option<crate::DefinitionSafety>,
    },
    /// An inductive type, with its safety.
    Inductive(InductiveVal, Option<crate::DefinitionSafety>),
    /// A constructor, with its safety.
    Constructor(ConstructorVal, Option<crate::DefinitionSafety>),
    /// A recursor, the names of its mutual block, and its nested count, with
    /// its safety.
    Recursor(RecursorVal, Vec<Name>, u32, Option<crate::DefinitionSafety>),
}

impl PartRecord {
    /// The declared name.
    pub(crate) fn name(&self) -> &Name {
        match self {
            Self::Constant { info, .. } => &info.name,
            Self::Inductive(v, _) => &v.name,
            Self::Constructor(v, _) => &v.name,
            Self::Recursor(v, ..) => &v.name,
        }
    }

    /// Whether two parts say the same thing: every field the loader reads,
    /// compared structurally.
    fn same_as(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Constant {
                    info: a,
                    safety: sa,
                },
                Self::Constant {
                    info: b,
                    safety: sb,
                },
            ) => {
                sa == sb
                    && a.name == b.name
                    && a.kind == b.kind
                    && a.level_params == b.level_params
                    && a.type_ == b.type_
                    && a.value == b.value
                    && a.is_reducible == b.is_reducible
                    && a.reducibility == b.reducibility
            }
            (Self::Inductive(a, sa), Self::Inductive(b, sb)) => {
                sa == sb
                    && a.name == b.name
                    && a.level_params == b.level_params
                    && a.type_ == b.type_
                    && a.num_params == b.num_params
                    && a.num_indices == b.num_indices
                    && a.all_names == b.all_names
                    && a.constructor_names == b.constructor_names
                    && a.is_recursive == b.is_recursive
                    && a.is_reflexive == b.is_reflexive
                    && a.is_large_elim == b.is_large_elim
                    && a.is_nested == b.is_nested
            }
            (Self::Constructor(a, sa), Self::Constructor(b, sb)) => {
                sa == sb
                    && a.name == b.name
                    && a.inductive_name == b.inductive_name
                    && a.level_params == b.level_params
                    && a.type_ == b.type_
                    && a.num_params == b.num_params
                    && a.num_fields == b.num_fields
                    && a.constructor_idx == b.constructor_idx
            }
            (Self::Recursor(a, all_a, nested_a, sa), Self::Recursor(b, all_b, nested_b, sb)) => {
                let same_rule = |x: &RecursorRule, y: &RecursorRule| {
                    x.constructor_name == y.constructor_name
                        && x.num_fields == y.num_fields
                        && x.recursive_fields == y.recursive_fields
                        && x.rhs == y.rhs
                };
                sa == sb
                    && all_a == all_b
                    && nested_a == nested_b
                    && a.name == b.name
                    && a.arg_order == b.arg_order
                    && a.level_params == b.level_params
                    && a.type_ == b.type_
                    && a.inductive_name == b.inductive_name
                    && a.num_params == b.num_params
                    && a.num_indices == b.num_indices
                    && a.num_motives == b.num_motives
                    && a.num_minors == b.num_minors
                    && a.is_k == b.is_k
                    && a.rules.len() == b.rules.len()
                    && a.rules.iter().zip(&b.rules).all(|(x, y)| same_rule(x, y))
            }
            _ => false,
        }
    }
}

impl PersistentExtState for ArtifactLedger {
    type Entry = NoLedgerEntry;

    fn add_entry(&mut self, _entry: &Self::Entry) {}

    fn forget_declaration(&mut self, name: &Name) -> bool {
        self.axioms.forget_declaration(name)
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static ARTIFACT_LEDGER_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

fn ledger_idx() -> ExtensionIdx {
    *ARTIFACT_LEDGER_IDX.get_or_init(|| {
        register_persistent_ext::<ArtifactLedger>(Name::from_string("Clean.olean.artifactLedger"))
    })
}

fn display(key: &ArtifactKey) -> String {
    key.clone()
        .unwrap_or_else(|| "<unnamed module>".to_string())
}

/// Record that the part labelled `label` belongs to `artifact`. A label
/// already bound to a different artifact is refused: the constants of the
/// two would be indistinguishable by origin.
pub(crate) fn bind_part(
    env: &mut Environment,
    label: &Option<String>,
    artifact: &ArtifactKey,
) -> Result<(), ImportError> {
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    match ledger.parts.get(label) {
        Some(bound) if bound != artifact => Err(ImportError::AmbiguousModuleLabel {
            label: display(label),
            first: display(bound),
            second: display(artifact),
        }),
        Some(_) => Ok(()),
        None => {
            ledger.parts.insert(label.clone(), artifact.clone());
            Ok(())
        }
    }
}

/// The table entries of `entries` that rule 4 compares: every decoded row
/// of an elaborator table Clean registers (instances, classes, simp lemmas,
/// aliases, structure tables), and — for an artifact that is not a
/// module-system one, whose companions `lean` never reads — every other
/// named row too. A module-system artifact's other named rows (Lean's
/// `namespacesExt`, docstrings, …) are not compared: `lean` does not state
/// them cumulatively across the parts (measured: an honest Lean-built
/// module's `.olean` holds a `namespacesExt` row its `.olean.private` does
/// not), and Clean registers them from the part `lean` reads only
/// (`PartEntries::Read`), so a difference between the parts is not a second
/// meaning. Rows no registrar reads (`Unmeasured`, a legacy raw scalar) are
/// not entries of any table.
fn read_entries(entries: &[TypedExtension], module_system: bool) -> HashSet<EntryKey> {
    entries
        .iter()
        .flat_map(|extension| {
            extension
                .entries
                .iter()
                .filter_map(move |entry| match entry {
                    TypedExtensionEntry::Unmeasured { .. } | TypedExtensionEntry::RawScalar => None,
                    TypedExtensionEntry::Named { .. } if module_system => None,
                    _ => Some((extension.extension_name.clone(), entry.clone())),
                })
        })
        .collect()
}

fn entry_disagreement(artifact: &ArtifactKey, (extension, entry): &EntryKey) -> ImportError {
    let mut entry = format!("{entry:?}");
    if entry.len() > 200 {
        let mut end = 200;
        while !entry.is_char_boundary(end) {
            end -= 1;
        }
        entry.truncate(end);
        entry.push('…');
    }
    ImportError::PartsDisagreeOnEntry {
        module: display(artifact),
        extension: extension.to_string(),
        entry,
    }
}

/// End the load in progress, if any: every stub it left to a later part
/// must have been completed.
fn end_load(ledger: &mut ArtifactLedger) -> Result<(), ImportError> {
    let Some(load) = ledger.load.take() else {
        return Ok(());
    };
    let mut open: Vec<&Name> = load.pending_stubs.iter().collect();
    open.sort_by_key(|n| n.to_string());
    match open.first() {
        Some(name) => Err(ImportError::PartsDisagree {
            name: name.to_string(),
            module: display(&load.artifact),
        }),
        None => Ok(()),
    }
}

/// Begin loading `artifact`'s parts: the load before it ends (its stubs
/// must be complete), and `module_system` records whether the artifact's
/// first part is a module-system part. A loader that knows where an
/// artifact's parts begin says so here; a part loaded without it begins a
/// load of its own when the load in progress is another artifact's.
pub(crate) fn begin_artifact_load(
    env: &mut Environment,
    artifact: &ArtifactKey,
    module_system: bool,
) -> Result<(), ImportError> {
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    end_load(ledger)?;
    if let Some(module) = artifact {
        ledger.axioms.begin_load(module);
    }
    ledger.load = Some(ArtifactLoad {
        artifact: artifact.clone(),
        module_system,
        entry_parts: Vec::new(),
        pending_stubs: HashSet::new(),
    });
    Ok(())
}

/// The last part of `artifact` is loaded: a value-free record this load
/// left for a later part to complete refuses the import.
/// A receipt exists only for a matching active load that actually completed.
/// Repeating this call, including after a refused completion, grants none.
pub(super) fn finish_artifact_load(
    env: &mut Environment,
    artifact: &ArtifactKey,
) -> Result<Option<ArtifactCompletion>, ImportError> {
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    let Some(load) = ledger
        .load
        .as_ref()
        .filter(|load| &load.artifact == artifact)
    else {
        return Ok(None);
    };
    let module_system = load.module_system;
    end_load(ledger)?;
    let Some((key, records)) = ledger.records.as_ref().filter(|(key, _)| key == artifact) else {
        return Ok(None);
    };
    // Keep the rolling ASREAD map intact for repeated-artifact comparisons.
    // Foreign aliases are deduplicated out of this map and are NOT certified
    // by it; their original occurrences come from the authoritative raw part.
    let theorems = records
        .values()
        .filter_map(|record| match record {
            PartRecord::Constant { info, safety }
                if info.kind == clean_kernel::env::ConstantKind::Theorem && info.value.is_some()
                // Lean theorem records carry no declaration-safety field.
                && matches!(safety, None | Some(crate::DefinitionSafety::Safe)) =>
            {
                Some(info.clone())
            }
            _ => None,
        })
        .collect();
    Ok(Some(ArtifactCompletion {
        artifact: key.clone(),
        module_system,
        theorems,
    }))
}

/// Private completion evidence produced by the validated ledger transition.
#[derive(Debug)]
pub(super) struct ArtifactCompletion {
    artifact: ArtifactKey,
    module_system: bool,
    theorems: Vec<ConstantInfo>,
}

impl ArtifactCompletion {
    pub(super) fn artifact(&self) -> &ArtifactKey {
        &self.artifact
    }
    pub(super) fn module_system(&self) -> bool {
        self.module_system
    }
    pub(super) fn theorems(&self) -> &[ConstantInfo] {
        &self.theorems
    }
}

/// The load in progress for `artifact`, beginning one (from this part's own
/// `isModule`) when the load in progress is another artifact's.
fn load_for<'l>(
    ledger: &'l mut ArtifactLedger,
    artifact: &ArtifactKey,
    is_module: bool,
) -> Result<&'l mut ArtifactLoad, ImportError> {
    let load = match ledger.load.take_if(|load| &load.artifact == artifact) {
        Some(load) => load,
        None => {
            end_load(ledger)?;
            ArtifactLoad {
                artifact: artifact.clone(),
                module_system: is_module,
                entry_parts: Vec::new(),
                pending_stubs: HashSet::new(),
            }
        }
    };
    Ok(ledger.load.insert(load))
}

/// The records `artifact`'s parts declared so far (rule 4), starting a fresh
/// table when the table held is another artifact's.
fn records_for<'l>(
    ledger: &'l mut ArtifactLedger,
    artifact: &ArtifactKey,
) -> &'l mut HashMap<Name, PartRecord> {
    if ledger
        .records
        .as_ref()
        .is_some_and(|(key, _)| key != artifact)
    {
        ledger.records = None;
    }
    &mut ledger
        .records
        .get_or_insert_with(|| (artifact.clone(), HashMap::new()))
        .1
}

/// Rule 4 for the tables Clean reads, over the parts of one artifact in
/// level order (`.olean`, `.olean.server`, `.olean.private`; `None` for an
/// absent part), before anything of the artifact is registered.
///
/// * A module-system artifact's levels are cumulative — Lean's
///   `exportEntriesFn` states each level's entries again at every higher
///   level (`PersistentEnvExtension.exportEntriesFn`, `OLeanEntries`: "each
///   level should include all data of previous levels") — and a consumer
///   reads one level: a module the exported part, the language server the
///   server part, anything else the private part. So every entry a part
///   states, each higher part states identically.
/// * Any other artifact is read through its `.olean` alone, by every
///   consumer: a companion part states no entry the `.olean` does not.
///
/// Either way the part a consumer reads holds every entry any part states,
/// and no two consumers read one entry two ways.
pub(crate) fn check_artifact_entries(
    artifact: &ArtifactKey,
    module_system: bool,
    parts: &[Option<&[TypedExtension]>],
) -> Result<(), ImportError> {
    let sets: Vec<HashSet<EntryKey>> = parts
        .iter()
        .flatten()
        .map(|entries| read_entries(entries, module_system))
        .collect();
    entries_agree(artifact, module_system, &sets)
}

/// [`check_artifact_entries`] for part sets already read, in level order.
fn entries_agree(
    artifact: &ArtifactKey,
    module_system: bool,
    sets: &[HashSet<EntryKey>],
) -> Result<(), ImportError> {
    let Some(first) = sets.first() else {
        return Ok(());
    };
    for (i, later) in sets.iter().enumerate().skip(1) {
        if module_system {
            for earlier in &sets[..i] {
                if let Some(missing) = earlier.iter().find(|e| !later.contains(*e)) {
                    return Err(entry_disagreement(artifact, missing));
                }
            }
        } else if let Some(extra) = later.iter().find(|e| !first.contains(*e)) {
            return Err(entry_disagreement(artifact, extra));
        }
    }
    Ok(())
}

/// [`check_artifact_entries`] one part at a time, for a loader that is
/// handed an artifact's parts one call each (the public `ParsedModule`
/// path): the part is compared with the parts of the load in progress, and
/// begins a load of its own when that load is another artifact's.
pub(crate) fn check_part_entries(
    env: &mut Environment,
    artifact: &ArtifactKey,
    is_module: bool,
    entries: &[TypedExtension],
) -> Result<(), ImportError> {
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    let load = load_for(ledger, artifact, is_module)?;
    load.entry_parts
        .push(read_entries(entries, load.module_system));
    let result = entries_agree(artifact, load.module_system, &load.entry_parts);
    if result.is_err() {
        load.entry_parts.pop();
    }
    result
}

/// A part of `artifact` whose exact bytes were loaded before (so its
/// records were compared then) still states, in THIS load, a value-free
/// record for each name `stubs` gives, and a value for each name `valued`
/// gives: a stub of a name the environment holds with a value must be
/// completed by a later part of this load; a value completes it.
pub(crate) fn note_met_before_part(
    env: &mut Environment,
    artifact: &ArtifactKey,
    is_module: bool,
    stubs: impl IntoIterator<Item = Name>,
    valued: impl IntoIterator<Item = Name>,
) -> Result<(), ImportError> {
    let pending: Vec<Name> = stubs
        .into_iter()
        .filter(|n| env.get_const(n).is_some_and(|c| c.value.is_some()))
        .collect();
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    let load = load_for(ledger, artifact, is_module)?;
    load.pending_stubs.extend(pending);
    for name in valued {
        load.pending_stubs.remove(&name);
    }
    Ok(())
}

/// The artifact that declared the registered `name`, or `None` when it is
/// not an artifact's (the checker's native prelude, source elaboration).
pub(crate) fn declaring_artifact(env: &Environment, name: &Name) -> Option<ArtifactKey> {
    let label = match env.get_constant_origin(name)? {
        ConstantOrigin::Olean { module, .. } | ConstantOrigin::CleanPayload { module, .. } => {
            module.clone()
        }
        ConstantOrigin::Kernel { .. } => return None,
    };
    let bound = env
        .get_ext_state::<ArtifactLedger>(ledger_idx())
        .and_then(|ledger| ledger.parts.get(&label).cloned());
    Some(bound.unwrap_or(label))
}

/// Return the module that supplied a registered Lean-format declaration.
/// A split part maps to its base artifact through the import ledger.
#[must_use]
pub fn lean_declaration_artifact(env: &Environment, name: &Name) -> Option<String> {
    let ConstantOrigin::Olean { module, .. } = env.get_constant_origin(name)? else {
        return None;
    };
    env.get_ext_state::<ArtifactLedger>(ledger_idx())?
        .parts
        .get(module)?
        .clone()
}

/// The module of a different artifact that already declared `name`.
pub(crate) fn declared_by_other_artifact(
    env: &Environment,
    name: &Name,
    artifact: &ArtifactKey,
) -> Option<String> {
    match declaring_artifact(env, name) {
        Some(first) if &first != artifact => Some(display(&first)),
        _ => None,
    }
}

/// Record that a part of `artifact` whose bytes (with the parts it is
/// read against) hash to `digest` is being loaded, and whether exactly
/// these bytes were loaded for this artifact before. Such a part states
/// nothing its first load did not, and what that load stated was compared
/// then (rule 4); a part with bytes not met before is compared declaration
/// by declaration.
pub(crate) fn part_met_before(
    env: &mut Environment,
    artifact: &ArtifactKey,
    digest: [u8; 32],
) -> bool {
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    !ledger
        .part_digests
        .entry(artifact.clone())
        .or_default()
        .insert(digest)
}

/// Whether the registered `name` was declared by an earlier part of
/// `artifact` itself (a part's own duplicates are refused before this).
pub(crate) fn declared_by_this_artifact(
    env: &Environment,
    name: &Name,
    artifact: &ArtifactKey,
) -> bool {
    registered(env, name) && declaring_artifact(env, name).as_ref() == Some(artifact)
}

/// Remember what one part of `artifact` declared (rule 4). A record for a
/// name already remembered replaces it: that is a stub the part completed.
pub(crate) fn remember_part_records(
    env: &mut Environment,
    artifact: &ArtifactKey,
    records: impl IntoIterator<Item = PartRecord>,
) {
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    let table = records_for(ledger, artifact);
    for record in records {
        table.insert(record.name().clone(), record);
    }
}

/// Rule 4: `incoming` names a declaration an earlier part of `artifact`
/// holds. It must be the record an earlier part of this load read (`None`:
/// the record did not convert, so it cannot be shown to agree), and the
/// record is then what this load has said of the name.
///
/// A name no earlier part of this load stated — the artifact was met in an
/// earlier load, before another one — is compared with the environment's
/// copy on the fields registration never changes afterwards, and one rule
/// holds for both: a value-free record of a name that has a value stands
/// for that value only as a stub a later part of the same load completes.
/// Within one load a stub after its definition is refused at once (the
/// definition was stated before it); a stub of the environment's
/// definition is left to a later part of this load, which must state the
/// environment's value, and [`finish_artifact_load`] (or the next load)
/// refuses the import when none did.
pub(crate) fn check_same_artifact_record(
    env: &mut Environment,
    artifact: &ArtifactKey,
    name: &Name,
    incoming: Option<&PartRecord>,
) -> Result<(), ImportError> {
    let disagree = || ImportError::PartsDisagree {
        name: name.to_string(),
        module: display(artifact),
    };
    let incoming = incoming.ok_or_else(disagree)?;
    let remembered = env
        .get_ext_state::<ArtifactLedger>(ledger_idx())
        .and_then(|ledger| match &ledger.records {
            Some((key, table)) if key == artifact => table.get(name).cloned(),
            _ => None,
        });
    let has_value = |record: &PartRecord| matches!(record, PartRecord::Constant { info, .. } if info.value.is_some());
    let is_stub = |record: &PartRecord| matches!(record, PartRecord::Constant { info, .. } if info.value.is_none());
    // Only a module-system artifact's later part completes an earlier part's
    // stub (R131): every importer reads a non-module artifact's `.olean` alone.
    let module_system = env
        .get_ext_state::<ArtifactLedger>(ledger_idx())
        .and_then(|ledger| ledger.load.as_ref())
        .is_some_and(|load| &load.artifact == artifact && load.module_system);
    let pending = match remembered {
        // This load's own stub, completed by this part (an artifact met
        // again: the environment's copy already has the value, so the
        // completion is not an upgrade): it must state the environment's
        // declaration.
        Some(earlier) if is_stub(&earlier) && has_value(incoming) => {
            if !module_system
                || !stub_completed_by(&earlier, incoming)
                || !agrees_with_environment(env, incoming)
            {
                return Err(disagree());
            }
            Some(false)
        }
        Some(earlier) => {
            if !earlier.same_as(incoming) {
                return Err(disagree());
            }
            None
        }
        None => {
            if !agrees_with_environment(env, incoming) {
                return Err(disagree());
            }
            let env_has_value = env.get_const(name).is_some_and(|c| c.value.is_some());
            if is_stub(incoming) && env_has_value {
                Some(true)
            } else if has_value(incoming) {
                Some(false)
            } else {
                None
            }
        }
    };
    let ledger = env.get_ext_state_mut::<ArtifactLedger>(ledger_idx());
    if let Some(pending) = pending {
        let is_module = ledger.load.as_ref().is_some_and(|l| l.module_system);
        let load = load_for(ledger, artifact, is_module)?;
        if pending {
            load.pending_stubs.insert(name.clone());
        } else {
            load.pending_stubs.remove(name);
        }
    }
    records_for(ledger, artifact).insert(name.clone(), incoming.clone());
    Ok(())
}

/// Rule 4 for a stub an earlier part of this load stated and `completion`
/// completes (the upgrade path): the completion must state the stub's
/// declaration — its universe parameters and type as read. A stub that is
/// not this artifact's (a value-free constant of the checker's own prelude)
/// is left to the kernel's type anchor at the upgrade.
pub(crate) fn check_stub_completion(
    env: &Environment,
    artifact: &ArtifactKey,
    completion: &ConstantInfo,
) -> Result<(), ImportError> {
    let remembered = env
        .get_ext_state::<ArtifactLedger>(ledger_idx())
        .and_then(|ledger| match &ledger.records {
            Some((key, table)) if key == artifact => table.get(&completion.name).cloned(),
            _ => None,
        });
    let Some(stub) = remembered else {
        return Ok(());
    };
    // The completion's value may already be elided by the import policy; the
    // declaration it states is its name, universe parameters and type.
    let states_the_stub = matches!(&stub, PartRecord::Constant { info: s, .. }
        if s.value.is_none()
            && s.name == completion.name
            && s.level_params == completion.level_params
            && s.type_ == completion.type_);
    if states_the_stub {
        Ok(())
    } else {
        Err(ImportError::PartsDisagree {
            name: completion.name.to_string(),
            module: display(artifact),
        })
    }
}

/// Rule 4 between two parts of one artifact in level order: `later` states what
/// `earlier` states, or completes `earlier`'s value-free stub. R113's artifact
/// reader (`artifact::check_artifact_parts`) decides value agreement with this.
pub(crate) fn records_agree(earlier: &PartRecord, later: &PartRecord) -> bool {
    earlier.same_as(later) || stub_completed_by(earlier, later)
}

/// Rule 4 for a non-module artifact's companion (R131): it restates the record
/// exactly. Every importer reads such an artifact's `.olean` alone, so a
/// companion that completes the `.olean`'s stub states another declaration.
pub(crate) fn records_same(earlier: &PartRecord, later: &PartRecord) -> bool {
    earlier.same_as(later)
}

/// The producer's axiom stub preserves the completed declaration's safety.
/// Lean 4.30 encoded partial definitions as Safe stubs; 4.35 uses Unsafe.
/// Neither encoding permits an Unsafe stub to become a Safe declaration, or
/// a Safe stub to become an Unsafe definition/opaque. Clean payload records
/// carry no separate safety field: preserve their existing None/None equality
/// without interpreting unknown metadata as safe or as a replay exclusion.
pub(super) fn stub_safety_agrees(
    stub: Option<crate::DefinitionSafety>,
    full_kind: &crate::ConstantKind,
    full: Option<crate::DefinitionSafety>,
) -> bool {
    use crate::{ConstantKind, DefinitionSafety};
    if stub.is_none() && full.is_none() {
        return true;
    }
    match (full_kind, full) {
        (ConstantKind::Theorem, None) => stub == Some(DefinitionSafety::Safe),
        (ConstantKind::Definition, Some(DefinitionSafety::Partial)) => {
            matches!(
                stub,
                Some(DefinitionSafety::Safe | DefinitionSafety::Unsafe)
            )
        }
        (_, Some(DefinitionSafety::Safe | DefinitionSafety::Unsafe)) => stub == full,
        _ => false,
    }
}

/// `complete` states the declaration `stub` stubs: the same name, universe
/// parameters and type, with a value.
fn stub_completed_by(stub: &PartRecord, complete: &PartRecord) -> bool {
    match (stub, complete) {
        (
            PartRecord::Constant {
                info: s,
                safety: ss,
            },
            PartRecord::Constant {
                info: c,
                safety: cs,
            },
        ) => {
            let kind = match c.kind {
                clean_kernel::env::ConstantKind::Theorem => crate::ConstantKind::Theorem,
                clean_kernel::env::ConstantKind::Opaque => crate::ConstantKind::Opaque,
                clean_kernel::env::ConstantKind::Axiom => crate::ConstantKind::Axiom,
                clean_kernel::env::ConstantKind::Definition => crate::ConstantKind::Definition,
            };
            stub_safety_agrees(*ss, &kind, *cs)
                && s.name == c.name
                && s.level_params == c.level_params
                && s.type_ == c.type_
                && s.value.is_none()
                && c.value.is_some()
        }
        _ => false,
    }
}

/// The fields of `incoming` that registration never rewrites, against the
/// environment's copy — for an artifact met again after another one was
/// loaded, whose parts' records are no longer remembered. Registration drops
/// the value of an elided proof, completes a stub from a later part, and
/// derives `is_large_elim` and each recursor rule's recursive fields; so a
/// constant's value (and its kind, which a completed stub changes) is
/// compared where both carry one, and those derived fields are not compared.
/// A record without a value beside a registered value is the stub a later
/// part completed: it must still state the same type.
pub(crate) fn agrees_with_environment(env: &Environment, incoming: &PartRecord) -> bool {
    match incoming {
        PartRecord::Constant { info, .. } => env.get_const(&info.name).is_some_and(|c| {
            let family = env.get_inductive(&info.name).is_some()
                || env.get_constructor(&info.name).is_some()
                || env.get_recursor(&info.name).is_some();
            let same_value = match (&c.value, &info.value) {
                (Some(registered), Some(read)) => c.kind == info.kind && registered == read,
                _ => true,
            };
            !family && c.level_params == info.level_params && c.type_ == info.type_ && same_value
        }),
        PartRecord::Inductive(v, s) => env.get_inductive(&v.name).is_some_and(|c| {
            let mut read = v.clone();
            read.is_large_elim = c.is_large_elim;
            PartRecord::Inductive(c.clone(), *s).same_as(&PartRecord::Inductive(read, *s))
        }),
        PartRecord::Constructor(v, s) => env.get_constructor(&v.name).is_some_and(|c| {
            PartRecord::Constructor(c.clone(), *s).same_as(&PartRecord::Constructor(v.clone(), *s))
        }),
        PartRecord::Recursor(v, all, nested, s) => env.get_recursor(&v.name).is_some_and(|c| {
            let mut read = v.clone();
            for (rule, registered) in read.rules.iter_mut().zip(&c.rules) {
                rule.recursive_fields
                    .clone_from(&registered.recursive_fields);
            }
            PartRecord::Recursor(c.clone(), all.clone(), *nested, *s)
                .same_as(&PartRecord::Recursor(read, all.clone(), *nested, *s))
        }),
    }
}

/// Missing declarations in the resident family's types, walking each DAG node
/// once. Values and recursor rules are not dependency guesses for this test.
pub(crate) fn missing_family_type_dependencies(env: &Environment, family: &Name) -> Vec<Name> {
    let mut seen = HashSet::new();
    let mut names = std::collections::HashSet::new();
    if let Some(ind) = env.get_inductive(family) {
        for member in &ind.all_names {
            if let Some(ind) = env.get_inductive(member) {
                graph::walk_constants(&ind.type_, &mut seen, &mut names);
                for name in &ind.constructor_names {
                    if let Some(ctor) = env.get_constructor(name) {
                        graph::walk_constants(&ctor.type_, &mut seen, &mut names);
                    }
                }
            }
        }
    }
    let mut missing: Vec<_> = names
        .into_iter()
        .filter(|name| !registered(env, name))
        .collect();
    missing.sort();
    missing
}

fn registered(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

/// Rule 1 for the Lean-built records of one part, checked before anything
/// of the part is registered. `records` are `(index, name)` of the records
/// the loader would register (compiler artifacts it skips, and names the
/// module's own Clean payload declares, are left out by the caller). A name
/// twice in the part is refused here. A name a different artifact already
/// declared is returned with that artifact, for the caller to decide on the
/// converted record: Lean's import allows only a second proof, or axiom
/// stub, of the very statement (`dite.congr_simp` is realized in two `Init`
/// modules under v4.30) and refuses every other duplicate.
pub(crate) fn check_lean_records(
    env: &Environment,
    records: impl Iterator<Item = (usize, Name)>,
    artifact: &ArtifactKey,
) -> Result<Vec<(usize, String)>, ImportError> {
    let mut seen = HashSet::new();
    let mut others = Vec::new();
    for (index, name) in records {
        if name.is_anon() {
            continue;
        }
        if !seen.insert(name.clone()) {
            return Err(ImportError::DuplicateDeclaration {
                name: name.to_string(),
                what: "declaration",
            });
        }
        if registered(env, &name) {
            if let Some(first) = declared_by_other_artifact(env, &name, artifact) {
                others.push((index, first));
            }
        }
    }
    Ok(others)
}

/// Rules 2 and 3 for the names one part of `artifact` just added (`added`,
/// plus `upgraded`: stubs whose value the part supplied). Run after the
/// part's safety marks are applied, so an `unsafe` declaration — which Lean
/// lets refer to itself — is known as such.
///
/// With `refuse_cycles` false, rule 3 is left to the caller's replay of this
/// artifact (`OleanImportPolicy::with_module_replay_refusals`): a
/// self-dependent declaration registers as stored, while rule 2 and the
/// ledger's bookkeeping run as always.
pub(crate) fn check_part_references(
    env: &mut Environment,
    artifact: &ArtifactKey,
    added: &[Name],
    upgraded: &[Name],
    refuse_cycles: bool,
) -> Result<(), ImportError> {
    let idx = ledger_idx();
    let (earlier_parts, unresolved_hits) = {
        let ledger = env.get_ext_state_mut::<ArtifactLedger>(idx);
        let earlier = match &ledger.current {
            Some((key, names)) if key == artifact => names.clone(),
            _ => Vec::new(),
        };
        let mut hits = Vec::new();
        for name in added.iter().chain(upgraded) {
            if let Some(referrer) = ledger.unresolved.remove(name) {
                hits.push((name.clone(), referrer));
            }
        }
        (earlier, hits)
    };
    let mut spans_parts = false;
    for (name, referrer) in unresolved_hits {
        if &referrer != artifact {
            return Err(ImportError::ForwardReference {
                name: name.to_string(),
                referrer: display(&referrer),
                declared_by: display(artifact),
            });
        }
        spans_parts = true;
    }

    // The nodes: this part's names, and the earlier parts' of the same
    // artifact when one of them referred forward into this part. Earlier
    // artifacts cannot close a cycle: nothing they refer to is declared later
    // (rule 2).
    let mut nodes: Vec<Name> = added.iter().chain(upgraded).cloned().collect();
    if spans_parts {
        nodes.extend(earlier_parts);
    }
    let mut seen = HashSet::new();
    nodes.retain(|n| seen.insert(n.clone()));
    let index: HashMap<Name, usize> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), i))
        .collect();
    // An edge to itself is kept: a declaration that mentions itself is the
    // one-member cycle.
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
    let mut unresolved = Vec::new();
    let mut refs = std::collections::HashSet::new();
    let mut shared = HashSet::new();
    for (i, name) in nodes.iter().enumerate() {
        references(env, name, &mut shared, &mut refs);
        for r in &refs {
            if let Some(&j) = index.get(r) {
                edges[i].push(j);
            } else if !registered(env, r) {
                unresolved.push(r.clone());
            }
        }
    }
    if let Some(cycle) = first_cycle(env, &nodes, &edges).filter(|_| refuse_cycles) {
        return Err(ImportError::DefinitionalCycle {
            names: cycle.iter().map(ToString::to_string).collect(),
        });
    }

    let ledger = env.get_ext_state_mut::<ArtifactLedger>(idx);
    for r in unresolved {
        ledger
            .unresolved
            .entry(r)
            .or_insert_with(|| artifact.clone());
    }
    match &mut ledger.current {
        Some((key, names)) if key == artifact => names.extend(added.iter().cloned()),
        current => *current = Some((artifact.clone(), added.to_vec())),
    }
    Ok(())
}

#[cfg(test)]
#[path = "artifact_ledger_tests.rs"]
mod tests;
