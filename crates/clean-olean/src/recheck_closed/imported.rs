// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The gate every consumer that prints a kernel verdict runs over a
//! declaration's cone before it credits the declaration.
//!
//! # What was wrong
//!
//! An imported module's declarations enter the importing environment through
//! the structural tier (`extend_constants_structural` and the
//! `extend_*_structural` family legs, `import/load_register.rs`): closed,
//! metavariable-free, level-scoped — and NEVER type-checked. The origin ledger
//! records that (`CleanPayloadUnpinned` / `OleanUnpinned`, both
//! `needs_recheck`), but `clean check` and `clean lake build` never asked it.
//! They kernel-checked the citing declaration against the imported TYPES and
//! credited it. Measured on `7369eb6fd` (report
//! `reports/2026-09-24-module-trust.md`): after rewriting a built module's
//! artifact, `theorem k1_false : (0 : Nat) = 1` checked and built, exit 0, by
//! citing a lemma whose stated type had been changed, whose proof had been
//! replaced by `sorry`, which had become an axiom, whose proof's own
//! dependency had been removed, or whose family's recursor rules had been
//! swapped.
//!
//! # What this does
//!
//! [`ImportedConeGate::new`] snapshots the consumer's kernel BASE — the
//! environment it built before loading any import. [`ImportedConeGate::check`]
//! walks a declaration's whole cone (types, values, family heads,
//! constructors; the same planner as [`super::recheck_closed`]) and:
//!
//! * takes as given only what the base holds and what earlier checks of this
//!   gate re-admitted — each compared for identity, never believed by name;
//! * takes as given, for the fast path only, a declaration this session
//!   admitted through the kernel's own full check (`FullKernelCheck`, no
//!   import origin) — but the moment the cone contains ANY other declaration,
//!   everything outside the base is replayed, session declarations included,
//!   because a session declaration was checked against the imported types;
//! * re-admits every other member through `add_decl` / `add_inductive_core`
//!   over the base, in dependency order, with the same extension-binding gate
//!   and the same family regeneration as the closed replay (an imported
//!   name the base's native-reducer table also evaluates is admitted like any
//!   other: the kernel fires a reducer only over a canonical definition of its
//!   head, `clean-kernel/src/env/native_fold_authority.rs`);
//! * treats a name whose value-free base declaration the importer upgraded
//!   to an imported definition (`upgrade_axiom_stubs_checked`) as NOT given:
//!   a session declaration citing it was kernel-checked against the imported
//!   value, which the base never had, so the cone is replayed and the replay
//!   keeps the base's value-free declaration;
//! * lists every trust marker (`sorry`, `sorryAx`, `trustedArith`,
//!   `trustedAy`) the cone reaches, and every axiom that is neither the
//!   base's own declaration (compared, not matched by name — a name on the
//!   foundational list is no evidence) nor declared by this session.
//!
//! A cone that re-admits cleanly, reaches no trust marker and rests on no
//! axiom from outside the base and this session is the only one [`ImportedConeVerdict::passed`]
//! accepts. The gate keeps what it re-admitted, so each imported declaration is
//! replayed once per consumer run, not once per citation.

use clean_kernel::env::{
    is_trust_marker, ConstantInfo, ConstantKind, ConstantOrigin, DeclarationVerification,
    Environment,
};
use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::time::Instant;

use super::drive::{replay_in_order, Given, ReplayPlan};
use super::{
    extension_key_fingerprints, ClosedRecheckOptions, ClosedRecheckRefusal, ConePlanner,
    FamilyIndex, RecheckLevel, ReplayStats, Unit, UnitId,
};

/// The replay environment a consumer's citations are re-admitted into.
#[derive(Debug, Clone)]
pub struct ImportedConeGate {
    /// Base plus everything this gate has re-admitted so far.
    replay: Environment,
    /// Names the base held when the gate was created.
    base_names: HashSet<Name>,
    /// Names an earlier check of this gate re-admitted. The replay holds the
    /// KERNEL's regenerated form of a family member, which is compared with
    /// the imported one (up to definitional equality) at admission — so a
    /// later check must recognise the name as admitted, not re-compare bytes.
    admitted: HashSet<Name>,
    options: ClosedRecheckOptions,
    /// Original records whose complete cone passed ReferenceKernel admission.
    /// Regenerated recursors can differ syntactically; only these exact source
    /// records may use that successful admission as their base evidence.
    reference_source: Option<(Environment, HashSet<Name>)>,
}

/// What one [`ImportedConeGate::check`] measured.
#[derive(Debug, Clone, Serialize)]
pub struct ImportedConeVerdict {
    /// Always [`RecheckLevel::ImportedOverBase`].
    pub level: RecheckLevel,
    /// The roots asked about.
    pub roots: Vec<String>,
    /// Distinct names in the cone.
    pub cone_constants: usize,
    /// Cone members that were neither in the base nor admitted by this
    /// session's own full check (imported declarations, as a rule).
    pub untrusted_in_cone: Vec<String>,
    /// Units skipped because the replay environment already held them.
    pub given_units: usize,
    /// Ordinary constants re-admitted by this call.
    pub constants_admitted: usize,
    /// Inductive families re-admitted by this call.
    pub families_replayed: usize,
    /// Everything the replay refused.
    pub refusals: Vec<ClosedRecheckRefusal>,
    /// Trust markers the cone reaches, each with the cone members that cite
    /// it directly (`marker <- a, b`).
    pub trust_markers: Vec<String>,
    /// Axioms the cone reaches that are neither the base's own declaration
    /// nor declared by this session — whatever their names.
    pub imported_axioms: Vec<String>,
    /// Wall-clock milliseconds.
    pub elapsed_ms: u128,
}

/// Trust markers a consumer's `--allow-sorry` may waive; the solver-bridge
/// markers are never waived.
const SORRY_MARKERS: &[&str] = &["sorry", "sorryAx"];

impl ImportedConeVerdict {
    /// The cone re-admitted cleanly, reaches no trust marker and rests on no
    /// axiom from outside the base and this session. With `allow_sorry` (a consumer's
    /// `--allow-sorry`) a `sorry` / `sorryAx` marker is waived; the
    /// solver-bridge markers and imported axioms never are.
    #[must_use]
    pub fn passed(&self, allow_sorry: bool) -> bool {
        self.refusals.is_empty()
            && self.imported_axioms.is_empty()
            && self.trust_markers.iter().all(|m| {
                allow_sorry
                    && SORRY_MARKERS
                        .iter()
                        .any(|s| m.split(' ').next() == Some(*s))
            })
    }

    /// One line naming why the cone was not accepted (empty when it was).
    #[must_use]
    pub fn refusal_summary(&self, allow_sorry: bool) -> String {
        let mut parts = Vec::new();
        if !self.refusals.is_empty() {
            let shown: Vec<String> = self
                .refusals
                .iter()
                .take(3)
                .map(|r| format!("{}: {}", r.subject(), refusal_reason(r)))
                .collect();
            let more = self.refusals.len().saturating_sub(shown.len());
            parts.push(format!(
                "{} imported declaration(s) failed the kernel re-check ({}{})",
                self.refusals.len(),
                shown.join("; "),
                if more > 0 {
                    format!("; +{more} more")
                } else {
                    String::new()
                }
            ));
        }
        let markers: Vec<&String> = self
            .trust_markers
            .iter()
            .filter(|m| {
                !(allow_sorry
                    && SORRY_MARKERS
                        .iter()
                        .any(|s| m.split(' ').next() == Some(*s)))
            })
            .collect();
        if !markers.is_empty() {
            parts.push(format!(
                "the cited closure reaches {}",
                markers
                    .iter()
                    .map(|m| m.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        if !self.imported_axioms.is_empty() {
            parts.push(format!(
                "the cited closure rests on imported axiom(s) {}",
                self.imported_axioms.join(", ")
            ));
        }
        parts.join("; ")
    }
}

fn refusal_reason(r: &ClosedRecheckRefusal) -> String {
    match r {
        ClosedRecheckRefusal::AbsentFromEnvironment { .. } => "absent".to_string(),
        ClosedRecheckRefusal::DependencyCycle { names } => format!("cycle {}", names.join(" -> ")),
        ClosedRecheckRefusal::DeclarationRefused { error, .. } => first_line(error),
        ClosedRecheckRefusal::FamilyRefused { error, .. } => first_line(error),
        ClosedRecheckRefusal::FamilyIncomplete { detail, .. }
        | ClosedRecheckRefusal::MemberMismatch { detail, .. }
        | ClosedRecheckRefusal::BaseConflict { detail, .. }
        | ClosedRecheckRefusal::QuotientPrecondition { detail, .. } => first_line(detail),
        ClosedRecheckRefusal::RecursorRuleMismatch {
            constructor,
            detail,
            ..
        } => format!("rule for {constructor}: {}", first_line(detail)),
        ClosedRecheckRefusal::MemberNotRegenerated { family, .. } => {
            format!("not regenerated by family {family}")
        }
        ClosedRecheckRefusal::DependencyRefused { blocked_by, .. } => {
            format!("depends on refused {blocked_by}")
        }
        ClosedRecheckRefusal::ExtensionBindingMismatch { hook, .. } => {
            format!("by-name kernel reduction ({hook}) not bound to this declaration")
        }
        ClosedRecheckRefusal::OutsideTrustedFragment { marker, .. } => (*marker).to_string(),
    }
}

fn first_line(s: &str) -> String {
    let line = s.lines().next().unwrap_or_default();
    if line.chars().count() > 160 {
        let cut: String = line.chars().take(160).collect();
        format!("{cut}…")
    } else {
        line.to_string()
    }
}

impl ImportedConeGate {
    /// Snapshot `base` — the consumer's environment BEFORE it loaded any
    /// import. Everything in it is taken as given by every later check, so a
    /// caller that snapshots after an import has trusted that import.
    #[must_use]
    pub fn new(base: &Environment) -> Self {
        let mut replay = base.clone();
        replay.set_option(
            "maxHeartbeats".to_string(),
            Some(clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT.to_string()),
        );
        let base_names = base.constants().map(|c| c.name.clone()).collect();
        Self {
            replay,
            base_names,
            admitted: HashSet::new(),
            options: ClosedRecheckOptions::default(),
            reference_source: None,
        }
    }

    /// Build a citation base by fully re-admitting the selected source cone
    /// through ReferenceKernel. Keep the checked source records for exact
    /// comparisons: regenerated recursors need not have identical syntax.
    ///
    /// # Errors
    /// Returns the reference replay's refusal; a partial replay supplies no base.
    pub fn from_reference_cone(
        source: &Environment,
        roots: &BTreeSet<Name>,
    ) -> Result<Self, String> {
        let checked = super::reference_base::reference_base_closed(
            source,
            roots,
            &ClosedRecheckOptions::default(),
        )
        .map_err(|error| error.to_string())?;
        let names = checked.admitted.iter().cloned().collect();
        let kernel = checked
            .into_kernel()
            .map_err(|report| report.verdict_sentence())?;
        let mut gate = Self::new(kernel.environment());
        gate.reference_source = Some((source.clone(), names));
        Ok(gate)
    }

    pub(super) fn admitted_names(&self) -> impl Iterator<Item = &Name> {
        self.admitted.iter()
    }

    /// Source-value evidence for a frozen source checked by this fresh gate.
    /// A type-only base-stub upgrade supports logical replay, not its source
    /// value. Given records need the same logical declaration and family;
    /// freshly admitted family records retain their actual replay evidence.
    /// The consuming witness still requires actual kernel verification.
    pub(super) fn has_source_record_evidence(&self, source: &Environment, name: &Name) -> bool {
        self.admitted.contains(name) || same_as_replayed(source, &self.replay, name)
    }

    /// Read-only access to the declarations actually admitted into this gate.
    #[must_use]
    pub fn environment(&self) -> &Environment {
        &self.replay
    }

    fn matches_reference_source(&self, env: &Environment, name: &Name) -> bool {
        self.reference_source
            .as_ref()
            .is_some_and(|(source, names)| {
                names.contains(name) && same_reference_record(env, source, name)
            })
    }

    /// Whether `env` holds the base declaration or the exact source record
    /// whose successful reference admission established that base.
    fn same_as_base(&self, env: &Environment, name: &Name) -> bool {
        if self
            .reference_source
            .as_ref()
            .is_some_and(|(_, names)| names.contains(name))
        {
            return self.matches_reference_source(env, name);
        }
        self.base_names.contains(name) && same_as_replayed(env, &self.replay, name)
    }

    /// Re-admit the cone of `roots` over the base; see the module docs.
    pub fn check(&mut self, env: &Environment, roots: &BTreeSet<Name>) -> ImportedConeVerdict {
        let started = Instant::now();
        let index = FamilyIndex::build(env);
        let mut refusals = Vec::new();
        let mut planner = ConePlanner::new(env, &index);
        for root in roots {
            planner.enqueue(root);
        }
        planner.run(self.options.max_closure, &mut refusals);
        let ConePlanner {
            units,
            cone,
            order,
            cycles,
            absent,
            ..
        } = planner;
        for cycle in cycles {
            refusals.push(ClosedRecheckRefusal::DependencyCycle { names: cycle });
        }

        let untrusted: Vec<String> = cone
            .iter()
            .filter(|name| {
                if self
                    .reference_source
                    .as_ref()
                    .is_some_and(|(_, names)| names.contains(*name))
                {
                    return !self.matches_reference_source(env, name);
                }
                !session_checked(env, name)
                    && !self.admitted.contains(*name)
                    && !same_as_replayed(env, &self.replay, name)
            })
            .map(ToString::to_string)
            .collect();
        let (trust_markers, imported_axioms) = self.scan_axioms(env, &cone);

        let mut stats = ReplayStats::default();
        let mut given_units = 0usize;
        if !untrusted.is_empty() || !refusals.is_empty() {
            let key_fingerprints = extension_key_fingerprints(env, &cone);
            let mut unavailable: BTreeMap<Name, String> = absent
                .into_iter()
                .map(|name| {
                    let label = name.to_string();
                    (name, label)
                })
                .collect();
            let plan = ReplayPlan {
                env,
                index: &index,
                units: &units,
                order: &order,
                key_fingerprints: &key_fingerprints,
                options: &self.options,
                clean_families: true,
            };
            let admitted = &self.admitted;
            let reference_source = &self.reference_source;
            let driven = replay_in_order(
                &plan,
                &mut self.replay,
                &mut unavailable,
                &mut stats,
                &mut refusals,
                &|replay, id, unit| {
                    if let Some((source, names)) = reference_source {
                        if unit.members.iter().any(|name| names.contains(name)) {
                            return if unit.members.iter().all(|name| {
                                names.contains(name) && same_reference_record(env, source, name)
                            }) {
                                Given::Yes
                            } else {
                                Given::Conflict(
                                    "reference-admitted source records changed".to_owned(),
                                )
                            };
                        }
                    }
                    if unit.members.iter().all(|m| admitted.contains(m)) {
                        return Given::Yes;
                    }
                    given(env, replay, id, unit)
                },
            );
            given_units = driven.given_units;
            // Only what was admitted with nothing refused in its own unit: a
            // family that was added and then failed its member comparison is
            // in `unavailable`, not here.
            self.admitted.extend(
                stats
                    .admitted_names
                    .iter()
                    .filter(|n| !unavailable.contains_key(*n))
                    .cloned(),
            );
        }

        ImportedConeVerdict {
            level: RecheckLevel::ImportedOverBase,
            roots: roots.iter().map(ToString::to_string).collect(),
            cone_constants: cone.len(),
            untrusted_in_cone: untrusted,
            given_units,
            constants_admitted: stats.constants_admitted,
            families_replayed: stats.families_replayed,
            refusals,
            trust_markers,
            imported_axioms,
            elapsed_ms: started.elapsed().as_millis(),
        }
    }

    /// Trust markers the cone reaches (with their direct citers) and the
    /// axioms in it that are not the base's own declaration and that this
    /// session did not declare.
    fn scan_axioms(&self, env: &Environment, cone: &BTreeSet<Name>) -> (Vec<String>, Vec<String>) {
        let mut markers: BTreeMap<Name, BTreeSet<String>> = BTreeMap::new();
        let mut axioms = Vec::new();
        for name in cone {
            let Some(info) = env.get_const(name) else {
                continue;
            };
            if info.kind == ConstantKind::Axiom {
                if is_trust_marker(name) {
                    markers.entry(name.clone()).or_default();
                } else if !session_checked(env, name) && !self.same_as_base(env, name) {
                    // An axiom is taken as given only when the consumer's
                    // base holds this very declaration. A NAME on the
                    // foundational list is no evidence: an imported
                    // `axiom proofIrrel : False` carries the name and none of
                    // the content (module-trust verification, 2026-09-25).
                    axioms.push(name.to_string());
                }
            }
            let mut refs = HashSet::new();
            // DAG walks: a term with shared subterms (a match's copied
            // right-hand side, G15/G76) is visited once per distinct node,
            // not once per path.
            info.type_
                .used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
            if let Some(value) = &info.value {
                value.used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
            }
            for r in refs {
                if is_trust_marker(&r) {
                    markers.entry(r).or_default().insert(name.to_string());
                }
            }
        }
        let markers = markers
            .into_iter()
            .map(|(marker, citers)| {
                if citers.is_empty() {
                    marker.to_string()
                } else {
                    format!(
                        "{marker} (cited by {})",
                        citers.into_iter().collect::<Vec<_>>().join(", ")
                    )
                }
            })
            .collect();
        (markers, axioms)
    }
}

/// A declaration this session admitted through the kernel's own full check,
/// with no import origin.
fn session_checked(env: &Environment, name: &Name) -> bool {
    env.declaration_verification(name) == Some(DeclarationVerification::FullKernelCheck)
        && env
            .get_constant_origin(name)
            .is_none_or(|origin| matches!(origin, ConstantOrigin::Kernel { .. }))
}

/// A reference receipt covers the complete source metadata, not just the
/// fields needed by the ordinary base's historical compatibility comparison.
fn same_reference_record(env: &Environment, source: &Environment, name: &Name) -> bool {
    match (env.get_const(name), source.get_const(name)) {
        (Some(a), Some(b)) => {
            same_info(a, b)
                && env.get_inductive(name) == source.get_inductive(name)
                && env.get_constructor(name) == source.get_constructor(name)
                && env.get_recursor(name) == source.get_recursor(name)
        }
        _ => false,
    }
}

/// `name` is in the replay environment as the same declaration `env` holds.
fn same_as_replayed(env: &Environment, replay: &Environment, name: &Name) -> bool {
    match (env.get_const(name), replay.get_const(name)) {
        (Some(ours), Some(theirs)) => {
            same_info(ours, theirs) && same_family_member(env, replay, name)
        }
        _ => false,
    }
}

/// Same declaration for the kernel's purposes. Reducibility hints are not
/// compared: they steer the order of unfolding, never what is derivable, and
/// the importer re-applies Lean's hints to declarations it already holds.
fn same_info(a: &ConstantInfo, b: &ConstantInfo) -> bool {
    a.level_params == b.level_params && a.type_ == b.type_ && a.value == b.value && a.kind == b.kind
}

/// The importer's axiom-stub upgrade (`upgrade_axiom_stubs_checked`) replaces
/// a value-free declaration the base holds with an imported declaration of a
/// definitionally equal type. The replay keeps the BASE's value-free
/// declaration: whatever the replay admits against it is checked against the
/// type the base already trusted, and nothing can unfold a value the replay
/// does not hold (a dependent that needed to is refused by `add_decl`). So,
/// DURING A REPLAY, the upgraded unit is given iff the replay's own copy is
/// value-free and the two types agree in the replay environment.
///
/// It is NOT a reason to skip the replay: the consumer's own declarations
/// were checked against the upgraded VALUE, so an upgraded name in a cone
/// counts as untrusted and forces every session declaration in it through
/// `add_decl` over the base. Counting it as given let
/// `def Fact (p : Prop) : Prop := p → p` in an imported module make the
/// base's `Fact.out` prove `False` (module-trust verification, 2026-09-25).
fn base_stub_upgrade(env: &Environment, replay: &Environment, name: &Name) -> bool {
    let (Some(ours), Some(theirs)) = (env.get_const(name), replay.get_const(name)) else {
        return false;
    };
    if theirs.value.is_some() || ours.level_params.len() != theirs.level_params.len() {
        return false;
    }
    if env.get_recursor(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
    {
        return false;
    }
    let ours_type = if ours.level_params == theirs.level_params {
        ours.type_.clone()
    } else {
        let renaming: Vec<clean_kernel::Level> = theirs
            .level_params
            .iter()
            .map(|n| clean_kernel::Level::param(n.clone()))
            .collect();
        ours.type_
            .instantiate_level_params_direct(&ours.level_params, &renaming)
    };
    ours_type == theirs.type_
        || clean_kernel::tc::TypeChecker::new(replay).is_def_eq(&ours_type, &theirs.type_)
}

/// The family metadata the kernel reduces with — a recursor's rules and
/// shape, an inductive's constructor list — agrees too.
fn same_family_member(env: &Environment, replay: &Environment, name: &Name) -> bool {
    match (env.get_recursor(name), replay.get_recursor(name)) {
        (Some(a), Some(b)) => {
            return a.num_params == b.num_params
                && a.num_indices == b.num_indices
                && a.num_motives == b.num_motives
                && a.num_minors == b.num_minors
                && a.is_k == b.is_k
                && a.inductive_name == b.inductive_name
                && a.rules.len() == b.rules.len()
                && a.rules.iter().zip(&b.rules).all(|(x, y)| {
                    x.constructor_name == y.constructor_name
                        && x.num_fields == y.num_fields
                        && x.rhs == y.rhs
                });
        }
        (None, None) => {}
        _ => return false,
    }
    match (env.get_inductive(name), replay.get_inductive(name)) {
        (Some(a), Some(b)) => {
            return a.num_params == b.num_params
                && a.constructor_names == b.constructor_names
                && a.all_names == b.all_names;
        }
        (None, None) => {}
        _ => return false,
    }
    match (env.get_constructor(name), replay.get_constructor(name)) {
        (Some(a), Some(b)) => a.inductive_name == b.inductive_name && a.type_ == b.type_,
        (None, None) => true,
        _ => false,
    }
}

/// Whether the replay environment already holds `unit` as the same
/// declaration(s) the source environment reaches.
fn given(env: &Environment, replay: &Environment, id: &UnitId, unit: &Unit) -> Given {
    let present = unit
        .members
        .iter()
        .filter(|m| replay.get_const(m).is_some())
        .count();
    if present == 0 {
        return Given::No;
    }
    if present != unit.members.len() {
        return Given::Conflict(format!(
            "{present} of {} members are already held under the same name by the \
             consumer's base",
            unit.members.len()
        ));
    }
    if let UnitId::Constant(name) = id {
        if base_stub_upgrade(env, replay, name) {
            return Given::Yes;
        }
    }
    match unit
        .members
        .iter()
        .find(|m| !same_as_replayed(env, replay, m))
    {
        None => Given::Yes,
        Some(m) => Given::Conflict(format!(
            "{m} is already held by the replay environment (the consumer's base, or an \
             earlier refused re-admission) as a different declaration"
        )),
    }
}

#[cfg(test)]
#[path = "imported_native_reducer_tests.rs"]
mod native_reducer_tests;
