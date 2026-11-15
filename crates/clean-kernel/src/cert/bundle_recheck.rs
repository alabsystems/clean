// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Re-derive a bundle's embedded environment from the kernel's canonical base.
//!
//! # What was wrong
//!
//! A `.cleancert` bundle carries the [`Environment`] its certificates replay
//! in, and the bundle's author chooses it. `kernel cert verify` replayed each
//! manifest theorem against that environment and believed every declaration
//! in it: a `Theorem`-kind `Test.fakeFalse : False := True.intro`, inserted
//! without a check, then `Test.bad : False := Test.fakeFalse`, verified
//! `all_passed` (pinned as the EXPECTED outcome by
//! `forged_dependency_cannot_earn_kernel_verified_bundle_trust` from f88cde40d,
//! 2026-07-27, until 2026-09-28). The axiom disclosure lists `Axiom`-kind
//! constants only, so it listed nothing for `Test.bad`, and the one remaining
//! signal (`trust_level: unverified`) is also what a legitimate bundle
//! reports. The canonical-statement check that decides whether `propext` or
//! `Classical.choice` is the kernel's own compares `Iff`, `Eq` and `Nonempty`
//! BY NAME, so in an environment the author controls those names could mean
//! anything.
//!
//! # What this does
//!
//! [`rebuild_from_canonical_base`] starts from [`Environment::try_with_prelude`]
//! — the environment `clean export-cert` itself elaborates in — and walks EVERY
//! declaration the bundle environment holds (constants, and every inductive,
//! constructor, recursor and quotient record), in dependency order:
//!
//! * a name the base holds is taken as given only when the bundle holds the
//!   base's VERY declaration — kind, universe parameters, type, value, and
//!   every family or quotient record, compared structurally. Anything else
//!   under a base name is refused. This pins `Iff`, `Eq`, `Nonempty`, `True`,
//!   `False`, `Bool`, the quotient and every other prelude declaration to the
//!   canonical prelude's own, so the canonical-statement check reads them as
//!   the kernel means them;
//! * every other declaration is re-admitted by the kernel against only the
//!   base and what was re-admitted before it: an ordinary constant through
//!   [`Environment::add_decl`], an inductive family through
//!   [`Environment::add_inductive`] / [`Environment::add_inductive_core`] with
//!   its recursors REGENERATED and the bundle's only compared;
//! * a name outside the base is refused when the kernel reduces or builds it
//!   BY NAME ([`KERNEL_BY_NAME_CONSTANTS`]), when the base's native-reducer
//!   table evaluates it, when it is a quotient primitive, or when the bundle
//!   marks it `unsafe` / `partial`;
//! * a refusal propagates to every declaration that depends on it.
//!
//! Replay, the final type comparison, cross-project verification and the
//! rooted certification audit then run in the REBUILT environment, never in
//! the bundle's. A theorem whose constant closure reaches a declaration the
//! rebuild did not re-derive fails, naming it.
//!
//! # What a pass does not establish
//!
//! It re-derives nothing in the base (the prelude a `clean check` session
//! trusts, native reducers included), and nothing about the axioms it
//! admitted: an `Axiom`-kind declaration is admitted as an assumption and
//! disclosed as one.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use crate::inductive::{Constructor, InductiveDecl, InductiveType, RecursorRule};
use crate::name::Name;
use crate::tc::TypeChecker;

/// Every constant the type checker reduces, types or builds BY NAME, never
/// consulting the declaration that carries it (`tc/reduction/nat.rs`,
/// `tc/reduction/int.rs`, `quot.rs`, `inductive/mod.rs`). A bundle
/// declaration under one of these names that is not the base's own would give
/// the name two meanings — the declared one by δ, the built-in one by name.
///
/// Mirrors the names of `clean_olean::recheck_closed::extension_binding::
/// EXTENSION_KEYS`, whose census test keeps that list exhaustive over `tc/`;
/// `every_extension_key_is_a_kernel_by_name_constant` there fails if this list
/// misses one.
pub const KERNEL_BY_NAME_CONSTANTS: &[&str] = &[
    "Nat",
    "Nat.zero",
    "Nat.succ",
    "Nat.rec",
    "Nat.pred",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.pow",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Int",
    "Int.ofNat",
    "Int.negSucc",
    "Int.rec",
    "Int.add",
    "Int.sub",
    "Int.mul",
    "Bool.true",
    "Bool.false",
    "String",
    "String.ofList",
    "List.nil",
    "List.cons",
    "Char",
    "Char.ofNat",
    "Lean.reduceBool",
    "Lean.reduceNat",
    "Eq",
    "optParam",
    "autoParam",
    "outParam",
    "semiOutParam",
];

fn is_kernel_by_name_constant(name: &Name) -> bool {
    KERNEL_BY_NAME_CONSTANTS
        .iter()
        .any(|key| crate::env::name_has_components(name, key))
}

/// What re-deriving a bundle's environment from the canonical base measured.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct BundleEnvironmentRecheck {
    /// Bundle constants that are the canonical base's very declaration (taken
    /// as given, compared structurally).
    pub pinned_to_base: usize,
    /// Ordinary constants re-admitted through `add_decl`.
    pub constants_readmitted: usize,
    /// Inductive families re-admitted with their recursors regenerated.
    pub families_readmitted: usize,
    /// Canonical-base declarations the bundle holds with OTHER content (or a
    /// prelude family it extends or reshapes), rendered unambiguously. Any
    /// entry fails every theorem of the bundle: no honest producer changes the
    /// prelude, and the canonical-statement check reads `Iff`, `Eq`,
    /// `Nonempty` by name. Each is also in [`Self::refusals`].
    pub redefined_base: Vec<String>,
    /// Every bundle declaration the rebuild did not re-derive, with the reason
    /// (a dependent refused because of another names it). Rendered with
    /// [`Name::to_unambiguous_string`]. Sorted.
    pub refusals: Vec<(String, String)>,
}

impl BundleEnvironmentRecheck {
    /// The report when the canonical base itself could not be built: nothing
    /// was re-derived.
    #[must_use]
    pub(crate) fn unavailable(reason: &str) -> Self {
        Self {
            refusals: vec![("[canonical base]".to_string(), reason.to_string())],
            ..Self::default()
        }
    }

    /// Every declaration of the bundle environment was re-derived.
    #[must_use]
    pub fn passed(&self) -> bool {
        self.refusals.is_empty() && self.redefined_base.is_empty()
    }
}

/// The rebuilt environment and what the rebuild found.
#[derive(Debug, Clone)]
pub(crate) struct RebuiltEnvironment {
    /// The canonical base plus every re-admitted declaration. Nothing in it
    /// came from the bundle without a kernel check or a structural match
    /// against the base.
    pub(crate) env: Environment,
    /// The report.
    pub(crate) report: BundleEnvironmentRecheck,
    /// Bundle names NOT re-derived, each with the reason.
    pub(crate) unchecked: HashMap<Name, String>,
}

impl RebuiltEnvironment {
    /// The declarations `name`'s constant closure in `bundle` reaches that the
    /// rebuild did not re-derive (`name` itself included), each with the
    /// reason. Empty when everything it rests on was re-derived.
    pub(crate) fn unchecked_in_closure(
        &self,
        bundle: &Environment,
        name: &Name,
    ) -> Vec<(Name, String)> {
        if self.unchecked.is_empty() {
            return Vec::new();
        }
        let mut seen: HashSet<Name> = HashSet::new();
        let mut stack = vec![name.clone()];
        let mut found: BTreeMap<String, (Name, String)> = BTreeMap::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            if let Some(reason) = self.unchecked.get(&current) {
                found.insert(
                    current.to_unambiguous_string(),
                    (current.clone(), reason.clone()),
                );
            }
            let mut refs = HashSet::new();
            if let Some(info) = bundle.get_const(&current) {
                info.type_.collect_constants_into(&mut refs);
                if let Some(value) = &info.value {
                    value.collect_constants_into(&mut refs);
                }
            }
            stack.extend(refs.into_iter().filter(|r| !seen.contains(r)));
        }
        found.into_values().collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum UnitId {
    Constant(Name),
    Family(Name),
}

impl UnitId {
    fn label(&self) -> String {
        match self {
            Self::Constant(name) => name.to_unambiguous_string(),
            Self::Family(head) => format!("family {}", head.to_unambiguous_string()),
        }
    }
}

struct Unit {
    members: Vec<Name>,
    deps: BTreeSet<Name>,
}

/// Why a unit was not re-derived.
struct Refusal {
    reason: String,
    /// The unit holds canonical-base names with other content.
    redefines_base: bool,
}

impl Refusal {
    fn base(reason: String) -> Self {
        Self {
            reason,
            redefines_base: true,
        }
    }

    fn other(reason: String) -> Self {
        Self {
            reason,
            redefines_base: false,
        }
    }
}

/// Re-derive `bundle` from the canonical base; see the module docs.
///
/// # Errors
///
/// Only when the canonical base itself cannot be built.
pub(crate) fn rebuild_from_canonical_base(
    bundle: &Environment,
) -> Result<RebuiltEnvironment, String> {
    let base = Environment::try_with_prelude()
        .map_err(|e| format!("the canonical base (the prelude) cannot be built: {e}"))?;
    Ok(Rebuild::new(bundle, base).run())
}

struct Rebuild<'a> {
    bundle: &'a Environment,
    replay: Environment,
    base_names: HashSet<Name>,
    recursors_by_family: BTreeMap<Name, Vec<Name>>,
    constructors_by_family: BTreeMap<Name, Vec<Name>>,
    units: BTreeMap<UnitId, Unit>,
    unit_of: HashMap<Name, UnitId>,
    unavailable: HashMap<Name, String>,
    /// Bundle names whose rebuilt declaration the KERNEL built (a
    /// regenerated family member, a generated auxiliary definition): compared
    /// with [`Match::KernelBuilt`].
    kernel_built: HashSet<Name>,
    report: BundleEnvironmentRecheck,
}

impl<'a> Rebuild<'a> {
    fn new(bundle: &'a Environment, mut base: Environment) -> Self {
        base.set_option(
            "maxHeartbeats".to_string(),
            Some(crate::tc::DEFAULT_HEARTBEAT_LIMIT.to_string()),
        );
        let base_names = base.constants().map(|c| c.name.clone()).collect();
        let mut recursors_by_family: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        for rec in bundle.recursors() {
            recursors_by_family
                .entry(rec.inductive_name.clone())
                .or_default()
                .push(rec.name.clone());
        }
        for names in recursors_by_family.values_mut() {
            names.sort();
        }
        let mut constructors_by_family: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        for ctor in bundle.constructors() {
            constructors_by_family
                .entry(ctor.inductive_name.clone())
                .or_default()
                .push(ctor.name.clone());
        }
        for names in constructors_by_family.values_mut() {
            names.sort();
        }
        Self {
            bundle,
            replay: base,
            base_names,
            recursors_by_family,
            constructors_by_family,
            units: BTreeMap::new(),
            unit_of: HashMap::new(),
            unavailable: HashMap::new(),
            kernel_built: HashSet::new(),
            report: BundleEnvironmentRecheck::default(),
        }
    }

    /// Every name the bundle environment declares, in any table.
    fn bundle_names(&self) -> BTreeSet<Name> {
        let b = self.bundle;
        b.constants()
            .map(|c| c.name.clone())
            .chain(b.inductives().map(|i| i.name.clone()))
            .chain(b.constructors().map(|c| c.name.clone()))
            .chain(b.recursors().map(|r| r.name.clone()))
            .chain(b.quotients().map(|q| q.name.clone()))
            .collect()
    }

    /// The canonical head of the bundle family `name` belongs to, if any.
    fn family_head(&self, name: &Name) -> Option<Name> {
        let b = self.bundle;
        let ind = b.get_inductive(name).or_else(|| {
            b.get_constructor(name)
                .and_then(|c| b.get_inductive(&c.inductive_name))
                .or_else(|| {
                    b.get_recursor(name)
                        .and_then(|r| b.get_inductive(&r.inductive_name))
                })
        })?;
        Some(
            ind.all_names
                .iter()
                .filter(|n| b.get_inductive(n).is_some())
                .min()
                .cloned()
                .unwrap_or_else(|| ind.name.clone()),
        )
    }

    fn family_names(&self, head: &Name) -> Vec<Name> {
        self.bundle
            .get_inductive(head)
            .map(|ind| {
                if ind.all_names.is_empty() {
                    vec![ind.name.clone()]
                } else {
                    ind.all_names.clone()
                }
            })
            .unwrap_or_else(|| vec![head.clone()])
    }

    fn build_unit(&self, id: &UnitId) -> Unit {
        let b = self.bundle;
        let mut members = Vec::new();
        let mut refs = HashSet::new();
        match id {
            UnitId::Constant(name) => {
                members.push(name.clone());
                if let Some(info) = b.get_const(name) {
                    info.type_.collect_constants_into(&mut refs);
                    if let Some(value) = &info.value {
                        value.collect_constants_into(&mut refs);
                    }
                }
                if let Some(quot) = b.get_quot(name) {
                    quot.type_.collect_constants_into(&mut refs);
                }
            }
            UnitId::Family(head) => {
                for family in self.family_names(head) {
                    let Some(ind) = b.get_inductive(&family) else {
                        continue;
                    };
                    members.push(family.clone());
                    // Exactly `add_inductive`'s input: the family and
                    // constructor types. The bundle's recursors are
                    // regenerated, never consumed.
                    ind.type_.collect_constants_into(&mut refs);
                    for ctor in &ind.constructor_names {
                        members.push(ctor.clone());
                        if let Some(c) = b.get_constructor(ctor) {
                            c.type_.collect_constants_into(&mut refs);
                        }
                    }
                    if let Some(recs) = self.recursors_by_family.get(&family) {
                        members.extend(recs.iter().cloned());
                    }
                    // A constructor record naming this family that the family
                    // does not list: a member, so the comparison with what
                    // the kernel regenerates refuses it.
                    if let Some(ctors) = self.constructors_by_family.get(&family) {
                        for ctor in ctors {
                            if !members.contains(ctor) {
                                members.push(ctor.clone());
                            }
                        }
                    }
                }
            }
        }
        let own: HashSet<&Name> = members.iter().collect();
        let deps = refs.into_iter().filter(|n| !own.contains(n)).collect();
        Unit { members, deps }
    }

    fn plan(&mut self) -> Vec<UnitId> {
        for name in self.bundle_names() {
            if self.unit_of.contains_key(&name) {
                continue;
            }
            let id = match self.family_head(&name) {
                Some(head) => UnitId::Family(head),
                None => UnitId::Constant(name.clone()),
            };
            if !self.units.contains_key(&id) {
                let unit = self.build_unit(&id);
                for member in &unit.members {
                    self.unit_of.insert(member.clone(), id.clone());
                }
                self.units.insert(id.clone(), unit);
            }
            self.unit_of.insert(name, id);
        }
        self.topological_order()
    }

    /// Iterative DFS post-order over unit dependencies. A back edge is a
    /// cycle: every unit on it is refused.
    fn topological_order(&mut self) -> Vec<UnitId> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Color {
            Grey,
            Black,
        }
        let dep_units: BTreeMap<UnitId, Vec<UnitId>> = self
            .units
            .iter()
            .map(|(id, unit)| {
                let mut ds: Vec<UnitId> = unit
                    .deps
                    .iter()
                    .filter_map(|d| self.unit_of.get(d).cloned())
                    .filter(|d| d != id)
                    .collect();
                ds.sort();
                ds.dedup();
                (id.clone(), ds)
            })
            .collect();
        let mut color: BTreeMap<UnitId, Color> = BTreeMap::new();
        let mut order = Vec::with_capacity(self.units.len());
        let mut cycles: Vec<Vec<UnitId>> = Vec::new();
        let roots: Vec<UnitId> = self.units.keys().cloned().collect();
        for root in roots {
            if color.contains_key(&root) {
                continue;
            }
            let mut path: Vec<UnitId> = vec![root.clone()];
            let mut stack: Vec<(UnitId, usize)> = vec![(root.clone(), 0)];
            color.insert(root, Color::Grey);
            while let Some((id, next)) = stack.pop() {
                let deps = dep_units.get(&id).map_or(&[][..], Vec::as_slice);
                if next < deps.len() {
                    stack.push((id.clone(), next + 1));
                    let dep = deps[next].clone();
                    match color.get(&dep) {
                        Some(Color::Black) => {}
                        Some(Color::Grey) => {
                            let start = path.iter().position(|p| p == &dep).unwrap_or(0);
                            cycles.push(path[start..].to_vec());
                        }
                        None => {
                            color.insert(dep.clone(), Color::Grey);
                            path.push(dep.clone());
                            stack.push((dep, 0));
                        }
                    }
                } else {
                    color.insert(id.clone(), Color::Black);
                    if path.last() == Some(&id) {
                        path.pop();
                    }
                    order.push(id);
                }
            }
        }
        for cycle in cycles {
            let labels: Vec<String> = cycle.iter().map(UnitId::label).collect();
            for id in &cycle {
                self.refuse(id, format!("dependency cycle: {}", labels.join(" -> ")));
            }
        }
        order
    }

    fn refuse(&mut self, id: &UnitId, reason: String) {
        let Some(unit) = self.units.get(id) else {
            return;
        };
        for member in &unit.members {
            self.unavailable
                .entry(member.clone())
                .or_insert_with(|| reason.clone());
        }
        self.report.refusals.push((id.label(), reason));
    }

    fn run(mut self) -> RebuiltEnvironment {
        let order = self.plan();
        for id in order {
            if self
                .units
                .get(&id)
                .is_some_and(|u| u.members.iter().any(|m| self.unavailable.contains_key(m)))
            {
                // Already refused (a cycle).
                continue;
            }
            if let Err(refusal) = self.admit(&id) {
                if refusal.redefines_base {
                    self.report.redefined_base.push(id.label());
                }
                self.refuse(&id, refusal.reason);
            }
        }
        // Backstop: every bundle record the rebuild holds must be the rebuilt
        // one. Anything else is unchecked, however it got past the loop.
        for name in self.bundle_names() {
            if self.unavailable.contains_key(&name) {
                continue;
            }
            let how = if self.kernel_built.contains(&name) {
                Match::KernelBuilt
            } else {
                Match::Exact
            };
            if let Err(detail) = same_declaration(self.bundle, &self.replay, &name, how) {
                let reason =
                    format!("the rebuilt environment holds a different declaration: {detail}");
                self.unavailable.insert(name.clone(), reason.clone());
                self.report
                    .refusals
                    .push((name.to_unambiguous_string(), reason));
            }
        }
        self.report.refusals.sort();
        self.report.refusals.dedup();
        self.report.redefined_base.sort();
        self.report.redefined_base.dedup();
        RebuiltEnvironment {
            env: self.replay,
            report: self.report,
            unchecked: self.unavailable,
        }
    }

    fn admit(&mut self, id: &UnitId) -> Result<(), Refusal> {
        let unit = self.units.get(id).expect("planned unit");
        let members = unit.members.clone();
        if let Some((dep, why)) = unit
            .deps
            .iter()
            .find_map(|d| self.unavailable.get(d).map(|why| (d, why)))
        {
            return Err(Refusal::other(format!(
                "depends on {}, which was not re-derived ({})",
                dep.to_unambiguous_string(),
                first_line(why)
            )));
        }
        if let Some(absent) = unit.deps.iter().find(|d| {
            self.bundle.get_const(d).is_none()
                && !self.unit_of.contains_key(*d)
                && self.replay.get_const(d).is_none()
        }) {
            return Err(Refusal::other(format!(
                "depends on {}, which neither the bundle nor the canonical base declares",
                absent.to_unambiguous_string()
            )));
        }

        // Under the base's names: the base's very declaration, or refused.
        let in_base = members
            .iter()
            .filter(|m| self.base_names.contains(*m))
            .count();
        if in_base > 0 {
            if in_base != members.len() {
                return Err(Refusal::base(format!(
                    "{in_base} of {} members are canonical-base declarations and the rest are \
                     not: the bundle extends or reshapes a prelude family",
                    members.len()
                )));
            }
            for member in &members {
                same_declaration(self.bundle, &self.replay, member, Match::Exact).map_err(
                    |detail| {
                        Refusal::base(format!(
                            "redefines the canonical prelude declaration {}: {detail}",
                            member.to_unambiguous_string()
                        ))
                    },
                )?;
            }
            self.report.pinned_to_base += members.len();
            return Ok(());
        }

        // Outside the base: re-admitted by the kernel, unless the name is one
        // the kernel gives a meaning of its own.
        let outside = |reason: String| Err(Refusal::other(reason));
        for member in &members {
            if crate::quot::is_quot_name(member) {
                return outside(format!(
                    "{} is a quotient primitive: only the kernel builds those",
                    member.to_unambiguous_string()
                ));
            }
            if is_kernel_by_name_constant(member) {
                return outside(format!(
                    "{} is a name the kernel reduces or builds by name; only the canonical \
                     base's declaration may carry it",
                    member.to_unambiguous_string()
                ));
            }
            if self.replay.get_native_reducer(member).is_some() {
                return outside(format!(
                    "the canonical base evaluates {} by a native reducer",
                    member.to_unambiguous_string()
                ));
            }
            if self.bundle.is_unsafe(member) {
                return outside(format!("{} is unsafe", member.to_unambiguous_string()));
            }
            if self.bundle.is_partial(member) {
                return outside(format!("{} is partial", member.to_unambiguous_string()));
            }
        }
        match id {
            UnitId::Constant(name) => self.admit_constant(name),
            UnitId::Family(head) => self.admit_family(head, &members),
        }
        .map_err(Refusal::other)
    }

    fn admit_constant(&mut self, name: &Name) -> Result<(), String> {
        let Some(info) = self.bundle.get_const(name) else {
            return Err("a record with no constant declaration".to_string());
        };
        // Generated alongside a family re-admitted earlier (`noConfusion`,
        // `below`, …): the kernel's own output is kept and the bundle's copy
        // must be it.
        if self.replay.get_const(name).is_some() {
            self.kernel_built.insert(name.clone());
            return same_declaration(self.bundle, &self.replay, name, Match::KernelBuilt).map_err(
                |detail| {
                    format!("differs from the declaration the kernel generated for it: {detail}")
                },
            );
        }
        let decl = declaration_from_info(info).ok_or_else(|| {
            "declaration has no value and is not an axiom (nothing to re-derive)".to_string()
        })?;
        self.replay
            .add_decl(decl)
            .map_err(|e| format!("the kernel refused it: {e}"))?;
        self.report.constants_readmitted += 1;
        same_declaration(self.bundle, &self.replay, name, Match::Exact)
    }

    fn admit_family(&mut self, head: &Name, members: &[Name]) -> Result<(), String> {
        let b = self.bundle;
        let head_val = b
            .get_inductive(head)
            .ok_or_else(|| "family head is not registered as an inductive".to_string())?;
        let mut types = Vec::new();
        for family in self.family_names(head) {
            let ind = b
                .get_inductive(&family)
                .ok_or_else(|| format!("mutual member {family} is not registered"))?;
            let mut constructors = Vec::with_capacity(ind.constructor_names.len());
            for ctor_name in &ind.constructor_names {
                let ctor = b
                    .get_constructor(ctor_name)
                    .ok_or_else(|| format!("constructor {ctor_name} is not registered"))?;
                constructors.push(Constructor {
                    name: ctor.name.clone(),
                    type_: ctor.type_.clone(),
                });
            }
            types.push(InductiveType {
                name: ind.name.clone(),
                type_: ind.type_.clone(),
                constructors,
            });
        }
        let decl = InductiveDecl {
            level_params: head_val.level_params.clone(),
            num_params: head_val.num_params,
            types,
        };
        // Clean's own `add_inductive` produces `casesOn` / `recOn` as
        // RECURSORS; Lean's families carry them as definitions.
        let clean_built = members.iter().any(|m| {
            b.get_recursor(m).is_some() && {
                let s = m.to_string();
                s.ends_with(".casesOn") || s.ends_with(".recOn")
            }
        });
        let admitted = if clean_built {
            self.replay.add_inductive(decl)
        } else {
            self.replay.add_inductive_core(decl)
        };
        admitted.map_err(|e| format!("the kernel refused the family: {e}"))?;
        self.report.families_readmitted += 1;
        for member in members {
            self.kernel_built.insert(member.clone());
            same_declaration(b, &self.replay, member, Match::KernelBuilt).map_err(|detail| {
                format!(
                    "member {} differs from the one the kernel regenerated: {detail}",
                    member.to_unambiguous_string()
                )
            })?;
        }
        Ok(())
    }
}

/// The first line of `s`, cut at 160 characters.
pub(crate) fn first_line(s: &str) -> String {
    let line = s.lines().next().unwrap_or_default();
    if line.chars().count() > 160 {
        format!("{}…", line.chars().take(160).collect::<String>())
    } else {
        line.to_string()
    }
}

/// How closely a bundle declaration must match the rebuilt one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Match {
    /// Everything, values included: a declaration pinned to the base, or one
    /// re-admitted from the bundle's own content.
    Exact,
    /// A declaration the KERNEL built — a regenerated family member or a
    /// generated auxiliary definition (`casesOn`, `noConfusion`, `below`, …):
    /// kind, universe parameters and type up to definitional equality. The
    /// rebuilt environment keeps the kernel's value, so the bundle's value is
    /// never consulted and need not be the kernel's spelling (an imported
    /// family's `casesOn` is not).
    KernelBuilt,
}

/// Whether `rebuilt` holds `name` as the declaration `bundle` holds, as
/// closely as `how` demands: constant, inductive, constructor, recursor
/// (type and rules up to definitional equality in `rebuilt`: the kernel
/// keeps its regenerated rules either way) and quotient records.
/// Reducibility hints are never compared: they steer the order of unfolding,
/// never what is derivable, and `rebuilt` keeps its own.
fn same_declaration(
    bundle: &Environment,
    rebuilt: &Environment,
    name: &Name,
    how: Match,
) -> Result<(), String> {
    match (bundle.get_const(name), rebuilt.get_const(name)) {
        (Some(a), Some(b)) => same_constant(rebuilt, a, b, how)?,
        (None, None) => {}
        (Some(_), None) => return Err("absent from the rebuilt environment".to_string()),
        (None, Some(_)) => {
            return Err("the bundle holds a family record without its constant".to_string())
        }
    }
    match (bundle.get_inductive(name), rebuilt.get_inductive(name)) {
        (Some(a), Some(b)) if a == b => {}
        (None, None) => {}
        _ => return Err("inductive record differs".to_string()),
    }
    match (bundle.get_constructor(name), rebuilt.get_constructor(name)) {
        (Some(a), Some(b)) if a == b => {}
        (None, None) => {}
        _ => return Err("constructor record differs".to_string()),
    }
    match (bundle.get_quot(name), rebuilt.get_quot(name)) {
        (Some(a), Some(b)) if a == b => {}
        (None, None) => {}
        _ => return Err("quotient record differs".to_string()),
    }
    match (bundle.get_recursor(name), rebuilt.get_recursor(name)) {
        (Some(a), Some(b)) => {
            if a.level_params != b.level_params
                || a.inductive_name != b.inductive_name
                || a.num_params != b.num_params
                || a.num_indices != b.num_indices
                || a.num_motives != b.num_motives
                || a.num_minors != b.num_minors
                || a.is_k != b.is_k
                || a.arg_order != b.arg_order
            {
                return Err("recursor shape differs".to_string());
            }
            if !same_term(rebuilt, &a.type_, &b.type_) {
                return Err("recursor type differs".to_string());
            }
            same_rules(rebuilt, &a.rules, &b.rules)?;
        }
        (None, None) => {}
        _ => return Err("recursor record differs".to_string()),
    }
    Ok(())
}

fn same_constant(
    rebuilt: &Environment,
    a: &ConstantInfo,
    b: &ConstantInfo,
    how: Match,
) -> Result<(), String> {
    if a.kind != b.kind {
        return Err(format!("kind {:?}, rebuilt {:?}", a.kind, b.kind));
    }
    if a.level_params != b.level_params {
        return Err("universe parameters differ".to_string());
    }
    match how {
        Match::Exact => {
            if a.type_ != b.type_ {
                return Err("type differs".to_string());
            }
            if a.value != b.value {
                return Err("value differs".to_string());
            }
        }
        Match::KernelBuilt => {
            if !same_term(rebuilt, &a.type_, &b.type_) {
                return Err("type is not definitionally equal to the kernel's".to_string());
            }
        }
    }
    Ok(())
}

fn same_rules(
    rebuilt: &Environment,
    ours: &[RecursorRule],
    theirs: &[RecursorRule],
) -> Result<(), String> {
    if ours.len() != theirs.len() {
        return Err(format!(
            "{} ι-rules, the kernel regenerates {}",
            ours.len(),
            theirs.len()
        ));
    }
    for (a, b) in ours.iter().zip(theirs) {
        if a.constructor_name != b.constructor_name
            || a.num_fields != b.num_fields
            || a.recursive_fields != b.recursive_fields
        {
            return Err(format!(
                "ι-rule for {} differs in shape",
                a.constructor_name.to_unambiguous_string()
            ));
        }
        if !same_term(rebuilt, &a.rhs, &b.rhs) {
            return Err(format!(
                "ι-rule right-hand side for {} differs from the regenerated one",
                a.constructor_name.to_unambiguous_string()
            ));
        }
    }
    Ok(())
}

/// Syntactic equality, then definitional equality in the rebuilt environment.
fn same_term(rebuilt: &Environment, a: &crate::Expr, b: &crate::Expr) -> bool {
    a == b || TypeChecker::new(rebuilt).is_def_eq(a, b)
}

fn declaration_from_info(info: &ConstantInfo) -> Option<Declaration> {
    match info.kind {
        ConstantKind::Definition => Some(Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
            is_reducible: info.is_reducible,
        }),
        ConstantKind::Theorem => Some(Declaration::Theorem {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
        }),
        ConstantKind::Opaque => Some(Declaration::Opaque {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
        }),
        ConstantKind::Axiom => Some(Declaration::Axiom {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
        }),
    }
}
