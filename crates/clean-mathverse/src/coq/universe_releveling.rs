// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Global monomorphic universe RE-LEVELING for the Coq SerAPI import — the
//! measured fix for the pure `expected Sort(Succ(Zero)), got
//! Sort(Succ(Succ(Zero)))` over-leveling class.
//!
//! # Measured diagnosis (2026-07-12, decoded from the real corpus)
//!
//! The over-leveling seeds (`Coq.Lists.List.app_assoc`,
//! `PeanoNat.Nat.max_case_strong`, `mathcomp.ssreflect.bigop.big_nil`, …)
//! all share ONE shape: a dependency with a `A : Type@{u}` binder — `u` a
//! NAMED global monomorphic level, collapsed to the model's `Type 1` — is
//! applied at a TYPE-LEVEL argument:
//!
//! - a sort literal (`@eq Type@{v} (list A) (list A)` in the `f_equal`-style
//!   compiled proofs), whose kernel type is `Type 2`, or
//! - a Π-telescope over `Type`-sorted binders (`unlock (∀R:Type.∀I:Type.…)`
//!   in the mathcomp `bigop` locked-definition proofs), which also lives at
//!   `Type 2`.
//!
//! Coq accepts these because the dependency's `u` is a FLEXIBLE global
//! level: the use site contributes the constraint `u ≥ v + 1` to the global
//! universe graph. The SerAPI dumps carry universe OCCURRENCES but not the
//! constraint graph, and the importer's uniform `base(named) = 1` collapse
//! floors `u` below its own use sites — one Coq level, rendered
//! inconsistently with its obligations (the DIRECTION RULE's identity-loss
//! case, NOT cumulativity: `got` is BIGGER than `expected`).
//!
//! # The lever: reconstruct the constraints FROM the application sites
//!
//! The only witnesses of the lost constraints ARE the application sites, so
//! mine them back:
//!
//! 1. **Signature scan** — for every dumped declaration, record which leading
//!    Π-binders are plain named-level sorts (`Type@{uid}`, single arm) and
//!    the (symbolic) sort of its codomain.
//! 2. **Constraint scan** — walk every type/value term; at each application
//!    of a known constant/inductive/constructor, compare each argument
//!    against the matching binder: when the binder is `Type@{uid_f}+k` and
//!    the argument's kernel-rendered type level is computable symbolically
//!    (`max` of `uid + c` / constant arms — sorts, Π-telescopes over sorts,
//!    registered result sorts, locally-bound `Rel`s), emit
//!    `base(uid_f) + k ≥ arm` edges. Anything else mines nothing
//!    (fail-closed: that site keeps today's behavior).
//! 3. **Solve** — max-plus fixpoint from `base = 1` with a hard cap,
//!    self-cycle/non-convergence poisoning (poisoned uid ⇒ stays at 1 =
//!    today's rendering), and STRUCTURAL PINS: any uid mentioned in the
//!    arity or constructor types of a NON-`Prop`-codomain inductive whose
//!    arity level cannot move is pinned to 1 — raising a Type-valued
//!    inductive's parameter level above its (template-collapsed) arity
//!    level would make its kernel `add_inductive` replay reject wholesale
//!    (measured: `ssreflect`'s `unlockable` shares its level with `unlock`;
//!    `eq`'s level is shared only by `Prop`-valued inductives, so the
//!    dominant `eq`-family raise stays live). Two refinements
//!    (2026-07-16, the mathcomp `Equality.clone` class — 52 mathcomp
//!    declarations whose own DECLARED TYPES rejected on `expected Sort(1),
//!    got Sort(2)`, chaining `Unknown constant` through the `eqType`
//!    hierarchy):
//!    - **lockstep relaxation** — when the arity codomain is itself a
//!      single-arm raisable named level, the family-replay constraint is
//!      mined as ordinary `arity ≥ member` edges instead of a pin, so the
//!      family's levels rise in lockstep (ssrfun's module-wide level,
//!      frozen by `wrapped`/`simpl_fun`, kept `phant_id`'s binders at
//!      `Type 1`); a poisoned arity freezes its whole group fail-closed;
//!    - **poisoned-source edge degradation** — an edge whose source is
//!      pinned degrades to the floor `to ≥ 1 + off` (the pinned source
//!      renders at base 1) instead of being dropped, so a correctly-pinned
//!      structure sort (`Equality.type`'s multi-arm arity) still pushes
//!      the helper binders that consume it above it.
//! 4. **Render** — [`super::alpha`]'s `classify_serapi_type_universe` looks
//!    the named-level uid up in the solved [`UniverseBaseMap`]: one uid ⇒
//!    one base EVERYWHERE (both binder and argument occurrences, across
//!    declarations), restoring the identity the collapse lost. Every
//!    declaration whose rendering actually uses a raised base is marked
//!    `SPECULATIVE_MOTIVE`, so a kernel rejection fails closed to a clean
//!    type-only fallback (never a taint seed, never an unsound accept).
//!
//! Soundness is unchanged: the importer only chooses different CONCRETE
//! levels; the kernel re-checks every declaration (with the Coq lane's
//! cumulative `Sort i ≤ Sort j` ascription rule absorbing the raises at
//! argument positions) and arbitrates every guess.
//!
//! # Status (2026-07-12, measured over 5 instrumented gate cycles) — OPT-IN
//!
//! The import pipeline runs this pass only under `CLEAN_COQ_UID_RELEVEL=1`
//! (default OFF = byte-identical rendering). Measured with the raise ON
//! against the 22,504-KV promoted baseline (solved raise set: 5 `Coq.Init.
//! Logic` uids → base 2):
//!
//! - **mathcomp: +5 KV, REGRESSED 0** (`GRing.SubType.cast_ringType`-class
//!   type-level `eq_rect` casts flip to KernelVerified);
//! - **stdlib: +137 KV net, but REGRESSED 128** — the raise resolves the
//!   whole measured seed class (`List.app_assoc` +18 cluster,
//!   `max_case_strong`, the `f_equal2`-family statement/proof level splits)
//!   yet 128 previously-KV decls fall to SECOND-ORDER couplings:
//!   1. recursor ELIM-SHAPE mirror divergence — a Prop record with raised
//!      `Type` params (`Berardi.retract`, `Cpo.Directed`) makes the
//!      importer's syntactic singleton analysis fail-closed to a
//!      level-param recursor while the kernel generates the Prop-only
//!      recursor (`declared 0 level params, got 1`);
//!   2. the `setoid_ring`/`Numbers.Cyclic` functor towers (~89 chained)
//!      behind a handful of `pow_pos`-class seeds mixing raised and
//!      unraised levels at invariant positions the miner cannot see.
//!
//! Both are the same lockstep-vs-anchor story one mirror deeper; clearing
//! them (elim-shape derivation consulting the raised sorts consistently,
//! plus per-site links for the ring functors) is the remaining runway
//! before the raise can default ON. The containment rules above were each
//! measured-in: gate cycle 1 (no pins) cascaded to −5,729 stdlib KV through
//! the `Var`-poly `Morphisms` sinks; cycle 4/5 (pins + alias + telescope
//! lockstep + an inductive-builder cumulativity companion) reached the
//! residual described here.
//!
//! ## Required kernel companion (NOT shipped — see below before enabling)
//!
//! The raise additionally needs the Coq lane's cumulative subtyping applied
//! inside `Environment::do_inductive_type_check`
//! (`clean-kernel/src/env/inductive_builder.rs` builds its `TypeChecker`
//! without `tc.set_cumulative(self.cumulative)`, unlike `decl_add.rs`), or
//! constructor fields applying a raised-binder constant at `Set` arguments
//! reject wholesale (measured cycle 3: mathcomp −413 through the
//! `unlockable`-record families). That one-liner is NOT included here
//! because it is behavior-changing on its own: it lets the
//! `Berardi.retract`-class Prop-record families replay for real (+8 family
//! members KV), which EXPOSES the pre-existing importer/kernel ELIM-SHAPE
//! mirror divergence — the importer emits their `…rec` references with a
//! speculative motive level param while the kernel's real recursor is
//! Prop-only (`Level count mismatch … declared 0 level params, got 1`),
//! regressing 14 baseline-KV dependents (`Berardi.*`, `Diaconescu.*`,
//! `PropExtensionality.proof_irrelevance`). Fix the elim-shape mirror
//! first; then land the kernel companion and this raise together.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::alpha::{parse_sexps, serapi_id_atom, serapi_qualified_name, Sexp};
use crate::error::{MathverseError, MathverseResult};

/// Hard cap on a solved base: a fixpoint pushing a monomorphic level above
/// this is treated as a mining artifact and poisoned back to 1 (fail-closed).
const MAX_RAISED_BASE: u32 = 4;

/// Maximum fixpoint sweeps before non-converged targets are poisoned.
const MAX_SOLVE_SWEEPS: usize = 64;

/// The dumper's synthetic template-collapse `DirPath`. Its single uid is
/// SHARED by every template-polymorphic arity in the corpus, so raising it
/// would entangle all of them; it is never a raise target.
const SYNTHETIC_TEMPLATE_DIRPATH: &str = "mathverse_template_collapse";

/// Solved global `uid → base` assignment. Only RAISED (`base > 1`) uids are
/// stored; every other named level keeps the historical base 1, so an empty
/// map reproduces the old rendering byte-for-byte.
#[derive(Debug, Default)]
pub struct UniverseBaseMap {
    raised: HashMap<String, u32>,
}

impl UniverseBaseMap {
    /// The RAISED base for `uid_key`, if the solver raised it above 1.
    #[must_use]
    pub fn raised_base(&self, uid_key: &str) -> Option<u32> {
        self.raised.get(uid_key).copied()
    }

    /// Number of raised uids.
    #[must_use]
    pub fn len(&self) -> usize {
        self.raised.len()
    }

    /// Whether no uid was raised (rendering identical to the old collapse).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.raised.is_empty()
    }

    /// Sorted `(uid, base)` snapshot (debug/observability).
    #[must_use]
    pub fn raised_entries(&self) -> Vec<(String, u32)> {
        let mut v: Vec<(String, u32)> = self.raised.iter().map(|(k, b)| (k.clone(), *b)).collect();
        v.sort();
        v
    }
}

/// The canonical map key of a named-global `(Level ((DirPath …) uid))`
/// datum: `<reversed DirPath dotted>/<uid>` (e.g.
/// `Coq.Init.Logic/23503782208`). `None` for any other datum shape.
pub(crate) fn level_datum_uid_key(datum: &Sexp) -> Option<String> {
    let Sexp::List(v) = datum else { return None };
    if !matches!(v.first(), Some(Sexp::Atom(h)) if h == "Level") {
        return None;
    }
    let Some(Sexp::List(pair)) = v.get(1) else {
        return None;
    };
    let Some(Sexp::List(dp)) = pair.first() else {
        return None;
    };
    if !matches!(dp.first(), Some(Sexp::Atom(t)) if t == "DirPath") {
        return None;
    }
    let Some(Sexp::List(segs)) = dp.get(1) else {
        return None;
    };
    let mut names: Vec<String> = Vec::with_capacity(segs.len());
    for seg in segs.iter().rev() {
        names.push(serapi_id_atom(seg)?);
    }
    let uid = match pair.get(1) {
        Some(Sexp::Atom(u)) => u.clone(),
        _ => return None,
    };
    Some(format!("{}/{}", names.join("."), uid))
}

/// One arm of a symbolic (max-plus) level expression: either a concrete
/// level or `base(uid) + offset`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LevelArm {
    Const(u32),
    Uid(String, u32),
}

/// Classification of one leading Π-binder domain for constraint mining.
#[derive(Clone, Debug, PartialEq, Eq)]
enum BinderKind {
    /// Exactly `(Sort (Type ((… (Level uid)) inc)))` — a raisable named
    /// level: argument-type arms become `≥` edges onto it.
    RaisableNamed(String, u32),
    /// A sort the re-leveling can NEVER raise: `Set`/`Prop`, a
    /// `Var`-collapsed polymorphic level (universe-polymorphic consumers
    /// like `Morphisms`/`RelationClasses`), or a multi-arm `max`. A raised
    /// level flowing INTO such a binder would flip the site from accept to
    /// reject, so every uid arm of such an argument is PINNED (measured in
    /// gate cycle 1: unpinned raises cascaded through the `Var`-poly setoid
    /// layer and knocked out the whole `Morphisms` tower).
    UnraisableSort,
    /// Not a syntactic sort (element-level binder): no mining.
    NonSort,
}

/// A declaration's mined signature: the leading Π-binder domains that are
/// plain single-arm named-level sorts, plus the (symbolic) VALUE of its
/// codomain sort when the codomain is a syntactic sort.
#[derive(Clone, Debug, Default)]
struct DeclSig {
    /// Per leading Π-binder: its [`BinderKind`].
    binders: Vec<BinderKind>,
    /// Kernel-rendered VALUE arms of the codomain sort (`Prop → 0`,
    /// `Set → 1`, `Type payload → floor-1 max of arms`), or `None` when the
    /// codomain is not a syntactic sort.
    result: Option<Vec<LevelArm>>,
}

/// Mines application-site universe constraints from raw SerAPI dumps and
/// solves them into a [`UniverseBaseMap`]. Feed every module of the import
/// session (context libraries included) through [`Self::scan_signatures`]
/// first, then [`Self::scan_constraints`], then call [`Self::solve`].
#[derive(Debug, Default)]
pub struct UniverseConstraintMiner {
    sigs: HashMap<String, DeclSig>,
    /// `base(to) ≥ base(from) + offset` edges (deduped).
    edges: HashSet<(String, String, i64)>,
    /// `base(to) ≥ floor` bounds (deduped).
    floors: HashSet<(String, u32)>,
    /// Uids that must NEVER be raised: mentioned in the arity/constructor
    /// types of a non-`Prop`-codomain inductive whose arity level cannot
    /// move (raising them would break the inductive's kernel replay),
    /// flowing into an [`BinderKind::UnraisableSort`] sink, occurring at an
    /// INVARIANT (nested binder domain) position, or involved in an
    /// unsatisfiable self-cycle.
    pinned: HashSet<String>,
    /// LOCKSTEP families (structural-pin relaxation, 2026-07-16): a
    /// non-`Prop` inductive whose arity codomain is itself a single-arm
    /// raisable named level `Type@{uid_a}+inc` does NOT pin its member
    /// levels — the kernel family-replay constraint (parameter and field
    /// levels fit under the arity level) is mined as ordinary max-plus
    /// edges onto `uid_a` instead, so the family's levels rise in LOCKSTEP
    /// (the measured `ssrfun.wrapped`/`simpl_fun` case, whose module-wide
    /// uid the old wholesale pin froze, keeping `phant_id`'s binder at
    /// `Type 1` and rejecting every mathcomp `*.clone` helper). Fail-closed
    /// companion: when `uid_a` itself ends up POISONED (cap-out, cycle,
    /// pinned elsewhere), the whole family freezes back to today's
    /// rendering — entries here are `(uid_a, members)` consulted by the
    /// backward-poisoning fixpoint in [`Self::solve`].
    lockstep_groups: Vec<(String, HashSet<String>)>,
}

impl UniverseConstraintMiner {
    /// Pass A: record every declaration's binder/codomain sort signature.
    /// Also records the STRUCTURAL PINS from non-`Prop` inductives. Errors
    /// only when the top-level s-expression stream does not parse.
    pub fn scan_signatures(&mut self, data: &str) -> MathverseResult<()> {
        let sexps = parse_sexps(data).map_err(|e| MathverseError::ImportFailed {
            system: "Coq".into(),
            reason: e.to_string(),
        })?;
        for form in &sexps {
            let Sexp::List(items) = form else { continue };
            let head = match items.first() {
                Some(Sexp::Atom(s)) => s.as_str(),
                _ => continue,
            };
            match head {
                "CoqConstant" | "CoqAxiom" => {
                    if items.len() < 3 {
                        continue;
                    }
                    let Sexp::Atom(name) = &items[1] else {
                        continue;
                    };
                    self.sigs.insert(name.clone(), sig_of_type(&items[2]));
                    // INVARIANT-POSITION PIN: a literal sort inside a nested
                    // binder DOMAIN (e.g. `Π(f : Type@{w} → X). …`) is
                    // compared INVARIANTLY by the kernel's Pi rule, so
                    // raising `w` would break every consumer that still
                    // passes an unraised function. Codomain-spine sorts
                    // (`P : A → Type@{u}`, the eq_rect motive) stay
                    // raisable — `is_le` recurses covariantly through Pi
                    // codomains and cumulativity absorbs the raise there.
                    pin_invariant_sort_positions(&items[2], &mut self.pinned);
                }
                "CoqInductive" => {
                    if items.len() < 4 {
                        continue;
                    }
                    let Sexp::Atom(name) = &items[1] else {
                        continue;
                    };
                    let Sexp::Atom(idx) = &items[2] else {
                        continue;
                    };
                    let arity = &items[3];
                    self.sigs
                        .insert(format!("{name}#{idx}"), sig_of_type(arity));
                    let mut ctor_no = 0u32;
                    let mut ctor_types: Vec<&Sexp> = Vec::new();
                    for entry in &items[4..] {
                        let Sexp::List(e) = entry else { continue };
                        if matches!(e.first(), Some(Sexp::Atom(h)) if h == "Ctor") && e.len() >= 3 {
                            ctor_no += 1;
                            self.sigs
                                .insert(format!("{name}#{idx}#{ctor_no}"), sig_of_type(&e[2]));
                            ctor_types.push(&e[2]);
                        }
                    }
                    // STRUCTURAL PIN vs LOCKSTEP: a non-Prop-codomain
                    // inductive's levels participate in the kernel's
                    // inductive level check (parameter/field levels must fit
                    // under the collapsed arity level). When the arity
                    // codomain is itself a single-arm RAISABLE named level
                    // `Type@{uid_a}+inc`, that check is expressible as
                    // ordinary max-plus edges `base(uid_a)+inc ≥
                    // base(uid_f)+k` — the family's levels then move in
                    // LOCKSTEP with the arity instead of being frozen (the
                    // relaxation registers the group so a poisoned arity
                    // freezes the whole family fail-closed; see `solve`).
                    // Any other arity shape (`Set`, the shared synthetic
                    // template level, a multi-arm `max`, `Var`) cannot move,
                    // so every member level keeps today's wholesale pin.
                    // Sort payloads only — `Instance` levels are stripped at
                    // import and cannot affect rendering.
                    if !inductive_codomain_is_prop(arity) {
                        let relax = arity_codomain_named_level(arity).filter(|(uid, _)| {
                            !uid.starts_with(&format!("{SYNTHETIC_TEMPLATE_DIRPATH}/"))
                        });
                        match relax {
                            Some((arity_uid, arity_inc)) => {
                                let mut arms: Vec<LevelArm> = Vec::new();
                                collect_sort_arms_lockstep(arity, &mut arms);
                                for ct in &ctor_types {
                                    collect_sort_arms_lockstep(ct, &mut arms);
                                }
                                let mut members: HashSet<String> = HashSet::new();
                                for arm in arms {
                                    match arm {
                                        LevelArm::Uid(uid_f, k) => {
                                            members.insert(uid_f.clone());
                                            self.edges.insert((
                                                arity_uid.clone(),
                                                uid_f,
                                                i64::from(k) - i64::from(arity_inc),
                                            ));
                                        }
                                        LevelArm::Const(c) => {
                                            let floor = i64::from(c) - i64::from(arity_inc);
                                            if floor > 1 {
                                                self.floors.insert((
                                                    arity_uid.clone(),
                                                    u32::try_from(floor).unwrap_or(1),
                                                ));
                                            }
                                        }
                                    }
                                }
                                // Nested INVARIANT binder domains inside the
                                // family keep the same pin discipline as
                                // constant types (the wholesale pin used to
                                // subsume this).
                                pin_invariant_sort_positions(arity, &mut self.pinned);
                                for ct in &ctor_types {
                                    pin_invariant_sort_positions(ct, &mut self.pinned);
                                }
                                members.remove(&arity_uid);
                                if !members.is_empty() {
                                    self.lockstep_groups.push((arity_uid, members));
                                }
                            }
                            None => {
                                collect_sort_level_uids(arity, &mut self.pinned);
                                for ct in ctor_types {
                                    collect_sort_level_uids(ct, &mut self.pinned);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Pass B: mine `binder ≥ argument-type-level` edges from every
    /// application site in `data`'s types and values. Errors only when the
    /// top-level stream does not parse.
    pub fn scan_constraints(&mut self, data: &str) -> MathverseResult<()> {
        let sexps = parse_sexps(data).map_err(|e| MathverseError::ImportFailed {
            system: "Coq".into(),
            reason: e.to_string(),
        })?;
        for form in &sexps {
            let Sexp::List(items) = form else { continue };
            let head = match items.first() {
                Some(Sexp::Atom(s)) => s.as_str(),
                _ => continue,
            };
            match head {
                "CoqConstant" | "CoqAxiom" => {
                    if items.len() < 3 {
                        continue;
                    }
                    let mut stack = Vec::new();
                    self.walk(&items[2], &mut stack);
                    // A `CoqAxiom`'s optional 4th element is the `StandIn`
                    // marker atom, never a value.
                    if head == "CoqConstant" {
                        if let Some(value) = items.get(3) {
                            let mut stack = Vec::new();
                            self.walk(value, &mut stack);
                            // Same invariant-position discipline for the
                            // value's nested binder annotations (a raised
                            // uid inside `λ(g : Type@{w} → X). …` breaks
                            // the annotation against unraised callers).
                            pin_invariant_sort_positions(value, &mut self.pinned);
                            // Alias / partial-application values
                            // (`f_equal_nat := f_equal nat`): the residual
                            // Π-telescope is compared INVARIANTLY against
                            // the declared type, so the paired binder
                            // levels must move in LOCKSTEP (equality
                            // edges), and a Set/`Var`-anchored pair pins.
                            self.mine_value_alias(&items[2], value);
                            // The value's own λ-telescope annotations are
                            // the SAME binders as the declared type's
                            // Π-telescope, but Coq elaborates the Qed body
                            // with FRESH levels unified only through the
                            // constraint graph the dumps lack (measured:
                            // `Logic.f_equal2`'s statement binds A1/A2/B at
                            // one Logic uid, its proof lambdas at another).
                            // The kernel compares them INVARIANTLY, so link
                            // the paired levels in lockstep.
                            self.mine_type_value_telescopes(&items[2], value);
                        }
                    }
                }
                "CoqInductive" => {
                    if items.len() < 4 {
                        continue;
                    }
                    let mut stack = Vec::new();
                    self.walk(&items[3], &mut stack);
                    for entry in &items[4..] {
                        let Sexp::List(e) = entry else { continue };
                        if matches!(e.first(), Some(Sexp::Atom(h)) if h == "Ctor") && e.len() >= 3 {
                            let mut stack = Vec::new();
                            self.walk(&e[2], &mut stack);
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Solve the mined constraints into the global base map (max-plus
    /// fixpoint, cap + cycle poisoning, structural pins honored).
    #[must_use]
    pub fn solve(mut self) -> UniverseBaseMap {
        // Never raise the shared synthetic template-collapse level.
        let synthetic_prefix = format!("{SYNTHETIC_TEMPLATE_DIRPATH}/");
        let mut poisoned: HashSet<String> = self
            .pinned
            .drain()
            .chain(
                self.edges
                    .iter()
                    .map(|(to, _, _)| to.clone())
                    .chain(self.floors.iter().map(|(to, _)| to.clone()))
                    .filter(|to| to.starts_with(&synthetic_prefix)),
            )
            .collect();
        // Immediate self-cycles (`u ≥ u + k`, `k > 0`) are unsatisfiable.
        for (to, from, off) in &self.edges {
            if to == from && *off > 0 {
                poisoned.insert(to.clone());
            }
        }
        loop {
            // BACKWARD PIN PROPAGATION: an edge into a pinned target with a
            // non-negative offset means the SOURCE's level flows into a
            // binder that cannot rise with it — raising the source (for any
            // other reason) would flip that site from accept to reject, so
            // the pin propagates source-ward to a fixpoint (re-run per
            // re-solve so cap/cycle poisons propagate too). Negative
            // offsets have slack and are left to the cap.
            loop {
                let mut grew = false;
                for (to, from, off) in &self.edges {
                    if *off >= 0 && poisoned.contains(to) && poisoned.insert(from.clone()) {
                        grew = true;
                    }
                }
                // LOCKSTEP FAMILIES: a poisoned arity level freezes every
                // member of its inductive family — the family-replay
                // constraint (members fit under the arity) can no longer
                // track a member's raise once the arity is frozen at base 1,
                // so the whole family reverts to today's rendering
                // (fail-closed; equals the old wholesale structural pin).
                for (arity_uid, members) in &self.lockstep_groups {
                    if poisoned.contains(arity_uid) {
                        for m in members {
                            if poisoned.insert(m.clone()) {
                                grew = true;
                            }
                        }
                    }
                }
                if !grew {
                    break;
                }
            }
            let edges: Vec<&(String, String, i64)> = self
                .edges
                .iter()
                .filter(|(to, from, _)| !poisoned.contains(to) && !poisoned.contains(from))
                .collect();
            let mut floors: Vec<(String, u32)> = self
                .floors
                .iter()
                .filter(|(to, _)| !poisoned.contains(to))
                .cloned()
                .collect();
            // EDGE DEGRADATION (2026-07-16): an edge whose SOURCE is
            // poisoned used to be dropped wholesale, silently discarding a
            // REAL constraint — the poisoned source renders at the fixed
            // base 1, so `base(to) ≥ base(from) + off` degrades exactly to
            // the floor `base(to) ≥ 1 + off`. The measured case: mathcomp's
            // `Equality.type` arity level is (correctly) pinned by the
            // multi-arm structural rule, but `phant_id`'s binder still has
            // to sit ABOVE it (`clone` applies `phant_id` AT the structure
            // type); dropping the edge left the binder at `Type 1` and the
            // whole `*.clone` helper class rejecting on
            // `expected Sort(1), got Sort(2)`. Only `off > 0` degrades
            // (`1 + 0 = 1` is the default base — a no-op).
            for (to, from, off) in &self.edges {
                if *off > 0 && !poisoned.contains(to) && poisoned.contains(from) {
                    let floor = u32::try_from((1 + *off).min(i64::from(MAX_RAISED_BASE) + 1))
                        .unwrap_or(MAX_RAISED_BASE + 1);
                    floors.push((to.clone(), floor));
                }
            }
            let mut values: BTreeMap<&str, u32> = BTreeMap::new();
            for (to, from, _) in &edges {
                values.entry(to).or_insert(1);
                values.entry(from).or_insert(1);
            }
            for (to, floor) in &floors {
                let v = values.entry(to).or_insert(1);
                *v = (*v).max(*floor);
            }
            let mut converged = false;
            let mut last_changed: HashSet<String> = HashSet::new();
            for _ in 0..MAX_SOLVE_SWEEPS {
                let mut changed = false;
                last_changed.clear();
                for (to, from, off) in &edges {
                    let want = i64::from(*values.get(from.as_str()).unwrap_or(&1)) + off;
                    let cur = values.entry(to).or_insert(1);
                    if want > i64::from(*cur) {
                        *cur = u32::try_from(want.min(i64::from(MAX_RAISED_BASE) + 1))
                            .unwrap_or(MAX_RAISED_BASE + 1);
                        changed = true;
                        last_changed.insert(to.clone());
                    }
                }
                if !changed {
                    converged = true;
                    break;
                }
            }
            // Fail-closed poisoning: capped-out or non-converged uids revert
            // to base 1 (today's rendering) and their edges are dropped for
            // a re-solve, so a bad chain never drags sound raises with it.
            let mut new_poison: Vec<String> = values
                .iter()
                .filter(|(_, v)| **v > MAX_RAISED_BASE)
                .map(|(k, _)| (*k).to_string())
                .collect();
            if !converged {
                new_poison.extend(last_changed.iter().cloned());
            }
            if new_poison.is_empty() {
                let raised: HashMap<String, u32> = values
                    .into_iter()
                    .filter(|(_, v)| *v > 1)
                    .map(|(k, v)| (k.to_string(), v))
                    .collect();
                return UniverseBaseMap { raised };
            }
            poisoned.extend(new_poison);
        }
    }

    /// Recursive constraint walk. `stack` holds, per enclosing binder
    /// (innermost last), the symbolic VALUE arms of the binder's domain when
    /// that domain is a syntactic sort (`None` otherwise). Unrecognized
    /// binding constructs (`Case`, `Fix`, …) descend with a FRESH empty
    /// stack, so `Rel`s inside them fail closed instead of misresolving.
    fn walk(&mut self, t: &Sexp, stack: &mut Vec<Option<Vec<LevelArm>>>) {
        let Sexp::List(items) = t else { return };
        let head = match items.first() {
            Some(Sexp::Atom(s)) => s.as_str(),
            _ => {
                // Bare list (argument groups etc.): recurse into children.
                for c in items {
                    self.walk(c, stack);
                }
                return;
            }
        };
        match head {
            "Prod" | "Lambda" if items.len() >= 4 => {
                self.walk(&items[2], stack);
                stack.push(sort_value_arms(&items[2]));
                self.walk(&items[3], stack);
                stack.pop();
            }
            "LetIn" if items.len() >= 5 => {
                // (LetIn <annot> <value> <type> <body>)
                self.walk(&items[2], stack);
                self.walk(&items[3], stack);
                stack.push(sort_value_arms(&items[3]));
                self.walk(&items[4], stack);
                stack.pop();
            }
            "Cast" if items.len() >= 4 => {
                self.walk(&items[1], stack);
                self.walk(&items[3], stack);
            }
            "App" if items.len() >= 3 => {
                self.walk(&items[1], stack);
                if let Sexp::List(args) = &items[2] {
                    for a in args {
                        self.walk(a, stack);
                    }
                    self.mine_application(&items[1], args, stack);
                    self.mine_lambda_redex(&items[1], args, stack);
                }
            }
            "Sort" | "Rel" | "Var" | "Int" | "Float" => {}
            "Const" | "Ind" | "Construct" => {}
            _ => {
                // Case / Fix / CoFix / Proj / Evar / …: binder structure not
                // tracked here — recurse with a fresh stack (Rel → None).
                let mut fresh = Vec::new();
                for c in &items[1..] {
                    self.walk_opaque(c, &mut fresh);
                }
            }
        }
    }

    /// Descent helper for unrecognized nodes: same dispatch as [`Self::walk`]
    /// (so nested `App`/`Prod` shapes still mine) but the caller supplies the
    /// fresh, outer-context-free stack.
    fn walk_opaque(&mut self, t: &Sexp, stack: &mut Vec<Option<Vec<LevelArm>>>) {
        self.walk(t, stack);
    }

    /// At an application of a known head, compare each argument against the
    /// head's matching Π-binder: a raisable named-sort binder yields `≥`
    /// edges; an UNRAISABLE sort binder PINS every uid arm of the argument
    /// (raising a level that flows into a fixed-level sink would flip the
    /// site from accept to reject — the measured gate-cycle-1 cascade).
    fn mine_application(&mut self, f: &Sexp, args: &[Sexp], stack: &[Option<Vec<LevelArm>>]) {
        let Some(key) = reference_sig_key(f) else {
            return;
        };
        let Some(sig) = self.sigs.get(&key) else {
            return;
        };
        let mut mined: Vec<(BinderKind, Vec<LevelArm>)> = Vec::new();
        for (arg, binder) in args.iter().zip(sig.binders.iter()) {
            if matches!(binder, BinderKind::NonSort) {
                continue;
            }
            let Some(arms) = term_type_level(arg, &self.sigs, stack, 0) else {
                continue;
            };
            mined.push((binder.clone(), arms));
        }
        for (binder, arms) in mined {
            self.record_binder_flow(&binder, arms);
        }
    }

    /// A beta-redex whose head is an annotated lambda telescope
    /// (`(App (Lambda (x:T) …) (a…))`, the compiled-proof `_evar_` shape):
    /// each annotation is a binder the kernel checks the matching argument
    /// against — mine it exactly like a constant's Π-binder.
    fn mine_lambda_redex(&mut self, f: &Sexp, args: &[Sexp], stack: &[Option<Vec<LevelArm>>]) {
        let mut cur = f;
        for arg in args {
            let Sexp::List(items) = cur else { return };
            if !matches!(items.first(), Some(Sexp::Atom(h)) if h == "Lambda") || items.len() < 4 {
                return;
            }
            let binder = classify_binder_domain(&items[2]);
            if !matches!(binder, BinderKind::NonSort) {
                if let Some(arms) = term_type_level(arg, &self.sigs, stack, 0) {
                    self.record_binder_flow(&binder, arms);
                }
            }
            cur = &items[3];
        }
    }

    /// Alias / partial-application VALUE (`Definition f_equal_nat :=
    /// f_equal nat`, `Definition esym := eq_sym`, possibly under a leading
    /// λ-telescope): the kernel compares the value's RESIDUAL Π-telescope
    /// against the declared type's remaining Π-binders INVARIANTLY (Pi
    /// domains use def-eq even under cumulativity), so each paired binder
    /// level must render EQUAL. Mine equality edges between paired raisable
    /// named levels — the alias closure then raises in lockstep or, when
    /// any member is anchored to an unraisable sort (`Set`, `Var`-collapsed,
    /// multi-arm), pins the whole chain through backward propagation
    /// (measured gate cycle 2: `Peano.f_equal_nat`/`ssrfun.esym` broke as
    /// new seeds when `eq`'s level rose alone).
    fn mine_value_alias(&mut self, decl_type: &Sexp, value: &Sexp) {
        // Peel the value: `Cast`s transparently, then the leading
        // λ-telescope (each λ consumes one declared Π-binder).
        let mut peeled = 0usize;
        let mut v = value;
        loop {
            let Sexp::List(items) = v else { return };
            match items.first() {
                Some(Sexp::Atom(h)) if h == "Cast" && items.len() >= 2 => v = &items[1],
                Some(Sexp::Atom(h)) if h == "Lambda" && items.len() >= 4 => {
                    peeled += 1;
                    v = &items[3];
                }
                _ => break,
            }
        }
        let (head_key, applied) = {
            let Sexp::List(items) = v else { return };
            match items.first() {
                Some(Sexp::Atom(h)) if h == "Const" || h == "Ind" || h == "Construct" => {
                    match reference_sig_key(v) {
                        Some(k) => (k, 0usize),
                        None => return,
                    }
                }
                Some(Sexp::Atom(h)) if h == "App" && items.len() >= 3 => {
                    let Some(k) = reference_sig_key(&items[1]) else {
                        return;
                    };
                    let Sexp::List(args) = &items[2] else { return };
                    (k, args.len())
                }
                _ => return,
            }
        };
        let Some(head_sig) = self.sigs.get(&head_key).cloned() else {
            return;
        };
        let decl_sig = sig_of_type(decl_type);
        // The head must have residual binders left for this to constrain
        // anything (a fully-applied head reduces to codomain linking only).
        let head_rest = head_sig.binders.get(applied..).unwrap_or(&[]);
        let decl_rest = decl_sig.binders.get(peeled..).unwrap_or(&[]);
        let paired = head_rest.len().min(decl_rest.len());
        for (h, d) in head_rest.iter().zip(decl_rest.iter()) {
            self.link_invariant(h, d);
        }
        // Length mismatch (declared codomain abbreviates the residual
        // telescope or vice versa): the unmatched raisable levels sit at
        // positions we cannot pair — pin them (fail-closed).
        for b in head_rest
            .iter()
            .skip(paired)
            .chain(decl_rest.iter().skip(paired))
        {
            if let BinderKind::RaisableNamed(u, _) = b {
                self.pinned.insert(u.clone());
            }
        }
        // Codomain linking, only for the exactly-paired case: equality-link
        // single-uid result sorts; pin uid arms on any shape mismatch where
        // a uid is involved.
        if head_rest.len() == paired && decl_rest.len() == paired {
            self.link_result_arms(head_sig.result.as_deref(), decl_sig.result.as_deref());
        }
    }

    /// Walk the declared type's Π-telescope and the value's λ-telescope in
    /// step, equality-linking each paired binder-domain level (the kernel's
    /// `check_type` compares them with INVARIANT Pi domains). `Cast`s on the
    /// value unwrap transparently; the walk stops at the first non-Π /
    /// non-λ node (the residual is the alias rule's job).
    fn mine_type_value_telescopes(&mut self, decl_type: &Sexp, value: &Sexp) {
        let mut ty = decl_type;
        let mut v = value;
        loop {
            // Unwrap value-side casts.
            loop {
                let Sexp::List(vi) = v else { return };
                if matches!(vi.first(), Some(Sexp::Atom(h)) if h == "Cast") && vi.len() >= 2 {
                    v = &vi[1];
                } else {
                    break;
                }
            }
            let (Sexp::List(ti), Sexp::List(vi)) = (ty, v) else {
                return;
            };
            let ty_is_prod =
                matches!(ti.first(), Some(Sexp::Atom(h)) if h == "Prod") && ti.len() >= 4;
            let v_is_lam =
                matches!(vi.first(), Some(Sexp::Atom(h)) if h == "Lambda") && vi.len() >= 4;
            if !ty_is_prod || !v_is_lam {
                return;
            }
            self.link_invariant(
                &classify_binder_domain(&ti[2]),
                &classify_binder_domain(&vi[2]),
            );
            ty = &ti[3];
            v = &vi[3];
        }
    }

    /// Equality-link the (invariant) codomain sorts of an alias pairing.
    fn link_result_arms(&mut self, head: Option<&[LevelArm]>, decl: Option<&[LevelArm]>) {
        let uid_arms = |arms: Option<&[LevelArm]>| -> Vec<(String, u32)> {
            arms.map(|a| {
                a.iter()
                    .filter_map(|arm| match arm {
                        LevelArm::Uid(u, k) => Some((u.clone(), *k)),
                        LevelArm::Const(_) => None,
                    })
                    .collect()
            })
            .unwrap_or_default()
        };
        let h = uid_arms(head);
        let d = uid_arms(decl);
        if h.is_empty() && d.is_empty() {
            return;
        }
        match (h.as_slice(), d.as_slice()) {
            ([(u1, k1)], [(u2, k2)]) => {
                self.edges
                    .insert((u1.clone(), u2.clone(), i64::from(*k2) - i64::from(*k1)));
                self.edges
                    .insert((u2.clone(), u1.clone(), i64::from(*k1) - i64::from(*k2)));
            }
            _ => {
                for (u, _) in h.iter().chain(d.iter()) {
                    self.pinned.insert(u.clone());
                }
            }
        }
    }

    /// One invariant binder pairing of an alias/partial-application value:
    /// raisable↔raisable levels move in lockstep (mutual `≥` edges);
    /// a raisable level paired with an unraisable sort pins.
    fn link_invariant(&mut self, a: &BinderKind, b: &BinderKind) {
        match (a, b) {
            (BinderKind::RaisableNamed(u1, k1), BinderKind::RaisableNamed(u2, k2)) => {
                self.edges
                    .insert((u1.clone(), u2.clone(), i64::from(*k2) - i64::from(*k1)));
                self.edges
                    .insert((u2.clone(), u1.clone(), i64::from(*k1) - i64::from(*k2)));
            }
            (BinderKind::RaisableNamed(u, _), BinderKind::UnraisableSort)
            | (BinderKind::UnraisableSort, BinderKind::RaisableNamed(u, _)) => {
                self.pinned.insert(u.clone());
            }
            _ => {}
        }
    }

    /// Record one argument-into-binder flow: edges/floors onto a raisable
    /// named binder, pins for arms flowing into an unraisable sort binder.
    fn record_binder_flow(&mut self, binder: &BinderKind, arms: Vec<LevelArm>) {
        match binder {
            BinderKind::RaisableNamed(uid_f, inc_f) => {
                for arm in arms {
                    match arm {
                        LevelArm::Const(c) => {
                            let floor = i64::from(c) - i64::from(*inc_f);
                            if floor > 1 {
                                self.floors
                                    .insert((uid_f.clone(), u32::try_from(floor).unwrap_or(1)));
                            }
                        }
                        LevelArm::Uid(a, k) => {
                            let off = i64::from(k) - i64::from(*inc_f);
                            self.edges.insert((uid_f.clone(), a, off));
                        }
                    }
                }
            }
            BinderKind::UnraisableSort => {
                for arm in arms {
                    if let LevelArm::Uid(a, _) = arm {
                        self.pinned.insert(a);
                    }
                }
            }
            BinderKind::NonSort => {}
        }
    }
}

/// The signature-registry key of a `Const`/`Ind`/`Construct` reference node,
/// mirroring the keys [`UniverseConstraintMiner::scan_signatures`] writes.
fn reference_sig_key(f: &Sexp) -> Option<String> {
    let Sexp::List(items) = f else { return None };
    let head = match items.first() {
        Some(Sexp::Atom(s)) => s.as_str(),
        _ => return None,
    };
    match head {
        "Const" => serapi_qualified_name(f),
        "Ind" => {
            let name = serapi_qualified_name(f)?;
            let idx = ind_ref_indices(items.get(1)?, 1)?;
            Some(format!("{name}#{}", idx[0]))
        }
        "Construct" => {
            let name = serapi_qualified_name(f)?;
            let idx = ind_ref_indices(items.get(1)?, 2)?;
            Some(format!("{name}#{}#{}", idx[0], idx[1]))
        }
        _ => None,
    }
}

/// Collect the trailing `want` integer atoms of a nested SerAPI
/// `Ind`/`Construct` reference payload, innermost-integer-last:
/// `(((MutInd …) 0) 1)` → `[0, 1]` for `want == 2`; `((MutInd …) 0)` →
/// `[0]` for `want == 1`. The payload's head element may itself be a list
/// wrapping the next level.
fn ind_ref_indices(payload: &Sexp, want: usize) -> Option<Vec<u32>> {
    let Sexp::List(v) = payload else { return None };
    // payload = (<inner> <Instance …>) or already (<…> <int>).
    let mut out = Vec::with_capacity(want);
    let mut cur = v;
    loop {
        // Trailing integer atom at this level?
        let last_int = match cur.last() {
            Some(Sexp::Atom(a)) => a.parse::<u32>().ok(),
            _ => None,
        };
        if let Some(i) = last_int {
            out.push(i);
            if out.len() == want {
                out.reverse();
                return Some(out);
            }
        }
        match cur.first() {
            Some(Sexp::List(inner)) => cur = inner,
            _ => return None,
        }
    }
}

/// Whether an inductive's arity codomain (after its leading Π-telescope) is
/// syntactically `Prop` (impredicative — parameter levels unconstrained).
fn inductive_codomain_is_prop(arity: &Sexp) -> bool {
    let mut cur = arity;
    loop {
        let Sexp::List(items) = cur else { return false };
        match items.first() {
            Some(Sexp::Atom(h)) if h == "Prod" && items.len() >= 4 => cur = &items[3],
            Some(Sexp::Atom(h)) if h == "Sort" => {
                return matches!(items.get(1), Some(Sexp::Atom(s)) if s == "Prop");
            }
            _ => return false,
        }
    }
}

/// Collect every named-level uid key occurring anywhere in `t`.
fn collect_level_uids(t: &Sexp, out: &mut HashSet<String>) {
    if let Some(key) = level_datum_uid_key(t) {
        out.insert(key);
        return;
    }
    if let Sexp::List(items) = t {
        for c in items {
            collect_level_uids(c, out);
        }
    }
}

/// Collect the named-level uids of every literal `(Sort (Type …))` payload in
/// `t` (universe `Instance`s are excluded — they are STRIPPED at import and
/// cannot affect rendering, so pinning from them would be pure noise).
fn collect_sort_level_uids(t: &Sexp, out: &mut HashSet<String>) {
    let Sexp::List(items) = t else { return };
    if matches!(items.first(), Some(Sexp::Atom(h)) if h == "Sort") {
        if let Some(payload) = items.get(1) {
            collect_level_uids(payload, out);
        }
        return;
    }
    for c in items {
        collect_sort_level_uids(c, out);
    }
}

/// `Some((uid_key, inc))` when the inductive arity's CODOMAIN (after its
/// leading Π-telescope) is exactly a single-arm raisable named-level sort —
/// the lockstep-relaxation eligibility shape (see `scan_signatures`).
fn arity_codomain_named_level(arity: &Sexp) -> Option<(String, u32)> {
    let mut cur = arity;
    while let Sexp::List(items) = cur {
        if matches!(items.first(), Some(Sexp::Atom(h)) if h == "Prod") && items.len() >= 4 {
            cur = &items[3];
        } else {
            break;
        }
    }
    single_named_level_sort(cur)
}

/// Collect the rendered level arms — WITH increments — of every literal
/// `(Sort …)` payload in `t`, for the lockstep relaxation: named arms
/// become `≥` edges onto the family's arity level, fixed arms become
/// floors. Datums the model renders at a FIXED base contribute `Const`
/// arms mirroring `classify_serapi_type_universe`'s collapse: `Prop → 0`,
/// `Set → 1`, pierced-`Set` (`SProp` datum) `→ inc`, `Var`/unrecognized
/// datums `→ 1 + inc` (the monomorphic collapse renders them at base 1; a
/// datum the renderer instead REJECTS fails that declaration's import
/// outright, making the mined constraint vacuous). Universe `Instance`s
/// are excluded exactly like [`collect_sort_level_uids`].
fn collect_sort_arms_lockstep(t: &Sexp, out: &mut Vec<LevelArm>) {
    let Sexp::List(items) = t else { return };
    if matches!(items.first(), Some(Sexp::Atom(h)) if h == "Sort") {
        match items.get(1) {
            Some(Sexp::Atom(s)) if s == "Prop" => out.push(LevelArm::Const(0)),
            Some(Sexp::Atom(s)) if s == "Set" => out.push(LevelArm::Const(1)),
            Some(Sexp::List(v)) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Type") => {
                let Some(Sexp::List(pairs)) = v.get(1) else {
                    return;
                };
                for entry in pairs {
                    let Sexp::List(pair) = entry else { continue };
                    if pair.len() != 2 {
                        continue;
                    }
                    let Some(inc) = (match &pair[1] {
                        Sexp::Atom(s) => s.parse::<u32>().ok(),
                        _ => None,
                    }) else {
                        continue;
                    };
                    let datum = match &pair[0] {
                        Sexp::List(fields) => fields.iter().find_map(|f| match f {
                            Sexp::List(kv)
                                if kv.len() == 2
                                    && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                            {
                                Some(&kv[1])
                            }
                            _ => None,
                        }),
                        _ => None,
                    };
                    match datum {
                        Some(d @ Sexp::List(_)) => match level_datum_uid_key(d) {
                            Some(key) => out.push(LevelArm::Uid(key, inc)),
                            None => out.push(LevelArm::Const(1 + inc)),
                        },
                        Some(Sexp::Atom(a)) if a == "SProp" => out.push(LevelArm::Const(inc)),
                        _ => out.push(LevelArm::Const(1 + inc)),
                    }
                }
            }
            _ => {}
        }
        return;
    }
    for c in items {
        collect_sort_arms_lockstep(c, out);
    }
}

/// Pin every literal-sort uid at an INVARIANT position in `t`: any sort
/// occurring inside a nested binder DOMAIN off that domain's own
/// Pi-codomain spine. The kernel's cumulative `is_le` recurses covariantly
/// through Pi CODOMAINS (so `P : A → Type@{u}` motive sorts stay raisable)
/// but compares Pi DOMAINS invariantly (so `f : Type@{w} → X` would break
/// against unraised callers if `w` raised). Binder domains that are exactly
/// the raisable single-named-sort shape are the mining targets themselves
/// and stay unpinned.
fn pin_invariant_sort_positions(t: &Sexp, pinned: &mut HashSet<String>) {
    let Sexp::List(items) = t else { return };
    let head = match items.first() {
        Some(Sexp::Atom(s)) => s.as_str(),
        _ => {
            for c in items {
                pin_invariant_sort_positions(c, pinned);
            }
            return;
        }
    };
    match head {
        "Prod" | "Lambda" if items.len() >= 4 => {
            if single_named_level_sort(&items[2]).is_none() {
                pin_domain_sorts(&items[2], pinned);
            }
            pin_invariant_sort_positions(&items[3], pinned);
        }
        "LetIn" if items.len() >= 5 => {
            if single_named_level_sort(&items[3]).is_none() {
                pin_domain_sorts(&items[3], pinned);
            }
            pin_invariant_sort_positions(&items[2], pinned);
            pin_invariant_sort_positions(&items[4], pinned);
        }
        "Sort" => {}
        _ => {
            for c in &items[1..] {
                pin_invariant_sort_positions(c, pinned);
            }
        }
    }
}

/// Inside a (non-raisable) binder domain: pin every literal-sort uid OFF the
/// domain's own Pi-codomain spine — nested Pi/λ/let DOMAINS pin wholesale;
/// the covariant codomain spine continues; sorts exactly ON the spine are
/// covariant (cumulativity absorbs a raise there) and stay unpinned.
fn pin_domain_sorts(d: &Sexp, pinned: &mut HashSet<String>) {
    let Sexp::List(items) = d else { return };
    let head = match items.first() {
        Some(Sexp::Atom(s)) => s.as_str(),
        _ => {
            for c in items {
                pin_domain_sorts(c, pinned);
            }
            return;
        }
    };
    match head {
        "Prod" | "Lambda" if items.len() >= 4 => {
            collect_sort_level_uids(&items[2], pinned);
            pin_domain_sorts(&items[3], pinned);
        }
        "LetIn" if items.len() >= 5 => {
            collect_sort_level_uids(&items[3], pinned);
            pin_domain_sorts(&items[2], pinned);
            pin_domain_sorts(&items[4], pinned);
        }
        "Sort" => {}
        _ => {
            for c in &items[1..] {
                pin_domain_sorts(c, pinned);
            }
        }
    }
}

/// The kernel-rendered VALUE arms of a syntactic sort node `(Sort …)`:
/// `Prop → 0`, `Set → 1`, `Type payload → max(1, arms(base+inc))` with the
/// model floor arm `Const(1)` included. `None` when `t` is not a sort or the
/// payload is out of model (`Var`, malformed).
fn sort_value_arms(t: &Sexp) -> Option<Vec<LevelArm>> {
    let Sexp::List(items) = t else { return None };
    if !matches!(items.first(), Some(Sexp::Atom(h)) if h == "Sort") {
        return None;
    }
    match items.get(1)? {
        Sexp::Atom(s) if s == "Prop" => Some(vec![LevelArm::Const(0)]),
        Sexp::Atom(s) if s == "Set" => Some(vec![LevelArm::Const(1)]),
        payload @ Sexp::List(v) if matches!(v.first(), Some(Sexp::Atom(h)) if h == "Type") => {
            type_payload_value_arms(payload)
        }
        _ => None,
    }
}

/// The VALUE arms of a `(Type <pairs>)` payload, mirroring
/// `classify_serapi_type_universe`'s increment-aware collapse: per arm
/// `(Level uid, inc) → Uid(uid, inc)`, pierced-`Set` `(SProp, inc) →
/// Const(inc)`, plus the model floor `Const(1)`. `Var` and malformed arms
/// yield `None` (fail closed).
fn type_payload_value_arms(payload: &Sexp) -> Option<Vec<LevelArm>> {
    let Sexp::List(v) = payload else { return None };
    let Some(Sexp::List(pairs)) = v.get(1) else {
        return None;
    };
    if pairs.is_empty() {
        return None;
    }
    let mut arms = vec![LevelArm::Const(1)];
    for entry in pairs {
        let Sexp::List(pair) = entry else { return None };
        if pair.len() != 2 {
            return None;
        }
        let inc: u32 = match &pair[1] {
            Sexp::Atom(s) => s.parse().ok()?,
            _ => return None,
        };
        let datum = match &pair[0] {
            Sexp::List(fields) => fields.iter().find_map(|f| match f {
                Sexp::List(kv)
                    if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") =>
                {
                    Some(&kv[1])
                }
                _ => None,
            }),
            _ => None,
        };
        match datum {
            Some(d @ Sexp::List(_)) => {
                let key = level_datum_uid_key(d)?;
                arms.push(LevelArm::Uid(key, inc));
            }
            Some(Sexp::Atom(a)) if a == "SProp" => arms.push(LevelArm::Const(inc)),
            _ => return None,
        }
    }
    Some(arms)
}

/// Shift every arm by `+n` (symbolic successor).
fn arms_plus(arms: Vec<LevelArm>, n: u32) -> Vec<LevelArm> {
    arms.into_iter()
        .map(|a| match a {
            LevelArm::Const(c) => LevelArm::Const(c + n),
            LevelArm::Uid(u, k) => LevelArm::Uid(u, k + n),
        })
        .collect()
}

/// The kernel-rendered LEVEL OF THE TYPE of `t` (`t : Sort(result)`),
/// symbolically, for the type-level shapes the over-leveling class
/// exercises. `stack` carries enclosing binder-domain value arms (innermost
/// last); `local_depth` counts frames pushed within the current argument.
/// Returns `None` whenever the level is not syntactically determined
/// (fail-closed: no constraint is mined from that argument).
fn term_type_level(
    t: &Sexp,
    sigs: &HashMap<String, DeclSig>,
    stack: &[Option<Vec<LevelArm>>],
    depth: usize,
) -> Option<Vec<LevelArm>> {
    let _ = depth;
    let Sexp::List(items) = t else { return None };
    let head = match items.first() {
        Some(Sexp::Atom(s)) => s.as_str(),
        _ => return None,
    };
    match head {
        // A sort term: `Sort(v) : Sort(v+1)`, with v the rendered value.
        "Sort" => sort_value_arms(t).map(|arms| arms_plus(arms, 1)),
        // A bound variable used AS A TYPE: its level is the VALUE of its
        // binder's domain sort (only when that domain was a syntactic sort).
        "Rel" => {
            let j: usize = match items.get(1) {
                Some(Sexp::Atom(a)) => a.parse().ok()?,
                _ => return None,
            };
            if j == 0 || j > stack.len() {
                return None;
            }
            stack[stack.len() - j].clone()
        }
        // Π-telescope: imax(domain level, codomain level) — Prop codomain
        // (syntactic) makes the whole Π live in Prop.
        "Prod" if items.len() >= 4 => {
            let k_dom = term_type_level(&items[2], sigs, stack, depth + 1)?;
            let mut inner = stack.to_vec();
            inner.push(sort_value_arms(&items[2]));
            let k_cod = term_type_level(&items[3], sigs, &inner, depth + 1)?;
            if k_cod == vec![LevelArm::Const(0)] {
                return Some(vec![LevelArm::Const(0)]);
            }
            let mut out = k_dom;
            out.extend(k_cod);
            Some(out)
        }
        // A (possibly applied) constant/inductive used AS A TYPE: level =
        // the registered codomain-sort value of its head. Template
        // instantiation is approximated by the head's raw codomain arms —
        // an over-approximation the kernel arbitrates.
        "App" => {
            let key = reference_sig_key(items.get(1)?)?;
            sigs.get(&key)?.result.clone()
        }
        "Const" | "Ind" => {
            let key = reference_sig_key(t)?;
            sigs.get(&key)?.result.clone()
        }
        _ => None,
    }
}

/// Classify one binder domain node into its [`BinderKind`].
fn classify_binder_domain(d: &Sexp) -> BinderKind {
    if let Some((uid, inc)) = single_named_level_sort(d) {
        return BinderKind::RaisableNamed(uid, inc);
    }
    let is_sort = matches!(d, Sexp::List(items) if matches!(items.first(), Some(Sexp::Atom(h)) if h == "Sort"));
    if is_sort {
        BinderKind::UnraisableSort
    } else {
        BinderKind::NonSort
    }
}

/// Parse a raw declaration TYPE into its [`DeclSig`]: classify each leading
/// Π-binder domain, then the codomain sort.
fn sig_of_type(ty: &Sexp) -> DeclSig {
    let mut binders = Vec::new();
    let mut cur = ty;
    while let Sexp::List(items) = cur {
        if !matches!(items.first(), Some(Sexp::Atom(h)) if h == "Prod") || items.len() < 4 {
            break;
        }
        binders.push(classify_binder_domain(&items[2]));
        cur = &items[3];
    }
    let result = sort_value_arms(cur);
    DeclSig { binders, result }
}

/// `Some((uid_key, inc))` when `t` is exactly a single-arm named-level
/// `(Sort (Type ((… (Level uid)) inc)))` — the raisable binder shape.
fn single_named_level_sort(t: &Sexp) -> Option<(String, u32)> {
    let Sexp::List(items) = t else { return None };
    if !matches!(items.first(), Some(Sexp::Atom(h)) if h == "Sort") {
        return None;
    }
    let Some(Sexp::List(v)) = items.get(1) else {
        return None;
    };
    if !matches!(v.first(), Some(Sexp::Atom(h)) if h == "Type") {
        return None;
    }
    let Some(Sexp::List(pairs)) = v.get(1) else {
        return None;
    };
    let [Sexp::List(pair)] = pairs.as_slice() else {
        return None;
    };
    if pair.len() != 2 {
        return None;
    }
    let inc: u32 = match &pair[1] {
        Sexp::Atom(s) => s.parse().ok()?,
        _ => return None,
    };
    let datum = match &pair[0] {
        Sexp::List(fields) => fields.iter().find_map(|f| match f {
            Sexp::List(kv) if kv.len() == 2 && matches!(&kv[0], Sexp::Atom(k) if k == "data") => {
                Some(&kv[1])
            }
            _ => None,
        })?,
        _ => return None,
    };
    let key = level_datum_uid_key(datum)?;
    Some((key, inc))
}

#[cfg(test)]
mod tests {
    use super::super::alpha::{parse_sexp, CoqImporter, CoqSessionRegistry};
    use super::*;
    use crate::shard::ShardWriter;

    /// REAL `Coq.Init.Logic.eq` dump form (verbatim from
    /// `data/corpora/coq-sexp/stdlib/Coq.Init.Logic.sexp`, Coq 8.20). The
    /// `A` binder level is the module-shared `Coq.Init.Logic/23503782208`.
    const RAW_EQ_IND: &str = r#"(CoqInductive Coq.Init.Logic.eq 0 (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 2) (Sort Prop)))) (NumParams 2) (Ctor Coq.Init.Logic.eq_refl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 739561026853) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1)))))))"#;

    /// REAL `Coq.Init.Datatypes.bool` dump form.
    const RAW_BOOL_IND: &str = r#"(CoqInductive Coq.Init.Datatypes.bool 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Datatypes.true (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))) (Ctor Coq.Init.Datatypes.false (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ()))))))"#;

    /// A type-level reflexivity theorem in the REAL over-leveling shape
    /// (`app_assoc` microcosm): `@eq Type@{SerTop.7} bool bool` proved by
    /// `@eq_refl Type@{SerTop.7} bool` — the `A := Type@{v}` argument lives
    /// at `Type 2`, one above `eq`'s collapsed `Type 1` binder.
    const RAW_TYPE_LEVEL_REFL: &str = r#"(CoqConstant SerTop.type_level_refl (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Sort (Type ((((hash 77) (data (Level ((DirPath ((Id SerTop))) 7)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))) ((Sort (Type ((((hash 77) (data (Level ((DirPath ((Id SerTop))) 7)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))))"#;

    /// Negative control: an UNSATISFIABLE self-cycle — `eq` applied at
    /// `Sort(Type@{Coq.Init.Logic/23503782208})`, i.e. at its own binder
    /// level (`u ≥ u + 1`).
    const RAW_SELF_CYCLE: &str = r#"(CoqConstant SerTop.self_cycle_use (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Sort (Type ((((hash 88) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))) ((Sort (Type ((((hash 88) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))))"#;

    /// REAL `Coq.Init.Datatypes.nat` dump head (constructors only as far as
    /// needed): used by the wrong-statement negative control.
    const RAW_NAT_IND: &str = r#"(CoqInductive Coq.Init.Datatypes.nat 0 (Sort Set) (NumParams 0) (Ctor Coq.Init.Datatypes.O (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ()))))) (Ctor Coq.Init.Datatypes.S (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))))"#;

    /// Negative control: a WRONG type-level statement (`bool = nat` at
    /// `Type@{SerTop.7}`) "proved" by `@eq_refl Type@{SerTop.7} bool` —
    /// must stay rejected even when the raise makes the sorts agree.
    const RAW_WRONG_STATEMENT: &str = r#"(CoqConstant SerTop.type_level_wrong (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Sort (Type ((((hash 77) (data (Level ((DirPath ((Id SerTop))) 7)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id nat)) ()) 0) (Instance (() ())))))) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))) ((Sort (Type ((((hash 77) (data (Level ((DirPath ((Id SerTop))) 7)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id Datatypes) (Id Init) (Id Coq)))) (Id bool)) ()) 0) (Instance (() ())))))))"#;

    const EQ_UID: &str = "Coq.Init.Logic/23503782208";

    fn mine(input: &str) -> UniverseBaseMap {
        let mut miner = UniverseConstraintMiner::default();
        miner
            .scan_signatures(input)
            .expect("signature scan must parse");
        miner
            .scan_constraints(input)
            .expect("constraint scan must parse");
        miner.solve()
    }

    /// Full pipeline mirror of the production `coq-import` lane: mine →
    /// install → registry pre-passes → import → kernel verify (cumulative,
    /// as `coq_import_command` sets it).
    fn verify_with_mining(input: &str) -> crate::verify::incremental::IncrementalVerifyReport {
        use crate::library::MathverseLibrary;
        use crate::trust::policy::TrustPolicy;
        use crate::verify::incremental::verify_corpus_incremental;

        let mut registry = CoqSessionRegistry::default();
        registry.install_universe_bases(mine(input));
        CoqImporter
            .register_inductive_forms(input, &mut registry)
            .expect("inductive registration must parse");
        CoqImporter
            .register_constant_shapes(input, &mut registry)
            .expect("constant-shape registration must parse");
        let mut w = ShardWriter::new();
        CoqImporter
            .import_sexp_with_registry(input, &registry, &mut w)
            .expect("import must succeed");
        let mut buf = Vec::new();
        w.write(&mut buf).expect("shard serialization");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("shard reader");
        let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
        lib.load_shard(&reader).expect("shard load");
        let mut prelude =
            clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
        prelude.set_cumulative(true);
        verify_corpus_incremental(&lib, prelude)
    }

    #[test]
    fn test_level_datum_uid_key_extracts_dotted_reversed_dirpath() {
        let datum =
            parse_sexp(r#"(Level ((DirPath ((Id List) (Id Lists) (Id Coq))) 18336402176))"#)
                .expect("datum parses");
        assert_eq!(
            level_datum_uid_key(&datum).as_deref(),
            Some("Coq.Lists.List/18336402176")
        );
        let bad = parse_sexp(r#"(Var 0)"#).expect("datum parses");
        assert_eq!(level_datum_uid_key(&bad), None);
    }

    #[test]
    fn test_miner_sort_argument_raises_binder_uid() {
        let input = format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}");
        let bases = mine(&input);
        assert_eq!(
            bases.raised_base(EQ_UID),
            Some(2),
            "a Sort argument at eq's Type binder must raise eq's level to 2, got {bases:?}"
        );
        assert_eq!(
            bases.raised_base("SerTop/7"),
            None,
            "the argument's own level must stay at base 1"
        );
    }

    #[test]
    fn test_miner_pi_over_sorts_argument_raises_binder_uid() {
        // `unlock`-shape: a constant with a Type binder applied at a
        // Π-telescope over Type-sorted binders whose codomain is a bound
        // Rel referring to one of those binders (the bigop.big_nil shape).
        let input = r#"(CoqAxiom SerTop.consume (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Sort Prop)))
(CoqAxiom SerTop.use (App (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id consume)) ()) (Instance (() ())))) ((Prod ((binder_name (Name (Id R))) (binder_relevance Relevant)) (Sort (Type ((((hash 2) (data (Level ((DirPath ((Id SerTop))) 6)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (Rel 2))))))"#;
        let bases = mine(input);
        assert_eq!(
            bases.raised_base("SerTop/5"),
            Some(2),
            "a Π-over-Type argument must raise the consuming binder level, got {bases:?}"
        );
    }

    #[test]
    fn test_miner_self_cycle_poisons_fail_closed() {
        let input = format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_SELF_CYCLE}");
        let bases = mine(&input);
        assert!(
            bases.raised_base(EQ_UID).is_none(),
            "an unsatisfiable self-cycle must poison the uid back to base 1, got {bases:?}"
        );
    }

    #[test]
    fn test_miner_structural_pin_blocks_type_valued_inductive_levels() {
        // A Type-valued inductive shares its binder uid with a constant
        // (the measured `unlockable`/`unlock` sharing): the uid must be
        // pinned even though a Sort-argument constraint targets it.
        let input = r#"(CoqInductive SerTop.box 0 (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Sort (Type ((((hash 0) (data (Level ((DirPath ((Id mathverse_template_collapse))) 0)))) 0))))) (NumParams 1) (Ctor SerTop.Box (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id box)) ()) 0) (Instance (() ())))) ((Rel 2)))))))
(CoqAxiom SerTop.consume (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Sort Prop)))
(CoqAxiom SerTop.use (App (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id consume)) ()) (Instance (() ())))) ((Sort (Type ((((hash 2) (data (Level ((DirPath ((Id SerTop))) 6)))) 0))))))) "#;
        let bases = mine(input);
        assert!(
            bases.raised_base("SerTop/5").is_none(),
            "a uid mentioned by a Type-valued inductive must stay pinned at 1, got {bases:?}"
        );
    }

    #[test]
    fn test_miner_prop_inductive_levels_stay_raisable() {
        // eq's own arity mentions the uid, but eq is Prop-codomain —
        // impredicative, so the raise must stay live.
        let input = format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}");
        let bases = mine(&input);
        assert_eq!(bases.raised_base(EQ_UID), Some(2));
    }

    #[test]
    fn test_solve_cap_poisons_runaway_chain_and_pins_backward() {
        let mut miner = UniverseConstraintMiner::default();
        // a ≥ b+2, b ≥ c+2, c ≥ d+2, d ≥ 2 → a = 8 > cap → a poisons, and
        // the pin propagates BACKWARD through the whole chain (raising any
        // link would break the site that feeds the capped-out consumer).
        // An independent floor-raised uid is untouched.
        miner.edges.insert(("A/1".into(), "B/1".into(), 2));
        miner.edges.insert(("B/1".into(), "C/1".into(), 2));
        miner.edges.insert(("C/1".into(), "D/1".into(), 2));
        miner.floors.insert(("D/1".into(), 2));
        miner.floors.insert(("E/1".into(), 2));
        // Keep E in the graph via a slack (negative-offset) edge so the
        // backward pass exercises the off < 0 exemption.
        miner.edges.insert(("A/1".into(), "E/1".into(), -3));
        let bases = miner.solve();
        for uid in ["A/1", "B/1", "C/1", "D/1"] {
            assert!(
                bases.raised_base(uid).is_none(),
                "chain member {uid} must be pinned fail-closed, got {bases:?}"
            );
        }
        assert_eq!(
            bases.raised_base("E/1"),
            Some(2),
            "an independent floor raise (slack edge only) survives"
        );
    }

    /// An ALIAS value (`SerTop.myrefl := eq_refl`) declared at its own
    /// module level: the residual telescope is invariant, so the declared
    /// binder level must raise in LOCKSTEP with eq's.
    const RAW_ALIAS_OWN_LEVEL: &str = r#"(CoqConstant SerTop.myrefl (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 9) (data (Level ((DirPath ((Id SerTop))) 9)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1))))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))))"#;

    /// The same alias anchored at `Set`: `Set` cannot rise, so the whole
    /// equality chain (including eq's level) must pin.
    const RAW_ALIAS_SET_ANCHORED: &str = r#"(CoqConstant SerTop.myrefl_set (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort Set) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1))))) (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))))"#;

    /// A theorem whose declared TYPE binds `A` at eq's (raise-driven) uid
    /// while the VALUE's λ binds the SAME `A` at a fresh proof-side uid —
    /// the measured `Logic.f_equal2` statement/Qed-body split.
    const RAW_SPLIT_TELESCOPE: &str = r#"(CoqConstant SerTop.split_uid (Prod ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id Logic) (Id Init) (Id Coq))) 23503782208)))) 0)))) (Prod ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) (Instance (() ())))) ((Rel 2) (Rel 1) (Rel 1))))) (Lambda ((binder_name (Name (Id A))) (binder_relevance Relevant)) (Sort (Type ((((hash 2) (data (Level ((DirPath ((Id SerTop))) 11)))) 0)))) (Lambda ((binder_name (Name (Id x))) (binder_relevance Relevant)) (Rel 1) (App (Construct ((((MutInd (KerName (MPfile (DirPath ((Id Logic) (Id Init) (Id Coq)))) (Id eq)) ()) 0) 1) (Instance (() ())))) ((Rel 2) (Rel 1))))))"#;

    #[test]
    fn test_type_value_telescope_split_raises_in_lockstep() {
        let input =
            format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}\n{RAW_SPLIT_TELESCOPE}");
        let bases = mine(&input);
        assert_eq!(bases.raised_base(EQ_UID), Some(2), "driver raise live");
        assert_eq!(
            bases.raised_base("SerTop/11"),
            Some(2),
            "the proof-side λ-annotation level must raise in lockstep with \
             the statement's Π level, got {bases:?}"
        );
        // End-to-end: the split-telescope theorem must survive the raise.
        let report = verify_with_mining(&input);
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.split_uid".to_string()),
            "split-telescope decl must kernel-verify under the lockstep raise; \
             fallbacks: {:?}",
            report.axiom_fallback_names
        );
    }

    #[test]
    fn test_alias_value_raises_declared_level_in_lockstep() {
        let input =
            format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}\n{RAW_ALIAS_OWN_LEVEL}");
        let bases = mine(&input);
        assert_eq!(bases.raised_base(EQ_UID), Some(2), "eq raise stays live");
        assert_eq!(
            bases.raised_base("SerTop/9"),
            Some(2),
            "the alias's declared binder level must raise in lockstep, got {bases:?}"
        );
    }

    #[test]
    fn test_alias_set_anchored_pins_whole_chain() {
        let input = format!(
            "{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}\n{RAW_ALIAS_SET_ANCHORED}"
        );
        let bases = mine(&input);
        assert!(
            bases.raised_base(EQ_UID).is_none(),
            "a Set-anchored alias must pin the whole equality chain, got {bases:?}"
        );
    }

    #[test]
    fn test_e2e_type_level_refl_flips_to_kernel_verified() {
        let input = format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}");
        let report = verify_with_mining(&input);
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.type_level_refl".to_string()),
            "the re-leveled type-level reflexivity proof must kernel-verify; \
             fallbacks: {:?}, failures: {:?}",
            report.axiom_fallback_names,
            report.failures
        );
    }

    #[test]
    fn test_e2e_self_cycle_variant_stays_rejected_fail_closed() {
        // The same theorem plus an unsatisfiable use: the poison disables
        // the raise, so the theorem keeps today's honest rejection (a
        // deliberately-inconsistent assignment must never be rendered).
        let input =
            format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_TYPE_LEVEL_REFL}\n{RAW_SELF_CYCLE}");
        let report = verify_with_mining(&input);
        assert!(
            !report
                .kernel_verified_names
                .contains(&"SerTop.type_level_refl".to_string()),
            "with the raise poisoned the old rendering must persist (rejection), got KV"
        );
    }

    #[test]
    fn test_e2e_wrong_statement_stays_rejected_under_raise() {
        // Negative control (wrong-but-would-typecheck guard): the raise
        // fixes the SORTS, but a proof of `bool = nat` must still be
        // rejected by the kernel — re-leveling can never fabricate a proof.
        let input = format!("{RAW_EQ_IND}\n{RAW_BOOL_IND}\n{RAW_NAT_IND}\n{RAW_WRONG_STATEMENT}");
        let report = verify_with_mining(&input);
        assert!(
            !report
                .kernel_verified_names
                .contains(&"SerTop.type_level_wrong".to_string()),
            "a wrong type-level statement must stay rejected under the raise"
        );
        // And the raise itself must have been live (eq at base 2), so the
        // rejection above is exercised at the raised rendering.
        let bases = mine(&input);
        assert_eq!(bases.raised_base(EQ_UID), Some(2));
    }

    // ────────────────────────────────────────────────────────────────────
    // Structural-pin LOCKSTEP relaxation + poisoned-source EDGE DEGRADATION
    // (2026-07-16, the mathcomp `Equality.clone` class). Microcosm of the
    // measured corpus shape:
    //   * `SerTop.wrapped` — a Type-valued inductive whose arity codomain
    //     IS the module-wide uid `SerTop/5` (ssrfun's `wrapped`): the old
    //     wholesale structural pin froze `SerTop/5`; the relaxation mines
    //     lockstep edges instead.
    //   * `SerTop.strct` — a structure record with a MULTI-ARM arity
    //     (`Type@{max(S/6, S/6+1)}`, eqtype's `Equality.type`): stays
    //     wholesale-pinned (correctly).
    //   * `SerTop.pick` — a `phant_id`-shaped helper with binders at
    //     `SerTop/5`, applied AT `strct` by `SerTop.use_pick`: the mined
    //     edge `S/5 ≥ S/6 + 1` has a PINNED source, so it must DEGRADE to
    //     the floor `S/5 ≥ 2` instead of being dropped.
    // ────────────────────────────────────────────────────────────────────

    /// `Variant wrapped (T : Type@{SerTop/5}) : Type@{SerTop/5} := Wrap of T.`
    const RAW_WRAPPED_IND: &str = r#"(CoqInductive SerTop.wrapped 0 (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0))))) (NumParams 1) (Ctor SerTop.Wrap (Prod ((binder_name (Name (Id T))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Prod ((binder_name Anonymous) (binder_relevance Relevant)) (Rel 1) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id wrapped)) ()) 0) (Instance (() ())))) ((Rel 2)))))))"#;

    /// `Record strct : Type@{max(SerTop/6, SerTop/6+1)} := Pack { sort : Type@{SerTop/6} }.`
    const RAW_STRUCT_IND: &str = r#"(CoqInductive SerTop.strct 0 (Sort (Type ((((hash 2) (data (Level ((DirPath ((Id SerTop))) 6)))) 0) (((hash 3) (data (Level ((DirPath ((Id SerTop))) 6)))) 1)))) (NumParams 0) (Ctor SerTop.Pack (Prod ((binder_name (Name (Id sort))) (binder_relevance Relevant)) (Sort (Type ((((hash 2) (data (Level ((DirPath ((Id SerTop))) 6)))) 0)))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))))))"#;

    /// `Definition pick (T1 T2 : Type@{SerTop/5}) (v1 : T1) (v2 : T2) : T1 := v1.`
    const RAW_PICK: &str = r#"(CoqConstant SerTop.pick (Prod ((binder_name (Name (Id T1))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Prod ((binder_name (Name (Id T2))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Prod ((binder_name (Name (Id v1))) (binder_relevance Relevant)) (Rel 2) (Prod ((binder_name (Name (Id v2))) (binder_relevance Relevant)) (Rel 2) (Rel 4))))) (Lambda ((binder_name (Name (Id T1))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Lambda ((binder_name (Name (Id T2))) (binder_relevance Relevant)) (Sort (Type ((((hash 1) (data (Level ((DirPath ((Id SerTop))) 5)))) 0)))) (Lambda ((binder_name (Name (Id v1))) (binder_relevance Relevant)) (Rel 2) (Lambda ((binder_name (Name (Id v2))) (binder_relevance Relevant)) (Rel 2) (Rel 2))))))"#;

    /// `Definition use_pick (cT : strct) : strct := pick strct strct cT cT.`
    /// The `T1 := strct` argument lives at `Sort 2` (strct's multi-arm
    /// arity), one above `pick`'s collapsed `Type 1` binder — the
    /// `Equality.clone` failure shape.
    const RAW_USE_PICK: &str = r#"(CoqConstant SerTop.use_pick (Prod ((binder_name (Name (Id cT))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ()))))) (Lambda ((binder_name (Name (Id cT))) (binder_relevance Relevant)) (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))) (App (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id pick)) ()) (Instance (() ())))) ((Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))) (Rel 1) (Rel 1)))))"#;

    /// Negative control: same raised rendering, WRONG value — declared to
    /// return `strct` but picks from `wrapped strct` (a different head).
    /// The raise fixes sorts, never wrong proofs.
    const RAW_USE_PICK_WRONG: &str = r#"(CoqConstant SerTop.use_pick_wrong (Prod ((binder_name (Name (Id cT))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id wrapped)) ()) 0) (Instance (() ())))) ((Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))))) (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ()))))) (Lambda ((binder_name (Name (Id cT))) (binder_relevance Relevant)) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id wrapped)) ()) 0) (Instance (() ())))) ((Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))))) (App (Const ((Constant (KerName (MPfile (DirPath ((Id SerTop)))) (Id pick)) ()) (Instance (() ())))) ((App (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id wrapped)) ()) 0) (Instance (() ())))) ((Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))))) (App (Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id wrapped)) ()) 0) (Instance (() ())))) ((Ind (((MutInd (KerName (MPfile (DirPath ((Id SerTop)))) (Id strct)) ()) 0) (Instance (() ())))))) (Rel 1) (Rel 1)))))"#;

    #[test]
    fn test_lockstep_relaxation_unpins_single_arm_arity_family_uid() {
        // The wrapped family alone must not pin SerTop/5 anymore; the
        // degraded pinned-source edge must raise it to 2.
        let input = format!("{RAW_WRAPPED_IND}\n{RAW_STRUCT_IND}\n{RAW_PICK}\n{RAW_USE_PICK}");
        let bases = mine(&input);
        assert_eq!(
            bases.raised_base("SerTop/5"),
            Some(2),
            "the family uid must relax to lockstep and the pinned-source \
             edge must degrade to a floor `S/5 ≥ 2`, got {bases:?}"
        );
        assert!(
            bases.raised_base("SerTop/6").is_none(),
            "the multi-arm structure arity uid must stay wholesale-pinned, got {bases:?}"
        );
    }

    #[test]
    fn test_e2e_clone_shape_flips_to_kernel_verified() {
        // COMPUTE TEST: the full pipeline must kernel-verify the
        // `Equality.clone`-shaped declaration (helper applied AT the
        // structure type), the relaxed `wrapped` family, and the helper
        // itself, all at the raised rendering.
        let input = format!("{RAW_WRAPPED_IND}\n{RAW_STRUCT_IND}\n{RAW_PICK}\n{RAW_USE_PICK}");
        let report = verify_with_mining(&input);
        for name in ["SerTop.pick", "SerTop.use_pick"] {
            assert!(
                report.kernel_verified_names.contains(&name.to_string()),
                "{name} must kernel-verify under the degraded-floor raise; \
                 fallbacks: {:?}, failures: {:?}",
                report.axiom_fallback_names,
                report.failures
            );
        }
        assert!(
            report.failures.is_empty(),
            "the relaxed wrapped/strct families must still replay: {:?}",
            report.failures
        );
    }

    #[test]
    fn test_e2e_clone_shape_wrong_value_stays_rejected() {
        // NEGATIVE CONTROL: under the SAME raise, a wrong value (returns
        // `wrapped strct` where `strct` is declared) must stay rejected —
        // the relaxation can never launder a wrong proof into KV.
        let input = format!(
            "{RAW_WRAPPED_IND}\n{RAW_STRUCT_IND}\n{RAW_PICK}\n{RAW_USE_PICK}\n{RAW_USE_PICK_WRONG}"
        );
        let bases = mine(&input);
        assert_eq!(bases.raised_base("SerTop/5"), Some(2), "raise stays live");
        let report = verify_with_mining(&input);
        assert!(
            !report
                .kernel_verified_names
                .contains(&"SerTop.use_pick_wrong".to_string()),
            "a wrong value must stay rejected under the raise"
        );
        assert!(
            report
                .kernel_verified_names
                .contains(&"SerTop.use_pick".to_string()),
            "the correct clone-shaped sibling still verifies"
        );
    }

    #[test]
    fn test_lockstep_group_freezes_when_arity_uid_poisons() {
        // Fail-closed companion: when the (relaxed) arity uid poisons via
        // an unsatisfiable self-cycle, every lockstep member must freeze
        // back to base 1 even under an otherwise-live raising floor.
        let mut miner = UniverseConstraintMiner::default();
        miner.lockstep_groups.push((
            "ARITY/1".into(),
            ["MEMBER/1".to_string()].into_iter().collect(),
        ));
        // Poison the arity: immediate self-cycle.
        miner.edges.insert(("ARITY/1".into(), "ARITY/1".into(), 1));
        // A raise that would otherwise lift the member.
        miner.floors.insert(("MEMBER/1".into(), 2));
        // An independent uid with the same floor survives (isolation).
        miner.floors.insert(("OTHER/1".into(), 2));
        let bases = miner.solve();
        assert!(
            bases.raised_base("MEMBER/1").is_none(),
            "a lockstep member must freeze with its poisoned arity, got {bases:?}"
        );
        assert_eq!(
            bases.raised_base("OTHER/1"),
            Some(2),
            "an unrelated raise survives the freeze"
        );
    }

    #[test]
    fn test_degraded_edge_respects_cap_poisoning() {
        // A pinned-source edge with a huge offset degrades to a floor above
        // the cap: the target must poison fail-closed, not render raised.
        let mut miner = UniverseConstraintMiner::default();
        miner.pinned.insert("PINNED/1".into());
        miner
            .edges
            .insert(("TARGET/1".into(), "PINNED/1".into(), 40));
        let bases = miner.solve();
        assert!(
            bases.raised_base("TARGET/1").is_none(),
            "a degraded floor above the cap must poison the target, got {bases:?}"
        );
    }
}
