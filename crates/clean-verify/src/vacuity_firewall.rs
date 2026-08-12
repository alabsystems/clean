// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Vacuity firewall for generated execution relations (job **C2** of the
//! crystal program).
//!
//! ## What this guards against
//!
//! A refinement into a *vacuous* specification proves nothing. The concrete
//! failure mode this module exists to catch is a relation that claims to model
//! **what the code does** (layer 1 — an operation: look the name up, open the
//! binder, step the machine) while its constructor fields actually assert
//! **what typing means** (layer 2 — `Typing` / `has_type`). Such a relation is
//! not a model of an implementation: its introduction rules demand the very
//! judgment the refinement is supposed to establish, so building the relation
//! already requires proving the goal, and the relation contributes nothing.
//!
//! Two such arms are live in the tree today, and this module's tests pin both
//! as *expected findings* (see [`crate::vacuity_firewall`] tests and
//! `tests/vacuity_firewall.rs`):
//!
//! - `KernelInferAccepts.const` — its single field is
//!   `… → has_type (KExpr.const n us) T`. Denied at **depth 0**: the forbidden
//!   name is written in the constructor type itself.
//! - `KernelInferAccepts.lam` — its field is `LamInferWitness A body bt T`,
//!   which is *not* itself forbidden. `LamInferWitness.mk` carries
//!   `Typing A (KExpr.sort dl)` and `Typing body bt`. Denied at **depth 2**
//!   (arm → witness → witness constructor → `Typing`), and **only** if the
//!   walker follows the inductive→constructor edge.
//!
//! Running it found more than those two: four of the five arms breach, because
//! the `KernelStateLocalCtxWellFormed` guard is itself stated in layer-2 terms.
//! The measured table and its reading are in `tests/vacuity_firewall.rs`'s
//! `PINNED_FINDINGS`.
//!
//! ## Polarity — why plain reachability was not the right predicate (job C2b)
//!
//! The first run's finding set mixed two opposite things under one verdict, and
//! `designs/2026-07-29-vacuity-firewall-polarity.md` records the diagnosis.
//! Reaching a denied name says *where the name occurs*, not *which way the
//! implication runs*:
//!
//! - `KernelInferAccepts.const`'s only field **concludes**
//!   `has_type (KExpr.const n us) T`. The arm HANDS a typing judgment to
//!   whoever eliminates it, so `kernel_infer_inversion`'s `const` minor is the
//!   identity on that field. Genuine vacuity — [`Class::Strict`].
//! - `KernelInferAccepts.app`'s fourth field **concludes**
//!   `KernelInputAdmissible st Rf`, an operational fact; `Typing` is reachable
//!   only by descending into the *hypothesis* `KernelStateLocalCtxWellFormed st`,
//!   whose `cons` constructor legitimately demands `Typing ty (KExpr.sort u)` —
//!   a context is well-formed exactly when every declaration's domain is a sort.
//!   The arm DEMANDS that evidence rather than supplying it, which strengthens
//!   the hypothesis and is the safe direction — [`Class::PremiseOnly`].
//!
//! So the walker carries a [`Polarity`] alongside each reached name:
//!
//! ```text
//! Pi (x : A), B    A flips,  B keeps        <- the ONLY polarity-flipping form
//! constructor C    every field and the result type keep the ambient polarity
//! everything else  keeps
//! ```
//!
//! The constructor rule is the one a naive implementation gets wrong. A
//! constructor type is itself an arrow chain, so applying the `Pi` rule to it
//! would flip every field — and `KernelLocalCtxWellFormed.cons`, reached through
//! a hypothesis, would report its `Typing` field as *positive* and the false
//! positive would come straight back. The correct reading is that a constructor
//! occurrence is a **conjunction of its fields at the ambient polarity**:
//! demanding a `KernelLocalCtxWellFormed` demands its fields, supplying one
//! supplies them. Polarity flips again only inside a field, which is what makes
//! a hypothesis of a hypothesis positive.
//!
//! This is deliberately **not** an allowlist. `KernelLocalCtxWellFormed`
//! reaching `Typing` is legitimate in a hypothesis and would be a real defect in
//! a conclusion; a name-keyed exception cannot express that difference and would
//! suppress the genuine case along with the false one. Polarity is the property
//! that separates them, so polarity is computed.
//!
//! ## Why the existing machinery is not enough (the trap)
//!
//! [`clean_kernel::Environment::axiom_deps`] is a transitive walker, but it
//! follows only `type_` + `value` of each reached constant. When it reaches
//! the *name* `LamInferWitness` it looks at that inductive's own type
//! (`KExpr → KExpr → KExpr → KExpr → Type`) and stops — it never descends into
//! `LamInferWitness.mk`'s fields. Reusing it unchanged would report the `lam`
//! arm clean, missing exactly the nested-witness case this module exists to
//! catch. `SpecDefinition::dependencies` / `axiom_deps` are worse still: they
//! are hand-authored name-sets that nothing recomputes
//! (`dependencies_from_value` has zero callers).
//!
//! So the walker here adds **one edge** to the kernel's own closure algorithm:
//!
//! ```text
//! reached an inductive name I
//!   ==> enqueue every name in get_inductive(I).constructor_names
//!       (whose elaborated types the ordinary constant edge then scans)
//! ```
//!
//! [`FirewallConfig::follow_constructor_edge`] toggles that edge, so the test
//! suite can run the *naive* walker as a control and demonstrate that the edge
//! is load-bearing rather than decorative: with the edge off, the `lam` breach
//! disappears.
//!
//! ## The one edge that is deliberately CUT
//!
//! §5 clause 3 permits *operational* dependencies — "recursive executions,
//! lookups, state transitions". The audited relation's own recursive occurrences
//! are exactly that, and the walker never descends through them
//! ([`FirewallConfig::permitted_operational`], which always contains the
//! relation and its constructor names). This is not a softening: an execution
//! relation's arms nearly always mention the relation recursively, so following
//! that edge would expand every arm into every other arm and report every breach
//! against every constructor. Per-arm attribution — *which* arm is the vacuous
//! one — is the entire output of this walker, so the recursive edge has to go.
//!
//! ## Scope, stated honestly
//!
//! This is a **necessary** condition, not a sufficient one. There is no
//! complete decidable test for semantic non-triviality. What the walker
//! decides is exactly one clause of the §5 discipline of
//! `designs/2026-07-29-crystal-deployed-kernel-bridge.md`: *no transitive
//! dependency from a constructor field of the relation to a denied
//! layer-2 predicate, after alias unfolding and through nested witness types.*
//! The other clauses of that discipline (branch coverage against the source,
//! determinism, positive witnesses per arm, mutation testing, hash-binding to
//! the IR artifact) are separate obligations and are **not** checked here.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use clean_kernel::{Environment, Expr, ExprKind, Name};

use crate::spec::Specification;

/// Which side of an implication an occurrence sits on.
///
/// The property the original "any transitive reach" rule conflated. See the
/// module header and `designs/2026-07-29-vacuity-firewall-polarity.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Polarity {
    /// Conclusion side. The constructor **supplies** this to consumers, so a
    /// denied name here is content the refinement was supposed to establish.
    Positive,
    /// Hypothesis side. The constructor **demands** this from whoever builds
    /// it, so a denied name here strengthens the premise — the safe direction.
    Negative,
}

impl Polarity {
    /// Cross one `Pi` domain.
    #[must_use]
    pub fn flip(self) -> Self {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
        }
    }

    /// Lower-case word used in rendered findings.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Polarity::Positive => "positive",
            Polarity::Negative => "negative",
        }
    }
}

/// The verdict for one `(constructor, denied name)` pair, computed from the
/// polarities at which that name was reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Class {
    /// At least one **positive** reach: the constructor hands layer-2 content
    /// to consumers. Genuine vacuity. Fails the gate.
    Strict,
    /// Every reach is **negative**: the constructor demands layer-2 evidence.
    /// Recorded rather than failed — but recorded precisely because a
    /// premise-only path that later turns positive is how the defect re-enters.
    PremiseOnly,
}

impl Class {
    /// Upper-case tag used in rendered findings and pinned tables.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Class::Strict => "STRICT",
            Class::PremiseOnly => "PREMISE-ONLY",
        }
    }
}

/// Layer-2 predicate names an execution relation may never transitively reach
/// from a constructor field.
///
/// `Typing` is the inductive typing judgment; `has_type` is its reducible
/// alias (`has_type e T := Typing e T`), which is why both are listed — the
/// alias is what `KernelInferAccepts.const` actually names, and denying only
/// the head of the alias chain would let a rename slip past.
pub const DENIED_EXACT: &[&str] = &["Typing", "has_type"];

/// Denied name *prefixes*. `TypingCtx` covers `TypingCtx`, `TypingCtxConv`,
/// and any future context-typing sibling without needing a list edit.
pub const DENIED_PREFIX: &[&str] = &["TypingCtx"];

/// How the firewall walks, and what it denies.
///
/// [`FirewallConfig::default`] is the shipping configuration: the
/// inductive→constructor edge **on**, value unfolding **on**, the deny sets of
/// [`DENIED_EXACT`] / [`DENIED_PREFIX`], and an empty operational boundary.
#[derive(Debug, Clone)]
pub struct FirewallConfig {
    /// Names denied by exact match.
    pub denied_exact: BTreeSet<String>,
    /// Names denied when they start with one of these prefixes.
    pub denied_prefix: Vec<String>,
    /// Operational-boundary names: separately-modelled calls (the `ExecDefEq`
    /// shape of §5 clause 3) at which the walk stops instead of descending.
    ///
    /// Each entry maps to the name of the companion soundness theorem that
    /// discharges the boundary (e.g. `ExecDefEq → DefEq`). A boundary whose
    /// companion is **not registered in the spec env** is reported as
    /// [`FirewallReport::boundary_without_companion`] and makes the report
    /// dirty — an unproved boundary is a hole, not a permission.
    pub boundary: BTreeMap<String, String>,
    /// Names treated as **permitted operational dependencies** and never
    /// descended into. §5 clause 3 of the crystal doc permits exactly
    /// "recursive executions, lookups, state transitions".
    ///
    /// The audited relation itself is *always* in this set, added by
    /// [`audit_relation_with`]. That is not a convenience: an execution
    /// relation's arms almost always mention the relation recursively (a `lam`
    /// derivation contains a body derivation), so descending through the
    /// recursive occurrence would expand every arm into every *other* arm and
    /// every breach would be reported against every constructor. Per-arm
    /// attribution — which arm is the vacuous one — is the whole output of this
    /// walker, so the recursive edge has to be cut.
    ///
    /// Add mutual partners here when a relation is one of a mutually-recursive
    /// pair (`KernelInferAccepts` / `KernelCheckAccepts` package each other's
    /// acceptance), for the same reason.
    pub permitted_operational: BTreeSet<String>,
    /// Follow the inductive→constructor edge. **The load-bearing edge.**
    /// Setting this to `false` reproduces the naive `axiom_deps`-shaped walker
    /// and is used only as a control that proves the edge catches something.
    pub follow_constructor_edge: bool,
    /// Unfold valued constants through `ConstantInfo.value` (alias unfolding).
    pub follow_values: bool,
}

impl Default for FirewallConfig {
    fn default() -> Self {
        Self {
            denied_exact: DENIED_EXACT.iter().map(|s| (*s).to_string()).collect(),
            denied_prefix: DENIED_PREFIX.iter().map(|s| (*s).to_string()).collect(),
            boundary: BTreeMap::new(),
            permitted_operational: BTreeSet::new(),
            follow_constructor_edge: true,
            follow_values: true,
        }
    }
}

impl FirewallConfig {
    /// The naive control: identical deny sets, but without the
    /// inductive→constructor edge. Reproduces what reusing
    /// [`clean_kernel::Environment::axiom_deps`] unchanged would have seen.
    #[must_use]
    pub fn naive_control() -> Self {
        Self {
            follow_constructor_edge: false,
            ..Self::default()
        }
    }

    /// Add an operational boundary `name` discharged by `companion`.
    #[must_use]
    pub fn with_boundary(mut self, name: &str, companion: &str) -> Self {
        self.boundary
            .insert(name.to_string(), companion.to_string());
        self
    }

    /// Mark `name` a permitted operational dependency, never descended into.
    /// See [`FirewallConfig::permitted_operational`].
    #[must_use]
    pub fn with_permitted(mut self, name: &str) -> Self {
        self.permitted_operational.insert(name.to_string());
        self
    }

    fn is_denied(&self, name: &str) -> bool {
        self.denied_exact.contains(name) || self.denied_prefix.iter().any(|p| name.starts_with(p))
    }
}

/// One transitive reach from a constructor field to a denied predicate, at one
/// polarity.
///
/// The same `(ctor, denied)` pair can appear twice with different polarities
/// when the name is reachable both ways; [`FirewallReport::findings`] folds
/// those into one classified [`Finding`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Breach {
    /// The relation constructor whose field started the chain.
    pub ctor: String,
    /// The denied name that was reached.
    pub denied: String,
    /// Edge count from the constructor-type scan. `0` means the denied name is
    /// written directly in the constructor's own elaborated type.
    pub depth: usize,
    /// Whether this reach is on the conclusion side or the hypothesis side.
    pub polarity: Polarity,
    /// The witnessing chain, `ctor` first and `denied` last.
    pub path: Vec<String>,
}

impl Breach {
    /// One-line rendering used in test failure output and expected-finding
    /// tables.
    #[must_use]
    pub fn render(&self) -> String {
        format!(
            "{} reaches {} at depth {} in {} position via {}",
            self.ctor,
            self.denied,
            self.depth,
            self.polarity.label(),
            self.path.join(" -> ")
        )
    }
}

/// One `(constructor, denied name)` pair with its computed [`Class`].
///
/// This is the unit the gate ratchets on: the raw [`Breach`] list is the
/// evidence, a `Finding` is the verdict.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Finding {
    /// The relation constructor whose field started the chain.
    pub ctor: String,
    /// The denied name that was reached.
    pub denied: String,
    /// `Strict` iff some reach was positive.
    pub class: Class,
    /// Shortest depth among the reaches *of the classifying polarity* — the
    /// positive ones for `Strict`, the negative ones for `PremiseOnly`.
    pub depth: usize,
}

impl Finding {
    /// One-line rendering.
    #[must_use]
    pub fn render(&self) -> String {
        format!(
            "{} / {} = {} (depth {})",
            self.ctor,
            self.denied,
            self.class.label(),
            self.depth
        )
    }
}

/// The verdict for one relation.
#[derive(Debug, Clone)]
pub struct FirewallReport {
    /// The relation that was audited.
    pub relation: String,
    /// The constructor names whose elaborated types seeded the walk. Empty
    /// when `relation` is not an inductive (then the walk seeds from the
    /// constant's own type/value).
    pub roots: Vec<String>,
    /// How many distinct names the walk expanded — the coverage denominator.
    pub visited: usize,
    /// Every denied reach found, sorted by (ctor, depth, denied).
    pub breaches: Vec<Breach>,
    /// Boundary names reached whose companion soundness theorem is absent from
    /// the environment.
    pub boundary_without_companion: Vec<String>,
    /// Names referenced but absent from the environment. Diagnostic only: with
    /// a fully-built spec this should be empty, and a non-empty list means the
    /// walk could not see part of the closure.
    pub unresolved: Vec<String>,
}

impl FirewallReport {
    /// Fold the raw [`Breach`] list into one classified [`Finding`] per
    /// `(ctor, denied)` pair.
    ///
    /// A pair is [`Class::Strict`] iff **some** reach is positive: one route by
    /// which the constructor hands typing content to a consumer is enough, no
    /// matter how many hypothesis-side routes accompany it.
    #[must_use]
    pub fn findings(&self) -> Vec<Finding> {
        // (ctor, denied) -> (min positive depth, min negative depth)
        let mut folded: BTreeMap<(String, String), (Option<usize>, Option<usize>)> =
            BTreeMap::new();
        for b in &self.breaches {
            let slot = folded
                .entry((b.ctor.clone(), b.denied.clone()))
                .or_insert((None, None));
            let cell = match b.polarity {
                Polarity::Positive => &mut slot.0,
                Polarity::Negative => &mut slot.1,
            };
            *cell = Some(cell.map_or(b.depth, |d: usize| d.min(b.depth)));
        }
        folded
            .into_iter()
            .filter_map(|((ctor, denied), (pos, neg))| {
                let (class, depth) = match (pos, neg) {
                    (Some(d), _) => (Class::Strict, d),
                    (None, Some(d)) => (Class::PremiseOnly, d),
                    (None, None) => return None,
                };
                Some(Finding {
                    ctor,
                    denied,
                    class,
                    depth,
                })
            })
            .collect()
    }

    /// The findings that fail the gate: denied names in conclusion position.
    #[must_use]
    pub fn strict_findings(&self) -> Vec<Finding> {
        self.findings()
            .into_iter()
            .filter(|f| f.class == Class::Strict)
            .collect()
    }

    /// The findings that are recorded but do not fail: denied names reachable
    /// only through hypotheses.
    #[must_use]
    pub fn premise_only_findings(&self) -> Vec<Finding> {
        self.findings()
            .into_iter()
            .filter(|f| f.class == Class::PremiseOnly)
            .collect()
    }

    /// Is any denied name reachable in a positive position?
    #[must_use]
    pub fn has_strict_finding(&self) -> bool {
        self.breaches
            .iter()
            .any(|b| b.polarity == Polarity::Positive)
    }

    /// A relation passes iff no denied name is reachable **in a conclusion
    /// position**, every boundary is discharged, and the closure was fully
    /// resolvable.
    ///
    /// Premise-only reaches do not make a report dirty: they strengthen the
    /// constructor's hypotheses rather than supplying the goal. They are still
    /// carried in [`FirewallReport::breaches`] and surfaced by
    /// [`FirewallReport::premise_only_findings`] so a caller can ratchet on
    /// them — which the `KernelInferAccepts` gate does, because a premise-only
    /// path that turns positive is exactly how the defect re-enters.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        !self.has_strict_finding()
            && self.boundary_without_companion.is_empty()
            && self.unresolved.is_empty()
    }

    /// The stronger property: no denied name reachable at *any* polarity.
    ///
    /// Used where the expectation is zero layer-2 contact of any kind, so that
    /// a first premise-only reach is a deliberate decision rather than a silent
    /// drift.
    #[must_use]
    pub fn is_pristine(&self) -> bool {
        self.breaches.is_empty()
            && self.boundary_without_companion.is_empty()
            && self.unresolved.is_empty()
    }

    /// Multi-line rendering for test output.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = format!(
            "{}: {} constructor(s), {} name(s) visited, {} breach(es)",
            self.relation,
            self.roots.len(),
            self.visited,
            self.breaches.len()
        );
        for f in self.findings() {
            out.push_str("\n  FINDING ");
            out.push_str(&f.render());
        }
        for b in &self.breaches {
            out.push_str("\n  BREACH ");
            out.push_str(&b.render());
        }
        for b in &self.boundary_without_companion {
            out.push_str("\n  UNDISCHARGED BOUNDARY ");
            out.push_str(b);
        }
        for u in &self.unresolved {
            out.push_str("\n  UNRESOLVED ");
            out.push_str(u);
        }
        out
    }
}

/// Audit `relation` in the spec's live kernel environment with the shipping
/// configuration.
///
/// See [`audit_relation_with`] for the mechanics.
#[must_use]
pub fn audit_relation(spec: &Specification, relation: &str) -> FirewallReport {
    audit_relation_with(spec, relation, &FirewallConfig::default())
}

/// Audit `relation` under an explicit [`FirewallConfig`].
///
/// The walk is a breadth-first closure over `(name, polarity)` pairs, with
/// three edge kinds:
///
/// 1. constant → the constants of its elaborated `type_`, each tagged with the
///    polarity of its position (see [`constants_polarized`]);
/// 2. constant → the constants of its `value` (alias unfolding), when
///    [`FirewallConfig::follow_values`];
/// 3. **inductive → its constructor names**, when
///    [`FirewallConfig::follow_constructor_edge`]. A reached constructor's type
///    is scanned by [`constants_of_constructor`], which keeps every field at the
///    ambient polarity instead of flipping it — that is where nested witness
///    types such as `LamInferWitness.mk` expose their `Typing` fields, and where
///    `KernelLocalCtxWellFormed.cons` correctly keeps its `Typing` field on the
///    hypothesis side when the context predicate itself was a hypothesis.
///
/// Polarity is part of the visited key, so a name reachable both ways is
/// expanded both ways; the name *set* the walk reaches is unchanged from the
/// polarity-free version, only the labelling is new.
///
/// Seeding: if `relation` names an inductive, each of its constructors' types
/// is scanned at [`Polarity::Positive`] — a constructor supplies its fields to
/// whoever eliminates it — and the constants found there enter the queue at
/// depth 0, tagged with that constructor. Otherwise the constant's own
/// type/value seeds the queue under the pseudo-constructor `<self>`.
#[must_use]
pub fn audit_relation_with(
    spec: &Specification,
    relation: &str,
    cfg: &FirewallConfig,
) -> FirewallReport {
    let env = spec.env();
    let root = Name::from_string(relation);

    // The audited relation is always a permitted operational dependency: see
    // `FirewallConfig::permitted_operational` for why cutting the recursive edge
    // is required rather than convenient. Its own constructor NAMES are
    // permitted too, since the constructor-edge expansion would otherwise
    // re-enter the relation through them.
    let mut permitted: BTreeSet<String> = cfg.permitted_operational.clone();
    permitted.insert(relation.to_string());
    // Its constructors and its generated eliminators too: the constructor edge
    // would otherwise re-enter the relation through a constructor name, and a
    // recursor's type quantifies over every minor — i.e. over every other arm —
    // so reaching `<relation>.rec` from one arm would smear every other arm's
    // findings onto it.
    permitted.insert(format!("{relation}.rec"));
    permitted.insert(format!("{relation}.casesOn"));
    if let Some(ind) = env.get_inductive(&root) {
        for c in &ind.constructor_names {
            permitted.insert(c.to_string());
        }
    }

    let mut roots: Vec<String> = Vec::new();
    // A node is a name paired with the polarity it was reached at.
    type Node = (String, Polarity);
    // (node, depth, originating ctor)
    let mut queue: VecDeque<(Node, usize, String)> = VecDeque::new();
    // (ctor, node) -> parent node, for path reconstruction.
    let mut parent: BTreeMap<(String, Node), Option<Node>> = BTreeMap::new();
    let mut seen: BTreeSet<(String, Node)> = BTreeSet::new();

    let seed = |queue: &mut VecDeque<(Node, usize, String)>,
                parent: &mut BTreeMap<(String, Node), Option<Node>>,
                seen: &mut BTreeSet<(String, Node)>,
                ctor: &str,
                names: BTreeSet<Node>| {
        for node in names {
            if permitted.contains(&node.0) {
                continue;
            }
            if seen.insert((ctor.to_string(), node.clone())) {
                parent.insert((ctor.to_string(), node.clone()), None);
                queue.push_back((node, 0usize, ctor.to_string()));
            }
        }
    };

    if let Some(ind) = env.get_inductive(&root) {
        for ctor_name in &ind.constructor_names {
            let ctor = ctor_name.to_string();
            roots.push(ctor.clone());
            let Some(ctor_info) = env.get_constructor(ctor_name) else {
                continue;
            };
            // A constructor of the audited relation supplies its fields to
            // whoever eliminates it, so the whole telescope starts positive.
            seed(
                &mut queue,
                &mut parent,
                &mut seen,
                &ctor,
                constants_of_constructor(&ctor_info.type_, Polarity::Positive),
            );
        }
    } else if let Some(info) = env.get_const(&root) {
        let ctor = "<self>".to_string();
        let mut names = constants_polarized(&info.type_, Polarity::Positive);
        if cfg.follow_values {
            if let Some(v) = info.value.as_ref() {
                names.extend(constants_polarized(v, Polarity::Positive));
            }
        }
        seed(&mut queue, &mut parent, &mut seen, &ctor, names);
    } else {
        return FirewallReport {
            relation: relation.to_string(),
            roots,
            visited: 0,
            breaches: Vec::new(),
            boundary_without_companion: Vec::new(),
            unresolved: vec![relation.to_string()],
        };
    }

    let mut breaches: Vec<Breach> = Vec::new();
    let mut undischarged: BTreeSet<String> = BTreeSet::new();
    let mut unresolved: BTreeSet<String> = BTreeSet::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();

    while let Some((node, depth, ctor)) = queue.pop_front() {
        let (name, pol) = node.clone();
        visited.insert(name.clone());

        if cfg.is_denied(&name) {
            breaches.push(Breach {
                ctor: ctor.clone(),
                denied: name.clone(),
                depth,
                polarity: pol,
                path: reconstruct_path(&parent, &ctor, &node),
            });
            // Do not descend past a denied name: the breach is already
            // reported and everything below it is noise.
            continue;
        }

        if let Some(companion) = cfg.boundary.get(&name) {
            if env.get_const(&Name::from_string(companion)).is_none() {
                undischarged.insert(format!("{name} (companion {companion} not registered)"));
            }
            // Boundary reached: stop descending either way. An undischarged
            // boundary is already recorded as a finding.
            continue;
        }

        let kname = Name::from_string(&name);
        let mut next: BTreeSet<Node> = BTreeSet::new();
        let mut resolved = false;

        if let Some(ctor_info) = env.get_constructor(&kname) {
            // A constructor occurrence is a conjunction of its fields at the
            // AMBIENT polarity. Flipping here (as the generic `Pi` rule would)
            // is the mistake that turns every hypothesis-side witness into a
            // false positive — see the module header.
            resolved = true;
            next.extend(constants_of_constructor(&ctor_info.type_, pol));
        } else if let Some(info) = env.get_const(&kname) {
            resolved = true;
            next.extend(constants_polarized(&info.type_, pol));
            if cfg.follow_values {
                if let Some(v) = info.value.as_ref() {
                    next.extend(constants_polarized(v, pol));
                }
            }
        }

        if cfg.follow_constructor_edge {
            if let Some(ind) = env.get_inductive(&kname) {
                resolved = true;
                for c in &ind.constructor_names {
                    // The constructor name inherits the inductive's polarity;
                    // its fields are then read at that polarity above.
                    next.insert((c.to_string(), pol));
                }
            }
        } else if env.get_inductive(&kname).is_some() {
            resolved = true;
        }

        if !resolved {
            unresolved.insert(name.clone());
            continue;
        }

        for n in next {
            if n == node || permitted.contains(&n.0) {
                continue;
            }
            if seen.insert((ctor.clone(), n.clone())) {
                parent.insert((ctor.clone(), n.clone()), Some(node.clone()));
                queue.push_back((n, depth + 1, ctor.clone()));
            }
        }
    }

    breaches.sort_by(|a, b| {
        (&a.ctor, a.depth, &a.denied, a.polarity)
            .cmp(&(&b.ctor, b.depth, &b.denied, b.polarity))
            .then_with(|| a.path.cmp(&b.path))
    });
    breaches.dedup();

    FirewallReport {
        relation: relation.to_string(),
        roots,
        visited: visited.len(),
        breaches,
        boundary_without_companion: undischarged.into_iter().collect(),
        unresolved: unresolved.into_iter().collect(),
    }
}

/// Every relation the firewall is expected to pass, audited in one call.
///
/// Missing relations come back as reports with a single `unresolved` entry, so
/// a caller that pins a name which has not yet been registered fails closed
/// rather than silently auditing nothing.
#[must_use]
pub fn audit_all(spec: &Specification, relations: &[&str]) -> Vec<FirewallReport> {
    relations.iter().map(|r| audit_relation(spec, r)).collect()
}

/// Every constant in `e`, each tagged with the polarity of its position, given
/// that `e` as a whole sits at polarity `start`.
///
/// The rule set is deliberately small, and every choice in it is a choice about
/// which direction an error goes:
///
/// - **`Pi (x : A), B` is the only flipping form.** `A` is what a term of this
///   type demands, `B` is what it delivers. This is the arrow polarity the
///   design calls for, and it is what makes a hypothesis of a hypothesis
///   positive again — nesting two `Pi` domains flips twice.
/// - **`Lam`, `App`, `Let`, `Proj`, `MData` keep the polarity.** A lambda is a
///   function *value*, not an implication; its binder domain is an ascription,
///   not an antecedent. Treating it as an antecedent would flip a positive
///   occurrence to negative and *hide* a genuine breach, so the conservative
///   reading keeps it.
/// - **Anything else falls back to `collect_constants` at `start`.** The exotic
///   `ExprKind` families (cubical, ZFC, `Squash`) are unused by this spec, but a
///   silent `_ => {}` arm would be a hole in a firewall: a name that stops being
///   *seen* looks exactly like a name that is clean. Collecting them all at the
///   ambient polarity keeps them visible and, again, errs toward reporting.
///
/// **Known approximation.** Polarity is not propagated through *applied*
/// aliases: reaching `Not` and unfolding `fun A => A → False` cannot flip the
/// argument, because the argument is a bound variable at that point, not a
/// constant. The effect is that such an occurrence keeps the ambient polarity
/// instead of flipping — again the reporting direction, never the silent one.
///
/// Iterative rather than recursive: spec constructor types nest deeply enough
/// that a recursive walker is a stack-overflow risk in a test binary.
#[must_use]
pub fn constants_polarized(e: &Expr, start: Polarity) -> BTreeSet<(String, Polarity)> {
    let mut out: BTreeSet<(String, Polarity)> = BTreeSet::new();
    let mut stack: Vec<(&Expr, Polarity)> = vec![(e, start)];
    while let Some((cur, p)) = stack.pop() {
        match cur.kind() {
            ExprKind::Const(name, _) => {
                out.insert((name.to_string(), p));
            }
            ExprKind::App(f, a) => {
                stack.push((f, p));
                stack.push((a, p));
            }
            ExprKind::Pi(_, dom, body) => {
                stack.push((dom, p.flip()));
                stack.push((body, p));
            }
            ExprKind::Lam(_, dom, body) => {
                stack.push((dom, p));
                stack.push((body, p));
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push((ty, p));
                stack.push((val, p));
                stack.push((body, p));
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push((inner, p)),
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Lit(_)
            | ExprKind::SProp => {}
            _ => {
                // Fail loud, not silent: everything this walker does not model
                // structurally is still collected, at the ambient polarity.
                for n in cur.collect_constants() {
                    out.insert((n.to_string(), p));
                }
            }
        }
    }
    out
}

/// Every constant in a **constructor type**, tagged with polarity, given that
/// the constructor occurrence itself sits at `ambient`.
///
/// A constructor type is `Π (p₁ : A₁) … (pₙ : Aₙ), I args`, and the generic
/// `Pi` rule is **wrong** for it. A constructor occurrence is a conjunction of
/// its fields: to supply an `I` you must supply every field, and to demand an
/// `I` is to demand every field. So the telescope is peeled and each domain —
/// and the result type — is read at `ambient`, with
/// [`constants_polarized`] applying the ordinary arrow rule *inside* each field.
///
/// This is precisely the distinction the first firewall run got wrong.
/// `KernelInferAccepts.app`'s hypothesis `KernelStateLocalCtxWellFormed st`
/// unfolds to `KernelLocalCtxWellFormed env ctx`, whose `cons` field
/// `Typing ty (KExpr.sort u)` must stay **negative**: the arm demands a
/// well-formed context, it does not hand one out. Flipping at the constructor
/// telescope would have reported it positive and reinstated the false positive.
#[must_use]
pub fn constants_of_constructor(ty: &Expr, ambient: Polarity) -> BTreeSet<(String, Polarity)> {
    let mut out: BTreeSet<(String, Polarity)> = BTreeSet::new();
    let mut cur = ty;
    loop {
        match cur.kind() {
            ExprKind::Pi(_, dom, body) => {
                out.extend(constants_polarized(dom, ambient));
                cur = body;
            }
            ExprKind::MData(_, inner) => cur = inner,
            _ => {
                // The result type `I args`: the indices are as much a part of
                // what the constructor produces as the fields are.
                out.extend(constants_polarized(cur, ambient));
                break;
            }
        }
    }
    out
}

fn reconstruct_path(
    parent: &BTreeMap<(String, (String, Polarity)), Option<(String, Polarity)>>,
    ctor: &str,
    node: &(String, Polarity),
) -> Vec<String> {
    let mut chain = vec![node.0.clone()];
    let mut cur = node.clone();
    // The parent map is acyclic by construction (each key is inserted once,
    // at first discovery), but bound the walk anyway so a future edit that
    // breaks that invariant cannot hang a test.
    for _ in 0..1024 {
        match parent.get(&(ctor.to_string(), cur.clone())) {
            Some(Some(p)) => {
                chain.push(p.0.clone());
                cur = p.clone();
            }
            _ => break,
        }
    }
    chain.push(ctor.to_string());
    chain.reverse();
    chain
}

/// Every inductive in the spec env whose name starts with one of `prefixes`,
/// sorted.
///
/// This is how the firewall's callers stay honest about *newly registered*
/// relations without an edit per relation: a test that audits everything named
/// `ImplInfer*` covers job C1's relation the moment it lands, and cannot be
/// left behind by a rename. Discovery is the right default — a hardcoded list is
/// a list that goes stale silently.
#[must_use]
pub fn discover_relations(spec: &Specification, prefixes: &[&str]) -> Vec<String> {
    let mut found: BTreeSet<String> = BTreeSet::new();
    for ind in spec.env().inductives() {
        let name = ind.name.to_string();
        if prefixes.iter().any(|p| name.starts_with(p)) {
            found.insert(name);
        }
    }
    found.into_iter().collect()
}

/// Does `env` know this name at all (as a constant or an inductive)?
///
/// Exposed so callers pinning an expected-findings table can assert the arms
/// they name still exist rather than passing because a rename made them
/// invisible.
#[must_use]
pub fn env_knows(env: &Environment, name: &str) -> bool {
    let n = Name::from_string(name);
    env.get_const(&n).is_some() || env.get_inductive(&n).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::build_eval_ir_spec_with_stack;
    use clean_kernel::BinderInfo;

    // These lib-suite tests all use the EvalIR bundle: it is two stages, builds
    // in seconds, and contains genuinely recursive families to walk. The richer
    // `ImplementationSoundness` bundle would let them assert against
    // `KernelInferAccepts` directly, but it cannot build at HEAD — see the
    // header of `tests/vacuity_firewall.rs` for the exact stage-table
    // inconsistency — so the `KernelInferAccepts` assertions live in that
    // integration test against the full spec instead.

    /// The deny predicate is the whole instrument; test it directly rather than
    /// only through a spec audit, where a bug in it would look like a clean
    /// report.
    #[test]
    fn test_deny_matching_covers_exact_and_prefix() {
        let cfg = FirewallConfig::default();
        assert!(cfg.is_denied("Typing"));
        assert!(cfg.is_denied("has_type"));
        assert!(cfg.is_denied("TypingCtx"));
        assert!(cfg.is_denied("TypingCtxConv"));
        // Near-misses must NOT be denied: over-denial would make every audit
        // fail and the firewall would be discarded as noise.
        assert!(!cfg.is_denied("TypeChecker"));
        assert!(!cfg.is_denied("KernelInfers"));
        assert!(!cfg.is_denied("has_typeX"));
        assert!(!cfg.is_denied("MyTyping"));
    }

    /// The control differs from the shipping config in exactly one field, so
    /// any difference in results is attributable to the edge alone.
    #[test]
    fn test_naive_control_differs_only_in_the_edge() {
        let full = FirewallConfig::default();
        let naive = FirewallConfig::naive_control();
        assert!(full.follow_constructor_edge);
        assert!(!naive.follow_constructor_edge);
        assert_eq!(full.denied_exact, naive.denied_exact);
        assert_eq!(full.denied_prefix, naive.denied_prefix);
        assert_eq!(full.boundary, naive.boundary);
        assert_eq!(full.permitted_operational, naive.permitted_operational);
        assert_eq!(full.follow_values, naive.follow_values);
    }

    /// Cutting a name as a permitted operational dependency shrinks the walk.
    ///
    /// `IRNode.mk : IRInst -> IRList Nat -> IRNode`, so an `IRNode` audit reaches
    /// `IRInst` at depth 0 and then everything `IRInst` mentions. Permitting
    /// `IRInst` must therefore reduce what is reached — the same mechanism that
    /// cuts a relation's own recursive occurrences, tested where its effect is
    /// measurable.
    #[test]
    fn test_permitted_operational_cuts_the_walk() {
        let spec = build_eval_ir_spec_with_stack();
        let wide = audit_relation(&spec, "IRNode");
        let cut = audit_relation_with(
            &spec,
            "IRNode",
            &FirewallConfig::default().with_permitted("IRInst"),
        );

        assert!(
            cut.visited < wide.visited,
            "permitting IRInst must reduce what an IRNode audit reaches. wide={}, cut={}",
            wide.visited,
            cut.visited
        );
        assert!(
            wide.is_clean() && cut.is_clean(),
            "both must still pass:\n{}\n{}",
            wide.render(),
            cut.render()
        );
    }

    /// An operational boundary whose companion soundness theorem is not
    /// registered must make the report dirty. An undischarged boundary is a
    /// hole, not a permission.
    ///
    /// `IRMachine.mk : IRList IRFrame -> ... -> IRMachine`, so auditing
    /// `IRMachine` reaches `IRFrame` at depth 0 — a boundary genuinely
    /// encountered, which is what makes this a test of the boundary logic rather
    /// than of an unreached branch.
    #[test]
    fn test_undischarged_boundary_makes_the_report_dirty() {
        let spec = build_eval_ir_spec_with_stack();
        let cfg =
            FirewallConfig::default().with_boundary("IRFrame", "no_such_soundness_theorem_exists");
        let report = audit_relation_with(&spec, "IRMachine", &cfg);
        assert!(
            !report.boundary_without_companion.is_empty(),
            "a boundary whose companion is absent must be reported: {}",
            report.render()
        );
        assert!(!report.is_clean(), "and must make the report dirty");
    }

    /// The same boundary with a companion that IS registered is accepted, and the
    /// walk stops there instead of descending.
    #[test]
    fn test_discharged_boundary_is_accepted() {
        let spec = build_eval_ir_spec_with_stack();
        // `ir_eval` is a real registered constant, standing in for a companion
        // soundness theorem.
        let cfg = FirewallConfig::default().with_boundary("IRFrame", "ir_eval");
        let report = audit_relation_with(&spec, "IRMachine", &cfg);
        assert!(
            report.boundary_without_companion.is_empty(),
            "a boundary with a registered companion must not be flagged: {}",
            report.render()
        );
        assert!(report.is_clean(), "{}", report.render());
        assert!(
            report.visited < audit_relation(&spec, "IRMachine").visited,
            "a discharged boundary stops the walk, so fewer names are reached than without it"
        );
    }

    /// A breach renders its whole chain, because "X is vacuous" is not a useful
    /// finding without the route — and its polarity, because that is the
    /// difference between a defect and a strengthened hypothesis.
    #[test]
    fn test_breach_render_shows_the_chain() {
        let b = Breach {
            ctor: "R.lam".to_string(),
            denied: "Typing".to_string(),
            depth: 1,
            polarity: Polarity::Positive,
            path: vec![
                "R.lam".to_string(),
                "LamInferWitness".to_string(),
                "LamInferWitness.mk".to_string(),
                "Typing".to_string(),
            ],
        };
        let rendered = b.render();
        assert!(rendered.contains("R.lam reaches Typing at depth 1"));
        assert!(rendered.contains("positive position"));
        assert!(rendered.contains("LamInferWitness.mk -> Typing"));
    }

    // ── Polarity, tested directly ────────────────────────────────────────────
    //
    // Polarity is now the load-bearing property of this module, so it is tested
    // on synthetic expressions where the expected answer is unarguable, not only
    // through a spec audit where a bug in it would look like a reclassification.

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), Vec::new())
    }

    fn polarities_of(e: &Expr, start: Polarity) -> BTreeMap<String, BTreeSet<Polarity>> {
        let mut m: BTreeMap<String, BTreeSet<Polarity>> = BTreeMap::new();
        for (n, p) in constants_polarized(e, start) {
            m.entry(n).or_default().insert(p);
        }
        m
    }

    /// `A -> B` from a positive start: the hypothesis is negative, the
    /// conclusion positive. The base case the whole refinement rests on.
    #[test]
    fn test_polarity_arrow_splits_hypothesis_from_conclusion() {
        let e = Expr::arrow(c("A"), c("B"));
        let m = polarities_of(&e, Polarity::Positive);
        assert_eq!(m["A"], BTreeSet::from([Polarity::Negative]));
        assert_eq!(m["B"], BTreeSet::from([Polarity::Positive]));
    }

    /// `(A -> B) -> C`: polarity FLIPS AGAIN inside a negative position, so `A`
    /// — a hypothesis of a hypothesis — is positive.
    ///
    /// This is the clause a naive implementation gets wrong (it usually stops at
    /// "top-level arrow domains are negative"), and getting it wrong here would
    /// silently downgrade a genuine breach to premise-only.
    #[test]
    fn test_polarity_flips_again_inside_a_negative_position() {
        let e = Expr::arrow(Expr::arrow(c("A"), c("B")), c("C"));
        let m = polarities_of(&e, Polarity::Positive);
        assert_eq!(
            m["A"],
            BTreeSet::from([Polarity::Positive]),
            "a hypothesis of a hypothesis is positive"
        );
        assert_eq!(m["B"], BTreeSet::from([Polarity::Negative]));
        assert_eq!(m["C"], BTreeSet::from([Polarity::Positive]));
    }

    /// Starting negative mirrors everything: the same term read as a hypothesis
    /// has every polarity inverted.
    #[test]
    fn test_polarity_start_negative_mirrors_the_whole_term() {
        let e = Expr::arrow(Expr::arrow(c("A"), c("B")), c("C"));
        let m = polarities_of(&e, Polarity::Negative);
        assert_eq!(m["A"], BTreeSet::from([Polarity::Negative]));
        assert_eq!(m["B"], BTreeSet::from([Polarity::Positive]));
        assert_eq!(m["C"], BTreeSet::from([Polarity::Negative]));
    }

    /// One name occurring on both sides is reported at both polarities — the
    /// fold to a `Finding` is what decides, and it decides `Strict`.
    #[test]
    fn test_polarity_records_both_sides_of_the_same_name() {
        let e = Expr::arrow(c("A"), c("A"));
        let m = polarities_of(&e, Polarity::Positive);
        assert_eq!(
            m["A"],
            BTreeSet::from([Polarity::Positive, Polarity::Negative])
        );
    }

    /// A lambda does NOT flip: it is a function value, not an implication.
    /// Flipping there would turn a positive occurrence negative and hide a
    /// breach — the one direction this walker must never err in.
    #[test]
    fn test_polarity_lambda_does_not_flip() {
        let e = Expr::lam(BinderInfo::Default, c("A"), c("B"));
        let m = polarities_of(&e, Polarity::Positive);
        assert_eq!(m["A"], BTreeSet::from([Polarity::Positive]));
        assert_eq!(m["B"], BTreeSet::from([Polarity::Positive]));
    }

    /// A CONSTRUCTOR telescope does not flip its fields — they are a
    /// conjunction, read at the constructor's own polarity.
    ///
    /// `mk : A -> B -> I` reached as a hypothesis keeps `A` and `B` negative.
    /// Applying the generic `Pi` rule instead would report them positive, which
    /// is exactly the false positive C2b exists to remove: it is how
    /// `KernelLocalCtxWellFormed.cons`'s legitimate `Typing` field looked like a
    /// supplied typing judgment.
    #[test]
    fn test_constructor_telescope_keeps_fields_at_the_ambient_polarity() {
        let ctor_ty = Expr::arrow(c("A"), Expr::arrow(c("B"), c("I")));

        let neg = {
            let mut m: BTreeMap<String, BTreeSet<Polarity>> = BTreeMap::new();
            for (n, p) in constants_of_constructor(&ctor_ty, Polarity::Negative) {
                m.entry(n).or_default().insert(p);
            }
            m
        };
        assert_eq!(neg["A"], BTreeSet::from([Polarity::Negative]));
        assert_eq!(neg["B"], BTreeSet::from([Polarity::Negative]));
        assert_eq!(neg["I"], BTreeSet::from([Polarity::Negative]));

        // And the contrast: the generic rule would have flipped the fields.
        let generic = polarities_of(&ctor_ty, Polarity::Negative);
        assert_eq!(
            generic["A"],
            BTreeSet::from([Polarity::Positive]),
            "the generic Pi rule flips A; the constructor rule must not"
        );
    }

    /// A field that is itself an arrow still splits INSIDE the field: the
    /// constructor rule suppresses the flip only at the telescope, not below it.
    #[test]
    fn test_constructor_fields_still_split_internally() {
        // mk : (H -> Con) -> I
        let ctor_ty = Expr::arrow(Expr::arrow(c("H"), c("Con")), c("I"));
        let mut m: BTreeMap<String, BTreeSet<Polarity>> = BTreeMap::new();
        for (n, p) in constants_of_constructor(&ctor_ty, Polarity::Positive) {
            m.entry(n).or_default().insert(p);
        }
        assert_eq!(
            m["Con"],
            BTreeSet::from([Polarity::Positive]),
            "the field's conclusion is what the constructor supplies"
        );
        assert_eq!(
            m["H"],
            BTreeSet::from([Polarity::Negative]),
            "the field's own hypothesis is demanded, not supplied"
        );
    }

    /// The fold: one positive reach makes the pair `Strict` however many
    /// negative reaches accompany it, and the recorded depth is the shortest
    /// reach of the CLASSIFYING polarity.
    #[test]
    fn test_findings_fold_positive_wins_and_depth_follows_the_class() {
        let mk = |depth, polarity| Breach {
            ctor: "R.a".to_string(),
            denied: "Typing".to_string(),
            depth,
            polarity,
            path: vec!["R.a".to_string(), "Typing".to_string()],
        };
        let report = FirewallReport {
            relation: "R".to_string(),
            roots: vec!["R.a".to_string()],
            visited: 1,
            breaches: vec![
                mk(1, Polarity::Negative),
                mk(4, Polarity::Positive),
                mk(9, Polarity::Positive),
            ],
            boundary_without_companion: Vec::new(),
            unresolved: Vec::new(),
        };
        let findings = report.findings();
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].class, Class::Strict);
        assert_eq!(
            findings[0].depth, 4,
            "depth must come from the positive reaches, not the shorter negative one"
        );
        assert!(!report.is_clean(), "a strict finding is not clean");
        assert!(!report.is_pristine());
    }

    /// A report with only negative reaches is clean but not pristine — the
    /// premise-only class, expressed in the two predicates the gate uses.
    #[test]
    fn test_premise_only_report_is_clean_but_not_pristine() {
        let report = FirewallReport {
            relation: "R".to_string(),
            roots: vec!["R.a".to_string()],
            visited: 1,
            breaches: vec![Breach {
                ctor: "R.a".to_string(),
                denied: "Typing".to_string(),
                depth: 3,
                polarity: Polarity::Negative,
                path: vec!["R.a".to_string(), "Typing".to_string()],
            }],
            boundary_without_companion: Vec::new(),
            unresolved: Vec::new(),
        };
        assert_eq!(report.findings()[0].class, Class::PremiseOnly);
        assert!(
            report.is_clean(),
            "demanding typing evidence is not vacuity"
        );
        assert!(
            !report.is_pristine(),
            "but it is still layer-2 contact and must stay visible"
        );
        assert_eq!(report.strict_findings().len(), 0);
        assert_eq!(report.premise_only_findings().len(), 1);
    }

    /// The lib-suite audit: the EvalIR families (job C3) clear the firewall.
    ///
    /// This lives in the lib suite rather than only in `tests/` because the
    /// EvalIR bundle is two stages and cheap, so there is no reason for the
    /// default `cargo test --lib -p clean-verify` run not to include a real
    /// audit of a real relation set.
    #[test]
    fn test_eval_ir_families_pass_the_firewall() {
        let spec = build_eval_ir_spec_with_stack();
        let families = discover_relations(&spec, &["IR"]);
        assert!(
            families.len() >= 20,
            "expected the EvalIR family set to be discovered; found {}: {families:?}",
            families.len()
        );

        let mut dirty = Vec::new();
        for f in &families {
            let report = audit_relation(&spec, f);
            // `is_pristine`, not `is_clean`: these families are expected to have
            // no layer-2 contact at all, so the first premise-only reach must
            // surface here rather than be absorbed by the polarity refinement.
            if !report.is_pristine() {
                dirty.push(report.render());
            }
        }
        assert!(
            dirty.is_empty(),
            "the vacuity firewall rejected {} EvalIR family/families:\n{}",
            dirty.len(),
            dirty.join("\n")
        );
    }
}
