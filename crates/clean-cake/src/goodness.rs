// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof goodness — the trace-tree score, anchored at the bedrock 3 axioms.
//!
//! From the bedrock (`propext`, `Classical.choice`, `Quot.sound`) we walk a constant's
//! **transitive dependency closure** and aggregate two scores (see
//! `designs/2026-06-15-cake-semantic-identity-and-proof-goodness.md`):
//!
//! * **`g_mass` = Σ s(n)** over the deduplicated closure — cumulative derivation goodness
//!   ("sum the scores up the trace tree"). Richness/quality. Because it sums, it grows
//!   with proof size, so [`Goodness::normalized`] (`g_mass / closure_size`) is reported
//!   alongside it.
//! * **`floor` = min over the closure** — the **weakest link**. Soundness is an AND, not
//!   a sum: one `sorry` or domain axiom *anywhere* poisons the whole theorem. This is the
//!   honest trust label; `g_mass` is the quality signal. A headline claim needs the floor
//!   at [`FloorLevel::Foundational`] *and* a high `g_mass`.
//!
//! Deduplication is by kernel constant **name** here — the same registered lemma reused
//! N times is one node. Collapsing *differently-named but defeq* lemmas additionally is
//! the [`crate::identity`] refinement (semantic-identity dedup), layered on later.

use std::collections::{BTreeSet, VecDeque};

use clean_kernel::{is_foundational_axiom, is_trust_marker, ConstantKind, Environment, Name};

/// The soundness floor of a closure — its weakest link. Ordered worst → best so that
/// `min` over a closure yields the floor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloorLevel {
    /// A trust marker (`sorry` / `native_decide` / `sorryAx`) is reachable — unsound.
    Unsound,
    /// A non-foundational (domain-specific) axiom is reachable — sound only relative to
    /// that assumed axiom.
    AxiomDependent,
    /// Everything reachable is a foundational axiom or a kernel-checked declaration —
    /// the bedrock ceiling.
    Foundational,
}

/// Aggregated goodness of a constant's dependency closure.
#[derive(Debug, Clone)]
pub struct Goodness {
    /// Σ local scores over the deduplicated transitive closure. A **signed** score:
    /// kernel-checked declarations contribute positively (richness), but domain axioms
    /// (−5) and trust markers (−100) contribute negatively, so an axiom-/sorry-heavy
    /// closure can drive `g_mass` (and [`Goodness::normalized`]) negative. Read `g_mass`
    /// as "net derivation goodness", not pure positive richness; `floor` is the soundness
    /// label.
    pub g_mass: f64,
    /// The weakest link in the closure (soundness label).
    pub floor: FloorLevel,
    /// Number of distinct constants in the closure (incl. the root and axioms).
    pub closure_size: usize,
    /// Distinct non-foundational (domain) axioms the closure depends on.
    pub domain_axioms: Vec<String>,
    /// Distinct trust markers (`sorry`/`native_decide`/…) reachable — should be empty.
    pub trust_markers: Vec<String>,
}

impl Goodness {
    /// `g_mass / closure_size` — depth-of-clean-derivation, separated from sheer bulk.
    #[must_use]
    pub fn normalized(&self) -> f64 {
        if self.closure_size == 0 {
            0.0
        } else {
            self.g_mass / self.closure_size as f64
        }
    }

    /// Is the closure sound at the bedrock ceiling (no domain axioms, no trust markers)?
    #[must_use]
    pub fn is_foundational(&self) -> bool {
        self.floor == FloorLevel::Foundational
    }
}

/// Local goodness contribution + floor of a single closure node.
fn local_score(name: &Name, kind: ConstantKind, has_value: bool) -> (f64, FloorLevel) {
    if is_trust_marker(name) {
        return (-100.0, FloorLevel::Unsound);
    }
    if kind == ConstantKind::Axiom {
        if is_foundational_axiom(name) {
            // Bedrock: trusted, but not "work" — a small positive anchor.
            return (0.5, FloorLevel::Foundational);
        }
        // Domain-specific axiom: a real soundness debt.
        return (-5.0, FloorLevel::AxiomDependent);
    }
    // A kernel-checked declaration. Theorems are the substance; defs/opaque support.
    let base = match kind {
        ConstantKind::Theorem => 1.0,
        ConstantKind::Definition | ConstantKind::Opaque => 0.5,
        ConstantKind::Axiom => unreachable!("handled above"),
    };
    // A present value means there is content the kernel re-checked.
    let value_bonus = if has_value { 0.25 } else { 0.0 };
    (base + value_bonus, FloorLevel::Foundational)
}

/// Compute the [`Goodness`] of `root`'s transitive dependency closure in `env`.
/// Returns `None` if `root` is not in the environment.
#[must_use]
pub fn closure_goodness(env: &Environment, root: &Name) -> Option<Goodness> {
    env.get_const(root)?;

    let mut visited: BTreeSet<Name> = BTreeSet::new();
    let mut queue: VecDeque<Name> = VecDeque::new();
    queue.push_back(root.clone());
    visited.insert(root.clone());

    let mut g_mass = 0.0_f64;
    let mut floor = FloorLevel::Foundational;
    let mut domain_axioms: BTreeSet<String> = BTreeSet::new();
    let mut trust_markers: BTreeSet<String> = BTreeSet::new();
    // Reused per-node scratch for the constant collector (cleared each iteration).
    let mut refs: std::collections::HashSet<Name> = std::collections::HashSet::new();

    while let Some(name) = queue.pop_front() {
        let Some(info) = env.get_const(&name) else {
            // A referenced name absent from the env (e.g. a bare axiom token). Score it
            // structurally by name classification so the floor still reflects it.
            if is_trust_marker(&name) {
                trust_markers.insert(name.to_string());
                g_mass += -100.0;
                floor = floor.min(FloorLevel::Unsound);
            } else if !is_foundational_axiom(&name) {
                domain_axioms.insert(name.to_string());
                g_mass += -5.0;
                floor = floor.min(FloorLevel::AxiomDependent);
            } else {
                g_mass += 0.5;
            }
            continue;
        };

        let (s, node_floor) = local_score(&name, info.kind, info.value.is_some());
        g_mass += s;
        floor = floor.min(node_floor);
        match node_floor {
            FloorLevel::Unsound => {
                trust_markers.insert(name.to_string());
            }
            FloorLevel::AxiomDependent => {
                domain_axioms.insert(name.to_string());
            }
            FloorLevel::Foundational => {}
        }

        // Enqueue dependencies from the type and (if present) the value/proof term.
        // Use the kernel's EXHAUSTIVE collector: a hand-rolled `match` silently skips
        // `Squash`/`Cubical*`/`ZFC*` ExprKind variants, which would let a domain axiom
        // reachable only through such a subterm escape the floor — unsound. `collect_constants`
        // covers every variant and is the single source of truth for "what this term cites".
        // Reuse one scratch set across the BFS (cleared per node) instead of allocating
        // up to two fresh `HashSet`s per node.
        refs.clear();
        info.type_.collect_constants_into(&mut refs);
        if let Some(val) = info.value.as_ref() {
            val.collect_constants_into(&mut refs);
        }
        for r in refs.drain() {
            if visited.insert(r.clone()) {
                queue.push_back(r);
            }
        }
    }

    Some(Goodness {
        g_mass,
        floor,
        closure_size: visited.len(),
        domain_axioms: domain_axioms.into_iter().collect(),
        trust_markers: trust_markers.into_iter().collect(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Declaration, Expr, Level};

    // Build an env with: an axiom `A`, a definition `D := A`-typed, a theorem `T : D`.
    // (We exercise scoring + closure structure; the kernel's own checks live elsewhere.)
    fn name(s: &str) -> Name {
        Name::from_string(s)
    }

    #[test]
    fn test_floor_ordering_min_picks_weakest() {
        assert!(FloorLevel::Unsound < FloorLevel::AxiomDependent);
        assert!(FloorLevel::AxiomDependent < FloorLevel::Foundational);
        let min = [FloorLevel::Foundational, FloorLevel::AxiomDependent]
            .into_iter()
            .min()
            .unwrap();
        assert_eq!(min, FloorLevel::AxiomDependent);
    }

    #[test]
    fn test_local_score_classifies_bedrock_domain_and_unsound() {
        // Foundational axiom → small positive, Foundational floor.
        let (s, f) = local_score(&name("propext"), ConstantKind::Axiom, false);
        assert!(s > 0.0 && f == FloorLevel::Foundational);
        // A non-foundational axiom → penalty, AxiomDependent floor.
        let (s, f) = local_score(&name("MyDomain.bigAxiom"), ConstantKind::Axiom, false);
        assert!(s < 0.0 && f == FloorLevel::AxiomDependent);
        // A theorem → positive contribution, Foundational floor.
        let (s, f) = local_score(&name("MyThm"), ConstantKind::Theorem, true);
        assert!(s > 1.0 && f == FloorLevel::Foundational);
    }

    #[test]
    fn test_closure_goodness_walks_and_aggregates() {
        use clean_kernel::expr::BinderData;
        let mut env = Environment::default();
        // Foundational axiom propext : Prop (stand-in type; we only score structure).
        let prop = Expr::sort(Level::zero());
        env.add_decl(Declaration::Axiom {
            name: name("propext"),
            level_params: vec![],
            type_: prop,
        })
        .expect("add propext");
        // A domain axiom whose TYPE references propext: `T : propext → propext`. A Prop is
        // a valid Pi domain, so this type-checks, and the closure walk reaches propext.
        let t_type = Expr::pi(
            BinderData::default(),
            Expr::const_str("propext"),
            Expr::const_str("propext"),
        );
        env.add_decl(Declaration::Axiom {
            name: name("MyDomain.T"),
            level_params: vec![],
            type_: t_type,
        })
        .expect("add MyDomain.T");

        // Closure of T is {MyDomain.T, propext}: a domain axiom over the bedrock.
        let g = closure_goodness(&env, &name("MyDomain.T")).expect("T present");
        assert!(g.closure_size >= 2, "closure should reach propext");
        assert_eq!(g.floor, FloorLevel::AxiomDependent);
        assert!(g.domain_axioms.contains(&"MyDomain.T".to_string()));
        assert!(!g.is_foundational());

        // propext alone is at the bedrock ceiling.
        let gp = closure_goodness(&env, &name("propext")).expect("propext present");
        assert_eq!(gp.floor, FloorLevel::Foundational);
        assert!(gp.is_foundational());
        assert!(gp.domain_axioms.is_empty());

        // A missing root → None.
        assert!(closure_goodness(&env, &name("DoesNotExist")).is_none());
    }
}
