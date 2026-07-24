// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sorry dependency tracer: prioritizes which sorry/axiom obligations to fill.
//!
//! tMIR's #1 question when using clean is: "if I fix this sorry, does it help?"
//! This module answers that by tracing axiom/sorry dependencies so users can
//! prioritize which sorry obligations to fill first.
//!
//! # Key APIs
//!
//! - [`SorryTracer::build`] — scans all declarations, builds forward + reverse dependency graph
//! - [`SorryTracer::trace_deps`] — given a declaration, returns all sorry axioms it depends on
//! - [`SorryTracer::impact`] — given a sorry axiom, returns all declarations that depend on it
//! - [`SorryTracer::priority`] — ranks sorry axioms by downstream dependent count (highest first)

use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use hashbrown::{HashMap, HashSet};

use super::axiom_audit::is_foundational_axiom;
use super::types::{ConstantInfo, ConstantKind};
use super::Environment;

/// A "sorry" axiom is any axiom that represents an unproved obligation.
///
/// Detection criteria:
/// 1. `Declaration::Axiom` with `sorry` in its name (e.g., `sorryAx`)
/// 2. `Declaration::Axiom` that is not a foundational axiom and was likely
///    added via `add_decl_structural`
/// 3. Any declaration whose proof term references such an axiom
///
/// We identify sorry axioms as: any `ConstantKind::Axiom` whose name contains
/// "sorry" (case-insensitive) OR any non-foundational domain-specific axiom.
pub(super) fn is_sorry_axiom(info: &ConstantInfo) -> bool {
    if info.kind != ConstantKind::Axiom {
        return false;
    }
    let name_str = info.name.to_string();
    // Direct sorry markers
    if name_str.contains("sorry") || name_str.contains("Sorry") {
        return true;
    }
    // Non-foundational axioms are sorry obligations (domain-specific assumptions).
    // Delegates to `axiom_audit::is_foundational_axiom` as the single source of
    // truth for the foundational whitelist (#3560). Prior to consolidation this
    // module carried its own `is_foundational_axiom_name` copy which drifted
    // from the canonical list — missing Rat min/max, Fin.castSucc/Fin.last, the
    // Rat ring / field axiom batches (#3551/#3555), and Nat.le_refl — causing
    // the sorry tracer to classify those as sorry obligations while
    // `proof_quality()` classified the same names as foundational.
    !is_foundational_axiom(&info.name)
}

/// Collect all `Expr::Const` names referenced in an expression tree.
///
/// Uses an explicit stack to avoid deep recursion on large expressions.
fn collect_const_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack: Vec<&Expr> = vec![expr];

    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) | ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            // Terminals: BVar, FVar, Sort, Lit, SProp, Cubical variants
            _ => {}
        }
    }
}

/// Pre-computed sorry dependency graph for an environment.
///
/// Provides O(1) lookups for forward dependencies (which sorry axioms does a
/// declaration depend on?) and reverse dependencies (which declarations depend
/// on a given sorry axiom?).
#[derive(Clone, Debug)]
pub struct SorryTracer {
    /// Forward map: declaration name -> set of sorry axiom names it transitively depends on.
    forward: HashMap<Name, Vec<Name>>,
    /// Reverse map: sorry axiom name -> set of declaration names that depend on it.
    reverse: HashMap<Name, Vec<Name>>,
    /// All sorry axiom names, sorted by descending impact (most dependents first).
    priority_order: Vec<(Name, usize)>,
}

impl SorryTracer {
    /// Build a sorry dependency tracer by scanning all declarations in the environment.
    ///
    /// Algorithm:
    /// 1. Identify all sorry axioms (domain-specific axioms + sorry-named axioms)
    /// 2. For each non-sorry declaration, compute transitive sorry dependencies via BFS
    /// 3. Build reverse index from sorry axioms to their dependents
    /// 4. Sort sorry axioms by impact (descending dependent count)
    #[must_use]
    pub fn build(env: &Environment) -> Self {
        // Step 1: Identify all sorry axioms
        let sorry_axioms: HashSet<Name> = env
            .constants()
            .filter(|c| is_sorry_axiom(c))
            .map(|c| c.name.clone())
            .collect();

        // Step 2: For each declaration, compute transitive sorry dependencies
        let mut forward: HashMap<Name, Vec<Name>> = HashMap::new();
        let mut reverse: HashMap<Name, Vec<Name>> = HashMap::new();

        // Initialize reverse map entries for all sorry axioms
        for sorry_name in &sorry_axioms {
            reverse.entry(sorry_name.clone()).or_default();
        }

        // Collect all declaration names to avoid borrow issues
        let all_names: Vec<Name> = env.constants().map(|c| c.name.clone()).collect();

        for decl_name in &all_names {
            let sorry_deps = Self::compute_sorry_deps(env, decl_name, &sorry_axioms);

            if !sorry_deps.is_empty() {
                // Update reverse map
                for sorry_name in &sorry_deps {
                    reverse
                        .entry(sorry_name.clone())
                        .or_default()
                        .push(decl_name.clone());
                }
                forward.insert(decl_name.clone(), sorry_deps);
            }
        }

        // Step 3: Sort forward and reverse vecs for deterministic output
        for deps in forward.values_mut() {
            deps.sort_by_key(|a| a.to_string());
        }
        for deps in reverse.values_mut() {
            deps.sort_by_key(|a| a.to_string());
        }

        // Step 4: Build priority ordering (descending by dependent count)
        let mut priority_order: Vec<(Name, usize)> = reverse
            .iter()
            .map(|(name, deps)| (name.clone(), deps.len()))
            .collect();
        priority_order.sort_by(|a, b| {
            b.1.cmp(&a.1)
                .then_with(|| a.0.to_string().cmp(&b.0.to_string()))
        });

        SorryTracer {
            forward,
            reverse,
            priority_order,
        }
    }

    /// Compute the transitive sorry axiom dependencies for a single declaration.
    fn compute_sorry_deps(
        env: &Environment,
        name: &Name,
        sorry_axioms: &HashSet<Name>,
    ) -> Vec<Name> {
        let info = match env.get_const(name) {
            Some(info) => info,
            None => return Vec::new(),
        };

        // Collect direct const refs from type and value
        let mut all_refs = HashSet::new();
        collect_const_refs(&info.type_, &mut all_refs);
        if let Some(ref value) = info.value {
            collect_const_refs(value, &mut all_refs);
        }

        // BFS through transitive dependencies to find sorry axioms
        let mut found_sorry: HashSet<Name> = HashSet::new();
        let mut visited = HashSet::new();
        visited.insert(name.clone());
        let mut worklist: Vec<Name> = all_refs.into_iter().collect();

        while let Some(ref_name) = worklist.pop() {
            if !visited.insert(ref_name.clone()) {
                continue;
            }

            // Check if this is a sorry axiom
            if sorry_axioms.contains(&ref_name) {
                found_sorry.insert(ref_name.clone());
            }

            // Walk transitive dependencies
            if let Some(ref_info) = env.get_const(&ref_name) {
                let mut transitive_refs = HashSet::new();
                collect_const_refs(&ref_info.type_, &mut transitive_refs);
                if let Some(ref value) = ref_info.value {
                    collect_const_refs(value, &mut transitive_refs);
                }
                for tr in transitive_refs {
                    if !visited.contains(&tr) {
                        worklist.push(tr);
                    }
                }
            }
        }

        let mut result: Vec<Name> = found_sorry.into_iter().collect();
        result.sort_by_key(|a| a.to_string());
        result
    }

    /// Returns the sorry axioms that the given declaration transitively depends on.
    ///
    /// Returns an empty slice if the declaration has no sorry dependencies or is not found.
    #[must_use]
    pub fn trace_deps(&self, name: &Name) -> &[Name] {
        self.forward.get(name).map_or(&[], |v| v.as_slice())
    }

    /// Returns all declarations that depend on the given sorry axiom.
    ///
    /// Returns an empty slice if the sorry axiom has no dependents or is not found.
    #[must_use]
    pub fn impact(&self, sorry_name: &Name) -> &[Name] {
        self.reverse.get(sorry_name).map_or(&[], |v| v.as_slice())
    }

    /// Returns sorry axioms ranked by number of downstream dependents (highest first).
    ///
    /// Each entry is `(sorry_axiom_name, dependent_count)`. Sorry axioms with zero
    /// dependents are included (they exist but nothing uses them yet).
    #[must_use]
    pub fn priority(&self) -> &[(Name, usize)] {
        &self.priority_order
    }

    /// Returns the total number of sorry axioms in the environment.
    #[must_use]
    pub fn sorry_count(&self) -> usize {
        self.reverse.len()
    }

    /// Returns true if the given declaration has any sorry dependencies.
    #[must_use]
    pub fn has_sorry_deps(&self, name: &Name) -> bool {
        self.forward.get(name).is_some_and(|deps| !deps.is_empty())
    }
}

/// Convenience methods on Environment for sorry tracing.
impl Environment {
    /// Build a sorry dependency tracer for this environment.
    ///
    /// This is a potentially expensive operation that scans all declarations.
    /// Cache the result if calling multiple trace operations.
    #[must_use]
    pub fn sorry_tracer(&self) -> SorryTracer {
        SorryTracer::build(self)
    }

    /// Returns the sorry axioms that the given declaration transitively depends on.
    ///
    /// Convenience wrapper that builds a fresh tracer. For multiple lookups,
    /// use [`Self::sorry_tracer`] and call methods on the returned [`SorryTracer`].
    #[must_use]
    pub fn trace_sorry_deps(&self, name: &Name) -> Vec<Name> {
        let tracer = SorryTracer::build(self);
        tracer.trace_deps(name).to_vec()
    }

    /// Returns all declarations that depend on the given sorry axiom.
    ///
    /// Convenience wrapper that builds a fresh tracer. For multiple lookups,
    /// use [`Self::sorry_tracer`] and call methods on the returned [`SorryTracer`].
    #[must_use]
    pub fn sorry_impact(&self, sorry_name: &Name) -> Vec<Name> {
        let tracer = SorryTracer::build(self);
        tracer.impact(sorry_name).to_vec()
    }

    /// Returns sorry axioms ranked by downstream dependent count (highest first).
    ///
    /// Convenience wrapper that builds a fresh tracer. For multiple lookups,
    /// use [`Self::sorry_tracer`] and call methods on the returned [`SorryTracer`].
    #[must_use]
    pub fn sorry_priority(&self) -> Vec<(Name, usize)> {
        let tracer = SorryTracer::build(self);
        tracer.priority().to_vec()
    }
}
