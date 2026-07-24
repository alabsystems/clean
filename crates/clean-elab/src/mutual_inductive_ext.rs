// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended mutual inductive elaboration: grouping, universe unification,
//! parameter consistency, constructor elaboration, positivity checking,
//! recursor/induction/below/BRec generation, and dependency graphs.
//!
//! Lean 4 reference: `src/Lean/Elab/MutualDef.lean`, `src/kernel/inductive.cpp`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use clean_kernel::inductive::mentions_name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name};

use crate::error::ElabError;
use crate::inductive_ext::extract_universe_from_type;

// =============================================================================
// Error types
// =============================================================================

/// Errors specific to extended mutual inductive elaboration.
#[derive(Debug, Clone, thiserror::Error)]
pub(crate) enum MutualIndExtError {
    #[error("parameter mismatch: type `{type_name}` has {actual} params, expected {expected}")]
    ParameterMismatch {
        type_name: Name,
        expected: usize,
        actual: usize,
    },
    #[error("universe unification failed: {detail}")]
    UniverseUnificationFailed { detail: String },
    #[error("constructor `{ctor}` references unknown type `{referenced}`")]
    UnknownTypeReference { ctor: Name, referenced: Name },
    #[error("non-positive occurrence of `{offender}` in constructor `{ctor}` of `{type_name}`")]
    MutualPositivityViolation {
        type_name: Name,
        ctor: Name,
        offender: Name,
    },
    #[error("dependency cycle in mutual block: {cycle}")]
    DependencyCycle { cycle: String },
}

impl From<MutualIndExtError> for ElabError {
    fn from(e: MutualIndExtError) -> Self {
        ElabError::Unsupported {
            feature: e.to_string(),
        }
    }
}

// =============================================================================
// Core types
// =============================================================================

/// A type entry in an extended mutual inductive block.
#[derive(Debug, Clone)]
pub(crate) struct MutualTypeEntry {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) params: Vec<(Name, Expr)>,
    pub(crate) constructors: Vec<MutualCtorEntry>,
}

/// A constructor entry in an extended mutual inductive block.
#[derive(Debug, Clone)]
pub(crate) struct MutualCtorEntry {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) fields: Vec<(Name, Expr)>,
}

/// An extended mutual inductive block ready for elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualIndExtBlock {
    pub(crate) types: Vec<MutualTypeEntry>,
    pub(crate) universe_params: Vec<Name>,
}

// =============================================================================
// Dependency graph
// =============================================================================

/// Dependency graph for types within a mutual block.
#[derive(Debug, Clone)]
pub(crate) struct MutualDepGraph {
    pub(crate) edges: BTreeMap<Name, BTreeSet<Name>>,
}

impl MutualDepGraph {
    pub(crate) fn build(block: &MutualIndExtBlock) -> Self {
        let all_names: HashSet<&Name> = block.types.iter().map(|t| &t.name).collect();
        let mut edges = BTreeMap::new();
        for ty in &block.types {
            let mut deps = BTreeSet::new();
            for ctor in &ty.constructors {
                for (_, field_ty) in &ctor.fields {
                    for name in &all_names {
                        if mentions_name(field_ty, name) && **name != ty.name {
                            deps.insert((*name).clone());
                        }
                    }
                }
                for name in &all_names {
                    if mentions_name(&ctor.type_expr, name) && **name != ty.name {
                        deps.insert((*name).clone());
                    }
                }
            }
            edges.insert(ty.name.clone(), deps);
        }
        Self { edges }
    }

    pub(crate) fn deps_of(&self, name: &Name) -> Option<&BTreeSet<Name>> {
        self.edges.get(name)
    }

    pub(crate) fn depends_on(&self, from: &Name, to: &Name) -> bool {
        self.edges.get(from).is_some_and(|deps| deps.contains(to))
    }

    pub(crate) fn edge_count(&self) -> usize {
        self.edges.values().map(|deps| deps.len()).sum()
    }

    pub(crate) fn topological_sort(&self) -> Result<Vec<Name>, MutualIndExtError> {
        let mut in_degree: HashMap<&Name, usize> = HashMap::new();
        for name in self.edges.keys() {
            in_degree.entry(name).or_insert(0);
            if let Some(deps) = self.edges.get(name) {
                for dep in deps {
                    *in_degree.entry(dep).or_insert(0) += 1;
                }
            }
        }
        let mut queue: Vec<&Name> = in_degree
            .iter()
            .filter(|(_, &deg)| deg == 0)
            .map(|(&n, _)| n)
            .collect();
        queue.sort();
        let mut result = Vec::new();
        while let Some(node) = queue.pop() {
            result.push(node.clone());
            if let Some(deps) = self.edges.get(node) {
                for dep in deps {
                    if let Some(deg) = in_degree.get_mut(dep) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            queue.push(dep);
                            queue.sort();
                        }
                    }
                }
            }
        }
        if result.len() < self.edges.len() {
            let remaining: Vec<String> = self
                .edges
                .keys()
                .filter(|n| !result.contains(n))
                .map(|n| n.to_string())
                .collect();
            Err(MutualIndExtError::DependencyCycle {
                cycle: remaining.join(" -> "),
            })
        } else {
            Ok(result)
        }
    }
}

// =============================================================================
// Grouping
// =============================================================================

/// Identify mutual groups by analyzing cross-references between types.
/// Returns groups of indices where each group contains mutually-referencing types.
pub(crate) fn identify_mutual_groups(types: &[MutualTypeEntry]) -> Vec<Vec<usize>> {
    let n = types.len();
    let all_names: Vec<&Name> = types.iter().map(|t| &t.name).collect();

    let mut adj = vec![vec![false; n]; n];
    for (i, ty) in types.iter().enumerate() {
        for ctor in &ty.constructors {
            for (j, name) in all_names.iter().enumerate() {
                if i != j && mentions_name(&ctor.type_expr, name) {
                    adj[i][j] = true;
                    adj[j][i] = true;
                }
            }
        }
    }

    // Union-Find for connected components.
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], x: usize) -> usize {
        if parent[x] != x {
            parent[x] = find(parent, parent[x]);
        }
        parent[x]
    }
    // Indices `i` and `j` are used to look up `adj[i][j]` (offset `j > i`) and
    // pass into `find`; an iterator does not help readability here.
    #[allow(clippy::needless_range_loop)]
    for i in 0..n {
        for j in (i + 1)..n {
            if adj[i][j] {
                let (ri, rj) = (find(&mut parent, i), find(&mut parent, j));
                if ri != rj {
                    parent[ri] = rj;
                }
            }
        }
    }

    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..n {
        groups.entry(find(&mut parent, i)).or_default().push(i);
    }
    groups.into_values().collect()
}

// =============================================================================
// Validation functions
// =============================================================================

/// Unify universe levels across all types (returns max of all type universes).
pub(crate) fn unify_universe_levels(block: &MutualIndExtBlock) -> Result<Level, MutualIndExtError> {
    if block.types.is_empty() {
        return Ok(Level::zero());
    }
    let mut result = extract_universe_from_type(&block.types[0].type_expr);
    for ty in &block.types[1..] {
        result = Level::max(result, extract_universe_from_type(&ty.type_expr));
    }
    Ok(result)
}

/// Check that all types share the same parameter count.
pub(crate) fn check_parameter_consistency(
    block: &MutualIndExtBlock,
) -> Result<usize, MutualIndExtError> {
    if block.types.is_empty() {
        return Ok(0);
    }
    let expected = block.types[0].params.len();
    for ty in &block.types[1..] {
        if ty.params.len() != expected {
            return Err(MutualIndExtError::ParameterMismatch {
                type_name: ty.name.clone(),
                expected,
                actual: ty.params.len(),
            });
        }
    }
    Ok(expected)
}

/// Validate constructor return types target types in the mutual block.
pub(crate) fn check_constructor_targets(
    block: &MutualIndExtBlock,
) -> Result<(), MutualIndExtError> {
    let all_names: HashSet<&Name> = block.types.iter().map(|t| &t.name).collect();
    for ty in &block.types {
        for ctor in &ty.constructors {
            if let Some(target) = extract_return_head(&ctor.type_expr) {
                if !all_names.contains(&target) {
                    return Err(MutualIndExtError::UnknownTypeReference {
                        ctor: ctor.name.clone(),
                        referenced: target.clone(),
                    });
                }
            }
        }
    }
    Ok(())
}

fn extract_return_head(expr: &Expr) -> Option<&Name> {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    if let ExprKind::Const(name, _) = current.get_app_fn().kind() {
        Some(name)
    } else {
        None
    }
}

/// Check strict positivity for all types across the mutual block.
pub(crate) fn check_mutual_positivity(block: &MutualIndExtBlock) -> Result<(), MutualIndExtError> {
    let all_names: Vec<&Name> = block.types.iter().map(|t| &t.name).collect();
    for ty in &block.types {
        for ctor in &ty.constructors {
            for name in &all_names {
                if has_negative_occurrence(name, &ctor.type_expr) {
                    return Err(MutualIndExtError::MutualPositivityViolation {
                        type_name: ty.name.clone(),
                        ctor: ctor.name.clone(),
                        offender: (*name).clone(),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Check whether `name` occurs in a *strictly-negative* position within
/// the constructor type `ty`.
///
/// Walks the constructor's Pi telescope: each argument domain must satisfy
/// strict positivity for `name`. The argument's codomain (i.e. the rest of
/// the constructor) is checked recursively the same way.
///
/// Strict positivity (`check_strictly_positive`): the argument may itself
/// be a Pi (an arrow), and `name` may appear in the codomain of that
/// nested arrow, but NOT in its domain. Direct occurrences (`Const(name,
/// _)`), applications, lambdas, lets, and projections are descended into
/// uniformly.
///
/// This correctly accepts the classical `Tree.node : Forest → Tree`
/// (`Forest` appears only as a top-level Pi argument, never under an
/// inner arrow) and `Nat.succ : Nat → Nat` (same shape with the
/// inductive itself), and correctly rejects `Tree.bad : (Forest → Bool)
/// → Tree` (`Forest` appears under an inner arrow's domain).
fn has_negative_occurrence(name: &Name, ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, domain, body) => {
            // The domain is a constructor argument; it must be strictly
            // positive w.r.t. `name`. The body is the rest of the
            // constructor's telescope and is checked the same way.
            !is_strictly_positive(name, domain) || has_negative_occurrence(name, body)
        }
        _ => false,
    }
}

/// Strict positivity check: `name` may appear at the head of a direct
/// application, or in the codomain of an arrow, but never in the domain
/// of an arrow.
fn is_strictly_positive(name: &Name, expr: &Expr) -> bool {
    match expr.kind() {
        // Atomic / non-Pi heads are always strictly positive: any
        // `Const(name, _)` occurrence as an argument is fine.
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Lit(_)
        | ExprKind::Const(_, _) => true,
        // Applications: descend into both halves. The head can be
        // `Const(name, _)` (the recursive type itself applied to
        // arguments); the args themselves must still be strictly
        // positive in `name`.
        ExprKind::App(f, a) => is_strictly_positive(name, f) && is_strictly_positive(name, a),
        // The key case: a nested arrow. The domain MUST NOT mention
        // `name` at all (any mention is negative); the codomain is
        // checked strictly positively (still under "left of zero
        // arrows"-since-domain count).
        ExprKind::Pi(_, domain, body) => {
            !mentions_name(domain, name) && is_strictly_positive(name, body)
        }
        // Lambdas and let-bindings: descend transparently.
        ExprKind::Lam(_, ty, body) => {
            is_strictly_positive(name, ty) && is_strictly_positive(name, body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            is_strictly_positive(name, ty)
                && is_strictly_positive(name, val)
                && is_strictly_positive(name, body)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => is_strictly_positive(name, e),
        // Conservative: treat any other ExprKind as failing strict
        // positivity if `name` is mentioned at all — these are mode
        // extensions (Cubical/ZFC) not relevant to standard mutual
        // inductive elaboration.
        _ => !mentions_name(expr, name),
    }
}

// =============================================================================
// Generation types and functions
// =============================================================================

/// Specification for a mutual recursor.
#[derive(Debug, Clone)]
pub(crate) struct MutualRecursorSpec {
    pub(crate) name: Name,
    pub(crate) target_type: Name,
    pub(crate) num_motives: u32,
    pub(crate) num_minors: u32,
    pub(crate) type_expr: Expr,
}

/// Specification for a mutual induction principle.
#[derive(Debug, Clone)]
pub(crate) struct InductionPrincipleSpec {
    pub(crate) name: Name,
    pub(crate) target_type: Name,
    pub(crate) type_expr: Expr,
}

/// Specification for a below type or bounded recursion principle.
#[derive(Debug, Clone)]
pub(crate) struct BelowSpec {
    pub(crate) name: Name,
    pub(crate) target_type: Name,
    pub(crate) type_expr: Expr,
}

/// Specification for a bounded recursion principle.
#[derive(Debug, Clone)]
pub(crate) struct BRecSpec {
    pub(crate) name: Name,
    pub(crate) target_type: Name,
    pub(crate) type_expr: Expr,
}

/// Build a Pi-wrapped type with `total` binders over `result_sort`.
fn build_pi_type(total: u32, result_sort: Level) -> Expr {
    let mut result = Expr::sort(result_sort);
    for _ in 0..total {
        result = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), result);
    }
    result
}

fn total_ctors(block: &MutualIndExtBlock) -> u32 {
    block
        .types
        .iter()
        .map(|t| t.constructors.len() as u32)
        .sum()
}

/// Generate mutual recursor specifications.
pub(crate) fn generate_recursors(block: &MutualIndExtBlock) -> Vec<MutualRecursorSpec> {
    let (n_types, n_ctors) = (block.types.len() as u32, total_ctors(block));
    block
        .types
        .iter()
        .map(|ty| {
            let total = ty.params.len() as u32 + n_types + n_ctors + 1;
            MutualRecursorSpec {
                name: Name::from_string(&format!("{}.rec", ty.name)),
                target_type: ty.name.clone(),
                num_motives: n_types,
                num_minors: n_ctors,
                type_expr: build_pi_type(total, Level::param(Name::from_string("u_motive"))),
            }
        })
        .collect()
}

/// Generate induction principle specifications (target Prop).
pub(crate) fn generate_induction_principles(
    block: &MutualIndExtBlock,
) -> Vec<InductionPrincipleSpec> {
    let (n_types, n_ctors) = (block.types.len() as u32, total_ctors(block));
    block
        .types
        .iter()
        .map(|ty| {
            let total = ty.params.len() as u32 + n_types + n_ctors + 1;
            InductionPrincipleSpec {
                name: Name::from_string(&format!("{}.ind", ty.name)),
                target_type: ty.name.clone(),
                type_expr: build_pi_type(total, Level::zero()),
            }
        })
        .collect()
}

/// Generate below-type specs for mutual recursive types.
pub(crate) fn generate_below(block: &MutualIndExtBlock) -> Vec<BelowSpec> {
    block
        .types
        .iter()
        .map(|ty| {
            let total = ty.params.len() as u32 + 2;
            BelowSpec {
                name: Name::from_string(&format!("{}.below", ty.name)),
                target_type: ty.name.clone(),
                type_expr: build_pi_type(total, Level::param(Name::from_string("u_below"))),
            }
        })
        .collect()
}

/// Generate BRec (bounded recursion) specs for mutual recursive types.
pub(crate) fn generate_brec(block: &MutualIndExtBlock) -> Vec<BRecSpec> {
    block
        .types
        .iter()
        .map(|ty| {
            let total = ty.params.len() as u32 + 2;
            BRecSpec {
                name: Name::from_string(&format!("{}.brecOn", ty.name)),
                target_type: ty.name.clone(),
                type_expr: build_pi_type(total, Level::param(Name::from_string("u_brec"))),
            }
        })
        .collect()
}

// =============================================================================
// Statistics and pipeline
// =============================================================================

/// Statistics from mutual inductive elaboration.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct MutualIndExtStats {
    pub(crate) mutual_blocks_processed: u32,
    pub(crate) types_in_block: u32,
    pub(crate) constructors_checked: u32,
    pub(crate) recursors_generated: u32,
    pub(crate) induction_principles_generated: u32,
    pub(crate) below_specs_generated: u32,
    pub(crate) brec_specs_generated: u32,
    pub(crate) dependency_edges: u32,
}

/// Result of extended mutual inductive elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualIndExtResult {
    pub(crate) unified_universe: Level,
    pub(crate) num_params: usize,
    pub(crate) dep_graph: MutualDepGraph,
    pub(crate) recursors: Vec<MutualRecursorSpec>,
    pub(crate) induction_principles: Vec<InductionPrincipleSpec>,
    pub(crate) below_specs: Vec<BelowSpec>,
    pub(crate) brec_specs: Vec<BRecSpec>,
    pub(crate) stats: MutualIndExtStats,
}

/// Run the full extended mutual inductive elaboration pipeline.
pub(crate) fn elaborate_mutual_inductive_ext(
    block: &MutualIndExtBlock,
) -> Result<MutualIndExtResult, ElabError> {
    if block.types.is_empty() {
        return Err(ElabError::NotImplemented(
            "empty mutual inductive block".into(),
        ));
    }

    let num_params = check_parameter_consistency(block)?;
    let unified_universe = unify_universe_levels(block)?;
    check_constructor_targets(block)?;
    check_mutual_positivity(block)?;

    let dep_graph = MutualDepGraph::build(block);
    let recursors = generate_recursors(block);
    let induction_principles = generate_induction_principles(block);
    let below_specs = generate_below(block);
    let brec_specs = generate_brec(block);

    let n_ctors = total_ctors(block);
    let stats = MutualIndExtStats {
        mutual_blocks_processed: 1,
        types_in_block: block.types.len() as u32,
        constructors_checked: n_ctors,
        recursors_generated: recursors.len() as u32,
        induction_principles_generated: induction_principles.len() as u32,
        below_specs_generated: below_specs.len() as u32,
        brec_specs_generated: brec_specs.len() as u32,
        dependency_edges: dep_graph.edge_count() as u32,
    };

    Ok(MutualIndExtResult {
        unified_universe,
        num_params,
        dep_graph,
        recursors,
        induction_principles,
        below_specs,
        brec_specs,
        stats,
    })
}
