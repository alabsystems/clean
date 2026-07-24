// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended coercion elaboration with chain composition, sort coercions,
//! function coercions, numeric literal coercions, and diamond resolution.
//!
//! Builds on [`crate::coercion`] with richer coercion search, user-defined
//! coercion registration, ambiguity detection, and trace generation for
//! debugging.
//!
//! # Reference
//!
//! Lean 4 `src/Lean/Meta/Coe.lean`, `src/Lean/Elab/Coercion.lean`

use std::collections::{HashMap, HashSet, VecDeque};

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use crate::coercion::{CoercionEntry, CoercionKind, CoercionPath, CoercionRegistry};
use crate::error::ElabError;

/// Configuration for extended coercion search.
#[derive(Debug, Clone)]
pub(crate) struct CoercionExtConfig {
    pub(crate) max_depth: usize,
    pub(crate) sort_coercions: bool,
    pub(crate) function_coercions: bool,
    pub(crate) numeric_coercions: bool,
    pub(crate) detect_ambiguity: bool,
    pub(crate) trace_enabled: bool,
}

impl Default for CoercionExtConfig {
    fn default() -> Self {
        Self {
            max_depth: 8,
            sort_coercions: true,
            function_coercions: true,
            numeric_coercions: true,
            detect_ambiguity: true,
            trace_enabled: false,
        }
    }
}

/// Sort coercion identifiers for universe lifting.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum SortCoercion {
    PropToType,
    TypeToSort,
}

/// A single entry in a coercion search trace.
#[derive(Debug, Clone)]
pub(crate) struct CoercionTraceEntry {
    pub(crate) kind: TraceStepKind,
    pub(crate) source: Name,
    pub(crate) target: Name,
    pub(crate) success: bool,
}

/// Kind of step in a coercion trace.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TraceStepKind {
    Direct,
    Chain,
    Sort(SortCoercion),
    FunctionCoe,
    Numeric,
}

/// Accumulated coercion search trace for debugging.
#[derive(Debug, Clone, Default)]
pub(crate) struct CoercionTrace {
    pub(crate) entries: Vec<CoercionTraceEntry>,
}

impl CoercionTrace {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }
    pub(crate) fn push(&mut self, entry: CoercionTraceEntry) {
        self.entries.push(entry);
    }
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
}

/// Result of ambiguity check: all coercion paths from source to target.
#[derive(Debug, Clone)]
pub(crate) struct AmbiguityResult {
    pub(crate) paths: Vec<CoercionPath>,
    pub(crate) is_ambiguous: bool,
}

/// Extended coercion search engine with sort, function, and numeric coercions.
#[derive(Debug, Clone)]
pub(crate) struct CoercionExtSearch {
    config: CoercionExtConfig,
    sort_coercion_fns: HashMap<SortCoercion, Name>,
    coe_fun_sources: HashSet<Name>,
    of_nat_targets: HashSet<Name>,
    of_scientific_targets: HashSet<Name>,
}

impl CoercionExtSearch {
    /// Create a new extended search with default configuration.
    #[must_use]
    pub(crate) fn new(config: CoercionExtConfig) -> Self {
        let mut sort_coercion_fns = HashMap::new();
        sort_coercion_fns.insert(SortCoercion::PropToType, Name::from_string("propToType"));
        sort_coercion_fns.insert(SortCoercion::TypeToSort, Name::from_string("typeToSort"));

        let mut of_nat_targets = HashSet::new();
        of_nat_targets.insert(Name::from_string("Int"));
        of_nat_targets.insert(Name::from_string("Float"));
        of_nat_targets.insert(Name::from_string("Rat"));

        let mut of_scientific_targets = HashSet::new();
        of_scientific_targets.insert(Name::from_string("Float"));

        Self {
            config,
            sort_coercion_fns,
            coe_fun_sources: HashSet::new(),
            of_nat_targets,
            of_scientific_targets,
        }
    }

    /// Create a search engine with default config.
    #[must_use]
    pub(crate) fn with_defaults() -> Self {
        Self::new(CoercionExtConfig::default())
    }

    /// Register a type as having a coeFun instance.
    pub(crate) fn register_coe_fun(&mut self, type_name: Name) {
        self.coe_fun_sources.insert(type_name);
    }

    /// Register a type as supporting OfNat coercion from Nat literals.
    pub(crate) fn register_of_nat_target(&mut self, type_name: Name) {
        self.of_nat_targets.insert(type_name);
    }

    /// Register a type as supporting OfScientific coercion from Float literals.
    pub(crate) fn register_of_scientific_target(&mut self, type_name: Name) {
        self.of_scientific_targets.insert(type_name);
    }

    /// Check whether a type has a registered coeFun instance.
    #[must_use]
    pub(crate) fn has_coe_fun(&self, type_name: &Name) -> bool {
        self.coe_fun_sources.contains(type_name)
    }

    /// Check whether a type supports OfNat coercion.
    #[must_use]
    pub(crate) fn has_of_nat(&self, type_name: &Name) -> bool {
        self.of_nat_targets.contains(type_name)
    }

    /// Check whether a type supports OfScientific coercion.
    #[must_use]
    pub(crate) fn has_of_scientific(&self, type_name: &Name) -> bool {
        self.of_scientific_targets.contains(type_name)
    }

    /// Try to find a sort coercion from `source` to `target`.
    #[must_use]
    pub(crate) fn find_sort_coercion(
        &self,
        source: &Name,
        target: &Name,
    ) -> Option<(SortCoercion, Name)> {
        if !self.config.sort_coercions {
            return None;
        }
        let source_s = source.to_string();
        let target_s = target.to_string();

        if source_s == "Prop" && target_s == "Type" {
            let kind = SortCoercion::PropToType;
            return self.sort_coercion_fns.get(&kind).map(|n| (kind, n.clone()));
        }
        if source_s == "Type" && target_s == "Sort" {
            let kind = SortCoercion::TypeToSort;
            return self.sort_coercion_fns.get(&kind).map(|n| (kind, n.clone()));
        }
        None
    }

    /// Try to apply a function coercion (coeFun) to an expression.
    #[must_use]
    pub(crate) fn try_function_coercion(&self, source_type: &Name, expr: Expr) -> Option<Expr> {
        if !self.config.function_coercions {
            return None;
        }
        if !self.coe_fun_sources.contains(source_type) {
            return None;
        }
        let coe_fn = Name::from_string("coeFun");
        Some(Expr::app(Expr::const_(coe_fn, Vec::new()), expr))
    }

    /// Try to find a numeric literal coercion from Nat to `target` via OfNat.
    #[must_use]
    pub(crate) fn find_nat_literal_coercion(&self, target: &Name) -> Option<CoercionEntry> {
        if !self.config.numeric_coercions {
            return None;
        }
        if !self.of_nat_targets.contains(target) {
            return None;
        }
        let fn_name = Name::from_string(&format!("{}.ofNat", target));
        Some(CoercionEntry {
            fn_name,
            source: Name::from_string("Nat"),
            target: target.clone(),
            kind: CoercionKind::BuiltinUpcast,
        })
    }

    /// Try to find a scientific literal coercion to `target` via OfScientific.
    #[must_use]
    pub(crate) fn find_scientific_literal_coercion(&self, target: &Name) -> Option<CoercionEntry> {
        if !self.config.numeric_coercions {
            return None;
        }
        if !self.of_scientific_targets.contains(target) {
            return None;
        }
        let fn_name = Name::from_string(&format!("{}.ofScientific", target));
        Some(CoercionEntry {
            fn_name,
            source: Name::from_string("Float"),
            target: target.clone(),
            kind: CoercionKind::BuiltinUpcast,
        })
    }

    /// Find ALL coercion paths from `source` to `target` via BFS up to `max_depth`.
    #[must_use]
    pub(crate) fn find_all_paths(
        &self,
        registry: &CoercionRegistry,
        source: &Name,
        target: &Name,
    ) -> AmbiguityResult {
        let max_depth = self.config.max_depth;
        let mut all_paths = Vec::new();

        // BFS collecting all paths (not just the first).
        let mut queue: VecDeque<(Name, Vec<CoercionEntry>, HashSet<Name>)> = VecDeque::new();
        let mut start_visited = HashSet::new();
        start_visited.insert(source.clone());
        queue.push_back((source.clone(), Vec::new(), start_visited));

        while let Some((current, path, visited)) = queue.pop_front() {
            if path.len() >= max_depth {
                continue;
            }
            for entry in registry.iter() {
                if entry.source != current {
                    continue;
                }
                let mut new_path = path.clone();
                new_path.push(entry.clone());

                if entry.target == *target {
                    all_paths.push(CoercionPath { steps: new_path });
                    continue;
                }
                if !visited.contains(&entry.target) {
                    let mut new_visited = visited.clone();
                    new_visited.insert(entry.target.clone());
                    queue.push_back((entry.target.clone(), new_path, new_visited));
                }
            }
        }

        let is_ambiguous = all_paths.len() > 1;
        AmbiguityResult {
            paths: all_paths,
            is_ambiguous,
        }
    }

    /// Resolve a diamond coercion by preferring the shortest path.
    #[must_use]
    pub(crate) fn resolve_diamond(
        &self,
        registry: &CoercionRegistry,
        source: &Name,
        target: &Name,
    ) -> Option<CoercionPath> {
        let result = self.find_all_paths(registry, source, target);
        if result.paths.is_empty() {
            return None;
        }
        // Select shortest path (diamond resolution policy).
        result.paths.into_iter().min_by_key(|p| p.len())
    }

    /// Perform extended coercion search: registry chains, sort, then numeric.
    pub(crate) fn search(
        &self,
        registry: &CoercionRegistry,
        source: &Name,
        target: &Name,
    ) -> (Option<CoercionPath>, CoercionTrace) {
        let mut trace = CoercionTrace::new();

        // 1. Try direct/chain coercion from registry (diamond-aware).
        if self.config.detect_ambiguity {
            let resolved = self.resolve_diamond(registry, source, target);
            if self.config.trace_enabled {
                trace.push(CoercionTraceEntry {
                    kind: TraceStepKind::Chain,
                    source: source.clone(),
                    target: target.clone(),
                    success: resolved.is_some(),
                });
            }
            if resolved.is_some() {
                return (resolved, trace);
            }
        } else {
            let chain = registry.find_chain(source, target);
            if self.config.trace_enabled {
                trace.push(CoercionTraceEntry {
                    kind: TraceStepKind::Direct,
                    source: source.clone(),
                    target: target.clone(),
                    success: chain.is_some(),
                });
            }
            if chain.is_some() {
                return (chain, trace);
            }
        }

        // 2. Try sort coercion.
        if let Some((sort_kind, fn_name)) = self.find_sort_coercion(source, target) {
            if self.config.trace_enabled {
                trace.push(CoercionTraceEntry {
                    kind: TraceStepKind::Sort(sort_kind),
                    source: source.clone(),
                    target: target.clone(),
                    success: true,
                });
            }
            let entry = CoercionEntry {
                fn_name,
                source: source.clone(),
                target: target.clone(),
                kind: CoercionKind::BuiltinUpcast,
            };
            return (Some(CoercionPath { steps: vec![entry] }), trace);
        } else if self.config.trace_enabled && self.config.sort_coercions {
            trace.push(CoercionTraceEntry {
                kind: TraceStepKind::Sort(SortCoercion::PropToType),
                source: source.clone(),
                target: target.clone(),
                success: false,
            });
        }

        // 3. Try numeric literal coercion (Nat -> target via OfNat).
        let source_s = source.to_string();
        if source_s == "Nat" {
            if let Some(entry) = self.find_nat_literal_coercion(target) {
                if self.config.trace_enabled {
                    trace.push(CoercionTraceEntry {
                        kind: TraceStepKind::Numeric,
                        source: source.clone(),
                        target: target.clone(),
                        success: true,
                    });
                }
                return (Some(CoercionPath { steps: vec![entry] }), trace);
            }
        }

        if self.config.trace_enabled {
            trace.push(CoercionTraceEntry {
                kind: TraceStepKind::Numeric,
                source: source.clone(),
                target: target.clone(),
                success: false,
            });
        }

        (None, trace)
    }

    /// Try to coerce `expr` from `actual_type` to `expected_type` using full pipeline.
    pub(crate) fn try_coerce_ext(
        &self,
        registry: &CoercionRegistry,
        expr: Expr,
        actual_type: &Expr,
        expected_type: &Expr,
    ) -> Result<(Expr, CoercionTrace), ElabError> {
        let source = crate::coercion::head_type_name(actual_type).ok_or_else(|| {
            ElabError::TypeMismatch {
                expected: format!("{expected_type:?}"),
                actual: format!("{actual_type:?}"),
            }
        })?;
        let target = crate::coercion::head_type_name(expected_type).ok_or_else(|| {
            ElabError::TypeMismatch {
                expected: format!("{expected_type:?}"),
                actual: format!("{actual_type:?}"),
            }
        })?;

        let (path_opt, trace) = self.search(registry, &source, &target);
        match path_opt {
            Some(path) => {
                let coerced = crate::coercion::apply_coercion_path(&path, expr);
                Ok((coerced, trace))
            }
            None => Err(ElabError::TypeMismatch {
                expected: format!("{expected_type:?}"),
                actual: format!("{actual_type:?}"),
            }),
        }
    }
}
