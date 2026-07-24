// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended structure inheritance analysis (phase 2).
//!
//! Builds on [`crate::structure_inherit`] and [`crate::structure_inherit_ext`]
//! with tree analysis, field resolution, override analysis, diamond detection,
//! C3 linearization, DOT visualization, and inheritance statistics.

use crate::structure_inherit::{structural_type_eq, FieldInfo, InheritanceResolver};
use clean_kernel::{Environment, Expr, Name};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Write as FmtWrite;
use thiserror::Error;

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum InheritAnalysisError {
    #[error("unknown structure `{name}`")]
    UnknownStructure { name: Name },
    #[error("C3 linearization failed: inconsistent hierarchy for `{name}`")]
    LinearizationFailed { name: Name },
    #[error("field `{field}` has conflicting types from `{source_a}` and `{source_b}`")]
    FieldTypeConflict {
        field: Name,
        source_a: Name,
        source_b: Name,
    },
    #[error("diamond detected at `{ancestor}` via paths: {paths:?}")]
    DiamondDetected { ancestor: Name, paths: Vec<Name> },
    #[error("depth limit ({limit}) exceeded for `{name}`")]
    DepthLimitExceeded { name: Name, limit: usize },
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct InheritTreeNode {
    pub(crate) name: Name,
    pub(crate) fields: Vec<Name>,
    pub(crate) children: Vec<Name>,
    pub(crate) depth: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct InheritTree {
    pub(crate) root: Name,
    pub(crate) nodes: HashMap<Name, InheritTreeNode>,
    pub(crate) max_depth: usize,
    pub(crate) max_breadth: usize,
    pub(crate) total_nodes: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct ResolvedField {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) origin: Name,
    pub(crate) chain: Vec<Name>,
    pub(crate) is_override: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct OverrideRecord {
    pub(crate) field: Name,
    pub(crate) parent_type: Expr,
    pub(crate) child_type: Expr,
    pub(crate) parent_struct: Name,
    pub(crate) child_struct: Name,
    pub(crate) is_compatible: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct DiamondInfo {
    pub(crate) ancestor: Name,
    pub(crate) paths: Vec<Vec<Name>>,
    pub(crate) shared_fields: Vec<Name>,
    pub(crate) resolution: DiamondResolution,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DiamondResolution {
    Deduplicate,
    ExplicitOverride,
    NoConflict,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InheritStats {
    pub(crate) max_depth: usize,
    pub(crate) max_breadth: usize,
    pub(crate) total_structures: usize,
    pub(crate) total_fields: usize,
    pub(crate) inherited_fields: usize,
    pub(crate) own_fields: usize,
    pub(crate) override_count: usize,
    pub(crate) diamond_count: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct AnalyzerConfig {
    pub(crate) max_depth: usize,
}

impl Default for AnalyzerConfig {
    fn default() -> Self {
        Self { max_depth: 64 }
    }
}

// ---------------------------------------------------------------------------
// Analyzer
// ---------------------------------------------------------------------------

pub(crate) struct InheritAnalyzer<'a> {
    env: &'a Environment,
    config: AnalyzerConfig,
}

impl<'a> InheritAnalyzer<'a> {
    pub(crate) fn new(env: &'a Environment, config: AnalyzerConfig) -> Self {
        Self { env, config }
    }

    pub(crate) fn with_defaults(env: &'a Environment) -> Self {
        Self::new(env, AnalyzerConfig::default())
    }

    /// Build the full inheritance tree rooted at `name`.
    pub(crate) fn build_tree(&self, name: &Name) -> Result<InheritTree, InheritAnalysisError> {
        let mut nodes = HashMap::new();
        let mut queue: VecDeque<(Name, usize)> = VecDeque::new();
        let mut max_depth = 0usize;
        let mut breadth_at: HashMap<usize, usize> = HashMap::new();
        queue.push_back((name.clone(), 0));

        while let Some((current, depth)) = queue.pop_front() {
            if depth > self.config.max_depth {
                return Err(InheritAnalysisError::DepthLimitExceeded {
                    name: current,
                    limit: self.config.max_depth,
                });
            }
            if nodes.contains_key(&current) {
                continue;
            }
            max_depth = max_depth.max(depth);
            *breadth_at.entry(depth).or_insert(0) += 1;
            let fields = self.field_names_of(&current);
            let parents = self.parents_of(&current);
            for p in &parents {
                queue.push_back((p.clone(), depth + 1));
            }
            nodes.insert(
                current.clone(),
                InheritTreeNode {
                    name: current,
                    fields,
                    children: parents,
                    depth,
                },
            );
        }

        let max_breadth = breadth_at.values().copied().max().unwrap_or(0);
        let total_nodes = nodes.len();
        Ok(InheritTree {
            root: name.clone(),
            nodes,
            max_depth,
            max_breadth,
            total_nodes,
        })
    }

    /// Resolve all fields visible to `struct_name` through inheritance chains.
    pub(crate) fn resolve_fields(
        &self,
        struct_name: &Name,
        own_fields: &[FieldInfo],
    ) -> Result<Vec<ResolvedField>, InheritAnalysisError> {
        let mut resolved: Vec<ResolvedField> = Vec::new();
        let mut seen: HashMap<Name, ResolvedField> = HashMap::new();
        let parents = self.parents_of(struct_name);
        let mut queue: VecDeque<(Name, Vec<Name>)> = parents
            .into_iter()
            .map(|p| (p.clone(), vec![struct_name.clone(), p]))
            .collect();

        while let Some((current, chain)) = queue.pop_front() {
            let base = InheritanceResolver::new(self.env);
            if let Ok(infos) = base.resolve_parents(std::slice::from_ref(&current)) {
                for parent in &infos {
                    for field in &parent.fields {
                        if let Some(existing) = seen.get(&field.name) {
                            if !structural_type_eq(&existing.type_expr, &field.type_expr) {
                                return Err(InheritAnalysisError::FieldTypeConflict {
                                    field: field.name.clone(),
                                    source_a: existing.origin.clone(),
                                    source_b: parent.name.clone(),
                                });
                            }
                        } else {
                            seen.insert(
                                field.name.clone(),
                                ResolvedField {
                                    name: field.name.clone(),
                                    type_expr: field.type_expr.clone(),
                                    origin: parent.name.clone(),
                                    chain: chain.clone(),
                                    is_override: false,
                                },
                            );
                        }
                    }
                }
            }
            for gp in self.parents_of(&current) {
                if chain.len() < self.config.max_depth {
                    let mut c = chain.clone();
                    c.push(gp.clone());
                    queue.push_back((gp, c));
                }
            }
        }

        resolved.extend(seen.into_values());
        for field in own_fields {
            let is_override = resolved.iter().any(|r| r.name == field.name);
            resolved.push(ResolvedField {
                name: field.name.clone(),
                type_expr: field.type_expr.clone(),
                origin: struct_name.clone(),
                chain: vec![struct_name.clone()],
                is_override,
            });
        }
        Ok(resolved)
    }

    /// Analyze field overrides between a child and its parents.
    pub(crate) fn analyze_overrides(
        &self,
        struct_name: &Name,
        own_fields: &[FieldInfo],
        parent_names: &[Name],
    ) -> Result<Vec<OverrideRecord>, InheritAnalysisError> {
        let mut overrides = Vec::new();
        let base = InheritanceResolver::new(self.env);
        let Ok(parent_infos) = base.resolve_parents(parent_names) else {
            return Ok(overrides);
        };
        let own_by_name: HashMap<&Name, &FieldInfo> =
            own_fields.iter().map(|f| (&f.name, f)).collect();
        for parent in &parent_infos {
            for pf in &parent.fields {
                if let Some(own) = own_by_name.get(&pf.name) {
                    overrides.push(OverrideRecord {
                        field: pf.name.clone(),
                        parent_type: pf.type_expr.clone(),
                        child_type: own.type_expr.clone(),
                        parent_struct: parent.name.clone(),
                        child_struct: struct_name.clone(),
                        is_compatible: structural_type_eq(&own.type_expr, &pf.type_expr),
                    });
                }
            }
        }
        Ok(overrides)
    }

    /// Detect diamond patterns and suggest resolution strategies.
    pub(crate) fn detect_diamonds(&self, parent_names: &[Name]) -> Vec<DiamondInfo> {
        if parent_names.len() < 2 {
            return Vec::new();
        }
        let mut ancestor_paths: HashMap<Name, Vec<Vec<Name>>> = HashMap::new();
        for parent in parent_names {
            let mut visited = HashSet::new();
            let mut stack = vec![(parent.clone(), vec![parent.clone()])];
            while let Some((current, path)) = stack.pop() {
                if !visited.insert(current.clone()) {
                    continue;
                }
                ancestor_paths
                    .entry(current.clone())
                    .or_default()
                    .push(path.clone());
                for gp in self.parents_of(&current) {
                    if path.len() < self.config.max_depth {
                        let mut np = path.clone();
                        np.push(gp.clone());
                        stack.push((gp, np));
                    }
                }
            }
        }
        ancestor_paths
            .into_iter()
            .filter(|(_, paths)| paths.len() >= 2)
            .map(|(anc, paths)| {
                let shared = self.field_names_of(&anc);
                let resolution = if shared.is_empty() {
                    DiamondResolution::NoConflict
                } else {
                    self.classify_diamond(&anc, &shared)
                };
                DiamondInfo {
                    ancestor: anc,
                    paths,
                    shared_fields: shared,
                    resolution,
                }
            })
            .collect()
    }

    fn classify_diamond(&self, ancestor: &Name, shared: &[Name]) -> DiamondResolution {
        let base = InheritanceResolver::new(self.env);
        let Ok(infos) = base.resolve_parents(std::slice::from_ref(ancestor)) else {
            return DiamondResolution::NoConflict;
        };
        for parent in &infos {
            let ft: HashMap<&Name, &Expr> = parent
                .fields
                .iter()
                .map(|f| (&f.name, &f.type_expr))
                .collect();
            for name in shared {
                if !ft.contains_key(name) {
                    return DiamondResolution::ExplicitOverride;
                }
            }
        }
        DiamondResolution::Deduplicate
    }

    /// Compute C3 linearization (method resolution order) for `name`.
    pub(crate) fn c3_linearize(&self, name: &Name) -> Result<Vec<Name>, InheritAnalysisError> {
        let mut result = vec![name.clone()];
        let parents = self.parents_of(name);
        if parents.is_empty() {
            return Ok(result);
        }
        let mut lins: Vec<Vec<Name>> = parents
            .iter()
            .map(|p| self.c3_linearize(p))
            .collect::<Result<_, _>>()?;
        lins.push(parents);
        result.extend(self.c3_merge(&mut lins, name)?);
        Ok(result)
    }

    fn c3_merge(
        &self,
        lists: &mut Vec<Vec<Name>>,
        name: &Name,
    ) -> Result<Vec<Name>, InheritAnalysisError> {
        let mut result = Vec::new();
        let max_iter = self.config.max_depth * lists.len().max(1);
        for _ in 0..max_iter {
            lists.retain(|l| !l.is_empty());
            if lists.is_empty() {
                return Ok(result);
            }
            let found = lists.iter().find_map(|list| {
                let head = &list[0];
                let in_tail = lists.iter().any(|o| o.len() > 1 && o[1..].contains(head));
                if !in_tail {
                    Some(head.clone())
                } else {
                    None
                }
            });
            let Some(good) = found else {
                return Err(InheritAnalysisError::LinearizationFailed { name: name.clone() });
            };
            result.push(good.clone());
            for list in lists.iter_mut() {
                if !list.is_empty() && list[0] == good {
                    list.remove(0);
                }
            }
        }
        if lists.iter().any(|l| !l.is_empty()) {
            return Err(InheritAnalysisError::LinearizationFailed { name: name.clone() });
        }
        Ok(result)
    }

    /// Compute inheritance statistics for a structure.
    pub(crate) fn compute_stats(
        &self,
        struct_name: &Name,
        own_fields: &[FieldInfo],
        parent_names: &[Name],
    ) -> Result<InheritStats, InheritAnalysisError> {
        let tree = self.build_tree(struct_name)?;
        let overrides = self.analyze_overrides(struct_name, own_fields, parent_names)?;
        let diamonds = self.detect_diamonds(parent_names);
        let inherited: usize = tree
            .nodes
            .values()
            .filter(|n| n.name != *struct_name)
            .map(|n| n.fields.len())
            .sum();
        Ok(InheritStats {
            max_depth: tree.max_depth,
            max_breadth: tree.max_breadth,
            total_structures: tree.total_nodes,
            total_fields: own_fields.len() + inherited,
            inherited_fields: inherited,
            own_fields: own_fields.len(),
            override_count: overrides.len(),
            diamond_count: diamonds.len(),
        })
    }

    /// Generate DOT format visualization of the inheritance tree.
    pub(crate) fn to_dot(&self, name: &Name) -> Result<String, InheritAnalysisError> {
        let tree = self.build_tree(name)?;
        let mut out = String::new();
        writeln!(out, "digraph inheritance {{").expect("fmt");
        writeln!(out, "  rankdir=BT;").expect("fmt");
        writeln!(out, "  node [shape=record];").expect("fmt");
        for (nn, node) in &tree.nodes {
            let label = if node.fields.is_empty() {
                nn.to_string()
            } else {
                let fl: Vec<String> = node.fields.iter().map(|f| f.to_string()).collect();
                format!("{}|{}", nn, fl.join("\\n"))
            };
            writeln!(out, "  \"{}\" [label=\"{{{}}}\"];", nn, label).expect("fmt");
        }
        for (nn, node) in &tree.nodes {
            for child in &node.children {
                writeln!(out, "  \"{}\" -> \"{}\";", nn, child).expect("fmt");
            }
        }
        writeln!(out, "}}").expect("fmt");
        Ok(out)
    }

    fn field_names_of(&self, name: &Name) -> Vec<Name> {
        self.env
            .get_structure_field_names(name)
            .map(|names| {
                names
                    .iter()
                    .filter(|n| {
                        n.last_component()
                            .map(|c| !c.starts_with("to"))
                            .unwrap_or(true)
                    })
                    .cloned()
                    .collect()
            })
            .unwrap_or_default()
    }

    fn parents_of(&self, name: &Name) -> Vec<Name> {
        let Some(fields) = self.env.get_structure_field_names(name) else {
            return Vec::new();
        };
        fields
            .iter()
            .filter_map(|f| {
                let leaf = f.last_component()?;
                let suffix = leaf.strip_prefix("to")?;
                if suffix.is_empty() {
                    return None;
                }
                let c = Name::from_string(suffix);
                self.env
                    .get_structure_field_names(&c)
                    .is_some()
                    .then_some(c)
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Convenience functions
// ---------------------------------------------------------------------------

/// Check if a structure has any diamond inheritance patterns.
pub(crate) fn has_diamonds(parent_names: &[Name], env: &Environment) -> bool {
    !InheritAnalyzer::with_defaults(env)
        .detect_diamonds(parent_names)
        .is_empty()
}

/// Get the C3 linearization for a structure.
pub(crate) fn linearize(name: &Name, env: &Environment) -> Result<Vec<Name>, InheritAnalysisError> {
    InheritAnalyzer::with_defaults(env).c3_linearize(name)
}

/// Compute inheritance depth for a structure.
pub(crate) fn tree_depth(name: &Name, env: &Environment) -> Result<usize, InheritAnalysisError> {
    Ok(InheritAnalyzer::with_defaults(env)
        .build_tree(name)?
        .max_depth)
}
