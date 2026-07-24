// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual definition blocks with dependency graph analysis.
//!
//! Provides higher-level abstractions for `mutual ... end` blocks and `where`
//! helper definitions. The core responsibilities are:
//!
//! 1. **Dependency graph construction** — scan declaration bodies for
//!    cross-references to sibling declarations within the same mutual block.
//! 2. **Well-founded recursion check** — verify that the dependency graph has
//!    no ill-formed cycles that would prevent termination checking.
//! 3. **Elaboration orchestration** — drive the two-pass elaboration via
//!    [`ElabCtx::elab_mutual`] and return collected results.
//!
//! # Lean 4 Reference
//!
//! Lean 4 `src/Lean/Elab/MutualDef.lean` performs a similar analysis:
//! - `elabMutualDef` collects headers, builds a dependency graph, and checks
//!   well-foundedness before elaborating bodies.
//! - `where` clauses are desugared to `let rec` bindings in
//!   `elabWhereDeclsAsLetRec`.
//!
//! This module is the clean equivalent at the declaration-level (above the
//! expression elaborator in `infer/elab_mutual.rs`).

use crate::dep_graph::DependencyGraph;
use crate::error::ElabError;
use crate::infer::{ElabCtx, ElabResult};
use clean_kernel::Expr;
use clean_parser::{SurfaceDecl, SurfaceExpr};
use std::collections::HashSet;

/// A single entry in a mutual definition block.
///
/// Captures the declaration's name, optional elaborated type, body expression,
/// and whether it is marked `noncomputable`.
#[derive(Debug, Clone)]
pub(crate) struct MutualEntry {
    /// Declaration name (unqualified).
    pub(crate) name: String,
    /// Optional type annotation (kernel `Expr` after elaboration, or `None`
    /// if the type should be inferred).
    pub(crate) ty: Option<Expr>,
    /// Body expression (kernel `Expr`).
    pub(crate) body: Expr,
    /// Whether this entry carries the `noncomputable` modifier.
    pub(crate) is_noncomputable: bool,
}

/// A `mutual ... end` block with dependency analysis.
///
/// # Usage
///
/// ```text
/// let mut block = MutualBlock::new();
/// block.add_entry(entry_a);
/// block.add_entry(entry_b);
/// block.build_dep_graph();
/// block.check_well_founded()?;
/// let results = block.elaborate_all(&mut ctx)?;
/// ```
#[derive(Debug, Clone)]
pub(crate) struct MutualBlock {
    /// Ordered declarations in this mutual block.
    pub(crate) declarations: Vec<MutualEntry>,
    /// Dependency graph (populated by [`build_dep_graph`]).
    pub(crate) dep_graph: DependencyGraph,
}

impl MutualBlock {
    /// Create an empty mutual block.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            declarations: Vec::new(),
            dep_graph: DependencyGraph::new(),
        }
    }

    /// Add an entry to the mutual block.
    pub(crate) fn add_entry(&mut self, entry: MutualEntry) {
        self.declarations.push(entry);
    }

    /// Build the dependency graph by scanning each entry's body for references
    /// to sibling declaration names.
    ///
    /// This must be called after all entries have been added.
    pub(crate) fn build_dep_graph(&mut self) {
        let names: Vec<&str> = self.declarations.iter().map(|e| e.name.as_str()).collect();
        self.dep_graph = DependencyGraph::new();

        for (from_idx, entry) in self.declarations.iter().enumerate() {
            let mut referenced = HashSet::new();
            collect_const_refs(&entry.body, &names, &mut referenced);
            for to_idx in referenced {
                if to_idx != from_idx {
                    self.dep_graph.add_edge(from_idx, to_idx);
                }
            }
        }
    }

    /// Check that the mutual block is well-founded.
    ///
    /// Rejects empty blocks and mixed computable/noncomputable cycles.
    /// Pure mutual recursion (all computable or all noncomputable) is accepted
    /// since the recursion compiler in `wf_recursion/` handles termination.
    pub(crate) fn check_well_founded(&self) -> Result<(), ElabError> {
        if self.declarations.is_empty() {
            return Err(ElabError::NotImplemented("empty mutual block".to_string()));
        }

        let n = self.declarations.len();

        if let Some(cycle) = self.dep_graph.find_cycle(n) {
            let has_computable = cycle
                .iter()
                .any(|&i| i < n && !self.declarations[i].is_noncomputable);
            let has_noncomputable = cycle
                .iter()
                .any(|&i| i < n && self.declarations[i].is_noncomputable);

            if has_computable && has_noncomputable {
                let cycle_names: Vec<&str> = cycle
                    .iter()
                    .filter(|&&i| i < n)
                    .map(|&i| self.declarations[i].name.as_str())
                    .collect();
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "mutual recursion between computable and noncomputable \
                         declarations: {}",
                        cycle_names.join(", ")
                    ),
                });
            }
        }

        Ok(())
    }

    /// Elaborate all declarations in this mutual block.
    ///
    /// Wraps entries into a `SurfaceDecl::Mutual` and delegates to
    /// [`ElabCtx::elab_decl`] which dispatches to the two-pass mutual
    /// elaboration in `infer/elab_mutual.rs`.
    pub(crate) fn elaborate_all(
        &self,
        ctx: &mut ElabCtx<'_>,
    ) -> Result<Vec<ElabResult>, ElabError> {
        if self.declarations.is_empty() {
            return Ok(Vec::new());
        }

        let dummy = clean_parser::Span::dummy();
        let surface_decls: Vec<SurfaceDecl> = self
            .declarations
            .iter()
            .map(|entry| SurfaceDecl::Def {
                span: dummy,
                name: entry.name.clone(),
                universe_params: Vec::new(),
                binders: Vec::new(),
                ty: entry
                    .ty
                    .as_ref()
                    .map(|_| Box::new(SurfaceExpr::Hole(dummy))),
                val: Box::new(SurfaceExpr::Hole(dummy)),
                where_decls: Vec::new(),
                attrs: Vec::new(),
                termination: clean_parser::TerminationHints::default(),
                modifiers: clean_parser::DeclModifiers::default(),
            })
            .collect();

        let mutual_decl = SurfaceDecl::Mutual {
            span: dummy,
            decls: surface_decls,
        };

        match ctx.elab_decl(&mutual_decl)? {
            ElabResult::Multiple(results) => Ok(results),
            single => Ok(vec![single]),
        }
    }

    /// Return the number of declarations in this block.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Check if this block is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }

    /// Return the names of all declarations in this block.
    #[must_use]
    pub(crate) fn names(&self) -> Vec<&str> {
        self.declarations.iter().map(|e| e.name.as_str()).collect()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Dependency reference scanning
// ─────────────────────────────────────────────────────────────────────────────

/// Collect references to declarations in `names` that appear as `Const`
/// expressions in `expr`.
fn collect_const_refs(expr: &Expr, names: &[&str], out: &mut HashSet<usize>) {
    match expr.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            for (idx, &decl_name) in names.iter().enumerate() {
                if name_str == decl_name || name_str.ends_with(&format!(".{decl_name}")) {
                    out.insert(idx);
                }
            }
        }
        clean_kernel::expr::ExprKind::App(f, a) => {
            collect_const_refs(f, names, out);
            collect_const_refs(a, names, out);
        }
        clean_kernel::expr::ExprKind::Lam(_, ty, body)
        | clean_kernel::expr::ExprKind::Pi(_, ty, body) => {
            collect_const_refs(ty, names, out);
            collect_const_refs(body, names, out);
        }
        clean_kernel::expr::ExprKind::Let(_, ty, val, body, _) => {
            collect_const_refs(ty, names, out);
            collect_const_refs(val, names, out);
            collect_const_refs(body, names, out);
        }
        clean_kernel::expr::ExprKind::MData(_, e) | clean_kernel::expr::ExprKind::Proj(_, _, e) => {
            collect_const_refs(e, names, out);
        }
        _ => {}
    }
}

/// Collect identifier references from a surface expression for pre-elaboration
/// dependency analysis.
pub(crate) fn collect_surface_refs(expr: &SurfaceExpr, names: &[&str], out: &mut HashSet<usize>) {
    match expr {
        SurfaceExpr::Ident(_, name) => {
            for (idx, &decl_name) in names.iter().enumerate() {
                if name == decl_name {
                    out.insert(idx);
                }
            }
        }
        SurfaceExpr::App(_, f, args) => {
            collect_surface_refs(f, names, out);
            for arg in args {
                collect_surface_refs(&arg.expr, names, out);
            }
        }
        SurfaceExpr::Lambda(_, _binders, body) | SurfaceExpr::Pi(_, _binders, body) => {
            collect_surface_refs(body, names, out);
        }
        SurfaceExpr::Let(_, _binder, val, body) | SurfaceExpr::LetRec(_, _binder, val, body) => {
            collect_surface_refs(val, names, out);
            collect_surface_refs(body, names, out);
        }
        SurfaceExpr::If(_, cond, then_, else_) => {
            collect_surface_refs(cond, names, out);
            collect_surface_refs(then_, names, out);
            collect_surface_refs(else_, names, out);
        }
        SurfaceExpr::Match(_, _, scrut, arms) => {
            collect_surface_refs(scrut, names, out);
            for arm in arms {
                collect_surface_refs(&arm.body, names, out);
            }
        }
        SurfaceExpr::Paren(_, inner) => {
            collect_surface_refs(inner, names, out);
        }
        _ => {}
    }
}

/// Build a [`MutualBlock`] from a slice of surface declarations.
///
/// The returned block has a pre-built dependency graph. Callers should
/// call [`MutualBlock::check_well_founded`] before elaboration.
#[must_use]
pub(crate) fn build_mutual_block_from_surface(decls: &[SurfaceDecl]) -> MutualBlock {
    let mut block = MutualBlock::new();

    let names: Vec<&str> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();

    for decl in decls {
        let (name, body_expr, is_noncomp) = match decl {
            SurfaceDecl::Def {
                name,
                val,
                modifiers,
                ..
            } => (name, &**val, modifiers.is_noncomputable),
            SurfaceDecl::Theorem {
                name,
                proof,
                modifiers,
                ..
            } => (name, &**proof, modifiers.is_noncomputable),
            _ => continue,
        };

        block.add_entry(MutualEntry {
            name: name.clone(),
            ty: None,
            body: Expr::sort(clean_kernel::Level::zero()),
            is_noncomputable: is_noncomp,
        });

        let from_idx = block.declarations.len() - 1;
        let mut refs = HashSet::new();
        collect_surface_refs(body_expr, &names, &mut refs);
        for to_idx in refs {
            if to_idx != from_idx {
                block.dep_graph.add_edge(from_idx, to_idx);
            }
        }
    }

    block
}

#[cfg(test)]
#[path = "mutual_decl_tests.rs"]
mod tests;
