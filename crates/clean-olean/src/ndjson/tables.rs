// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The export's internalization tables: names (`in`), levels (`il`) and
//! expressions (`ie`), and the primitive records that bind them.
//!
//! An index is a key, not a position: indices may be sparse and bound in any
//! order (the arena's `good/other/sparse-name-index` and
//! `good/other/level-index-out-of-order` are accept tests). An index may be
//! bound only once, the predefined index 0 of the name table (the anonymous
//! name) and of the level table (level zero) included (lean4#15542). A
//! reference must name an index an earlier line bound.
//!
//! Expressions are hash-consed: a node structurally equal to one already
//! built is the same `Arc`, so a table that spells one term under many indices
//! costs one node, and the kernel's pointer-equality fast paths see sharing.
//! The hash-consing key is SHALLOW (the node's own fields and its children's
//! addresses), never the kernel's 32-bit metadata hash with a deep equality
//! walk: lets that differ only in their names, or lambdas that differ only in
//! binder information, share that hash, and a reader keyed on it goes
//! quadratic on adversarial input.
//!
//! Cost bounds: a level's tree, counted with every shared subterm unfolded
//! (as the kernel's hashing and normalization walk it), and a `const`'s levels
//! together, stay under [`MAX_LEVEL_TREE_NODES`]; a few lines of `imax`
//! records otherwise build a level DAG whose tree has `2^64` nodes. A level
//! record's flattened `max` has at most
//! [`super::levels::MAX_LEVEL_COMPOSITE_ARGS`] composite arguments, so the
//! constructors' normalization of it costs a bounded amount.
//!
//! Names are stored so that they read back as themselves
//! ([`super::names`]); levels are built with the kernel's constructors, and a
//! rewrite Lean could tell is recorded, with every level and expression over
//! it ([`super::levels`]).

mod expr;

use expr::unknown;
use std::sync::Arc;

use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use hashbrown::{HashMap, HashSet};

use super::error::NdjsonError;
use super::fields::{nat_value, Fields};
use super::json::JsonValue;
use super::levels::{
    composite_args, level_record_work, rewrite_problem, surely_nonzero, LevelProblem, Written,
    MAX_LEVEL_COMPOSITE_ARGS, MAX_LEVEL_WORK,
};
use super::names::stored_component;
use super::natval::{parse_nat_literal, NatTextError, MAX_NAT_LITERAL_DIGITS};

/// The largest level tree (nodes, every shared subterm unfolded) a level
/// record, or a `const` record's levels together, may build. Lean's own levels
/// have tens of nodes (the Round 2026-09 archive's largest has 30, Lean
/// core's 51).
pub const MAX_LEVEL_TREE_NODES: u64 = 256;

/// A hash-consing key: a node's own fields and its children's addresses. Every
/// child is an interned `Arc` the tables keep alive, so two nodes are
/// structurally equal exactly when their keys are equal.
#[derive(PartialEq, Eq, Hash)]
enum NodeKey {
    BVar(u32),
    Sort(Level),
    Const(Name, Vec<Level>),
    App(usize, usize),
    Lam(BinderInfo, usize, usize),
    Pi(BinderInfo, usize, usize),
    Let(Name, usize, usize, usize, bool),
    Proj(Name, u32, usize),
    MData(usize),
}

/// A built expression: the node, its hash-consing key, whether it mentions a
/// rewritten level, and a level Lean could tell from the built one that it
/// mentions.
type Built = (Expr, Option<NodeKey>, bool, Option<u64>);

fn addr(e: &Arc<Expr>) -> usize {
    Arc::as_ptr(e) as usize
}

/// How a `max`/`imax` level record is built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LevelBuild {
    /// Through the kernel's simplifying constructors, with every rewrite
    /// Lean could tell marked (`levels.rs`, R125): the front door.
    Constructors,
    /// Node for node, as the record states it and as the `.olean` loader
    /// builds a stored level since R150 (`import/convert_expr.rs`,
    /// `convert_level`). Nothing is rewritten, so nothing is marked. For a
    /// consumer that hands the terms to the fenced reference entry, whose
    /// level algebra is pinned Lean's, or that compares them with what was
    /// written.
    AsWritten,
}

/// The three tables.
pub(crate) struct Tables {
    level_build: LevelBuild,
    /// Each name as stored ([`super::names`]).
    names: HashMap<u64, Name>,
    /// Each stored name's name as written, for every name bound.
    written_names: HashMap<Name, Name>,
    levels: HashMap<u64, Level>,
    /// Each level's tree size (an upper bound, saturating).
    level_sizes: HashMap<u64, u64>,
    /// Each level's `imax` nodes as written, every shared subterm unfolded
    /// (an upper bound on the built level's, saturating).
    level_imaxes: HashMap<u64, u64>,
    /// The export's level records' estimated normalization work so far.
    level_work: u64,
    /// Each level as written, as the decline rules read it.
    written_levels: HashMap<u64, Written>,
    /// The levels whose record the kernel's level constructors rewrote
    /// (`max u u` built as `u`), or that are built on one.
    rewritten_levels: HashSet<u64>,
    /// The level records Lean could tell from the built level.
    level_problems: HashMap<u64, LevelProblem>,
    /// Each level that is, or is built on, one of those: which.
    problem_levels: HashMap<u64, u64>,
    exprs: HashMap<u64, Arc<Expr>>,
    /// The expressions that mention a rewritten level.
    rewritten_exprs: HashSet<u64>,
    /// The expressions that mention a level of `problem_levels`: which.
    problem_exprs: HashMap<u64, u64>,
    interned: HashMap<NodeKey, Arc<Expr>>,
}

impl Tables {
    pub(crate) fn new(level_build: LevelBuild) -> Self {
        let mut names = HashMap::new();
        names.insert(0, Name::anon());
        let mut written_names = HashMap::new();
        written_names.insert(Name::anon(), Name::anon());
        let mut levels = HashMap::new();
        levels.insert(0, Level::zero());
        let mut level_sizes = HashMap::new();
        level_sizes.insert(0, 1);
        let mut level_imaxes = HashMap::new();
        level_imaxes.insert(0, 0);
        let mut written_levels = HashMap::new();
        written_levels.insert(0, Written::zero());
        Self {
            level_build,
            names,
            written_names,
            levels,
            level_sizes,
            level_imaxes,
            level_work: 0,
            written_levels,
            rewritten_levels: HashSet::new(),
            level_problems: HashMap::new(),
            problem_levels: HashMap::new(),
            exprs: HashMap::new(),
            rewritten_exprs: HashSet::new(),
            problem_exprs: HashMap::new(),
            interned: HashMap::new(),
        }
    }

    /// Whether expression `index` mentions a level the reader rewrote.
    pub(crate) fn mentions_rewritten_level(&self, index: u64) -> bool {
        self.rewritten_exprs.contains(&index)
    }

    /// A level Lean could tell from the built one that expression `index`
    /// mentions, if any.
    pub(crate) fn level_problem(&self, index: u64) -> Option<&LevelProblem> {
        self.problem_exprs
            .get(&index)
            .and_then(|level| self.level_problems.get(level))
    }

    /// The name a stored name was written as.
    pub(crate) fn written_name<'a>(&'a self, stored: &'a Name) -> &'a Name {
        self.written_names.get(stored).unwrap_or(stored)
    }

    /// A stored name, rendered unambiguously as written.
    pub(crate) fn shown(&self, stored: &Name) -> String {
        self.written_name(stored).to_unambiguous_string()
    }

    /// The stored names that differ from their written names, with those.
    pub(crate) fn escaped_names(&self) -> std::collections::HashMap<Name, Name> {
        self.written_names
            .iter()
            .filter(|(stored, written)| stored != written)
            .map(|(stored, written)| (stored.clone(), written.clone()))
            .collect()
    }

    fn written_level(&self, line: u64, index: u64) -> Result<&Written, NdjsonError> {
        self.written_levels
            .get(&index)
            .ok_or(NdjsonError::UnboundLevel { line, index })
    }

    fn level_imax_count(&self, line: u64, index: u64) -> Result<u64, NdjsonError> {
        self.level_imaxes
            .get(&index)
            .copied()
            .ok_or(NdjsonError::UnboundLevel { line, index })
    }

    fn level_size(&self, line: u64, index: u64) -> Result<u64, NdjsonError> {
        self.level_sizes
            .get(&index)
            .copied()
            .ok_or(NdjsonError::UnboundLevel { line, index })
    }

    pub(crate) fn name(&self, line: u64, index: u64) -> Result<Name, NdjsonError> {
        self.names
            .get(&index)
            .cloned()
            .ok_or(NdjsonError::UnboundName { line, index })
    }

    pub(crate) fn level(&self, line: u64, index: u64) -> Result<Level, NdjsonError> {
        self.levels
            .get(&index)
            .cloned()
            .ok_or(NdjsonError::UnboundLevel { line, index })
    }

    pub(crate) fn expr(&self, line: u64, index: u64) -> Result<Arc<Expr>, NdjsonError> {
        self.exprs
            .get(&index)
            .cloned()
            .ok_or(NdjsonError::UnboundExpr { line, index })
    }

    pub(crate) fn names_of(&self, line: u64, indices: &[u64]) -> Result<Vec<Name>, NdjsonError> {
        indices.iter().map(|&i| self.name(line, i)).collect()
    }

    fn intern(&mut self, expr: Expr, key: Option<NodeKey>) -> Arc<Expr> {
        match key {
            Some(key) => Arc::clone(self.interned.entry(key).or_insert_with(|| Arc::new(expr))),
            None => Arc::new(expr),
        }
    }

    /// A name record (`{"in": i, "str"|"num": ...}`).
    pub(crate) fn bind_name(
        &mut self,
        line: u64,
        index: u64,
        kind: &str,
        data: JsonValue,
    ) -> Result<(), NdjsonError> {
        let (stored, written) = match kind {
            "str" => {
                let mut f = Fields::new(line, "Name.str", data)?;
                let pre = f.nat("pre")?;
                let component = f.string("str")?;
                f.finish()?;
                let parent = self.name(line, pre)?;
                let written = self.written_name(&parent).clone().str(&component);
                (parent.str(stored_component(&component)), written)
            }
            "num" => {
                let mut f = Fields::new(line, "Name.num", data)?;
                let pre = f.nat("pre")?;
                let i = f.nat("i")?;
                f.finish()?;
                let parent = self.name(line, pre)?;
                let written = self.written_name(&parent).clone().num(i);
                (parent.num(i), written)
            }
            other => return Err(unknown(line, "in", other)),
        };
        if self.names.contains_key(&index) {
            return Err(NdjsonError::NameIndexRebound { line, index });
        }
        match self.written_names.get(&stored) {
            Some(other) if *other != written => {
                return Err(NdjsonError::NameCollision {
                    line,
                    name: written.to_unambiguous_string(),
                    other: other.to_unambiguous_string(),
                })
            }
            Some(_) => {}
            None => {
                self.written_names.insert(stored.clone(), written);
            }
        }
        self.names.insert(index, stored);
        Ok(())
    }

    /// A level record (`{"il": i, "succ"|"max"|"imax"|"param": ...}`).
    ///
    /// Built with the kernel's level constructors, exactly as the `.olean`
    /// loader builds them (`import::convert_expr::convert_level`), so a
    /// declaration reads the same through either front door: the content
    /// digests native-fold authority keys `Nat.add`'s reductions on
    /// (`env/native_fold_canon.tsv`) are taken over `.olean`-loaded terms.
    /// A rewrite Lean could tell from the level as written is recorded as a
    /// [`LevelProblem`], and every rewritten level is recorded, so a
    /// declaration over the one and an inductive block over the other keep the
    /// export from being accepted ([`super::levels`]). The tree's size and its
    /// composite `max` arguments are bounded before anything is built, and
    /// decline.
    pub(crate) fn bind_level(
        &mut self,
        line: u64,
        index: u64,
        kind: &str,
        data: JsonValue,
    ) -> Result<(), NdjsonError> {
        let (level, size, imaxes, written, rewritten, shape, children, to_zero) = match kind {
            "succ" => {
                let child = nat_value(line, "Level.succ", "succ", &data)?;
                let size = self.level_size(line, child)?.saturating_add(1);
                self.check_level_size(line, size)?;
                (
                    Level::succ(self.level(line, child)?),
                    size,
                    self.level_imax_count(line, child)?,
                    self.written_level(line, child)?.succ(),
                    self.rewritten_levels.contains(&child),
                    format!("succ of level {child}"),
                    vec![child],
                    None,
                )
            }
            "param" => {
                let name = self.name(line, nat_value(line, "Level.param", "param", &data)?)?;
                let written = Written::param(&name);
                (
                    Level::param(name),
                    1,
                    0,
                    written,
                    false,
                    String::new(),
                    Vec::new(),
                    None,
                )
            }
            "max" | "imax" => {
                let record = if kind == "max" {
                    "Level.max"
                } else {
                    "Level.imax"
                };
                let pair = match data {
                    JsonValue::Array(items) if items.len() == 2 => items,
                    other => {
                        return Err(NdjsonError::Field {
                            line,
                            record,
                            field: kind.to_owned(),
                            problem: format!(
                                "expected an array of two level indices, found {}",
                                other.type_name()
                            ),
                        })
                    }
                };
                let lhs_index = nat_value(line, record, kind, &pair[0])?;
                let rhs_index = nat_value(line, record, kind, &pair[1])?;
                let size = self
                    .level_size(line, lhs_index)?
                    .saturating_add(self.level_size(line, rhs_index)?)
                    .saturating_add(1);
                self.check_level_size(line, size)?;
                let lhs = self.level(line, lhs_index)?;
                let rhs = self.level(line, rhs_index)?;
                let args = composite_args(&lhs).saturating_add(composite_args(&rhs));
                if args > MAX_LEVEL_COMPOSITE_ARGS {
                    return Err(NdjsonError::LevelArgsBudget {
                        line,
                        args,
                        limit: MAX_LEVEL_COMPOSITE_ARGS,
                    });
                }
                let operand_imaxes = self
                    .level_imax_count(line, lhs_index)?
                    .saturating_add(self.level_imax_count(line, rhs_index)?);
                let normalizes = kind == "max" || surely_nonzero(&rhs);
                self.level_work = self.level_work.saturating_add(level_record_work(
                    size,
                    operand_imaxes,
                    normalizes,
                ));
                if self.level_work > MAX_LEVEL_WORK {
                    return Err(NdjsonError::LevelWorkBudget {
                        line,
                        work: self.level_work,
                        limit: MAX_LEVEL_WORK,
                    });
                }
                let (lhs_written, rhs_written) = (
                    self.written_level(line, lhs_index)?,
                    self.written_level(line, rhs_index)?,
                );
                let written = if kind == "max" {
                    lhs_written.max(rhs_written)
                } else {
                    Written::Imax
                };
                let built = match (self.level_build, kind == "max") {
                    (LevelBuild::Constructors, true) => Level::max(lhs.clone(), rhs.clone()),
                    (LevelBuild::Constructors, false) => Level::imax(lhs.clone(), rhs.clone()),
                    (LevelBuild::AsWritten, true) => {
                        Level::Max(lhs.clone().into(), rhs.clone().into())
                    }
                    (LevelBuild::AsWritten, false) => {
                        Level::IMax(lhs.clone().into(), rhs.clone().into())
                    }
                };
                let to_zero = built.is_zero().then_some(record);
                // The record as written, unless the constructor rewrote it.
                let as_written = match (&built, kind) {
                    (Level::Max(a, b), "max") | (Level::IMax(a, b), "imax") => {
                        **a == lhs && **b == rhs
                    }
                    _ => false,
                };
                let rewritten = !as_written
                    || self.rewritten_levels.contains(&lhs_index)
                    || self.rewritten_levels.contains(&rhs_index);
                (
                    built,
                    size,
                    operand_imaxes.saturating_add(u64::from(kind == "imax")),
                    written,
                    rewritten,
                    format!("{kind} of levels {lhs_index} and {rhs_index}"),
                    vec![lhs_index, rhs_index],
                    to_zero,
                )
            }
            other => return Err(unknown(line, "il", other)),
        };
        if self.levels.contains_key(&index) {
            return Err(NdjsonError::LevelIndexRebound { line, index });
        }
        let own = match to_zero {
            Some(record) => Some(LevelProblem::ToZero { index, record }),
            None if rewritten => {
                rewrite_problem(&written, &level).map(|why| LevelProblem::LeanVisible {
                    index,
                    written: shape,
                    built: level.to_string(),
                    why,
                })
            }
            None => None,
        };
        if let Some(problem) = own {
            self.level_problems.insert(index, problem);
            self.problem_levels.insert(index, index);
        } else if let Some(source) = children
            .iter()
            .find_map(|c| self.problem_levels.get(c).copied())
        {
            self.problem_levels.insert(index, source);
        }
        self.levels.insert(index, level);
        self.level_sizes.insert(index, size);
        self.level_imaxes.insert(index, imaxes);
        self.written_levels.insert(index, written);
        if rewritten {
            self.rewritten_levels.insert(index);
        }
        Ok(())
    }

    fn check_level_size(&self, line: u64, nodes: u64) -> Result<(), NdjsonError> {
        if nodes > MAX_LEVEL_TREE_NODES {
            return Err(NdjsonError::LevelBudget {
                line,
                nodes,
                limit: MAX_LEVEL_TREE_NODES,
            });
        }
        Ok(())
    }
}
