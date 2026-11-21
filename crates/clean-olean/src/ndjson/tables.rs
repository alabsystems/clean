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
use std::cell::RefCell;
use std::sync::Arc;

use clean_kernel::expr::{BinderInfo, Expr, ExprFolderOpt, ExprKind, LevelVec};
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
    /// Audit the kernel's simplifying constructors (R125). Keep a written,
    /// imax-free level when the audit finds the same normal form.
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
    /// Simplified levels used by the R125 audit when the terms kept the
    /// written shape. Keep that audit and its work accounting unchanged.
    simplified_levels: HashMap<Level, Level>,
    /// Each level's tree size (an upper bound, saturating).
    level_sizes: HashMap<u64, u64>,
    /// Each level's `imax` nodes as written, every shared subterm unfolded
    /// (an upper bound on the built level's, saturating).
    level_imaxes: HashMap<u64, u64>,
    /// The export's level records' estimated normalization work so far.
    level_work: u64,
    /// Each level as written, as the decline rules read it.
    written_levels: HashMap<u64, Written>,
    /// The levels whose record the kernel's level constructors would rewrite
    /// (`max u u` built as `u`), or that are built on one.
    rewritten_levels: HashSet<u64>,
    /// The level records Lean could tell from the built level.
    level_problems: HashMap<u64, LevelProblem>,
    /// Each level that is, or is built on, one of those: which.
    problem_levels: HashMap<u64, u64>,
    exprs: HashMap<u64, Arc<Expr>>,
    /// Simplified expressions shared across inductive records. Their original
    /// nodes remain owned by `exprs` for the table's lifetime.
    simplified_exprs: RefCell<HashMap<usize, Option<Arc<Expr>>>>,
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
            simplified_levels: HashMap::new(),
            level_sizes,
            level_imaxes,
            level_work: 0,
            written_levels,
            rewritten_levels: HashSet::new(),
            level_problems: HashMap::new(),
            problem_levels: HashMap::new(),
            exprs: HashMap::new(),
            simplified_exprs: RefCell::new(HashMap::new()),
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

    fn simplified_level(&self, line: u64, index: u64) -> Result<Level, NdjsonError> {
        let level = self.level(line, index)?;
        Ok(self.simplified_levels.get(&level).cloned().unwrap_or(level))
    }

    pub(crate) fn expr(&self, line: u64, index: u64) -> Result<Arc<Expr>, NdjsonError> {
        self.exprs
            .get(&index)
            .cloned()
            .ok_or(NdjsonError::UnboundExpr { line, index })
    }

    /// R125 checks an inductive block with the reader's simplified levels
    /// and separately records that such a block cannot be accepted.
    pub(crate) fn inductive_expr(&self, line: u64, index: u64) -> Result<Expr, NdjsonError> {
        let expr = self.expr(line, index)?;
        if self.simplified_levels.is_empty() || !self.mentions_rewritten_level(index) {
            return Ok((*expr).clone());
        }
        let mut memo = self.simplified_exprs.borrow_mut();
        let mut folder = InductiveLevels {
            levels: &self.simplified_levels,
            memo: &mut memo,
        };
        Ok((*folder.fold_expr_arc_opt(&expr).unwrap_or(expr)).clone())
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
    /// Keep the written shape of an imax-free level when the simplifying
    /// constructors leave its Lean normal form intact. The `.olean` loader
    /// preserves that shape, which the native-fold closure digests read.
    /// Record the same [`LevelProblem`], inductive-block rewrites and bounds
    /// from the simplified levels ([`super::levels`]).
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
                    Level::succ(self.simplified_level(line, child)?),
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
                let lhs = self.simplified_level(line, lhs_index)?;
                let rhs = self.simplified_level(line, rhs_index)?;
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
        let written_level = if self.level_build == LevelBuild::Constructors
            && rewritten
            && imaxes == 0
            && !self.problem_levels.contains_key(&index)
        {
            match children.as_slice() {
                [child] => Some(Level::succ(self.level(line, *child)?)),
                [lhs, rhs] => Some(Level::Max(
                    self.level(line, *lhs)?.into(),
                    self.level(line, *rhs)?.into(),
                )),
                _ => None,
            }
        } else {
            None
        };
        let level = match written_level {
            Some(written) => {
                self.simplified_levels.insert(written.clone(), level);
                written
            }
            None => level,
        };
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

struct InductiveLevels<'a> {
    levels: &'a HashMap<Level, Level>,
    memo: &'a mut HashMap<usize, Option<Arc<Expr>>>,
}

impl ExprFolderOpt for InductiveLevels<'_> {
    fn fold_expr_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        let key = addr(expr);
        if let Some(cached) = self.memo.get(&key) {
            return cached.clone();
        }
        let folded = self.fold_expr_opt(expr).map(Arc::new);
        self.memo.insert(key, folded.clone());
        folded
    }

    fn fold_binder_body_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_expr_arc_opt(expr)
    }

    fn fold_sort_opt(&mut self, level: &Level) -> Option<Expr> {
        self.levels.get(level).cloned().map(Expr::sort)
    }

    fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
        if !levels.iter().any(|level| self.levels.contains_key(level)) {
            return None;
        }
        let mapped: LevelVec = levels
            .iter()
            .map(|level| self.levels.get(level).unwrap_or(level).clone())
            .collect();
        Some(Expr::const_(name.clone(), mapped))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;

    fn levels(build: LevelBuild) -> Tables {
        let mut tables = Tables::new(build);
        for (index, data) in [
            (1, r#"{"pre":0,"str":"u"}"#),
            (2, r#"{"pre":0,"str":"u_1"}"#),
        ] {
            tables
                .bind_name(1, index, "str", parse_line(data.as_bytes()).unwrap())
                .unwrap();
        }
        for (index, kind, data) in [
            (1, "param", "1"),
            (2, "param", "2"),
            (3, "succ", "0"),
            (4, "succ", "1"),
            (5, "max", "[3,2]"),
            (6, "max", "[4,2]"),
            (7, "max", "[5,6]"),
            (8, "succ", "7"),
            (9, "imax", "[0,2]"),
            (10, "succ", "9"),
            (11, "max", "[0,0]"),
        ] {
            tables
                .bind_level(1, index, kind, parse_line(data.as_bytes()).unwrap())
                .unwrap();
        }
        tables
    }

    #[test]
    fn replay_keeps_the_written_level_of_list_brec_on_go() {
        let ordinary = levels(LevelBuild::Constructors);
        let reference = levels(LevelBuild::AsWritten);
        // Pinned Init's List.brecOn.go contains
        // max (max 1 u_1) (max (u+1) u_1). Its left operand is subsumed.
        for (preserved, simplified) in [(7, 6), (8, 8)] {
            let actual = ordinary.level(1, preserved).unwrap();
            assert_eq!(actual, reference.level(1, preserved).unwrap());
            let normalized = ordinary.simplified_level(1, simplified).unwrap();
            assert_ne!(actual, normalized);
            assert!(ordinary.rewritten_levels.contains(&preserved));
            assert!(!ordinary.problem_levels.contains_key(&preserved));
        }
        assert_eq!(
            ordinary.simplified_level(1, 7).unwrap(),
            reference.level(1, 6).unwrap()
        );
    }

    #[test]
    fn inductive_replay_reads_the_simplified_view_of_the_same_expression() {
        let mut tables = levels(LevelBuild::Constructors);
        tables
            .bind_expr(1, 0, "sort", parse_line(b"7").unwrap())
            .unwrap();
        tables
            .bind_expr(1, 1, "app", parse_line(br#"{"fn":0,"arg":0}"#).unwrap())
            .unwrap();
        let written = Expr::sort(tables.level(1, 7).unwrap());
        let simplified = Expr::sort(tables.simplified_level(1, 7).unwrap());
        assert_ne!(written, simplified);
        assert_eq!(
            *tables.expr(1, 1).unwrap(),
            Expr::app(written.clone(), written)
        );
        assert_eq!(
            tables.inductive_expr(1, 1).unwrap(),
            Expr::app(simplified.clone(), simplified)
        );
        assert!(tables.mentions_rewritten_level(1));
    }

    #[test]
    fn replay_retains_refusal_accounting_for_imax_and_zero_rewrites() {
        let ordinary = levels(LevelBuild::Constructors);
        assert_eq!(ordinary.level(1, 9).unwrap(), ordinary.level(1, 2).unwrap());
        assert_eq!(ordinary.problem_levels.get(&9), Some(&9));
        assert_eq!(ordinary.problem_levels.get(&10), Some(&10));
        assert!(ordinary.level(1, 11).unwrap().is_zero());
        assert!(matches!(
            ordinary.level_problems.get(&11),
            Some(LevelProblem::ToZero { .. })
        ));
    }
}
