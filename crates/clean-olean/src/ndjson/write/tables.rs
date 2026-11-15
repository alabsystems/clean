// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The writer's internalization tables: every name, level and expression a
//! declaration mentions gets an index, and its record is written once, before
//! the first record that refers to it.
//!
//! Indices are dense and in order of first use, as lean4export assigns them:
//! names from 1 (0 is the anonymous name), levels from 1 (0 is level zero),
//! expressions from 0. A node is identified by its own fields and its
//! children's indices, so two structurally equal terms share one record
//! however the kernel allocated them, and the output is a function of the
//! declarations alone, never of addresses or hash order.
//!
//! What the kernel's terms do not hold is written the one way the format
//! allows: a binder's name as the anonymous name (Clean's `Lam` and `Pi`
//! carry none; Lean's kernel compares binders up to their names), and an
//! `mdata` node with an empty payload (the format defines no reading of one).
//! A binder whose multiplicity is not the unrestricted one, and every
//! expression form outside Lean's (a free variable, the impredicative, cubical
//! and set-theoretic extensions), has no record: the writer refuses it.
//!
//! The walk is iterative: a kernel term is as deep as its longest application
//! spine or binder telescope.

use std::io::Write;
use std::sync::Arc;

use clean_kernel::expr::{BigNat, BinderInfo, Expr, ExprKind, Literal, Multiplicity};
use clean_kernel::name::Name;
use hashbrown::{HashMap, HashSet};
use sha2::{Digest, Sha256};

use super::error::ExportWriteError;
use super::json::Json;

/// A level node: its kind and its children's indices.
#[derive(PartialEq, Eq, Hash)]
enum LevelKey {
    Succ(u64),
    Max(u64, u64),
    IMax(u64, u64),
    Param(u64),
}

/// An expression node: its own fields and its children's indices.
#[derive(PartialEq, Eq, Hash)]
enum ExprKey {
    BVar(u32),
    Sort(u64),
    Const(u64, Vec<u64>),
    App(u64, u64),
    Lam(BinderInfo, u64, u64),
    Pi(BinderInfo, u64, u64),
    Let(u64, u64, u64, u64, bool),
    Proj(u64, u32, u64),
    Nat(BigNat),
    Str(Arc<str>),
    MData(u64),
}

/// The declaration being written: its label for a refusal, and the names its
/// own record declares (a block's members may mention each other).
pub(super) struct Scope<'a> {
    pub(super) label: &'a str,
    pub(super) members: &'a [Name],
}

/// One step of the expression walk.
enum Step<'e> {
    /// Find or build this node; the `Arc` is the one it was reached through.
    Visit(&'e Expr, Option<&'e Arc<Expr>>),
    /// Every child's index is on the result stack: build the node.
    Build(&'e Expr, Option<&'e Arc<Expr>>),
}

/// A name the reader stores otherwise than written, with the name as written
/// (`ExportSource::written_names`).
pub(super) type Spelling = std::collections::HashMap<Name, Name>;

/// What the writer wrote.
pub(super) struct Totals {
    pub(super) bytes: u64,
    pub(super) lines: u64,
    pub(super) sha256: String,
    pub(super) names: usize,
    pub(super) levels: usize,
    pub(super) exprs: usize,
}

/// The output and the three tables.
pub(super) struct Emitter<W> {
    out: W,
    line: Vec<u8>,
    digest: Sha256,
    bytes: u64,
    lines: u64,
    names: HashMap<Name, u64>,
    levels: HashMap<LevelKey, u64>,
    exprs: HashMap<ExprKey, u64>,
    /// The index of each shared node already written, by address. The `Arc` is
    /// held so the address cannot be reused while the entry lives.
    shared: HashMap<usize, (Arc<Expr>, u64)>,
    declared: HashSet<Name>,
    /// A name the NDJSON reader stores otherwise than its export wrote it
    /// (`names.rs`, R118), with the name as written: what is written here.
    spelling: Spelling,
}

impl<W: Write> Emitter<W> {
    /// `spelling` maps a name the reader stored escaped to the name its
    /// export wrote; it is empty for an environment no export was read into.
    pub(super) fn new(out: W, spelling: Spelling) -> Self {
        Self {
            spelling,
            out,
            line: Vec::new(),
            digest: Sha256::new(),
            bytes: 0,
            lines: 0,
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            shared: HashMap::new(),
            declared: HashSet::new(),
        }
    }

    /// Write one record as one line.
    pub(super) fn record(&mut self, record: &Json) -> Result<(), ExportWriteError> {
        self.line.clear();
        record.render(&mut self.line);
        self.line.push(b'\n');
        self.out.write_all(&self.line)?;
        self.digest.update(&self.line);
        self.bytes += self.line.len() as u64;
        self.lines += 1;
        Ok(())
    }

    /// Note that a record declared `names`; a name declared twice is refused.
    pub(super) fn declare(&mut self, names: &[Name]) -> Result<(), ExportWriteError> {
        for name in names {
            if !self.declared.insert(name.clone()) {
                return Err(ExportWriteError::DuplicateDeclaration {
                    name: name.to_unambiguous_string(),
                });
            }
        }
        Ok(())
    }

    /// Flush the output; the bytes written, their SHA-256 and the table sizes.
    pub(super) fn finish(mut self) -> Result<Totals, ExportWriteError> {
        self.out.flush()?;
        let sha256 = self
            .digest
            .finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        Ok(Totals {
            bytes: self.bytes,
            lines: self.lines,
            sha256,
            names: self.names.len(),
            levels: self.levels.len(),
            exprs: self.exprs.len(),
        })
    }

    fn expr_node(
        &mut self,
        key: ExprKey,
        body: (&'static str, Json),
    ) -> Result<u64, ExportWriteError> {
        if let Some(&found) = self.exprs.get(&key) {
            return Ok(found);
        }
        let index = self.exprs.len() as u64;
        self.record(&Json::Object(vec![("ie", Json::Nat(index)), body]))?;
        self.exprs.insert(key, index);
        Ok(index)
    }

    /// Refuse a constant no earlier record declares and this one does not.
    fn check_declared(&self, scope: &Scope<'_>, constant: &Name) -> Result<(), ExportWriteError> {
        if self.declared.contains(constant) || scope.members.contains(constant) {
            return Ok(());
        }
        Err(ExportWriteError::UndeclaredReference {
            declaration: scope.label.to_owned(),
            constant: constant.to_unambiguous_string(),
        })
    }

    /// The index of `root`, writing the records of every node of it not yet
    /// written, children before parents.
    pub(super) fn expr(&mut self, scope: &Scope<'_>, root: &Expr) -> Result<u64, ExportWriteError> {
        let mut steps = vec![Step::Visit(root, None)];
        let mut done: Vec<u64> = Vec::new();
        while let Some(step) = steps.pop() {
            let (shared, built) = match step {
                Step::Visit(node, shared) => {
                    let known =
                        shared.and_then(|arc| self.shared.get(&(Arc::as_ptr(arc) as usize)));
                    if let Some((_, index)) = known {
                        done.push(*index);
                        continue;
                    }
                    let children: [Option<&Arc<Expr>>; 3] = match node.kind() {
                        ExprKind::App(func, arg) => [Some(func), Some(arg), None],
                        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                            [Some(ty), Some(body), None]
                        }
                        ExprKind::Let(_, ty, value, body, _) => [Some(ty), Some(value), Some(body)],
                        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                            [Some(inner), None, None]
                        }
                        _ => [None, None, None],
                    };
                    if children[0].is_none() {
                        (shared, self.leaf(scope, node)?)
                    } else {
                        steps.push(Step::Build(node, shared));
                        // The last pushed is walked first: the children in order.
                        for child in children.into_iter().rev().flatten() {
                            steps.push(Step::Visit(child, Some(child)));
                        }
                        continue;
                    }
                }
                Step::Build(node, shared) => (shared, self.inner(scope, node, &mut done)?),
            };
            if let Some(arc) = shared {
                self.shared
                    .insert(Arc::as_ptr(arc) as usize, (Arc::clone(arc), built));
            }
            done.push(built);
        }
        Ok(done.pop().unwrap_or_default())
    }

    /// A node with no expression children.
    fn leaf(&mut self, scope: &Scope<'_>, node: &Expr) -> Result<u64, ExportWriteError> {
        match node.kind() {
            ExprKind::BVar(index) => {
                let body = ("bvar", Json::Nat(u64::from(*index)));
                self.expr_node(ExprKey::BVar(*index), body)
            }
            ExprKind::Sort(level) => {
                let level = self.level(level)?;
                self.expr_node(ExprKey::Sort(level), ("sort", Json::Nat(level)))
            }
            ExprKind::Const(name, levels) => {
                self.check_declared(scope, name)?;
                let name = self.name(name)?;
                let us: Vec<u64> = levels
                    .iter()
                    .map(|level| self.level(level))
                    .collect::<Result<_, _>>()?;
                let body = Json::Object(vec![("name", Json::Nat(name)), ("us", Json::nats(&us))]);
                self.expr_node(ExprKey::Const(name, us), ("const", body))
            }
            ExprKind::Lit(Literal::Nat(value)) => {
                let text = Json::Str(decimal(value));
                self.expr_node(ExprKey::Nat(value.clone()), ("natVal", text))
            }
            ExprKind::Lit(Literal::String(text)) => {
                let body = ("strVal", Json::Str(text.to_string()));
                self.expr_node(ExprKey::Str(Arc::clone(text)), body)
            }
            other => Err(unexportable(scope, form(other))),
        }
    }

    /// A node whose children's indices are the top of `done`.
    fn inner(
        &mut self,
        scope: &Scope<'_>,
        node: &Expr,
        done: &mut Vec<u64>,
    ) -> Result<u64, ExportWriteError> {
        let mut pop = || done.pop().unwrap_or_default();
        match node.kind() {
            ExprKind::App(..) => {
                let arg = pop();
                let func = pop();
                let body = Json::Object(vec![("fn", Json::Nat(func)), ("arg", Json::Nat(arg))]);
                self.expr_node(ExprKey::App(func, arg), ("app", body))
            }
            ExprKind::Lam(binder, ..) | ExprKind::Pi(binder, ..) => {
                let body = pop();
                let ty = pop();
                if binder.mult != Multiplicity::Many {
                    let what = format!("a binder of multiplicity {:?}", binder.mult);
                    return Err(unexportable(scope, &what));
                }
                let info = match binder.info {
                    BinderInfo::Default => "default",
                    BinderInfo::Implicit => "implicit",
                    BinderInfo::StrictImplicit => "strictImplicit",
                    BinderInfo::InstImplicit => "instImplicit",
                };
                let fields = Json::Object(vec![
                    ("name", Json::Nat(0)),
                    ("type", Json::Nat(ty)),
                    ("body", Json::Nat(body)),
                    ("binderInfo", Json::Str(info.to_owned())),
                ]);
                if matches!(node.kind(), ExprKind::Lam(..)) {
                    self.expr_node(ExprKey::Lam(binder.info, ty, body), ("lam", fields))
                } else {
                    self.expr_node(ExprKey::Pi(binder.info, ty, body), ("forallE", fields))
                }
            }
            ExprKind::Let(name, _, _, _, nondep) => {
                let body = pop();
                let value = pop();
                let ty = pop();
                let name = self.name(name)?;
                let fields = Json::Object(vec![
                    ("name", Json::Nat(name)),
                    ("type", Json::Nat(ty)),
                    ("value", Json::Nat(value)),
                    ("body", Json::Nat(body)),
                    ("nondep", Json::Bool(*nondep)),
                ]);
                let key = ExprKey::Let(name, ty, value, body, *nondep);
                self.expr_node(key, ("letE", fields))
            }
            ExprKind::Proj(type_name, index, _) => {
                let structure = pop();
                self.check_declared(scope, type_name)?;
                let type_name = self.name(type_name)?;
                let fields = Json::Object(vec![
                    ("typeName", Json::Nat(type_name)),
                    ("idx", Json::Nat(u64::from(*index))),
                    ("struct", Json::Nat(structure)),
                ]);
                let key = ExprKey::Proj(type_name, *index, structure);
                self.expr_node(key, ("proj", fields))
            }
            ExprKind::MData(..) => {
                let inner = pop();
                let fields = Json::Object(vec![
                    ("expr", Json::Nat(inner)),
                    ("data", Json::Object(Vec::new())),
                ]);
                self.expr_node(ExprKey::MData(inner), ("mdata", fields))
            }
            other => Err(unexportable(scope, form(other))),
        }
    }
}

fn unexportable(scope: &Scope<'_>, what: &str) -> ExportWriteError {
    ExportWriteError::Unexportable {
        declaration: scope.label.to_owned(),
        what: what.to_owned(),
    }
}

/// A natural literal in decimal, as `natVal` spells it.
fn decimal(value: &BigNat) -> String {
    match value.to_u64() {
        Some(small) => small.to_string(),
        None => {
            let bytes: Vec<u8> = value
                .limbs()
                .iter()
                .flat_map(|limb| limb.to_le_bytes())
                .collect();
            num_bigint::BigUint::from_bytes_le(&bytes).to_string()
        }
    }
}

/// What an expression form outside Lean's language is, for a refusal.
fn form(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::FVar(_) => "a free variable",
        _ => "an expression form outside Lean's (impredicative, cubical or set-theoretic)",
    }
}

mod names;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tables_big_literals_are_written_in_decimal() {
        assert_eq!(decimal(&BigNat::from_u64(0)), "0");
        assert_eq!(decimal(&BigNat::from_u64(u64::MAX)), "18446744073709551615");
        let big = BigNat::from_limbs(vec![0, 1]);
        assert_eq!(decimal(&big), "18446744073709551616");
        let read = crate::ndjson::natval::parse_nat_literal(&decimal(&big)).expect("decimal");
        assert_eq!(read, big);
    }
}
