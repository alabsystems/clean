// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The name and level tables of the writer (`super`): each record after the
//! records it refers to, an index given on first use.

use std::io::Write;

use clean_kernel::level::Level;
use clean_kernel::name::{Name, NameInner};

use super::{Emitter, LevelKey};
use crate::ndjson::names::ESCAPE;
use crate::ndjson::write::error::ExportWriteError;
use crate::ndjson::write::json::Json;

/// One step of the level walk.
enum LevelStep<'l> {
    Visit(&'l Level),
    Build(&'l Level),
}

impl<W: Write> Emitter<W> {
    /// The index of `name`, writing its record (and its prefixes') if new.
    pub(in crate::ndjson::write) fn name(&mut self, name: &Name) -> Result<u64, ExportWriteError> {
        let mut missing: Vec<&Name> = Vec::new();
        let mut current = name;
        let mut index = loop {
            if current.is_anon() {
                break 0;
            }
            if let Some(&found) = self.names.get(current) {
                break found;
            }
            missing.push(current);
            match current.inner() {
                NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent,
                NameInner::Anon => break 0,
            }
        };
        while let Some(next) = missing.pop() {
            let body = match next.inner() {
                NameInner::Str(_, component) => {
                    let written = match self.spelling.get(next).map(Name::inner) {
                        Some(NameInner::Str(_, written)) => written.to_string(),
                        _ if component.starts_with(ESCAPE) => {
                            return Err(ExportWriteError::Unexportable {
                                declaration: next.to_unambiguous_string(),
                                what: "a name component that begins with U+2024, the form the \
                                       export reader stores another spelling in (R118), with \
                                       no record of the spelling"
                                    .to_owned(),
                            });
                        }
                        _ => component.to_string(),
                    };
                    (
                        "str",
                        Json::Object(vec![("pre", Json::Nat(index)), ("str", Json::Str(written))]),
                    )
                }
                NameInner::Num(_, i) => (
                    "num",
                    Json::Object(vec![("pre", Json::Nat(index)), ("i", Json::Nat(*i))]),
                ),
                NameInner::Anon => continue,
            };
            index = self.names.len() as u64 + 1;
            self.record(&Json::Object(vec![("in", Json::Nat(index)), body]))?;
            self.names.insert(next.clone(), index);
        }
        Ok(index)
    }

    /// The indices of `names`, in order.
    pub(in crate::ndjson::write) fn names(
        &mut self,
        names: &[Name],
    ) -> Result<Vec<u64>, ExportWriteError> {
        names.iter().map(|name| self.name(name)).collect()
    }

    fn level_node(
        &mut self,
        key: LevelKey,
        body: (&'static str, Json),
    ) -> Result<u64, ExportWriteError> {
        if let Some(&found) = self.levels.get(&key) {
            return Ok(found);
        }
        let index = self.levels.len() as u64 + 1;
        self.record(&Json::Object(vec![("il", Json::Nat(index)), body]))?;
        self.levels.insert(key, index);
        Ok(index)
    }

    /// The index of `level`, writing its record (and its operands') if new.
    pub(in crate::ndjson::write) fn level(
        &mut self,
        level: &Level,
    ) -> Result<u64, ExportWriteError> {
        let mut steps = vec![LevelStep::Visit(level)];
        let mut done: Vec<u64> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                LevelStep::Visit(node) => match node {
                    Level::Zero => done.push(0),
                    Level::Param(name) => {
                        let name = self.name(name)?;
                        let key = LevelKey::Param(name);
                        done.push(self.level_node(key, ("param", Json::Nat(name)))?);
                    }
                    Level::Succ(inner) => {
                        steps.push(LevelStep::Build(node));
                        steps.push(LevelStep::Visit(inner));
                    }
                    Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
                        steps.push(LevelStep::Build(node));
                        steps.push(LevelStep::Visit(rhs));
                        steps.push(LevelStep::Visit(lhs));
                    }
                },
                LevelStep::Build(node) => {
                    let index = match node {
                        Level::Succ(_) => {
                            let inner = done.pop().unwrap_or_default();
                            self.level_node(LevelKey::Succ(inner), ("succ", Json::Nat(inner)))?
                        }
                        Level::Max(..) => {
                            let rhs = done.pop().unwrap_or_default();
                            let lhs = done.pop().unwrap_or_default();
                            let operands = Json::nats(&[lhs, rhs]);
                            self.level_node(LevelKey::Max(lhs, rhs), ("max", operands))?
                        }
                        Level::IMax(..) => {
                            let rhs = done.pop().unwrap_or_default();
                            let lhs = done.pop().unwrap_or_default();
                            let operands = Json::nats(&[lhs, rhs]);
                            self.level_node(LevelKey::IMax(lhs, rhs), ("imax", operands))?
                        }
                        Level::Zero | Level::Param(_) => 0,
                    };
                    done.push(index);
                }
            }
        }
        Ok(done.pop().unwrap_or_default())
    }
}
