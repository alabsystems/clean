// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

impl Solve {
    pub(super) fn expand<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        index: usize,
        literals: &mut Vec<Node>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.poll()?;
        let mut found = false;
        match self.nodes[index] {
            Node::Entry(entry) => self.clause(
                module,
                index,
                core::iter::once(&module.types[entry]),
                literals,
                work,
            )?,
            Node::Struct(id) => {
                for def in &module.structs {
                    work.poll()?;
                    if def.id == id {
                        found = true;
                        self.clause(
                            module,
                            index,
                            def.fields.iter().map(|field| &field.ty),
                            literals,
                            work,
                        )?;
                    }
                }
                if !found {
                    self.clause(module, index, core::iter::empty(), literals, work)?;
                }
            }
            Node::Record(id) => {
                for def in &module.records {
                    work.poll()?;
                    if def.id == id {
                        found = true;
                        self.clause(
                            module,
                            index,
                            def.fields.iter().map(|field| &field.ty),
                            literals,
                            work,
                        )?;
                    }
                }
                if !found {
                    self.clause(module, index, core::iter::empty(), literals, work)?;
                }
            }
            Node::Enum(id) => {
                for def in &module.enums {
                    work.poll()?;
                    if def.id != id {
                        continue;
                    }
                    found = true;
                    for variant in &def.variants {
                        work.poll()?;
                        self.clause(module, index, variant.fields.iter(), literals, work)?;
                    }
                }
                if !found {
                    self.clause(module, index, core::iter::empty(), literals, work)?;
                }
            }
        }
        Ok(())
    }
}
