// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
enum Names<'a> {
    Machines(&'a [SpecModule]),
    Actions(&'a [String]),
    Vars(&'a [SpecVar]),
    Invariants(&'a [SpecInvariant]),
    Temporal(&'a [SpecTemporal]),
}
impl<'a> Names<'a> {
    fn at<O: ExecutionObserver>(
        self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a str>> {
        work.admit(5, size_of::<Option<&str>>())?;
        Ok(match self {
            Self::Machines(rows) => work.at(rows, index)?.map(|row| row.name.as_str()),
            Self::Actions(rows) => work.at(rows, index)?.map(String::as_str),
            Self::Vars(rows) => work.at(rows, index)?.map(|row| row.name.as_str()),
            Self::Invariants(rows) => work.at(rows, index)?.map(|row| row.name.as_str()),
            Self::Temporal(rows) => work.at(rows, index)?.map(|row| row.name.as_str()),
        })
    }
}
impl<'a> State<'a> {
    fn duplicates<O: ExecutionObserver>(
        &mut self,
        names: Names<'_>,
        spec: Option<&SpecModule>,
        member: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(name) = names.at(index, work)? {
            if !work.blank(name)? {
                let mut prior = 0;
                while prior < index {
                    work.admit(1, 0)?;
                    let other = names
                        .at(prior, work)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if work.equal(name, other)? {
                        match spec {
                            Some(spec) => emit!(
                                self,
                                work,
                                V::DuplicateMemberIdentity {
                                    machine: &spec.name,
                                    member,
                                    name
                                }
                            )?,
                            None => {
                                emit!(self, work, V::DuplicateMachineIdentity { machine: name })?
                            }
                        };
                        break;
                    }
                    work.next(&mut prior)?;
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    pub(super) fn blank<O: ExecutionObserver>(
        &mut self,
        spec: &SpecModule,
        subject: &'static str,
        field: &'static str,
        value: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if work.blank(value)? {
            emit!(
                self,
                work,
                V::BlankSemanticValue {
                    container: &spec.name,
                    subject,
                    field
                }
            )?;
        }
        Ok(())
    }
    pub(super) fn declarations<O: ExecutionObserver>(
        &mut self,
        specs: &'a [SpecModule],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<Names<'_>>())?;
        self.duplicates(Names::Machines(specs), None, "machine", work)?;
        let mut index = 0;
        while let Some(spec) = work.at(specs, index)? {
            self.blank(spec, "SpecModule", "name", &spec.name, work)?;
            work.admit(3, 3 * size_of::<Names<'_>>())?;
            self.duplicates(Names::Actions(&spec.actions), Some(spec), "action", work)?;
            self.duplicates(Names::Vars(&spec.vars), Some(spec), "variable", work)?;
            self.duplicates(
                Names::Invariants(&spec.invariants),
                Some(spec),
                "invariant",
                work,
            )?;
            let mut at = 0;
            while let Some(action) = work.at(&spec.actions, at)? {
                self.blank(spec, "action", "name", action, work)?;
                work.next(&mut at)?;
            }
            let mut at = 0;
            while let Some(variable) = work.at(&spec.vars, at)? {
                self.blank(spec, "variable", "name", &variable.name, work)?;
                self.blank(spec, "variable", "type", &variable.ty, work)?;
                work.next(&mut at)?;
            }
            let mut at = 0;
            while let Some(invariant) = work.at(&spec.invariants, at)? {
                self.blank(spec, "invariant", "name", &invariant.name, work)?;
                self.blank(spec, "invariant", "formula", &invariant.formula, work)?;
                work.next(&mut at)?;
            }
            let mut at = 0;
            while let Some(variable) = work.at(&spec.vars, at)? {
                self.variable_sort(spec, variable, work)?;
                work.next(&mut at)?;
            }
            let mut at = 0;
            while let Some(invariant) = work.at(&spec.invariants, at)? {
                work.admit(1, size_of::<Option<&ProofFormula>>())?;
                if let Some(typed) = &invariant.typed {
                    self.typed(spec, "invariant", &invariant.name, typed, false, work)?;
                }
                work.next(&mut at)?;
            }
            work.admit(1, size_of::<Names<'_>>())?;
            self.duplicates(
                Names::Temporal(&spec.temporal),
                Some(spec),
                "temporal",
                work,
            )?;
            self.temporals(spec, work)?;
            work.admit(2, size_of::<Option<&str>>())?;
            match &spec.origin {
                SpecOrigin::Embedded => {}
                SpecOrigin::External(path) => {
                    self.blank(spec, "external origin", "path", path, work)?
                }
            }
            self.anchors(specs, spec, work)?;
            self.waivers(specs, spec, work)?;
            self.proofs(specs, spec, work)?;
            self.conflicts(spec, work)?;
            work.next(&mut index)?;
        }
        Ok(())
    }
}
