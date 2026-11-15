// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
enum Resolution {
    MachineMissing,
    ActionMissing,
    Clean,
}
pub(super) fn belongs<O: ExecutionObserver>(
    spec: &SpecModule,
    machine: &str,
    action: &str,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    Ok(!work.blank(&spec.name)?
        && !work.blank(machine)?
        && !work.blank(action)?
        && work.equal(machine, &spec.name)?)
}
fn known<O: ExecutionObserver>(
    specs: &[SpecModule],
    machine: &str,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut index = 0;
    while let Some(row) = work.at(specs, index)? {
        if work.equal(&row.name, machine)? {
            return Ok(true);
        }
        work.next(&mut index)?;
    }
    Ok(false)
}
fn needs<O: ExecutionObserver>(
    specs: &[SpecModule],
    spec: &SpecModule,
    machine: &str,
    action: &str,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    Ok(!work.blank(&spec.name)?
        && !work.blank(machine)?
        && !work.blank(action)?
        && (work.equal(machine, &spec.name)? || !known(specs, machine, work)?))
}
fn resolve<O: ExecutionObserver>(
    specs: &[SpecModule],
    machine: &str,
    action: &str,
    work: &mut Work<'_, '_, O>,
) -> R<Resolution> {
    work.admit(1, size_of::<Option<&SpecModule>>())?;
    let mut matched = None;
    let mut index = 0;
    while let Some(row) = work.at(specs, index)? {
        if work.equal(&row.name, machine)? {
            work.admit(1, 0)?;
            if matched.is_some() {
                return Ok(Resolution::Clean);
            }
            matched = Some(row);
        }
        work.next(&mut index)?;
    }
    match matched {
        None => Ok(Resolution::MachineMissing),
        Some(row) => {
            if work.blank(&row.name)? || bindings::has_action(row, action, work)? {
                Ok(Resolution::Clean)
            } else {
                Ok(Resolution::ActionMissing)
            }
        }
    }
}
impl State<'_> {
    pub(super) fn mismatch<O: ExecutionObserver>(
        &mut self,
        specs: &[SpecModule],
        spec: &SpecModule,
        machine: &str,
        action: &str,
        from: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if !work.blank(&spec.name)?
            && !work.blank(machine)?
            && !work.equal(machine, &spec.name)?
            && known(specs, machine, work)?
        {
            emit!(
                self,
                work,
                V::ReferenceContainerMismatch {
                    container: &spec.name,
                    machine,
                    action,
                    from
                }
            )?;
        }
        Ok(())
    }
    fn reference<O: ExecutionObserver>(
        &mut self,
        resolution: Resolution,
        machine: &str,
        action: &str,
        from: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(3, 0)?;
        match resolution {
            Resolution::MachineMissing => emit!(
                self,
                work,
                V::MachineMissing {
                    machine,
                    action,
                    from,
                    detail: &self.detail
                }
            )?,
            Resolution::ActionMissing => emit!(
                self,
                work,
                V::ActionMissing {
                    machine,
                    action,
                    from,
                    detail: &self.detail
                }
            )?,
            Resolution::Clean => {}
        }
        self.clear_detail(work)
    }
    pub(super) fn references<O: ExecutionObserver>(
        &mut self,
        specs: &[SpecModule],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(spec) = work.at(specs, index)? {
            let mut at = 0;
            while let Some(anchor) = work.at(&spec.anchors, at)? {
                if needs(specs, spec, &anchor.machine, &anchor.action, work)? {
                    let resolution = resolve(specs, &anchor.machine, &anchor.action, work)?;
                    if !matches!(resolution, Resolution::Clean) {
                        self.begin_detail(work)?;
                        work.text("function=", &mut self.detail)?;
                        work.admit(1, size_of::<Option<FuncId>>())?;
                        if let Some(function) = anchor.function {
                            work.number(u128::from(function.index()), &mut self.detail)?;
                        } else {
                            work.text("unresolved", &mut self.detail)?;
                        }
                        work.text(", rust_symbol=", &mut self.detail)?;
                        work.quoted(&anchor.rust_symbol, &mut self.detail)?;
                        self.reference(
                            resolution,
                            &anchor.machine,
                            &anchor.action,
                            "anchor",
                            work,
                        )?;
                    }
                }
                work.next(&mut at)?;
            }
            let mut at = 0;
            while let Some(waiver) = work.at(&spec.waivers, at)? {
                if needs(specs, spec, &waiver.machine, &waiver.action, work)? {
                    let resolution = resolve(specs, &waiver.machine, &waiver.action, work)?;
                    if !matches!(resolution, Resolution::Clean) {
                        self.begin_detail(work)?;
                        work.text("reason=", &mut self.detail)?;
                        work.quoted(&waiver.reason, &mut self.detail)?;
                        self.reference(
                            resolution,
                            &waiver.machine,
                            &waiver.action,
                            "waiver",
                            work,
                        )?;
                    }
                }
                work.next(&mut at)?;
            }
            let mut at = 0;
            while let Some(proof) = work.at(&spec.proofs, at)? {
                if needs(specs, spec, &proof.machine, &proof.action, work)? {
                    let resolution = resolve(specs, &proof.machine, &proof.action, work)?;
                    if !matches!(resolution, Resolution::Clean) {
                        self.begin_detail(work)?;
                        work.text("proof_name=", &mut self.detail)?;
                        work.quoted(&proof.proof_name, &mut self.detail)?;
                        self.reference(resolution, &proof.machine, &proof.action, "proof", work)?;
                    }
                }
                work.next(&mut at)?;
            }
            work.next(&mut index)?;
        }
        let mut index = 0;
        while let Some(spec) = work.at(specs, index)? {
            let mut at = 0;
            while let Some(anchor) = work.at(&spec.anchors, at)? {
                if belongs(spec, &anchor.machine, &anchor.action, work)? {
                    work.admit(1, size_of::<Option<&str>>())?;
                    let missing = match anchor.project.as_deref() {
                        None => true,
                        Some(project) => work.blank(project)?,
                    };
                    if missing {
                        emit!(
                            self,
                            work,
                            V::ProjectionMissing {
                                machine: &spec.name,
                                action: &anchor.action
                            }
                        )?;
                    }
                }
                work.next(&mut at)?;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
