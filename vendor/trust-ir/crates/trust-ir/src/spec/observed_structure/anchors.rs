// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn anchors<O: ExecutionObserver>(
        &mut self,
        specs: &[SpecModule],
        spec: &SpecModule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(anchor) = work.at(&spec.anchors, index)? {
            self.blank(spec, "anchor", "machine", &anchor.machine, work)?;
            self.blank(spec, "anchor", "action", &anchor.action, work)?;
            self.blank(spec, "anchor", "rust_symbol", &anchor.rust_symbol, work)?;
            self.mismatch(specs, spec, &anchor.machine, &anchor.action, "anchor", work)?;
            work.admit(
                3,
                size_of::<SpecEnforcementMode>()
                    + size_of::<Option<FuncId>>()
                    + size_of::<Option<SpecProjectionTarget>>(),
            )?;
            if spec.enforcement == SpecEnforcementMode::Linked {
                if anchor.function.is_none() {
                    emit!(
                        self,
                        work,
                        V::TypedTargetRequired {
                            machine: &spec.name,
                            action: &anchor.action,
                            target: "action function"
                        }
                    )?;
                }
                if anchor.projection_target.is_none() {
                    emit!(
                        self,
                        work,
                        V::TypedTargetRequired {
                            machine: &spec.name,
                            action: &anchor.action,
                            target: "projection"
                        }
                    )?;
                }
            }
            match anchor.projection_target {
                Some(SpecProjectionTarget::TemporalFieldPathsV1) => {
                    work.admit(1, size_of::<Option<&str>>())?;
                    let matches = match anchor.project.as_deref() {
                        Some(project) => work.equal(project, TEMPORAL_FIELD_PATH_PROJECTION_V1)?,
                        None => false,
                    };
                    if !matches {
                        self.begin_detail(work)?;
                        work.text(
                            "temporal-field-paths-v1 requires project ",
                            &mut self.detail,
                        )?;
                        work.quoted(TEMPORAL_FIELD_PATH_PROJECTION_V1, &mut self.detail)?;
                        emit!(
                            self,
                            work,
                            V::ProjectionTargetIncompatible {
                                machine: &spec.name,
                                action: &anchor.action,
                                detail: &self.detail
                            }
                        )?;
                        self.clear_detail(work)?;
                    }
                }
                Some(SpecProjectionTarget::ExternalUnresolved) => {
                    work.admit(2, 0)?;
                    if matches!(&spec.origin, SpecOrigin::Embedded) {
                        emit!(
                            self,
                            work,
                            V::ProjectionTargetIncompatible {
                                machine: &spec.name,
                                action: &anchor.action,
                                detail: "embedded models cannot use external-unresolved projections"
                            }
                        )?;
                    }
                }
                Some(SpecProjectionTarget::Function(_)) | None => {}
            }
            if references::belongs(spec, &anchor.machine, &anchor.action, work)? {
                let mut prior = 0;
                while prior < index {
                    work.admit(1, 0)?;
                    let other = work
                        .at(&spec.anchors, prior)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if references::belongs(spec, &other.machine, &other.action, work)?
                        && same_anchor(anchor, other, work)?
                    {
                        self.begin_detail(work)?;
                        work.quoted(&anchor.action, &mut self.detail)?;
                        work.admit(1, size_of::<Option<FuncId>>())?;
                        if let Some(function) = anchor.function {
                            work.text(" -> function #", &mut self.detail)?;
                            work.number(u128::from(function.index()), &mut self.detail)?;
                        } else {
                            work.text(" -> rust_symbol ", &mut self.detail)?;
                            work.quoted(&anchor.rust_symbol, &mut self.detail)?;
                        }
                        emit!(
                            self,
                            work,
                            V::DuplicateBindingIdentity {
                                machine: &spec.name,
                                binding: "anchor",
                                identity: &self.detail
                            }
                        )?;
                        self.clear_detail(work)?;
                        break;
                    }
                    work.next(&mut prior)?;
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    pub(super) fn waivers<O: ExecutionObserver>(
        &mut self,
        specs: &[SpecModule],
        spec: &SpecModule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(waiver) = work.at(&spec.waivers, index)? {
            self.blank(spec, "waiver", "machine", &waiver.machine, work)?;
            self.blank(spec, "waiver", "action", &waiver.action, work)?;
            self.blank(spec, "waiver", "reason", &waiver.reason, work)?;
            self.mismatch(specs, spec, &waiver.machine, &waiver.action, "waiver", work)?;
            if references::belongs(spec, &waiver.machine, &waiver.action, work)? {
                let mut prior = 0;
                while prior < index {
                    work.admit(1, 0)?;
                    let other = work
                        .at(&spec.waivers, prior)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if references::belongs(spec, &other.machine, &other.action, work)?
                        && work.equal(&waiver.action, &other.action)?
                    {
                        self.begin_detail(work)?;
                        work.text("action ", &mut self.detail)?;
                        work.quoted(&waiver.action, &mut self.detail)?;
                        emit!(
                            self,
                            work,
                            V::DuplicateBindingIdentity {
                                machine: &spec.name,
                                binding: "waiver",
                                identity: &self.detail
                            }
                        )?;
                        self.clear_detail(work)?;
                        break;
                    }
                    work.next(&mut prior)?;
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    pub(super) fn proofs<O: ExecutionObserver>(
        &mut self,
        specs: &[SpecModule],
        spec: &SpecModule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(proof) = work.at(&spec.proofs, index)? {
            self.blank(spec, "proof", "machine", &proof.machine, work)?;
            self.blank(spec, "proof", "action", &proof.action, work)?;
            self.blank(spec, "proof", "proof_name", &proof.proof_name, work)?;
            self.mismatch(specs, spec, &proof.machine, &proof.action, "proof", work)?;
            if references::belongs(spec, &proof.machine, &proof.action, work)?
                && !work.blank(&proof.proof_name)?
            {
                let mut prior = 0;
                while prior < index {
                    work.admit(1, 0)?;
                    let other = work
                        .at(&spec.proofs, prior)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    if references::belongs(spec, &other.machine, &other.action, work)?
                        && same_proof(proof, other, work)?
                    {
                        self.begin_detail(work)?;
                        work.text("action ", &mut self.detail)?;
                        work.quoted(&proof.action, &mut self.detail)?;
                        work.text(", kind ", &mut self.detail)?;
                        let kind = tag(&proof.kind, work)?;
                        work.text(kind, &mut self.detail)?;
                        work.text(", proof_name ", &mut self.detail)?;
                        work.quoted(&proof.proof_name, &mut self.detail)?;
                        emit!(
                            self,
                            work,
                            V::DuplicateBindingIdentity {
                                machine: &spec.name,
                                binding: "proof",
                                identity: &self.detail
                            }
                        )?;
                        self.clear_detail(work)?;
                        break;
                    }
                    work.next(&mut prior)?;
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    pub(super) fn conflicts<O: ExecutionObserver>(
        &mut self,
        spec: &SpecModule,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(anchor) = work.at(&spec.anchors, index)? {
            if references::belongs(spec, &anchor.machine, &anchor.action, work)? {
                let mut at = 0;
                while let Some(waiver) = work.at(&spec.waivers, at)? {
                    if references::belongs(spec, &waiver.machine, &waiver.action, work)?
                        && work.equal(&anchor.action, &waiver.action)?
                    {
                        emit!(
                            self,
                            work,
                            V::AnchorWaiverConflict {
                                machine: &spec.name,
                                action: &anchor.action
                            }
                        )?;
                        break;
                    }
                    work.next(&mut at)?;
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
}
fn same_anchor<O: ExecutionObserver>(
    a: &SpecAnchor,
    b: &SpecAnchor,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    if !work.equal(&a.action, &b.action)? {
        return Ok(false);
    }
    work.admit(3, 2 * size_of::<Option<FuncId>>())?;
    match (a.function, b.function) {
        (Some(a), Some(b)) => Ok(a.index() == b.index()),
        (None, None) => work.equal(&a.rust_symbol, &b.rust_symbol),
        (Some(_), None) | (None, Some(_)) => Ok(false),
    }
}
fn tag<O: ExecutionObserver>(kind: &ProofKind, work: &mut Work<'_, '_, O>) -> R<&'static str> {
    work.admit(2, size_of::<&str>())?;
    Ok(match kind {
        ProofKind::Kani => "kani",
        ProofKind::CleanTheorem { name: _ } => "clean-theorem",
    })
}
fn same_proof<O: ExecutionObserver>(
    a: &SpecProof,
    b: &SpecProof,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    if !work.equal(&a.action, &b.action)? {
        return Ok(false);
    }
    let left = tag(&a.kind, work)?;
    let right = tag(&b.kind, work)?;
    if !work.equal(left, right)? {
        return Ok(false);
    }
    work.equal(&a.proof_name, &b.proof_name)
}
