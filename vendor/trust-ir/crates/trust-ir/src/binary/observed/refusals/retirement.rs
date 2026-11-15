// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
fn record<O: ExecutionObserver>(s: &mut ObservedSession<'_, O>, site: ExecutionSite, bytes: usize) {
    s.retirement_record(site, 1, bytes);
}
fn text<O: ExecutionObserver>(value: String, s: &mut ObservedSession<'_, O>, site: ExecutionSite) {
    record(s, site, size_of::<String>());
    record(s, site, value.capacity());
    drop(value);
    s.retirement_poll(site);
}
pub(super) fn projection<O: ExecutionObserver>(
    value: BinaryProjectionError,
    s: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    record(s, site, size_of::<BinaryProjectionError>());
    match value {
        BinaryProjectionError::SignatureAbiUnencodable { detail, .. } => text(detail, s, site),
        BinaryProjectionError::DialectTypeRequiresV39
        | BinaryProjectionError::ContainerVtableRequiresV40
        | BinaryProjectionError::ContractSurfaceRequiresV41
        | BinaryProjectionError::TupleLayoutRequiresV42
        | BinaryProjectionError::HandleTypeRequiresV43
        | BinaryProjectionError::ImportSchemeRequiresV44
        | BinaryProjectionError::AbiSurfaceRequiresV45
        | BinaryProjectionError::InlinedScopeChainUnencodable { .. }
        | BinaryProjectionError::SpecCarrierRequiresV46
        | BinaryProjectionError::DropInstRequiresV47
        | BinaryProjectionError::WeakCmpXchgRequiresV48
        | BinaryProjectionError::UninitLaneRequiresV49
        | BinaryProjectionError::ArraySplatRequiresV50
        | BinaryProjectionError::InstWireBatchRequiresV51
        | BinaryProjectionError::AssertKindRequiresV52
        | BinaryProjectionError::CallUnwindBoundaryRequiresV53
        | BinaryProjectionError::PanicSiteRequiresV54
        | BinaryProjectionError::DropGlueRequiresV55
        | BinaryProjectionError::UnwindTwinsRequiresV56
        | BinaryProjectionError::NominalIdentityRequiresV58
        | BinaryProjectionError::EffectSummaryRequiresV59
        | BinaryProjectionError::SignatureAbiRequiresCurrentFormat
        | BinaryProjectionError::CertificateBindingRequiresV61
        | BinaryProjectionError::ParamPointeePlaceRequiresV62
        | BinaryProjectionError::StorageRequiresV64
        | BinaryProjectionError::MakeClosureRequiresV63
        | BinaryProjectionError::ClosureOriginRequiresV66
        | BinaryProjectionError::TensorRequiresV67
        | BinaryProjectionError::TensorMapReduceViewRequiresV68
        | BinaryProjectionError::TensorGatherScatterRequiresV69
        | BinaryProjectionError::TensorBlobRequiresV70
        | BinaryProjectionError::CompletenessClaimUnencodable
        | BinaryProjectionError::ConstructAheadOfWireTag { .. }
        | BinaryProjectionError::InvalidStorageGeometry(_)
        | BinaryProjectionError::ProducerInternalType
        | BinaryProjectionError::CountExceedsFormat { .. }
        | BinaryProjectionError::DuplicateOmission(_)
        | BinaryProjectionError::UnknownOmission(_)
        | BinaryProjectionError::AmbiguousOmission(_)
        | BinaryProjectionError::NonPendingOmission(_)
        | BinaryProjectionError::RetainedReference { .. } => {}
    }
    s.retirement_poll(site);
}
pub(super) fn rows<O: ExecutionObserver>(
    mut rows: Vec<BinaryProjectionError>,
    s: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    record(s, site, size_of::<Vec<BinaryProjectionError>>());
    loop {
        record(s, site, size_of::<Option<BinaryProjectionError>>());
        let Some(e) = rows.pop() else {
            break;
        };
        projection(e, s, site);
    }
    record(
        s,
        site,
        rows.capacity()
            .saturating_mul(size_of::<BinaryProjectionError>()),
    );
    drop(rows);
    s.retirement_poll(site);
}
impl Refusals {
    pub(super) fn retire<O: ExecutionObserver>(
        &mut self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        record(s, site, size_of::<Option<WireRefusal>>());
        if let Some(e) = self.pending.take() {
            match e {
                WireRefusal::SignatureAbi { detail, .. } => text(detail, s, site),
                WireRefusal::NoWireTag { .. }
                | WireRefusal::InlinedScopeChain { .. }
                | WireRefusal::CompletenessClaim
                | WireRefusal::ProducerInternalType
                | WireRefusal::InvalidStorageGeometry(_) => {}
            }
        }
        record(s, site, size_of::<Option<(usize, BinaryProjectionError)>>());
        if let Some((_, e)) = self.converted.take() {
            projection(e, s, site);
        }
        for e in &mut self.first {
            record(s, site, size_of::<Option<BinaryProjectionError>>());
            if let Some(e) = e.take() {
                projection(e, s, site);
            }
        }
        rows(take(&mut self.result), s, site);
        s.retirement_poll(site);
    }
}
