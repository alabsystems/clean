// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN full original lineage byte/digest contracts; no replay evidence.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofFormula,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
    PublicObligationIdentity, SpecObligationRef,
};
use crate::value::{FuncId, FuncTyId, ProofId, ValueId};
use crate::{BlockId, Function, Module};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("lineage stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(8003))
}
fn fixture() -> (Module, ProofObligation, CertificateBinding) {
    let mut module = Module::new("");
    module.functions = vec![Function::new(
        FuncId::new(77),
        "owneré🦀",
        FuncTyId::new(0),
        BlockId::new(9),
    )];
    let mut row = ProofObligation::new(
        ProofId::new(999),
        ObligationKind::Custom {
            namespace: "n\0é".into(),
            name: "opaque".into(),
        },
        ProofStatus::Certified,
        "description",
    );
    row.function = Some(FuncId::new(77));
    row.site = Some(crate::proof::ObligationSite::new(
        FuncId::new(77),
        BlockId::new(9),
        u32::MAX,
    ));
    let mut f = ProofFormula::new("schema", "payload");
    f.smtlib = Some("smtlib".into());
    f.sort = Some("sort".into());
    f.bindings = vec![(
        "x".into(),
        ClauseBinding {
            sort: ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Int)),
            place: ClausePlace::Value(ValueId::new(41)),
        },
    )];
    row.formula = Some(f);
    row.spec = Some(SpecObligationRef::new("machine", "temporal"));
    row.source = Some(
        ProofObligationSourceIdentity::new("source\0é", "assertion")
            .with_range(ProofObligationSourceRange {
                file: 4,
                start_line: 9,
                start_col: 8,
                end_line: 1,
                end_col: 0,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "public".into(),
                semantic_digest: ProofDigest {
                    algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                    bytes: [9; 32],
                },
            }),
    );
    (
        module,
        row,
        CertificateBinding::new(ProofDigest::sha256([3; 32]), ProofDigest::sha256([4; 32])),
    )
}
fn original_content(row: &ProofObligation, catalog: &ModuleFunctionCatalog<'_>) -> Option<Vec<u8>> {
    super::super::super::super::clean_cic_lineage_content_v8(row, &|id| {
        catalog.unique(id).map(|f| f.name.clone())
    })
}
fn original_v8(
    row: &ProofObligation,
    catalog: &ModuleFunctionCatalog<'_>,
    binding: Option<&CertificateBinding>,
) -> Option<ProofDigest> {
    super::super::super::super::clean_cic_lineage_digest_v8(
        row,
        &|id| catalog.unique(id).map(|f| f.name.clone()),
        binding,
    )
}
fn exact(module: &Module, row: &ProofObligation, binding: Option<&CertificateBinding>) {
    let catalog = ModuleFunctionCatalog::new(module);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        row.clean_cic_lineage_digest_observed(&mut s, site())
            .unwrap(),
        super::super::super::super::clean_cic_lineage_digest(row)
    );
    let bytes = row
        .clean_cic_lineage_content_v8_observed(&catalog, &mut s, site())
        .unwrap();
    assert_eq!(bytes, original_content(row, &catalog));
    if let Some(bytes) = bytes {
        ProofDigest::retire_canonical_bytes_observed(bytes, &mut s, site()).unwrap();
    }
    assert_eq!(
        row.clean_cic_lineage_digest_v8_observed(&catalog, binding, &mut s, site())
            .unwrap(),
        original_v8(row, &catalog, binding)
    );
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
