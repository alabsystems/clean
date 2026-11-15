// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Source-authored controls, UNRUN.
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    work: usize,
    cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("cleanup work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(975))
}
#[test]
fn cleanup_charges_original_cumulative_work_and_drains_despite_first_refusal() {
    let mut work = Work {
        first_text: "λ".repeat(3000),
        second_text: "界".repeat(2000),
        pending: Some(E::EmbeddedPublicObligationIdMismatch {
            request: NativeRequestId::new(0),
            obligation: ProofId::new(0),
            expected: "expected".into(),
            actual: "actual".into(),
        }),
        ..Work::default()
    };
    work.seen_variants.extend(0..32);
    work.discriminants.extend(0..32);
    let mut observer = Observer {
        cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    work.retire_scratch(&mut session, site());
    assert_eq!(session.first_refusal().unwrap().cause, "cleanup work");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(work.pending.is_none());
    assert!(work.first_text.is_empty() && work.second_text.is_empty());
    assert_eq!(
        (work.first_text.capacity(), work.second_text.capacity()),
        (0, 0)
    );
    assert!(work.seen_variants.is_empty() && work.discriminants.is_empty());
    assert_eq!(
        work.finish(Ok(()), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "cleanup work");
    assert!(observer.work >= 2 * (1..=32usize).sum::<usize>());
    assert!(observer.events.iter().all(|event| event.site == site()
        && event.phase == ExecutionPhase::ScratchRetirement
        && event.work > 0));
}
fn shape() -> Arc<TyLayoutShape> {
    Arc::new(TyLayoutShape {
        size_bits: 256,
        align_bits: Some(8),
        kind: TyLayoutKind::Tuple {
            fields: (0..32)
                .map(|index| FieldOffsetShape {
                    field: index,
                    name: format!("field-{index}"),
                    ty_shape: crate::TyShape::Unit,
                    offset_bits: Some(u64::from(index) * 8),
                })
                .collect(),
        },
    })
}
#[test]
fn shared_layout_release_keeps_external_owner_then_observes_final_inner_field_retirement() {
    let external = shape();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    layout(Arc::clone(&external), &mut session, site());
    assert_eq!(Arc::strong_count(&external), 1);
    assert!(
        matches!(&external.kind, TyLayoutKind::Tuple { fields } if fields.len() == 32 && fields[31].name == "field-31")
    );
    assert!(session.first_refusal().is_none());
    let mut final_observer = Observer {
        cap: Some(1),
        ..Observer::default()
    };
    let mut final_session = ObservedSession::new(InterpretOptions::default(), &mut final_observer);
    layout(external, &mut final_session, site());
    assert_eq!(final_session.first_refusal().unwrap().cause, "cleanup work");
    assert!(final_observer.events.len() > 32 * 2);
    assert!(
        final_observer
            .events
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement && event.work > 0)
    );
}
