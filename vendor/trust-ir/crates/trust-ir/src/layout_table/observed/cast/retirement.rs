// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN exhaustive cast-evidence retirement control.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;

#[test]
fn every_noncopy_cast_evidence_variant_retires_only_its_copy_guarded_fields_after_stop() {
    struct Stop(Vec<ExecutionProgress>);
    impl ExecutionObserver for Stop {
        type Refusal = &'static str;
        fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
            self.0.push(e);
            if e.phase == ExecutionPhase::ScratchRetirement {
                Err("retirement")
            } else {
                Ok(())
            }
        }
    }
    let site = ExecutionSite::Entry(crate::FuncId::new(152));
    let mut o = Stop(Vec::new());
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, site).unwrap();
    for value in [
        CastLayoutEvidence::NotLayoutSensitive,
        CastLayoutEvidence::PointerCast {
            src: crate::PointerLayoutShape::thin(64),
            dst: crate::PointerLayoutShape::thin(32),
        },
        CastLayoutEvidence::SameSize {
            size_bits: u64::MAX,
            src_align_bits: Some(128),
            dst_align_bits: None,
        },
        CastLayoutEvidence::ReifyFnPointer { pointer_bits: 128 },
    ] {
        retire_evidence(value, &mut w);
    }
    assert!(w.poll().is_err());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    drop(s);
    assert_eq!(
        o.0.iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work != 0)
            .count(),
        4
    );
    assert!(o.0.iter().all(|e| e.site == site));
}
