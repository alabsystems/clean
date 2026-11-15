// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::interpret::InterpretOptions;
use crate::{Block, Constant, FuncTy, Function, Global, InstrNode};

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
    retirement_stop: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.retirement_stop && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(17))
}
fn module() -> Module {
    let mut module = Module::new("wire_λ");
    module.files = vec!["first.rs".into(), "second.rs".into(), "first.rs".into()];
    module.func_types.push(FuncTy::unrecorded(
        vec![Ty::Tuple(vec![Ty::I32, Ty::Ref(Box::new(Ty::U8))])],
        vec![],
        false,
    ));
    let mut function = Function::new(FuncId::new(17), "wire_λ", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(crate::Inst::Return { values: vec![] }));
    function.blocks.push(block);
    module.functions.push(function);
    module.globals.push(Global {
        name: "wire_λ".into(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Record(vec![
            (
                "field".into(),
                Constant::Bytes {
                    data: (0..4097).map(|n| (n % 251) as u8).collect(),
                    utf8: false,
                },
            ),
            (
                "other".into(),
                Constant::Splat {
                    elem: Box::new(Constant::Int(-1)),
                    len: u64::MAX,
                },
            ),
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: crate::Visibility::Default,
        retained: false,
    });
    module
}

#[test]
fn actual_wire_collection_count_hash_matches_both_unchanged_identity_schemes() {
    let module = module();
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            observed_module_identity(&module, scheme, &mut session, site()).unwrap(),
            module.stable_digest_under(scheme)
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        assert!(observer.events.iter().all(|event| event.site == site()));
    }
}

#[test]
fn closure_frame_origin_observed_identity_matches_canonical_and_tracks_changes() {
    let mut module = module();
    module.closure_types.push(crate::ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![],
    });
    module.closure_layouts.push(crate::ClosureLayoutDescriptor {
        closure: crate::ClosureTyId::new(0),
        size: 0,
        align: 1,
        capture_offsets: vec![],
        origin: Some(crate::ty::TypeOrigin::Clean {
            decl: "Original.Closure".into(),
            env_digest: ProofDigest::sha256([7; 32]),
        }),
    });
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let original = observed_module_identity(&module, scheme, &mut session, site()).unwrap();
        assert_eq!(original, module.stable_digest_under(scheme));
        let Some(crate::ty::TypeOrigin::Clean { decl, .. }) = &mut module.closure_layouts[0].origin
        else {
            unreachable!()
        };
        decl.push_str(".Changed");
        let changed = observed_module_identity(&module, scheme, &mut session, site()).unwrap();
        assert_eq!(changed, module.stable_digest_under(scheme));
        assert_ne!(original, changed);
        module.closure_layouts[0].origin = None;
        assert_eq!(
            observed_module_identity(&module, scheme, &mut session, site()).unwrap(),
            module.stable_digest_under(scheme)
        );
        module.closure_layouts[0].origin = Some(crate::ty::TypeOrigin::Clean {
            decl: "Original.Closure".into(),
            env_digest: ProofDigest::sha256([7; 32]),
        });
    }
}

#[test]
fn observed_wire_identity_preserves_debug_path_projection_and_tamper_sensitivity() {
    let original = module();
    let mut changed = original.clone();
    changed.files[0].push_str("-change");
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let left = observed_module_identity(&original, scheme, &mut session, site()).unwrap();
        let right = observed_module_identity(&changed, scheme, &mut session, site()).unwrap();
        assert_eq!(left == right, scheme == IdentityScheme::V3);
    }
    changed.name.push_str("-identity-change");
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_ne!(
        original.stable_digest(),
        changed
            .stable_digest_observed(&mut session, site())
            .unwrap()
    );
}

#[test]
fn every_actual_small_module_collection_wire_hash_and_retirement_stop_is_terminal() {
    let module = Module::new("small");
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    module.stable_digest_observed(&mut session, site()).unwrap();
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            module.stable_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "event {stop}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert!(module.stable_digest_observed(&mut session, site()).is_err());
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn wire_work_copy_and_retirement_use_the_same_original_nonrenewable_session() {
    let module = module();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    module.stable_digest_observed(&mut session, site()).unwrap();
    for memory in [false, true] {
        let mut observer = if memory {
            Observer {
                byte_limit: Some(measured.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(measured.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        module.stable_digest_observed(&mut session, site()).unwrap();
        assert_eq!(
            module.stable_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if memory { "bytes" } else { "work" }
        );
    }
    let mut observer = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        module.stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
}

#[test]
fn unencodable_wire_claims_refuse_without_a_prefix_digest_or_weaker_encoding() {
    for ty in [Ty::Error, Ty::Tuple(vec![Ty::U8, Ty::Error])] {
        let mut module = Module::new("hole");
        module.types.push(ty);
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            module.stable_digest_observed(&mut session, site()),
            Err(ObservedValueError::UnsupportedValue)
        );
    }
}

#[test]
fn wire_length_frame_refuses_overrun_and_underrun_before_digest_publication() {
    for overrun in [false, true] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut out = Output::counter(&mut session, site()).unwrap();
        out.start_hash("length", 1).unwrap();
        let answer = if overrun {
            out.extend_from_slice(&[1, 2])
                .and_then(|()| out.finish_hash())
        } else {
            out.finish_hash()
        };
        assert_eq!(answer, Err(ObservedValueError::InvalidRange));
    }
}

mod abi;

mod checked;
mod module_errors;
