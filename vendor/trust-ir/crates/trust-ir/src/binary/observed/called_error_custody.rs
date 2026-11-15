// Exact first negative-control body retained; second is the explicit C1
// semantic-boundary successor. All Rust compiler/native UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    refuse_cleanup: bool,
    stop_at: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> core::result::Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len())
            || (self.refuse_cleanup && event.phase == ExecutionPhase::ScratchRetirement)
        {
            Err("first actual cleanup")
        } else {
            Ok(())
        }
    }
}

#[test]
fn actual_wire_type_local_error_survives_the_next_real_cleanup_refusal() {
    let site = ExecutionSite::Entry(FuncId::new(901));
    for refuse_cleanup in [false, true] {
        let mut observer = Observer {
            refuse_cleanup,
            ..Observer::default()
        };
        let mut session =
            ObservedSession::new(crate::interpret::InterpretOptions::default(), &mut observer);
        let mut out = Output::counter(&mut session, site).unwrap();
        out.admit(1, 2 * core::mem::size_of::<Builder>()).unwrap();
        let pool = Builder::new(false).seal();
        // This invokes the actual existing writer's Ty::Error refusal, not a
        // copied tail or an injected allocation/capacity/runtime assumption.
        let actual = observed_write_ty(&mut out, &pool, &Ty::Error);
        pool.retire(&mut out);
        drop(out);
        if refuse_cleanup {
            let stopped = session.first_refusal().unwrap();
            assert_eq!(stopped.cause, "first actual cleanup");
            assert_eq!(stopped.progress.phase, ExecutionPhase::ScratchRetirement);
            assert_eq!(stopped.progress.site, site);
        } else {
            assert!(session.first_refusal().is_none());
        }
        drop(session);
        assert!(observer.events.iter().all(|event| event.site == site));
        // Frozen old source instead returns AdmissionRefused on the second
        // iteration. This is a source-derived negative, never a native result.
        assert_eq!(actual, Err(ObservedValueError::UnsupportedValue));
    }
}

#[test]
fn actual_public_body_preserves_wire_error_before_later_cleanup_on_raw_cast_piece() {
    // C1 successor: this malformed raw preimage now has a complete ordinary
    // refusal before wire, rather than reaching an unencodable writer.
    let mut module = Module::new("raw refused body");
    let mut function =
        crate::Function::new(FuncId::new(1), "raw", FuncTyId::new(0), BlockId::new(0));
    function.attrs.params.push(ParamAttrs {
        pass: Some(PassMode::Cast {
            pieces: vec![Ty::Error],
        }),
        ..ParamAttrs::default()
    });
    let mut block = crate::Block::new(BlockId::new(0));
    block.body.push(crate::InstrNode::new(crate::Inst::Return {
        values: vec![],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    let expected = Err("function #1 spells the producer-internal Ty::Error, which has no binary spelling, so the body has no identity to state".to_owned());
    assert_eq!(module.function_body_digest(FuncId::new(1)), expected);
    let site = ExecutionSite::Entry(FuncId::new(902));
    let mut baseline = Observer::default();
    let mut session =
        ObservedSession::new(crate::interpret::InterpretOptions::default(), &mut baseline);
    let actual = module
        .function_body_digest_observed(FuncId::new(1), &mut session, site)
        .unwrap();
    assert_eq!(actual, expected);
    Module::retire_function_body_digest_result_observed(actual, &mut session, site).unwrap();
    assert!(session.first_refusal().is_none());
    drop(session);
    let mut measured = Observer::default();
    let mut session =
        ObservedSession::new(crate::interpret::InterpretOptions::default(), &mut measured);
    let actual = module
        .function_body_digest_observed(FuncId::new(1), &mut session, site)
        .unwrap();
    drop(session);
    let split = measured.events.len();
    assert_eq!(&baseline.events[..split], &measured.events);
    assert!(
        baseline.events[split..baseline.events.len() - 1]
            .iter()
            .any(|e| e.copy_bytes > 0)
    );
    for cut in split + 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut session =
            ObservedSession::new(crate::interpret::InterpretOptions::default(), &mut observer);
        let held = module
            .function_body_digest_observed(FuncId::new(1), &mut session, site)
            .unwrap();
        assert_eq!(held, expected);
        assert_eq!(
            Module::retire_function_body_digest_result_observed(held, &mut session, site),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress,
            baseline.events[cut - 1]
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "first actual cleanup"
        );
        drop(session);
        let end = if cut == baseline.events.len() {
            baseline.events.len()
        } else {
            baseline.events.len() - 1
        };
        assert_eq!(observer.events, baseline.events[..end]);
    }
    // The separately measured returned reason remains owned and is consumed.
    let mut cleanup = Observer::default();
    let mut session =
        ObservedSession::new(crate::interpret::InterpretOptions::default(), &mut cleanup);
    Module::retire_function_body_digest_result_observed(actual, &mut session, site).unwrap();
}
