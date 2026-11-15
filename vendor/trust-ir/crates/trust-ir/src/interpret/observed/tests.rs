// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(
    clippy::collapsible_if,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::*;
use super::*;

mod memory;
mod review_corrections;
mod startup;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<(ExecutionPhase, usize)>,
    seen: usize,
    refused: bool,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if let Some((phase, count)) = self.stop {
            if phase == progress.phase {
                self.seen += 1;
                if self.seen == count {
                    self.refused = true;
                }
            }
        }
        if self.refused {
            Err("original operation stopped")
        } else {
            Ok(())
        }
    }
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn f() -> FuncId {
    FuncId::new(0)
}
fn b() -> BlockId {
    BlockId::new(0)
}
fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}
fn void(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn int(ty: Ty, n: i128) -> InterpretValue {
    InterpretValue::int(ty, n).expect("test integer")
}

fn module(params: Vec<Ty>, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("observed_original_execution");
    module.types.push(Ty::U8);
    module
        .func_types
        .push(FuncTy::unrecorded(params.clone(), returns, false));
    let mut function = Function::new(f(), "original_entry", FuncTyId::new(0), b());
    let mut block = Block::new(b());
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(i, ty)| (v(i as u32), ty))
        .collect();
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn run(module: &Module, arguments: Vec<InterpretValue>, observer: &mut Observer) -> ObservedReport {
    let options = InterpretOptions::default();
    let mut session = ObservedSession::new(options, observer);
    Interpreter::with_module(module).execute_func_observed(f(), arguments, &mut session)
}

fn returned(report: &ObservedReport) -> &InterpretOutcome {
    match report.exit() {
        ObservedExit::Returned(outcome) => outcome,
        exit => panic!("expected returned data, got {exit:?}"),
    }
}

#[test]
fn observed_void_assert_retains_real_function_block_and_instruction() {
    let module = module(
        vec![Ty::Bool],
        vec![],
        vec![
            void(Inst::Assert {
                cond: v(0),
                kind: AssertKind::Unspecified,
                site: None,
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    let report = run(
        &module,
        vec![InterpretValue::bool(false)],
        &mut Observer::default(),
    );
    assert!(
        matches!(report.exit(), ObservedExit::ExecutedError { site, error }
        if *site == InstructionSite { function:f(), block:b(), instruction_index:0 }
        && error.code == InterpretErrorCode::Panic)
    );
    assert_eq!(report.steps(), 1);
    assert_eq!(report.host_calls(), 0);
}

#[test]
fn observed_return_is_reference_data_and_matches_ordinary_scalar_execution() {
    let module = module(
        vec![Ty::I64, Ty::I64],
        vec![Ty::I64],
        vec![
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                },
                2,
            ),
            void(Inst::Return { values: vec![v(2)] }),
        ],
    );
    let args = vec![int(Ty::I64, 19), int(Ty::I64, 23)];
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), args.clone())
        .expect("ordinary");
    let report = run(&module, args, &mut Observer::default());
    assert_eq!(returned(&report), &ordinary);
}

#[test]
fn observed_two_attempts_share_remaining_original_fuel() {
    let module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    let options = InterpretOptions {
        fuel: 1,
        ..InterpretOptions::default()
    };
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(options, &mut observer);
    let interpreter = Interpreter::with_module(&module).with_options(options);
    assert!(matches!(
        interpreter
            .execute_func_observed(f(), vec![], &mut session)
            .exit(),
        ObservedExit::Returned(_)
    ));
    assert_eq!(session.remaining_fuel(), 0);
    assert!(
        matches!(interpreter.execute_func_observed(f(), vec![], &mut session).exit(),
        ObservedExit::InterpreterLimit { error, .. } if error.code == InterpretErrorCode::OutOfFuel)
    );
    assert_eq!(session.remaining_fuel(), 0);
}

#[test]
fn observed_first_refusal_stays_typed_and_sticky_across_attempts() {
    let module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    let mut observer = Observer {
        stop: Some((ExecutionPhase::Instruction, 1)),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let interpreter = Interpreter::with_module(&module);
    assert!(matches!(
        interpreter
            .execute_func_observed(f(), vec![], &mut session)
            .exit(),
        ObservedExit::AdmissionRefused
    ));
    let first = session
        .first_refusal()
        .expect("retained first cause")
        .progress;
    assert!(matches!(
        interpreter
            .execute_func_observed(f(), vec![], &mut session)
            .exit(),
        ObservedExit::AdmissionRefused
    ));
    assert_eq!(
        session.first_refusal().expect("same refusal").progress,
        first
    );
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
}

#[test]
fn observed_final_publication_refusal_discards_return_payload() {
    let module = module(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![void(Inst::Return { values: vec![v(0)] })],
    );
    let mut observer = Observer {
        stop: Some((ExecutionPhase::Publication, 1)),
        ..Observer::default()
    };
    let report = run(&module, vec![int(Ty::I64, 7)], &mut observer);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn observed_cleanup_refusal_cannot_publish_an_executed_panic() {
    let module = module(
        vec![Ty::Bool],
        vec![],
        vec![void(Inst::Assert {
            cond: v(0),
            kind: AssertKind::Unspecified,
            site: None,
        })],
    );
    let mut observer = Observer {
        stop: Some((ExecutionPhase::ScratchRetirement, 1)),
        ..Observer::default()
    };
    let report = run(&module, vec![InterpretValue::bool(false)], &mut observer);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
}

#[test]
fn observed_report_payload_retirement_uses_same_original_observer() {
    let module = module(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![void(Inst::Return { values: vec![v(0)] })],
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(
        f(),
        vec![int(Ty::I64, 1)],
        &mut session,
    );
    assert_eq!(returned(&report).returns, vec![int(Ty::I64, 1)]);
    report
        .retire_observed(&mut session, ExecutionSite::Entry(f()))
        .expect("same cleanup");
    assert!(session.first_refusal().is_none());
}

#[test]
fn observed_invalid_result_arity_refuses_before_success() {
    let module = module(
        vec![],
        vec![],
        vec![
            void(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(3),
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    let report = run(&module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(), ObservedExit::ExecutedError { error, .. } if error.code == InterpretErrorCode::MalformedInstruction)
    );
}
