// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual interpreter routes distinguishing the four independent review losses.
//! All controls are source-only until the root schedules their native owner.

use super::*;
use core::mem::size_of;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    CopyLimit,
    LookupLimit,
}

#[derive(Default)]
struct BudgetObserver {
    events: Vec<ExecutionProgress>,
    copies: usize,
    copy_limit: Option<usize>,
    lookup_limit: Option<usize>,
    sparse_budget: Option<(ExecutionSite, usize)>,
    first: Option<Cause>,
}

impl ExecutionObserver for BudgetObserver {
    type Refusal = Cause;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Cause> {
        self.events.push(progress);
        if let Some(cause) = self.first {
            return Err(cause);
        }
        let sparse_refused = match self.sparse_budget.as_mut() {
            Some((site, remaining))
                if progress.phase == ExecutionPhase::SparseRun && progress.site == *site =>
            {
                match remaining.checked_sub(progress.work) {
                    Some(next) => {
                        *remaining = next;
                        false
                    }
                    None => true,
                }
            }
            _ => false,
        };
        let cause = if sparse_refused
            || (progress.phase == ExecutionPhase::Instruction
                && self.lookup_limit.is_some_and(|limit| progress.work > limit))
        {
            Some(Cause::LookupLimit)
        } else if self.copy_limit.is_some_and(|limit| {
            self.copies
                .checked_add(progress.copy_bytes)
                .is_none_or(|next| next > limit)
        }) {
            Some(Cause::CopyLimit)
        } else {
            None
        };
        if let Some(cause) = cause {
            self.first = Some(cause);
            return Err(cause);
        }
        self.copies += progress.copy_bytes;
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exit {
    Returned(usize),
    Refused,
    Unsupported,
    Executed(InterpretErrorCode, InstructionSite),
    Entry(InterpretErrorCode),
    Limit,
}

struct Capture<E> {
    exit: Exit,
    steps: u64,
    first: Option<(ExecutionProgress, E)>,
}

fn capture<O: ExecutionObserver>(
    module: &Module,
    arguments: Vec<InterpretValue>,
    observer: &mut O,
) -> Capture<O::Refusal>
where
    O::Refusal: Copy,
{
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    let report =
        Interpreter::with_module(module).execute_func_observed(f(), arguments, &mut session);
    let mut exit = match report.exit() {
        ObservedExit::Returned(outcome) => Exit::Returned(outcome.returns.len()),
        ObservedExit::AdmissionRefused => Exit::Refused,
        ObservedExit::ExecutedError { site, error } => Exit::Executed(error.code, *site),
        ObservedExit::EntryRejected(error) => Exit::Entry(error.code),
        ObservedExit::InterpreterLimit { .. } => Exit::Limit,
        ObservedExit::UnsupportedObservation { .. } => Exit::Unsupported,
    };
    let steps = report.steps();
    if report
        .retire_observed(&mut session, ExecutionSite::Entry(f()))
        .is_err()
    {
        exit = Exit::Refused;
    }
    let first = session
        .first_refusal()
        .map(|first| (first.progress, first.cause));
    Capture { exit, steps, first }
}

fn parameters(n: usize) -> Vec<InterpretValue> {
    (0..n)
        .map(|index| int(Ty::U8, (index % 256) as i128))
        .collect()
}

fn return_module(n: usize, returns: Vec<Ty>, ids: Vec<ValueId>) -> Module {
    module(
        vec![Ty::U8; n],
        returns,
        vec![void(Inst::Return { values: ids })],
    )
}

fn instruction(index: usize) -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: f(),
        block: b(),
        instruction_index: index,
    })
}

fn copy_before(
    events: &[ExecutionProgress],
    predicate: impl Fn(&ExecutionProgress) -> bool,
) -> (usize, ExecutionProgress) {
    let mut bytes = 0;
    for event in events {
        if predicate(event) {
            return (bytes, *event);
        }
        bytes += event.copy_bytes;
    }
    panic!("actual admission event absent");
}

fn retirement_polls(events: &[ExecutionProgress]) -> usize {
    events
        .iter()
        .take_while(|event| event.phase != ExecutionPhase::Publication)
        .filter(|event| event.phase == ExecutionPhase::ScratchRetirement && event.work == 0)
        .count()
}

#[test]
fn observed_undef_unit_cannot_continue_to_a_later_false_assert() {
    let module = module(
        vec![Ty::Bool],
        vec![],
        vec![
            node(Inst::Undef { ty: Ty::Unit }, 1),
            void(Inst::Assert {
                cond: v(0),
                kind: AssertKind::Unspecified,
                site: None,
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), vec![InterpretValue::bool(false)])
        .expect_err("ordinary Unit poison refuses at Undef");
    assert_eq!(ordinary.code, InterpretErrorCode::UndefinedBehavior);
    let observed = capture(
        &module,
        vec![InterpretValue::bool(false)],
        &mut Observer::default(),
    );
    assert_eq!(
        observed.exit,
        Exit::Executed(
            ordinary.code,
            InstructionSite {
                function: f(),
                block: b(),
                instruction_index: 0
            }
        )
    );
    assert_eq!(observed.steps, 1, "the later Assert must not execute");
    assert!(observed.first.is_none());
}

#[test]
fn observed_undef_u8_copy_store_preserves_poison_until_its_strict_use() {
    let module = module(
        vec![],
        vec![],
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                0,
            ),
            node(Inst::Undef { ty: Ty::U8 }, 1),
            node(
                Inst::Copy {
                    ty: Ty::U8,
                    operand: v(1),
                },
                2,
            ),
            void(Inst::Store {
                ty: Ty::U8,
                ptr: v(0),
                value: v(2),
                volatile: false,
                align: None,
            }),
            node(
                Inst::Load {
                    ty: Ty::U8,
                    ptr: v(0),
                    volatile: true,
                    align: None,
                },
                3,
            ),
            void(Inst::Return { values: vec![] }),
        ],
    );
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), [])
        .expect_err("strict poison use");
    let observed = capture(&module, vec![], &mut Observer::default());
    assert_eq!(
        observed.exit,
        Exit::Executed(
            ordinary.code,
            InstructionSite {
                function: f(),
                block: b(),
                instruction_index: 4
            }
        )
    );
    assert_eq!(ordinary.code, InterpretErrorCode::UndefinedBehavior);
}

#[test]
fn observed_first_ssa_leaf_requires_whole_node_copy_budget_before_insertion() {
    let module = return_module(1, vec![], vec![]);
    let mut baseline = BudgetObserver::default();
    assert_eq!(
        capture(&module, parameters(1), &mut baseline).exit,
        Exit::Returned(0)
    );
    let (before, event) = copy_before(&baseline.events, |p| {
        p.phase == ExecutionPhase::BlockParameters && p.copy_bytes > 0
    });
    assert!(event.copy_bytes > size_of::<(ValueId, InterpretValue)>());
    let mut limited = BudgetObserver {
        copy_limit: Some(before + size_of::<(ValueId, InterpretValue)>()),
        ..BudgetObserver::default()
    };
    let refused = capture(&module, parameters(1), &mut limited);
    assert_eq!(refused.exit, Exit::Refused);
    assert_eq!(refused.steps, 0);
    assert_eq!(refused.first, Some((event, Cause::CopyLimit)));
}

#[test]
fn observed_ssa_root_split_stays_in_the_original_copy_account() {
    let module = return_module(12, vec![], vec![]);
    let mut baseline = BudgetObserver::default();
    assert_eq!(
        capture(&module, parameters(12), &mut baseline).exit,
        Exit::Returned(0)
    );
    let cost = super::super::btree::insertion_cost::<ValueId, InterpretValue>(11)
        .expect("checked split bound");
    let (before, event) = copy_before(&baseline.events, |p| {
        p.phase == ExecutionPhase::BlockParameters && p.copy_bytes == cost.copy_bytes
    });
    let mut limited = BudgetObserver {
        copy_limit: Some(before + size_of::<(ValueId, InterpretValue)>()),
        ..BudgetObserver::default()
    };
    let refused = capture(&module, parameters(12), &mut limited);
    assert_eq!(refused.exit, Exit::Refused);
    assert_eq!(refused.steps, 0);
    assert_eq!(refused.first, Some((event, Cause::CopyLimit)));
}

fn allocation_program() -> Module {
    let mut body = (0..12)
        .map(|index| {
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                index,
            )
        })
        .collect::<Vec<_>>();
    body.push(void(Inst::Return { values: vec![] }));
    module(vec![], vec![], body)
}

fn refuse_allocation_insert(existing: usize) {
    let module = allocation_program();
    let mut baseline = BudgetObserver::default();
    assert_eq!(
        capture(&module, vec![], &mut baseline).exit,
        Exit::Returned(0)
    );
    let cost = super::super::btree::insertion_cost::<u64, Allocation>(existing)
        .expect("checked allocation-map bound");
    let (before, event) = copy_before(&baseline.events, |p| {
        p.site == instruction(existing)
            && p.phase == ExecutionPhase::HostAllocation
            && p.copy_bytes == cost.copy_bytes
    });
    let mut limited = BudgetObserver {
        copy_limit: Some(before + size_of::<(u64, Allocation)>()),
        ..BudgetObserver::default()
    };
    let refused = capture(&module, vec![], &mut limited);
    assert_eq!(refused.exit, Exit::Refused);
    assert_eq!(refused.steps, existing as u64 + 1);
    assert_eq!(refused.first, Some((event, Cause::CopyLimit)));
}

#[test]
fn observed_first_allocation_map_leaf_prices_whole_node_before_native_storage() {
    refuse_allocation_insert(0);
}

#[test]
fn observed_allocation_map_root_split_cannot_borrow_a_fresh_copy_grant() {
    refuse_allocation_insert(11);
}

#[test]
fn observed_full_leaf_greatest_and_missing_key_search_price_each_possible_comparison() {
    for id in [v(10), v(11)] {
        let module = return_module(11, vec![Ty::U8], vec![id]);
        let mut observer = BudgetObserver {
            lookup_limit: Some(5),
            ..BudgetObserver::default()
        };
        let refused = capture(&module, parameters(11), &mut observer);
        assert_eq!(refused.exit, Exit::Refused);
        let (event, cause) = refused.first.expect("original lookup refusal");
        assert_eq!(cause, Cause::LookupLimit);
        assert_eq!(event.phase, ExecutionPhase::Instruction);
        assert_eq!(event.site, instruction(0));
        assert_eq!(
            event.work, 12,
            "an eleven-key leaf is not a five-comparison path"
        );
    }
}

#[test]
fn observed_multi_node_lookup_refuses_under_same_original_work_budget() {
    let module = return_module(64, vec![Ty::U8], vec![v(63)]);
    let mut observer = BudgetObserver {
        lookup_limit: Some(8),
        ..BudgetObserver::default()
    };
    let refused = capture(&module, parameters(64), &mut observer);
    assert_eq!(refused.exit, Exit::Refused);
    assert_eq!(refused.first.expect("retained cause").0.work, 65);
}

#[test]
fn observed_pointer_icmp_prepays_both_allocation_lookups_before_comparison() {
    let mut module = allocation_program();
    module.func_types[0].returns = vec![Ty::Bool];
    let body = &mut module.functions[0].blocks[0].body;
    body.pop();
    body.push(node(
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::Ptr,
            lhs: v(0),
            rhs: v(0),
        },
        12,
    ));
    body.push(void(Inst::Return {
        values: vec![v(12)],
    }));
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), vec![])
        .expect("ordinary pointer comparison");
    let report = run(&module, vec![], &mut Observer::default());
    assert_eq!(&returned(&report).returns, &ordinary.returns);
    assert_eq!(returned(&report).returns[0].as_bool(), Some(true));

    let at = instruction(12);
    let work = super::super::btree::population_work(12).unwrap();
    let mut generous = BudgetObserver {
        sparse_budget: Some((at, 2 * work)),
        ..BudgetObserver::default()
    };
    assert_eq!(
        capture(&module, vec![], &mut generous).exit,
        Exit::Returned(1)
    );
    let lookups = generous
        .events
        .iter()
        .filter(|event| event.site == at && event.phase == ExecutionPhase::SparseRun)
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        lookups.len(),
        2,
        "each operand exposes its allocation's address"
    );
    assert!(
        lookups
            .iter()
            .all(|event| event.work == work && event.copy_bytes == 0)
    );

    for (prepaid, lookup) in lookups.iter().copied().enumerate() {
        let mut limited = BudgetObserver {
            sparse_budget: Some((at, (prepaid + 1) * work - 1)),
            ..BudgetObserver::default()
        };
        let refused = capture(&module, vec![], &mut limited);
        assert_eq!(refused.exit, Exit::Refused);
        assert_eq!(refused.steps, 13, "the Return must not execute");
        assert_eq!(refused.first, Some((lookup, Cause::LookupLimit)));
        assert_eq!(
            limited
                .events
                .iter()
                .filter(|event| event.site == at && event.phase == ExecutionPhase::SparseRun)
                .count(),
            prepaid + 1,
            "a refusal must stop before the next address lookup"
        );
    }
}

#[test]
fn observed_pointer_icmp_null_and_dangling_addresses_need_no_allocation_lookup() {
    let module = module(
        vec![Ty::Ptr, Ty::Ptr],
        vec![Ty::Bool],
        vec![
            node(
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::Ptr,
                    lhs: v(0),
                    rhs: v(1),
                },
                2,
            ),
            void(Inst::Return { values: vec![v(2)] }),
        ],
    );
    let pointer = |kind| InterpretValue { ty: Ty::Ptr, kind };
    for (lhs, rhs, expected) in [
        (
            InterpretValueKind::NullPtr,
            InterpretValueKind::NullPtr,
            true,
        ),
        (
            InterpretValueKind::DanglingPtr(8),
            InterpretValueKind::DanglingPtr(8),
            true,
        ),
        (
            InterpretValueKind::NullPtr,
            InterpretValueKind::DanglingPtr(8),
            false,
        ),
    ] {
        let arguments = vec![pointer(lhs), pointer(rhs)];
        let report = run(&module, arguments.clone(), &mut Observer::default());
        assert_eq!(returned(&report).returns[0].as_bool(), Some(expected));
        let mut observer = BudgetObserver {
            sparse_budget: Some((instruction(0), 0)),
            ..BudgetObserver::default()
        };
        assert_eq!(
            capture(&module, arguments, &mut observer).exit,
            Exit::Returned(1)
        );
        assert!(
            !observer
                .events
                .iter()
                .any(|event| event.site == instruction(0)
                    && event.phase == ExecutionPhase::SparseRun)
        );
    }
}

#[test]
fn observed_initial_memory_reserves_every_module_function_address() {
    for (function_count, first_data_address) in [(1023, 1024), (1024, 1025), (1101, 1102)] {
        let mut module = module(
            vec![Ty::Ptr],
            vec![Ty::Bool],
            vec![
                node(
                    Inst::Alloca {
                        ty: Ty::U8,
                        count: None,
                        align: None,
                    },
                    1,
                ),
                node(
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs: v(1),
                        rhs: v(0),
                    },
                    2,
                ),
                void(Inst::Return { values: vec![v(2)] }),
            ],
        );
        // Uncalled declarations reserve code words too. The executable root
        // alone does not determine where the data namespace begins.
        for id in 1..function_count {
            module.functions.push(Function::new(
                FuncId::new(id),
                format!("uncalled_{id}"),
                FuncTyId::new(0),
                b(),
            ));
        }
        let argument = |address| InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::DanglingPtr(address),
        };
        for probe in [first_data_address, 1024] {
            let arguments = vec![argument(probe)];
            let ordinary = Interpreter::with_module(&module)
                .execute_func(f(), arguments.clone())
                .expect("ordinary namespace reservation");
            assert_eq!(
                ordinary.returns[0].as_bool(),
                Some(probe == first_data_address)
            );
            let report = run(&module, arguments, &mut Observer::default());
            assert_eq!(
                returned(&report).returns,
                ordinary.returns,
                "{function_count} functions, pointer probe {probe}"
            );
        }

        let mut limited = BudgetObserver {
            copy_limit: Some(0),
            ..BudgetObserver::default()
        };
        let refused = capture(&module, vec![argument(first_data_address)], &mut limited);
        assert_eq!(refused.exit, Exit::Refused);
        assert_eq!(refused.steps, 0);
        assert_eq!(
            refused.first,
            Some((
                ExecutionProgress {
                    phase: ExecutionPhase::HostAllocation,
                    site: ExecutionSite::Entry(f()),
                    work: 1,
                    copy_bytes: 512,
                },
                Cause::CopyLimit,
            )),
            "the original startup diagnostic admission remains first"
        );
    }
}

#[test]
fn observed_map_population_and_storage_overflow_refuse_without_wrapping() {
    assert!(matches!(
        super::super::btree::population_work(usize::MAX),
        Err(ObservedValueError::CapacityOverflow)
    ));
    assert!(matches!(
        super::super::btree::insertion_cost::<ValueId, InterpretValue>(usize::MAX),
        Err(ObservedValueError::CapacityOverflow)
    ));
}

#[test]
fn observed_mid_make_aggregate_copy_retires_every_owned_prefix_element() {
    let ty = Ty::Array(TyId::new(0), 64);
    let module = module(
        vec![Ty::U8; 64],
        vec![ty.clone()],
        vec![
            node(
                Inst::MakeAggregate {
                    ty,
                    variant: None,
                    fields: (0..64).map(v).collect(),
                },
                64,
            ),
            void(Inst::Return {
                values: vec![v(64)],
            }),
        ],
    );
    let mut observer = Observer {
        stop: Some((ExecutionPhase::LiteralElement, 32)),
        ..Observer::default()
    };
    assert_eq!(
        capture(&module, parameters(64), &mut observer).exit,
        Exit::Refused
    );
    assert!(
        retirement_polls(&observer.events) >= 4 * (64 + 31),
        "both state and partial owned copy must drain"
    );
}

fn literal_prefix_stop(value: Constant) {
    let ty = Ty::Array(TyId::new(0), 64);
    let module = module(
        vec![],
        vec![ty.clone()],
        vec![
            node(Inst::Const { ty, value }, 0),
            void(Inst::Return { values: vec![v(0)] }),
        ],
    );
    let mut observer = Observer {
        stop: Some((ExecutionPhase::LiteralElement, 32)),
        ..Observer::default()
    };
    assert_eq!(capture(&module, vec![], &mut observer).exit, Exit::Refused);
    assert!(
        retirement_polls(&observer.events) >= 4 * 31,
        "owned literal prefix needs original cleanup polls"
    );
}

#[test]
fn observed_mid_array_constant_copy_retires_owned_prefix_after_refusal() {
    literal_prefix_stop(Constant::Array((0..64).map(Constant::Int).collect()));
}

#[test]
fn observed_mid_bytes_constant_copy_retires_owned_prefix_after_refusal() {
    literal_prefix_stop(Constant::Bytes {
        data: (0..64).collect(),
        utf8: false,
    });
}

#[test]
fn observed_mid_return_clone_retires_prefix_before_refusing_publication() {
    let module = return_module(64, vec![Ty::U8; 64], (0..64).map(v).collect());
    let mut observer = Observer {
        stop: Some((ExecutionPhase::LiteralElement, 32)),
        ..Observer::default()
    };
    assert_eq!(
        capture(&module, parameters(64), &mut observer).exit,
        Exit::Refused
    );
    assert!(retirement_polls(&observer.events) >= 4 * (64 + 31));
}

#[test]
fn observed_return_arity_validation_failure_retires_all_cloned_outputs() {
    let module = return_module(64, vec![Ty::U8], (0..64).map(v).collect());
    let mut observer = Observer::default();
    assert_eq!(
        capture(&module, parameters(64), &mut observer).exit,
        Exit::Executed(
            InterpretErrorCode::SignatureMismatch,
            InstructionSite {
                function: f(),
                block: b(),
                instruction_index: 0
            }
        )
    );
    assert!(retirement_polls(&observer.events) >= 4 * 128);
}

#[test]
fn observed_return_type_validation_failure_retires_all_cloned_outputs() {
    let module = return_module(64, vec![Ty::Bool; 64], (0..64).map(v).collect());
    let mut observer = Observer::default();
    assert_eq!(
        capture(&module, parameters(64), &mut observer).exit,
        Exit::Unsupported
    );
    assert!(retirement_polls(&observer.events) >= 4 * 128);
}

#[test]
fn observed_return_validation_admission_failure_retires_all_owned_outputs() {
    struct ValidationObserver {
        events: Vec<ExecutionProgress>,
        stopped: bool,
    }
    impl ExecutionObserver for ValidationObserver {
        type Refusal = &'static str;
        fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
            self.events.push(p);
            if p.site == instruction(0) && p.phase == ExecutionPhase::BlockParameters {
                self.stopped = true;
            }
            if self.stopped {
                Err("return validation stopped")
            } else {
                Ok(())
            }
        }
    }
    let module = return_module(64, vec![Ty::U8; 64], (0..64).map(v).collect());
    let mut observer = ValidationObserver {
        events: vec![],
        stopped: false,
    };
    let refused = capture(&module, parameters(64), &mut observer);
    assert_eq!(refused.exit, Exit::Refused);
    assert_eq!(
        refused.first.expect("original validation cause").0.phase,
        ExecutionPhase::BlockParameters
    );
    assert!(retirement_polls(&observer.events) >= 4 * 128);
}

#[test]
fn observed_cleanup_stop_during_failed_return_never_publishes_a_return_or_panic() {
    let mut ids = vec![v(0); 64];
    ids.push(v(999));
    let module = return_module(1, vec![Ty::U8; 65], ids);
    let mut observer = Observer {
        stop: Some((ExecutionPhase::ScratchRetirement, 1)),
        ..Observer::default()
    };
    let refused = capture(&module, parameters(1), &mut observer);
    assert_eq!(refused.exit, Exit::Refused);
    assert_eq!(
        refused.first.expect("first cleanup refusal").0.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(retirement_polls(&observer.events) >= 4 * 65);
}

#[test]
fn observed_late_invalid_literal_retires_its_successful_owned_prefix() {
    let ty = Ty::Array(TyId::new(0), 64);
    let mut elements = (0..64).map(Constant::Int).collect::<Vec<_>>();
    elements[32] = Constant::Bool(true);
    let module = module(
        vec![],
        vec![ty.clone()],
        vec![
            node(
                Inst::Const {
                    ty,
                    value: Constant::Array(elements),
                },
                0,
            ),
            void(Inst::Return { values: vec![v(0)] }),
        ],
    );
    let mut observer = Observer::default();
    let refused = capture(&module, vec![], &mut observer);
    assert_eq!(refused.exit, Exit::Unsupported);
    assert!(refused.first.is_none());
    assert!(retirement_polls(&observer.events) >= 4 * 32);
}

#[test]
fn observed_late_make_aggregate_lookup_error_retires_prefix_without_losing_fault_site() {
    let ty = Ty::Array(TyId::new(0), 64);
    let mut fields = (0..64).map(v).collect::<Vec<_>>();
    fields[32] = v(999);
    let module = module(
        vec![Ty::U8; 64],
        vec![ty.clone()],
        vec![
            node(
                Inst::MakeAggregate {
                    ty,
                    variant: None,
                    fields,
                },
                64,
            ),
            void(Inst::Return {
                values: vec![v(64)],
            }),
        ],
    );
    let mut observer = Observer::default();
    let refused = capture(&module, parameters(64), &mut observer);
    assert_eq!(
        refused.exit,
        Exit::Executed(
            InterpretErrorCode::MissingValue,
            InstructionSite {
                function: f(),
                block: b(),
                instruction_index: 0
            }
        )
    );
    assert!(refused.first.is_none());
    assert!(retirement_polls(&observer.events) >= 4 * (64 + 32));
}

#[test]
fn observed_phantom_constants_use_the_unit_only_typed_converter() {
    for ty in [Ty::Unit, Ty::I8, Ty::Bool, Ty::F64, Ty::Ptr] {
        let valid = ty == Ty::Unit;
        let module = module(
            vec![],
            vec![],
            vec![
                node(
                    Inst::Const {
                        ty,
                        value: Constant::PhantomData,
                    },
                    0,
                ),
                void(Inst::Return { values: vec![] }),
            ],
        );
        let ordinary = Interpreter::with_module(&module).execute_func(f(), []);
        let mut observer = Observer::default();
        let observed = capture(&module, vec![], &mut observer);
        if valid {
            assert!(ordinary.is_ok());
            assert_eq!(observed.exit, Exit::Returned(0));
            let mut stopped = Observer {
                stop: Some((ExecutionPhase::LiteralElement, 1)),
                ..Observer::default()
            };
            assert_eq!(capture(&module, vec![], &mut stopped).exit, Exit::Refused);
            assert!(
                !stopped
                    .events
                    .iter()
                    .any(|event| event.site == instruction(1))
            );
        } else {
            assert_eq!(
                ordinary.expect_err("non-Unit phantom").code,
                InterpretErrorCode::TypeError
            );
            assert_eq!(
                observed.exit,
                Exit::Executed(
                    InterpretErrorCode::TypeError,
                    InstructionSite {
                        function: f(),
                        block: b(),
                        instruction_index: 0,
                    }
                )
            );
            assert!(
                !observer
                    .events
                    .iter()
                    .any(|event| event.site == instruction(1))
            );
        }
    }
}
