// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for unwind-cleanup CFG emission in source -> VIR lowering.

use clean_rust_sem::vir::{Constant, UnwindAction};
use clean_rust_sem::{Body, Place, SourceProgram, Term};
use std::collections::BTreeSet;

fn lowered_main(source: &str) -> Body {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("source should lower to VIR")
        .functions
        .get("main")
        .cloned()
        .expect("lowered program should contain `main`")
}

fn local_id(body: &Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

fn call_unwind_action(body: &Body, callee: &str) -> UnwindAction {
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Term::Call {
                func: clean_rust_sem::Operand::Constant(Constant::FnDef { name, .. }),
                unwind,
                ..
            } if name == callee => Some(*unwind),
            _ => None,
        })
        .unwrap_or_else(|| panic!("expected call to `{callee}` in lowered body: {body:#?}"))
}

fn drop_unwind_cleanup_block(body: &Body, local: u32) -> u32 {
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Term::Drop {
                place: Place::Local(drop_local),
                unwind: UnwindAction::Cleanup(cleanup),
                ..
            } if *drop_local == local => Some(*cleanup),
            _ => None,
        })
        .unwrap_or_else(|| panic!("expected cleanup unwind edge for local {local}: {body:#?}"))
}

fn cleanup_blocks(body: &Body, entry: u32) -> BTreeSet<u32> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![entry];
    while let Some(block_id) = stack.pop() {
        if !seen.insert(block_id) {
            continue;
        }
        let block = &body.blocks[block_id as usize];
        assert!(
            block.is_cleanup,
            "cleanup successor should stay in cleanup CFG: block={block_id}, body={body:#?}"
        );
        for succ in block.terminator.successors() {
            if body.blocks[succ as usize].is_cleanup {
                stack.push(succ);
            }
        }
    }
    seen
}

fn cleanup_chain_contains_drop(body: &Body, entry: u32, local: u32) -> bool {
    cleanup_blocks(body, entry).into_iter().any(|block_id| {
        matches!(
            &body.blocks[block_id as usize].terminator,
            Term::Drop {
                place: Place::Local(drop_local),
                ..
            } if *drop_local == local
        )
    })
}

fn cleanup_chain_resumes(body: &Body, entry: u32) -> bool {
    cleanup_blocks(body, entry).into_iter().any(|block_id| {
        matches!(
            body.blocks[block_id as usize].terminator,
            Term::UnwindResume
        )
    })
}

#[test]
fn test_direct_call_emits_cleanup_cfg_for_in_scope_drop_local() {
    let source = r#"
        struct Guard { data: u32 }

        fn consume(value: u32) -> u32 { value }

        fn main() -> u32 {
            let guard: Guard = Guard { data: 1u32 };
            consume(7u32)
        }
    "#;

    let body = lowered_main(source);
    let guard = local_id(&body, "guard");
    let cleanup = match call_unwind_action(&body, "consume") {
        UnwindAction::Cleanup(block) => block,
        other => {
            panic!("direct call should unwind through cleanup CFG, found {other:?}: {body:#?}")
        }
    };

    assert!(
        cleanup_chain_contains_drop(&body, cleanup, guard),
        "direct-call cleanup should drop the in-scope guard: {body:#?}"
    );
    assert!(
        cleanup_chain_resumes(&body, cleanup),
        "cleanup CFG should terminate with UnwindResume: {body:#?}"
    );
}

#[test]
fn test_fresh_call_destination_does_not_create_spurious_cleanup_cfg() {
    let source = r#"
        struct Guard { data: u32 }

        fn make() -> Guard {
            Guard { data: 1u32 }
        }

        fn main() -> u32 {
            let value: Guard = make();
            0u32
        }
    "#;

    let body = lowered_main(source);
    assert!(
        matches!(call_unwind_action(&body, "make"), UnwindAction::Continue),
        "fresh destination local should not be dropped on unwind before initialization: {body:#?}"
    );
}

#[test]
fn test_reassigned_call_destination_keeps_cleanup_for_previous_value() {
    let source = r#"
        struct Guard { data: u32 }

        fn make() -> Guard {
            Guard { data: 2u32 }
        }

        fn main() -> u32 {
            let mut value: Guard = Guard { data: 1u32 };
            value = make();
            0u32
        }
    "#;

    let body = lowered_main(source);
    let value = local_id(&body, "value");
    let cleanup = match call_unwind_action(&body, "make") {
        UnwindAction::Cleanup(block) => block,
        other => panic!(
            "reassignment call should preserve old-value cleanup, found {other:?}: {body:#?}"
        ),
    };

    assert!(
        cleanup_chain_contains_drop(&body, cleanup, value),
        "reassignment call should drop the previously initialized local on unwind: {body:#?}"
    );
}

#[test]
fn test_branch_local_fresh_destination_stays_out_of_unwind_cleanup() {
    let source = r#"
        struct Guard { data: u32 }

        fn make() -> Guard {
            Guard { data: 3u32 }
        }

        fn main(flag: bool) -> u32 {
            let value: Guard;
            if flag {
                value = Guard { data: 1u32 };
            } else {
                value = make();
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    assert!(
        matches!(call_unwind_action(&body, "make"), UnwindAction::Continue),
        "branch-local fresh destinations should not inherit cleanup from sibling-branch defs: {body:#?}"
    );
}

#[test]
fn test_for_loop_iterator_next_call_emits_cleanup_cfg() {
    let source = r#"
        struct Guard { data: u32 }

        fn main() -> u32 {
            let guard: Guard = Guard { data: 1u32 };
            for i in 0u32..1u32 {
                let _copy: u32 = i;
            }
            guard.data
        }
    "#;

    let body = lowered_main(source);
    let guard = local_id(&body, "guard");
    let cleanup = match call_unwind_action(&body, "Iterator::next") {
        UnwindAction::Cleanup(block) => block,
        other => {
            panic!("Iterator::next should unwind through cleanup CFG, found {other:?}: {body:#?}")
        }
    };

    assert!(
        cleanup_chain_contains_drop(&body, cleanup, guard),
        "for-loop iterator cleanup should drop outer guards on unwind: {body:#?}"
    );
}

#[test]
fn test_scope_exit_drop_unwinds_through_outer_cleanup_cfg() {
    let source = r#"
        struct Outer { data: u32 }
        struct Inner { data: u32 }

        fn main() -> u32 {
            let outer: Outer = Outer { data: 1u32 };
            {
                let inner: Inner = Inner { data: 2u32 };
                let _copy: u32 = inner.data;
            }
            outer.data
        }
    "#;

    let body = lowered_main(source);
    let inner = local_id(&body, "inner");
    let outer = local_id(&body, "outer");
    let cleanup = drop_unwind_cleanup_block(&body, inner);

    assert!(
        cleanup_chain_contains_drop(&body, cleanup, outer),
        "scope-exit drop should clean remaining outer locals on unwind: {body:#?}"
    );
    assert!(
        cleanup_chain_resumes(&body, cleanup),
        "scope-exit cleanup CFG should end in UnwindResume: {body:#?}"
    );
}
