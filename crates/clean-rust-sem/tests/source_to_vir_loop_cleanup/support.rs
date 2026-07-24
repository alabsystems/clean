// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;

use clean_rust_sem::vir::{Rvalue, Stmt, Term};
use clean_rust_sem::{Body, Mutability, Place, RustType, SourceProgram};

pub(super) fn lowered_main(source: &str) -> Body {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("source should lower to VIR")
        .functions
        .get("main")
        .cloned()
        .expect("lowered program should contain `main`")
}

pub(super) fn anonymous_local_of_named_type(body: &Body, type_name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| match &decl.ty {
            RustType::Named { name, .. } if decl.name.is_none() && name == type_name => {
                Some(idx as u32)
            }
            _ => None,
        })
        .expect("anonymous local of the requested nominal type should exist")
}

pub(super) fn anonymous_mut_ref_local(body: &Body) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| match &decl.ty {
            RustType::Reference { mutability, .. }
                if decl.name.is_none() && *mutability == Mutability::Mutable =>
            {
                Some(idx as u32)
            }
            _ => None,
        })
        .expect("anonymous mutable-reference local should exist")
}

pub(super) fn named_local(body: &Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

pub(super) fn drop_terminator_count(body: &Body, local: u32) -> usize {
    body.blocks
        .iter()
        .filter(|bb| {
            matches!(
                &bb.terminator,
                Term::Drop {
                    place: Place::Local(drop_local),
                    ..
                } if *drop_local == local
            )
        })
        .count()
}

fn block_containing_storage_live(body: &Body, local: u32) -> u32 {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(idx, bb)| {
            bb.statements
                .iter()
                .any(|stmt| matches!(stmt, Stmt::StorageLive(storage_local) if *storage_local == local))
                .then_some(idx as u32)
        })
        .expect("StorageLive block for local should exist")
}

fn predecessor_blocks(body: &Body, target: u32) -> Vec<u32> {
    body.blocks
        .iter()
        .enumerate()
        .filter_map(|(idx, bb)| {
            bb.terminator
                .successors()
                .contains(&target)
                .then_some(idx as u32)
        })
        .collect()
}

fn block_has_storage_dead(body: &Body, block: u32, local: u32) -> bool {
    body.blocks[block as usize]
        .statements
        .iter()
        .any(|stmt| matches!(stmt, Stmt::StorageDead(dead_local) if *dead_local == local))
}

pub(super) fn storage_live_has_prior_storage_dead(
    body: &Body,
    live_local: u32,
    dead_local: u32,
) -> bool {
    let live_block = block_containing_storage_live(body, live_local);
    let mut pending = predecessor_blocks(body, live_block);
    let mut visited = BTreeSet::new();

    while let Some(block) = pending.pop() {
        if !visited.insert(block) {
            continue;
        }
        if block_has_storage_dead(body, block, dead_local) {
            continue;
        }

        let predecessors = predecessor_blocks(body, block);
        if predecessors.is_empty() {
            return false;
        }
        pending.extend(predecessors);
    }

    true
}

pub(super) fn has_switch_targeting_immediate_drop(body: &Body, local: u32) -> bool {
    body.blocks.iter().any(|bb| match &bb.terminator {
        Term::SwitchInt { targets, .. } => targets.iter_targets().any(|(_, target)| {
            matches!(
                &body.blocks[target.block as usize].terminator,
                Term::Drop {
                    place: Place::Local(drop_local),
                    ..
                } if *drop_local == local
            )
        }),
        _ => false,
    })
}

pub(super) fn iterator_next_continuation_block(body: &Body) -> u32 {
    body.blocks
        .iter()
        .find_map(|bb| match &bb.terminator {
            Term::Call {
                func:
                    clean_rust_sem::vir::Operand::Constant(clean_rust_sem::vir::Constant::FnDef {
                        name,
                        ..
                    }),
                target: Some(target),
                ..
            } if name == "Iterator::next" => Some(*target),
            _ => None,
        })
        .expect("Iterator::next call continuation should exist")
}

pub(super) fn entry_goto_target(body: &Body) -> u32 {
    match &body.blocks[0].terminator {
        Term::Goto { target, .. } => *target,
        terminator => panic!("entry block should lower to a goto, found {terminator:?}"),
    }
}

pub(super) fn has_drop_continuing_to(body: &Body, local: u32, expected_target: u32) -> bool {
    body.blocks.iter().any(|bb| match &bb.terminator {
        Term::Drop {
            place: Place::Local(drop_local),
            target,
            ..
        } if *drop_local == local => matches!(
            &body.blocks[*target as usize].terminator,
            Term::Goto { target, .. } if *target == expected_target
        ),
        _ => false,
    })
}

pub(super) fn for_discriminant_bool_local(body: &Body, next_result: u32) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| {
            (decl.name.is_none()
                && decl.ty == RustType::Bool
                && body.blocks.iter().any(|bb| {
                    bb.statements.iter().any(|stmt| {
                        matches!(
                            stmt,
                            Stmt::Assign {
                                place: Place::Local(dst),
                                rvalue: Rvalue::Discriminant(Place::Local(src)),
                            } if *dst == idx as u32 && *src == next_result
                        )
                    })
                }))
            .then_some(idx as u32)
        })
        .expect("anonymous Bool local assigned from the for-loop Option discriminant should exist")
}

pub(super) fn for_loop_some_body_block(body: &Body) -> u32 {
    body.blocks
        .iter()
        .find_map(|bb| match &bb.terminator {
            Term::SwitchInt { targets, .. } => targets
                .iter_targets()
                .find(|(val, _)| *val == Some(1))
                .map(|(_, t)| t.block),
            _ => None,
        })
        .expect("for-loop SwitchInt with Some (1) branch should exist")
}
