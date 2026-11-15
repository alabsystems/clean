// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual successor construction under the caller's original operation.
//! Only Edge headers are copied. Instruction types, switch constants and edge
//! argument vectors remain borrowed and are never cloned, compared or walked.

use super::{BlockId, Edge, EdgeKind, Inst, ValueId};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;

#[cfg(test)]
mod tests;

type R<T = ()> = Result<T, ObservedValueError>;

impl Inst {
    /// Every original CFG edge, with identical order, targets, argument-slice
    /// identity and kind. Observes actual construction in the same session/site;
    /// an outer error never supplies a partial or smaller successor list.
    /// This establishes no CFG/SSA/unwind validity or source/proof authority.
    /// Requested storage is logical; allocator latency/RSS and successful output
    /// disposal remain outside this helper's claim.
    pub fn successor_edges_observed<'a, O: ExecutionObserver>(
        &'a self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<Edge<'a>>> {
        admit(session, site, 1, size_of::<Vec<Edge<'a>>>())?;
        let mut edges = Vec::new();
        let result = build(self, &mut edges, session, site).and_then(|()| {
            session
                .admit(ExecutionProgress {
                    phase: ExecutionPhase::Publication,
                    site,
                    work: 1,
                    copy_bytes: size_of::<Vec<Edge<'a>>>(),
                })
                .map_err(Into::into)
        });
        match result {
            Ok(()) => Ok(edges),
            Err(error) => {
                retire(edges, session, site);
                if session.first_refusal().is_some() {
                    Err(ObservedValueError::AdmissionRefused)
                } else {
                    Err(error)
                }
            }
        }
    }
}

fn build<'a, O: ExecutionObserver>(
    instruction: &'a Inst,
    edges: &mut Vec<Edge<'a>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    match instruction {
        Inst::Br { target, args } => normal(edges, *target, args, session, site),
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => {
            normal(edges, *then_target, then_args, session, site)?;
            normal(edges, *else_target, else_args, session, site)
        }
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            for case in cases {
                admit(session, site, 1, 0)?;
                normal(edges, case.target, &case.args, session, site)?;
            }
            normal(edges, *default, default_args, session, site)
        }
        Inst::Invoke {
            normal_dest,
            normal_args,
            unwind_dest,
            ..
        }
        | Inst::AssertInvoke {
            normal_dest,
            normal_args,
            unwind_dest,
            ..
        }
        | Inst::DropInvoke {
            normal_dest,
            normal_args,
            unwind_dest,
            ..
        }
        | Inst::InvokeIndirect {
            normal_dest,
            normal_args,
            unwind_dest,
            ..
        } => {
            normal(edges, *normal_dest, normal_args, session, site)?;
            push(
                edges,
                Edge {
                    target: *unwind_dest,
                    args: &[],
                    kind: EdgeKind::Unwind,
                },
                session,
                site,
            )
        }
        // Exhaustive ordinary no-successor inventory is copied below. No
        // wildcard may silently make a future terminator into a CFG sink.
        Inst::Return { .. }
        | Inst::Resume { .. }
        | Inst::Unreachable
        | Inst::CoroSuspend { .. }
        | Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::Drop { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::LandingPad { .. }
        | Inst::DialectOp(_)
        | Inst::MakeAggregate { .. }
        | Inst::MakeClosure { .. }
        | Inst::ArraySplat { .. }
        | Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. } => Ok(()),
    }
}

fn normal<'a, O: ExecutionObserver>(
    edges: &mut Vec<Edge<'a>>,
    target: BlockId,
    args: &'a [ValueId],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    push(
        edges,
        Edge {
            target,
            args,
            kind: EdgeKind::Normal,
        },
        session,
        site,
    )
}

fn push<'a, O: ExecutionObserver>(
    edges: &mut Vec<Edge<'a>>,
    edge: Edge<'a>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    admit(session, site, 1, 0)?;
    if edges.len() == edges.capacity() {
        let requested = edges
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let images = requested
            .checked_add(edges.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        admit(
            session,
            site,
            images,
            images
                .checked_mul(size_of::<Edge<'a>>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        edges
            .try_reserve_exact(requested - edges.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    admit(session, site, 1, size_of::<Edge<'a>>())?;
    edges.push(edge);
    Ok(())
}

fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    copy_bytes: usize,
) -> R {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work,
            copy_bytes,
        })
        .map_err(Into::into)
}

fn retire<O: ExecutionObserver>(
    mut edges: Vec<Edge<'_>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !edges.is_empty() {
        session.retirement_step(site, 1);
        edges.pop();
    }
    session.retirement_poll(site);
    drop(edges);
    session.retirement_poll(site);
}
