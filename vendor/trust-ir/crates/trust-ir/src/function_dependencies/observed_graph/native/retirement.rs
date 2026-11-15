// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Custody of owned sink payloads before and after graph storage admission.
use super::*;
#[cfg(test)]
mod tests;

pub(super) fn store_node<O: ExecutionObserver>(
    graph: &mut ExpandedReachGraph,
    kind: ReachNodeKind,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<ReachNode> {
    // Keep kind owned here until EVERY admission/allocation can no longer
    // fail. The generic push<T> may drop its by-value argument on refusal and
    // is therefore unsuitable for a sink holding a recursive type.
    let result = (|| {
        if u32::try_from(graph.nodes.len()).is_err() {
            return Err(ObservedValueError::CapacityOverflow);
        }
        if graph.nodes.len() == graph.nodes.capacity() {
            let requested = graph
                .nodes
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(graph.nodes.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            admit(
                session,
                site,
                images
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                images
                    .checked_mul(size_of::<ReachNodeKind>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            graph
                .nodes
                .try_reserve_exact(requested - graph.nodes.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        admit(session, site, 1, size_of::<ReachNodeKind>())?;
        Ok(graph.handle(graph.nodes.len()))
    })();
    match result {
        Ok(node) => {
            graph.nodes.push(kind);
            Ok(node)
        }
        Err(error) => {
            retire_node(kind, session, site);
            if session.first_refusal().is_some() {
                Err(ObservedValueError::AdmissionRefused)
            } else {
                Err(error)
            }
        }
    }
}

pub(super) fn retire_node<O: ExecutionObserver>(
    kind: ReachNodeKind,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    match kind {
        ReachNodeKind::Program(spec) => retire_flat(spec, session, site),
        ReachNodeKind::Hub => {}
        ReachNodeKind::Sink(reason) => retire_reason(reason, session, site),
    }
    session.retirement_poll(site);
}
fn retire_reason<O: ExecutionObserver>(
    reason: DependencyRefusalKind,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    match reason {
        DependencyRefusalKind::ImplicitDestructor(ty) => {
            crate::ty::retire_ty_observed(ty, session, site)
        }
        DependencyRefusalKind::UnresolvedSymbol(text)
        | DependencyRefusalKind::AmbiguousSymbol(text) => retire_flat(text, session, site),
        // Exhaustive: a new owned refusal payload needs a retirement decision.
        fixed @ (DependencyRefusalKind::Missing(_)
        | DependencyRefusalKind::Ambiguous(_)
        | DependencyRefusalKind::BodylessFunction(_)
        | DependencyRefusalKind::MissingGlobalInitializer(_)
        | DependencyRefusalKind::IndirectCall
        | DependencyRefusalKind::IndirectSignatureMismatch
        | DependencyRefusalKind::OpaqueDialectOperation
        | DependencyRefusalKind::OpaqueType
        | DependencyRefusalKind::GlobalAssembly
        | DependencyRefusalKind::AmbiguousBlock(_)
        | DependencyRefusalKind::MissingEntryBlock(_)
        | DependencyRefusalKind::GlobalTableTooLarge
        | DependencyRefusalKind::ElidedDrops
        | DependencyRefusalKind::HavocDeclaration
        | DependencyRefusalKind::UnresolvedExtern
        | DependencyRefusalKind::Widened
        | DependencyRefusalKind::InlineAsm
        | DependencyRefusalKind::AsyncDropShim
        | DependencyRefusalKind::CoroutineClone
        | DependencyRefusalKind::ResolutionError
        | DependencyRefusalKind::UncoveredMention
        | DependencyRefusalKind::OpenPrincipal
        | DependencyRefusalKind::UnclosedPool) => retire_flat(fixed, session, site),
    }
}

fn retire_flat<T, O: ExecutionObserver>(
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    drop(value);
    session.retirement_poll(site);
}
