// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Inner observation of the native declaration-policy graph and the real
//! compressed-graph label solver. Pool derivation, general classifier summaries,
//! symbolic relocations and typed indirect resolution remain
//! outside the native builder's supported closure and fail nonsemantically.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError, observed_btree,
};
use core::mem::size_of;

mod native;
mod native_queries;
mod solve;
#[cfg(test)]
mod tests;

type Observed<T> = Result<T, ObservedValueError>;

/// Inspect every stored function/global under the native bundle's exact policy:
/// all functions Walk, definition keys are function IDs, runtime services are
/// UNKNOWN(UnresolvedExtern). This is not a substitute for a different supplied
/// DeclClassifier, and neither validates a module nor grants source authority.
///
/// All successful construction/label/check loops are observed. Unsupported
/// callable/type surfaces return an error before their ordinary helpers;
/// they never become a smaller apparently complete graph. General pool closure
/// and APPROX derivation remain OPEN. The label solver does retain the existing
/// compressed-hub behavior when used internally on an already expanded graph.
/// Successful output/later disposal and physical allocator latency are caller
/// duties; logical requested storage/copy prepayment is not an RSS guarantee.
pub fn inspect_native_module_reachability_observed<'m, O: ExecutionObserver>(
    module: &'m Module,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<ModuleReachability<'m>, ObservedValueError> {
    admit(session, site, 1, size_of::<ModuleReachability<'m>>())?;
    let mut catalog = ModuleFunctionCatalog::new_observed(module, session, site)?;
    let mut build = native::NativeBuild::new();
    let built = build.walk(module, &catalog, session, site);
    while !catalog.entries.is_empty() {
        session.retirement_poll(site);
        catalog.entries.pop_first();
    }
    session.retirement_poll(site);
    drop(catalog);
    let result = built.and_then(|()| build.prepare(session, site));
    let solution = result.and_then(|()| solve::solve(&build.graph, session, site));
    match solution {
        Ok((certificate, parents, fallback)) => {
            let publication = session.admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            });
            if publication.is_err() {
                solve::retire_solution(certificate, parents, session, site);
                build.retire(session, site);
                return Err(ObservedValueError::AdmissionRefused);
            }
            Ok(ModuleReachability {
                module,
                census: ReachCensus {
                    graph: build.graph,
                    certificate,
                    parents,
                    fallback,
                },
                nodes: build.nodes,
            })
        }
        Err(error) => {
            build.retire(session, site);
            if session.first_refusal().is_some() {
                Err(ObservedValueError::AdmissionRefused)
            } else {
                Err(error)
            }
        }
    }
}

fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    bytes: usize,
) -> Observed<()> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Reachability,
            site,
            work,
            copy_bytes: bytes,
        })
        .map_err(Into::into)
}

fn push<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<()> {
    if values.len() == values.capacity() {
        let capacity = values
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let images = capacity
            .checked_add(values.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let bytes = images
            .checked_mul(size_of::<T>())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        admit(
            session,
            site,
            images
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            bytes,
        )?;
        values
            .try_reserve_exact(capacity - values.len())
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    admit(session, site, 1, size_of::<T>())?;
    values.push(value);
    Ok(())
}

fn filled<T: Copy, O: ExecutionObserver>(
    count: usize,
    value: T,
    output: &mut Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<()> {
    for _ in 0..count {
        push(output, value, session, site)?;
    }
    Ok(())
}

fn tree_cost<K, V, O: ExecutionObserver>(
    entries: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<()> {
    let cost = observed_btree::insertion_cost::<K, V>(entries)?;
    admit(session, site, cost.work, cost.copy_bytes)
}

fn tree_lookup<O: ExecutionObserver>(
    entries: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<()> {
    admit(session, site, observed_btree::population_work(entries)?, 0)
}

fn retire_vec<T, O: ExecutionObserver>(
    values: Vec<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    // Callers use only Copy/borrowed or statically bounded payloads here.
    session.retirement_poll(site);
    drop(values);
    session.retirement_poll(site);
}

fn retire_rows<T, O: ExecutionObserver>(
    mut rows: Vec<Vec<T>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !rows.is_empty() {
        session.retirement_poll(site);
        rows.pop();
    }
    retire_vec(rows, session, site);
}
