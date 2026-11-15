// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn retire_set<T: Ord + Copy, O: ExecutionObserver>(
    values: &mut BTreeSet<T>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    // Both callers own only fixed Copy keys. No variable key Drop/Ord occurs.
    while !values.is_empty() {
        session.retirement_step(site, values.len());
        values.pop_first();
    }
    session.retirement_poll(site);
    drop(core::mem::take(values));
    session.retirement_poll(site);
}
pub(super) fn retire_closure<O: ExecutionObserver>(
    closure: Option<ThreadClosure>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    if let Some(mut closure) = closure {
        while !closure.reached.is_empty() {
            session.retirement_step(site, closure.reached.len());
            closure.reached.pop_first();
        }
        session.retirement_poll(site);
        drop(closure);
        session.retirement_poll(site);
    }
}
pub(super) fn retire_native_census<O: ExecutionObserver>(
    reachability: ModuleReachability<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    // This private caller consumes ONLY the census just constructed by the
    // native observed builder. Its pools/hubs/threads/defects are the known
    // empty native-policy fields, not arbitrary caller-supplied graph data.
    let ModuleReachability {
        module: _,
        census,
        nodes,
    } = reachability;
    let ReachCensus {
        graph,
        certificate,
        parents,
        fallback,
    } = census;
    solve::retire_solution(certificate, parents, session, site);
    match fallback {
        Some(ReachFallback::Defects(defects)) => retire_vec(defects, session, site),
        Some(ReachFallback::CertificateRejected(error)) => {
            retire_fixed(error, session, site);
        }
        None => {}
    }
    native::NativeBuild { graph, nodes }.retire(session, site);
}

fn retire_fixed<T, O: ExecutionObserver>(
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    drop(value);
    session.retirement_poll(site);
}
