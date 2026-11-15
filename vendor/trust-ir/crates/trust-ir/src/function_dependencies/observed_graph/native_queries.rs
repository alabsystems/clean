// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual request-root queries and retirement of their native-policy census.
use super::*;
use crate::request::{NativeVerificationBundle, NativeVerificationRequest};
mod custody;
#[cfg(test)]
mod tests;

#[derive(Default)]
struct Query<'m> {
    reachability: Option<ModuleReachability<'m>>,
    closure: Option<ThreadClosure>,
    reached: BTreeSet<ReachNode>,
    functions: BTreeSet<FuncId>,
}
impl NativeVerificationBundle {
    /// The exact stored functions reached by this bundle's TrustMc requests
    /// under the native declaration policy. This executes the real observed
    /// graph construction, solve/check and per-root thread closure, then drops
    /// their owned census/scratch before final publication. All layers borrow
    /// the same original session; catalog declaration visits retain their
    /// actual function IDs, and other events retain the request site. No new
    /// owner is captured.
    ///
    /// A missing/ambiguous reached ID returns InvalidRange; a census fallback
    /// or unsupported graph constituent returns UnsupportedValue. Neither is
    /// an accepting substitute for the original detailed native diagnostic.
    /// Other UNKNOWN sinks remain in closure exactly as in the ordinary query.
    /// This does not validate the module/bundle, authorize source, or establish
    /// proof. Successful fixed-ID set disposal remains caller-owned.
    pub fn trust_mc_reached_functions_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<BTreeSet<FuncId>> {
        admit(session, site, 1, size_of::<Query<'_>>())?;
        let mut state = Query::default();
        let result = (|| {
            state.reachability = Some(inspect_native_module_reachability_observed(
                &self.module,
                session,
                site,
            )?);
            state.collect(&self.requests, session, site)
        })();
        state.retire_scratch(session, site);
        let result = result.and_then(|()| {
            session.admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 1,
                copy_bytes: size_of::<BTreeSet<FuncId>>(),
            })?;
            Ok(())
        });
        match result {
            Ok(()) => Ok(core::mem::take(&mut state.functions)),
            Err(error) => {
                custody::retire_set(&mut state.functions, session, site);
                if session.first_refusal().is_some() {
                    Err(ObservedValueError::AdmissionRefused)
                } else {
                    Err(error)
                }
            }
        }
    }
}
impl Query<'_> {
    fn collect<O: ExecutionObserver>(
        &mut self,
        requests: &[NativeVerificationRequest],
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        admit(session, site, 1, 0)?;
        let Some(reachability) = &self.reachability else {
            return Err(ObservedValueError::InvalidRange);
        };
        if reachability.census.fallback.is_some() {
            return Err(ObservedValueError::UnsupportedValue);
        }
        for request in requests {
            admit(session, site, 1, 0)?;
            if let NativeVerificationRequest::TrustMc(request) = request {
                tree_lookup(reachability.nodes.len(), session, site)?;
                let Some(root) = reachability.node(DependencyNode::Function(request.function))
                else {
                    return Err(ObservedValueError::InvalidRange);
                };
                tree_lookup(self.reached.len(), session, site)?;
                if self.reached.contains(&root) {
                    continue;
                }
                self.closure = Some(reachability.census.thread_closure_observed(
                    Some(root),
                    session,
                    site,
                )?);
                if let Some(closure) = &self.closure {
                    let mut nodes = closure.reached.keys();
                    loop {
                        tree_lookup(closure.reached.len(), session, site)?;
                        let Some(node) = nodes.next() else { break };
                        tree_cost::<ReachNode, (), O>(self.reached.len(), session, site)?;
                        admit(session, site, 1, size_of::<ReachNode>())?;
                        self.reached.insert(*node);
                    }
                }
                custody::retire_closure(self.closure.take(), session, site);
            }
        }
        while !self.reached.is_empty() {
            tree_lookup(self.reached.len(), session, site)?;
            let Some(node) = self.reached.pop_first() else {
                break;
            };
            admit(session, site, 1, 0)?;
            match reachability.census.graph.nodes.get(node.index()) {
                Some(ReachNodeKind::Program(ReachNodeSpec {
                    origin: NodeOrigin::TrustIr(DependencyNode::Function(id)),
                    ..
                })) => {
                    tree_cost::<FuncId, (), O>(self.functions.len(), session, site)?;
                    admit(session, site, 1, size_of::<FuncId>())?;
                    self.functions.insert(*id);
                }
                Some(ReachNodeKind::Sink(
                    DependencyRefusalKind::Missing(_) | DependencyRefusalKind::Ambiguous(_),
                )) => {
                    return Err(ObservedValueError::InvalidRange);
                }
                _ => {}
            }
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        custody::retire_closure(self.closure.take(), session, site);
        custody::retire_set(&mut self.reached, session, site);
        if let Some(reachability) = self.reachability.take() {
            custody::retire_native_census(reachability, session, site);
        }
    }
}
