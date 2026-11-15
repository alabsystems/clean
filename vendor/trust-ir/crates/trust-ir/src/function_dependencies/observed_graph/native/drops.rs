// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl NativeBuild {
    pub(super) fn unresolved_drop<O: ExecutionObserver>(
        &mut self,
        from: ReachNode,
        ty: &Ty,
        location: ReachSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let owned = ty.clone_observed(session, site)?;
        let to = self.node(
            ReachNodeKind::Sink(DependencyRefusalKind::ImplicitDestructor(owned)),
            session,
            site,
        )?;
        self.drop_edge(from, to, location, session, site)
    }
    pub(super) fn drop_dependency<O: ExecutionObserver>(
        &mut self,
        from: ReachNode,
        glue: FuncId,
        location: ReachSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let key = DependencyNode::Function(glue);
        tree_lookup(self.nodes.len(), session, site)?;
        let target = self.nodes.get(&key).copied();
        let to = match target {
            Some(target) => target,
            None => self.node(
                ReachNodeKind::Sink(DependencyRefusalKind::Missing(key)),
                session,
                site,
            )?,
        };
        self.drop_edge(from, to, location, session, site)
    }
    fn drop_edge<O: ExecutionObserver>(
        &mut self,
        from: ReachNode,
        to: ReachNode,
        location: ReachSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        push(
            &mut self.graph.edges,
            ReachEdge {
                from,
                to,
                class: EdgeClass::Run,
                site: location,
                via_drop: true,
            },
            session,
            site,
        )
    }
}
