// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
mod constant;
mod drops;
mod retirement;

pub(super) struct NativeBuild {
    pub(super) graph: ExpandedReachGraph,
    pub(super) nodes: BTreeMap<DependencyNode, ReachNode>,
}

impl NativeBuild {
    pub(super) fn new() -> Self {
        Self {
            graph: ExpandedReachGraph {
                graph: NEXT_GRAPH.fetch_add(1, Ordering::Relaxed),
                nodes: Vec::new(),
                edges: Vec::new(),
                base_edges: 0,
                thread_entries: BTreeMap::new(),
                defects: Vec::new(),
                pools: ClosedPools::default(),
                derived: Derived::default(),
            },
            nodes: BTreeMap::new(),
        }
    }

    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let drop_glue = module.drop_glue_index_observed(session, site)?;
        let mut pending = Vec::new();
        let result = (|| {
            admit(session, site, 1, 0)?;
            if u32::try_from(module.globals.len()).is_err() {
                return Err(ObservedValueError::CapacityOverflow);
            }
            for function in &module.functions {
                admit(session, site, 1, 0)?;
                let key = DependencyNode::Function(function.id);
                tree_lookup(self.nodes.len(), session, site)?;
                if self.nodes.contains_key(&key) {
                    continue;
                }
                tree_lookup(catalog.len(), session, site)?;
                let definition = catalog
                    .unique(function.id)
                    .map(|_| DefinitionKey(u128::from(function.id.index())));
                let node = self.program(key, definition, session, site)?;
                // A duplicate ID is the original external Walked/UNKNOWN node.
                if definition.is_none()
                    && let ReachNodeKind::Program(spec) = &mut self.graph.nodes[node.index()]
                {
                    spec.locality = Locality::External;
                }
                push(&mut pending, key, session, site)?;
            }
            for (index, _) in module.globals.iter().enumerate() {
                admit(session, site, 1, 0)?;
                let id = u32::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?;
                let key = DependencyNode::Global(GlobalId(id));
                self.program(key, None, session, site)?;
                push(&mut pending, key, session, site)?;
            }
            for key in &pending {
                admit(session, site, 1, 0)?;
                self.expand(module, catalog, *key, &drop_glue, session, site)?;
            }
            self.graph.base_edges = self.graph.edges.len();
            Ok(())
        })();
        retire_vec(pending, session, site);
        result
    }

    fn program<O: ExecutionObserver>(
        &mut self,
        key: DependencyNode,
        definition: Option<DefinitionKey>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<ReachNode> {
        let node = self.node(
            ReachNodeKind::Program(ReachNodeSpec {
                origin: NodeOrigin::TrustIr(key),
                definition,
                locality: Locality::Local,
                body: NodeBody::Walked,
            }),
            session,
            site,
        )?;
        tree_cost::<DependencyNode, ReachNode, O>(self.nodes.len(), session, site)?;
        self.nodes.insert(key, node);
        Ok(node)
    }

    fn node<O: ExecutionObserver>(
        &mut self,
        kind: ReachNodeKind,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<ReachNode> {
        retirement::store_node(&mut self.graph, kind, session, site)
    }

    fn edge<O: ExecutionObserver>(
        &mut self,
        from: ReachNode,
        to: ReachNode,
        class: EdgeClass,
        location: ReachSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        push(
            &mut self.graph.edges,
            ReachEdge {
                from,
                to,
                class,
                site: location,
                via_drop: false,
            },
            session,
            site,
        )
    }

    fn unknown<O: ExecutionObserver>(
        &mut self,
        from: ReachNode,
        reason: DependencyRefusalKind,
        location: ReachSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let to = self.node(ReachNodeKind::Sink(reason), session, site)?;
        self.edge(from, to, EdgeClass::Run, location, session, site)
    }

    fn dependency<O: ExecutionObserver>(
        &mut self,
        from: ReachNode,
        key: DependencyNode,
        class: EdgeClass,
        location: ReachSite,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        tree_lookup(self.nodes.len(), session, site)?;
        if let Some(to) = self.nodes.get(&key).copied() {
            self.edge(from, to, class, location, session, site)
        } else {
            let to = self.node(
                ReachNodeKind::Sink(DependencyRefusalKind::Missing(key)),
                session,
                site,
            )?;
            self.edge(from, to, class, location, session, site)
        }
    }

    fn expand<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        catalog: &ModuleFunctionCatalog<'_>,
        key: DependencyNode,
        drop_glue: &crate::ObservedDropGlueIndex<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        tree_lookup(self.nodes.len(), session, site)?;
        let node = self.nodes[&key];
        let location = ReachSite::TrustIr(DependencySite::Definition(key));
        match key {
            DependencyNode::Function(id) => {
                if !module.global_asm.is_empty() {
                    self.unknown(
                        node,
                        DependencyRefusalKind::GlobalAssembly,
                        ReachSite::TrustIr(DependencySite::Module),
                        session,
                        site,
                    )?;
                }
                tree_lookup(catalog.len(), session, site)?;
                if let Some(function) = catalog.unique(id) {
                    self.body(function, node, drop_glue, session, site)
                } else {
                    self.unknown(
                        node,
                        DependencyRefusalKind::Ambiguous(key),
                        location,
                        session,
                        site,
                    )
                }
            }
            DependencyNode::Global(id) => match &module.globals[id.as_usize()].initializer {
                Some(value) => self.constant(value, session, site),
                None => {
                    let to = self.node(
                        ReachNodeKind::Sink(DependencyRefusalKind::MissingGlobalInitializer(id)),
                        session,
                        site,
                    )?;
                    self.edge(node, to, EdgeClass::Read, location, session, site)
                }
            },
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }

    fn body<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        node: ReachNode,
        drop_glue: &crate::ObservedDropGlueIndex<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        self.body_shape(function, node, session, site)?;
        for block in &function.blocks {
            admit(session, site, 1, 0)?;
            for (index, instruction) in block.body.iter().enumerate() {
                admit(session, site, 1, 0)?;
                let location = ReachSite::TrustIr(DependencySite::Instruction {
                    function: function.id,
                    block: block.id,
                    index,
                });
                self.instruction(node, &instruction.inst, location, drop_glue, session, site)?;
            }
        }
        Ok(())
    }

    fn instruction<O: ExecutionObserver>(
        &mut self,
        node: ReachNode,
        instruction: &Inst,
        location: ReachSite,
        drop_glue: &crate::ObservedDropGlueIndex<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        if let Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } = instruction {
            return match drop_glue.resolve(ty, session, site)? {
                crate::DropResolution::Resolved(glue) => {
                    self.drop_dependency(node, glue, location, session, site)
                }
                crate::DropResolution::Unresolved | crate::DropResolution::Ambiguous => {
                    self.unresolved_drop(node, ty, location, session, site)
                }
            };
        }
        // The exhaustive shared matcher sees no Drop here, so the empty index
        // cannot omit a real glue row or hide an unobserved type-key lookup.
        match instruction_reach(instruction, &crate::DropGlueIndex::default()) {
            InstructionReach::Call(id) | InstructionReach::SeqMap(id) => {
                self.dependency(
                    node,
                    DependencyNode::Function(id),
                    EdgeClass::Run,
                    location,
                    session,
                    site,
                )?;
            }
            InstructionReach::Global(id) => {
                self.dependency(
                    node,
                    DependencyNode::Global(id),
                    EdgeClass::Read,
                    location,
                    session,
                    site,
                )?;
            }
            InstructionReach::PanicSite { entry, global } => {
                self.dependency(
                    node,
                    DependencyNode::Function(entry),
                    EdgeClass::Run,
                    location,
                    session,
                    site,
                )?;
                if let Some(global) = global {
                    self.dependency(
                        node,
                        DependencyNode::Global(global),
                        EdgeClass::Read,
                        location,
                        session,
                        site,
                    )?;
                }
            }
            InstructionReach::Constant(value, _) => self.constant(value, session, site)?,
            InstructionReach::Cases(cases) => {
                for case in cases {
                    admit(session, site, 1, 0)?;
                    self.constant(&case.value, session, site)?;
                }
            }
            InstructionReach::Opaque => self.unknown(
                node,
                DependencyRefusalKind::OpaqueDialectOperation,
                location,
                session,
                site,
            )?,
            InstructionReach::Runtime(_) => self.unknown(
                node,
                DependencyRefusalKind::UnresolvedExtern,
                location,
                session,
                site,
            )?,
            InstructionReach::Cast { op, .. } if scalar_conversion(op) => {}
            InstructionReach::Nothing => {}
            InstructionReach::Closure(..)
            | InstructionReach::Indirect { .. }
            | InstructionReach::Drop(_)
            | InstructionReach::DropGlue(_)
            | InstructionReach::Cast { .. } => {
                return Err(ObservedValueError::UnsupportedValue);
            }
        }
        Ok(())
    }

    fn body_shape<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        node: ReachNode,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let location = ReachSite::TrustIr(DependencySite::Definition(DependencyNode::Function(
            function.id,
        )));
        admit(session, site, 1, 0)?;
        if function.blocks.is_empty() {
            return self.unknown(
                node,
                DependencyRefusalKind::BodylessFunction(function.id),
                location,
                session,
                site,
            );
        }
        let mut found_entry = false;
        for block in &function.blocks {
            admit(session, site, 1, 0)?;
            if block.id == function.entry {
                found_entry = true;
                break;
            }
        }
        if !found_entry {
            self.unknown(
                node,
                DependencyRefusalKind::MissingEntryBlock(function.entry),
                location,
                session,
                site,
            )?;
        }
        let mut blocks = BTreeMap::new();
        let result = (|| {
            for block in &function.blocks {
                tree_cost::<BlockId, (), O>(blocks.len(), session, site)?;
                if blocks.insert(block.id, ()).is_some() {
                    self.unknown(
                        node,
                        DependencyRefusalKind::AmbiguousBlock(block.id),
                        location,
                        session,
                        site,
                    )?;
                }
            }
            Ok(())
        })();
        while !blocks.is_empty() {
            session.retirement_poll(site);
            blocks.pop_first();
        }
        session.retirement_poll(site);
        drop(blocks);
        result
    }

    pub(super) fn prepare<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let mut unenumerated = false;
        for kind in &self.graph.nodes {
            admit(session, site, 1, 0)?;
            if matches!(kind, ReachNodeKind::Sink(_)) {
                unenumerated = true;
                break;
            }
        }
        admit(session, site, 1, size_of::<ClosedPools>())?;
        // No source pool helper has run. This constant-size constructor keeps
        // the empty universe's exact unclosed flag without calling close().
        self.graph.pools = ClosedPools::empty_with_unenumerated(unenumerated);
        self.graph.derived.hub_base = self.graph.nodes.len();
        for _ in &self.graph.nodes {
            admit(session, site, 1, 0)?;
            push(
                &mut self.graph.derived.facts_from,
                Vec::new(),
                session,
                site,
            )?;
            push(&mut self.graph.derived.hubs_of, Vec::new(), session, site)?;
        }
        Ok(())
    }

    pub(super) fn retire<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        while !self.nodes.is_empty() {
            session.retirement_poll(site);
            self.nodes.pop_first();
        }
        session.retirement_poll(site);
        drop(self.nodes);
        while !self.graph.nodes.is_empty() {
            session.retirement_step(site, 1);
            if let Some(kind) = self.graph.nodes.pop() {
                retirement::retire_node(kind, session, site);
            }
        }
        retire_vec(self.graph.nodes, session, site);
        retire_vec(self.graph.edges, session, site);
        retire_rows(self.graph.derived.facts_from, session, site);
        retire_rows(self.graph.derived.hubs_of, session, site);
        session.retirement_poll(site);
        // Remaining pool/hub/defect/thread-entry collections are empty here.
    }
}

fn scalar_conversion(op: CastOp) -> bool {
    match op {
        CastOp::Transmute
        | CastOp::Bitcast
        | CastOp::PtrToInt
        | CastOp::IntToPtr
        | CastOp::PtrToPtr => false,
        CastOp::ReifyFnPointer
        | CastOp::Trunc
        | CastOp::ZExt
        | CastOp::SExt
        | CastOp::FPTrunc
        | CastOp::FPExt
        | CastOp::FPToUI
        | CastOp::FPToSI
        | CastOp::UIToFP
        | CastOp::SIToFP
        | CastOp::FPToSISat
        | CastOp::FPToUISat => true,
    }
}
