// Copyright 2026 Andrew Yates | Apache-2.0
//! Explicit per-invocation graph state; ordinary serde has no hidden DAG mode.
use super::containers::{FromWire, ToWire};
use super::primitive::{Budget, Decoder, Encoder, Result, Wire};
use super::types::WExprKind;
use super::{error, MAX_DEPTH, MAX_EDGES, MAX_NODES};
use crate::{Expr, ExprKind};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Ref(pub(super) u32);
impl Wire for Ref {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.atom(|r| Ok(Self(r.u32()?)))
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.u32(self.0)
    }
}
impl ToWire for Expr {
    type Wire = Ref;
    fn to_wire(&self, p: &mut Projection) -> Result<Ref> {
        p.capture(self)
    }
}
impl ToWire for Arc<Expr> {
    type Wire = Ref;
    fn to_wire(&self, p: &mut Projection) -> Result<Ref> {
        p.capture(self)
    }
}
impl FromWire<Ref> for Expr {
    fn from_wire(wire: Ref, r: &mut Restoration) -> Result<Self> {
        r.resolve(wire.0)
    }
}
impl FromWire<Ref> for Arc<Expr> {
    fn from_wire(wire: Ref, r: &mut Restoration) -> Result<Self> {
        r.reference(wire.0)
    }
}

pub(super) struct Node {
    pub(super) id: u32,
    pub(super) kind: WExprKind,
    depth: usize,
}
#[derive(Default)]
pub(super) struct Projection {
    budget: Budget,
    by_address: HashMap<usize, u32>,
    visiting: HashSet<usize>,
    children: Vec<usize>,
    discovered: usize,
    edges: usize,
    pub(super) nodes: Vec<Node>,
}
impl Projection {
    pub(super) fn allocate(&mut self, count: usize, width: usize) -> Result<()> {
        self.budget.allocate(count, width)
    }
    pub(super) fn remaining(&self) -> usize {
        self.budget.remaining()
    }
    pub(super) fn atom<T>(&mut self, project: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.budget.enter()?;
        let result = project(self);
        self.budget.leave();
        result
    }
    fn record_depth(&mut self, depth: usize) {
        if let Some(parent) = self.children.last_mut() {
            *parent = (*parent).max(depth);
        }
    }
    fn capture(&mut self, expr: &Expr) -> Result<Ref> {
        // A DAG reference is an atom, but walking a separately encoded child
        // node must not turn its graph depth4096 into atom recursion depth256.
        self.atom(|_| Ok(()))?;
        self.edges = self
            .edges
            .checked_add(1)
            .ok_or_else(|| error("edge overflow"))?;
        if self.edges > MAX_EDGES {
            return Err(error("expression edge limit"));
        }
        let address = expr as *const Expr as usize;
        if let Some(id) = self.by_address.get(&address).copied() {
            self.record_depth(self.nodes[id as usize].depth);
            return Ok(Ref(id));
        }
        self.discovered = self
            .discovered
            .checked_add(1)
            .ok_or_else(|| error("node overflow"))?;
        if self.discovered > MAX_NODES || self.children.len() >= MAX_DEPTH {
            return Err(error("expression node/depth limit"));
        }
        self.allocate(1, size_of::<Node>().saturating_add(128))?;
        self.visiting
            .try_reserve(1)
            .map_err(|_| error("graph allocation refused"))?;
        if !self.visiting.insert(address) {
            return Err(error("cyclic expression graph"));
        }
        self.children
            .try_reserve(1)
            .map_err(|_| error("graph allocation refused"))?;
        self.children.push(0);
        // Root traversal is deterministic: fixed Environment field order,
        // canonical map keys BEFORE values, and exact sequence/kind order.
        // All inputs remain immutably borrowed until projection completes;
        // addresses are only sharing identities within this invocation.
        let kind = crate::expr::stack_safe(|| expr.dag_wire_kind().to_wire(self))?;
        let depth = self
            .children
            .pop()
            .ok_or_else(|| error("missing graph frame"))?
            .checked_add(1)
            .ok_or_else(|| error("depth overflow"))?;
        if depth > MAX_DEPTH {
            return Err(error("expression depth limit"));
        }
        let id = u32::try_from(self.nodes.len()).map_err(|_| error("node ID overflow"))?;
        self.nodes
            .try_reserve(1)
            .map_err(|_| error("graph allocation refused"))?;
        self.nodes.push(Node { id, kind, depth });
        self.visiting.remove(&address);
        self.by_address
            .try_reserve(1)
            .map_err(|_| error("graph allocation refused"))?;
        self.by_address.insert(address, id);
        self.record_depth(depth);
        Ok(Ref(id))
    }
}

pub(super) struct Restoration {
    budget: Budget,
    nodes: Vec<Option<Arc<Expr>>>,
    depths: Vec<usize>,
    current_depth: usize,
    edges: usize,
}
impl Restoration {
    pub(super) fn new(count: usize) -> Result<Self> {
        if count > MAX_NODES {
            return Err(error("expression node limit"));
        }
        let mut budget = Budget::default();
        budget.allocate(
            count,
            size_of::<Option<Arc<Expr>>>().saturating_add(size_of::<usize>()),
        )?;
        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(count)
            .map_err(|_| error("restore allocation refused"))?;
        nodes.resize_with(count, || None);
        let mut depths = Vec::new();
        depths
            .try_reserve_exact(count)
            .map_err(|_| error("restore allocation refused"))?;
        depths.resize(count, 0);
        Ok(Self {
            budget,
            nodes,
            depths,
            current_depth: 0,
            edges: 0,
        })
    }
    pub(super) fn allocate(&mut self, count: usize, width: usize) -> Result<()> {
        self.budget.allocate(count, width)
    }
    pub(super) fn atom<T>(&mut self, restore: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.budget.enter()?;
        let result = restore(self);
        self.budget.leave();
        result
    }
    fn resolve(&mut self, id: u32) -> Result<Expr> {
        self.allocate(1, size_of::<Expr>())?;
        Ok((*self.reference(id)?).clone())
    }
    fn reference(&mut self, id: u32) -> Result<Arc<Expr>> {
        self.atom(|r| {
            r.edges = r
                .edges
                .checked_add(1)
                .ok_or_else(|| error("edge overflow"))?;
            if r.edges > MAX_EDGES {
                return Err(error("expression edge limit"));
            }
            let index = usize::try_from(id).map_err(|_| error("node index overflow"))?;
            let expr = r
                .nodes
                .get(index)
                .and_then(Option::as_ref)
                .ok_or_else(|| error("unknown, cyclic or forward expression reference"))?;
            r.current_depth = r.current_depth.max(r.depths[index]);
            Ok(Arc::clone(expr))
        })
    }
    pub(super) fn node(&mut self, id: u32, wire: WExprKind) -> Result<()> {
        let index = usize::try_from(id).map_err(|_| error("node index overflow"))?;
        if self.nodes.get(index).is_none_or(Option::is_some) {
            return Err(error("duplicate/invalid node"));
        }
        self.current_depth = 0;
        let kind = ExprKind::from_wire(wire, self)?;
        if matches!(&kind,ExprKind::BVar(index) if *index>Expr::MAX_BVAR_INDEX) {
            return Err(error("invalid bound variable index"));
        }
        let depth = self
            .current_depth
            .checked_add(1)
            .ok_or_else(|| error("depth overflow"))?;
        if depth > MAX_DEPTH {
            return Err(error("expression depth limit"));
        }
        self.allocate(1, size_of::<Expr>().saturating_add(32))?;
        self.nodes[index] = Some(Arc::new(Expr::from_kind(kind)));
        self.depths[index] = depth;
        Ok(())
    }
}
