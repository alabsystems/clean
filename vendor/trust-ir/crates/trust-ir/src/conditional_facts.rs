// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conditional premises over immutable SSA values, independently of CFG shape.
//!
//! An untrusted producer suggests sparse block-entry invariants. The checker
//! separately checks every requirement and EVERY reachable incoming edge,
//! substituting block arguments and respecting branch polarity. Cyclic
//! invariants are allowed: entry and edge closure justify induction on actual
//! finite execution prefixes, not an assumption that a loop terminates.
//!
//! Operation rules are supplied semantic premises, NOT proved here. Properties
//! must concern immutable values (not mutable pointee state). Callers must also
//! validate the containing module and the exact operation-rule contracts. This
//! is a structural premise check, not source equivalence, a kernel theorem, a
//! proof-obligation discharge or permission to execute. No receipt survives a
//! mutation: checking always borrows and inspects the actual function again.
//! Invoke-produced values use shared normal-edge SSA availability; preexisting
//! immutable values may flow through both successors. Coroutine suspension is
//! not modeled by this pass.
//!
//! Storage is O(instructions + blocks + edges + suggested facts), not a dense
//! block-by-value matrix. Synthesis visits each distinct needed entry fact once;
//! work additionally includes its actual incoming edges and ordered-set lookups.
//! Dominating branch guards prove their immutable facts directly throughout
//! their dominance regions, without propagating a row through each block. Each
//! analyze/check call rebuilds its own rule-bound index from actual reachable
//! branches (validating all returned fact subjects there). Coalesced per-fact
//! intervals use O(branches) space. Construction scans blocks once, sorts the
//! intervals, and uses the existing dominance/SSA indexes plus supplied rule
//! callbacks. Point queries cost O(log blocks + log regions-for-fact); joins
//! still use the sparse incoming-edge invariant mechanism. This does not bound
//! arbitrary join-fact closure by the size of the IR.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::analysis::{DominatorTree, SsaDefinitionSite, SsaUseSite};
use crate::{BlockId, Function, Inst, InstrNode, ValueId};

/// A frontend-defined property of one immutable SSA value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConditionalFact {
    pub value: ValueId,
    pub property: u32,
}

/// A premise immediately BEFORE an actual instruction (zero-based index).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FactRequirement {
    pub block: BlockId,
    pub instruction: usize,
    pub fact: ConditionalFact,
}

/// One proposed block-entry invariant; public and deliberately untrusted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockEntryFact {
    pub block: BlockId,
    pub fact: ConditionalFact,
}

/// Sparse invariant proposal, not proof authority. The checker rejects repeated
/// rows and rechecks all rows, including those not used by a requirement.
#[derive(Debug, Clone, Default)]
pub struct ConditionalFactCertificate {
    pub entries: Vec<BlockEntryFact>,
}

/// Semantic premises supplied by an exact, separately validated rule set.
/// These callbacks inspect real instruction definitions, never producer labels.
pub trait ConditionalFactRules {
    /// Does this exact instruction establish the fact on its result?
    fn establishes(&self, node: &InstrNode, fact: ConditionalFact) -> bool;
    /// What fact follows when the named Boolean result takes this edge polarity?
    /// The condition is an actual result of `node`; returned subjects must be
    /// in scope at the branch. `None` establishes nothing.
    fn branch_fact(
        &self,
        node: &InstrNode,
        condition: ValueId,
        taken: bool,
    ) -> Option<ConditionalFact>;
}

/// Explicit invalid input, missing premise or malformed invariant proposal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionalFactError(pub String);
impl std::fmt::Display for ConditionalFactError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ConditionalFactError {}
type Result<T> = std::result::Result<T, ConditionalFactError>;
fn error(message: impl Into<String>) -> ConditionalFactError {
    ConditionalFactError(message.into())
}

#[derive(Clone, Copy)]
enum Definition {
    Parameter { block: BlockId, index: usize },
    Instruction { block: BlockId, index: usize },
}
impl Definition {
    fn site(self) -> SsaDefinitionSite {
        match self {
            Self::Parameter { block, .. } => SsaDefinitionSite {
                block,
                instruction: None,
            },
            Self::Instruction { block, index } => SsaDefinitionSite {
                block,
                instruction: Some(index),
            },
        }
    }
}

struct Edge<'a> {
    from: BlockId,
    args: &'a [ValueId],
    condition: Option<(ValueId, bool)>,
    site: SsaUseSite,
}

/// Ephemeral, rule-bound premises, never a producer-supplied certificate or a
/// cache surviving a check. Exact edge polarity is retained for join replay;
/// only edges dominating their destination contribute a direct-proof region.
#[derive(Default)]
struct GuardIndex {
    edges: HashMap<(BlockId, bool), ConditionalFact>,
    regions: HashMap<ConditionalFact, Vec<(usize, usize)>>,
}

impl GuardIndex {
    fn coalesce(&mut self) {
        for intervals in self.regions.values_mut() {
            intervals.sort_unstable();
            let mut kept = 0;
            for index in 0..intervals.len() {
                let interval = intervals[index];
                if kept > 0 && interval.0 <= intervals[kept - 1].1 {
                    intervals[kept - 1].1 = intervals[kept - 1].1.max(interval.1);
                } else {
                    intervals[kept] = interval;
                    kept += 1;
                }
            }
            intervals.truncate(kept);
        }
    }

    fn establishes(&self, fact: ConditionalFact, position: usize) -> bool {
        let Some(intervals) = self.regions.get(&fact) else {
            return false;
        };
        let next = intervals.partition_point(|interval| interval.0 <= position);
        next > 0 && position <= intervals[next - 1].1
    }

    fn edge_establishes(&self, edge: &Edge<'_>, wanted: ConditionalFact) -> bool {
        edge.condition
            .is_some_and(|(_, taken)| self.edges.get(&(edge.from, taken)) == Some(&wanted))
    }
}

/// Shared immutable indexes for proposal construction and separate replay.
pub struct ConditionalFactAnalysis<'a> {
    function: &'a Function,
    blocks: HashMap<BlockId, usize>,
    definitions: HashMap<ValueId, Definition>,
    copies: HashMap<ValueId, ValueId>,
    incoming: HashMap<BlockId, Vec<Edge<'a>>>,
    dominators: DominatorTree,
}

impl<'a> ConditionalFactAnalysis<'a> {
    pub fn new(function: &'a Function) -> Result<Self> {
        let dominators = DominatorTree::new(function);
        if !dominators.is_well_formed() {
            return Err(error("conditional facts require a well-formed CFG"));
        }
        let mut this = Self {
            function,
            blocks: HashMap::with_capacity(function.blocks.len()),
            definitions: HashMap::new(),
            copies: HashMap::new(),
            incoming: HashMap::new(),
            dominators,
        };
        for (index, block) in function.blocks.iter().enumerate() {
            this.blocks.insert(block.id, index);
            for (index, (value, _)) in block.params.iter().enumerate() {
                this.insert_definition(
                    *value,
                    Definition::Parameter {
                        block: block.id,
                        index,
                    },
                )?;
            }
            for (index, node) in block.body.iter().enumerate() {
                for value in &node.results {
                    this.insert_definition(
                        *value,
                        Definition::Instruction {
                            block: block.id,
                            index,
                        },
                    )?;
                }
            }
        }
        // Keep parallel edges distinct: then/else can have the same destination
        // but different arguments or facts. Unreachable predecessors cannot
        // supply an entry invariant and do not invalidate reachable ones.
        for block in &function.blocks {
            let terminator = &block.body.last().expect("checked CFG").inst;
            let before = SsaUseSite::BeforeInstruction {
                block: block.id,
                instruction: block.body.len() - 1,
            };
            let mut add = |target, args: &'a [ValueId], condition, site| -> Result<()> {
                if this.block(target)?.params.len() != args.len() {
                    return Err(error("conditional-fact edge argument count mismatch"));
                }
                if this.dominators.is_reachable(block.id) {
                    for arg in args {
                        this.available_at(*arg, site)?;
                    }
                    this.incoming.entry(target).or_default().push(Edge {
                        from: block.id,
                        args,
                        condition,
                        site,
                    });
                }
                Ok(())
            };
            match terminator {
                Inst::Br { target, args } => add(*target, args, None, before)?,
                Inst::CondBr {
                    cond,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    add(*then_target, then_args, Some((*cond, true)), before)?;
                    add(*else_target, else_args, Some((*cond, false)), before)?;
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    add(*default, default_args, None, before)?;
                    for case in cases {
                        add(case.target, &case.args, None, before)?;
                    }
                }
                // Amendment D, Part 2: an `InvokeIndirect` binds its call's
                // results on the normal edge exactly as an `Invoke` does.
                Inst::Invoke {
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
                    add(
                        *normal_dest,
                        normal_args,
                        None,
                        SsaUseSite::InvokeNormalEdge { block: block.id },
                    )?;
                    add(*unwind_dest, &[], None, before)?;
                }
                // Amendment P: an `AssertInvoke` binds no result, so its
                // normal-edge arguments are available before it, as a `Br`'s
                // are. Its edges carry no branch fact (conservative: a fact
                // the check implies on the normal edge is not claimed here).
                // Amendment D: a `DropInvoke` binds no result either.
                Inst::AssertInvoke {
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
                } => {
                    add(*normal_dest, normal_args, None, before)?;
                    add(*unwind_dest, &[], None, before)?;
                }
                Inst::Return { .. } | Inst::Resume { .. } | Inst::Unreachable => {}
                _ => return Err(error("unsupported conditional-fact terminator")),
            }
        }
        // Resolve Copy identities once, iteratively, even for reversed block
        // storage. Validate every chain link before memoizing its origin.
        let values: Vec<_> = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter(|node| matches!(node.inst, Inst::Copy { .. }))
            .flat_map(|node| node.results.iter().copied())
            .collect();
        let mut path = Vec::new();
        let mut seen = HashSet::new();
        for value in values {
            if this.copies.contains_key(&value) {
                continue;
            }
            let mut current = value;
            path.clear();
            debug_assert!(seen.is_empty());
            let origin = loop {
                if let Some(origin) = this.copies.get(&current) {
                    break *origin;
                }
                if !seen.insert(current) {
                    return Err(error("cyclic Copy identity in conditional facts"));
                }
                let Definition::Instruction { block, index } = this.definition(current)? else {
                    break current;
                };
                let node = &this.block(block)?.body[index];
                let Inst::Copy { operand, .. } = node.inst else {
                    break current;
                };
                if node.results.as_slice() != [current] {
                    return Err(error("Copy must have exactly one result"));
                }
                if this.dominators.is_reachable(block) {
                    this.available(operand, block, index)?;
                }
                path.push(current);
                current = operand;
            };
            this.copies.insert(current, origin);
            seen.remove(&current);
            for value in path.drain(..) {
                // Remove occupied keys individually: clearing a previously
                // deep HashSet can scan its capacity for every later short
                // chain. Scratch is reused without that repeated scan.
                seen.remove(&value);
                this.copies.insert(value, origin);
            }
        }
        Ok(this)
    }

    /// Suggest only invariants needed by the actual requirements. This search
    /// is not the checker: consumers must call `check` on its result.
    pub fn analyze(
        &self,
        rules: &impl ConditionalFactRules,
        requirements: &[FactRequirement],
    ) -> Result<ConditionalFactCertificate> {
        let guards = self.guard_index(rules)?;
        let mut entries = BTreeSet::new();
        let mut work = Vec::new();
        for requirement in requirements {
            if let Some(entry) = self.requirement_entry(rules, &guards, *requirement)?
                && entries.insert(entry)
            {
                work.push(entry);
            }
        }
        while let Some(entry) = work.pop() {
            self.check_entry_scope(entry)?;
            for edge in self.incoming.get(&entry.block).into_iter().flatten() {
                let fact = self.edge_subject(entry, edge)?;
                if !guards.edge_establishes(edge, fact)
                    && let Some(dependency) = self.at_point(rules, &guards, edge.site, fact)?
                    && entries.insert(dependency)
                {
                    work.push(dependency);
                }
            }
        }
        Ok(ConditionalFactCertificate {
            entries: entries.into_iter().collect(),
        })
    }

    /// Independently validate local invariant closure against the actual CFG.
    /// Requirements are supplied by the consumer, not chosen by the proposal.
    /// Success changes no IR proof status and confers no execution authority.
    pub fn check(
        &self,
        rules: &impl ConditionalFactRules,
        requirements: &[FactRequirement],
        certificate: &ConditionalFactCertificate,
    ) -> Result<()> {
        let entries: BTreeSet<_> = certificate.entries.iter().copied().collect();
        if entries.len() != certificate.entries.len() {
            return Err(error("duplicate conditional-fact invariant"));
        }
        // Rebuild from these rules and this borrowed function. Never trust a
        // producer's guard index, even when its certificate has no rows.
        let guards = self.guard_index(rules)?;
        for requirement in requirements {
            if let Some(entry) = self.requirement_entry(rules, &guards, *requirement)?
                && !entries.contains(&entry)
            {
                return Err(error(format!(
                    "missing conditional-fact invariant {entry:?}"
                )));
            }
        }
        for entry in &entries {
            self.check_entry_scope(*entry)?;
            for edge in self.incoming.get(&entry.block).into_iter().flatten() {
                let fact = self.edge_subject(*entry, edge)?;
                if guards.edge_establishes(edge, fact) {
                    continue;
                }
                if let Some(dependency) = self.at_point(rules, &guards, edge.site, fact)?
                    && !entries.contains(&dependency)
                {
                    return Err(error(format!(
                        "conditional fact {entry:?} is not preserved by incoming edge from {:?}",
                        edge.from
                    )));
                }
            }
        }
        Ok(())
    }

    fn insert_definition(&mut self, value: ValueId, definition: Definition) -> Result<()> {
        if self.definitions.insert(value, definition).is_some() {
            return Err(error(format!("duplicate SSA definition {value:?}")));
        }
        Ok(())
    }
    fn block(&self, id: BlockId) -> Result<&'a crate::Block> {
        self.blocks
            .get(&id)
            .map(|index| &self.function.blocks[*index])
            .ok_or_else(|| error(format!("unknown block {id:?}")))
    }
    fn definition(&self, value: ValueId) -> Result<Definition> {
        self.definitions
            .get(&value)
            .copied()
            .ok_or_else(|| error(format!("unknown SSA value {value:?}")))
    }
    fn canonical(&self, fact: ConditionalFact) -> ConditionalFact {
        ConditionalFact {
            value: self.copies.get(&fact.value).copied().unwrap_or(fact.value),
            ..fact
        }
    }
    fn available(&self, value: ValueId, block: BlockId, instruction: usize) -> Result<()> {
        self.available_at(value, SsaUseSite::BeforeInstruction { block, instruction })
    }
    fn available_at(&self, value: ValueId, site: SsaUseSite) -> Result<()> {
        let definition = self.definition(value)?;
        if self
            .dominators
            .definition_available_at(definition.site(), site)
        {
            Ok(())
        } else {
            Err(error(format!(
                "SSA value {value:?} is not available at {site:?}"
            )))
        }
    }
    fn requirement_entry(
        &self,
        rules: &impl ConditionalFactRules,
        guards: &GuardIndex,
        requirement: FactRequirement,
    ) -> Result<Option<BlockEntryFact>> {
        let block = self.block(requirement.block)?;
        if requirement.instruction >= block.body.len() {
            return Err(error(
                "conditional-fact requirement has no actual instruction",
            ));
        }
        self.definition(requirement.fact.value)?;
        if !self.dominators.is_reachable(requirement.block) {
            return Ok(None);
        }
        self.at_site(
            rules,
            guards,
            requirement.block,
            requirement.instruction,
            requirement.fact,
        )
    }
    fn at_site(
        &self,
        rules: &impl ConditionalFactRules,
        guards: &GuardIndex,
        block: BlockId,
        instruction: usize,
        fact: ConditionalFact,
    ) -> Result<Option<BlockEntryFact>> {
        self.at_point(
            rules,
            guards,
            SsaUseSite::BeforeInstruction { block, instruction },
            fact,
        )
    }
    fn at_point(
        &self,
        rules: &impl ConditionalFactRules,
        guards: &GuardIndex,
        site: SsaUseSite,
        fact: ConditionalFact,
    ) -> Result<Option<BlockEntryFact>> {
        self.available_at(fact.value, site)?;
        let block = site.block();
        let fact = self.canonical(fact);
        if self
            .dominators
            .dominance_interval(block)
            .is_some_and(|(position, _)| guards.establishes(fact, position))
        {
            return Ok(None);
        }
        if let Definition::Instruction {
            block: origin,
            index,
        } = self.definition(fact.value)?
        {
            let node = &self.block(origin)?.body[index];
            if rules.establishes(node, fact) {
                return Ok(None);
            }
            if origin == block {
                return Err(error(format!(
                    "required fact {fact:?} is not established after its definition in {block:?}"
                )));
            }
        }
        Ok(Some(BlockEntryFact { block, fact }))
    }
    fn check_entry_scope(&self, entry: BlockEntryFact) -> Result<()> {
        self.block(entry.block)?;
        if !self.dominators.is_reachable(entry.block) || entry.block == self.function.entry {
            return Err(error(
                "an entry invariant needs a reachable non-entry block",
            ));
        }
        if self.canonical(entry.fact) != entry.fact {
            return Err(error(
                "conditional-fact invariant must use canonical Copy identity",
            ));
        }
        self.available(entry.fact.value, entry.block, 0)?;
        if self.incoming.get(&entry.block).is_none_or(Vec::is_empty) {
            return Err(error(
                "conditional-fact invariant has no reachable incoming edge",
            ));
        }
        Ok(())
    }
    fn edge_subject(&self, entry: BlockEntryFact, edge: &Edge<'_>) -> Result<ConditionalFact> {
        let value = match self.definition(entry.fact.value)? {
            Definition::Parameter { block, index } if block == entry.block => edge.args[index],
            _ => entry.fact.value,
        };
        self.available_at(value, edge.site)?;
        Ok(self.canonical(ConditionalFact {
            value,
            ..entry.fact
        }))
    }
    fn guard_index(&self, rules: &impl ConditionalFactRules) -> Result<GuardIndex> {
        let mut guards = GuardIndex::default();
        for block in &self.function.blocks {
            if !self.dominators.is_reachable(block.id) {
                continue;
            }
            let Inst::CondBr {
                cond,
                then_target,
                else_target,
                ..
            } = block.body.last().expect("checked CFG").inst
            else {
                continue;
            };
            for (successor, taken, target) in [(0, true, then_target), (1, false, else_target)] {
                let Some(fact) = self.branch_fact(rules, block.id, cond, taken)? else {
                    continue;
                };
                guards.edges.insert((block.id, taken), fact);
                // Parallel then/else edges do not individually dominate a
                // shared target. A reachable alternate entry also disqualifies
                // the edge; neither case may be reduced to block dominance.
                if self.dominators.edge_dominates(block.id, successor, target) {
                    let interval = self
                        .dominators
                        .dominance_interval(target)
                        .expect("edge-dominated target is reachable");
                    guards.regions.entry(fact).or_default().push(interval);
                }
            }
        }
        guards.coalesce();
        Ok(guards)
    }

    fn branch_fact(
        &self,
        rules: &impl ConditionalFactRules,
        from: BlockId,
        condition: ValueId,
        taken: bool,
    ) -> Result<Option<ConditionalFact>> {
        let position = self.block(from)?.body.len() - 1;
        self.available(condition, from, position)?;
        let condition = self.copies.get(&condition).copied().unwrap_or(condition);
        let Definition::Instruction { block, index } = self.definition(condition)? else {
            return Ok(None);
        };
        let node = &self.block(block)?.body[index];
        let Some(fact) = rules.branch_fact(node, condition, taken) else {
            return Ok(None);
        };
        self.available(fact.value, from, position)?;
        Ok(Some(self.canonical(fact)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Block, Constant, FuncId, FuncTyId, ICmpOp, Ty};

    fn v(id: u32) -> ValueId {
        ValueId::new(id)
    }
    fn b(id: u32) -> BlockId {
        BlockId::new(id)
    }
    fn node(inst: Inst) -> InstrNode {
        InstrNode::new(inst)
    }
    fn ret() -> InstrNode {
        node(Inst::Return { values: vec![] })
    }
    fn zero(id: u32) -> InstrNode {
        node(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(v(id))
    }
    fn test(id: u32, value: u32) -> InstrNode {
        node(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U64,
            lhs: v(value),
            rhs: v(3),
        })
        .with_result(v(id))
    }
    fn copy(id: u32, from: u32) -> InstrNode {
        node(Inst::Copy {
            ty: Ty::U64,
            operand: v(from),
        })
        .with_result(v(id))
    }
    fn br(target: u32, args: &[u32]) -> InstrNode {
        node(Inst::Br {
            target: b(target),
            args: args.iter().copied().map(v).collect(),
        })
    }
    fn cond(condition: u32, yes: u32, yes_args: &[u32], no: u32, no_args: &[u32]) -> InstrNode {
        node(Inst::CondBr {
            cond: v(condition),
            then_target: b(yes),
            then_args: yes_args.iter().copied().map(v).collect(),
            else_target: b(no),
            else_args: no_args.iter().copied().map(v).collect(),
        })
    }
    fn block(id: u32, params: &[u32], body: Vec<InstrNode>) -> Block {
        let mut block = Block::new(b(id));
        block.params = params
            .iter()
            .map(|id| (v(*id), if *id == 1 { Ty::Bool } else { Ty::U64 }))
            .collect();
        block.body = body;
        block
    }
    fn function(blocks: Vec<Block>) -> Function {
        let mut f = Function::new(FuncId::new(0), "conditional", FuncTyId::new(0), b(0));
        f.blocks = blocks;
        f
    }
    fn requirement(block: u32, instruction: usize, value: u32) -> FactRequirement {
        FactRequirement {
            block: b(block),
            instruction,
            fact: ConditionalFact {
                value: v(value),
                property: 0,
            },
        }
    }
    // Test-only exact scalar rule assumptions; no frontend/dialect dependence.
    // v3 is the dominating literal zero in these fixtures.
    struct ZeroRules;
    impl ConditionalFactRules for ZeroRules {
        fn establishes(&self, node: &InstrNode, fact: ConditionalFact) -> bool {
            fact.property == 0
                && node.results.contains(&fact.value)
                && matches!(
                    node.inst,
                    Inst::Const {
                        ty: Ty::U64,
                        value: Constant::Int(0)
                    }
                )
        }
        fn branch_fact(
            &self,
            node: &InstrNode,
            condition: ValueId,
            taken: bool,
        ) -> Option<ConditionalFact> {
            if node.results.as_slice() != [condition] {
                return None;
            }
            match node.inst {
                Inst::ICmp {
                    op,
                    ty: Ty::U64,
                    lhs,
                    rhs,
                } if rhs == v(3)
                    && ((op == ICmpOp::Eq && taken) || (op == ICmpOp::Ne && !taken)) =>
                {
                    Some(ConditionalFact {
                        value: lhs,
                        property: 0,
                    })
                }
                _ => None,
            }
        }
    }
    fn diamond() -> Function {
        function(vec![
            block(0, &[0, 1, 2], vec![zero(3), cond(1, 1, &[], 2, &[])]),
            block(1, &[], vec![test(4, 0), cond(4, 4, &[0], 5, &[])]),
            block(2, &[], vec![test(5, 2), cond(5, 4, &[2], 5, &[])]),
            block(4, &[100], vec![copy(101, 100), ret()]),
            block(5, &[], vec![ret()]),
        ])
    }

    #[test]
    fn joins_require_all_edges_and_rename_their_actual_subjects() {
        let f = diamond();
        let requirements = [requirement(4, 0, 100)];
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        let cert = analysis.analyze(&ZeroRules, &requirements).unwrap();
        assert_eq!(cert.entries.len(), 1);
        analysis.check(&ZeroRules, &requirements, &cert).unwrap();
        assert!(
            analysis
                .check(
                    &ZeroRules,
                    &requirements,
                    &ConditionalFactCertificate::default()
                )
                .is_err()
        );
        for mutation in 0..3 {
            let mut wrong = f.clone();
            match mutation {
                0 => {
                    wrong.blocks[2].body[0].inst = Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::U64,
                        lhs: v(2),
                        rhs: v(3),
                    }
                }
                1 => wrong.blocks[2].body[1] = cond(5, 4, &[0], 5, &[]),
                _ => wrong.blocks[2].body[1] = br(4, &[2]),
            }
            let analysis = ConditionalFactAnalysis::new(&wrong).unwrap();
            assert!(analysis.analyze(&ZeroRules, &requirements).is_err());
            assert!(
                analysis.check(&ZeroRules, &requirements, &cert).is_err(),
                "stale certificate mutation={mutation}"
            );
        }
        let mut reordered = f.clone();
        reordered.blocks.reverse();
        ConditionalFactAnalysis::new(&reordered)
            .unwrap()
            .check(&ZeroRules, &requirements, &cert)
            .unwrap();
    }

    #[test]
    fn parallel_edges_and_switch_or_invoke_predecessors_cannot_disappear() {
        let f = function(vec![
            block(
                0,
                &[0],
                vec![zero(3), test(4, 0), cond(4, 1, &[0], 1, &[0])],
            ),
            block(1, &[10], vec![copy(11, 10), ret()]),
        ]);
        let req = [requirement(1, 0, 10)];
        assert!(
            ConditionalFactAnalysis::new(&f)
                .unwrap()
                .analyze(&ZeroRules, &req)
                .is_err()
        );
        for use_invoke in [false, true] {
            let mut f = diamond();
            f.blocks[2].body = vec![if use_invoke {
                node(Inst::Invoke {
                    callee: FuncId::new(77),
                    args: vec![],
                    normal_dest: b(4),
                    normal_args: vec![v(2)],
                    unwind_dest: b(5),
                })
            } else {
                node(Inst::Switch {
                    value: v(2),
                    default: b(4),
                    default_args: vec![v(2)],
                    cases: vec![],
                    exhaustive_enum_unreachable: false,
                })
            }];
            let analysis = ConditionalFactAnalysis::new(&f).unwrap();
            assert!(
                analysis
                    .analyze(&ZeroRules, &[requirement(4, 0, 100)])
                    .is_err()
            );
        }
    }

    #[test]
    fn cyclic_invariants_need_real_entry_seeds_and_preserved_backedges() {
        let mut f = function(vec![
            block(0, &[0, 1], vec![zero(3), br(1, &[3])]),
            block(1, &[10], vec![cond(1, 2, &[], 3, &[])]),
            block(2, &[], vec![copy(11, 10), br(1, &[11])]),
            block(3, &[], vec![copy(12, 10), ret()]),
            // Unreachable incoming edge must not create or destroy facts.
            block(4, &[], vec![br(1, &[0])]),
        ]);
        let requirements = [requirement(3, 0, 10)];
        let cert = {
            let analysis = ConditionalFactAnalysis::new(&f).unwrap();
            let cert = analysis.analyze(&ZeroRules, &requirements).unwrap();
            analysis.check(&ZeroRules, &requirements, &cert).unwrap();
            assert_eq!(cert.entries.len(), 3);
            cert
        };
        f.blocks[0].body[1] = br(1, &[0]);
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        assert!(analysis.check(&ZeroRules, &requirements, &cert).is_err());
        assert!(analysis.analyze(&ZeroRules, &requirements).is_err());
        f.blocks[0].body[1] = br(1, &[3]);
        f.blocks[2].body[1] = br(1, &[0]);
        assert!(
            ConditionalFactAnalysis::new(&f)
                .unwrap()
                .check(&ZeroRules, &requirements, &cert)
                .is_err()
        );
    }

    #[test]
    fn invoke_result_facts_are_available_only_after_normal_return() {
        // Test-only supplied callee contract: this particular Invoke returns
        // zero normally. The availability checker must not use that result
        // contract on an unwind edge. This is not a proof of a real callee.
        struct InvokeZeroRules;
        impl ConditionalFactRules for InvokeZeroRules {
            fn establishes(&self, node: &InstrNode, fact: ConditionalFact) -> bool {
                ZeroRules.establishes(node, fact)
                    || (fact.property == 0
                        && node.results.contains(&fact.value)
                        && matches!(node.inst, Inst::Invoke { callee, .. } if callee == FuncId::new(77)))
            }
            fn branch_fact(
                &self,
                node: &InstrNode,
                condition: ValueId,
                taken: bool,
            ) -> Option<ConditionalFact> {
                ZeroRules.branch_fact(node, condition, taken)
            }
        }
        let mut f = function(vec![
            block(0, &[0], vec![zero(3), test(4, 0), cond(4, 1, &[], 4, &[])]),
            block(
                1,
                &[],
                vec![
                    node(Inst::Invoke {
                        callee: FuncId::new(77),
                        args: vec![],
                        normal_dest: b(2),
                        normal_args: vec![],
                        unwind_dest: b(3),
                    })
                    .with_result(v(77)),
                ],
            ),
            block(2, &[], vec![ret()]),
            block(3, &[], vec![ret()]),
            block(4, &[], vec![ret()]),
        ]);
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        let requirements = [requirement(2, 0, 0), requirement(3, 0, 0)];
        let cert = analysis.analyze(&ZeroRules, &requirements).unwrap();
        analysis.check(&ZeroRules, &requirements, &cert).unwrap();
        assert!(
            analysis
                .analyze(&ZeroRules, &[requirement(2, 0, 77)])
                .is_err()
        );
        let requirements = [requirement(2, 0, 77)];
        let cert = analysis.analyze(&InvokeZeroRules, &requirements).unwrap();
        analysis
            .check(&InvokeZeroRules, &requirements, &cert)
            .unwrap();
        assert!(
            analysis
                .check(&InvokeZeroRules, &[requirement(3, 0, 77)], &cert)
                .is_err()
        );
        // Ordinary normal-dominated Copies retain the edge-defined value.
        f.blocks[2].body.insert(0, copy(78, 77));
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        let requirements = [requirement(2, 1, 78)];
        let cert = analysis.analyze(&InvokeZeroRules, &requirements).unwrap();
        analysis
            .check(&InvokeZeroRules, &requirements, &cert)
            .unwrap();
        f.blocks[2].body.remove(0);
        // An unwind Copy must not launder a result unavailable on this edge.
        f.blocks[3].body.insert(0, copy(78, 77));
        assert!(ConditionalFactAnalysis::new(&f).is_err());
        f.blocks[3].body.remove(0);
        // The result exists when passing the actual normal-edge argument,
        // even though it does not exist before the terminating Invoke.
        f.blocks[2].params.push((v(78), Ty::U64));
        if let Inst::Invoke { normal_args, .. } = &mut f.blocks[1].body[0].inst {
            normal_args.push(v(77));
        }
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        let requirements = [requirement(2, 0, 78)];
        let cert = analysis.analyze(&InvokeZeroRules, &requirements).unwrap();
        analysis
            .check(&InvokeZeroRules, &requirements, &cert)
            .unwrap();
        // A reachable alternate incoming value still needs its own premise.
        f.blocks[3].body[0] = br(2, &[79]);
        f.blocks[0].params.push((v(79), Ty::U64));
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        assert!(
            analysis
                .check(&InvokeZeroRules, &requirements, &cert)
                .is_err()
        );
    }

    #[test]
    fn forged_rows_use_sites_dominance_and_new_definitions_are_rejected() {
        let mut f = diamond();
        let requirements = [requirement(4, 0, 100)];
        let good = ConditionalFactAnalysis::new(&f)
            .unwrap()
            .analyze(&ZeroRules, &requirements)
            .unwrap();
        for extra in [
            good.entries[0],
            BlockEntryFact {
                block: b(0),
                fact: ConditionalFact {
                    value: v(0),
                    property: 0,
                },
            },
            BlockEntryFact {
                block: b(4),
                fact: ConditionalFact {
                    value: v(101),
                    property: 0,
                },
            },
            BlockEntryFact {
                block: b(99),
                fact: ConditionalFact {
                    value: v(0),
                    property: 0,
                },
            },
        ] {
            let mut forged = good.clone();
            forged.entries.push(extra);
            assert!(
                ConditionalFactAnalysis::new(&f)
                    .unwrap()
                    .check(&ZeroRules, &requirements, &forged)
                    .is_err()
            );
        }
        for req in [
            requirement(4, 0, 101),
            requirement(4, 99, 100),
            requirement(4, 0, 999),
            requirement(2, 0, 4),
        ] {
            assert!(
                ConditionalFactAnalysis::new(&f)
                    .unwrap()
                    .analyze(&ZeroRules, &[req])
                    .is_err()
            );
        }
        // The new value is not the old guarded value, even with identical type.
        f.blocks[3].body.insert(
            0,
            node(Inst::Call {
                callee: FuncId::new(4),
                args: vec![],
            })
            .with_result(v(102)),
        );
        assert!(
            ConditionalFactAnalysis::new(&f)
                .unwrap()
                .analyze(&ZeroRules, &[requirement(4, 1, 102)])
                .is_err()
        );
    }

    #[test]
    fn guard_and_subject_copies_preserve_polarity_without_recomputing_values() {
        let mut f = function(vec![
            block(
                0,
                &[0],
                vec![
                    zero(3),
                    copy(6, 0),
                    test(4, 6),
                    node(Inst::Copy {
                        ty: Ty::Bool,
                        operand: v(4),
                    })
                    .with_result(v(7)),
                    cond(7, 1, &[0], 2, &[]),
                ],
            ),
            block(1, &[10], vec![copy(11, 10), ret()]),
            block(2, &[], vec![ret()]),
        ]);
        let requirements = [requirement(1, 0, 10)];
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        analysis
            .check(
                &ZeroRules,
                &requirements,
                &analysis.analyze(&ZeroRules, &requirements).unwrap(),
            )
            .unwrap();
        f.blocks[0].body[2].inst = Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::U64,
            lhs: v(6),
            rhs: v(3),
        };
        f.blocks[0].body[4] = cond(7, 2, &[], 1, &[0]);
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        analysis
            .check(
                &ZeroRules,
                &requirements,
                &analysis.analyze(&ZeroRules, &requirements).unwrap(),
            )
            .unwrap();
    }

    #[test]
    fn shared_requirements_and_long_copy_cfg_chains_have_sparse_invariants() {
        const BLOCKS: u32 = 513;
        const COPIES: u32 = 4096;
        let mut blocks = vec![block(
            0,
            &[0],
            vec![zero(3), test(4, 0), cond(4, 1, &[], BLOCKS, &[])],
        )];
        for id in 1..BLOCKS {
            blocks.push(block(
                id,
                &[],
                if id + 1 == BLOCKS {
                    vec![]
                } else {
                    vec![br(id + 1, &[])]
                },
            ));
        }
        let last = blocks.last_mut().unwrap();
        for i in 0..COPIES {
            last.body
                .push(copy(10000 + i, if i == 0 { 0 } else { 9999 + i }));
        }
        last.body.push(ret());
        blocks.push(block(BLOCKS, &[], vec![ret()]));
        let mut f = function(blocks);
        f.blocks.reverse();
        let requirements = vec![requirement(BLOCKS - 1, COPIES as usize, 10000 + COPIES - 1); 2000];
        let analysis = ConditionalFactAnalysis::new(&f).unwrap();
        let cert = analysis.analyze(&ZeroRules, &requirements).unwrap();
        assert!(cert.entries.is_empty());
        analysis.check(&ZeroRules, &requirements, &cert).unwrap();
    }
}

#[cfg(test)]
#[path = "conditional_facts/guard_tests.rs"]
mod guard_tests;
