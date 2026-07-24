// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared CFG and SSA utilities.
//!
//! This module provides a generic basic-block CFG abstraction that can be
//! reused by multiple IRs. Control-flow structure is represented directly in
//! the CFG while IR-specific instruction and terminator payloads remain
//! generic.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Generic basic block representation.
///
/// `L` is the block label type and `P` is the block-parameter type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlock<I, T, L = u32, P = ()> {
    /// Block label.
    pub label: L,
    /// SSA block parameters.
    pub params: Vec<P>,
    /// Sequential instructions in the block.
    pub instructions: Vec<I>,
    /// Control-flow terminator.
    pub terminator: T,
}

impl<I, T, L, P> BasicBlock<I, T, L, P> {
    /// Create a block with no parameters or instructions.
    pub fn new(label: L, terminator: T) -> Self {
        Self {
            label,
            params: Vec::new(),
            instructions: Vec::new(),
            terminator,
        }
    }

    /// Create a block with parameters.
    pub fn with_params(label: L, params: Vec<P>, terminator: T) -> Self {
        Self {
            label,
            params,
            instructions: Vec::new(),
            terminator,
        }
    }

    /// Create a block with parameters and instructions.
    pub fn with_body(label: L, params: Vec<P>, instructions: Vec<I>, terminator: T) -> Self {
        Self {
            label,
            params,
            instructions,
            terminator,
        }
    }

    /// Append an instruction to the block.
    pub fn add_instruction(&mut self, instruction: I) {
        self.instructions.push(instruction);
    }

    /// Append a parameter to the block.
    pub fn add_param(&mut self, param: P) {
        self.params.push(param);
    }
}

/// Terminator adapter for CFG successor discovery.
pub trait Successors<L> {
    /// Return successor labels for this terminator.
    fn successors(&self) -> Vec<L>;
}

/// Control-flow graph rooted at `entry`.
#[derive(Clone, Debug)]
pub struct Cfg<I, T, L = u32, P = ()> {
    /// Entry block label.
    pub entry: L,
    /// All blocks in the graph keyed by label.
    pub blocks: HashMap<L, BasicBlock<I, T, L, P>>,
}

impl<I, T, L, P> Cfg<I, T, L, P>
where
    L: Clone + Eq + Hash,
{
    /// Create a CFG from an entry label and block map.
    pub fn new(entry: L, blocks: HashMap<L, BasicBlock<I, T, L, P>>) -> Result<Self, CfgError<L>> {
        if !blocks.contains_key(&entry) {
            return Err(CfgError::MissingEntry {
                entry: entry.clone(),
            });
        }

        for (key, block) in &blocks {
            if key != &block.label {
                return Err(CfgError::MismatchedBlockLabel {
                    key: key.clone(),
                    block: block.label.clone(),
                });
            }
        }

        Ok(Self { entry, blocks })
    }

    /// Look up a block by label.
    pub fn block(&self, label: &L) -> Option<&BasicBlock<I, T, L, P>> {
        self.blocks.get(label)
    }

    /// Return successors for a specific block.
    pub fn successors(&self, label: &L) -> Result<Vec<L>, CfgError<L>>
    where
        T: Successors<L>,
    {
        let block = self
            .blocks
            .get(label)
            .ok_or_else(|| CfgError::MissingBlock {
                label: label.clone(),
            })?;
        let successors = block.terminator.successors();
        for successor in &successors {
            if !self.blocks.contains_key(successor) {
                return Err(CfgError::DanglingEdge {
                    from: label.clone(),
                    to: successor.clone(),
                });
            }
        }
        Ok(successors)
    }

    /// Return the successor map for the whole graph.
    pub fn successor_map(&self) -> Result<HashMap<L, Vec<L>>, CfgError<L>>
    where
        T: Successors<L>,
    {
        let mut map = HashMap::with_capacity(self.blocks.len());
        for label in self.blocks.keys() {
            map.insert(label.clone(), self.successors(label)?);
        }
        Ok(map)
    }

    /// Return the predecessor map for the whole graph.
    pub fn predecessor_map(&self) -> Result<HashMap<L, HashSet<L>>, CfgError<L>>
    where
        T: Successors<L>,
    {
        let successors = self.successor_map()?;
        let mut predecessors = HashMap::with_capacity(self.blocks.len());

        for label in self.blocks.keys() {
            predecessors.insert(label.clone(), HashSet::new());
        }

        for (source, targets) in successors {
            for target in targets {
                // `successor_map` already validated every target against the
                // block map, so this entry always exists; `entry` keeps the
                // lookup panic-free.
                predecessors
                    .entry(target)
                    .or_default()
                    .insert(source.clone());
            }
        }

        Ok(predecessors)
    }

    /// Return the predecessors for a specific block.
    pub fn predecessors(&self, label: &L) -> Result<HashSet<L>, CfgError<L>>
    where
        T: Successors<L>,
    {
        let predecessors = self.predecessor_map()?;
        predecessors
            .get(label)
            .cloned()
            .ok_or_else(|| CfgError::MissingBlock {
                label: label.clone(),
            })
    }

    /// Return the reachable block set from the entry.
    pub fn reachable_blocks(&self) -> Result<HashSet<L>, CfgError<L>>
    where
        T: Successors<L>,
    {
        let successors = self.successor_map()?;
        let mut reachable = HashSet::new();
        let mut worklist = vec![self.entry.clone()];

        while let Some(block) = worklist.pop() {
            if !reachable.insert(block.clone()) {
                continue;
            }

            if let Some(targets) = successors.get(&block) {
                for target in targets {
                    if !reachable.contains(target) {
                        worklist.push(target.clone());
                    }
                }
            }
        }

        Ok(reachable)
    }

    /// Compute the block dominator tree with a simple iterative algorithm.
    pub fn dominator_tree(&self) -> Result<DominatorTree<L>, CfgError<L>>
    where
        T: Successors<L>,
    {
        let predecessors = self.predecessor_map()?;
        let reachable = self.reachable_blocks()?;
        let mut dominators = HashMap::<L, HashSet<L>>::with_capacity(reachable.len());

        for block in &reachable {
            let initial = if block == &self.entry {
                HashSet::from([block.clone()])
            } else {
                reachable.clone()
            };
            dominators.insert(block.clone(), initial);
        }

        let mut changed = true;
        while changed {
            changed = false;

            for block in reachable.iter().filter(|label| *label != &self.entry) {
                let block_predecessors = predecessors
                    .get(block)
                    .into_iter()
                    .flat_map(|preds| preds.iter())
                    .filter(|pred| reachable.contains(*pred))
                    .cloned()
                    .collect::<Vec<_>>();

                let mut pred_iter = block_predecessors.into_iter();
                let mut updated = match pred_iter.next() {
                    None => HashSet::new(),
                    Some(first_pred) => {
                        let first = dominators.get(&first_pred).cloned().unwrap_or_default();
                        pred_iter.fold(first, |acc, pred| {
                            let other = dominators.get(&pred).cloned().unwrap_or_default();
                            acc.intersection(&other).cloned().collect()
                        })
                    }
                };
                updated.insert(block.clone());

                if dominators.get(block) != Some(&updated) {
                    dominators.insert(block.clone(), updated);
                    changed = true;
                }
            }
        }

        let mut immediate_dominators = HashMap::new();
        let mut children = reachable
            .iter()
            .cloned()
            .map(|label| (label, Vec::new()))
            .collect::<HashMap<_, _>>();

        for block in reachable.iter().filter(|label| *label != &self.entry) {
            let strict_dominators = dominators
                .get(block)
                .into_iter()
                .flat_map(|doms| doms.iter())
                .filter(|candidate| *candidate != block)
                .cloned()
                .collect::<Vec<_>>();

            let immediate_dominator = strict_dominators
                .iter()
                .find(|candidate| {
                    strict_dominators.iter().all(|other| {
                        other == *candidate
                            || !dominators
                                .get(other)
                                .is_some_and(|other_doms| other_doms.contains(*candidate))
                    })
                })
                .cloned();

            if let Some(idom) = immediate_dominator {
                // `idom` is drawn from the dominator sets over reachable
                // blocks, all of which were initialized in `children` above;
                // `entry` keeps the lookup panic-free.
                children
                    .entry(idom.clone())
                    .or_default()
                    .push(block.clone());
                immediate_dominators.insert(block.clone(), idom);
            }
        }

        Ok(DominatorTree {
            entry: self.entry.clone(),
            reachable,
            dominators,
            immediate_dominators,
            children,
        })
    }

    /// Validate SSA dominance for reachable blocks.
    ///
    /// Block parameters are treated as definitions at block entry, instruction
    /// definitions occur after that instruction's uses, and terminator
    /// definitions occur after all instruction uses in the block.
    pub fn validate_ssa<V, ParamDefs, InstructionSsa, TerminatorSsa>(
        &self,
        param_defs: ParamDefs,
        instruction_ssa: InstructionSsa,
        terminator_ssa: TerminatorSsa,
    ) -> Result<(), SsaValidationError<L, V>>
    where
        T: Successors<L>,
        V: Clone + Eq + Hash,
        ParamDefs: Fn(&P) -> Vec<V>,
        InstructionSsa: Fn(&I) -> SsaInfo<V>,
        TerminatorSsa: Fn(&T) -> SsaInfo<V>,
    {
        let dominators = self.dominator_tree()?;
        let mut definitions = HashMap::<V, DefinitionSite<L>>::new();

        for label in &dominators.reachable {
            // Reachable labels are produced from `self.blocks`, so the lookup
            // always succeeds; skip rather than panic if that ever changed.
            let Some(block) = self.blocks.get(label) else {
                continue;
            };

            for (param_index, param) in block.params.iter().enumerate() {
                for value in param_defs(param) {
                    let site = DefinitionSite {
                        block: label.clone(),
                        position: SsaPosition::Param(param_index),
                    };
                    Self::insert_definition(&mut definitions, value, site)?;
                }
            }

            for (instruction_index, instruction) in block.instructions.iter().enumerate() {
                let ssa = instruction_ssa(instruction);
                for value in ssa.defs {
                    let site = DefinitionSite {
                        block: label.clone(),
                        position: SsaPosition::Instruction(instruction_index),
                    };
                    Self::insert_definition(&mut definitions, value, site)?;
                }
            }

            let terminator = terminator_ssa(&block.terminator);
            for value in terminator.defs {
                let site = DefinitionSite {
                    block: label.clone(),
                    position: SsaPosition::Terminator,
                };
                Self::insert_definition(&mut definitions, value, site)?;
            }
        }

        for label in &dominators.reachable {
            // Reachable labels are produced from `self.blocks`, so the lookup
            // always succeeds; skip rather than panic if that ever changed.
            let Some(block) = self.blocks.get(label) else {
                continue;
            };

            for (instruction_index, instruction) in block.instructions.iter().enumerate() {
                let ssa = instruction_ssa(instruction);
                let use_site = UseSite {
                    block: label.clone(),
                    position: SsaPosition::Instruction(instruction_index),
                };
                Self::validate_uses(&definitions, &dominators, ssa.uses, use_site)?;
            }

            let terminator = terminator_ssa(&block.terminator);
            let use_site = UseSite {
                block: label.clone(),
                position: SsaPosition::Terminator,
            };
            Self::validate_uses(&definitions, &dominators, terminator.uses, use_site)?;
        }

        Ok(())
    }

    fn insert_definition<V>(
        definitions: &mut HashMap<V, DefinitionSite<L>>,
        value: V,
        site: DefinitionSite<L>,
    ) -> Result<(), SsaValidationError<L, V>>
    where
        V: Clone + Eq + Hash,
    {
        if let Some(first) = definitions.insert(value.clone(), site.clone()) {
            return Err(SsaValidationError::DuplicateDefinition {
                value,
                first,
                second: site,
            });
        }
        Ok(())
    }

    fn validate_uses<V>(
        definitions: &HashMap<V, DefinitionSite<L>>,
        dominators: &DominatorTree<L>,
        uses: Vec<V>,
        use_site: UseSite<L>,
    ) -> Result<(), SsaValidationError<L, V>>
    where
        V: Clone + Eq + Hash,
    {
        for value in uses {
            let Some(definition_site) = definitions.get(&value) else {
                return Err(SsaValidationError::UndefinedUse {
                    value,
                    use_site: use_site.clone(),
                });
            };

            if !Self::definition_dominates_use(dominators, definition_site, &use_site) {
                return Err(SsaValidationError::UseNotDominated {
                    value,
                    def_site: definition_site.clone(),
                    use_site: use_site.clone(),
                });
            }
        }

        Ok(())
    }

    fn definition_dominates_use(
        dominators: &DominatorTree<L>,
        definition_site: &DefinitionSite<L>,
        use_site: &UseSite<L>,
    ) -> bool {
        if definition_site.block == use_site.block {
            return match (&definition_site.position, &use_site.position) {
                (SsaPosition::Param(_), _) => true,
                (SsaPosition::Instruction(def_index), SsaPosition::Instruction(use_index)) => {
                    def_index < use_index
                }
                (SsaPosition::Instruction(_), SsaPosition::Terminator) => true,
                (SsaPosition::Terminator, SsaPosition::Terminator) => false,
                (SsaPosition::Terminator, SsaPosition::Instruction(_)) => false,
                (SsaPosition::Instruction(_), SsaPosition::Param(_)) => false,
                (SsaPosition::Terminator, SsaPosition::Param(_)) => false,
            };
        }

        dominators.dominates(&definition_site.block, &use_site.block)
    }
}

/// Incremental CFG builder.
#[derive(Clone, Debug)]
pub struct CfgBuilder<I, T, L = u32, P = ()> {
    entry: L,
    blocks: HashMap<L, BasicBlock<I, T, L, P>>,
}

impl<I, T, L, P> CfgBuilder<I, T, L, P>
where
    L: Clone + Eq + Hash,
{
    /// Create an empty builder with the given entry label.
    pub fn new(entry: L) -> Self {
        Self {
            entry,
            blocks: HashMap::new(),
        }
    }

    /// Add a block to the graph.
    pub fn add_block(&mut self, block: BasicBlock<I, T, L, P>) -> Result<(), CfgError<L>> {
        let label = block.label.clone();
        if self.blocks.insert(label.clone(), block).is_some() {
            return Err(CfgError::DuplicateBlock { label });
        }
        Ok(())
    }

    /// Consume the builder and produce a CFG.
    pub fn build(self) -> Result<Cfg<I, T, L, P>, CfgError<L>> {
        Cfg::new(self.entry, self.blocks)
    }
}

/// CFG construction and integrity errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgError<L> {
    /// Two blocks shared the same label in a builder.
    DuplicateBlock { label: L },
    /// The entry label did not exist in the block map.
    MissingEntry { entry: L },
    /// A requested block label did not exist.
    MissingBlock { label: L },
    /// The hash-map key and block label disagreed.
    MismatchedBlockLabel { key: L, block: L },
    /// A terminator referenced a non-existent block.
    DanglingEdge { from: L, to: L },
}

/// Dominator information for reachable blocks.
#[derive(Clone, Debug)]
pub struct DominatorTree<L> {
    entry: L,
    reachable: HashSet<L>,
    dominators: HashMap<L, HashSet<L>>,
    immediate_dominators: HashMap<L, L>,
    children: HashMap<L, Vec<L>>,
}

impl<L> DominatorTree<L>
where
    L: Clone + Eq + Hash,
{
    /// Entry block label.
    pub fn entry(&self) -> &L {
        &self.entry
    }

    /// Return whether a block is reachable from the entry.
    pub fn is_reachable(&self, label: &L) -> bool {
        self.reachable.contains(label)
    }

    /// Dominator set for a block, if reachable.
    pub fn dominators(&self, label: &L) -> Option<&HashSet<L>> {
        self.dominators.get(label)
    }

    /// Return whether `dominator` dominates `block`.
    pub fn dominates(&self, dominator: &L, block: &L) -> bool {
        self.dominators
            .get(block)
            .is_some_and(|doms| doms.contains(dominator))
    }

    /// Immediate dominator for a non-entry reachable block.
    pub fn immediate_dominator(&self, label: &L) -> Option<&L> {
        self.immediate_dominators.get(label)
    }

    /// Dominator-tree children for a block, if reachable.
    pub fn children(&self, label: &L) -> Option<&[L]> {
        self.children.get(label).map(Vec::as_slice)
    }
}

/// SSA defs/uses for an instruction or terminator.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SsaInfo<V> {
    /// Values defined by this node.
    pub defs: Vec<V>,
    /// Values used by this node.
    pub uses: Vec<V>,
}

impl<V> SsaInfo<V> {
    /// Construct explicit defs/uses information.
    pub fn new(defs: Vec<V>, uses: Vec<V>) -> Self {
        Self { defs, uses }
    }

    /// Construct a defs-only record.
    pub fn defs(defs: Vec<V>) -> Self {
        Self {
            defs,
            uses: Vec::new(),
        }
    }

    /// Construct a uses-only record.
    pub fn uses(uses: Vec<V>) -> Self {
        Self {
            defs: Vec::new(),
            uses,
        }
    }
}

/// Position of a definition or use within a block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SsaPosition {
    /// Block parameter at the given index.
    Param(usize),
    /// Instruction at the given index.
    Instruction(usize),
    /// Block terminator.
    Terminator,
}

/// SSA definition site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionSite<L> {
    /// Block containing the definition.
    pub block: L,
    /// Position within the block.
    pub position: SsaPosition,
}

/// SSA use site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UseSite<L> {
    /// Block containing the use.
    pub block: L,
    /// Position within the block.
    pub position: SsaPosition,
}

/// SSA validation errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SsaValidationError<L, V> {
    /// Underlying CFG was malformed.
    Cfg(CfgError<L>),
    /// A value was defined more than once.
    DuplicateDefinition {
        value: V,
        first: DefinitionSite<L>,
        second: DefinitionSite<L>,
    },
    /// A use had no matching definition.
    UndefinedUse { value: V, use_site: UseSite<L> },
    /// A definition existed but did not dominate a use.
    UseNotDominated {
        value: V,
        def_site: DefinitionSite<L>,
        use_site: UseSite<L>,
    },
}

impl<L, V> From<CfgError<L>> for SsaValidationError<L, V> {
    fn from(value: CfgError<L>) -> Self {
        Self::Cfg(value)
    }
}

#[cfg(test)]
mod tests {
    use super::{BasicBlock, CfgBuilder, SsaInfo, SsaValidationError, Successors};

    use std::collections::HashSet;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum TestInstruction {
        Op {
            defs: Vec<&'static str>,
            uses: Vec<&'static str>,
        },
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum TestTerminator {
        Return {
            uses: Vec<&'static str>,
        },
        Goto {
            target: u32,
            uses: Vec<&'static str>,
        },
        Branch {
            then_target: u32,
            else_target: u32,
            uses: Vec<&'static str>,
        },
    }

    impl Successors<u32> for TestTerminator {
        fn successors(&self) -> Vec<u32> {
            match self {
                TestTerminator::Return { .. } => Vec::new(),
                TestTerminator::Goto { target, .. } => vec![*target],
                TestTerminator::Branch {
                    then_target,
                    else_target,
                    ..
                } => vec![*then_target, *else_target],
            }
        }
    }

    fn cfg_builder() -> CfgBuilder<TestInstruction, TestTerminator, u32, &'static str> {
        CfgBuilder::new(0)
    }

    fn op(defs: &[&'static str], uses: &[&'static str]) -> TestInstruction {
        TestInstruction::Op {
            defs: defs.to_vec(),
            uses: uses.to_vec(),
        }
    }

    fn instruction_ssa(instruction: &TestInstruction) -> SsaInfo<&'static str> {
        match instruction {
            TestInstruction::Op { defs, uses } => SsaInfo::new(defs.clone(), uses.clone()),
        }
    }

    fn terminator_ssa(terminator: &TestTerminator) -> SsaInfo<&'static str> {
        match terminator {
            TestTerminator::Return { uses }
            | TestTerminator::Goto { uses, .. }
            | TestTerminator::Branch { uses, .. } => SsaInfo::uses(uses.clone()),
        }
    }

    #[test]
    fn cfg_builder_constructs_blocks() {
        let mut builder = cfg_builder();
        builder
            .add_block(BasicBlock::new(
                0,
                TestTerminator::Goto {
                    target: 1,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::new(1, TestTerminator::Return { uses: vec![] }))
            .unwrap();

        let cfg = builder.build().unwrap();
        assert_eq!(cfg.entry, 0);
        assert_eq!(cfg.blocks.len(), 2);
        assert!(cfg.block(&1).is_some());
    }

    #[test]
    fn predecessor_map_handles_diamond_cfg() {
        let cfg = diamond_cfg();
        let predecessors = cfg.predecessor_map().unwrap();

        assert!(predecessors.get(&0).unwrap().is_empty());
        assert_eq!(predecessors.get(&1).unwrap(), &HashSet::from([0]));
        assert_eq!(predecessors.get(&2).unwrap(), &HashSet::from([0]));
        assert_eq!(predecessors.get(&3).unwrap(), &HashSet::from([1, 2]));
    }

    #[test]
    fn dominator_tree_handles_diamond_cfg() {
        let cfg = diamond_cfg();
        let dominators = cfg.dominator_tree().unwrap();

        assert!(dominators.dominates(&0, &0));
        assert!(dominators.dominates(&0, &1));
        assert!(dominators.dominates(&0, &2));
        assert!(dominators.dominates(&0, &3));
        assert!(!dominators.dominates(&1, &3));
        assert_eq!(dominators.immediate_dominator(&1), Some(&0));
        assert_eq!(dominators.immediate_dominator(&2), Some(&0));
        assert_eq!(dominators.immediate_dominator(&3), Some(&0));
    }

    #[test]
    fn ssa_validation_rejects_non_dominating_definition() {
        let mut builder = cfg_builder();
        builder
            .add_block(BasicBlock::new(
                0,
                TestTerminator::Branch {
                    then_target: 1,
                    else_target: 2,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::with_body(
                1,
                vec![],
                vec![op(&["x"], &[])],
                TestTerminator::Goto {
                    target: 3,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::new(
                2,
                TestTerminator::Goto {
                    target: 3,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::with_body(
                3,
                vec![],
                vec![op(&[], &["x"])],
                TestTerminator::Return { uses: vec![] },
            ))
            .unwrap();

        let cfg = builder.build().unwrap();
        let result = cfg.validate_ssa(
            |param: &&'static str| vec![*param],
            instruction_ssa,
            terminator_ssa,
        );

        assert!(matches!(
            result,
            Err(SsaValidationError::UseNotDominated { value: "x", .. })
        ));
    }

    fn diamond_cfg() -> super::Cfg<TestInstruction, TestTerminator, u32, &'static str> {
        let mut builder = cfg_builder();
        builder
            .add_block(BasicBlock::new(
                0,
                TestTerminator::Branch {
                    then_target: 1,
                    else_target: 2,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::new(
                1,
                TestTerminator::Goto {
                    target: 3,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::new(
                2,
                TestTerminator::Goto {
                    target: 3,
                    uses: vec![],
                },
            ))
            .unwrap();
        builder
            .add_block(BasicBlock::new(3, TestTerminator::Return { uses: vec![] }))
            .unwrap();
        builder.build().unwrap()
    }
}
