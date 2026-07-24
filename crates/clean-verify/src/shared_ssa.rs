// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared SSA/CFG patterns for cross-project IR adapters.

use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SsaVariable {
    pub local: String,
    pub version: u32,
}

impl SsaVariable {
    #[must_use]
    pub fn new(local: impl Into<String>, version: u32) -> Self {
        Self {
            local: local.into(),
            version,
        }
    }

    #[must_use]
    pub fn name(&self) -> String {
        format!("_{}_{}", self.local, self.version)
    }
}

impl std::fmt::Display for SsaVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    Int(i64),
    Bool(bool),
    Text(String),
    Symbol(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Variable(SsaVariable),
    Constant(Constant),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    AndType,
    Or,
    Xor,
    Shl,
    Shr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOperator {
    Neg,
    Not,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PhiInput {
    pub label: String,
    pub value: Operand,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Instruction {
    Assign(SsaVariable, Operand),
    Call(Option<SsaVariable>, String, Vec<Operand>),
    Load(SsaVariable, Operand),
    Store(Operand, Operand),
    BinOp(SsaVariable, BinaryOperator, Operand, Operand),
    UnaryOp(SsaVariable, UnaryOperator, Operand),
    Cast(SsaVariable, Operand, String),
    Phi(SsaVariable, Vec<PhiInput>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BranchTarget {
    pub label: String,
    pub args: Vec<Operand>,
}

impl BranchTarget {
    #[must_use]
    pub fn new(label: impl Into<String>) -> Self {
        Self {
            label: label.into(),
            args: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SwitchCase {
    pub value: Constant,
    pub target: BranchTarget,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminator {
    Return(Option<Operand>),
    Branch(BranchTarget),
    ConditionalBranch(Operand, BranchTarget, BranchTarget),
    Switch(Operand, Vec<SwitchCase>, BranchTarget),
    Unreachable,
}

impl Terminator {
    fn successor_labels(&self) -> Vec<String> {
        match self {
            Self::Return(_) | Self::Unreachable => Vec::new(),
            Self::Branch(target) => vec![target.label.clone()],
            Self::ConditionalBranch(_, then_target, else_target) => {
                vec![then_target.label.clone(), else_target.label.clone()]
            }
            Self::Switch(_, cases, default) => cases
                .iter()
                .map(|case| case.target.label.clone())
                .chain(std::iter::once(default.label.clone()))
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    pub label: String,
    pub params: Vec<SsaVariable>,
    pub body: Vec<Instruction>,
    pub terminator: Terminator,
}

impl BasicBlock {
    #[must_use]
    pub fn new(label: impl Into<String>, terminator: Terminator) -> Self {
        Self {
            label: label.into(),
            params: Vec::new(),
            body: Vec::new(),
            terminator,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlFlowGraph {
    pub blocks: Vec<BasicBlock>,
    pub entry: String,
}

impl ControlFlowGraph {
    #[must_use]
    pub fn new(entry: impl Into<String>, blocks: Vec<BasicBlock>) -> Self {
        Self {
            blocks,
            entry: entry.into(),
        }
    }

    pub fn dominators(&self) -> Result<HashMap<String, HashSet<String>>, CfgValidationError> {
        let successors = self.successor_map()?;
        let predecessors = self.predecessor_map(&successors);
        let reachable = self.reachable_labels(&successors)?;
        let mut dominators = HashMap::with_capacity(reachable.len());

        for label in &reachable {
            let initial = if label == &self.entry {
                HashSet::from([label.clone()])
            } else {
                reachable.clone()
            };
            dominators.insert(label.clone(), initial);
        }

        let mut changed = true;
        while changed {
            changed = false;

            for label in reachable.iter().filter(|label| *label != &self.entry) {
                let pred_set = predecessors.get(label).cloned().unwrap_or_default();
                let reachable_preds = pred_set
                    .into_iter()
                    .filter(|pred| reachable.contains(pred))
                    .collect::<Vec<_>>();

                let mut updated = if reachable_preds.is_empty() {
                    HashSet::new()
                } else {
                    let mut pred_iter = reachable_preds.into_iter();
                    let first = dominators
                        .get(&pred_iter.next().expect("reachable predecessor exists"))
                        .cloned()
                        .unwrap_or_default();
                    pred_iter.fold(first, |acc, pred| {
                        let other = dominators.get(&pred).cloned().unwrap_or_default();
                        acc.intersection(&other).cloned().collect()
                    })
                };
                updated.insert(label.clone());

                if dominators.get(label) != Some(&updated) {
                    dominators.insert(label.clone(), updated);
                    changed = true;
                }
            }
        }

        Ok(dominators)
    }

    fn label_index(&self) -> Result<HashMap<&str, usize>, CfgValidationError> {
        let mut labels = HashMap::with_capacity(self.blocks.len());
        for (index, block) in self.blocks.iter().enumerate() {
            if labels.insert(block.label.as_str(), index).is_some() {
                return Err(CfgValidationError::DuplicateLabel {
                    label: block.label.clone(),
                });
            }
        }
        Ok(labels)
    }

    fn successor_map(&self) -> Result<HashMap<String, Vec<String>>, CfgValidationError> {
        let labels = self.label_index()?;
        let mut successors = HashMap::with_capacity(self.blocks.len());

        for block in &self.blocks {
            let targets = block.terminator.successor_labels();
            for target in &targets {
                if !labels.contains_key(target.as_str()) {
                    return Err(CfgValidationError::InvalidBranchTarget {
                        from: block.label.clone(),
                        target: target.clone(),
                    });
                }
            }
            successors.insert(block.label.clone(), targets);
        }

        Ok(successors)
    }

    fn predecessor_map(
        &self,
        successors: &HashMap<String, Vec<String>>,
    ) -> HashMap<String, HashSet<String>> {
        let mut predecessors = self
            .blocks
            .iter()
            .map(|block| (block.label.clone(), HashSet::new()))
            .collect::<HashMap<_, _>>();

        for (source, targets) in successors {
            for target in targets {
                predecessors
                    .entry(target.clone())
                    .or_default()
                    .insert(source.clone());
            }
        }

        predecessors
    }

    fn reachable_labels(
        &self,
        successors: &HashMap<String, Vec<String>>,
    ) -> Result<HashSet<String>, CfgValidationError> {
        if !successors.contains_key(&self.entry) {
            return Err(CfgValidationError::MissingEntry {
                entry: self.entry.clone(),
            });
        }

        let mut reachable = HashSet::new();
        let mut worklist = vec![self.entry.clone()];

        while let Some(label) = worklist.pop() {
            if !reachable.insert(label.clone()) {
                continue;
            }

            if let Some(targets) = successors.get(&label) {
                for target in targets {
                    if !reachable.contains(target) {
                        worklist.push(target.clone());
                    }
                }
            }
        }

        Ok(reachable)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CfgValidationError {
    #[error("duplicate basic block label `{label}`")]
    DuplicateLabel { label: String },
    #[error("missing entry block `{entry}`")]
    MissingEntry { entry: String },
    #[error("invalid branch target `{target}` from block `{from}`")]
    InvalidBranchTarget { from: String, target: String },
    #[error("block `{label}` is unreachable from entry `{entry}`")]
    UnreachableBlock { entry: String, label: String },
}

pub struct CfgValidator;

impl CfgValidator {
    pub fn validate(cfg: &ControlFlowGraph) -> Result<(), CfgValidationError> {
        let successors = cfg.successor_map()?;
        let reachable = cfg.reachable_labels(&successors)?;

        for block in &cfg.blocks {
            if !reachable.contains(&block.label) {
                return Err(CfgValidationError::UnreachableBlock {
                    entry: cfg.entry.clone(),
                    label: block.label.clone(),
                });
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        BasicBlock, BranchTarget, CfgValidationError, CfgValidator, Constant, ControlFlowGraph,
        Operand, SsaVariable, Terminator,
    };
    use std::collections::HashSet;

    fn var(local: &str, version: u32) -> SsaVariable {
        SsaVariable::new(local, version)
    }

    fn diamond_cfg() -> ControlFlowGraph {
        let cond = Operand::Variable(var("cond", 0));
        ControlFlowGraph::new(
            "entry",
            vec![
                BasicBlock::new(
                    "entry",
                    Terminator::ConditionalBranch(
                        cond,
                        BranchTarget::new("left"),
                        BranchTarget::new("right"),
                    ),
                ),
                BasicBlock::new("left", Terminator::Branch(BranchTarget::new("exit"))),
                BasicBlock::new("right", Terminator::Branch(BranchTarget::new("exit"))),
                BasicBlock::new("exit", Terminator::Return(None)),
            ],
        )
    }

    #[test]
    fn ssa_variable_uses_shared_name_convention() {
        assert_eq!(var("tmp", 7).to_string(), "_tmp_7");
    }

    #[test]
    fn graph_construction_computes_dominators() {
        let cfg = diamond_cfg();
        let dominators = cfg.dominators().unwrap();

        assert_eq!(cfg.blocks.last().unwrap().label, "exit");
        assert_eq!(
            dominators.get("entry").unwrap(),
            &HashSet::from(["entry".into()])
        );
        assert_eq!(
            dominators.get("left").unwrap(),
            &HashSet::from(["entry".into(), "left".into()])
        );
        assert_eq!(
            dominators.get("right").unwrap(),
            &HashSet::from(["entry".into(), "right".into()])
        );
        assert_eq!(
            dominators.get("exit").unwrap(),
            &HashSet::from(["entry".into(), "exit".into()])
        );
    }

    #[test]
    fn validator_rejects_duplicate_labels() {
        let cfg = ControlFlowGraph::new(
            "entry",
            vec![
                BasicBlock::new("entry", Terminator::Branch(BranchTarget::new("dup"))),
                BasicBlock::new("dup", Terminator::Return(None)),
                BasicBlock::new("dup", Terminator::Return(None)),
            ],
        );

        assert_eq!(
            CfgValidator::validate(&cfg),
            Err(CfgValidationError::DuplicateLabel {
                label: "dup".into()
            })
        );
    }

    #[test]
    fn validator_rejects_invalid_branch_target() {
        let cfg = ControlFlowGraph::new(
            "entry",
            vec![BasicBlock::new(
                "entry",
                Terminator::Branch(BranchTarget::new("missing")),
            )],
        );

        assert_eq!(
            CfgValidator::validate(&cfg),
            Err(CfgValidationError::InvalidBranchTarget {
                from: "entry".into(),
                target: "missing".into(),
            })
        );
    }

    #[test]
    fn validator_rejects_unreachable_blocks() {
        let cfg = ControlFlowGraph::new(
            "entry",
            vec![
                BasicBlock::new(
                    "entry",
                    Terminator::Return(Some(Operand::Constant(Constant::Bool(true)))),
                ),
                BasicBlock::new("dead", Terminator::Unreachable),
            ],
        );

        assert_eq!(
            CfgValidator::validate(&cfg),
            Err(CfgValidationError::UnreachableBlock {
                entry: "entry".into(),
                label: "dead".into(),
            })
        );
    }
}
