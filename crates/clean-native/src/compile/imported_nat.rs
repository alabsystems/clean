// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lower a checked capture's first-order Nat program to native LCNF.

use std::collections::HashMap;

use anyhow::{anyhow, ensure};
use clean_compiler::lcnf::{Arg, Code, Decl, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Literal, Name};
use clean_olean::{
    CapturedNatDefinition, CapturedNatOperation, CapturedNatProgram, CapturedNatSlot,
};

const MAX_INLINE_DEPTH: usize = 32;
const MAX_INLINE_STEPS: usize = 4096;

pub(super) struct LoweredImportedNat {
    pub(super) declaration: Decl,
    /// The native selector must audit the exact stable `Nat.add` shim edge.
    pub(super) uses_nat_add: bool,
}

/// Inline same-artifact private calls into the exported entry. The ordinary
/// LCNF pipeline owns Clean's reference counting and Nat representation.
pub(super) fn lower_imported_nat_program(
    program: &CapturedNatProgram,
) -> anyhow::Result<LoweredImportedNat> {
    let functions: HashMap<_, _> = program
        .functions()
        .iter()
        .map(|function| (function.name(), function))
        .collect();
    ensure!(
        functions.len() == program.functions().len(),
        "duplicate functions in captured Nat program"
    );
    let root = functions
        .get(program.root())
        .ok_or_else(|| anyhow!("captured Nat entry `{}` has no body", program.root()))?;
    let arity = u64::try_from(root.arity())?;
    let nat = Expr::const_str("Nat");
    let arguments: Vec<_> = (0..arity).map(FVarId::new).collect();
    let params = arguments
        .iter()
        .map(|argument| Param::new(*argument, Name::anon(), nat.clone()))
        .collect();
    let mut lowering = Lowering {
        functions,
        nat: nat.clone(),
        bindings: Vec::new(),
        next_fvar: arity,
        remaining_steps: MAX_INLINE_STEPS,
        uses_nat_add: false,
    };
    let result = lowering.inline(program.root(), &arguments, 0)?;
    let body = lowering
        .bindings
        .into_iter()
        .rev()
        .fold(Code::Return(result), |body, declaration| {
            Code::let_bind(declaration, body)
        });
    Ok(LoweredImportedNat {
        declaration: Decl::new(program.root().clone(), Vec::new(), nat, params, body, false),
        uses_nat_add: lowering.uses_nat_add,
    })
}

struct Lowering<'a> {
    functions: HashMap<&'a Name, &'a CapturedNatDefinition>,
    nat: Expr,
    bindings: Vec<LetDecl>,
    next_fvar: u64,
    remaining_steps: usize,
    uses_nat_add: bool,
}

impl Lowering<'_> {
    fn inline(
        &mut self,
        name: &Name,
        arguments: &[FVarId],
        depth: usize,
    ) -> anyhow::Result<FVarId> {
        self.step(name)?;
        ensure!(
            depth < MAX_INLINE_DEPTH,
            "captured Nat call depth exceeded at `{name}`"
        );
        let function = self
            .functions
            .get(name)
            .copied()
            .ok_or_else(|| anyhow!("captured Nat call `{name}` has no body in its artifact"))?;
        ensure!(
            function.arity() == arguments.len(),
            "captured Nat call `{name}` has the wrong arity"
        );
        let mut slots = arguments.to_vec();
        for operation in function.operations() {
            self.step(name)?;
            let result = match operation {
                CapturedNatOperation::Literal(value) => {
                    ensure!(
                        value.limbs().len() <= 2,
                        "captured Nat literal in `{name}` exceeds the native C carrier"
                    );
                    self.bind(LetValue::Lit(Literal::Nat(value.clone())))
                }
                CapturedNatOperation::Add { left, right } => {
                    self.uses_nat_add = true;
                    self.bind(LetValue::Const {
                        name: Name::anon().str("Nat").str("add"),
                        levels: Vec::new(),
                        args: vec![
                            Arg::FVar(slot(name, &slots, *left)?),
                            Arg::FVar(slot(name, &slots, *right)?),
                        ],
                    })
                }
                CapturedNatOperation::Call { target, arguments } => {
                    let args = arguments
                        .iter()
                        .map(|argument| slot(name, &slots, *argument))
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    self.inline(target, &args, depth + 1)?
                }
                _ => anyhow::bail!("unsupported captured Nat operation in `{name}`"),
            };
            slots.push(result);
        }
        slot(name, &slots, function.result())
    }

    fn step(&mut self, name: &Name) -> anyhow::Result<()> {
        self.remaining_steps = self
            .remaining_steps
            .checked_sub(1)
            .ok_or_else(|| anyhow!("captured Nat inlining budget exhausted at `{name}`"))?;
        Ok(())
    }

    fn bind(&mut self, value: LetValue) -> FVarId {
        let id = FVarId::new(self.next_fvar);
        self.next_fvar += 1;
        self.bindings
            .push(LetDecl::new(id, Name::anon(), self.nat.clone(), value));
        id
    }
}

fn slot(name: &Name, slots: &[FVarId], slot: CapturedNatSlot) -> anyhow::Result<FVarId> {
    slots
        .get(slot.index())
        .copied()
        .ok_or_else(|| anyhow!("invalid captured Nat slot {} in `{name}`", slot.index()))
}

#[cfg(test)]
mod tests;
