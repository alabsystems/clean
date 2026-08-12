// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::Interpreter;
use crate::expr::{AsmOperand as ExprAsmOperand, EvalResult, Expr, InlineAsm as ExprInlineAsm};
use crate::types::{IntType, UintType};
use crate::values::{eval_binop, BinOp, Value};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsmConstraint {
    Reg,
    RegByte,
    RegAbcd,
    Other(String),
}
impl AsmConstraint {
    fn parse(raw: &str) -> Self {
        match raw.trim() {
            "reg" => Self::Reg,
            "reg_byte" => Self::RegByte,
            "reg_abcd" => Self::RegAbcd,
            other => Self::Other(other.to_string()),
        }
    }

    fn validate(&self, value: &Value) -> Result<(), String> {
        let valid = match (self, value) {
            (Self::Reg, Value::Uint { .. } | Value::Int { .. } | Value::Bool(_)) => true,
            (
                Self::RegByte,
                Value::Uint {
                    ty: UintType::U8, ..
                },
            ) => true,
            (
                Self::RegByte,
                Value::Int {
                    ty: IntType::I8, ..
                }
                | Value::Bool(_),
            ) => true,
            (Self::RegAbcd, Value::Uint { .. } | Value::Int { .. } | Value::Bool(_)) => true,
            (Self::Other(_), _) => false,
            _ => false,
        };
        if valid {
            Ok(())
        } else {
            Err(format!(
                "inline asm register class `{}` does not support value `{:?}`",
                self.name(),
                value
            ))
        }
    }

    fn name(&self) -> &str {
        match self {
            Self::Reg => "reg",
            Self::RegByte => "reg_byte",
            Self::RegAbcd => "reg_abcd",
            Self::Other(raw) => raw,
        }
    }
}
#[derive(Debug, Clone)]
pub(crate) enum AsmOperand {
    In {
        constraint: AsmConstraint,
        expr: Expr,
    },
    Out {
        constraint: AsmConstraint,
        expr: Option<Expr>,
    },
    InOut {
        constraint: AsmConstraint,
        in_expr: Expr,
        out_expr: Option<Expr>,
    },
    Const(Expr),
    Sym,
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum OperandRef {
    Index(usize),
    Name(String),
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum TemplateOperand {
    Placeholder {
        reference: OperandRef,
        modifier: Option<String>,
    },
    Literal(String),
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct TemplateInstruction {
    opcode: String,
    operands: Vec<TemplateOperand>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsmTemplate {
    instructions: Vec<TemplateInstruction>,
}
impl AsmTemplate {
    pub fn parse(raw: &str) -> Result<Self, String> {
        let mut instructions = Vec::new();
        for line in raw
            .split(['\n', ';'])
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            let mut parts = line.split_whitespace();
            let Some(opcode) = parts.next() else {
                continue;
            };
            let remainder = line[opcode.len()..].trim();
            let operands = if remainder.is_empty() {
                Vec::new()
            } else {
                remainder
                    .split(',')
                    .map(Self::parse_operand)
                    .collect::<Result<Vec<_>, _>>()?
            };
            instructions.push(TemplateInstruction {
                opcode: opcode.to_ascii_lowercase(),
                operands,
            });
        }
        if instructions.is_empty() {
            return Err("inline asm requires at least one instruction".to_string());
        }
        Ok(Self { instructions })
    }
    fn parse_operand(token: &str) -> Result<TemplateOperand, String> {
        let token = token.trim();
        let Some(inner) = token
            .strip_prefix('{')
            .and_then(|token| token.strip_suffix('}'))
        else {
            return Ok(TemplateOperand::Literal(token.to_string()));
        };
        let (slot, modifier) = inner
            .split_once(':')
            .map_or((inner.trim(), None), |(slot, modifier)| {
                (slot.trim(), Some(modifier.trim().to_string()))
            });
        let reference = slot
            .parse::<usize>()
            .map(OperandRef::Index)
            .unwrap_or_else(|_| OperandRef::Name(slot.to_string()));
        Ok(TemplateOperand::Placeholder {
            reference,
            modifier,
        })
    }
    fn placeholder_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for instruction in &self.instructions {
            for operand in &instruction.operands {
                if let TemplateOperand::Placeholder {
                    reference: OperandRef::Name(name),
                    ..
                } = operand
                {
                    if !names.iter().any(|seen| seen == name) {
                        names.push(name.clone());
                    }
                }
            }
        }
        names
    }
}
#[derive(Debug, Clone)]
pub struct InlineAsmBlock {
    pub template: AsmTemplate,
    pub operands: Vec<AsmOperand>,
    named_operands: HashMap<String, usize>,
}
impl InlineAsmBlock {
    fn new(template: AsmTemplate, operands: Vec<AsmOperand>) -> Self {
        let named_operands = template
            .placeholder_names()
            .into_iter()
            .enumerate()
            .map(|(index, name)| (name, index))
            .collect();
        Self {
            template,
            operands,
            named_operands,
        }
    }

    fn from_expr(asm: &ExprInlineAsm) -> Result<Self, String> {
        let template = AsmTemplate::parse(&asm.template)?;
        let operands = asm
            .operands
            .iter()
            .map(|operand| match operand {
                ExprAsmOperand::In { constraint, expr } => AsmOperand::In {
                    constraint: AsmConstraint::parse(constraint),
                    expr: expr.clone(),
                },
                ExprAsmOperand::Out { constraint, expr } => AsmOperand::Out {
                    constraint: AsmConstraint::parse(constraint),
                    expr: expr.clone(),
                },
                ExprAsmOperand::InOut {
                    constraint,
                    in_expr,
                    out_expr,
                } => AsmOperand::InOut {
                    constraint: AsmConstraint::parse(constraint),
                    in_expr: in_expr.clone(),
                    out_expr: out_expr.clone(),
                },
                ExprAsmOperand::Const(expr) => AsmOperand::Const(expr.clone()),
                ExprAsmOperand::Sym(_) => AsmOperand::Sym,
            })
            .collect();
        Ok(Self::new(template, operands))
    }

    fn resolve(&self, reference: &OperandRef) -> Option<usize> {
        let index = match reference {
            OperandRef::Index(index) => *index,
            OperandRef::Name(name) => *self.named_operands.get(name)?,
        };
        self.operands.get(index).map(|_| index)
    }
}
#[derive(Debug, Clone)]
enum RuntimeOperand {
    In {
        value: Value,
    },
    Out {
        constraint: AsmConstraint,
        expr: Option<Expr>,
        value: Value,
    },
    InOut {
        constraint: AsmConstraint,
        expr: Option<Expr>,
        value: Value,
    },
    Const,
    Sym,
}
impl RuntimeOperand {
    fn read(&self) -> Result<&Value, String> {
        match self {
            Self::In { value } | Self::InOut { value, .. } => Ok(value),
            Self::Out { .. } => Err("inline asm output operand cannot be read".to_string()),
            Self::Const | Self::Sym => {
                Err("inline asm instruction requires register operands".to_string())
            }
        }
    }

    fn write(&mut self, value: Value) -> Result<(), String> {
        match self {
            Self::Out {
                constraint,
                value: slot,
                ..
            }
            | Self::InOut {
                constraint,
                value: slot,
                ..
            } => {
                constraint.validate(&value)?;
                *slot = value;
                Ok(())
            }
            _ => Err("inline asm destination must be an output register".to_string()),
        }
    }

    fn output(&self) -> Option<(&Expr, Value)> {
        match self {
            Self::Out {
                expr: Some(expr),
                value,
                ..
            }
            | Self::InOut {
                expr: Some(expr),
                value,
                ..
            } => Some((expr, value.clone())),
            _ => None,
        }
    }
}
enum SimulationStatus {
    Executed,
    Fallback,
}
pub(super) fn eval_inline_asm(interpreter: &mut Interpreter, asm: &ExprInlineAsm) -> EvalResult {
    if let Err(err) = interpreter.ctx.require_unsafe("inline assembly") {
        return EvalResult::Error(err.to_string());
    }

    let block = match InlineAsmBlock::from_expr(asm) {
        Ok(block) => block,
        Err(err) => return EvalResult::Error(err),
    };
    let mut operands = match collect_operands(interpreter, &block.operands) {
        Ok(operands) => operands,
        Err(result) => return result,
    };

    let outputs = match execute_block(&block, &mut operands) {
        Ok(SimulationStatus::Executed) => apply_outputs(interpreter, operands.iter()),
        Ok(SimulationStatus::Fallback) => apply_fallback_outputs(interpreter, &block.operands),
        Err(err) => EvalResult::Error(err),
    };
    if !outputs.is_value() {
        return outputs;
    }

    if !asm.options.nomem {
        if let Err(err) = interpreter.havoc_modeled_memory() {
            return EvalResult::Error(format!("inline asm memory havoc failed: {err}"));
        }
    }

    EvalResult::Value(Value::Unit)
}
fn collect_operands(
    interpreter: &mut Interpreter,
    operands: &[AsmOperand],
) -> Result<Vec<RuntimeOperand>, EvalResult> {
    operands
        .iter()
        .map(|operand| match operand {
            AsmOperand::In { constraint, expr } => {
                let value = eval_value(interpreter, expr)?;
                constraint.validate(&value).map_err(EvalResult::Error)?;
                Ok(RuntimeOperand::In { value })
            }
            AsmOperand::Out { constraint, expr } => Ok(RuntimeOperand::Out {
                constraint: constraint.clone(),
                expr: expr.clone(),
                value: Value::Uninit,
            }),
            AsmOperand::InOut {
                constraint,
                in_expr,
                out_expr,
            } => {
                let value = eval_value(interpreter, in_expr)?;
                constraint.validate(&value).map_err(EvalResult::Error)?;
                Ok(RuntimeOperand::InOut {
                    constraint: constraint.clone(),
                    expr: out_expr.clone(),
                    value,
                })
            }
            AsmOperand::Const(expr) => {
                let _ = eval_value(interpreter, expr)?;
                Ok(RuntimeOperand::Const)
            }
            AsmOperand::Sym => Ok(RuntimeOperand::Sym),
        })
        .collect()
}
fn eval_value(interpreter: &mut Interpreter, expr: &Expr) -> Result<Value, EvalResult> {
    match interpreter.eval(expr) {
        EvalResult::Value(value) => Ok(value),
        other => Err(other),
    }
}
fn apply_outputs<'a>(
    interpreter: &mut Interpreter,
    operands: impl Iterator<Item = &'a RuntimeOperand>,
) -> EvalResult {
    for operand in operands {
        if let Some((expr, value)) = operand.output() {
            match interpreter.assign_place(expr, value) {
                EvalResult::Value(_) => {}
                other => return other,
            }
        }
    }
    EvalResult::Value(Value::Unit)
}
fn apply_fallback_outputs(interpreter: &mut Interpreter, operands: &[AsmOperand]) -> EvalResult {
    for operand in operands {
        let output_expr = match operand {
            AsmOperand::Out { expr, .. } => expr.as_ref(),
            AsmOperand::InOut { out_expr, .. } => out_expr.as_ref(),
            AsmOperand::In { .. } | AsmOperand::Const(_) | AsmOperand::Sym => None,
        };
        if let Some(expr) = output_expr {
            match interpreter.assign_place(expr, Value::Uninit) {
                EvalResult::Value(_) => {}
                other => return other,
            }
        }
    }
    EvalResult::Value(Value::Unit)
}
fn execute_block(
    block: &InlineAsmBlock,
    operands: &mut [RuntimeOperand],
) -> Result<SimulationStatus, String> {
    let mut next = operands.to_vec();
    for instruction in &block.template.instructions {
        let executed = match instruction.opcode.as_str() {
            "mov" => execute_mov(block, &mut next, instruction)?,
            "add" => execute_binop(block, &mut next, instruction, BinOp::Add)?,
            "sub" => execute_binop(block, &mut next, instruction, BinOp::Sub)?,
            "xor" => execute_binop(block, &mut next, instruction, BinOp::BitXor)?,
            _ => false,
        };
        if !executed {
            return Ok(SimulationStatus::Fallback);
        }
    }
    operands.clone_from_slice(&next);
    Ok(SimulationStatus::Executed)
}
fn execute_mov(
    block: &InlineAsmBlock,
    operands: &mut [RuntimeOperand],
    instruction: &TemplateInstruction,
) -> Result<bool, String> {
    let Some((dst, src)) = resolve_register_pair(block, instruction)? else {
        return Ok(false);
    };
    let value = operands[src].read()?.clone();
    operands[dst].write(value)?;
    Ok(true)
}
fn execute_binop(
    block: &InlineAsmBlock,
    operands: &mut [RuntimeOperand],
    instruction: &TemplateInstruction,
    op: BinOp,
) -> Result<bool, String> {
    let Some((dst, src)) = resolve_register_pair(block, instruction)? else {
        return Ok(false);
    };
    let left = operands[dst].read()?.clone();
    let right = operands[src].read()?.clone();
    let value = eval_binop(op, &left, &right).ok_or_else(|| {
        format!(
            "inline asm `{}` is unsupported for values `{:?}` and `{:?}`",
            instruction.opcode, left, right
        )
    })?;
    operands[dst].write(value)?;
    Ok(true)
}
fn resolve_register_pair(
    block: &InlineAsmBlock,
    instruction: &TemplateInstruction,
) -> Result<Option<(usize, usize)>, String> {
    let [dst, src] = instruction.operands.as_slice() else {
        return Ok(None);
    };
    let (
        TemplateOperand::Placeholder { reference: dst, .. },
        TemplateOperand::Placeholder { reference: src, .. },
    ) = (dst, src)
    else {
        return Ok(None);
    };
    let dst = block
        .resolve(dst)
        .ok_or_else(|| "inline asm template referenced a missing operand".to_string())?;
    let src = block
        .resolve(src)
        .ok_or_else(|| "inline asm template referenced a missing operand".to_string())?;
    Ok(Some((dst, src)))
}
