// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validate a selected first-order Nat IR call graph for native lowering.
//! Public roots come from the checked base signature and helpers retain
//! their original typed names. No constants are added to the kernel.

use std::collections::{HashMap, HashSet};

use clean_kernel::{BigNat, Name};

use super::decode::IrDecoder;
use super::exported_term_eval::{
    is_tagged_nat, Program, MAX_ARGUMENTS, MAX_CALL_DEPTH, MAX_EXECUTION_STEPS, MAX_NAT_LIMBS,
};
use super::module_ir::{PartEntries, BUILTIN_INIT_EXT, DECL_MAP_EXT, REGULAR_INIT_EXT};
use super::types::{Arg, Decl, Expr, Instr, IrType, LitVal, Terminal, VarId};
use crate::header::OleanHeader;
use crate::region::CompactedRegion;
use crate::{OleanError, OleanResult};

#[cfg(test)]
mod tests;

/// One selected function and the same-capture declarations reachable from it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedNatProgram {
    root: Name,
    functions: Vec<CapturedNatDefinition>,
}

impl CapturedNatProgram {
    /// The exact exported source name selected by the caller.
    #[must_use]
    pub fn root(&self) -> &Name {
        &self.root
    }

    /// The root and its helpers. Every same-capture call points to a
    /// definition earlier in this list.
    #[must_use]
    pub fn functions(&self) -> &[CapturedNatDefinition] {
        &self.functions
    }
}

/// One straight-line function of Nat arguments returning a Nat.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedNatDefinition {
    name: Name,
    arity: usize,
    operations: Vec<CapturedNatOperation>,
    result: CapturedNatSlot,
}

impl CapturedNatDefinition {
    /// The original IR declaration name, including private namespaces.
    #[must_use]
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// The number of arguments and the first operation's slot index.
    #[must_use]
    pub const fn arity(&self) -> usize {
        self.arity
    }

    /// Each operation defines a slot at its index plus the argument count.
    #[must_use]
    pub fn operations(&self) -> &[CapturedNatOperation] {
        &self.operations
    }

    /// The slot returned by the function.
    #[must_use]
    pub const fn result(&self) -> CapturedNatSlot {
        self.result
    }
}

/// One argument or prior operation result in the current declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CapturedNatSlot(usize);

impl CapturedNatSlot {
    /// Position in the argument and operation slots.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0
    }
}

/// A supported operation on arbitrary-precision natural numbers.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CapturedNatOperation {
    /// The exact natural number literal stored by Lean.
    Literal(BigNat),
    /// The measured pure `Nat.add` primitive.
    Add {
        /// Left operand.
        left: CapturedNatSlot,
        /// Right operand.
        right: CapturedNatSlot,
    },
    /// A fully applied call into this capture's declaration graph.
    Call {
        /// Its exact Lean declaration name.
        target: Name,
        /// The arguments in call order.
        arguments: Vec<CapturedNatSlot>,
    },
}

pub(super) fn reject_base_initializers(bytes: &[u8], function: &Name) -> OleanResult<()> {
    let header = OleanHeader::parse(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    let parts = region
        .ir_part_entries(region.root_ptr()?)
        .map_err(|error| refusal(function, error))?;
    reject_initializers(&region, &parts, function)
}

fn reject_initializers(
    region: &CompactedRegion<'_>,
    part: &PartEntries,
    function: &Name,
) -> OleanResult<()> {
    let decoder = IrDecoder::for_stable_execution(region);
    for extension in [REGULAR_INIT_EXT, BUILTIN_INIT_EXT] {
        if let Some(table) = part.get(extension) {
            let initializers = decoder
                .array(table, extension, MAX_EXECUTION_STEPS)
                .map_err(|error| refusal(function, error))?;
            if !initializers.is_empty() {
                return Err(refusal(
                    function,
                    format!("unsupported initialization in {extension}"),
                ));
            }
        }
    }
    Ok(())
}

pub(super) fn extract_nat_program(
    region: &CompactedRegion<'_>,
    root: u64,
    function: &Name,
    arity: usize,
) -> OleanResult<CapturedNatProgram> {
    let part = region
        .ir_part_entries(root)
        .map_err(|error| refusal(function, error))?;
    if !part.is_module {
        return Err(refusal(function, "captured .ir is not module data"));
    }
    reject_initializers(region, &part, function)?;
    let table = part
        .get(DECL_MAP_EXT)
        .ok_or_else(|| refusal(function, "missing captured Lean.IR.declMapExt"))?;
    let mut extractor = Extractor {
        program: Program::new(region, table, function)?,
        active: HashSet::new(),
        finished: HashMap::new(),
        functions: Vec::new(),
        work: MAX_EXECUTION_STEPS,
    };
    extractor.function(function, arity, 0)?;
    Ok(CapturedNatProgram {
        root: function.clone(),
        functions: extractor.functions,
    })
}

#[derive(Clone, Copy)]
struct Slot {
    index: CapturedNatSlot,
    tagged: bool,
}

#[derive(Clone, Copy)]
struct Signature {
    arity: usize,
    tagged_result: bool,
    call_depth: usize,
    inlined_work: usize,
}

struct Extractor<'r, 'bytes> {
    program: Program<'r, 'bytes>,
    active: HashSet<Name>,
    finished: HashMap<Name, Signature>,
    functions: Vec<CapturedNatDefinition>,
    work: usize,
}

impl Extractor<'_, '_> {
    fn function(&mut self, name: &Name, arity: usize, depth: usize) -> OleanResult<Signature> {
        if arity > MAX_ARGUMENTS || depth >= MAX_CALL_DEPTH {
            return Err(refusal(name, "call depth or arity limit"));
        }
        if let Some(&signature) = self.finished.get(name) {
            if signature.arity != arity {
                return Err(refusal(name, "inconsistent captured call arity"));
            }
            if depth + signature.call_depth > MAX_CALL_DEPTH {
                return Err(refusal(name, "call depth limit"));
            }
            return Ok(signature);
        }
        if !self.active.insert(name.clone()) {
            return Err(refusal(name, "recursive captured call"));
        }
        let declaration = self
            .program
            .declaration(name)?
            .ok_or_else(|| refusal(name, "missing body in the selected .ir capture"))?;
        let Decl::FDecl {
            params,
            ty,
            body,
            info,
            ..
        } = declaration.as_ref()
        else {
            return Err(refusal(name, "unsupported extern call"));
        };
        if *ty != IrType::TObject
            || params.len() != arity
            || !params.iter().all(|param| param.ty == IrType::TObject)
            || info.sorry_dep.is_some()
        {
            return Err(refusal(
                name,
                "expected a pure Nat call signature without a sorry dependency",
            ));
        }
        let bounds = info
            .index_bounds
            .as_ref()
            .ok_or_else(|| refusal(name, "missing stable local index bounds"))?;
        let work = body
            .instrs
            .len()
            .checked_add(1)
            .ok_or_else(|| refusal(name, "invalid instruction count"))?;
        self.work = self
            .work
            .checked_sub(work)
            .ok_or_else(|| refusal(name, "native IR extraction budget exhausted"))?;

        let mut slots = HashMap::new();
        for (index, param) in params.iter().enumerate() {
            bind(
                name,
                &mut slots,
                param.x,
                bounds.max_var,
                Slot {
                    index: CapturedNatSlot(index),
                    tagged: false,
                },
            )?;
        }
        let mut operations = Vec::new();
        let mut call_depth = 1;
        let mut inlined_work = work;
        for instr in &body.instrs {
            match instr {
                Instr::VDecl { x, ty, e } => {
                    let (operation, tagged, callee) = self.operation(name, e, &slots, depth)?;
                    if let Some(callee) = callee {
                        call_depth = call_depth.max(1 + callee.call_depth);
                        inlined_work += callee.inlined_work;
                        if inlined_work > MAX_EXECUTION_STEPS {
                            return Err(refusal(
                                name,
                                "inlined Nat call graph exceeds the size bound",
                            ));
                        }
                    }
                    if !(*ty == IrType::TObject || (*ty == IrType::Tagged && tagged)) {
                        return Err(refusal(
                            name,
                            format!("unsupported Nat representation for x_{}: {ty:?}", x.0),
                        ));
                    }
                    let index = CapturedNatSlot(arity + operations.len());
                    bind(name, &mut slots, *x, bounds.max_var, Slot { index, tagged })?;
                    operations.push(operation);
                }
                Instr::Inc { x, .. } | Instr::Dec { x, .. } | Instr::Del { x } => {
                    // Lowering uses immutable Nat values, with no observable
                    // reference count operation in this fragment.
                    lookup(name, &slots, Arg::Var(*x))?;
                }
                Instr::JDecl { .. } => return Err(refusal(name, "unsupported jdecl")),
                Instr::Set { .. } => return Err(refusal(name, "unsupported set")),
                Instr::SetTag { .. } => return Err(refusal(name, "unsupported setTag")),
                Instr::USet { .. } => return Err(refusal(name, "unsupported uset")),
                Instr::SSet { .. } => return Err(refusal(name, "unsupported sset")),
            }
        }
        let result = match &body.terminal {
            Terminal::Ret(arg) => lookup(name, &slots, *arg)?,
            Terminal::Case { .. } => return Err(refusal(name, "unsupported case")),
            Terminal::Jmp { .. } => return Err(refusal(name, "unsupported jmp")),
            Terminal::Unreachable => return Err(refusal(name, "unsupported unreachable")),
        };
        self.active.remove(name);
        let signature = Signature {
            arity,
            tagged_result: result.tagged,
            call_depth,
            inlined_work,
        };
        self.finished.insert(name.clone(), signature);
        self.functions.push(CapturedNatDefinition {
            name: name.clone(),
            arity,
            operations,
            result: result.index,
        });
        Ok(signature)
    }

    fn operation(
        &mut self,
        name: &Name,
        expr: &Expr,
        slots: &HashMap<VarId, Slot>,
        depth: usize,
    ) -> OleanResult<(CapturedNatOperation, bool, Option<Signature>)> {
        match expr {
            Expr::Lit(LitVal::Num(literal)) => {
                if literal.limbs().len() > MAX_NAT_LIMBS {
                    return Err(refusal(name, "Nat literal exceeds execution bound"));
                }
                let value = BigNat::from_limbs(literal.limbs().to_vec());
                let tagged = is_tagged_nat(&value);
                Ok((CapturedNatOperation::Literal(value), tagged, None))
            }
            Expr::Fap { f, args } => {
                if args.len() > MAX_ARGUMENTS {
                    return Err(refusal(f, "call arity limit"));
                }
                let arguments = args
                    .iter()
                    .map(|arg| lookup(name, slots, *arg).map(|slot| slot.index))
                    .collect::<OleanResult<Vec<_>>>()?;
                if self.program.declaration(f)?.is_some() {
                    let callee = self.function(f, args.len(), depth + 1)?;
                    return Ok((
                        CapturedNatOperation::Call {
                            target: f.clone(),
                            arguments,
                        },
                        callee.tagged_result,
                        Some(callee),
                    ));
                }
                if *f == Name::anon().str("Nat").str("add") {
                    let [left, right] = arguments.as_slice() else {
                        return Err(refusal(f, "Nat.add requires two arguments"));
                    };
                    return Ok((
                        CapturedNatOperation::Add {
                            left: *left,
                            right: *right,
                        },
                        false,
                        None,
                    ));
                }
                Err(refusal(name, format!("unsupported call {f}")))
            }
            Expr::Lit(LitVal::Str(_)) => Err(refusal(name, "unsupported String literal")),
            Expr::Ctor { info, .. } => Err(refusal(
                name,
                format!("unsupported constructor {}", info.name),
            )),
            Expr::Reset { .. } => Err(refusal(name, "unsupported reset")),
            Expr::Reuse { .. } => Err(refusal(name, "unsupported reuse")),
            Expr::Proj { .. } => Err(refusal(name, "unsupported proj")),
            Expr::UProj { .. } => Err(refusal(name, "unsupported uproj")),
            Expr::SProj { .. } => Err(refusal(name, "unsupported sproj")),
            Expr::Pap { .. } => Err(refusal(name, "unsupported pap")),
            Expr::Ap { .. } => Err(refusal(name, "unsupported ap")),
            Expr::Box { .. } => Err(refusal(name, "unsupported box")),
            Expr::Unbox { .. } => Err(refusal(name, "unsupported unbox")),
            Expr::IsShared { .. } => Err(refusal(name, "unsupported isShared")),
        }
    }
}

fn bind(
    name: &Name,
    slots: &mut HashMap<VarId, Slot>,
    id: VarId,
    maximum: u64,
    slot: Slot,
) -> OleanResult<()> {
    if id.0 > maximum {
        return Err(refusal(
            name,
            format!("x_{} exceeds persisted maxVar {maximum}", id.0),
        ));
    }
    if slots.insert(id, slot).is_some() {
        return Err(refusal(name, format!("duplicate variable x_{}", id.0)));
    }
    Ok(())
}

fn lookup(name: &Name, slots: &HashMap<VarId, Slot>, arg: Arg) -> OleanResult<Slot> {
    let Arg::Var(id) = arg else {
        return Err(refusal(name, "erased Nat operand"));
    };
    slots
        .get(&id)
        .copied()
        .ok_or_else(|| refusal(name, format!("unbound Nat slot x_{}", id.0)))
}

fn refusal(name: &Name, detail: impl std::fmt::Display) -> OleanError {
    OleanError::Region(format!("captured Nat program {name}: {detail}"))
}
