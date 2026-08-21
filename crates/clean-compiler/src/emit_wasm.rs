// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WebAssembly emitter for the straight-line first-order L5IR fragment.
//!
//! Lowers the same IR the C backend consumes ([`crate::emit_c`]) to a
//! self-contained Wasm module — as text (`.wat`) via [`emit_wat`] and as the
//! binary encoding via [`emit_wasm_binary`]. Both renderings are produced from
//! ONE lowering ([`lower_module`]), so the text an author inspects and the
//! bytes a host executes are the same program by construction.
//!
//! # The accepted fragment, and why it is exactly this
//!
//! Accepted decls are straight-line, call-free, first-order and fixed-width:
//!
//! * types — `UInt8`, `UInt16`, `UInt32`, `UInt64`, and nothing else;
//! * bodies — a chain of `VDecl` bindings ending in `Ret(Var)`;
//! * expressions — width-matched integer literals, and saturated
//!   `UInt{8,16,32,64}.{add,sub,mul}` applications, which are lowered to
//!   NATIVE Wasm instructions rather than calls.
//!
//! The accepted TYPE set is exactly the set of widths the accepted OPERATION
//! set covers ([`wasm_arith`], the same table as
//! `emit_trust_ir::uint_arith_binop`). That is the whole design rule: this
//! backend admits a type only when it can also compute with it, so no value
//! can enter a module that the module has no faithful way to manipulate.
//!
//! Everything else is refused LOUDLY, with the refusal naming the form:
//!
//! * `Nat` — arbitrary precision. It lowers to `IRType::Object`, a heap cell;
//!   there is no `i32`/`i64` that represents it, and a silent truncation to a
//!   machine word is exactly the class of bug this refusal exists to prevent.
//! * `USize` — host-pointer-width, so a module emitted for it would not be
//!   target-stable (the same reason `uint_arith_binop` excludes it).
//! * `Bool` — no operation in the fragment produces or consumes one, so
//!   admitting it would mean committing to a normalization convention (`0`/`1`
//!   versus "nonzero is true") that nothing here could exercise or test.
//! * floats, objects, structs, unions, erased values, `Void`; `Case`, join
//!   points, `Jmp`, RC ops, field mutation, `Unreachable`; constructors,
//!   projections, boxing, closures, strings, reuse; and every call to a
//!   non-arithmetic callee — recursion included.
//!
//! # Narrow widths wrap where Lean says they wrap
//!
//! Wasm has no `i8`/`i16`: `UInt8` and `UInt16` are carried in an `i32`, whose
//! arithmetic wraps at 32 bits, not at 8 or 16. So every narrow-width result
//! is masked (`i32.and` with `0xff`/`0xffff`) and every narrow-width parameter
//! is masked once on entry. The entry mask is what makes the carrier invariant
//! — "an `i32` holding a `UInt8` is in `[0, 256)`" — hold for values that
//! arrive from outside the module, where nothing else enforces it. `UInt32`
//! and `UInt64` need no mask: `i32`/`i64` wrap at exactly their width, which
//! is Lean's `UInt32`/`UInt64` semantics.
//!
//! # What this does NOT establish
//!
//! Nothing here is proved. The emitted module is checked by structural
//! assertion and by EXECUTION against a battery (see the tests); that is a
//! differential over the inputs actually run, not a semantics-preservation
//! certificate. The certificate lane is `emit_trust_ir_tv`, and it does not
//! cover this backend.

use std::collections::{HashMap, HashSet};

use thiserror::Error;

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::ir_checker::{check_decls, IRError};
use crate::mangle::mangle_name;

/// Why a declaration is not in the Wasm fragment.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum WasmEmitError {
    #[error("L5IR validation failed: {0}")]
    Ir(#[from] IRError),

    #[error(
        "type {ty:?} is outside the Wasm fragment ({context}): only UInt8/UInt16/UInt32/UInt64 \
         are supported — heap types (Nat, String, constructors) have no machine-word \
         representation, USize is host-pointer-width, and Bool/floats have no operation here"
    )]
    UnsupportedType { ty: IRType, context: &'static str },

    #[error(
        "body form `{form}` is outside the Wasm fragment: straight-line `let`* + `return` only"
    )]
    UnsupportedBody { form: &'static str },

    #[error("expression form `{form}` is outside the Wasm fragment: literals and saturated fixed-width UInt add/sub/mul only")]
    UnsupportedExpr { form: &'static str },

    #[error("literal form `{form}` is outside the Wasm fragment")]
    UnsupportedLiteral { form: &'static str },

    #[error("call to `{callee}` is outside the Wasm fragment: it is call-free, and only UInt{{8,16,32,64}}.{{add,sub,mul}} lower to native instructions")]
    UnsupportedCall { callee: String },

    #[error("`{callee}` expects {expected} operands, got {actual}")]
    ArityMismatch {
        callee: String,
        expected: usize,
        actual: usize,
    },

    #[error("operand of `{callee}` has type {actual:?}, expected {expected:?}")]
    OperandTypeMismatch {
        callee: String,
        expected: IRType,
        actual: IRType,
    },

    #[error("{context}: expected type {expected:?}, got {actual:?}")]
    ResultTypeMismatch {
        context: &'static str,
        expected: IRType,
        actual: IRType,
    },

    #[error("erased operand has no Wasm representation")]
    ErasedOperand,

    #[error("unbound variable x{}", _0.0)]
    UnboundVar(VarId),

    #[error("variable x{} is bound twice", _0.0)]
    DuplicateVar(VarId),

    #[error("duplicate export name `{name}`")]
    DuplicateExport { name: String },
}

/// A Wasm numeric type. The fragment uses no reference or vector types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValType {
    I32,
    I64,
}

impl ValType {
    const fn wat(self) -> &'static str {
        match self {
            Self::I32 => "i32",
            Self::I64 => "i64",
        }
    }

    const fn byte(self) -> u8 {
        match self {
            Self::I32 => 0x7f,
            Self::I64 => 0x7e,
        }
    }
}

/// A native Wasm binary operator used by this fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    /// Only ever emitted for the narrow-width carrier mask.
    And,
}

/// One Wasm instruction. Deliberately 1:1 with both a `.wat` line and a
/// binary opcode, so the two renderings cannot drift in instruction count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Instr {
    LocalGet(u32),
    LocalSet(u32),
    /// A constant; `u64` carries the raw bits, read at the given width.
    Const(ValType, u64),
    Bin(ValType, ArithOp),
}

impl Instr {
    fn opcode(self) -> u8 {
        match self {
            Self::LocalGet(_) => 0x20,
            Self::LocalSet(_) => 0x21,
            Self::Const(ValType::I32, _) => 0x41,
            Self::Const(ValType::I64, _) => 0x42,
            Self::Bin(ValType::I32, op) => match op {
                ArithOp::Add => 0x6a,
                ArithOp::Sub => 0x6b,
                ArithOp::Mul => 0x6c,
                ArithOp::And => 0x71,
            },
            Self::Bin(ValType::I64, op) => match op {
                ArithOp::Add => 0x7c,
                ArithOp::Sub => 0x7d,
                ArithOp::Mul => 0x7e,
                ArithOp::And => 0x83,
            },
        }
    }
}

/// A lowered function: the single source both renderings are derived from.
struct WasmFunc {
    /// Wat identifier (no leading `$`), from the shared name mangler.
    ident: String,
    /// Export name — the Lean name verbatim.
    export: String,
    params: Vec<ValType>,
    result: ValType,
    locals: Vec<ValType>,
    /// Wat names for every slot, params first then locals (index-aligned).
    slot_names: Vec<String>,
    instrs: Vec<Instr>,
}

/// Where a bound variable lives, and at what IR type.
struct Slot {
    index: u32,
    ty: IRType,
}

/// The Wasm type carrying `ty`, or a refusal.
fn val_type(ty: &IRType, context: &'static str) -> Result<ValType, WasmEmitError> {
    match ty {
        IRType::UInt8 | IRType::UInt16 | IRType::UInt32 => Ok(ValType::I32),
        IRType::UInt64 => Ok(ValType::I64),
        _ => Err(WasmEmitError::UnsupportedType {
            ty: ty.clone(),
            context,
        }),
    }
}

/// The mask restoring `ty`'s width after an `i32` operation, if `ty` is
/// narrower than its carrier.
const fn narrow_mask(ty: &IRType) -> Option<u32> {
    match ty {
        IRType::UInt8 => Some(0xff),
        IRType::UInt16 => Some(0xffff),
        _ => None,
    }
}

/// The fixed-width UInt primitives that lower to NATIVE Wasm instructions.
///
/// The same table as `emit_trust_ir::uint_arith_binop`, and excluded for the
/// same reasons: `Nat.*` is arbitrary-precision, `USize.*` is host-width, and
/// `.div`/`.mod` carry division-by-zero semantics a plain `i32.div_u` does not
/// model.
fn wasm_arith(name: &str) -> Option<(ArithOp, IRType)> {
    let (prefix, suffix) = name.rsplit_once('.')?;
    let ty = match prefix {
        "UInt8" => IRType::UInt8,
        "UInt16" => IRType::UInt16,
        "UInt32" => IRType::UInt32,
        "UInt64" => IRType::UInt64,
        _ => return None,
    };
    let op = match suffix {
        "add" => ArithOp::Add,
        "sub" => ArithOp::Sub,
        "mul" => ArithOp::Mul,
        _ => return None,
    };
    Some((op, ty))
}

/// Name of a body form, for refusal messages.
const fn body_form(body: &IRBody) -> &'static str {
    match body {
        IRBody::VDecl { .. } => "let",
        IRBody::JDecl { .. } => "join point",
        IRBody::Inc { .. } => "inc",
        IRBody::Dec { .. } => "dec",
        IRBody::Set { .. } => "set",
        IRBody::SetTag { .. } => "setTag",
        IRBody::USet { .. } => "uset",
        IRBody::SSet { .. } => "sset",
        IRBody::Case { .. } => "case",
        IRBody::Jmp { .. } => "jmp",
        IRBody::Ret(_) => "return",
        IRBody::Unreachable => "unreachable",
    }
}

/// Name of an expression form, for refusal messages.
const fn expr_form(expr: &IRExpr) -> &'static str {
    match expr {
        IRExpr::Ctor { .. } => "ctor",
        IRExpr::Proj { .. } => "proj",
        IRExpr::Tag(_) => "tag",
        IRExpr::Box { .. } => "box",
        IRExpr::Unbox { .. } => "unbox",
        IRExpr::Lit(_) => "literal",
        IRExpr::Apply { .. } => "apply",
        IRExpr::PartialApply { .. } => "partial apply",
        IRExpr::ClosureApply { .. } => "closure apply",
        IRExpr::UProj { .. } => "uproj",
        IRExpr::SProj { .. } => "sproj",
        IRExpr::IsShared(_) => "isShared",
        IRExpr::String(_) => "string",
        IRExpr::Reset(_) => "reset",
        IRExpr::Reuse { .. } => "reuse",
    }
}

/// Name of a literal form, for refusal messages.
const fn literal_form(lit: &IRLiteral) -> &'static str {
    match lit {
        IRLiteral::Bool(_) => "Bool",
        IRLiteral::UInt8(_) => "UInt8",
        IRLiteral::UInt16(_) => "UInt16",
        IRLiteral::UInt32(_) => "UInt32",
        IRLiteral::UInt64(_) => "UInt64",
        IRLiteral::USize(_) => "USize",
        IRLiteral::NatBig(_) => "Nat (>= 2^64)",
        IRLiteral::Float32(_) => "Float32",
        IRLiteral::Float64(_) => "Float64",
    }
}

/// The constant instruction for `lit`, checked against the binding's declared
/// type. A width-mismatched literal is refused rather than coerced.
fn lower_literal(lit: &IRLiteral, declared: &IRType) -> Result<Instr, WasmEmitError> {
    let (ty, bits) = match lit {
        IRLiteral::UInt8(n) => (IRType::UInt8, u64::from(*n)),
        IRLiteral::UInt16(n) => (IRType::UInt16, u64::from(*n)),
        IRLiteral::UInt32(n) => (IRType::UInt32, u64::from(*n)),
        IRLiteral::UInt64(n) => (IRType::UInt64, *n),
        other => {
            return Err(WasmEmitError::UnsupportedLiteral {
                form: literal_form(other),
            })
        }
    };
    if ty != *declared {
        return Err(WasmEmitError::ResultTypeMismatch {
            context: "literal binding",
            expected: declared.clone(),
            actual: ty,
        });
    }
    Ok(Instr::Const(val_type(&ty, "literal")?, bits))
}

/// Push the instructions computing `expr`, leaving exactly one value of the
/// binding's declared type on the stack.
fn lower_expr(
    expr: &IRExpr,
    declared: &IRType,
    slots: &HashMap<VarId, Slot>,
    instrs: &mut Vec<Instr>,
) -> Result<(), WasmEmitError> {
    match expr {
        IRExpr::Lit(lit) => {
            instrs.push(lower_literal(lit, declared)?);
            Ok(())
        }
        IRExpr::Apply { fn_id, args } => {
            let callee = fn_id.0.to_string();
            let Some((op, prim)) = wasm_arith(&callee) else {
                return Err(WasmEmitError::UnsupportedCall { callee });
            };
            if args.len() != 2 {
                return Err(WasmEmitError::ArityMismatch {
                    callee,
                    expected: 2,
                    actual: args.len(),
                });
            }
            if prim != *declared {
                return Err(WasmEmitError::ResultTypeMismatch {
                    context: "arithmetic binding",
                    expected: declared.clone(),
                    actual: prim,
                });
            }
            for arg in args {
                let IRArg::Var(var) = arg else {
                    return Err(WasmEmitError::ErasedOperand);
                };
                let slot = slots.get(var).ok_or(WasmEmitError::UnboundVar(*var))?;
                if slot.ty != prim {
                    return Err(WasmEmitError::OperandTypeMismatch {
                        callee,
                        expected: prim,
                        actual: slot.ty.clone(),
                    });
                }
                instrs.push(Instr::LocalGet(slot.index));
            }
            instrs.push(Instr::Bin(val_type(&prim, "arithmetic")?, op));
            Ok(())
        }
        other => Err(WasmEmitError::UnsupportedExpr {
            form: expr_form(other),
        }),
    }
}

/// Append the two-instruction narrow-width mask for `ty`, if it needs one.
fn push_narrow_mask(ty: &IRType, instrs: &mut Vec<Instr>) {
    if let Some(mask) = narrow_mask(ty) {
        instrs.push(Instr::Const(ValType::I32, u64::from(mask)));
        instrs.push(Instr::Bin(ValType::I32, ArithOp::And));
    }
}

/// Lower one declaration, or refuse it.
fn lower_decl(decl: &IRDecl) -> Result<WasmFunc, WasmEmitError> {
    let mut slots: HashMap<VarId, Slot> = HashMap::new();
    let mut params = Vec::new();
    let mut locals = Vec::new();
    let mut slot_names = Vec::new();
    let mut instrs = Vec::new();

    for (var, ty) in &decl.params {
        let vt = val_type(ty, "parameter")?;
        let index = params.len() as u32;
        if slots
            .insert(
                *var,
                Slot {
                    index,
                    ty: ty.clone(),
                },
            )
            .is_some()
        {
            return Err(WasmEmitError::DuplicateVar(*var));
        }
        params.push(vt);
        slot_names.push(format!("v{}", var.0));
        // Normalize a narrow parameter ONCE on entry. Values arriving from
        // outside the module are not otherwise constrained to the carrier
        // invariant, and every later instruction assumes it.
        if narrow_mask(ty).is_some() {
            instrs.push(Instr::LocalGet(index));
            push_narrow_mask(ty, &mut instrs);
            instrs.push(Instr::LocalSet(index));
        }
    }

    let result = val_type(&decl.return_type, "return type")?;

    let mut body = &decl.body;
    loop {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                let vt = val_type(ty, "let binding")?;
                lower_expr(value, ty, &slots, &mut instrs)?;
                push_narrow_mask(ty, &mut instrs);
                let index = (params.len() + locals.len()) as u32;
                if slots
                    .insert(
                        *var,
                        Slot {
                            index,
                            ty: ty.clone(),
                        },
                    )
                    .is_some()
                {
                    return Err(WasmEmitError::DuplicateVar(*var));
                }
                locals.push(vt);
                slot_names.push(format!("v{}", var.0));
                instrs.push(Instr::LocalSet(index));
                body = rest;
            }
            IRBody::Ret(IRArg::Var(var)) => {
                let slot = slots.get(var).ok_or(WasmEmitError::UnboundVar(*var))?;
                if slot.ty != decl.return_type {
                    return Err(WasmEmitError::ResultTypeMismatch {
                        context: "return",
                        expected: decl.return_type.clone(),
                        actual: slot.ty.clone(),
                    });
                }
                instrs.push(Instr::LocalGet(slot.index));
                break;
            }
            IRBody::Ret(IRArg::Erased) => return Err(WasmEmitError::ErasedOperand),
            other => {
                return Err(WasmEmitError::UnsupportedBody {
                    form: body_form(other),
                })
            }
        }
    }

    Ok(WasmFunc {
        ident: mangle_name(&decl.name),
        export: decl.name.to_string(),
        params,
        result,
        locals,
        slot_names,
        instrs,
    })
}

/// Lower a whole slice, refusing duplicate export names (which would make the
/// module invalid rather than merely wrong).
fn lower_module(decls: &[IRDecl]) -> Result<Vec<WasmFunc>, WasmEmitError> {
    check_decls(decls)?;
    let mut seen: HashSet<String> = HashSet::new();
    let mut funcs = Vec::with_capacity(decls.len());
    for decl in decls {
        let func = lower_decl(decl)?;
        if !seen.insert(func.export.clone()) {
            return Err(WasmEmitError::DuplicateExport { name: func.export });
        }
        funcs.push(func);
    }
    Ok(funcs)
}

/// Escape a Wasm string literal: printable ASCII passes through, everything
/// else becomes a `\HH` byte escape.
fn escape_wat_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for byte in s.bytes() {
        match byte {
            b'"' | b'\\' => {
                out.push('\\');
                out.push(byte as char);
            }
            0x20..=0x7e => out.push(byte as char),
            other => out.push_str(&format!("\\{other:02x}")),
        }
    }
    out
}

/// Render one instruction as a `.wat` line.
fn instr_wat(instr: Instr, names: &[String]) -> String {
    let slot = |i: u32| -> String {
        names
            .get(i as usize)
            .map_or_else(|| i.to_string(), |n| format!("${n}"))
    };
    match instr {
        Instr::LocalGet(i) => format!("local.get {}", slot(i)),
        Instr::LocalSet(i) => format!("local.set {}", slot(i)),
        Instr::Const(ValType::I32, bits) => format!("i32.const {}", bits as u32),
        Instr::Const(ValType::I64, bits) => format!("i64.const {bits}"),
        Instr::Bin(vt, op) => {
            let op = match op {
                ArithOp::Add => "add",
                ArithOp::Sub => "sub",
                ArithOp::Mul => "mul",
                ArithOp::And => "and",
            };
            format!("{}.{op}", vt.wat())
        }
    }
}

/// Emit the WebAssembly TEXT format for `decls`.
///
/// # Errors
///
/// Returns [`WasmEmitError`] if any declaration is outside the fragment
/// documented on this module.
pub fn emit_wat(decls: &[IRDecl]) -> Result<String, WasmEmitError> {
    let funcs = lower_module(decls)?;
    let mut out = String::from("(module\n  ;; Generated by the Clean compiler (emit_wasm).\n");
    for func in &funcs {
        out.push_str(&format!(
            "  (func ${} (export \"{}\")",
            func.ident,
            escape_wat_string(&func.export)
        ));
        for (i, vt) in func.params.iter().enumerate() {
            out.push_str(&format!(" (param ${} {})", func.slot_names[i], vt.wat()));
        }
        out.push_str(&format!(" (result {})\n", func.result.wat()));
        for (i, vt) in func.locals.iter().enumerate() {
            let name = &func.slot_names[func.params.len() + i];
            out.push_str(&format!("    (local ${name} {})\n", vt.wat()));
        }
        for instr in &func.instrs {
            out.push_str(&format!("    {}\n", instr_wat(*instr, &func.slot_names)));
        }
        out.push_str("  )\n");
    }
    out.push_str(")\n");
    Ok(out)
}

/// Unsigned LEB128.
fn leb_u32(mut value: u32, out: &mut Vec<u8>) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

/// Signed LEB128, over the two's-complement reading of a machine word.
fn leb_i64(mut value: i64, out: &mut Vec<u8>) {
    loop {
        let byte = (value as u8) & 0x7f;
        value >>= 7;
        let sign_set = byte & 0x40 != 0;
        if (value == 0 && !sign_set) || (value == -1 && sign_set) {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

/// Append a section: id, byte length, contents.
fn push_section(id: u8, content: &[u8], out: &mut Vec<u8>) {
    if content.is_empty() {
        return;
    }
    out.push(id);
    leb_u32(content.len() as u32, out);
    out.extend_from_slice(content);
}

/// Encode one instruction (opcode plus immediate).
fn encode_instr(instr: Instr, out: &mut Vec<u8>) {
    out.push(instr.opcode());
    match instr {
        Instr::LocalGet(i) | Instr::LocalSet(i) => leb_u32(i, out),
        // Wasm constants are SIGNED LEB128 even when the value is read as
        // unsigned: `i32.const 4294967295` encodes as -1.
        Instr::Const(ValType::I32, bits) => leb_i64(i64::from(bits as u32 as i32), out),
        Instr::Const(ValType::I64, bits) => leb_i64(bits as i64, out),
        Instr::Bin(..) => {}
    }
}

/// Emit the WebAssembly BINARY encoding for `decls`.
///
/// Rendered from the same lowering as [`emit_wat`], so the bytes a host runs
/// and the text an author reads are the same program.
///
/// # Errors
///
/// Returns [`WasmEmitError`] if any declaration is outside the fragment
/// documented on this module.
pub fn emit_wasm_binary(decls: &[IRDecl]) -> Result<Vec<u8>, WasmEmitError> {
    let funcs = lower_module(decls)?;
    let mut out = vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];

    // Type section: one functype per function, index-aligned.
    let mut types = Vec::new();
    leb_u32(funcs.len() as u32, &mut types);
    for func in &funcs {
        types.push(0x60);
        leb_u32(func.params.len() as u32, &mut types);
        types.extend(func.params.iter().map(|vt| vt.byte()));
        leb_u32(1, &mut types);
        types.push(func.result.byte());
    }
    push_section(1, &types, &mut out);

    // Function section: function i uses type i.
    let mut fns = Vec::new();
    leb_u32(funcs.len() as u32, &mut fns);
    for i in 0..funcs.len() {
        leb_u32(i as u32, &mut fns);
    }
    push_section(3, &fns, &mut out);

    // Export section: every function is exported under its Lean name.
    let mut exports = Vec::new();
    leb_u32(funcs.len() as u32, &mut exports);
    for (i, func) in funcs.iter().enumerate() {
        let name = func.export.as_bytes();
        leb_u32(name.len() as u32, &mut exports);
        exports.extend_from_slice(name);
        exports.push(0x00); // export kind: func
        leb_u32(i as u32, &mut exports);
    }
    push_section(7, &exports, &mut out);

    // Code section.
    let mut code = Vec::new();
    leb_u32(funcs.len() as u32, &mut code);
    for func in &funcs {
        let mut body = Vec::new();
        leb_u32(func.locals.len() as u32, &mut body);
        for vt in &func.locals {
            leb_u32(1, &mut body);
            body.push(vt.byte());
        }
        for instr in &func.instrs {
            encode_instr(*instr, &mut body);
        }
        body.push(0x0b); // end
        leb_u32(body.len() as u32, &mut code);
        code.extend_from_slice(&body);
    }
    push_section(10, &code, &mut out);

    Ok(out)
}

#[cfg(test)]
#[path = "emit_wasm_tests.rs"]
mod tests;
