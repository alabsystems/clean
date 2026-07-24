// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C Operational Semantics Interpreter
//!
//! This module implements a big-step operational semantics interpreter
//! for C programs. It can be used to:
//!
//! 1. Execute C programs for testing
//! 2. Generate execution traces for verification
//! 3. Detect undefined behavior at runtime
//!
//! ## Execution Model
//!
//! The interpreter uses a big-step semantics:
//! - Expressions evaluate to values (or UB)
//! - Statements execute and modify state (or UB)
//! - Function calls use a call stack
//!
//! ## State
//!
//! The execution state consists of:
//! - Memory: heap and stack allocations
//! - Environment: variable name → location mapping
//! - Call stack: for function calls
//! - Control flow state: for break/continue/return

use crate::expr::{
    BinOp, BitFieldRef, CExpr, Designator, ExprResult, Ident, Initializer, SizeOfArg, UnaryOp,
};
use crate::memory::{BlockId, Memory, Pointer};
use crate::stmt::{CStmt, FuncDef, StorageClass, TranslationUnit, VarDecl};
use crate::types::{CType, IntKind, Signedness};
use crate::ub::{UBKind, UBResult};
use crate::values::{to_pointer_offset, CValue};
use clean_kernel::sem_memory_model::MemoryModel;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Maximum loop iterations (prevent infinite loops during interpretation)
const MAX_LOOP_ITERATIONS: usize = 100_000;

/// Compile-time diagnostic for a `_Static_assert` (C11 6.7.10).
///
/// A static assertion is a translation-time *constraint*: the controlling
/// constant expression must evaluate to a non-zero value, otherwise the
/// program is ill-formed. This error carries the failure reason; the
/// `AssertionFailed` variant carries the assertion's diagnostic message.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum StaticAssertError {
    /// The controlling expression evaluated to zero (assertion is false).
    #[error("static assertion failed: {message}")]
    AssertionFailed {
        /// The assertion's diagnostic message (or a default when omitted).
        message: String,
    },

    /// The controlling expression is not a (foldable) integer constant
    /// expression, so the assertion cannot be evaluated at compile time.
    #[error("static assertion expression is not a constant expression: {reason}")]
    NotConstant {
        /// Why the expression could not be folded to an integer constant.
        reason: String,
    },
}

/// Variable binding in the environment
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VarBinding {
    /// Pointer to the variable's storage
    pub ptr: Pointer,
    /// Type of the variable
    pub ty: CType,
    /// Is this a const variable?
    pub is_const: bool,
}

/// Local environment (variable scope)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LocalEnv {
    /// Variable bindings: name → binding
    vars: HashMap<Ident, VarBinding>,
}

impl LocalEnv {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }

    pub fn bind(&mut self, name: Ident, binding: VarBinding) {
        self.vars.insert(name, binding);
    }

    pub fn lookup(&self, name: &str) -> Option<&VarBinding> {
        self.vars.get(name)
    }
}

/// Control flow outcome from statement execution
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ControlFlow {
    /// Normal continuation
    Continue,
    /// Break from loop/switch
    Break,
    /// Continue to next iteration
    LoopContinue,
    /// Return from function
    Return(Option<CValue>),
    /// Goto a label
    Goto(Ident),
}

/// Call frame for function calls
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallFrame {
    /// Function name (for debugging)
    pub func_name: Ident,
    /// Return type
    pub return_type: CType,
    /// Local environment
    pub locals: LocalEnv,
    /// Return address (not used in interpreter, for debugging)
    pub call_depth: usize,
}

/// The execution state
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct State {
    /// Memory
    pub memory: Memory,
    /// Global environment
    pub globals: LocalEnv,
    /// Call stack
    pub call_stack: Vec<CallFrame>,
    /// Current local environment (top of stack)
    current_locals: LocalEnv,
    /// Function definitions
    pub functions: HashMap<Ident, FuncDef>,
    /// Memory blocks standing in for function addresses (for function
    /// pointers). Allocated lazily so that callers who insert directly into
    /// `functions` still get well-defined addresses. Maps name -> block and
    /// the reverse so an indirect call can recover the callee from a pointer.
    func_addresses: HashMap<Ident, BlockId>,
    addr_to_func: HashMap<BlockId, Ident>,
    /// String literals (allocated once, reused)
    string_literals: HashMap<String, Pointer>,
    /// Execution depth limit (for recursion)
    pub max_depth: usize,
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl State {
    /// Create a new empty state
    pub fn new() -> Self {
        Self {
            memory: Memory::new(),
            globals: LocalEnv::new(),
            call_stack: Vec::new(),
            current_locals: LocalEnv::new(),
            functions: HashMap::new(),
            func_addresses: HashMap::new(),
            addr_to_func: HashMap::new(),
            string_literals: HashMap::new(),
            max_depth: 1000,
        }
    }

    /// Initialize state from a translation unit
    pub fn from_translation_unit(tu: &TranslationUnit) -> UBResult<Self> {
        let mut state = Self::new();

        // First pass: register function definitions
        for decl in &tu.decls {
            if let crate::stmt::TopLevel::FuncDef(func) = decl {
                state.functions.insert(func.name.clone(), func.clone());
            }
        }

        // Second pass: allocate global variables
        for decl in &tu.decls {
            if let crate::stmt::TopLevel::VarDecl(var) = decl {
                state.alloc_global(var)?;
            }
        }

        Ok(state)
    }

    /// Allocate a global variable
    fn alloc_global(&mut self, decl: &VarDecl) -> UBResult<()> {
        let size = decl.ty.size();
        let align = decl.ty.align();
        let ptr = self.memory.alloc(size, align)?;

        // Initialize to zero by default
        let zero = CValue::zero(&decl.ty);
        self.store_value(ptr, &zero, &decl.ty)?;

        // Apply initializer if present
        if let Some(ref init) = decl.init {
            let val = self.eval_initializer(init, &decl.ty)?;
            self.store_value(ptr, &val, &decl.ty)?;
        }

        self.globals.bind(
            decl.name.clone(),
            VarBinding {
                ptr,
                ty: decl.ty.clone(),
                is_const: false,
            },
        );

        Ok(())
    }

    /// Lookup a variable (local then global)
    pub fn lookup_var(&self, name: &str) -> Option<&VarBinding> {
        // Try local first
        if let Some(binding) = self.current_locals.lookup(name) {
            return Some(binding);
        }
        // Then global
        self.globals.lookup(name)
    }

    /// Get (lazily allocating) the function-pointer value for a function.
    ///
    /// Each function is assigned a unique, stable memory block that serves as
    /// its address. The pointer `{ block, offset: 0 }` is the value of a
    /// function name when it decays to a function pointer (e.g. `fp = add;`),
    /// and an indirect call recovers the callee by mapping the block back to
    /// the function name. Returns `None` if `name` is not a known function.
    pub fn function_pointer(&mut self, name: &str) -> UBResult<Option<Pointer>> {
        if !self.functions.contains_key(name) {
            return Ok(None);
        }
        if let Some(block) = self.func_addresses.get(name) {
            return Ok(Some(Pointer::new(*block)));
        }
        // Allocate a fresh, never-aliased block to stand in for the function's
        // address. Size 1 keeps it distinct from every other object.
        let ptr = self.memory.alloc(1, 1)?;
        self.func_addresses.insert(name.to_string(), ptr.block);
        self.addr_to_func.insert(ptr.block, name.to_string());
        Ok(Some(ptr))
    }

    /// Resolve a function-pointer value back to the function it designates.
    ///
    /// The offset must be 0 (a function pointer points at the function, not
    /// into it), and the block must be a registered function address.
    fn function_at(&self, ptr: Pointer) -> Option<&str> {
        if ptr.offset != 0 {
            return None;
        }
        self.addr_to_func.get(&ptr.block).map(String::as_str)
    }

    /// Store a value at a memory location
    pub fn store_value(&mut self, ptr: Pointer, val: &CValue, ty: &CType) -> UBResult<()> {
        match val {
            CValue::Bool(b) => self.memory.store_u8(ptr, u8::from(*b)),
            // SAFETY: Intentional truncation - C semantics require storing low bits matching type size
            #[allow(clippy::cast_possible_truncation)]
            CValue::Int(i) => match ty.size() {
                1 => self.memory.store_u8(ptr, *i as u8),
                2 => self.memory.store_u16(ptr, *i as u16),
                4 => self.memory.store_i32(ptr, *i as i32),
                8 => self.memory.store_i64(ptr, *i as i64),
                _ => Err(UBKind::Other("unsupported integer size".to_string())),
            },
            // SAFETY: Intentional truncation - C semantics require storing low bits matching type size
            #[allow(clippy::cast_possible_truncation)]
            CValue::UInt(u) => match ty.size() {
                1 => self.memory.store_u8(ptr, *u as u8),
                2 => self.memory.store_u16(ptr, *u as u16),
                4 => self.memory.store_u32(ptr, *u as u32),
                8 => self.memory.store_u64(ptr, *u as u64),
                _ => Err(UBKind::Other("unsupported integer size".to_string())),
            },
            CValue::Float(f) => self.memory.store_f32(ptr, *f),
            CValue::Double(d) => self.memory.store_f64(ptr, *d),
            CValue::Pointer(p) => self.memory.store_ptr(ptr, *p),
            CValue::Struct(fields) => {
                if let CType::Struct {
                    fields: field_types,
                    ..
                } = ty.unqualified()
                {
                    let layouts = ty.struct_field_layouts().ok_or_else(|| {
                        UBKind::Other("type mismatch in struct store".to_string())
                    })?;
                    for ((val, field_ty), layout) in
                        fields.iter().zip(field_types.iter()).zip(layouts.iter())
                    {
                        let field_ptr = ptr
                            .offset(layout.byte_offset as i64)
                            .ok_or(UBKind::PointerOverflow)?;
                        match layout.bitfield {
                            Some(bf) => {
                                // A zero-width separator carries no value.
                                if !matches!(val, CValue::Undef) {
                                    self.store_bitfield(
                                        field_ptr,
                                        BitFieldRef {
                                            bit_offset: bf.bit_offset,
                                            bit_width: bf.bit_width,
                                            unit_bytes: bf.unit_bytes,
                                        },
                                        val,
                                    )?;
                                }
                            }
                            None => {
                                self.store_value(field_ptr, val, &field_ty.ty)?;
                            }
                        }
                    }
                    Ok(())
                } else {
                    Err(UBKind::Other("type mismatch in struct store".to_string()))
                }
            }
            CValue::Array(elems) => {
                if let CType::Array(elem_ty, _) = ty.unqualified() {
                    let elem_size = elem_ty.size();
                    for (i, val) in elems.iter().enumerate() {
                        let byte_offset = i
                            .checked_mul(elem_size)
                            .and_then(|o| i64::try_from(o).ok())
                            .ok_or(UBKind::PointerOverflow)?;
                        let elem_ptr = ptr.offset(byte_offset).ok_or(UBKind::PointerOverflow)?;
                        self.store_value(elem_ptr, val, elem_ty)?;
                    }
                    Ok(())
                } else {
                    Err(UBKind::Other("type mismatch in array store".to_string()))
                }
            }
            CValue::Union { value, .. } => {
                // Store the active field value at offset 0
                self.store_value(ptr, value, ty)
            }
            CValue::Undef => {
                // Don't store anything for undef
                Ok(())
            }
        }
    }

    /// Load a value from a memory location
    pub fn load_value(&self, ptr: Pointer, ty: &CType) -> UBResult<CValue> {
        match ty.unqualified() {
            CType::Int(IntKind::Bool, _) => {
                let b = self.memory.load_u8(ptr)?;
                Ok(CValue::Bool(b != 0))
            }
            // SAFETY: For unsigned loads, we reinterpret the signed bits as unsigned.
            // `d as u32` on i32 and `q as u64` on i64 are bit-preserving reinterpretations,
            // not truncation, since the types have the same width.
            CType::Int(kind, sign) => {
                let val = match kind.size() {
                    1 => {
                        let b = self.memory.load_u8(ptr)?;
                        match sign {
                            Signedness::Signed => CValue::Int(b as i8 as i128),
                            Signedness::Unsigned => CValue::UInt(b as u128),
                        }
                    }
                    2 => {
                        let w = self.memory.load_u16(ptr)?;
                        match sign {
                            Signedness::Signed => CValue::Int(w as i16 as i128),
                            Signedness::Unsigned => CValue::UInt(w as u128),
                        }
                    }
                    4 => {
                        let d = self.memory.load_i32(ptr)?;
                        match sign {
                            Signedness::Signed => CValue::Int(d as i128),
                            Signedness::Unsigned => CValue::UInt(d as u32 as u128),
                        }
                    }
                    8 => {
                        let q = self.memory.load_i64(ptr)?;
                        match sign {
                            Signedness::Signed => CValue::Int(q as i128),
                            Signedness::Unsigned => CValue::UInt(q as u64 as u128),
                        }
                    }
                    _ => return Err(UBKind::Other("unsupported integer size".to_string())),
                };
                Ok(val)
            }
            CType::Float(crate::types::FloatKind::Float) => {
                Ok(CValue::Float(self.memory.load_f32(ptr)?))
            }
            CType::Float(_) => Ok(CValue::Double(self.memory.load_f64(ptr)?)),
            CType::Pointer(_) => Ok(CValue::Pointer(self.memory.load_ptr(ptr)?)),
            CType::Enum { .. } => {
                // Enums are ints
                Ok(CValue::Int(self.memory.load_i32(ptr)? as i128))
            }
            CType::Struct { fields, .. } => {
                let layouts = ty
                    .struct_field_layouts()
                    .ok_or_else(|| UBKind::Other("type mismatch in struct load".to_string()))?;
                let mut values = Vec::with_capacity(fields.len());
                for (field, layout) in fields.iter().zip(layouts.iter()) {
                    let field_ptr = ptr
                        .offset(layout.byte_offset as i64)
                        .ok_or(UBKind::PointerOverflow)?;
                    match layout.bitfield {
                        Some(bf) => {
                            values.push(self.load_bitfield(
                                field_ptr,
                                &field.ty,
                                BitFieldRef {
                                    bit_offset: bf.bit_offset,
                                    bit_width: bf.bit_width,
                                    unit_bytes: bf.unit_bytes,
                                },
                            )?);
                        }
                        None => {
                            // A zero-width separator (unnamed, no storage)
                            // contributes a placeholder slot to keep the value
                            // vector aligned with the field list.
                            if field.is_bitfield() {
                                values.push(CValue::Undef);
                            } else {
                                values.push(self.load_value(field_ptr, &field.ty)?);
                            }
                        }
                    }
                }
                Ok(CValue::Struct(values))
            }
            CType::Array(elem_ty, count) => {
                let elem_size = elem_ty.size();
                let mut values = Vec::new();
                for i in 0..*count {
                    let byte_offset = i
                        .checked_mul(elem_size)
                        .and_then(|o| i64::try_from(o).ok())
                        .ok_or(UBKind::PointerOverflow)?;
                    let elem_ptr = ptr.offset(byte_offset).ok_or(UBKind::PointerOverflow)?;
                    values.push(self.load_value(elem_ptr, elem_ty)?);
                }
                Ok(CValue::Array(values))
            }
            _ => Err(UBKind::Other(format!("cannot load type {ty:?}"))),
        }
    }

    /// Load the raw storage unit (`unit_bytes` bytes) at `ptr` as an unsigned
    /// integer. Used by bit-field read/write so masking happens on the full
    /// unit regardless of the field's signedness.
    fn load_storage_unit(&self, ptr: Pointer, unit_bytes: usize) -> UBResult<u128> {
        match unit_bytes {
            1 => Ok(u128::from(self.memory.load_u8(ptr)?)),
            2 => Ok(u128::from(self.memory.load_u16(ptr)?)),
            4 => Ok(u128::from(self.memory.load_u32(ptr)?)),
            8 => Ok(u128::from(self.memory.load_u64(ptr)?)),
            _ => Err(UBKind::Other(format!(
                "unsupported bit-field storage unit size: {unit_bytes}"
            ))),
        }
    }

    /// Store an unsigned integer back into the raw storage unit at `ptr`,
    /// truncating to `unit_bytes`.
    #[allow(clippy::cast_possible_truncation)]
    fn store_storage_unit(&mut self, ptr: Pointer, unit_bytes: usize, raw: u128) -> UBResult<()> {
        match unit_bytes {
            1 => self.memory.store_u8(ptr, raw as u8),
            2 => self.memory.store_u16(ptr, raw as u16),
            4 => self.memory.store_u32(ptr, raw as u32),
            8 => self.memory.store_u64(ptr, raw as u64),
            _ => Err(UBKind::Other(format!(
                "unsupported bit-field storage unit size: {unit_bytes}"
            ))),
        }
    }

    /// Read a bit-field at `ptr` (the storage unit), extracting `bit_width`
    /// bits starting at `bit_offset` (counted from the least-significant bit).
    /// The result is sign-extended for signed declared types (C11 6.7.2.1).
    pub fn load_bitfield(&self, ptr: Pointer, ty: &CType, bits: BitFieldRef) -> UBResult<CValue> {
        if bits.bit_width == 0 || bits.bit_width > bits.unit_bytes * 8 {
            return Err(UBKind::Other(format!(
                "invalid bit-field width: {}",
                bits.bit_width
            )));
        }
        let raw = self.load_storage_unit(ptr, bits.unit_bytes)?;
        // Mask is `bit_width` ones; safe because `bit_width <= 128`.
        let mask: u128 = if bits.bit_width >= 128 {
            u128::MAX
        } else {
            (1u128 << bits.bit_width) - 1
        };
        let field_bits = (raw >> bits.bit_offset) & mask;

        let signed = matches!(ty.unqualified(), CType::Int(_, Signedness::Signed));
        if signed {
            // Sign-extend: if the top retained bit is set, the value is
            // negative in two's-complement of `bit_width` bits.
            let sign_bit = 1u128 << (bits.bit_width - 1);
            if field_bits & sign_bit != 0 {
                // Set all the higher bits, then reinterpret as i128.
                let extended = field_bits | !mask;
                #[allow(clippy::cast_possible_wrap)]
                Ok(CValue::Int(extended as i128))
            } else {
                #[allow(clippy::cast_possible_wrap)]
                Ok(CValue::Int(field_bits as i128))
            }
        } else {
            Ok(CValue::UInt(field_bits))
        }
    }

    /// Write a bit-field at `ptr` (the storage unit): the low `bit_width` bits
    /// of `value` replace bits `bit_offset..bit_offset+bit_width`; the rest of
    /// the storage unit is preserved. The value wraps to the field width.
    pub fn store_bitfield(
        &mut self,
        ptr: Pointer,
        bits: BitFieldRef,
        value: &CValue,
    ) -> UBResult<()> {
        if bits.bit_width == 0 || bits.bit_width > bits.unit_bytes * 8 {
            return Err(UBKind::Other(format!(
                "invalid bit-field width: {}",
                bits.bit_width
            )));
        }
        // Reinterpret the incoming value's low bits without regard to sign:
        // both signed and unsigned values store the same low `bit_width` bits.
        let incoming: u128 = match value {
            CValue::Bool(b) => u128::from(*b),
            #[allow(clippy::cast_sign_loss)]
            CValue::Int(i) => *i as u128,
            CValue::UInt(u) => *u,
            _ => {
                return Err(UBKind::Other(
                    "bit-field assignment requires an integer value".to_string(),
                ));
            }
        };
        let mask: u128 = if bits.bit_width >= 128 {
            u128::MAX
        } else {
            (1u128 << bits.bit_width) - 1
        };
        let positioned = (incoming & mask) << bits.bit_offset;
        let clear = !(mask << bits.bit_offset);

        let raw = self.load_storage_unit(ptr, bits.unit_bytes)?;
        let new_raw = (raw & clear) | positioned;
        self.store_storage_unit(ptr, bits.unit_bytes, new_raw)
    }

    /// Get or create a string literal
    fn get_string_literal(&mut self, s: &str) -> UBResult<Pointer> {
        if let Some(ptr) = self.string_literals.get(s) {
            return Ok(*ptr);
        }

        // Allocate string with null terminator
        let bytes = s.as_bytes();
        let ptr = self.memory.alloc(bytes.len() + 1, 1)?;

        // Store bytes
        for (i, &b) in bytes.iter().enumerate() {
            let char_ptr = ptr.offset(i as i64).ok_or(UBKind::PointerOverflow)?;
            self.memory.store_u8(char_ptr, b)?;
        }
        // Null terminator
        let null_ptr = ptr
            .offset(bytes.len() as i64)
            .ok_or(UBKind::PointerOverflow)?;
        self.memory.store_u8(null_ptr, 0)?;

        self.string_literals.insert(s.to_string(), ptr);
        Ok(ptr)
    }

    /// Evaluate an initializer into a [`CValue`] of the given type.
    ///
    /// Implements C99 6.7.8 aggregate initialization, including designated
    /// initializers (`.field = v`, `[index] = v`) and the positional
    /// continuation rule: after a designator, subsequent un-designated
    /// initializers resume from the element following the designated one.
    fn eval_initializer(&mut self, init: &Initializer, ty: &CType) -> UBResult<CValue> {
        match init {
            Initializer::Expr(expr) => self.eval_expr_to_value(expr),
            Initializer::List(inits) => self.eval_init_list(inits, ty),
            Initializer::Designated { designator, init } => {
                // A bare designated initializer at top level (no surrounding
                // brace list) is treated as a single-element list so the
                // designator is resolved against `ty`.
                let one = [Initializer::Designated {
                    designator: designator.clone(),
                    init: init.clone(),
                }];
                self.eval_init_list(&one, ty)
            }
        }
    }

    /// Evaluate a brace-enclosed initializer list against an aggregate type,
    /// honoring designators and positional continuation.
    fn eval_init_list(&mut self, inits: &[Initializer], ty: &CType) -> UBResult<CValue> {
        match ty.unqualified() {
            CType::Array(elem_ty, count) => {
                let mut values = vec![CValue::zero(elem_ty); *count];
                let mut cursor = 0usize;
                for entry in inits {
                    cursor = self.apply_array_entry(&mut values, *count, elem_ty, cursor, entry)?;
                }
                Ok(CValue::Array(values))
            }
            CType::Struct { fields, .. } => {
                let mut values: Vec<CValue> = fields.iter().map(|f| CValue::zero(&f.ty)).collect();
                let mut cursor = 0usize;
                for entry in inits {
                    cursor = self.apply_struct_entry(&mut values, fields, cursor, entry)?;
                }
                Ok(CValue::Struct(values))
            }
            CType::Union { fields, .. } => {
                // A brace list for a union initializes the first member unless a
                // designator selects another. We support the leading entry.
                let mut active = 0usize;
                let mut value = fields
                    .first()
                    .map_or(CValue::Undef, |f| CValue::zero(&f.ty));
                for entry in inits {
                    match entry {
                        Initializer::Designated { designator, init } => {
                            let (idx, field_ty) = resolve_field_designator(designator, fields)?;
                            active = idx;
                            value = self.apply_designated_chain(
                                CValue::zero(field_ty),
                                field_ty,
                                designator,
                                1,
                                init,
                            )?;
                        }
                        _ => {
                            if let Some(field) = fields.first() {
                                active = 0;
                                value = self.eval_initializer(entry, &field.ty)?;
                            }
                        }
                    }
                }
                Ok(CValue::Union {
                    active_field: active,
                    value: Box::new(value),
                })
            }
            scalar => {
                // Scalar initialized with a brace list: use the first element.
                if let Some(first) = inits.first() {
                    self.eval_initializer(first, scalar)
                } else {
                    Ok(CValue::zero(scalar))
                }
            }
        }
    }

    /// Apply one initializer-list entry to an array buffer, returning the next
    /// positional cursor.
    fn apply_array_entry(
        &mut self,
        values: &mut [CValue],
        count: usize,
        elem_ty: &CType,
        cursor: usize,
        entry: &Initializer,
    ) -> UBResult<usize> {
        match entry {
            Initializer::Designated { designator, init } => {
                let idx = self.resolve_index_designator(designator)?;
                if idx >= count {
                    return Err(UBKind::OutOfBounds);
                }
                let existing = std::mem::replace(&mut values[idx], CValue::Undef);
                values[idx] =
                    self.apply_designated_chain(existing, elem_ty, designator, 1, init)?;
                Ok(idx + 1)
            }
            _ => {
                if cursor >= count {
                    // Excess positional initializers are ignored (already covers
                    // the slot range); evaluate for side effects but discard.
                    self.eval_initializer(entry, elem_ty)?;
                    Ok(cursor + 1)
                } else {
                    values[cursor] = self.eval_initializer(entry, elem_ty)?;
                    Ok(cursor + 1)
                }
            }
        }
    }

    /// Apply one initializer-list entry to a struct buffer, returning the next
    /// positional cursor (the index after the field just written).
    fn apply_struct_entry(
        &mut self,
        values: &mut [CValue],
        fields: &[crate::types::StructField],
        cursor: usize,
        entry: &Initializer,
    ) -> UBResult<usize> {
        match entry {
            Initializer::Designated { designator, init } => {
                let (idx, field_ty) = resolve_field_designator(designator, fields)?;
                // C99 6.7.8p2: a flexible array member cannot be initialized.
                if field_ty.is_flexible_array() {
                    return Err(UBKind::Other(
                        "cannot initialize a flexible array member".to_string(),
                    ));
                }
                let existing = std::mem::replace(&mut values[idx], CValue::Undef);
                values[idx] =
                    self.apply_designated_chain(existing, field_ty, designator, 1, init)?;
                Ok(idx + 1)
            }
            _ => {
                if cursor < fields.len() {
                    // C99 6.7.8p2: a flexible array member cannot be
                    // initialized, including by a positional initializer.
                    if fields[cursor].ty.is_flexible_array() {
                        return Err(UBKind::Other(
                            "cannot initialize a flexible array member".to_string(),
                        ));
                    }
                    values[cursor] = self.eval_initializer(entry, &fields[cursor].ty)?;
                }
                // Excess positional initializers past the last field are ignored.
                Ok(cursor + 1)
            }
        }
    }

    /// Resolve the remaining designators in a chain (starting at `depth`) by
    /// descending into `current` (of type `ty`) and applying `init` at the leaf.
    ///
    /// `depth == 1` for the first call means the outermost designator has
    /// already been consumed by the caller (which selected `current`). For a
    /// non-chain designator (`Field`/`Index`) there is nothing left to descend,
    /// so `init` is applied directly to `ty`.
    fn apply_designated_chain(
        &mut self,
        current: CValue,
        ty: &CType,
        designator: &Designator,
        depth: usize,
        init: &Initializer,
    ) -> UBResult<CValue> {
        let chain = match designator {
            Designator::Chain(ds) => ds.as_slice(),
            _ => {
                // Single-level designator: apply the value directly.
                return self.eval_initializer(init, ty);
            }
        };

        if depth >= chain.len() {
            // All designators consumed: apply the value to the current leaf type.
            return self.eval_initializer(init, ty);
        }

        // Descend one more level using chain[depth].
        match (ty.unqualified(), &chain[depth]) {
            (
                CType::Struct { fields, .. } | CType::Union { fields, .. },
                Designator::Field(name),
            ) => {
                let (idx, field) = ty
                    .get_field(name)
                    .ok_or_else(|| UBKind::Other(format!("unknown struct field: {name}")))?;
                let field_ty = field.ty.clone();
                let mut slots = match current {
                    CValue::Struct(v) => v,
                    _ => fields.iter().map(|f| CValue::zero(&f.ty)).collect(),
                };
                if idx >= slots.len() {
                    return Err(UBKind::OutOfBounds);
                }
                let existing = std::mem::replace(&mut slots[idx], CValue::Undef);
                slots[idx] =
                    self.apply_designated_chain(existing, &field_ty, designator, depth + 1, init)?;
                if matches!(ty.unqualified(), CType::Union { .. }) {
                    Ok(CValue::Union {
                        active_field: idx,
                        value: Box::new(std::mem::replace(&mut slots[idx], CValue::Undef)),
                    })
                } else {
                    Ok(CValue::Struct(slots))
                }
            }
            (CType::Array(elem_ty, len), Designator::Index(idx_expr)) => {
                let idx = self.eval_const_index(idx_expr)?;
                if idx >= *len {
                    return Err(UBKind::OutOfBounds);
                }
                let mut slots = match current {
                    CValue::Array(v) => v,
                    _ => vec![CValue::zero(elem_ty); *len],
                };
                let existing = std::mem::replace(&mut slots[idx], CValue::Undef);
                slots[idx] =
                    self.apply_designated_chain(existing, elem_ty, designator, depth + 1, init)?;
                Ok(CValue::Array(slots))
            }
            (_, Designator::Field(name)) => Err(UBKind::Other(format!(
                "field designator .{name} on non-aggregate"
            ))),
            (_, Designator::Index(_)) => Err(UBKind::Other(
                "index designator on non-array type".to_string(),
            )),
            (_, Designator::Chain(_)) => Err(UBKind::Other(
                "nested chain designator unsupported".to_string(),
            )),
        }
    }

    /// Resolve the first (outermost) designator of an array entry to an index.
    fn resolve_index_designator(&mut self, designator: &Designator) -> UBResult<usize> {
        let first = match designator {
            Designator::Index(idx) => idx.as_ref(),
            Designator::Chain(ds) => match ds.first() {
                Some(Designator::Index(idx)) => idx.as_ref(),
                Some(Designator::Field(name)) => {
                    return Err(UBKind::Other(format!(
                        "field designator .{name} on array type"
                    )));
                }
                _ => {
                    return Err(UBKind::Other("empty array designator chain".to_string()));
                }
            },
            Designator::Field(name) => {
                return Err(UBKind::Other(format!(
                    "field designator .{name} on array type"
                )));
            }
        };
        self.eval_const_index(first)
    }

    /// Evaluate an array index designator expression to a non-negative `usize`.
    fn eval_const_index(&mut self, expr: &CExpr) -> UBResult<usize> {
        let val = self.eval_expr_to_value(expr)?;
        let idx = val.to_int()?;
        if idx < 0 {
            return Err(UBKind::OutOfBounds);
        }
        usize::try_from(idx).map_err(|_| UBKind::OutOfBounds)
    }
}

/// Resolve the first (outermost) designator of a struct entry to a
/// `(field index, field type)` pair.
fn resolve_field_designator<'a>(
    designator: &Designator,
    fields: &'a [crate::types::StructField],
) -> UBResult<(usize, &'a crate::types::CType)> {
    let name = match designator {
        Designator::Field(name) => name,
        Designator::Chain(ds) => match ds.first() {
            Some(Designator::Field(name)) => name,
            Some(Designator::Index(_)) => {
                return Err(UBKind::Other(
                    "index designator [..] on struct type".to_string(),
                ));
            }
            _ => {
                return Err(UBKind::Other("empty struct designator chain".to_string()));
            }
        },
        Designator::Index(_) => {
            return Err(UBKind::Other(
                "index designator [..] on struct type".to_string(),
            ));
        }
    };
    fields
        .iter()
        .enumerate()
        .find(|(_, f)| &f.name == name)
        .map(|(i, f)| (i, &f.ty))
        .ok_or_else(|| UBKind::Other(format!("unknown struct field: {name}")))
}

/// The interpreter
pub struct Interpreter<'a> {
    state: &'a mut State,
}

impl<'a> Interpreter<'a> {
    pub fn new(state: &'a mut State) -> Self {
        Self { state }
    }

    /// Evaluate an expression to a value (rvalue)
    pub fn eval_expr_to_value(&mut self, expr: &CExpr) -> UBResult<CValue> {
        let result = self.eval_expr(expr)?;
        match result {
            ExprResult::RValue(val) => Ok(val),
            ExprResult::LValue(lv) => match lv.bitfield {
                Some(bits) => self.state.load_bitfield(lv.ptr, &lv.ty, bits),
                None => self.state.load_value(lv.ptr, &lv.ty),
            },
        }
    }

    /// Evaluate an expression
    pub fn eval_expr(&mut self, expr: &CExpr) -> UBResult<ExprResult> {
        match expr {
            CExpr::IntLit(i) => Ok(ExprResult::rvalue(CValue::Int(*i as i128))),

            CExpr::UIntLit(u) => Ok(ExprResult::rvalue(CValue::UInt(*u as u128))),

            CExpr::FloatLit(f) => Ok(ExprResult::rvalue(CValue::Double(*f))),

            CExpr::CharLit(c) => Ok(ExprResult::rvalue(CValue::Int(*c as i128))),

            CExpr::StringLit(s) => {
                let ptr = self.state.get_string_literal(s)?;
                Ok(ExprResult::rvalue(CValue::Pointer(ptr)))
            }

            CExpr::Var(name) => {
                if let Some(binding) = self.state.lookup_var(name) {
                    return Ok(ExprResult::lvalue(binding.ptr, binding.ty.clone()));
                }
                // A bare function name (with no shadowing variable) decays to a
                // function pointer rvalue, e.g. `int (*fp)(int) = add;`.
                if let Some(ptr) = self.state.function_pointer(name)? {
                    return Ok(ExprResult::rvalue(CValue::Pointer(ptr)));
                }
                Err(UBKind::Other(format!("undefined variable: {name}")))
            }

            CExpr::BinOp { op, left, right } => self.eval_binop(*op, left, right),

            CExpr::UnaryOp { op, operand } => self.eval_unary(*op, operand),

            CExpr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond_val = self.eval_expr_to_value(cond)?;
                if cond_val.to_bool()? {
                    self.eval_expr(then_expr)
                } else {
                    self.eval_expr(else_expr)
                }
            }

            CExpr::Cast { ty, expr } => {
                let val = self.eval_expr_to_value(expr)?;
                // Get source type (approximate)
                let from_ty = self.infer_type(expr)?;
                let casted = val.cast(&from_ty, ty)?;
                Ok(ExprResult::rvalue(casted))
            }

            CExpr::SizeOf(arg) => {
                let ty = match arg {
                    SizeOfArg::Type(ty) => ty.clone(),
                    // Don't evaluate, just get the operand's type.
                    SizeOfArg::Expr(e) => self.infer_type(e)?,
                };
                // `sizeof` applied to an incomplete type is a constraint
                // violation (C11 6.5.3.4p1): the result would be meaningless
                // because the type's size is not known. This covers `void`, a
                // bare flexible array / incomplete array type (`T[]`), a
                // function type, and a forward-declared (fieldless)
                // struct/union. A *complete* type whose last member is a
                // flexible array (`struct { int x; int arr[]; }`) still has a
                // well-defined size (omitting the FAM) and is allowed.
                if !ty.is_complete() {
                    // Keep the more specific "incomplete array" wording for a
                    // bare flexible-array operand.
                    let detail = if ty.is_flexible_array() {
                        "incomplete array type"
                    } else {
                        "incomplete type"
                    };
                    return Err(UBKind::Other(format!(
                        "sizeof applied to {detail} {ty:?} (C11 6.5.3.4p1)"
                    )));
                }
                Ok(ExprResult::rvalue(CValue::UInt(ty.size() as u128)))
            }

            CExpr::AlignOf(ty) => Ok(ExprResult::rvalue(CValue::UInt(ty.align() as u128))),

            CExpr::Index { array, index } => {
                let arr_val = self.eval_expr(array)?;
                let idx_val = self.eval_expr_to_value(index)?;
                let idx = to_pointer_offset(idx_val.to_int()?)?;

                match arr_val {
                    ExprResult::LValue(lv) => {
                        // Array subscript
                        if let Some(elem_ty) = lv.ty.element() {
                            let offset = idx
                                .checked_mul(elem_ty.size() as i64)
                                .ok_or(UBKind::PointerOverflow)?;
                            let elem_ptr = lv.ptr.offset(offset).ok_or(UBKind::PointerOverflow)?;
                            Ok(ExprResult::lvalue(elem_ptr, elem_ty.clone()))
                        } else if let Some(pointee) = lv.ty.pointee() {
                            // Pointer decay
                            let ptr = self.state.load_value(lv.ptr, &lv.ty)?;
                            let base = ptr.to_ptr()?;
                            let offset = idx
                                .checked_mul(pointee.size() as i64)
                                .ok_or(UBKind::PointerOverflow)?;
                            let elem_ptr = base.offset(offset).ok_or(UBKind::PointerOverflow)?;
                            Ok(ExprResult::lvalue(elem_ptr, pointee.clone()))
                        } else {
                            Err(UBKind::Other("subscript on non-array/pointer".to_string()))
                        }
                    }
                    ExprResult::RValue(CValue::Pointer(ptr)) => {
                        // Pointer indexing
                        let arr_ty = self.infer_type(array)?;
                        if let Some(pointee) = arr_ty.pointee() {
                            let offset = idx
                                .checked_mul(pointee.size() as i64)
                                .ok_or(UBKind::PointerOverflow)?;
                            let elem_ptr = ptr.offset(offset).ok_or(UBKind::PointerOverflow)?;
                            Ok(ExprResult::lvalue(elem_ptr, pointee.clone()))
                        } else {
                            Err(UBKind::Other("subscript on non-pointer".to_string()))
                        }
                    }
                    _ => Err(UBKind::Other("subscript on non-array".to_string())),
                }
            }

            CExpr::Member { object, field } => {
                let obj_result = self.eval_expr(object)?;
                match obj_result {
                    ExprResult::LValue(lv) => Self::field_lvalue(&lv.ty, lv.ptr, field),
                    _ => Err(UBKind::Other("member access on non-lvalue".to_string())),
                }
            }

            CExpr::Arrow { pointer, field } => {
                let ptr_val = self.eval_expr_to_value(pointer)?;
                let ptr = ptr_val.to_ptr()?;

                let ptr_ty = self.infer_type(pointer)?;
                let struct_ty = ptr_ty
                    .pointee()
                    .ok_or_else(|| UBKind::Other("arrow on non-pointer".to_string()))?;

                Self::field_lvalue(struct_ty, ptr, field)
            }

            CExpr::Call { func, args } => self.eval_call(func, args),

            CExpr::CompoundLiteral { ty, init } => {
                let size = ty.size();
                let align = ty.align();
                let ptr = self.state.memory.alloc(size, align)?;

                // Initialize
                let full_init = Initializer::List(init.clone());
                let val = self.state.eval_initializer(&full_init, ty)?;
                self.state.store_value(ptr, &val, ty)?;

                Ok(ExprResult::lvalue(ptr, ty.clone()))
            }

            CExpr::Generic {
                control,
                associations,
            } => {
                // C11 6.5.1.1: generic selection.
                // The controlling expression is NOT evaluated; only its type is
                // used. After lvalue conversion the controlling type's top-level
                // qualifiers are dropped (`unqualified`). The result expression
                // is the one from the association whose type name is compatible
                // with the controlling type; otherwise the `default` association.
                let control_ty = self.infer_type(control)?;
                let control_ty = control_ty.unqualified();

                let mut selected: Option<&CExpr> = None;
                let mut default_branch: Option<&CExpr> = None;
                for (assoc_ty, result_expr) in associations {
                    match assoc_ty {
                        Some(ty) => {
                            if ty.unqualified().is_compatible(control_ty) {
                                if selected.is_some() {
                                    // 6.5.1.1p2: the controlling type shall be
                                    // compatible with at most one type name.
                                    return Err(UBKind::Other(
                                        "_Generic: controlling type matches multiple associations"
                                            .to_string(),
                                    ));
                                }
                                selected = Some(result_expr);
                            }
                        }
                        None => {
                            if default_branch.is_some() {
                                // 6.5.1.1p2: at most one default association.
                                return Err(UBKind::Other(
                                    "_Generic: multiple default associations".to_string(),
                                ));
                            }
                            default_branch = Some(result_expr);
                        }
                    }
                }

                match selected.or(default_branch) {
                    Some(chosen) => {
                        // Clone to release the borrow on `associations` before the
                        // recursive `&mut self` evaluation of the chosen branch.
                        let chosen = chosen.clone();
                        self.eval_expr(&chosen)
                    }
                    None => Err(UBKind::Other(
                        "_Generic: no association matches controlling type and no default"
                            .to_string(),
                    )),
                }
            }

            CExpr::StmtExpr(stmts) => {
                // GCC extension: ({ stmts; expr })
                let mut last_val = CValue::Undef;
                for stmt in stmts {
                    if let ControlFlow::Return(Some(v)) = self.exec_stmt(stmt)? {
                        return Ok(ExprResult::rvalue(v));
                    }
                    // If last statement is expression, capture its value
                    if let CStmt::Expr(e) = stmt {
                        last_val = self.eval_expr_to_value(e)?;
                    }
                }
                Ok(ExprResult::rvalue(last_val))
            }
        }
    }

    /// Evaluate a binary operation
    fn eval_binop(&mut self, op: BinOp, left: &CExpr, right: &CExpr) -> UBResult<ExprResult> {
        // Handle short-circuit operators
        if op == BinOp::LogAnd {
            let l = self.eval_expr_to_value(left)?;
            if !l.to_bool()? {
                return Ok(ExprResult::rvalue(CValue::Int(0)));
            }
            let r = self.eval_expr_to_value(right)?;
            return Ok(ExprResult::rvalue(CValue::Int(i128::from(r.to_bool()?))));
        }

        if op == BinOp::LogOr {
            let l = self.eval_expr_to_value(left)?;
            if l.to_bool()? {
                return Ok(ExprResult::rvalue(CValue::Int(1)));
            }
            let r = self.eval_expr_to_value(right)?;
            return Ok(ExprResult::rvalue(CValue::Int(i128::from(r.to_bool()?))));
        }

        // Handle comma operator
        if op == BinOp::Comma {
            let _ = self.eval_expr_to_value(left)?;
            return self.eval_expr(right);
        }

        // Handle assignment operators
        if op.is_assignment() {
            return self.eval_assignment(op, left, right);
        }

        // Regular binary operators
        let l = self.eval_expr_to_value(left)?;
        let r = self.eval_expr_to_value(right)?;

        let left_ty = self.infer_type(left)?;
        // C11 6.5.7p3: shift operators do not undergo the usual arithmetic
        // conversions. Each operand is integer-promoted independently and the
        // result type (which governs the shift-amount UB check and truncation)
        // is that of the promoted *left* operand only.
        let promoted_ty = if op.is_shift() {
            left_ty.integer_promotion()
        } else {
            left_ty.usual_arithmetic_conversion(&self.infer_type(right)?)
        };

        // C11 6.5.8p3 / 6.5.9p4: relational and equality operators undergo the
        // usual arithmetic conversions, so a comparison between two arithmetic
        // operands of different types (e.g. `sizeof(int) >= 2`, where the left
        // is `unsigned` and the right `int`) compares them in a common type.
        // Convert both arithmetic operands to `promoted_ty` before comparing;
        // pointer/aggregate operands fall through to the comparison's own arms.
        if op.is_comparison() {
            let (cmp_l, cmp_r) = if l.is_arithmetic() && r.is_arithmetic() {
                (
                    l.cast(&left_ty, &promoted_ty)?,
                    r.cast(&self.infer_type(right)?, &promoted_ty)?,
                )
            } else {
                (l, r)
            };
            let result = match op {
                BinOp::Eq => cmp_l.eq(&cmp_r)?,
                BinOp::Ne => cmp_l.ne(&cmp_r)?,
                BinOp::Lt => cmp_l.lt(&cmp_r)?,
                BinOp::Le => cmp_l.le(&cmp_r)?,
                BinOp::Gt => cmp_l.gt(&cmp_r)?,
                BinOp::Ge => cmp_l.ge(&cmp_r)?,
                _ => unreachable!("op.is_comparison() guarantees a comparison operator"),
            };
            return Ok(ExprResult::rvalue(result));
        }

        let result = match op {
            BinOp::Add => l.add(&r, &promoted_ty)?,
            BinOp::Sub => l.sub(&r, &promoted_ty)?,
            BinOp::Mul => l.mul(&r, &promoted_ty)?,
            BinOp::Div => l.div(&r, &promoted_ty)?,
            BinOp::Mod => l.rem(&r, &promoted_ty)?,
            BinOp::BitAnd => l.bit_and(&r, &promoted_ty)?,
            BinOp::BitOr => l.bit_or(&r, &promoted_ty)?,
            BinOp::BitXor => l.bit_xor(&r, &promoted_ty)?,
            BinOp::Shl => l.shl(&r, &promoted_ty)?,
            BinOp::Shr => l.shr(&r, &promoted_ty)?,
            _ => unreachable!("comparison operators handled above"),
        };

        Ok(ExprResult::rvalue(result))
    }

    /// Build the lvalue for member `field` of an aggregate of type `agg_ty`
    /// whose first byte lives at `base`. Resolves bit-field members to an
    /// lvalue that designates the bit range within the storage unit.
    fn field_lvalue(agg_ty: &CType, base: Pointer, field: &str) -> UBResult<ExprResult> {
        let layout = agg_ty
            .field_layout(field)
            .ok_or_else(|| UBKind::Other(format!("no field: {field}")))?;
        let (_, field_info) = agg_ty
            .get_field(field)
            .ok_or_else(|| UBKind::Other(format!("no field: {field}")))?;
        let field_ptr = base
            .offset(layout.byte_offset as i64)
            .ok_or(UBKind::PointerOverflow)?;
        match layout.bitfield {
            Some(bf) => Ok(ExprResult::lvalue_bitfield(
                field_ptr,
                field_info.ty.clone(),
                BitFieldRef {
                    bit_offset: bf.bit_offset,
                    bit_width: bf.bit_width,
                    unit_bytes: bf.unit_bytes,
                },
            )),
            None => Ok(ExprResult::lvalue(field_ptr, field_info.ty.clone())),
        }
    }

    /// Evaluate an assignment operation
    fn eval_assignment(&mut self, op: BinOp, left: &CExpr, right: &CExpr) -> UBResult<ExprResult> {
        let ExprResult::LValue(lv) = self.eval_expr(left)? else {
            return Err(UBKind::Other("assignment to non-lvalue".to_string()));
        };

        let rhs = self.eval_expr_to_value(right)?;

        let new_val = if op == BinOp::Assign {
            // Simple assignment
            rhs.cast(&self.infer_type(right)?, &lv.ty)?
        } else {
            // Compound assignment: load, operate, store. Reading a bit-field
            // goes through `load_bitfield` so the operand reflects the narrowed
            // (and possibly sign-extended) field value.
            let old_val = match lv.bitfield {
                Some(bits) => self.state.load_bitfield(lv.ptr, &lv.ty, bits)?,
                None => self.state.load_value(lv.ptr, &lv.ty)?,
            };
            match op {
                BinOp::AddAssign => old_val.add(&rhs, &lv.ty)?,
                BinOp::SubAssign => old_val.sub(&rhs, &lv.ty)?,
                BinOp::MulAssign => old_val.mul(&rhs, &lv.ty)?,
                BinOp::DivAssign => old_val.div(&rhs, &lv.ty)?,
                BinOp::ModAssign => old_val.rem(&rhs, &lv.ty)?,
                BinOp::BitAndAssign => old_val.bit_and(&rhs, &lv.ty)?,
                BinOp::BitOrAssign => old_val.bit_or(&rhs, &lv.ty)?,
                BinOp::BitXorAssign => old_val.bit_xor(&rhs, &lv.ty)?,
                BinOp::ShlAssign => old_val.shl(&rhs, &lv.ty)?,
                BinOp::ShrAssign => old_val.shr(&rhs, &lv.ty)?,
                _ => unreachable!("compound assignment op not covered"),
            }
        };

        match lv.bitfield {
            Some(bits) => {
                self.state.store_bitfield(lv.ptr, bits, &new_val)?;
                // The value of an assignment expression is the value stored,
                // re-read so it reflects bit-field truncation / sign-extension.
                let stored = self.state.load_bitfield(lv.ptr, &lv.ty, bits)?;
                Ok(ExprResult::rvalue(stored))
            }
            None => {
                self.state.store_value(lv.ptr, &new_val, &lv.ty)?;
                Ok(ExprResult::rvalue(new_val))
            }
        }
    }

    /// Evaluate a unary operation
    fn eval_unary(&mut self, op: UnaryOp, operand: &CExpr) -> UBResult<ExprResult> {
        match op {
            UnaryOp::Neg => {
                let val = self.eval_expr_to_value(operand)?;
                let ty = self.infer_type(operand)?;
                Ok(ExprResult::rvalue(val.neg(&ty)?))
            }

            UnaryOp::Pos => {
                // No-op for arithmetic types
                self.eval_expr(operand)
            }

            UnaryOp::BitNot => {
                let val = self.eval_expr_to_value(operand)?;
                let ty = self.infer_type(operand)?;
                Ok(ExprResult::rvalue(val.bit_not(&ty)?))
            }

            UnaryOp::LogNot => {
                let val = self.eval_expr_to_value(operand)?;
                Ok(ExprResult::rvalue(val.log_not()?))
            }

            UnaryOp::Deref => {
                let ptr_val = self.eval_expr_to_value(operand)?;
                let ptr = ptr_val.to_ptr()?;
                let ptr_ty = self.infer_type(operand)?;
                let pointee_ty = ptr_ty
                    .pointee()
                    .ok_or_else(|| UBKind::Other("deref non-pointer".to_string()))?;
                Ok(ExprResult::lvalue(ptr, pointee_ty.clone()))
            }

            UnaryOp::AddrOf => {
                let result = self.eval_expr(operand)?;
                match result {
                    // C11 6.5.3.2p1: the `&` operand may not be a bit-field.
                    ExprResult::LValue(lv) if lv.bitfield.is_some() => Err(UBKind::Other(
                        "cannot take the address of a bit-field".to_string(),
                    )),
                    ExprResult::LValue(lv) => Ok(ExprResult::rvalue(CValue::Pointer(lv.ptr))),
                    // `&f` for a function designator `f` is the function
                    // pointer itself (functions are not lvalues with storage):
                    // `&f` and `f` yield the same value.
                    ExprResult::RValue(val @ CValue::Pointer(_))
                        if self.is_function_designator(operand) =>
                    {
                        Ok(ExprResult::rvalue(val))
                    }
                    _ => Err(UBKind::Other("address-of non-lvalue".to_string())),
                }
            }

            UnaryOp::PreInc | UnaryOp::PreDec => {
                let ExprResult::LValue(lv) = self.eval_expr(operand)? else {
                    return Err(UBKind::Other("increment/decrement non-lvalue".to_string()));
                };

                let old_val = match lv.bitfield {
                    Some(bits) => self.state.load_bitfield(lv.ptr, &lv.ty, bits)?,
                    None => self.state.load_value(lv.ptr, &lv.ty)?,
                };
                let one = CValue::Int(1);
                let new_val = if op == UnaryOp::PreInc {
                    old_val.add(&one, &lv.ty)?
                } else {
                    old_val.sub(&one, &lv.ty)?
                };

                match lv.bitfield {
                    Some(bits) => {
                        self.state.store_bitfield(lv.ptr, bits, &new_val)?;
                        let stored = self.state.load_bitfield(lv.ptr, &lv.ty, bits)?;
                        Ok(ExprResult::rvalue(stored))
                    }
                    None => {
                        self.state.store_value(lv.ptr, &new_val, &lv.ty)?;
                        Ok(ExprResult::rvalue(new_val))
                    }
                }
            }

            UnaryOp::PostInc | UnaryOp::PostDec => {
                let ExprResult::LValue(lv) = self.eval_expr(operand)? else {
                    return Err(UBKind::Other("increment/decrement non-lvalue".to_string()));
                };

                let old_val = match lv.bitfield {
                    Some(bits) => self.state.load_bitfield(lv.ptr, &lv.ty, bits)?,
                    None => self.state.load_value(lv.ptr, &lv.ty)?,
                };
                let one = CValue::Int(1);
                let new_val = if op == UnaryOp::PostInc {
                    old_val.add(&one, &lv.ty)?
                } else {
                    old_val.sub(&one, &lv.ty)?
                };

                match lv.bitfield {
                    Some(bits) => self.state.store_bitfield(lv.ptr, bits, &new_val)?,
                    None => self.state.store_value(lv.ptr, &new_val, &lv.ty)?,
                }
                Ok(ExprResult::rvalue(old_val)) // Return old value
            }
        }
    }

    /// True if `expr` is a bare function name not shadowed by a variable,
    /// i.e. a function designator that decays to a function pointer.
    fn is_function_designator(&self, expr: &CExpr) -> bool {
        matches!(expr, CExpr::Var(name)
            if self.state.lookup_var(name).is_none()
                && self.state.functions.contains_key(name))
    }

    /// Strip operators that leave a function designator unchanged.
    ///
    /// In C a function designator and a pointer to it are interchangeable as a
    /// call target: `add`, `&add`, `*fp`, `**fp`, `(*&add)` all designate the
    /// same function. We peel `*` (Deref) and `&` (AddrOf) so the remaining
    /// expression evaluates directly to the underlying function-pointer value
    /// (avoiding a load through a `Function`-typed lvalue, which has no storage).
    fn strip_func_designators(expr: &CExpr) -> &CExpr {
        let mut cur = expr;
        while let CExpr::UnaryOp {
            op: UnaryOp::Deref | UnaryOp::AddrOf,
            operand,
        } = cur
        {
            cur = operand;
        }
        cur
    }

    /// Resolve a call target to a concrete function name.
    ///
    /// Direct calls (`name(..)`) short-circuit to the named function unless a
    /// variable of the same name shadows it. Otherwise the target is treated as
    /// an indirect call: the callee's static type must be a function or a
    /// pointer to function, it is evaluated to a function-pointer value, and
    /// that value is mapped back to the function it designates. Mismatches
    /// (calling through a non-function pointer, or a pointer that does not name
    /// a function) yield typed errors rather than silent acceptance.
    fn resolve_callee(&mut self, func: &CExpr) -> UBResult<Ident> {
        // Fast path: a bare function name that is not shadowed by a variable.
        if let CExpr::Var(name) = func {
            if self.state.lookup_var(name).is_none() && self.state.functions.contains_key(name) {
                return Ok(name.clone());
            }
        }

        // Indirect call: the callee must be (a pointer to) a function type.
        let callee_ty = self.infer_type(func)?;
        let stripped_ty = callee_ty.unqualified();
        let is_callable = match stripped_ty {
            CType::Function { .. } => true,
            CType::Pointer(inner) => matches!(inner.unqualified(), CType::Function { .. }),
            _ => false,
        };
        if !is_callable {
            return Err(UBKind::Other(format!(
                "call through non-function pointer (type {callee_ty:?})"
            )));
        }

        // Evaluate the underlying function-pointer value. Peeling `*`/`&`
        // avoids loading through a `Function`-typed lvalue, which has no
        // representable value.
        let target = Self::strip_func_designators(func);
        let val = self.eval_expr_to_value(target)?;
        let ptr = match val {
            CValue::Pointer(p) => p,
            _ => {
                return Err(UBKind::Other(
                    "indirect call target is not a function pointer".to_string(),
                ))
            }
        };
        if ptr.is_null() {
            return Err(UBKind::NullDeref);
        }
        match self.state.function_at(ptr) {
            Some(name) => Ok(name.to_string()),
            None => Err(UBKind::InvalidPointer),
        }
    }

    /// Evaluate a function call
    fn eval_call(&mut self, func: &CExpr, args: &[CExpr]) -> UBResult<ExprResult> {
        // Resolve the callee to a concrete function name. A direct call names a
        // function (`add(..)`); an indirect call evaluates the callee to a
        // function-pointer value and recovers the function from it
        // (`fp(..)`, `(*fp)(..)`, `s.cb(..)`, ...).
        let func_name = self.resolve_callee(func)?;

        // Check recursion depth
        if self.state.call_stack.len() >= self.state.max_depth {
            return Err(UBKind::StackOverflow);
        }

        // Find function definition
        let func_def = self
            .state
            .functions
            .get(&func_name)
            .ok_or_else(|| UBKind::Other(format!("undefined function: {func_name}")))?
            .clone();

        // Check argument count
        if !func_def.variadic && args.len() != func_def.params.len() {
            return Err(UBKind::ArgumentCountMismatch);
        }
        if func_def.variadic && args.len() < func_def.params.len() {
            return Err(UBKind::ArgumentCountMismatch);
        }

        // Evaluate arguments
        let mut arg_vals = Vec::new();
        for arg in args {
            arg_vals.push(self.eval_expr_to_value(arg)?);
        }

        // Push stack frame
        self.state.memory.push_frame();
        let old_locals = std::mem::take(&mut self.state.current_locals);
        self.state.call_stack.push(CallFrame {
            func_name: func_name.clone(),
            return_type: func_def.return_type.clone(),
            locals: LocalEnv::new(),
            call_depth: self.state.call_stack.len(),
        });

        // Bind parameters
        for (i, param) in func_def.params.iter().enumerate() {
            let size = param.ty.size();
            let align = param.ty.align();
            let ptr = self
                .state
                .memory
                .alloc_stack(size, align, Some(param.name.clone()))?;
            self.state.store_value(ptr, &arg_vals[i], &param.ty)?;
            self.state.current_locals.bind(
                param.name.clone(),
                VarBinding {
                    ptr,
                    ty: param.ty.clone(),
                    is_const: false,
                },
            );
        }

        // Execute body
        let result = self.exec_stmt(&func_def.body);

        // Pop stack frame
        self.state.memory.pop_frame();
        self.state.call_stack.pop();
        self.state.current_locals = old_locals;

        // Handle return value
        match result? {
            ControlFlow::Return(Some(val)) => Ok(ExprResult::rvalue(val)),
            ControlFlow::Return(None) | ControlFlow::Continue => {
                if func_def.return_type == CType::Void {
                    Ok(ExprResult::rvalue(CValue::Undef))
                } else {
                    Err(UBKind::MissingReturn)
                }
            }
            _ => Err(UBKind::Other(
                "unexpected control flow from function".to_string(),
            )),
        }
    }

    /// Execute a statement
    pub fn exec_stmt(&mut self, stmt: &CStmt) -> UBResult<ControlFlow> {
        match stmt {
            CStmt::Empty => Ok(ControlFlow::Continue),

            CStmt::Expr(e) => {
                let _ = self.eval_expr_to_value(e)?;
                Ok(ControlFlow::Continue)
            }

            CStmt::Decl(decl) => {
                self.exec_decl(decl)?;
                Ok(ControlFlow::Continue)
            }

            CStmt::DeclList(decls) => {
                for decl in decls {
                    self.exec_decl(decl)?;
                }
                Ok(ControlFlow::Continue)
            }

            CStmt::Block(stmts) => {
                for stmt in stmts {
                    match self.exec_stmt(stmt)? {
                        ControlFlow::Continue => {}
                        other => return Ok(other),
                    }
                }
                Ok(ControlFlow::Continue)
            }

            CStmt::If {
                cond,
                then_stmt,
                else_stmt,
            } => {
                let cond_val = self.eval_expr_to_value(cond)?;
                if cond_val.to_bool()? {
                    self.exec_stmt(then_stmt)
                } else if let Some(else_s) = else_stmt {
                    self.exec_stmt(else_s)
                } else {
                    Ok(ControlFlow::Continue)
                }
            }

            CStmt::While { cond, body } => {
                for _ in 0..MAX_LOOP_ITERATIONS {
                    let cond_val = self.eval_expr_to_value(cond)?;
                    if !cond_val.to_bool()? {
                        return Ok(ControlFlow::Continue);
                    }
                    match self.exec_stmt(body)? {
                        ControlFlow::Continue | ControlFlow::LoopContinue => {}
                        ControlFlow::Break => return Ok(ControlFlow::Continue),
                        other => return Ok(other),
                    }
                }
                Err(UBKind::Other(
                    "maximum loop iterations exceeded".to_string(),
                ))
            }

            CStmt::DoWhile { body, cond } => {
                for _ in 0..MAX_LOOP_ITERATIONS {
                    match self.exec_stmt(body)? {
                        ControlFlow::Continue | ControlFlow::LoopContinue => {}
                        ControlFlow::Break => return Ok(ControlFlow::Continue),
                        other => return Ok(other),
                    }
                    let cond_val = self.eval_expr_to_value(cond)?;
                    if !cond_val.to_bool()? {
                        return Ok(ControlFlow::Continue);
                    }
                }
                Err(UBKind::Other(
                    "maximum loop iterations exceeded".to_string(),
                ))
            }

            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                // Execute init
                if let Some(init_stmt) = init {
                    match self.exec_stmt(init_stmt)? {
                        ControlFlow::Continue => {}
                        other => return Ok(other),
                    }
                }

                for _ in 0..MAX_LOOP_ITERATIONS {
                    // Check condition
                    if let Some(cond_expr) = cond {
                        let cond_val = self.eval_expr_to_value(cond_expr)?;
                        if !cond_val.to_bool()? {
                            return Ok(ControlFlow::Continue);
                        }
                    }

                    // Execute body
                    match self.exec_stmt(body)? {
                        ControlFlow::Continue | ControlFlow::LoopContinue => {}
                        ControlFlow::Break => return Ok(ControlFlow::Continue),
                        other => return Ok(other),
                    }

                    // Execute update
                    if let Some(update_expr) = update {
                        let _ = self.eval_expr_to_value(update_expr)?;
                    }
                }
                Err(UBKind::Other(
                    "maximum loop iterations exceeded".to_string(),
                ))
            }

            CStmt::Break => Ok(ControlFlow::Break),

            CStmt::Continue => Ok(ControlFlow::LoopContinue),

            CStmt::Return(expr) => {
                let val = if let Some(e) = expr {
                    Some(self.eval_expr_to_value(e)?)
                } else {
                    None
                };
                Ok(ControlFlow::Return(val))
            }

            CStmt::Goto(label) => Ok(ControlFlow::Goto(label.clone())),

            CStmt::Label { stmt, .. } => {
                // Just execute the statement (labels handled by goto)
                self.exec_stmt(stmt)
            }

            CStmt::Switch { cond, body } => {
                let _val = self.eval_expr_to_value(cond)?;
                // Switch execution requires special handling
                // For now, just execute body
                self.exec_stmt(body)
            }

            CStmt::Case { stmt, .. } => self.exec_stmt(stmt),

            CStmt::FuncDef(_) => {
                // Function definitions at statement level are already handled
                Ok(ControlFlow::Continue)
            }

            CStmt::Asm(_) => {
                // Inline assembly not supported
                Err(UBKind::Other("inline assembly not supported".to_string()))
            }

            CStmt::Assert(_spec) => {
                // Assertions are handled by verification, not execution
                // At runtime, we just skip them (or could check and panic)
                Ok(ControlFlow::Continue)
            }

            CStmt::Assume(_spec) => {
                // Assumptions are handled by verification, not execution
                // At runtime, we assume the spec holds
                Ok(ControlFlow::Continue)
            }

            CStmt::StaticAssert { cond, message } => {
                // C11 6.7.10: a static assertion is a compile-time constraint.
                // A well-formed translation unit can only contain assertions
                // that hold, so a holding assertion is a no-op. We still verify
                // here so a false assertion is never silently accepted.
                match check_static_assert(cond, message.as_deref()) {
                    Ok(()) => Ok(ControlFlow::Continue),
                    Err(e) => Err(UBKind::Other(e.to_string())),
                }
            }
        }
    }

    /// Execute a variable declaration
    fn exec_decl(&mut self, decl: &VarDecl) -> UBResult<()> {
        let size = decl.ty.size();
        let align = decl.ty.align();

        let ptr = match decl.storage {
            StorageClass::Static => {
                // Static locals go in global memory
                self.state.memory.alloc(size, align)?
            }
            _ => {
                // Stack allocation
                self.state
                    .memory
                    .alloc_stack(size, align, Some(decl.name.clone()))?
            }
        };

        // Initialize
        if let Some(ref init) = decl.init {
            let val = self.state.eval_initializer(init, &decl.ty)?;
            self.state.store_value(ptr, &val, &decl.ty)?;
        }

        // Bind to local scope
        self.state.current_locals.bind(
            decl.name.clone(),
            VarBinding {
                ptr,
                ty: decl.ty.clone(),
                is_const: false,
            },
        );

        Ok(())
    }

    /// Infer the type of an expression (approximate)
    fn infer_type(&self, expr: &CExpr) -> UBResult<CType> {
        match expr {
            CExpr::UIntLit(_) => Ok(CType::uint()),
            CExpr::FloatLit(_) => Ok(CType::Float(crate::types::FloatKind::Double)),
            CExpr::CharLit(_) => Ok(CType::char()),
            CExpr::StringLit(_) => Ok(CType::ptr(CType::char())),

            CExpr::Var(name) => {
                if let Some(binding) = self.state.lookup_var(name) {
                    return Ok(binding.ty.clone());
                }
                // A bare function name decays to a pointer-to-function type.
                if let Some(func_def) = self.state.functions.get(name) {
                    return Ok(CType::ptr(func_def.func_type()));
                }
                Err(UBKind::Other(format!("undefined variable: {name}")))
            }

            CExpr::BinOp { op, left, right } => {
                if op.is_comparison() || op.is_logical() {
                    Ok(CType::int())
                } else if op.is_assignment() {
                    self.infer_type(left)
                } else if op.is_shift() {
                    // C11 6.5.7p3: result type is the promoted left operand.
                    Ok(self.infer_type(left)?.integer_promotion())
                } else {
                    let lt = self.infer_type(left)?;
                    let rt = self.infer_type(right)?;
                    Ok(lt.usual_arithmetic_conversion(&rt))
                }
            }

            CExpr::UnaryOp { op, operand } => match op {
                UnaryOp::Deref => {
                    let ptr_ty = self.infer_type(operand)?;
                    ptr_ty
                        .pointee()
                        .cloned()
                        .ok_or_else(|| UBKind::Other("deref non-pointer".to_string()))
                }
                UnaryOp::AddrOf => {
                    let inner_ty = self.infer_type(operand)?;
                    Ok(CType::ptr(inner_ty))
                }
                UnaryOp::LogNot => Ok(CType::int()),
                _ => self.infer_type(operand),
            },

            CExpr::Conditional {
                then_expr,
                else_expr,
                ..
            } => {
                let then_ty = self.infer_type(then_expr)?;
                let else_ty = self.infer_type(else_expr)?;
                Ok(conditional_common_type(
                    &then_ty, then_expr, &else_ty, else_expr,
                ))
            }

            CExpr::Cast { ty, .. } | CExpr::CompoundLiteral { ty, .. } => Ok(ty.clone()),

            CExpr::SizeOf(_) | CExpr::AlignOf(_) => {
                Ok(CType::Int(IntKind::Long, Signedness::Unsigned)) // size_t
            }

            CExpr::Index { array, .. } => {
                let arr_ty = self.infer_type(array)?;
                arr_ty
                    .element()
                    .or_else(|| arr_ty.pointee())
                    .cloned()
                    .ok_or_else(|| UBKind::Other("subscript on non-array".to_string()))
            }

            CExpr::Member { object, field }
            | CExpr::Arrow {
                pointer: object,
                field,
            } => {
                let obj_ty = if matches!(expr, CExpr::Arrow { .. }) {
                    let ptr_ty = self.infer_type(object)?;
                    ptr_ty
                        .pointee()
                        .ok_or_else(|| UBKind::Other("arrow on non-pointer".to_string()))?
                        .clone()
                } else {
                    self.infer_type(object)?
                };

                obj_ty
                    .get_field(field)
                    .map(|(_, f)| f.ty.clone())
                    .ok_or_else(|| UBKind::Other(format!("no field: {field}")))
            }

            CExpr::Call { func, .. } => {
                // Direct call: take the return type from the named function.
                if let CExpr::Var(name) = func.as_ref() {
                    if self.state.lookup_var(name).is_none() {
                        if let Some(func_def) = self.state.functions.get(name) {
                            return Ok(func_def.return_type.clone());
                        }
                    }
                }
                // Indirect call: the callee's (pointer-to-)function type carries
                // the return type.
                let callee_ty = self.infer_type(func)?;
                let func_ty = match callee_ty.unqualified() {
                    f @ CType::Function { .. } => Some(f),
                    CType::Pointer(inner) => match inner.unqualified() {
                        f @ CType::Function { .. } => Some(f),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(CType::Function { return_type, .. }) = func_ty {
                    return Ok((**return_type).clone());
                }
                Ok(CType::int()) // Default
            }

            CExpr::Generic {
                control,
                associations,
            } => {
                // C11 6.5.1.1: the type of a generic selection is the type of
                // its selected result expression. Mirror the selection rule used
                // during evaluation so static typing agrees with runtime.
                let control_ty = self.infer_type(control)?;
                let control_ty = control_ty.unqualified();
                let mut selected: Option<&CExpr> = None;
                let mut default_branch: Option<&CExpr> = None;
                for (assoc_ty, result_expr) in associations {
                    match assoc_ty {
                        Some(ty) if ty.unqualified().is_compatible(control_ty) => {
                            selected = Some(result_expr);
                        }
                        None => default_branch = Some(result_expr),
                        Some(_) => {}
                    }
                }
                match selected.or(default_branch) {
                    Some(chosen) => self.infer_type(chosen),
                    None => Ok(CType::int()),
                }
            }

            // Default to int for unknown/unhandled expression types (including IntLit)
            _ => Ok(CType::int()),
        }
    }
}

/// Determine whether an expression is a null pointer constant (C11 6.3.2.3p3):
/// an integer constant expression with the value 0, or such an expression cast
/// to type `void *`.
fn is_null_pointer_constant(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(0) | CExpr::UIntLit(0) | CExpr::CharLit(0) => true,
        // A null pointer constant cast to `void *` is still a null pointer
        // constant for the purposes of the conditional operator.
        CExpr::Cast { ty, expr } => {
            matches!(ty.unqualified().pointee(), Some(CType::Void))
                && is_null_pointer_constant(expr)
        }
        _ => false,
    }
}

/// Compute the type of a conditional (ternary) expression `c ? then : else`
/// following C11 6.5.15p5-6.
///
/// The well-defined cases handled here:
/// - both operands arithmetic -> usual arithmetic conversions;
/// - both `void` -> `void`;
/// - both pointers to compatible types -> that pointer type (a `void *`
///   operand makes the result `void *`);
/// - one operand a pointer and the other a null pointer constant -> the
///   pointer type.
///
/// For any remaining shape (which would be a constraint violation in a
/// conforming program, or a type the surface does not model precisely) the
/// `then`-branch type is returned so inference never fabricates a narrower
/// type than the existing behavior.
fn conditional_common_type(
    then_ty: &CType,
    then_expr: &CExpr,
    else_ty: &CType,
    else_expr: &CExpr,
) -> CType {
    // Both arithmetic: usual arithmetic conversions (6.5.15p5).
    if then_ty.is_arithmetic() && else_ty.is_arithmetic() {
        return then_ty.usual_arithmetic_conversion(else_ty);
    }

    // Both void.
    if matches!(then_ty.unqualified(), CType::Void) && matches!(else_ty.unqualified(), CType::Void)
    {
        return CType::Void;
    }

    let then_unq = then_ty.unqualified();
    let else_unq = else_ty.unqualified();

    // Both pointer types.
    if let (Some(then_pointee), Some(else_pointee)) = (then_unq.pointee(), else_unq.pointee()) {
        // If either points to `void`, the result is `void *` (6.5.15p6).
        if matches!(then_pointee, CType::Void) || matches!(else_pointee, CType::Void) {
            return CType::ptr(CType::Void);
        }
        // Pointers to compatible types: use the (canonicalized) pointer type.
        if then_pointee.is_compatible(else_pointee) {
            return then_unq.clone();
        }
        // Incompatible pointers: keep the then-branch type rather than guess.
        return then_ty.clone();
    }

    // One operand is a pointer, the other a null pointer constant -> pointer.
    if then_unq.is_pointer() && is_null_pointer_constant(else_expr) {
        return then_unq.clone();
    }
    if else_unq.is_pointer() && is_null_pointer_constant(then_expr) {
        return else_unq.clone();
    }

    // Fallback: preserve prior behavior (then-branch type).
    then_ty.clone()
}

// Add this method to State to allow direct expression evaluation
impl State {
    /// Evaluate an expression (convenience method)
    pub fn eval_expr_to_value(&mut self, expr: &CExpr) -> UBResult<CValue> {
        Interpreter::new(self).eval_expr_to_value(expr)
    }
}

/// Evaluate a `_Static_assert` at compile time (C11 6.7.10).
///
/// The controlling constant expression is folded against an empty
/// environment (static assertions may only reference integer constant
/// expressions such as literals, `sizeof`, and `_Alignof`). The result:
///
/// - non-zero  -> `Ok(())` (the assertion holds; the statement is a no-op);
/// - zero      -> `Err(StaticAssertError::AssertionFailed { message })`;
/// - unfoldable -> `Err(StaticAssertError::NotConstant { .. })`.
///
/// This never accepts a false static assertion: a controlling expression that
/// folds to zero is always rejected.
pub fn check_static_assert(cond: &CExpr, message: Option<&str>) -> Result<(), StaticAssertError> {
    let mut state = State::new();
    let value = state
        .eval_expr_to_value(cond)
        .map_err(|e| StaticAssertError::NotConstant {
            reason: e.to_string(),
        })?;
    let truth = value
        .to_bool()
        .map_err(|e| StaticAssertError::NotConstant {
            reason: e.to_string(),
        })?;
    if truth {
        Ok(())
    } else {
        Err(StaticAssertError::AssertionFailed {
            message: message
                .map(str::to_string)
                .unwrap_or_else(|| "static assertion failed".to_string()),
        })
    }
}

impl MemoryModel for State {
    type Error = UBKind;

    fn allocate(
        &mut self,
        size: usize,
    ) -> Result<clean_kernel::sem_memory_model::Address, Self::Error> {
        let ptr = self.memory.alloc(size, 1)?;
        Ok(clean_kernel::sem_memory_model::Address::new(ptr.block.0))
    }

    fn read(
        &self,
        addr: clean_kernel::sem_memory_model::Address,
        offset: usize,
    ) -> Result<clean_kernel::sem_memory_model::MemoryValue, Self::Error> {
        let ptr = Pointer {
            block: BlockId(addr.raw()),
            offset: offset as i64,
        };
        self.memory
            .load_u8(ptr)
            .map(clean_kernel::sem_memory_model::MemoryValue::new)
    }

    fn write(
        &mut self,
        addr: clean_kernel::sem_memory_model::Address,
        offset: usize,
        value: clean_kernel::sem_memory_model::MemoryValue,
    ) -> Result<(), Self::Error> {
        let ptr = Pointer {
            block: BlockId(addr.raw()),
            offset: offset as i64,
        };
        self.memory.store_u8(ptr, value.get())
    }

    fn free(&mut self, addr: clean_kernel::sem_memory_model::Address) -> Result<(), Self::Error> {
        let ptr = Pointer {
            block: BlockId(addr.raw()),
            offset: 0,
        };
        self.memory.free(ptr)
    }

    fn is_valid(&self, addr: clean_kernel::sem_memory_model::Address) -> bool {
        let ptr = Pointer {
            block: BlockId(addr.raw()),
            offset: 0,
        };
        self.memory.is_valid(ptr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::BinOp;
    use crate::stmt::{FuncDef, FuncParam};
    use proptest::prelude::*;
    use std::collections::HashSet;

    #[test]
    fn test_eval_int_literal() {
        let mut state = State::new();
        let val = state.eval_expr_to_value(&CExpr::int(42)).unwrap();
        assert_eq!(val, CValue::Int(42));
    }

    #[test]
    fn test_eval_arithmetic() {
        let mut state = State::new();
        let expr = CExpr::add(CExpr::int(10), CExpr::int(5));
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(15));
    }

    #[test]
    fn test_eval_comparison() {
        let mut state = State::new();
        let expr = CExpr::binop(BinOp::Lt, CExpr::int(3), CExpr::int(5));
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(1)); // true
    }

    #[test]
    fn test_eval_short_circuit_and() {
        let mut state = State::new();
        // 0 && undefined -> 0 (short circuit)
        let expr = CExpr::binop(BinOp::LogAnd, CExpr::int(0), CExpr::var("undefined"));
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(0));
    }

    #[test]
    fn test_eval_short_circuit_or() {
        let mut state = State::new();
        // 1 || undefined -> 1 (short circuit)
        let expr = CExpr::binop(BinOp::LogOr, CExpr::int(1), CExpr::var("undefined"));
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(1));
    }

    #[test]
    fn test_eval_alignof_int_returns_four() {
        let mut state = State::new();
        let val = state
            .eval_expr_to_value(&CExpr::AlignOf(CType::int()))
            .unwrap();
        assert_eq!(val, CValue::UInt(4));
    }

    #[test]
    fn test_eval_alignof_char_returns_one() {
        let mut state = State::new();
        let val = state
            .eval_expr_to_value(&CExpr::AlignOf(CType::char()))
            .unwrap();
        assert_eq!(val, CValue::UInt(1));
    }

    #[test]
    fn test_eval_alignof_double_returns_eight() {
        let mut state = State::new();
        let ty = CType::Float(crate::types::FloatKind::Double);
        let val = state.eval_expr_to_value(&CExpr::AlignOf(ty)).unwrap();
        assert_eq!(val, CValue::UInt(8));
    }

    #[test]
    fn test_eval_alignof_struct_uses_max_field_alignment() {
        // struct Point { int x; int y; } has alignment max(4, 4) = 4.
        let mut state = State::new();
        let ty = CType::Struct {
            name: Some("Point".to_string()),
            fields: vec![
                crate::types::StructField::new("x", CType::int()),
                crate::types::StructField::new("y", CType::int()),
            ],
        };
        let val = state.eval_expr_to_value(&CExpr::AlignOf(ty)).unwrap();
        assert_eq!(val, CValue::UInt(4));
    }

    #[test]
    fn test_eval_alignof_incomplete_struct_returns_one() {
        // A forward-declared `struct Point` (no fields) has the model's
        // default alignment of 1.
        let mut state = State::new();
        let ty = CType::Struct {
            name: Some("Point".to_string()),
            fields: Vec::new(),
        };
        let val = state.eval_expr_to_value(&CExpr::AlignOf(ty)).unwrap();
        assert_eq!(val, CValue::UInt(1));
    }

    #[test]
    fn test_eval_comma_three_operands_yields_last_and_runs_side_effects() {
        // C11 6.5.17: a comma expression evaluates each operand for its side
        // effects and the whole expression's value is the value of the *last*
        // operand. The parser produces a left-associative chain, so we build
        // `(a = 1, b = 2, 3)` as `BinOp(Comma, BinOp(Comma, a=1, b=2), 3)` and
        // check (a) the result is the last operand `3` and (b) both earlier
        // assignment side effects ran.
        let mut state = State::new();

        // int a = 0; int b = 0;
        let setup = CStmt::block(vec![
            CStmt::decl_init("a", CType::int(), CExpr::int(0)),
            CStmt::decl_init("b", CType::int(), CExpr::int(0)),
        ]);
        Interpreter::new(&mut state).exec_stmt(&setup).unwrap();

        // (a = 1, b = 2, 3)  ==  ((a = 1, b = 2), 3)
        let inner = CExpr::binop(
            BinOp::Comma,
            CExpr::assign(CExpr::var("a"), CExpr::int(1)),
            CExpr::assign(CExpr::var("b"), CExpr::int(2)),
        );
        let chain = CExpr::binop(BinOp::Comma, inner, CExpr::int(3));

        let val = Interpreter::new(&mut state)
            .eval_expr_to_value(&chain)
            .unwrap();
        assert_eq!(val, CValue::Int(3), "comma value is the last operand");

        let a = state.lookup_var("a").unwrap();
        assert_eq!(
            state.load_value(a.ptr, &a.ty).unwrap(),
            CValue::Int(1),
            "first operand's side effect must run"
        );
        let b = state.lookup_var("b").unwrap();
        assert_eq!(
            state.load_value(b.ptr, &b.ty).unwrap(),
            CValue::Int(2),
            "middle operand's side effect must run"
        );
    }

    #[test]
    fn test_eval_comma_two_operands_yields_last() {
        // Two-operand regression: `(7, 9)` evaluates to 9.
        let mut state = State::new();
        let chain = CExpr::binop(BinOp::Comma, CExpr::int(7), CExpr::int(9));
        let val = Interpreter::new(&mut state)
            .eval_expr_to_value(&chain)
            .unwrap();
        assert_eq!(val, CValue::Int(9));
    }

    #[test]
    fn test_exec_if() {
        let mut state = State::new();

        // int x = 0; if (1) x = 10;
        let stmt = CStmt::block(vec![
            CStmt::decl_init("x", CType::int(), CExpr::int(0)),
            CStmt::if_stmt(
                CExpr::int(1),
                CStmt::expr(CExpr::assign(CExpr::var("x"), CExpr::int(10))),
            ),
        ]);

        let mut interp = Interpreter::new(&mut state);
        interp.exec_stmt(&stmt).unwrap();

        let binding = state.lookup_var("x").unwrap();
        let val = state.load_value(binding.ptr, &binding.ty).unwrap();
        assert_eq!(val, CValue::Int(10));
    }

    #[test]
    fn test_exec_while_loop() {
        let mut state = State::new();

        // int i = 0; int sum = 0; while (i < 5) { sum += i; i++; }
        let stmt = CStmt::block(vec![
            CStmt::decl_init("i", CType::int(), CExpr::int(0)),
            CStmt::decl_init("sum", CType::int(), CExpr::int(0)),
            CStmt::while_loop(
                CExpr::binop(BinOp::Lt, CExpr::var("i"), CExpr::int(5)),
                CStmt::block(vec![
                    CStmt::expr(CExpr::binop(
                        BinOp::AddAssign,
                        CExpr::var("sum"),
                        CExpr::var("i"),
                    )),
                    CStmt::expr(CExpr::unary(UnaryOp::PostInc, CExpr::var("i"))),
                ]),
            ),
        ]);

        let mut interp = Interpreter::new(&mut state);
        interp.exec_stmt(&stmt).unwrap();

        let binding = state.lookup_var("sum").unwrap();
        let val = state.load_value(binding.ptr, &binding.ty).unwrap();
        assert_eq!(val, CValue::Int(10)); // 0+1+2+3+4 = 10
    }

    #[test]
    fn test_function_call() {
        let mut state = State::new();

        // Define: int add(int a, int b) { return a + b; }
        let add_func = FuncDef::new(
            "add",
            CType::int(),
            vec![
                FuncParam::new("a", CType::int()),
                FuncParam::new("b", CType::int()),
            ],
            CStmt::return_stmt(Some(CExpr::add(CExpr::var("a"), CExpr::var("b")))),
        );

        state.functions.insert("add".to_string(), add_func);

        // Call: add(3, 4)
        let call = CExpr::call(CExpr::var("add"), vec![CExpr::int(3), CExpr::int(4)]);
        let result = state.eval_expr_to_value(&call).unwrap();
        assert_eq!(result, CValue::Int(7));
    }

    #[test]
    fn test_factorial() {
        let mut state = State::new();

        // int fact(int n) { if (n <= 1) return 1; return n * fact(n-1); }
        let fact_func = FuncDef::new(
            "fact",
            CType::int(),
            vec![FuncParam::new("n", CType::int())],
            CStmt::block(vec![
                CStmt::if_stmt(
                    CExpr::binop(BinOp::Le, CExpr::var("n"), CExpr::int(1)),
                    CStmt::return_stmt(Some(CExpr::int(1))),
                ),
                CStmt::return_stmt(Some(CExpr::mul(
                    CExpr::var("n"),
                    CExpr::call(
                        CExpr::var("fact"),
                        vec![CExpr::sub(CExpr::var("n"), CExpr::int(1))],
                    ),
                ))),
            ]),
        );

        state.functions.insert("fact".to_string(), fact_func);

        // fact(5) = 120
        let call = CExpr::call(CExpr::var("fact"), vec![CExpr::int(5)]);
        let result = state.eval_expr_to_value(&call).unwrap();
        assert_eq!(result, CValue::Int(120));
    }

    /// Register `int add(int a, int b) { return a + b; }`.
    fn register_add(state: &mut State) {
        let add_func = FuncDef::new(
            "add",
            CType::int(),
            vec![
                FuncParam::new("a", CType::int()),
                FuncParam::new("b", CType::int()),
            ],
            CStmt::return_stmt(Some(CExpr::add(CExpr::var("a"), CExpr::var("b")))),
        );
        state.functions.insert("add".to_string(), add_func);
    }

    /// Register `int inc(int x) { return x + 1; }`.
    fn register_inc(state: &mut State) {
        let inc_func = FuncDef::new(
            "inc",
            CType::int(),
            vec![FuncParam::new("x", CType::int())],
            CStmt::return_stmt(Some(CExpr::add(CExpr::var("x"), CExpr::int(1)))),
        );
        state.functions.insert("inc".to_string(), inc_func);
    }

    /// `int (*)(int)` — pointer to a function taking one int and returning int.
    fn fn_ptr_int_to_int() -> CType {
        CType::ptr(CType::Function {
            return_type: Box::new(CType::int()),
            params: vec![crate::types::FuncParam {
                name: None,
                ty: CType::int(),
            }],
            variadic: false,
        })
    }

    #[test]
    fn test_indirect_call_through_fn_ptr_var_returns_call_result() {
        let mut state = State::new();
        register_inc(&mut state);

        // int (*fp)(int) = inc; fp(5);  => 6
        let stmt = CStmt::block(vec![
            CStmt::decl_init("fp", fn_ptr_int_to_int(), CExpr::var("inc")),
            CStmt::Return(Some(CExpr::call(CExpr::var("fp"), vec![CExpr::int(5)]))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let result = interp
            .exec_stmt(&stmt)
            .expect("indirect call through fn ptr should evaluate");
        assert_eq!(result, ControlFlow::Return(Some(CValue::Int(6))));
    }

    #[test]
    fn test_indirect_call_explicit_deref_returns_call_result() {
        let mut state = State::new();
        register_inc(&mut state);

        // int (*fp)(int) = inc; (*fp)(5);  => 6
        let stmt = CStmt::block(vec![
            CStmt::decl_init("fp", fn_ptr_int_to_int(), CExpr::var("inc")),
            CStmt::Return(Some(CExpr::call(
                CExpr::deref(CExpr::var("fp")),
                vec![CExpr::int(5)],
            ))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let result = interp
            .exec_stmt(&stmt)
            .expect("explicit-deref indirect call should evaluate");
        assert_eq!(result, ControlFlow::Return(Some(CValue::Int(6))));
    }

    #[test]
    fn test_indirect_call_address_of_function_returns_call_result() {
        let mut state = State::new();
        register_inc(&mut state);

        // int (*fp)(int) = &inc; fp(41);  => 42
        let stmt = CStmt::block(vec![
            CStmt::decl_init("fp", fn_ptr_int_to_int(), CExpr::addr_of(CExpr::var("inc"))),
            CStmt::Return(Some(CExpr::call(CExpr::var("fp"), vec![CExpr::int(41)]))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let result = interp
            .exec_stmt(&stmt)
            .expect("&function indirect call should evaluate");
        assert_eq!(result, ControlFlow::Return(Some(CValue::Int(42))));
    }

    #[test]
    fn test_indirect_call_fn_ptr_passed_as_argument_returns_call_result() {
        let mut state = State::new();
        register_inc(&mut state);

        // int apply(int (*f)(int), int x) { return f(x); }
        let apply_func = FuncDef::new(
            "apply",
            CType::int(),
            vec![
                FuncParam::new("f", fn_ptr_int_to_int()),
                FuncParam::new("x", CType::int()),
            ],
            CStmt::return_stmt(Some(CExpr::call(CExpr::var("f"), vec![CExpr::var("x")]))),
        );
        state.functions.insert("apply".to_string(), apply_func);

        // apply(inc, 9) => 10  (inc decays to a function pointer argument)
        let call = CExpr::call(CExpr::var("apply"), vec![CExpr::var("inc"), CExpr::int(9)]);
        let result = state
            .eval_expr_to_value(&call)
            .expect("fn-ptr passed as argument and called should evaluate");
        assert_eq!(result, CValue::Int(10));
    }

    #[test]
    fn test_indirect_call_wrong_arity_errors() {
        let mut state = State::new();
        register_inc(&mut state);

        // int (*fp)(int) = inc; fp(1, 2);  => arity mismatch (inc takes 1 arg)
        let stmt = CStmt::block(vec![
            CStmt::decl_init("fp", fn_ptr_int_to_int(), CExpr::var("inc")),
            CStmt::Return(Some(CExpr::call(
                CExpr::var("fp"),
                vec![CExpr::int(1), CExpr::int(2)],
            ))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let err = interp
            .exec_stmt(&stmt)
            .expect_err("calling a 1-arg function with 2 args must error");
        assert_eq!(err, UBKind::ArgumentCountMismatch);
    }

    #[test]
    fn test_indirect_call_through_non_function_pointer_errors() {
        let mut state = State::new();

        // int n = 7; n(1);  => calling through a non-function pointer
        let stmt = CStmt::block(vec![
            CStmt::decl_init("n", CType::int(), CExpr::int(7)),
            CStmt::Return(Some(CExpr::call(CExpr::var("n"), vec![CExpr::int(1)]))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let err = interp
            .exec_stmt(&stmt)
            .expect_err("calling through a non-function pointer must error");
        match err {
            UBKind::Other(msg) => {
                assert!(
                    msg.contains("non-function pointer"),
                    "expected non-function-pointer error, got: {msg}"
                );
            }
            other => panic!("expected UBKind::Other, got {other:?}"),
        }
    }

    #[test]
    fn test_indirect_call_through_struct_field_returns_call_result() {
        let mut state = State::new();
        register_inc(&mut state);

        // struct { int (*cb)(int); } s; s.cb = inc; s.cb(7);  => 8
        let struct_ty = CType::Struct {
            name: Some("Ops".to_string()),
            fields: vec![crate::types::StructField::new("cb", fn_ptr_int_to_int())],
        };
        let stmt = CStmt::block(vec![
            CStmt::decl("s", struct_ty),
            CStmt::expr(CExpr::assign(
                CExpr::member(CExpr::var("s"), "cb"),
                CExpr::var("inc"),
            )),
            CStmt::Return(Some(CExpr::call(
                CExpr::member(CExpr::var("s"), "cb"),
                vec![CExpr::int(7)],
            ))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let result = interp
            .exec_stmt(&stmt)
            .expect("call through struct fn-ptr field should evaluate");
        assert_eq!(result, ControlFlow::Return(Some(CValue::Int(8))));
    }

    #[test]
    fn test_indirect_call_through_null_fn_ptr_errors() {
        let mut state = State::new();

        // int (*fp)(int) = 0; fp(5);  => null function pointer call
        let null_ptr = CExpr::Cast {
            ty: fn_ptr_int_to_int(),
            expr: Box::new(CExpr::int(0)),
        };
        let stmt = CStmt::block(vec![
            CStmt::decl_init("fp", fn_ptr_int_to_int(), null_ptr),
            CStmt::Return(Some(CExpr::call(CExpr::var("fp"), vec![CExpr::int(5)]))),
        ]);

        let mut interp = Interpreter::new(&mut state);
        let err = interp
            .exec_stmt(&stmt)
            .expect_err("calling a null function pointer must error");
        assert_eq!(err, UBKind::NullDeref);
    }

    #[test]
    fn test_function_name_decays_to_distinct_pointer_value() {
        let mut state = State::new();
        register_add(&mut state);
        register_inc(&mut state);

        // &add == &add (stable), &add != &inc (distinct functions).
        let add_ptr = state
            .eval_expr_to_value(&CExpr::var("add"))
            .expect("function name decays to pointer");
        let add_ptr2 = state
            .eval_expr_to_value(&CExpr::var("add"))
            .expect("function name decays to pointer");
        let inc_ptr = state
            .eval_expr_to_value(&CExpr::var("inc"))
            .expect("function name decays to pointer");

        assert_eq!(add_ptr, add_ptr2, "same function => same address");
        assert_ne!(add_ptr, inc_ptr, "distinct functions => distinct addresses");
        assert!(matches!(add_ptr, CValue::Pointer(p) if !p.is_null()));
    }

    #[test]
    fn test_sizeof() {
        let mut state = State::new();

        let expr = CExpr::SizeOf(SizeOfArg::Type(CType::int()));
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::UInt(4));
    }

    #[test]
    fn test_sizeof_incomplete_array_type_errors() {
        // C99 6.5.3.4p1: sizeof applied to an incomplete type (a bare flexible
        // array member type `int[]`) is a constraint violation.
        let mut state = State::new();
        let expr = CExpr::SizeOf(SizeOfArg::Type(CType::incomplete_array(CType::int())));
        let err = state
            .eval_expr_to_value(&expr)
            .expect_err("sizeof of an incomplete array type must error");
        assert!(
            matches!(err, UBKind::Other(ref m) if m.contains("incomplete array")),
            "expected an incomplete-array sizeof error, got {err:?}"
        );
    }

    #[test]
    fn test_sizeof_void_type_errors() {
        // C11 6.5.3.4p1: `void` is an incomplete type, so sizeof(void) is a
        // constraint violation rather than 0.
        let mut state = State::new();
        let expr = CExpr::SizeOf(SizeOfArg::Type(CType::void()));
        let err = state
            .eval_expr_to_value(&expr)
            .expect_err("sizeof of void must error");
        assert!(
            matches!(err, UBKind::Other(ref m) if m.contains("incomplete type")),
            "expected an incomplete-type sizeof error, got {err:?}"
        );
    }

    #[test]
    fn test_sizeof_forward_declared_struct_errors() {
        // C11 6.5.3.4p1: a forward-declared struct (`struct S;`, modeled as a
        // fieldless struct) is incomplete, so sizeof on it is a constraint
        // violation rather than silently returning 0.
        let mut state = State::new();
        let incomplete = CType::Struct {
            name: Some("S".to_string()),
            fields: Vec::new(),
        };
        let expr = CExpr::SizeOf(SizeOfArg::Type(incomplete));
        let err = state
            .eval_expr_to_value(&expr)
            .expect_err("sizeof of a forward-declared struct must error");
        assert!(
            matches!(err, UBKind::Other(ref m) if m.contains("incomplete type")),
            "expected an incomplete-type sizeof error, got {err:?}"
        );
    }

    #[test]
    fn test_sizeof_forward_declared_union_errors() {
        // A fieldless union models a forward-declared union (`union U;`), which
        // is incomplete: sizeof must error, not return 0.
        let mut state = State::new();
        let incomplete = CType::Union {
            name: Some("U".to_string()),
            fields: Vec::new(),
        };
        let expr = CExpr::SizeOf(SizeOfArg::Type(incomplete));
        let err = state
            .eval_expr_to_value(&expr)
            .expect_err("sizeof of a forward-declared union must error");
        assert!(
            matches!(err, UBKind::Other(ref m) if m.contains("incomplete type")),
            "expected an incomplete-type sizeof error, got {err:?}"
        );
    }

    #[test]
    fn test_sizeof_complete_struct_succeeds() {
        // A fully-defined struct has a well-defined size: struct { int a, b; }
        // is two ints == 8 bytes.
        let mut state = State::new();
        let complete = CType::Struct {
            name: Some("Pair".to_string()),
            fields: vec![
                crate::types::StructField::new("a", CType::int()),
                crate::types::StructField::new("b", CType::int()),
            ],
        };
        let val = state
            .eval_expr_to_value(&CExpr::SizeOf(SizeOfArg::Type(complete)))
            .expect("sizeof of a complete struct is well-defined");
        assert_eq!(val, CValue::UInt(8));
    }

    #[test]
    fn test_sizeof_fixed_array_type_succeeds() {
        // sizeof(int[3]) is a complete type: 3 * sizeof(int) == 12.
        let mut state = State::new();
        let arr = CType::array(CType::int(), 3);
        let val = state
            .eval_expr_to_value(&CExpr::SizeOf(SizeOfArg::Type(arr)))
            .expect("sizeof of a fixed-size array is well-defined");
        assert_eq!(val, CValue::UInt(12));
    }

    #[test]
    fn test_struct_with_flexible_array_member_sizeof_omits_fam() {
        // sizeof of a struct that has a flexible array member counts only the
        // fixed members (the FAM contributes 0): struct { int x; int arr[]; }.
        let mut state = State::new();
        let struct_ty = CType::Struct {
            name: Some("S".to_string()),
            fields: vec![
                crate::types::StructField::new("x", CType::int()),
                crate::types::StructField::new("arr", CType::incomplete_array(CType::int())),
            ],
        };
        let expr = CExpr::SizeOf(SizeOfArg::Type(struct_ty));
        let val = state
            .eval_expr_to_value(&expr)
            .expect("sizeof of a struct with a FAM is well-defined");
        assert_eq!(val, CValue::UInt(4));
    }

    // ---- C11 6.5.1.1 generic selection (_Generic) ----

    /// `_Generic(<int>, int: 1, double: 2)` selects the `int` branch -> 1.
    #[test]
    fn test_generic_selection_int_controlling_picks_int_branch() {
        let mut state = State::new();
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::int(),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![
                (Some(CType::int()), CExpr::int(1)),
                (
                    Some(CType::Float(crate::types::FloatKind::Double)),
                    CExpr::int(2),
                ),
            ],
        };
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(1));
    }

    /// `_Generic(<double>, int: 1, double: 2)` selects the `double` branch -> 2.
    #[test]
    fn test_generic_selection_double_controlling_picks_double_branch() {
        let mut state = State::new();
        let dbl = CType::Float(crate::types::FloatKind::Double);
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: dbl.clone(),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![
                (Some(CType::int()), CExpr::int(1)),
                (Some(dbl), CExpr::int(2)),
            ],
        };
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(2));
    }

    /// No association matches the controlling type, so the `default` branch wins.
    #[test]
    fn test_generic_selection_no_match_falls_to_default() {
        let mut state = State::new();
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::ptr(CType::char()),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![
                (Some(CType::int()), CExpr::int(1)),
                (None, CExpr::int(99)), // default
            ],
        };
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(99));
    }

    /// Top-level qualifiers on the controlling type are dropped before matching
    /// (lvalue conversion): `const int` matches an `int` association.
    #[test]
    fn test_generic_selection_drops_controlling_qualifiers() {
        let mut state = State::new();
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::const_ty(CType::int()),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![(Some(CType::int()), CExpr::int(7))],
        };
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(7));
    }

    /// The controlling expression is not evaluated; only its type matters.
    /// Here the control divides by zero but is never executed, while the
    /// selected branch is a plain literal.
    #[test]
    fn test_generic_selection_controlling_expr_not_evaluated() {
        let mut state = State::new();
        let div_by_zero = CExpr::div(CExpr::int(1), CExpr::int(0));
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::int(),
                expr: Box::new(div_by_zero),
            }),
            associations: vec![(Some(CType::int()), CExpr::int(42))],
        };
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(42));
    }

    /// No matching association and no default is a constraint violation -> error.
    #[test]
    fn test_generic_selection_no_match_no_default_errors() {
        let mut state = State::new();
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::ptr(CType::char()),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![(Some(CType::int()), CExpr::int(1))],
        };
        assert!(state.eval_expr_to_value(&expr).is_err());
    }

    /// A controlling type compatible with two associations is ambiguous -> error.
    #[test]
    fn test_generic_selection_ambiguous_match_errors() {
        let mut state = State::new();
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::int(),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![
                (Some(CType::int()), CExpr::int(1)),
                (Some(CType::int()), CExpr::int(2)),
            ],
        };
        assert!(state.eval_expr_to_value(&expr).is_err());
    }

    /// The selected branch is what is actually executed: side effects in
    /// unselected branches do not occur, and the selected result is returned.
    #[test]
    fn test_generic_selection_evaluates_only_selected_branch() {
        let mut state = State::new();
        // _Generic(<int>, int: 5 + 6, double: <unused>) -> 11
        let expr = CExpr::Generic {
            control: Box::new(CExpr::Cast {
                ty: CType::int(),
                expr: Box::new(CExpr::int(0)),
            }),
            associations: vec![
                (Some(CType::int()), CExpr::add(CExpr::int(5), CExpr::int(6))),
                (
                    Some(CType::Float(crate::types::FloatKind::Double)),
                    CExpr::div(CExpr::int(1), CExpr::int(0)),
                ),
            ],
        };
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(11));
    }

    #[test]
    fn test_pointer_arithmetic_in_expr() {
        let mut state = State::new();

        // Allocate array (10 ints)
        let array_ptr = state.memory.alloc(40, 4).unwrap();

        // Store values 0..9 in the array
        for i in 0..10 {
            let elem_ptr = array_ptr.offset((i * 4) as i64).unwrap();
            state.memory.store_i32(elem_ptr, i).unwrap();
        }

        // Allocate storage for the pointer variable 'arr'
        // Pointer storage is 8 bytes (4 for block_id + 4 for offset)
        let var_ptr = state.memory.alloc(8, 8).unwrap();
        // Store the array pointer value into 'arr'
        state.memory.store_ptr(var_ptr, array_ptr).unwrap();

        // Bind 'arr' as a pointer variable
        state.globals.bind(
            "arr".to_string(),
            VarBinding {
                ptr: var_ptr, // This is where 'arr' is stored
                ty: CType::ptr(CType::int()),
                is_const: false,
            },
        );

        // arr[5] should be 5
        let expr = CExpr::index(CExpr::var("arr"), CExpr::int(5));
        let val = state.eval_expr_to_value(&expr).unwrap();
        assert_eq!(val, CValue::Int(5));
    }

    #[test]
    fn test_division_by_zero_detection() {
        let mut state = State::new();

        let expr = CExpr::div(CExpr::int(10), CExpr::int(0));
        let result = state.eval_expr_to_value(&expr);
        assert!(matches!(result, Err(UBKind::DivisionByZero)));
    }

    #[test]
    fn test_break_statement() {
        let mut state = State::new();

        // int i = 0; while (1) { if (i == 5) break; i++; }
        let stmt = CStmt::block(vec![
            CStmt::decl_init("i", CType::int(), CExpr::int(0)),
            CStmt::while_loop(
                CExpr::int(1),
                CStmt::block(vec![
                    CStmt::if_stmt(
                        CExpr::binop(BinOp::Eq, CExpr::var("i"), CExpr::int(5)),
                        CStmt::break_stmt(),
                    ),
                    CStmt::expr(CExpr::unary(UnaryOp::PostInc, CExpr::var("i"))),
                ]),
            ),
        ]);

        let mut interp = Interpreter::new(&mut state);
        interp.exec_stmt(&stmt).unwrap();

        let binding = state.lookup_var("i").unwrap();
        let val = state.load_value(binding.ptr, &binding.ty).unwrap();
        assert_eq!(val, CValue::Int(5));
    }

    #[test]
    fn test_while_loop_iteration_limit() {
        let mut state = State::new();
        // while (1) {} — infinite loop should hit iteration limit
        let stmt = CStmt::while_loop(CExpr::int(1), CStmt::block(vec![]));
        let mut interp = Interpreter::new(&mut state);
        let result = interp.exec_stmt(&stmt);
        assert!(
            matches!(&result, Err(UBKind::Other(msg)) if msg.contains("loop iterations")),
            "infinite while loop should return iteration limit error, got: {result:?}"
        );
    }

    #[test]
    fn test_do_while_loop_iteration_limit() {
        let mut state = State::new();
        // do {} while (1); — infinite do-while should hit iteration limit
        let stmt = CStmt::do_while(CStmt::block(vec![]), CExpr::int(1));
        let mut interp = Interpreter::new(&mut state);
        let result = interp.exec_stmt(&stmt);
        assert!(
            matches!(&result, Err(UBKind::Other(msg)) if msg.contains("loop iterations")),
            "infinite do-while loop should return iteration limit error, got: {result:?}"
        );
    }

    #[test]
    fn test_for_loop_iteration_limit() {
        let mut state = State::new();
        // for (;;) {} — infinite for loop should hit iteration limit
        let stmt = CStmt::for_loop(None, None, None, CStmt::block(vec![]));
        let mut interp = Interpreter::new(&mut state);
        let result = interp.exec_stmt(&stmt);
        assert!(
            matches!(&result, Err(UBKind::Other(msg)) if msg.contains("loop iterations")),
            "infinite for loop should return iteration limit error, got: {result:?}"
        );
    }

    #[test]
    fn test_finite_loop_completes_normally() {
        let mut state = State::new();
        // int i = 0; while (i < 10) { i++; }  — finite loop should complete
        let stmt = CStmt::block(vec![
            CStmt::decl_init("i", CType::int(), CExpr::int(0)),
            CStmt::while_loop(
                CExpr::binop(BinOp::Lt, CExpr::var("i"), CExpr::int(10)),
                CStmt::expr(CExpr::unary(UnaryOp::PostInc, CExpr::var("i"))),
            ),
        ]);
        let mut interp = Interpreter::new(&mut state);
        let result = interp.exec_stmt(&stmt);
        assert!(result.is_ok(), "finite loop should complete normally");
        let binding = state.lookup_var("i").unwrap();
        let val = state.load_value(binding.ptr, &binding.ty).unwrap();
        assert_eq!(val, CValue::Int(10));
    }

    // ---- Shift operators (C11 6.5.7p3) ----
    //
    // Shift operators do NOT undergo the usual arithmetic conversions. Each
    // operand is integer-promoted independently and the result type -- which
    // determines both the shift-amount UB check and the truncation width -- is
    // that of the promoted LEFT operand only. The right operand's rank is
    // irrelevant to the result type.

    /// `(unsigned int)1 << (long)40`: the left operand promotes to a 32-bit
    /// `unsigned int`, so a shift count of 40 (>= 32) is undefined behavior.
    /// The wide `long` right operand must NOT widen the result type and mask
    /// the UB. This is the soundness-critical case: previously the engine used
    /// the usual arithmetic conversion (`long`, 64-bit) and silently accepted
    /// the out-of-range shift.
    #[test]
    fn test_shl_left_promoted_type_governs_shift_bound_ub() {
        let mut state = State::new();
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        let expr = CExpr::binop(
            BinOp::Shl,
            CExpr::cast(CType::uint(), CExpr::int(1)),
            CExpr::cast(long_ty, CExpr::int(40)),
        );
        let result = state.eval_expr_to_value(&expr);
        assert!(
            matches!(result, Err(UBKind::InvalidShift(_))),
            "shift of 40 on a 32-bit unsigned int must be UB, got: {result:?}"
        );
    }

    /// `(unsigned int)1 << (long)31`: a shift count of 31 is in range for a
    /// 32-bit operand and must succeed (boundary just below the width).
    #[test]
    fn test_shl_in_range_for_promoted_left_type_succeeds() {
        let mut state = State::new();
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        let expr = CExpr::binop(
            BinOp::Shl,
            CExpr::cast(CType::uint(), CExpr::int(1)),
            CExpr::cast(long_ty, CExpr::int(31)),
        );
        let result = state
            .eval_expr_to_value(&expr)
            .expect("31-bit shift is in range");
        assert_eq!(result, CValue::UInt(1u128 << 31));
    }

    /// `(unsigned int)0xFFFFFFFF << (long)4`: the result is truncated to the
    /// 32-bit `unsigned int` width of the promoted left operand, NOT to the
    /// 64-bit `long` that the usual arithmetic conversion would have produced.
    /// 0xFFFFFFFF << 4 = 0xFFFFFFFF0, truncated to 32 bits = 0xFFFFFFF0.
    #[test]
    fn test_shl_truncates_to_promoted_left_width_not_common_type() {
        let mut state = State::new();
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        let expr = CExpr::binop(
            BinOp::Shl,
            CExpr::cast(CType::uint(), CExpr::uint(0xFFFF_FFFF)),
            CExpr::cast(long_ty, CExpr::int(4)),
        );
        let result = state
            .eval_expr_to_value(&expr)
            .expect("4-bit shift is in range");
        assert_eq!(result, CValue::UInt(0xFFFF_FFF0));
    }

    /// `(unsigned char)0xFF << 8`: an `unsigned char` operand promotes to a
    /// 32-bit `int`, so the result is the full 0xFF00 with no narrowing back
    /// to 8 bits (which would yield 0). Confirms the left operand is promoted
    /// before the shift, per integer-promotion rules.
    #[test]
    fn test_shl_unsigned_char_promotes_before_shift() {
        let mut state = State::new();
        let expr = CExpr::binop(
            BinOp::Shl,
            CExpr::cast(CType::unsigned_char(), CExpr::int(0xFF)),
            CExpr::int(8),
        );
        let result = state
            .eval_expr_to_value(&expr)
            .expect("shift of promoted char");
        // 0xFF promotes to a 32-bit value before shifting, so the full 0xFF00
        // is retained (an 8-bit `unsigned char` result type would yield 0).
        // The operand was unsigned, so the engine keeps an unsigned value.
        assert_eq!(result, CValue::UInt(0xFF00));
    }

    /// Right shift mirrors left shift: the promoted left operand's width
    /// governs the shift-amount bound, so `(unsigned int)x >> (long)40` is UB.
    #[test]
    fn test_shr_left_promoted_type_governs_shift_bound_ub() {
        let mut state = State::new();
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        let expr = CExpr::binop(
            BinOp::Shr,
            CExpr::cast(CType::uint(), CExpr::uint(0xFFFF_FFFF)),
            CExpr::cast(long_ty, CExpr::int(40)),
        );
        let result = state.eval_expr_to_value(&expr);
        assert!(
            matches!(result, Err(UBKind::InvalidShift(_))),
            "shift of 40 on a 32-bit unsigned int must be UB, got: {result:?}"
        );
    }

    /// The static type inferred for a shift expression is the promoted type of
    /// the LEFT operand, independent of the right operand's (wider) type.
    #[test]
    fn test_infer_type_shift_result_is_promoted_left_operand() {
        let mut state = State::new();
        let long_ty = CType::Int(IntKind::Long, Signedness::Signed);
        let expr = CExpr::binop(
            BinOp::Shl,
            CExpr::cast(CType::uint(), CExpr::int(1)),
            CExpr::cast(long_ty, CExpr::int(3)),
        );
        let interp = Interpreter::new(&mut state);
        let ty = interp.infer_type(&expr).expect("infer shift type");
        assert_eq!(ty, CType::uint());
    }

    /// C11 6.5.15p5: when both branches of `?:` are arithmetic, the result
    /// type is the usual-arithmetic-conversions common type. Here `int : double`
    /// must yield `double`, NOT the then-branch's `int`.
    #[test]
    fn test_infer_type_conditional_arithmetic_promotes_to_double() {
        let mut state = State::new();
        let expr = CExpr::conditional(CExpr::int(1), CExpr::int(2), CExpr::float(3.0));
        let interp = Interpreter::new(&mut state);
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::Float(crate::types::FloatKind::Double));
    }

    /// The common type is symmetric: `double : int` is also `double`.
    #[test]
    fn test_infer_type_conditional_arithmetic_symmetric() {
        let mut state = State::new();
        let expr = CExpr::conditional(CExpr::int(0), CExpr::float(3.0), CExpr::int(2));
        let interp = Interpreter::new(&mut state);
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::Float(crate::types::FloatKind::Double));
    }

    /// Integer branches follow the usual arithmetic conversions: `int : unsigned`
    /// yields `unsigned int`, not plain `int`.
    #[test]
    fn test_infer_type_conditional_int_unsigned_is_unsigned() {
        let mut state = State::new();
        let expr = CExpr::conditional(CExpr::int(1), CExpr::int(2), CExpr::uint(3));
        let interp = Interpreter::new(&mut state);
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::uint());
    }

    /// `sizeof(cond ? int : double)` is observably wrong if the conditional
    /// reports `int`: it must be `sizeof(double) == 8`.
    #[test]
    fn test_sizeof_conditional_arithmetic_uses_common_type() {
        let mut state = State::new();
        let cond = CExpr::conditional(CExpr::int(1), CExpr::int(2), CExpr::float(3.0));
        let expr = CExpr::SizeOf(SizeOfArg::Expr(Box::new(cond)));
        let val = state.eval_expr_to_value(&expr).expect("eval sizeof");
        assert_eq!(val, CValue::UInt(8));
    }

    /// Both branches the same scalar type: the type is preserved (no spurious
    /// widening). `int : int` stays `int`.
    #[test]
    fn test_infer_type_conditional_same_type_preserved() {
        let mut state = State::new();
        let expr = CExpr::conditional(CExpr::int(1), CExpr::int(2), CExpr::int(3));
        let interp = Interpreter::new(&mut state);
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::int());
    }

    /// C11 6.5.15p6: a pointer branch and a null-pointer-constant branch yield
    /// the pointer type, in either operand position.
    #[test]
    fn test_infer_type_conditional_pointer_and_null_constant() {
        let mut state = State::new();
        // Declare `int *p;` so the pointer branch infers a real pointer type.
        let mut interp = Interpreter::new(&mut state);
        interp
            .exec_stmt(&CStmt::decl("p", CType::ptr(CType::int())))
            .expect("declare pointer");

        // p ? p : 0  -> int*
        let expr = CExpr::conditional(CExpr::var("p"), CExpr::var("p"), CExpr::int(0));
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::ptr(CType::int()));

        // p ? 0 : p  -> int* (null constant in then position)
        let expr = CExpr::conditional(CExpr::var("p"), CExpr::int(0), CExpr::var("p"));
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::ptr(CType::int()));
    }

    /// C11 6.5.15p6: if one operand is `void *`, the result pointer type is
    /// `void *`.
    #[test]
    fn test_infer_type_conditional_void_pointer_wins() {
        let mut state = State::new();
        let mut interp = Interpreter::new(&mut state);
        interp
            .exec_stmt(&CStmt::decl("p", CType::ptr(CType::int())))
            .expect("declare int pointer");
        interp
            .exec_stmt(&CStmt::decl("q", CType::ptr(CType::Void)))
            .expect("declare void pointer");

        let expr = CExpr::conditional(CExpr::int(1), CExpr::var("p"), CExpr::var("q"));
        let ty = interp.infer_type(&expr).expect("infer conditional type");
        assert_eq!(ty, CType::ptr(CType::Void));
    }

    /// A bare integer constant 0 is a null pointer constant; a non-zero
    /// integer or a non-constant expression is not.
    #[test]
    fn test_is_null_pointer_constant_recognizes_zero_only() {
        assert!(is_null_pointer_constant(&CExpr::int(0)));
        assert!(is_null_pointer_constant(&CExpr::uint(0)));
        assert!(is_null_pointer_constant(&CExpr::CharLit(0)));
        // (void *)0 is also a null pointer constant.
        assert!(is_null_pointer_constant(&CExpr::cast(
            CType::ptr(CType::Void),
            CExpr::int(0)
        )));
        // Non-zero and non-constant are not null pointer constants.
        assert!(!is_null_pointer_constant(&CExpr::int(1)));
        assert!(!is_null_pointer_constant(&CExpr::var("x")));
        // (int *)0 is a pointer value but NOT a null pointer constant per
        // 6.3.2.3p3 (only void* cast qualifies for the constant form).
        assert!(!is_null_pointer_constant(&CExpr::cast(
            CType::ptr(CType::int()),
            CExpr::int(0)
        )));
    }

    /// Build a simple enumeration type for tests.
    fn test_enum() -> CType {
        CType::Enum {
            name: Some("E".to_string()),
            variants: vec![("LO".to_string(), 0), ("HI".to_string(), 1)],
        }
    }

    /// Declare an enum-typed variable and seed it with a concrete int value.
    fn declare_enum_var(interp: &mut Interpreter, name: &str, value: i128) {
        interp
            .exec_stmt(&CStmt::decl(name, test_enum()))
            .expect("declare enum var");
        let binding = interp
            .state
            .lookup_var(name)
            .expect("enum var binding")
            .clone();
        interp
            .state
            .store_value(binding.ptr, &CValue::Int(value), &binding.ty)
            .expect("seed enum var");
    }

    /// C11 6.3.1.1p2: an enum operand promotes to its underlying integer type
    /// (int here), so `infer_type` of an enum-involving arithmetic expression
    /// must report `int`, never the raw enum type.
    #[test]
    fn test_infer_type_enum_arithmetic_is_int() {
        let mut state = State::new();
        let mut interp = Interpreter::new(&mut state);
        declare_enum_var(&mut interp, "e", 1);

        // e + 1
        let expr = CExpr::add(CExpr::var("e"), CExpr::int(1));
        let ty = interp
            .infer_type(&expr)
            .expect("infer enum arithmetic type");
        assert_eq!(ty, CType::int());

        // e + e
        let expr = CExpr::add(CExpr::var("e"), CExpr::var("e"));
        let ty = interp.infer_type(&expr).expect("infer enum+enum type");
        assert_eq!(ty, CType::int());
    }

    /// `sizeof(e + 1)` is observably wrong unless the enum promotes to int:
    /// the result must be `sizeof(int) == 4`, proving the expression type is
    /// the promoted `int`, not the enum type.
    #[test]
    fn test_sizeof_enum_arithmetic_is_int_sized() {
        let mut state = State::new();
        {
            let mut interp = Interpreter::new(&mut state);
            declare_enum_var(&mut interp, "e", 1);
        }
        let expr = CExpr::SizeOf(SizeOfArg::Expr(Box::new(CExpr::add(
            CExpr::var("e"),
            CExpr::int(1),
        ))));
        let val = state.eval_expr_to_value(&expr).expect("eval sizeof");
        assert_eq!(val, CValue::UInt(4));
    }

    /// Soundness: arithmetic that overflows the promoted `int` result type must
    /// be flagged as signed-overflow UB. Before enum promotion, the result type
    /// fell through as the raw enum type, which skipped the signed-overflow
    /// check and silently wrapped — accepting undefined behavior.
    #[test]
    fn test_enum_arithmetic_signed_overflow_is_ub() {
        let mut state = State::new();
        let mut interp = Interpreter::new(&mut state);
        declare_enum_var(&mut interp, "e", i128::from(i32::MAX));

        // e + 1 overflows INT_MAX -> signed overflow is UB.
        let expr = CExpr::add(CExpr::var("e"), CExpr::int(1));
        let result = interp.state.eval_expr_to_value(&expr);
        assert_eq!(result, Err(UBKind::SignedOverflow));
    }

    /// Enum arithmetic within range evaluates with plain int semantics.
    #[test]
    fn test_enum_subtraction_evaluates_with_int_semantics() {
        let mut state = State::new();
        let mut interp = Interpreter::new(&mut state);
        declare_enum_var(&mut interp, "a", 5);
        declare_enum_var(&mut interp, "b", 2);

        // a - b == 3 (int).
        let expr = CExpr::sub(CExpr::var("a"), CExpr::var("b"));
        let val = interp
            .state
            .eval_expr_to_value(&expr)
            .expect("eval enum subtraction");
        assert_eq!(val, CValue::Int(3));
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        #[test]
        fn prop_memory_model_write_then_read_roundtrips(
            size in 1usize..16,
            value in any::<u8>(),
        ) {
            use clean_kernel::sem_memory_model::MemoryValue;
            let mut state = State::new();
            let addr = state
                .allocate(size)
                .expect("shared memory allocation should succeed");

            state
                .write(addr, 0, MemoryValue::new(value))
                .expect("write to fresh shared memory allocation should succeed");

            prop_assert_eq!(
                state.read(addr, 0).expect("read after write should succeed"),
                MemoryValue::new(value)
            );
        }

        #[test]
        fn prop_memory_model_allocate_returns_unique_addresses(
            sizes in proptest::collection::vec(1usize..16, 1..16),
        ) {
            let mut state = State::new();
            let mut seen = HashSet::new();

            for size in sizes {
                let addr = state
                    .allocate(size)
                    .expect("shared memory allocation should succeed");
                prop_assert!(seen.insert(addr));
            }
        }

        #[test]
        fn prop_memory_model_free_then_read_errors(
            size in 1usize..16,
            value in any::<u8>(),
        ) {
            use clean_kernel::sem_memory_model::MemoryValue;
            let mut state = State::new();
            let addr = state
                .allocate(size)
                .expect("shared memory allocation should succeed");

            state
                .write(addr, 0, MemoryValue::new(value))
                .expect("write to fresh shared memory allocation should succeed");
            state
                .free(addr)
                .expect("free of live shared memory allocation should succeed");

            prop_assert!(!state.is_valid(addr));
            prop_assert!(state.read(addr, 0).is_err());
        }
    }

    // ------------------------------------------------------------------
    // Designated initializer tests (C99 6.7.8)
    // ------------------------------------------------------------------

    use crate::expr::Designator;
    use crate::types::StructField;

    fn struct_field(name: &str, ty: CType) -> StructField {
        StructField::new(name, ty)
    }

    /// struct P { int x; int y; int z; }
    fn struct_pxyz() -> CType {
        CType::Struct {
            name: Some("P".to_string()),
            fields: vec![
                struct_field("x", CType::int()),
                struct_field("y", CType::int()),
                struct_field("z", CType::int()),
            ],
        }
    }

    fn field_init(name: &str, value: i64) -> Initializer {
        Initializer::Designated {
            designator: Designator::Field(name.to_string()),
            init: Box::new(Initializer::Expr(CExpr::int(value))),
        }
    }

    fn index_init(idx: i64, value: i64) -> Initializer {
        Initializer::Designated {
            designator: Designator::Index(Box::new(CExpr::int(idx))),
            init: Box::new(Initializer::Expr(CExpr::int(value))),
        }
    }

    #[test]
    fn test_eval_initializer_struct_field_designators_in_order_places_values() {
        let mut state = State::new();
        let ty = struct_pxyz();
        let init = Initializer::List(vec![
            field_init("x", 1),
            field_init("y", 2),
            field_init("z", 3),
        ]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("designated struct init should evaluate");
        assert_eq!(
            val,
            CValue::Struct(vec![CValue::Int(1), CValue::Int(2), CValue::Int(3)])
        );
    }

    #[test]
    fn test_eval_initializer_struct_field_designators_out_of_order_places_values() {
        let mut state = State::new();
        let ty = struct_pxyz();
        // { .z = 30, .x = 10 }  =>  x=10, y=0, z=30
        let init = Initializer::List(vec![field_init("z", 30), field_init("x", 10)]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("out-of-order designated struct init should evaluate");
        assert_eq!(
            val,
            CValue::Struct(vec![CValue::Int(10), CValue::Int(0), CValue::Int(30)])
        );
    }

    #[test]
    fn test_eval_initializer_struct_designator_then_positional_continues() {
        let mut state = State::new();
        let ty = struct_pxyz();
        // { .y = 20, 99 }  =>  the 99 continues at the field after y (z)
        // x=0, y=20, z=99
        let init = Initializer::List(vec![field_init("y", 20), Initializer::Expr(CExpr::int(99))]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("designator-then-positional should evaluate");
        assert_eq!(
            val,
            CValue::Struct(vec![CValue::Int(0), CValue::Int(20), CValue::Int(99)])
        );
    }

    #[test]
    fn test_eval_initializer_struct_partial_zero_fills_rest() {
        let mut state = State::new();
        let ty = struct_pxyz();
        // { .x = 7 }  =>  x=7, y=0, z=0
        let init = Initializer::List(vec![field_init("x", 7)]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("partial designated struct init should evaluate");
        assert_eq!(
            val,
            CValue::Struct(vec![CValue::Int(7), CValue::Int(0), CValue::Int(0)])
        );
    }

    #[test]
    fn test_eval_initializer_struct_unknown_field_errors() {
        let mut state = State::new();
        let ty = struct_pxyz();
        let init = Initializer::List(vec![field_init("nope", 1)]);
        let err = state
            .eval_initializer(&init, &ty)
            .expect_err("unknown field designator must error");
        match err {
            UBKind::Other(msg) => assert!(
                msg.contains("unknown struct field"),
                "expected unknown-field error, got: {msg}"
            ),
            other => panic!("expected UBKind::Other, got {other:?}"),
        }
    }

    #[test]
    fn test_eval_initializer_array_index_designators_place_values() {
        let mut state = State::new();
        // int a[5] = { [2] = 7, [4] = 9 };
        let ty = CType::Array(Box::new(CType::int()), 5);
        let init = Initializer::List(vec![index_init(2, 7), index_init(4, 9)]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("designated array init should evaluate");
        assert_eq!(
            val,
            CValue::Array(vec![
                CValue::Int(0),
                CValue::Int(0),
                CValue::Int(7),
                CValue::Int(0),
                CValue::Int(9),
            ])
        );
    }

    #[test]
    fn test_eval_initializer_array_designator_then_positional_continues() {
        let mut state = State::new();
        // int a[5] = { [1] = 5, 6, 7 };  =>  a = {0,5,6,7,0}
        let ty = CType::Array(Box::new(CType::int()), 5);
        let init = Initializer::List(vec![
            index_init(1, 5),
            Initializer::Expr(CExpr::int(6)),
            Initializer::Expr(CExpr::int(7)),
        ]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("array designator-then-positional should evaluate");
        assert_eq!(
            val,
            CValue::Array(vec![
                CValue::Int(0),
                CValue::Int(5),
                CValue::Int(6),
                CValue::Int(7),
                CValue::Int(0),
            ])
        );
    }

    #[test]
    fn test_eval_initializer_array_index_out_of_bounds_errors() {
        let mut state = State::new();
        let ty = CType::Array(Box::new(CType::int()), 3);
        let init = Initializer::List(vec![index_init(5, 1)]);
        let err = state
            .eval_initializer(&init, &ty)
            .expect_err("out-of-bounds array designator must error");
        assert_eq!(err, UBKind::OutOfBounds);
    }

    #[test]
    fn test_eval_initializer_array_negative_index_errors() {
        let mut state = State::new();
        let ty = CType::Array(Box::new(CType::int()), 3);
        let init = Initializer::List(vec![index_init(-1, 1)]);
        let err = state
            .eval_initializer(&init, &ty)
            .expect_err("negative array designator must error");
        assert_eq!(err, UBKind::OutOfBounds);
    }

    #[test]
    fn test_eval_initializer_chained_field_designator_descends_nested_struct() {
        let mut state = State::new();
        // struct Q { struct Inner { int a; int b; } inner; int tag; };
        // struct Q q = { .inner.b = 3 };  =>  inner = {a:0, b:3}, tag:0
        let inner = CType::Struct {
            name: Some("Inner".to_string()),
            fields: vec![
                struct_field("a", CType::int()),
                struct_field("b", CType::int()),
            ],
        };
        let ty = CType::Struct {
            name: Some("Q".to_string()),
            fields: vec![
                struct_field("inner", inner),
                struct_field("tag", CType::int()),
            ],
        };
        let init = Initializer::List(vec![Initializer::Designated {
            designator: Designator::Chain(vec![
                Designator::Field("inner".to_string()),
                Designator::Field("b".to_string()),
            ]),
            init: Box::new(Initializer::Expr(CExpr::int(3))),
        }]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("chained field designator should evaluate");
        assert_eq!(
            val,
            CValue::Struct(vec![
                CValue::Struct(vec![CValue::Int(0), CValue::Int(3)]),
                CValue::Int(0),
            ])
        );
    }

    #[test]
    fn test_eval_initializer_chained_index_field_descends_array_of_struct() {
        let mut state = State::new();
        // struct Pt { int x; int y; } pts[3] = { [1].y = 8 };
        let pt = CType::Struct {
            name: Some("Pt".to_string()),
            fields: vec![
                struct_field("x", CType::int()),
                struct_field("y", CType::int()),
            ],
        };
        let ty = CType::Array(Box::new(pt), 3);
        let init = Initializer::List(vec![Initializer::Designated {
            designator: Designator::Chain(vec![
                Designator::Index(Box::new(CExpr::int(1))),
                Designator::Field("y".to_string()),
            ]),
            init: Box::new(Initializer::Expr(CExpr::int(8))),
        }]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("chained index.field designator should evaluate");
        let zero_pt = CValue::Struct(vec![CValue::Int(0), CValue::Int(0)]);
        assert_eq!(
            val,
            CValue::Array(vec![
                zero_pt.clone(),
                CValue::Struct(vec![CValue::Int(0), CValue::Int(8)]),
                zero_pt,
            ])
        );
    }

    #[test]
    fn test_eval_initializer_nested_list_value_at_designated_position() {
        let mut state = State::new();
        // struct Pt { int x; int y; } pts[3] = { [2] = { 4, 5 } };
        let pt = CType::Struct {
            name: Some("Pt".to_string()),
            fields: vec![
                struct_field("x", CType::int()),
                struct_field("y", CType::int()),
            ],
        };
        let ty = CType::Array(Box::new(pt), 3);
        let init = Initializer::List(vec![Initializer::Designated {
            designator: Designator::Index(Box::new(CExpr::int(2))),
            init: Box::new(Initializer::List(vec![
                Initializer::Expr(CExpr::int(4)),
                Initializer::Expr(CExpr::int(5)),
            ])),
        }]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("nested list at designated position should evaluate");
        let zero_pt = CValue::Struct(vec![CValue::Int(0), CValue::Int(0)]);
        assert_eq!(
            val,
            CValue::Array(vec![
                zero_pt.clone(),
                zero_pt,
                CValue::Struct(vec![CValue::Int(4), CValue::Int(5)]),
            ])
        );
    }

    #[test]
    fn test_eval_initializer_later_designator_overwrites_earlier_positional() {
        let mut state = State::new();
        // int a[3] = { 1, 2, [0] = 9 };  =>  a = {9, 2, 0}
        let ty = CType::Array(Box::new(CType::int()), 3);
        let init = Initializer::List(vec![
            Initializer::Expr(CExpr::int(1)),
            Initializer::Expr(CExpr::int(2)),
            index_init(0, 9),
        ]);
        let val = state
            .eval_initializer(&init, &ty)
            .expect("later designator overwriting earlier slot should evaluate");
        assert_eq!(
            val,
            CValue::Array(vec![CValue::Int(9), CValue::Int(2), CValue::Int(0)])
        );
    }

    // ------------------------------------------------------------------
    // Compound literal tests (C99 6.5.2.5)
    // ------------------------------------------------------------------

    /// Parse `int f(void){ return <e>; }` and return the evaluated value of the
    /// single returned expression. Exercises the full parse -> eval pipeline.
    fn eval_returned_expr(src: &str) -> CValue {
        let mut parser = crate::parser::CParser::new();
        let func = parser
            .parse_function(src)
            .expect("function with a return statement should parse");
        let expr = match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Return(Some(expr))) => expr.clone(),
                other => panic!("expected a single return statement, got {other:?}"),
            },
            other => panic!("expected a block body, got {other:?}"),
        };
        let mut state = State::new();
        state
            .eval_expr_to_value(&expr)
            .expect("returned expression should evaluate")
    }

    #[test]
    fn test_eval_compound_literal_scalar_int_yields_value() {
        // End-to-end: `(int){42}` parses to a compound literal and evaluates to
        // 42 after lvalue conversion of the unnamed object.
        assert_eq!(
            eval_returned_expr("int f(void){ return (int){42}; }"),
            CValue::Int(42)
        );
    }

    #[test]
    fn test_eval_compound_literal_array_subscript_yields_element() {
        // `(int[]){10, 20, 30}[1]` evaluates to the second element, 20.
        assert_eq!(
            eval_returned_expr("int f(void){ return (int[]){10, 20, 30}[1]; }"),
            CValue::Int(20)
        );
    }

    #[test]
    fn test_eval_compound_literal_array_zero_initializes_unwritten_slots() {
        // `(int[3]){5}[2]` leaves the trailing slots zero-initialized (6.7.9p21),
        // so the third element is 0 even though only one initializer was given.
        assert_eq!(
            eval_returned_expr("int f(void){ return (int[3]){5}[2]; }"),
            CValue::Int(0)
        );
    }

    #[test]
    fn test_eval_compound_literal_struct_designated_reads_back_fields() {
        // Build `(struct P){.y = 20, .x = 10}` directly with a complete struct
        // type (the parser only sees the struct tag) and read both fields back.
        // Designators may appear out of order; positional layout is unchanged.
        let ty = CType::Struct {
            name: Some("P".to_string()),
            fields: vec![
                struct_field("x", CType::int()),
                struct_field("y", CType::int()),
            ],
        };
        let literal = CExpr::CompoundLiteral {
            ty: ty.clone(),
            init: vec![field_init("y", 20), field_init("x", 10)],
        };
        let mut state = State::new();
        let val = state
            .eval_expr_to_value(&literal)
            .expect("struct compound literal should evaluate");
        assert_eq!(val, CValue::Struct(vec![CValue::Int(10), CValue::Int(20)]));
    }

    #[test]
    fn test_eval_compound_literal_unnamed_object_is_addressable_lvalue() {
        // C99 6.5.2.5p4: a compound literal is an unnamed object, hence an
        // lvalue. `eval_expr` (not the value form) must yield an LValue with a
        // valid pointer into freshly allocated storage.
        let literal = CExpr::CompoundLiteral {
            ty: CType::int(),
            init: vec![Initializer::Expr(CExpr::int(7))],
        };
        let mut state = State::new();
        let result = Interpreter::new(&mut state)
            .eval_expr(&literal)
            .expect("compound literal should evaluate");
        match result {
            ExprResult::LValue(lv) => {
                assert_eq!(lv.ty, CType::int());
                assert_eq!(
                    state.load_value(lv.ptr, &lv.ty).unwrap(),
                    CValue::Int(7),
                    "the unnamed object holds its initializer value"
                );
            }
            ExprResult::RValue(v) => panic!("compound literal must be an lvalue, got rvalue {v:?}"),
        }
    }

    // ------------------------------------------------------------------
    // Bit-field read / write / packing (C11 6.7.2.1)
    // ------------------------------------------------------------------

    use crate::types::{IntKind, Signedness};

    /// `unsigned char` storage-unit type for compact bit-field tests.
    fn uchar() -> CType {
        CType::Int(IntKind::Char, Signedness::Unsigned)
    }

    /// `signed int` for sign-extension tests.
    fn sint() -> CType {
        CType::Int(IntKind::Int, Signedness::Signed)
    }

    /// `unsigned int` storage-unit type.
    fn bf_uint() -> CType {
        CType::Int(IntKind::Int, Signedness::Unsigned)
    }

    /// Statement: `s.<field> = <value>;`
    fn assign_field(field: &str, value: i64) -> CStmt {
        CStmt::expr(CExpr::assign(
            CExpr::member(CExpr::var("s"), field),
            CExpr::int(value),
        ))
    }

    /// Declare struct `s` of `ty` plus an `out` local of `out_ty`, run `body`,
    /// then read `s.field` into `out`; return the captured value of `out`.
    fn capture_field(ty: CType, out_ty: CType, field: &str, body: Vec<CStmt>) -> CValue {
        let mut stmts = vec![
            CStmt::decl("s", ty),
            CStmt::decl_init("out", out_ty, CExpr::int(0)),
        ];
        stmts.extend(body);
        stmts.push(CStmt::expr(CExpr::assign(
            CExpr::var("out"),
            CExpr::member(CExpr::var("s"), field),
        )));
        let block = CStmt::block(stmts);
        let mut state = State::new();
        let mut interp = Interpreter::new(&mut state);
        interp.exec_stmt(&block).expect("block should execute");
        interp
            .eval_expr_to_value(&CExpr::var("out"))
            .expect("read out")
    }

    #[test]
    fn test_bitfield_single_field_round_trips_written_value() {
        let ty = CType::Struct {
            name: None,
            fields: vec![StructField::bitfield("a", uchar(), 3)],
        };
        let a = capture_field(ty, uchar(), "a", vec![assign_field("a", 5)]);
        assert_eq!(a, CValue::UInt(5));
    }

    #[test]
    fn test_bitfield_two_fields_pack_into_one_byte_independently() {
        // struct { unsigned a : 3; unsigned b : 5; }  (unsigned char base).
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 3),
                StructField::bitfield("b", uchar(), 5),
            ],
        };
        assert_eq!(ty.size(), 1, "a:3 + b:5 pack into one byte");

        let a = capture_field(
            ty.clone(),
            uchar(),
            "a",
            vec![assign_field("a", 5), assign_field("b", 20)],
        );
        let b = capture_field(
            ty,
            uchar(),
            "b",
            vec![assign_field("a", 5), assign_field("b", 20)],
        );
        assert_eq!(a, CValue::UInt(5), "a reads back independently");
        assert_eq!(b, CValue::UInt(20), "b reads back independently");
    }

    #[test]
    fn test_bitfield_value_wraps_to_field_width() {
        // unsigned a : 3 holds 0..7; writing 13 (0b1101) keeps low 3 bits (5).
        let ty = CType::Struct {
            name: None,
            fields: vec![StructField::bitfield("a", uchar(), 3)],
        };
        let a = capture_field(ty, uchar(), "a", vec![assign_field("a", 13)]);
        assert_eq!(a, CValue::UInt(5), "value truncates to 3-bit width");
    }

    #[test]
    fn test_bitfield_signed_field_sign_extends_on_read() {
        // signed int x : 4 holds -8..7. Writing 0b1111 (15) reads back as -1.
        let ty = CType::Struct {
            name: None,
            fields: vec![StructField::bitfield("x", sint(), 4)],
        };
        let x = capture_field(ty, sint(), "x", vec![assign_field("x", 15)]);
        assert_eq!(x, CValue::Int(-1), "top retained bit sign-extends");
    }

    #[test]
    fn test_bitfield_field_that_does_not_fit_starts_new_unit() {
        // struct { unsigned a : 6; unsigned b : 4; } with unsigned char base:
        // a uses bits 0..6 of byte 0; b (4 bits) overflows byte 0, so it
        // starts byte 1. sizeof == 2.
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 6),
                StructField::bitfield("b", uchar(), 4),
            ],
        };
        assert_eq!(ty.size(), 2, "b cannot share byte 0, so a new unit begins");
        let la = ty.field_layout("a").expect("a layout");
        let lb = ty.field_layout("b").expect("b layout");
        assert_eq!(la.byte_offset, 0);
        assert_eq!(lb.byte_offset, 1, "b lives in a fresh storage unit");
        assert_eq!(lb.bitfield.expect("b is a bit-field").bit_offset, 0);

        let a = capture_field(
            ty.clone(),
            uchar(),
            "a",
            vec![assign_field("a", 33), assign_field("b", 9)],
        );
        let b = capture_field(
            ty,
            uchar(),
            "b",
            vec![assign_field("a", 33), assign_field("b", 9)],
        );
        assert_eq!(a, CValue::UInt(33));
        assert_eq!(b, CValue::UInt(9));
    }

    #[test]
    fn test_bitfield_zero_width_separator_forces_next_unit() {
        // struct { unsigned a : 3; unsigned : 0; unsigned b : 3; } with
        // unsigned char base: the zero-width field forces b to a new byte.
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 3),
                StructField::bitfield("", uchar(), 0),
                StructField::bitfield("b", uchar(), 3),
            ],
        };
        assert_eq!(
            ty.size(),
            2,
            "zero-width separator pushes b to the next storage unit"
        );
        let lb = ty.field_layout("b").expect("b layout");
        assert_eq!(lb.byte_offset, 1, "b starts a new byte after the separator");
        assert_eq!(lb.bitfield.expect("b is a bit-field").bit_offset, 0);
    }

    #[test]
    fn test_bitfield_packing_layout_offsets_within_unit() {
        // a at bits 0..3, b at bits 3..8, both in byte 0.
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 3),
                StructField::bitfield("b", uchar(), 5),
            ],
        };
        let ba = ty
            .field_layout("a")
            .and_then(|l| l.bitfield)
            .expect("a placement");
        let bb = ty
            .field_layout("b")
            .and_then(|l| l.bitfield)
            .expect("b placement");
        assert_eq!((ba.byte_offset, ba.bit_offset, ba.bit_width), (0, 0, 3));
        assert_eq!((bb.byte_offset, bb.bit_offset, bb.bit_width), (0, 3, 5));
    }

    #[test]
    fn test_bitfield_mixed_with_ordinary_member_flushes_unit() {
        // struct { unsigned a : 3; int c; unsigned b : 3; } (uchar base for the
        // bit-fields): c flushes the unit and is naturally aligned; b starts a
        // fresh unit after c.
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", uchar(), 3),
                StructField::new("c", sint()),
                StructField::bitfield("b", uchar(), 3),
            ],
        };
        assert_eq!(ty.field_offset("a"), Some(0));
        assert_eq!(ty.field_offset("c"), Some(4));
        assert_eq!(ty.field_offset("b"), Some(8));
        assert_eq!(ty.size(), 12);

        let a = capture_field(
            ty,
            uchar(),
            "a",
            vec![
                assign_field("a", 7),
                assign_field("c", 1000),
                assign_field("b", 2),
            ],
        );
        assert_eq!(a, CValue::UInt(7), "ordinary member store leaves a intact");
    }

    #[test]
    fn test_bitfield_unsigned_int_base_uses_four_byte_unit() {
        // struct { unsigned a : 3; unsigned b : 5; } with `unsigned int` base
        // packs both into one 4-byte storage unit. sizeof == 4.
        let ty = CType::Struct {
            name: None,
            fields: vec![
                StructField::bitfield("a", bf_uint(), 3),
                StructField::bitfield("b", bf_uint(), 5),
            ],
        };
        assert_eq!(
            ty.size(),
            4,
            "shared 4-byte unit for unsigned-int bit-fields"
        );
        let lb = ty.field_layout("b").expect("b layout");
        assert_eq!(lb.byte_offset, 0);
        assert_eq!(lb.bitfield.expect("b placement").bit_offset, 3);
    }

    #[test]
    fn test_bitfield_compound_assignment_reads_and_writes_through_field() {
        // signed x : 4 starts at 5; x += 2 → 7 (fits in 4 bits). Using a signed
        // bit-field so the read value and the literal RHS share the Int kind.
        let ty = CType::Struct {
            name: None,
            fields: vec![StructField::bitfield("x", sint(), 4)],
        };
        let x = capture_field(
            ty,
            sint(),
            "x",
            vec![
                assign_field("x", 5),
                CStmt::expr(CExpr::binop(
                    BinOp::AddAssign,
                    CExpr::member(CExpr::var("s"), "x"),
                    CExpr::int(2),
                )),
            ],
        );
        assert_eq!(x, CValue::Int(7));
    }

    #[test]
    fn test_bitfield_compound_assignment_wraps_to_signed_field_width() {
        // signed x : 4 holds -8..7; x = 7 then x += 1 overflows the field and
        // wraps to -8 (0b1000 read as signed 4-bit).
        let ty = CType::Struct {
            name: None,
            fields: vec![StructField::bitfield("x", sint(), 4)],
        };
        let x = capture_field(
            ty,
            sint(),
            "x",
            vec![
                assign_field("x", 7),
                CStmt::expr(CExpr::binop(
                    BinOp::AddAssign,
                    CExpr::member(CExpr::var("s"), "x"),
                    CExpr::int(1),
                )),
            ],
        );
        assert_eq!(x, CValue::Int(-8), "overflow wraps within the 4-bit field");
    }

    #[test]
    fn test_bitfield_address_of_is_rejected() {
        // &(s.a) is a constraint violation for bit-fields (C11 6.5.3.2p1).
        let ty = CType::Struct {
            name: None,
            fields: vec![StructField::bitfield("a", uchar(), 3)],
        };
        let block = CStmt::block(vec![
            CStmt::decl("s", ty),
            CStmt::expr(CExpr::unary(
                UnaryOp::AddrOf,
                CExpr::member(CExpr::var("s"), "a"),
            )),
        ]);
        let mut state = State::new();
        let result = Interpreter::new(&mut state).exec_stmt(&block);
        assert!(
            result.is_err(),
            "taking the address of a bit-field must error"
        );
    }

    #[test]
    fn test_bitfield_parser_extracts_widths() {
        // End-to-end: the parser populates `bit_width` from the `: w` clause.
        let mut parser = crate::parser::CParser::new();
        let func = parser
            .parse_function(
                "struct S { unsigned a : 3; unsigned b : 5; } get(void) { struct S s; return s; }",
            )
            .expect("function with bit-field struct should parse");
        let CType::Struct { fields, .. } = func.return_type.unqualified() else {
            panic!("expected struct return type, got {:?}", func.return_type);
        };
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].name, "a");
        assert_eq!(fields[0].bit_width, Some(3));
        assert_eq!(fields[1].name, "b");
        assert_eq!(fields[1].bit_width, Some(5));
    }
}
