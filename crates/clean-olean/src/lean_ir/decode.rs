// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Object-level decoder from a compacted region to the IR model in
//! [`super::types`].
//!
//! The runtime layout of each IR constructor follows from how Lean's compiler
//! represents the inductive types of `Lean/Compiler/IR/Basic.lean`:
//!
//! * a constructor with fields is a constructor object whose tag is the
//!   constructor index, object fields first in declaration order, then the
//!   `Bool` fields as `u8` scalars in declaration order, the whole object
//!   8-byte aligned (`lean_alloc_ctor_memory` in `lean.h`);
//! * a nullary constructor of a type that has non-nullary ones is the tagged
//!   scalar `lean_box(idx)` (`IRType.object`, `Arg.erased`,
//!   `FnBody.unreachable`, `ExternEntry.opaque`, `Option.none`, `List.nil`);
//! * a structure with exactly one relevant field is represented by that field
//!   (LCNF's trivial-structure rule, `hasTrivialStructure?`): `VarId` and
//!   `JoinPointId` are their `Nat`, `DeclInfo` is its `Option Name`,
//!   `ExternAttrData` is its `List ExternEntry`.
//!
//! These are MEASURED, not assumed: every rule above is checked on every object
//! (tag, object-field count, object size, scalar values), and the census over
//! the Mathlib closure decodes every declaration through them. An object that
//! does not match is an error, never a skip.

use super::error::{LeanIrError, LeanIrResult};
use super::types::{
    Alt, Arg, CtorInfo, Decl, DeclInfo, Expr, ExternAttrData, ExternEntry, FnBody, Instr, IrType,
    JoinPointId, LitVal, Param, Terminal, VarId,
};
use crate::expr::BigNat;
use crate::region::{is_ptr, is_scalar, tags, unbox_scalar, CompactedRegion};
use clean_kernel::Name;

/// Maximum nesting of join-point bodies and `case` alternatives. The chain of
/// non-terminal instructions is decoded iteratively and does not count.
pub(crate) const MAX_NESTING: usize = 1024;

/// Maximum elements accepted in one IR array (`Array Param`, `Array Arg`,
/// `Array Alt`, `Array IRType`). Lean's IR arrays are small; an entry array of
/// a whole module is read through [`IrDecoder::array`] with its own bound.
const MAX_IR_ARRAY: usize = 1 << 20;

/// Maximum length of an `ExternAttrData` entry list.
const MAX_EXTERN_ENTRIES: usize = 64;

/// Maximum byte length of an IR string literal or extern pattern.
const MAX_STRING_BYTES: usize = 64 << 20;

/// A constructor object's header, checked: `tag`, `objs` object fields and
/// `scalar_bytes` bytes of scalars. Returns the object's file offset.
struct Ctor {
    offset: usize,
}

/// Decoder over one compacted region (a module part, or a module-system part
/// assembled over its base).
pub(crate) struct IrDecoder<'r, 'a> {
    region: &'r CompactedRegion<'a>,
    /// Deepest nesting seen so far (reported by the census).
    pub(crate) max_depth_seen: usize,
}

impl<'r, 'a> IrDecoder<'r, 'a> {
    pub(crate) fn new(region: &'r CompactedRegion<'a>) -> Self {
        Self {
            region,
            max_depth_seen: 0,
        }
    }

    /// The object at `pointer`: a compacted (rc 0) heap object.
    fn object(
        &self,
        pointer: u64,
        what: &'static str,
    ) -> LeanIrResult<(usize, crate::region::ObjectHeader)> {
        if !is_ptr(pointer) || !pointer.is_multiple_of(8) {
            return Err(LeanIrError::layout(
                what,
                pointer,
                "expected an object pointer",
            ));
        }
        let offset = self.region.ptr_to_offset(pointer)?;
        let header = self.region.read_header_at(offset)?;
        if header.rc != 0 {
            return Err(LeanIrError::layout(
                what,
                pointer,
                format!(
                    "nonzero reference count {} in a compacted region",
                    header.rc
                ),
            ));
        }
        Ok((offset, header))
    }

    /// Check a constructor object's shape exactly and return its offset.
    fn ctor(
        &self,
        pointer: u64,
        what: &'static str,
        tag: u8,
        objs: u8,
        scalar_bytes: usize,
    ) -> LeanIrResult<Ctor> {
        let (offset, header) = self.object(pointer, what)?;
        let size = 8 + 8 * usize::from(objs) + scalar_bytes;
        let aligned = size.div_ceil(8) * 8;
        if header.tag != tag || header.other != objs || usize::from(header.cs_sz) != aligned {
            return Err(LeanIrError::layout(
                what,
                pointer,
                format!(
                    "expected constructor {tag} with {objs} object field(s) and {scalar_bytes} \
                     scalar byte(s) ({aligned} bytes), found tag {} with {} field(s), {} bytes",
                    header.tag, header.other, header.cs_sz
                ),
            ));
        }
        self.region.bytes_at(offset, aligned)?;
        Ok(Ctor { offset })
    }

    /// Object field `i` of a checked constructor.
    fn field(&self, ctor: &Ctor, i: usize) -> LeanIrResult<u64> {
        Ok(self.region.read_u64_at(ctor.offset + 8 + 8 * i)?)
    }

    /// The `Bool` scalar at byte `byte` after `objs` object fields.
    fn bool_scalar(
        &self,
        ctor: &Ctor,
        objs: usize,
        byte: usize,
        what: &'static str,
    ) -> LeanIrResult<bool> {
        let bytes = self.region.bytes_at(ctor.offset + 8 + 8 * objs + byte, 1)?;
        match bytes[0] {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(LeanIrError::layout(
                what,
                self.region.offset_to_ptr(ctor.offset),
                format!("Bool scalar {other} is neither 0 nor 1"),
            )),
        }
    }

    /// The constructor index of a value of an inductive type whose nullary
    /// constructors are boxed: `Ok(Err(idx))` for `lean_box(idx)`,
    /// `Ok(Ok(tag))` for an object.
    fn tag_of(&self, pointer: u64, what: &'static str) -> LeanIrResult<Result<u8, u64>> {
        if is_scalar(pointer) {
            return Ok(Err(unbox_scalar(pointer)));
        }
        let (_, header) = self.object(pointer, what)?;
        if header.tag > tags::MAX_CTOR_TAG {
            return Err(LeanIrError::layout(
                what,
                pointer,
                format!(
                    "expected a constructor object, found runtime tag {}",
                    header.tag
                ),
            ));
        }
        Ok(Ok(header.tag))
    }

    /// A `Nat` that must fit in `u64` (indices, sizes). A heap `Nat` beyond
    /// that is refused by the region reader, never truncated.
    pub(crate) fn nat(&self, pointer: u64) -> LeanIrResult<u64> {
        Ok(self.region.read_kernel_nat_u64(pointer)?)
    }

    /// A `Nat` of any size (`LitVal.num`). Tagged scalars and canonical GMP
    /// objects only; the limbs must be stored inline and the top limb nonzero.
    fn big_nat(&self, pointer: u64) -> LeanIrResult<BigNat> {
        if is_scalar(pointer) {
            return Ok(BigNat::from_u64(unbox_scalar(pointer)));
        }
        let (offset, header) = self.object(pointer, "Nat")?;
        if header.tag != tags::MPZ || header.other != 0 {
            return Err(LeanIrError::layout(
                "Nat",
                pointer,
                format!("expected an MPZ object, found tag {}", header.tag),
            ));
        }
        let alloc = self.region.read_i32_at(offset + 8)?;
        let size = self.region.read_i32_at(offset + 12)?;
        let limbs = usize::try_from(size).map_err(|_| {
            LeanIrError::layout("Nat", pointer, format!("nonpositive MPZ size {size}"))
        })?;
        if limbs == 0 || alloc != size {
            return Err(LeanIrError::layout(
                "Nat",
                pointer,
                format!("noncanonical MPZ (alloc {alloc}, size {size})"),
            ));
        }
        if usize::from(header.cs_sz) != 24 + 8 * limbs {
            return Err(LeanIrError::layout(
                "Nat",
                pointer,
                format!("MPZ object size {} for {limbs} limb(s)", header.cs_sz),
            ));
        }
        let digits = self.region.read_u64_at(offset + 16)?;
        if Some(digits) != pointer.checked_add(24) {
            return Err(LeanIrError::layout(
                "Nat",
                pointer,
                "MPZ digits are not stored inline",
            ));
        }
        let values = (0..limbs)
            .map(|i| self.region.read_u64_at(offset + 24 + 8 * i))
            .collect::<Result<Vec<u64>, _>>()?;
        let canonical = match values.as_slice() {
            [single] => *single >= (1 << 63),
            [.., top] => *top != 0,
            [] => false,
        };
        if !canonical {
            return Err(LeanIrError::layout(
                "Nat",
                pointer,
                "MPZ value is not in canonical (smallest) form",
            ));
        }
        Ok(BigNat::from_limbs(values))
    }

    fn name(&self, pointer: u64) -> LeanIrResult<Name> {
        Ok(self.region.read_kernel_name_ptr(pointer)?)
    }

    /// A Lean `String` object, validated exactly (terminator, UTF-8, length).
    fn string(&self, pointer: u64) -> LeanIrResult<String> {
        let (offset, header) = self.object(pointer, "String")?;
        if header.tag != tags::STRING || header.other != 0 {
            return Err(LeanIrError::layout(
                "String",
                pointer,
                format!("expected a String object, found tag {}", header.tag),
            ));
        }
        let size = usize::try_from(self.region.read_u64_at(offset + 8)?)
            .map_err(|_| LeanIrError::layout("String", pointer, "size overflow"))?;
        let capacity = self.region.read_u64_at(offset + 16)?;
        if size == 0 || size > MAX_STRING_BYTES || size as u64 > capacity {
            return Err(LeanIrError::layout(
                "String",
                pointer,
                format!("size {size} / capacity {capacity} out of bounds"),
            ));
        }
        let bytes = self.region.bytes_at(offset + 32, size)?;
        let content = bytes
            .strip_suffix(&[0])
            .ok_or_else(|| LeanIrError::layout("String", pointer, "missing NUL terminator"))?;
        let text = std::str::from_utf8(content)
            .map_err(|_| LeanIrError::layout("String", pointer, "invalid UTF-8"))?;
        if self.region.read_u64_at(offset + 24)? != text.chars().count() as u64 {
            return Err(LeanIrError::layout(
                "String",
                pointer,
                "character count does not match the contents",
            ));
        }
        Ok(text.to_owned())
    }

    /// The element pointers of an `Array` object.
    pub(crate) fn array(
        &self,
        pointer: u64,
        what: &'static str,
        max: usize,
    ) -> LeanIrResult<Vec<u64>> {
        let (offset, header) = self.object(pointer, what)?;
        if header.tag != tags::ARRAY {
            return Err(LeanIrError::layout(
                what,
                pointer,
                format!("expected an Array object, found tag {}", header.tag),
            ));
        }
        let size = self.region.read_usize_at(offset + 8, what)?;
        let capacity = self.region.read_u64_at(offset + 16)?;
        if size > max || size as u64 > capacity {
            return Err(LeanIrError::layout(
                what,
                pointer,
                format!("array size {size} (capacity {capacity}, bound {max})"),
            ));
        }
        self.region.validate_array_bounds(offset, size)?;
        (0..size)
            .map(|i| {
                let at = self.region.array_elem_offset(offset, i, what)?;
                Ok(self.region.read_u64_at(at)?)
            })
            .collect()
    }

    /// The elements of a `List` (`nil` = `lean_box(0)`, `cons` = tag 1, 2 fields).
    fn list(&self, pointer: u64, what: &'static str, max: usize) -> LeanIrResult<Vec<u64>> {
        let mut items = Vec::new();
        let mut current = pointer;
        loop {
            match self.tag_of(current, what)? {
                Err(0) => return Ok(items),
                Err(other) => {
                    return Err(LeanIrError::layout(
                        what,
                        current,
                        format!("List scalar {other} is not nil"),
                    ))
                }
                Ok(_) => {
                    if items.len() >= max {
                        return Err(LeanIrError::layout(what, pointer, "list exceeds bound"));
                    }
                    let cons = self.ctor(current, what, 1, 2, 0)?;
                    items.push(self.field(&cons, 0)?);
                    current = self.field(&cons, 1)?;
                }
            }
        }
    }

    /// `Option α` (`none` = `lean_box(0)`, `some` = tag 1, 1 field).
    fn option(&self, pointer: u64, what: &'static str) -> LeanIrResult<Option<u64>> {
        match self.tag_of(pointer, what)? {
            Err(0) => Ok(None),
            Err(other) => Err(LeanIrError::layout(
                what,
                pointer,
                format!("Option scalar {other} is not none"),
            )),
            Ok(_) => {
                let some = self.ctor(pointer, what, 1, 1, 0)?;
                Ok(Some(self.field(&some, 0)?))
            }
        }
    }

    fn var(&self, pointer: u64) -> LeanIrResult<VarId> {
        Ok(VarId(self.nat(pointer)?))
    }

    fn join_point(&self, pointer: u64) -> LeanIrResult<JoinPointId> {
        Ok(JoinPointId(self.nat(pointer)?))
    }

    pub(crate) fn ir_type(&self, pointer: u64) -> LeanIrResult<IrType> {
        const WHAT: &str = "IRType";
        match self.tag_of(pointer, WHAT)? {
            Err(0) => Ok(IrType::Float),
            Err(1) => Ok(IrType::UInt8),
            Err(2) => Ok(IrType::UInt16),
            Err(3) => Ok(IrType::UInt32),
            Err(4) => Ok(IrType::UInt64),
            Err(5) => Ok(IrType::USize),
            Err(6) => Ok(IrType::Erased),
            Err(7) => Ok(IrType::Object),
            Err(8) => Ok(IrType::TObject),
            Err(9) => Ok(IrType::Float32),
            Err(12) => Ok(IrType::Tagged),
            Err(13) => Ok(IrType::Void),
            Err(other) => Err(LeanIrError::layout(
                WHAT,
                pointer,
                format!("scalar {other} is not a nullary IRType"),
            )),
            Ok(10) => {
                let c = self.ctor(pointer, WHAT, 10, 2, 0)?;
                let lean_type_name = self
                    .option(self.field(&c, 0)?, "IRType.struct leanTypeName")?
                    .map(|n| self.name(n))
                    .transpose()?;
                let types = self.ir_types(self.field(&c, 1)?)?;
                Ok(IrType::Struct {
                    lean_type_name,
                    types,
                })
            }
            Ok(11) => {
                let c = self.ctor(pointer, WHAT, 11, 2, 0)?;
                let lean_type_name = self.name(self.field(&c, 0)?)?;
                let types = self.ir_types(self.field(&c, 1)?)?;
                Ok(IrType::Union {
                    lean_type_name,
                    types,
                })
            }
            Ok(tag) => Err(LeanIrError::layout(
                WHAT,
                pointer,
                format!("object tag {tag} is not IRType.struct/union"),
            )),
        }
    }

    fn ir_types(&self, pointer: u64) -> LeanIrResult<Vec<IrType>> {
        self.array(pointer, "Array IRType", MAX_IR_ARRAY)?
            .into_iter()
            .map(|p| self.ir_type(p))
            .collect()
    }

    fn arg(&self, pointer: u64) -> LeanIrResult<Arg> {
        match self.tag_of(pointer, "Arg")? {
            Err(1) => Ok(Arg::Erased),
            Ok(0) => {
                let c = self.ctor(pointer, "Arg", 0, 1, 0)?;
                Ok(Arg::Var(self.var(self.field(&c, 0)?)?))
            }
            Ok(tag) => Err(LeanIrError::layout(
                "Arg",
                pointer,
                format!("object tag {tag} is not Arg.var"),
            )),
            Err(other) => Err(LeanIrError::layout(
                "Arg",
                pointer,
                format!("scalar {other} is not Arg.erased"),
            )),
        }
    }

    fn args(&self, pointer: u64) -> LeanIrResult<Vec<Arg>> {
        self.array(pointer, "Array Arg", MAX_IR_ARRAY)?
            .into_iter()
            .map(|p| self.arg(p))
            .collect()
    }

    fn lit(&self, pointer: u64) -> LeanIrResult<LitVal> {
        match self.tag_of(pointer, "LitVal")? {
            Ok(0) => {
                let c = self.ctor(pointer, "LitVal", 0, 1, 0)?;
                Ok(LitVal::Num(self.big_nat(self.field(&c, 0)?)?))
            }
            Ok(1) => {
                let c = self.ctor(pointer, "LitVal", 1, 1, 0)?;
                Ok(LitVal::Str(self.string(self.field(&c, 0)?)?))
            }
            _ => Err(LeanIrError::layout("LitVal", pointer, "not LitVal.num/str")),
        }
    }

    fn ctor_info(&self, pointer: u64) -> LeanIrResult<CtorInfo> {
        let c = self.ctor(pointer, "CtorInfo", 0, 5, 0)?;
        Ok(CtorInfo {
            name: self.name(self.field(&c, 0)?)?,
            cidx: self.nat(self.field(&c, 1)?)?,
            size: self.nat(self.field(&c, 2)?)?,
            usize: self.nat(self.field(&c, 3)?)?,
            ssize: self.nat(self.field(&c, 4)?)?,
        })
    }

    fn expr(&self, pointer: u64) -> LeanIrResult<Expr> {
        const WHAT: &str = "Expr";
        let tag = match self.tag_of(pointer, WHAT)? {
            Ok(tag) => tag,
            Err(other) => {
                return Err(LeanIrError::layout(
                    WHAT,
                    pointer,
                    format!("scalar {other}: every Expr constructor has fields"),
                ))
            }
        };
        let expr = match tag {
            0 => {
                let c = self.ctor(pointer, WHAT, 0, 2, 0)?;
                Expr::Ctor {
                    info: self.ctor_info(self.field(&c, 0)?)?,
                    args: self.args(self.field(&c, 1)?)?,
                }
            }
            1 => {
                let c = self.ctor(pointer, WHAT, 1, 2, 0)?;
                Expr::Reset {
                    n: self.nat(self.field(&c, 0)?)?,
                    x: self.var(self.field(&c, 1)?)?,
                }
            }
            2 => {
                let c = self.ctor(pointer, WHAT, 2, 3, 1)?;
                Expr::Reuse {
                    x: self.var(self.field(&c, 0)?)?,
                    info: self.ctor_info(self.field(&c, 1)?)?,
                    args: self.args(self.field(&c, 2)?)?,
                    update_header: self.bool_scalar(&c, 3, 0, WHAT)?,
                }
            }
            3 | 4 => {
                let c = self.ctor(pointer, WHAT, tag, 2, 0)?;
                let i = self.nat(self.field(&c, 0)?)?;
                let x = self.var(self.field(&c, 1)?)?;
                if tag == 3 {
                    Expr::Proj { i, x }
                } else {
                    Expr::UProj { i, x }
                }
            }
            5 => {
                let c = self.ctor(pointer, WHAT, 5, 3, 0)?;
                Expr::SProj {
                    n: self.nat(self.field(&c, 0)?)?,
                    offset: self.nat(self.field(&c, 1)?)?,
                    x: self.var(self.field(&c, 2)?)?,
                }
            }
            6 | 7 => {
                let c = self.ctor(pointer, WHAT, tag, 2, 0)?;
                let f = self.name(self.field(&c, 0)?)?;
                let args = self.args(self.field(&c, 1)?)?;
                if tag == 6 {
                    Expr::Fap { f, args }
                } else {
                    Expr::Pap { f, args }
                }
            }
            8 => {
                let c = self.ctor(pointer, WHAT, 8, 2, 0)?;
                Expr::Ap {
                    x: self.var(self.field(&c, 0)?)?,
                    args: self.args(self.field(&c, 1)?)?,
                }
            }
            9 => {
                let c = self.ctor(pointer, WHAT, 9, 2, 0)?;
                Expr::Box {
                    ty: self.ir_type(self.field(&c, 0)?)?,
                    x: self.var(self.field(&c, 1)?)?,
                }
            }
            10 | 12 => {
                let c = self.ctor(pointer, WHAT, tag, 1, 0)?;
                let x = self.var(self.field(&c, 0)?)?;
                if tag == 10 {
                    Expr::Unbox { x }
                } else {
                    Expr::IsShared { x }
                }
            }
            11 => {
                let c = self.ctor(pointer, WHAT, 11, 1, 0)?;
                Expr::Lit(self.lit(self.field(&c, 0)?)?)
            }
            other => {
                return Err(LeanIrError::layout(
                    WHAT,
                    pointer,
                    format!("object tag {other} is not an Expr constructor"),
                ))
            }
        };
        Ok(expr)
    }

    fn param(&self, pointer: u64) -> LeanIrResult<Param> {
        let c = self.ctor(pointer, "Param", 0, 2, 1)?;
        Ok(Param {
            x: self.var(self.field(&c, 0)?)?,
            ty: self.ir_type(self.field(&c, 1)?)?,
            borrow: self.bool_scalar(&c, 2, 0, "Param")?,
        })
    }

    fn params(&self, pointer: u64) -> LeanIrResult<Vec<Param>> {
        self.array(pointer, "Array Param", MAX_IR_ARRAY)?
            .into_iter()
            .map(|p| self.param(p))
            .collect()
    }

    fn alt(&mut self, pointer: u64, depth: usize) -> LeanIrResult<Alt> {
        match self.tag_of(pointer, "Alt")? {
            Ok(0) => {
                let c = self.ctor(pointer, "Alt", 0, 2, 0)?;
                let info = self.ctor_info(self.field(&c, 0)?)?;
                let body = self.fn_body(self.field(&c, 1)?, depth + 1)?;
                Ok(Alt::Ctor { info, body })
            }
            Ok(1) => {
                let c = self.ctor(pointer, "Alt", 1, 1, 0)?;
                let body = self.fn_body(self.field(&c, 0)?, depth + 1)?;
                Ok(Alt::Default { body })
            }
            _ => Err(LeanIrError::layout("Alt", pointer, "not Alt.ctor/default")),
        }
    }

    /// Decode a `FnBody` chain, flattening its non-terminal spine iteratively.
    pub(crate) fn fn_body(&mut self, pointer: u64, depth: usize) -> LeanIrResult<FnBody> {
        const WHAT: &str = "FnBody";
        if depth > MAX_NESTING {
            return Err(LeanIrError::DepthLimit {
                limit: MAX_NESTING,
                pointer,
            });
        }
        self.max_depth_seen = self.max_depth_seen.max(depth);
        let mut instrs = Vec::new();
        let mut current = pointer;
        loop {
            let tag = match self.tag_of(current, WHAT)? {
                Err(12) => {
                    return Ok(FnBody {
                        instrs,
                        terminal: Terminal::Unreachable,
                    })
                }
                Err(other) => {
                    return Err(LeanIrError::layout(
                        WHAT,
                        current,
                        format!("scalar {other} is not FnBody.unreachable"),
                    ))
                }
                Ok(tag) => tag,
            };
            let (instr, next) = match tag {
                0 => {
                    let c = self.ctor(current, WHAT, 0, 4, 0)?;
                    let instr = Instr::VDecl {
                        x: self.var(self.field(&c, 0)?)?,
                        ty: self.ir_type(self.field(&c, 1)?)?,
                        e: self.expr(self.field(&c, 2)?)?,
                    };
                    (instr, self.field(&c, 3)?)
                }
                1 => {
                    let c = self.ctor(current, WHAT, 1, 4, 0)?;
                    let j = self.join_point(self.field(&c, 0)?)?;
                    let params = self.params(self.field(&c, 1)?)?;
                    let body = self.fn_body(self.field(&c, 2)?, depth + 1)?;
                    (Instr::JDecl { j, params, body }, self.field(&c, 3)?)
                }
                2 => {
                    let c = self.ctor(current, WHAT, 2, 4, 0)?;
                    let instr = Instr::Set {
                        x: self.var(self.field(&c, 0)?)?,
                        i: self.nat(self.field(&c, 1)?)?,
                        y: self.arg(self.field(&c, 2)?)?,
                    };
                    (instr, self.field(&c, 3)?)
                }
                3 => {
                    let c = self.ctor(current, WHAT, 3, 3, 0)?;
                    let instr = Instr::SetTag {
                        x: self.var(self.field(&c, 0)?)?,
                        cidx: self.nat(self.field(&c, 1)?)?,
                    };
                    (instr, self.field(&c, 2)?)
                }
                4 => {
                    let c = self.ctor(current, WHAT, 4, 4, 0)?;
                    let instr = Instr::USet {
                        x: self.var(self.field(&c, 0)?)?,
                        i: self.nat(self.field(&c, 1)?)?,
                        y: self.var(self.field(&c, 2)?)?,
                    };
                    (instr, self.field(&c, 3)?)
                }
                5 => {
                    let c = self.ctor(current, WHAT, 5, 6, 0)?;
                    let instr = Instr::SSet {
                        x: self.var(self.field(&c, 0)?)?,
                        i: self.nat(self.field(&c, 1)?)?,
                        offset: self.nat(self.field(&c, 2)?)?,
                        y: self.var(self.field(&c, 3)?)?,
                        ty: self.ir_type(self.field(&c, 4)?)?,
                    };
                    (instr, self.field(&c, 5)?)
                }
                6 | 7 => {
                    let c = self.ctor(current, WHAT, tag, 3, 2)?;
                    let x = self.var(self.field(&c, 0)?)?;
                    let n = self.nat(self.field(&c, 1)?)?;
                    let check_ref = self.bool_scalar(&c, 3, 0, WHAT)?;
                    let persistent = self.bool_scalar(&c, 3, 1, WHAT)?;
                    let instr = if tag == 6 {
                        Instr::Inc {
                            x,
                            n,
                            check_ref,
                            persistent,
                        }
                    } else {
                        Instr::Dec {
                            x,
                            n,
                            check_ref,
                            persistent,
                        }
                    };
                    (instr, self.field(&c, 2)?)
                }
                8 => {
                    let c = self.ctor(current, WHAT, 8, 2, 0)?;
                    let instr = Instr::Del {
                        x: self.var(self.field(&c, 0)?)?,
                    };
                    (instr, self.field(&c, 1)?)
                }
                9 => {
                    let c = self.ctor(current, WHAT, 9, 4, 0)?;
                    let tid = self.name(self.field(&c, 0)?)?;
                    let x = self.var(self.field(&c, 1)?)?;
                    let x_type = self.ir_type(self.field(&c, 2)?)?;
                    let alts = self
                        .array(self.field(&c, 3)?, "Array Alt", MAX_IR_ARRAY)?
                        .into_iter()
                        .map(|p| self.alt(p, depth))
                        .collect::<LeanIrResult<Vec<_>>>()?;
                    let terminal = Terminal::Case {
                        tid,
                        x,
                        x_type,
                        alts,
                    };
                    return Ok(FnBody { instrs, terminal });
                }
                10 => {
                    let c = self.ctor(current, WHAT, 10, 1, 0)?;
                    let terminal = Terminal::Ret(self.arg(self.field(&c, 0)?)?);
                    return Ok(FnBody { instrs, terminal });
                }
                11 => {
                    let c = self.ctor(current, WHAT, 11, 2, 0)?;
                    let terminal = Terminal::Jmp {
                        j: self.join_point(self.field(&c, 0)?)?,
                        args: self.args(self.field(&c, 1)?)?,
                    };
                    return Ok(FnBody { instrs, terminal });
                }
                other => {
                    return Err(LeanIrError::layout(
                        WHAT,
                        current,
                        format!("object tag {other} is not a FnBody constructor"),
                    ))
                }
            };
            // Lean's object compactor writes an object only after every object
            // it points to, and a module part only after the parts it
            // references, so a continuation always sits at a LOWER address
            // than the instruction holding it (checked on every instruction of
            // the Mathlib-closure census). Requiring that bounds this loop on
            // any input: a corrupt or crafted chain that loops back is refused
            // instead of growing `instrs` until memory runs out.
            if is_ptr(next) && next >= current {
                return Err(LeanIrError::layout(
                    WHAT,
                    current,
                    format!("continuation 0x{next:x} does not precede its instruction"),
                ));
            }
            instrs.push(instr);
            current = next;
        }
    }

    fn extern_entry(&self, pointer: u64) -> LeanIrResult<ExternEntry> {
        const WHAT: &str = "ExternEntry";
        match self.tag_of(pointer, WHAT)? {
            Err(3) => Ok(ExternEntry::Opaque),
            Ok(0) => {
                let c = self.ctor(pointer, WHAT, 0, 1, 0)?;
                Ok(ExternEntry::Adhoc {
                    backend: self.name(self.field(&c, 0)?)?,
                })
            }
            Ok(1) => {
                let c = self.ctor(pointer, WHAT, 1, 2, 0)?;
                Ok(ExternEntry::Inline {
                    backend: self.name(self.field(&c, 0)?)?,
                    pattern: self.string(self.field(&c, 1)?)?,
                })
            }
            Ok(2) => {
                let c = self.ctor(pointer, WHAT, 2, 2, 0)?;
                Ok(ExternEntry::Standard {
                    backend: self.name(self.field(&c, 0)?)?,
                    symbol: self.string(self.field(&c, 1)?)?,
                })
            }
            _ => Err(LeanIrError::layout(
                WHAT,
                pointer,
                "not an ExternEntry constructor",
            )),
        }
    }

    /// `ExternAttrData`, represented by its single field `List ExternEntry`.
    pub(crate) fn extern_attr_data(&self, pointer: u64) -> LeanIrResult<ExternAttrData> {
        let entries = self
            .list(pointer, "ExternAttrData.entries", MAX_EXTERN_ENTRIES)?
            .into_iter()
            .map(|p| self.extern_entry(p))
            .collect::<LeanIrResult<Vec<_>>>()?;
        Ok(ExternAttrData { entries })
    }

    /// The name of a `Decl` without decoding the rest (for error context).
    pub(crate) fn decl_name(&self, pointer: u64) -> Option<Name> {
        let (offset, _) = self.object(pointer, "Decl").ok()?;
        let name = self.region.read_u64_at(offset + 8).ok()?;
        self.name(name).ok()
    }

    /// `Lean.IR.Decl`.
    pub(crate) fn decl(&mut self, pointer: u64) -> LeanIrResult<Decl> {
        const WHAT: &str = "Decl";
        match self.tag_of(pointer, WHAT)? {
            Ok(0) => {
                let c = self.ctor(pointer, WHAT, 0, 5, 0)?;
                let f = self.name(self.field(&c, 0)?)?;
                let params = self.params(self.field(&c, 1)?)?;
                let ty = self.ir_type(self.field(&c, 2)?)?;
                let body = self.fn_body(self.field(&c, 3)?, 0)?;
                // `DeclInfo` is represented by its single field `sorryDep? : Option Name`.
                let sorry_dep = self
                    .option(self.field(&c, 4)?, "DeclInfo.sorryDep?")?
                    .map(|n| self.name(n))
                    .transpose()?;
                Ok(Decl::FDecl {
                    f,
                    params,
                    ty,
                    body,
                    info: DeclInfo { sorry_dep },
                })
            }
            Ok(1) => {
                let c = self.ctor(pointer, WHAT, 1, 4, 0)?;
                Ok(Decl::Extern {
                    f: self.name(self.field(&c, 0)?)?,
                    params: self.params(self.field(&c, 1)?)?,
                    ty: self.ir_type(self.field(&c, 2)?)?,
                    ext: self.extern_attr_data(self.field(&c, 3)?)?,
                })
            }
            _ => Err(LeanIrError::layout(WHAT, pointer, "not Decl.fdecl/extern")),
        }
    }

    /// A `Name × Name` pair (the entry type of the `implemented_by` and
    /// `init` parametric attributes).
    pub(crate) fn name_pair(&self, pointer: u64) -> LeanIrResult<(Name, Name)> {
        let c = self.ctor(pointer, "Name × Name", 0, 2, 0)?;
        Ok((
            self.name(self.field(&c, 0)?)?,
            self.name(self.field(&c, 1)?)?,
        ))
    }

    /// A `Name × ExternAttrData` pair (the entry type of `externAttr`).
    pub(crate) fn extern_pair(&self, pointer: u64) -> LeanIrResult<(Name, ExternAttrData)> {
        let c = self.ctor(pointer, "Name × ExternAttrData", 0, 2, 0)?;
        Ok((
            self.name(self.field(&c, 0)?)?,
            self.extern_attr_data(self.field(&c, 1)?)?,
        ))
    }
}
