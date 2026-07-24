// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression parsing from .olean files
//!
//! Lean 4 expressions are represented as an inductive type with these constructors:
//!
//! ```text
//! inductive Expr where
//!   | bvar   (deBruijnIndex : Nat)                        -- tag 0, scalar
//!   | fvar   (fvarId : FVarId)                            -- tag 1, 1 field
//!   | mvar   (mvarId : MVarId)                            -- tag 2, 1 field
//!   | sort   (u : Level)                                  -- tag 3, 1 field
//!   | const  (declName : Name) (us : List Level)          -- tag 4, 2 fields
//!   | app    (fn : Expr) (arg : Expr)                     -- tag 5, 2 fields
//!   | lam    (binderName : Name) (binderType : Expr)
//!            (body : Expr) (binderInfo : BinderInfo)      -- tag 6, 3 fields + scalar
//!   | forallE(binderName : Name) (binderType : Expr)
//!            (body : Expr) (binderInfo : BinderInfo)      -- tag 7, 3 fields + scalar
//!   | letE   (declName : Name) (type : Expr) (value : Expr)
//!            (body : Expr) (nondep : Bool)                -- tag 8, 4 fields + scalar
//!   | lit    (value : Literal)                            -- tag 9, 1 field
//!   | mdata  (data : MData) (expr : Expr)                 -- tag 10, 2 fields
//!   | proj   (typeName : Name) (idx : Nat) (struct : Expr)-- tag 11, 2 fields + scalar
//! ```

use crate::error::{OleanError, OleanResult};
use crate::level::ParsedLevel;
use crate::region::{is_ptr, is_scalar, tags, unbox_scalar, CompactedRegion};

/// Expression constructor tags from the .olean format.
///
/// # Closed set of tags (no SProp / Squash / Cubical Expr constructor)
///
/// Mainline Lean 4's `Expr` inductive has exactly these twelve constructors,
/// tagged `0..=11` in declaration order. There is intentionally **no** separate
/// `Expr` constructor for strict-prop (`SProp`), truncation (`Squash`), or any
/// cubical / set-theoretic mode:
///
/// - Strict-prop / `Prop` is `Expr.sort` (tag 3) applied to universe level
///   zero — not a distinct `Expr` tag.
/// - `Squash` / truncation is an ordinary `Expr.const` (tag 4) reference to the
///   `Squash` declaration, elaborated like any other constant.
/// - Mainline Lean 4 has no cubical mode, so no cubical `Expr` tag exists.
///
/// Consequently, any object tag `>= 12` encountered where an `Expr` is expected
/// is **not** a higher / future `Expr` constructor; it indicates a malformed or
/// truncated `.olean` (or a pointer that does not actually point at an `Expr`).
/// [`CompactedRegion::read_expr_iterative`] therefore fails closed on such a tag
/// with a typed [`OleanError::InvalidObjectTag`] rather than silently
/// misclassifying it — see the unknown-tag tests in this module.
pub mod expr_tags {
    /// Bound variable (de Bruijn index).
    pub const BVAR: u8 = 0;
    /// Free variable.
    pub const FVAR: u8 = 1;
    /// Metavariable.
    pub const MVAR: u8 = 2;
    /// Sort (Type u).
    pub const SORT: u8 = 3;
    /// Constant reference.
    pub const CONST: u8 = 4;
    /// Function application.
    pub const APP: u8 = 5;
    /// Lambda abstraction.
    pub const LAM: u8 = 6;
    /// Pi/forall type.
    pub const FORALL_E: u8 = 7;
    /// Let binding.
    pub const LET_E: u8 = 8;
    /// Literal value.
    pub const LIT: u8 = 9;
    /// Metadata wrapper.
    pub const MDATA: u8 = 10;
    /// Structure projection.
    pub const PROJ: u8 = 11;
}

/// Binder information (matches kernel BinderInfo).
///
/// # Forward Compatibility
///
/// This enum is marked `#[non_exhaustive]` to allow future Lean 4 binder
/// kinds without breaking downstream code. Always include a wildcard arm
/// in match expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParsedBinderInfo {
    /// Explicit binder `(x : T)`.
    Default,
    /// Implicit binder `{x : T}`.
    Implicit,
    /// Strict implicit binder `⦃x : T⦄`.
    StrictImplicit,
    /// Instance implicit binder `[x : T]`.
    InstImplicit,
    /// Unknown binder kind from future Lean 4 version.
    ///
    /// Contains the raw tag value for logging/debugging. Callers should
    /// handle this gracefully (e.g., treat as explicit or emit a warning).
    Unknown(u8),
}

impl ParsedBinderInfo {
    /// Decode from u8 value (as stored in .olean).
    ///
    /// Returns [`Unknown`](Self::Unknown) for unrecognized tag values,
    /// preserving the raw byte for logging/debugging. This allows callers
    /// to detect and handle future Lean 4 binder kinds gracefully.
    pub fn from_u8(val: u8) -> Self {
        match val {
            0 => ParsedBinderInfo::Default,
            1 => ParsedBinderInfo::Implicit,
            2 => ParsedBinderInfo::StrictImplicit,
            3 => ParsedBinderInfo::InstImplicit,
            unknown => ParsedBinderInfo::Unknown(unknown),
        }
    }

    /// Returns `true` if this is an unknown binder kind.
    pub fn is_unknown(&self) -> bool {
        matches!(self, ParsedBinderInfo::Unknown(_))
    }
}

/// A literal value in an expression.
///
/// # Forward Compatibility
///
/// This enum is marked `#[non_exhaustive]` to allow future Lean 4 literal
/// types without breaking downstream code. Always include a wildcard arm
/// in match expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParsedLiteral {
    /// Natural number literal (arbitrary precision).
    Nat(BigNat),
    /// String literal.
    String(String),
}

/// A parsed expression.
///
/// # Forward Compatibility
///
/// This enum is marked `#[non_exhaustive]` to allow future Lean 4 expression
/// constructors without breaking downstream code. Always include a wildcard arm
/// in match expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParsedExpr {
    /// Bound variable (de Bruijn index)
    BVar(u64),
    /// Free variable
    FVar(String),
    /// Metavariable
    MVar(String),
    /// Sort (Type u)
    Sort(ParsedLevel),
    /// Constant with universe levels
    Const(String, Vec<ParsedLevel>),
    /// Application
    App(Box<ParsedExpr>, Box<ParsedExpr>),
    /// Lambda
    Lam(String, Box<ParsedExpr>, Box<ParsedExpr>, ParsedBinderInfo),
    /// Forall/Pi type
    ForallE(String, Box<ParsedExpr>, Box<ParsedExpr>, ParsedBinderInfo),
    /// Let binding
    LetE(
        String,
        Box<ParsedExpr>,
        Box<ParsedExpr>,
        Box<ParsedExpr>,
        bool,
    ),
    /// Literal
    Lit(ParsedLiteral),
    /// Metadata
    MData(Box<ParsedExpr>),
    /// Projection
    Proj(String, u64, Box<ParsedExpr>),
}

impl ParsedExpr {
    /// Get a short description of the expression kind
    pub fn kind(&self) -> &'static str {
        match self {
            ParsedExpr::BVar(_) => "bvar",
            ParsedExpr::FVar(_) => "fvar",
            ParsedExpr::MVar(_) => "mvar",
            ParsedExpr::Sort(_) => "sort",
            ParsedExpr::Const(_, _) => "const",
            ParsedExpr::App(_, _) => "app",
            ParsedExpr::Lam(_, _, _, _) => "lam",
            ParsedExpr::ForallE(_, _, _, _) => "forallE",
            ParsedExpr::LetE(_, _, _, _, _) => "letE",
            ParsedExpr::Lit(_) => "lit",
            ParsedExpr::MData(_) => "mdata",
            ParsedExpr::Proj(_, _, _) => "proj",
        }
    }

    /// Count the depth of the expression (for limiting recursion)
    pub fn depth(&self) -> usize {
        match self {
            ParsedExpr::BVar(_)
            | ParsedExpr::FVar(_)
            | ParsedExpr::MVar(_)
            | ParsedExpr::Sort(_)
            | ParsedExpr::Lit(_)
            | ParsedExpr::Const(_, _) => 0,
            ParsedExpr::App(f, a) => 1 + f.depth().max(a.depth()),
            ParsedExpr::Lam(_, t, b, _) | ParsedExpr::ForallE(_, t, b, _) => {
                1 + t.depth().max(b.depth())
            }
            ParsedExpr::LetE(_, t, v, b, _) => 1 + t.depth().max(v.depth()).max(b.depth()),
            ParsedExpr::MData(e) | ParsedExpr::Proj(_, _, e) => 1 + e.depth(),
        }
    }
}

/// Work item for iterative expression parsing
enum ExprWork {
    /// Parse expression at this pointer
    Parse(u64),
    /// Build App from top 2 results
    BuildApp,
    /// Build Lam from top 2 results
    BuildLam(String, ParsedBinderInfo),
    /// Build ForallE from top 2 results
    BuildForallE(String, ParsedBinderInfo),
    /// Build LetE from top 3 results
    BuildLetE(String, bool),
    /// Build MData from top result
    BuildMData,
    /// Build Proj from top result
    BuildProj(String, u64),
}

impl<'a> CompactedRegion<'a> {
    /// Read an Expr object at a file offset (iterative to avoid stack overflow)
    pub fn read_expr_at(&self, offset: usize) -> OleanResult<ParsedExpr> {
        // Convert offset to pointer for the unified parsing loop
        let ptr = self.offset_to_ptr(offset);
        self.read_expr_iterative(ptr)
    }

    /// Iterative expression parser to avoid stack overflow on deeply nested expressions
    fn read_expr_iterative(&self, initial_ptr: u64) -> OleanResult<ParsedExpr> {
        let mut work: Vec<ExprWork> = vec![ExprWork::Parse(initial_ptr)];
        let mut results: Vec<ParsedExpr> = Vec::new();

        // Depth limit to prevent infinite loops
        let mut iterations = 0usize;
        const MAX_ITERATIONS: usize = 2_000_000_000;

        while let Some(item) = work.pop() {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return Err(OleanError::Region("Expression too complex".into()));
            }

            match item {
                ExprWork::Parse(ptr) => {
                    // Handle scalar/null pointers
                    if is_scalar(ptr) {
                        results.push(ParsedExpr::BVar(unbox_scalar(ptr)));
                        continue;
                    }
                    if !is_ptr(ptr) {
                        return Err(OleanError::Region("Null expression pointer".into()));
                    }

                    let offset = self.ptr_to_offset(ptr)?;
                    let header = self.read_header_at(offset)?;
                    let field_base = offset + 8;
                    let scalar_base = field_base + header.other as usize * 8;

                    Self::require_expr_fields(&header, offset)?;

                    match header.tag {
                        expr_tags::BVAR => {
                            let idx_ptr = self.read_u64_at(field_base)?;
                            let idx = if is_scalar(idx_ptr) {
                                unbox_scalar(idx_ptr)
                            } else if is_ptr(idx_ptr) {
                                self.read_nat_value(idx_ptr)?
                            } else {
                                0
                            };
                            results.push(ParsedExpr::BVar(idx));
                        }

                        expr_tags::FVAR => {
                            let id_ptr = self.read_u64_at(field_base)?;
                            let name = self.resolve_name_ptr(id_ptr)?;
                            results.push(ParsedExpr::FVar(name));
                        }

                        expr_tags::MVAR => {
                            let id_ptr = self.read_u64_at(field_base)?;
                            let name = self.resolve_name_ptr(id_ptr)?;
                            results.push(ParsedExpr::MVar(name));
                        }

                        expr_tags::SORT => {
                            let level_ptr = self.read_u64_at(field_base)?;
                            let level = self.resolve_level_ptr(level_ptr, 0)?;
                            results.push(ParsedExpr::Sort(level));
                        }

                        expr_tags::CONST => {
                            let name_ptr = self.read_u64_at(field_base)?;
                            let levels_ptr = self.read_u64_at(field_base + 8)?;
                            let name = self.resolve_name_ptr(name_ptr)?;
                            let levels = self.read_level_list(levels_ptr)?;
                            results.push(ParsedExpr::Const(name, levels));
                        }

                        expr_tags::LIT => {
                            let lit_ptr = self.read_u64_at(field_base)?;
                            let lit = self.read_literal(lit_ptr)?;
                            results.push(ParsedExpr::Lit(lit));
                        }

                        expr_tags::APP => {
                            let fn_ptr = self.read_u64_at(field_base)?;
                            let arg_ptr = self.read_u64_at(field_base + 8)?;
                            // Push build instruction, then children (arg on top when popped)
                            work.push(ExprWork::BuildApp);
                            work.push(ExprWork::Parse(arg_ptr));
                            work.push(ExprWork::Parse(fn_ptr));
                        }

                        expr_tags::LAM => {
                            let name_ptr = self.read_u64_at(field_base)?;
                            let type_ptr = self.read_u64_at(field_base + 8)?;
                            let body_ptr = self.read_u64_at(field_base + 16)?;
                            let binder_name = self.resolve_name_ptr(name_ptr)?;
                            let binder_info_byte = self.bytes_at(scalar_base, 1)?[0] & 0x07;
                            let binder_info = ParsedBinderInfo::from_u8(binder_info_byte);
                            // Push build, then body, then type (type first on results stack)
                            work.push(ExprWork::BuildLam(binder_name, binder_info));
                            work.push(ExprWork::Parse(body_ptr));
                            work.push(ExprWork::Parse(type_ptr));
                        }

                        expr_tags::FORALL_E => {
                            let name_ptr = self.read_u64_at(field_base)?;
                            let type_ptr = self.read_u64_at(field_base + 8)?;
                            let body_ptr = self.read_u64_at(field_base + 16)?;
                            let binder_name = self.resolve_name_ptr(name_ptr)?;
                            let binder_info_byte = self.bytes_at(scalar_base, 1)?[0] & 0x07;
                            let binder_info = ParsedBinderInfo::from_u8(binder_info_byte);
                            work.push(ExprWork::BuildForallE(binder_name, binder_info));
                            work.push(ExprWork::Parse(body_ptr));
                            work.push(ExprWork::Parse(type_ptr));
                        }

                        expr_tags::LET_E => {
                            let name_ptr = self.read_u64_at(field_base)?;
                            let type_ptr = self.read_u64_at(field_base + 8)?;
                            let value_ptr = self.read_u64_at(field_base + 16)?;
                            let body_ptr = self.read_u64_at(field_base + 24)?;
                            let decl_name = self.resolve_name_ptr(name_ptr)?;
                            let nondep = self.bytes_at(scalar_base, 1)?[0] != 0;
                            // Order: type, value, body -> results stack has body on top
                            work.push(ExprWork::BuildLetE(decl_name, nondep));
                            work.push(ExprWork::Parse(body_ptr));
                            work.push(ExprWork::Parse(value_ptr));
                            work.push(ExprWork::Parse(type_ptr));
                        }

                        expr_tags::MDATA => {
                            let expr_ptr = self.read_u64_at(field_base + 8)?;
                            work.push(ExprWork::BuildMData);
                            work.push(ExprWork::Parse(expr_ptr));
                        }

                        expr_tags::PROJ => {
                            let type_name_ptr = self.read_u64_at(field_base)?;
                            let idx_ptr = self.read_u64_at(field_base + 8)?;
                            let struct_ptr = self.read_u64_at(field_base + 16)?;
                            let type_name = self.resolve_name_ptr(type_name_ptr)?;
                            let idx = if is_scalar(idx_ptr) {
                                unbox_scalar(idx_ptr)
                            } else if is_ptr(idx_ptr) {
                                self.read_nat_value(idx_ptr).unwrap_or(0)
                            } else {
                                0
                            };
                            work.push(ExprWork::BuildProj(type_name, idx));
                            work.push(ExprWork::Parse(struct_ptr));
                        }

                        _ => {
                            return Err(OleanError::InvalidObjectTag {
                                tag: header.tag,
                                offset,
                            })
                        }
                    }
                }

                ExprWork::BuildApp => {
                    let arg = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "App arg",
                    })?;
                    let func = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "App func",
                    })?;
                    results.push(ParsedExpr::App(Box::new(func), Box::new(arg)));
                }

                ExprWork::BuildLam(name, info) => {
                    let body = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "Lam body",
                    })?;
                    let ty = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "Lam type",
                    })?;
                    results.push(ParsedExpr::Lam(name, Box::new(ty), Box::new(body), info));
                }

                ExprWork::BuildForallE(name, info) => {
                    let body = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "ForallE body",
                    })?;
                    let ty = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "ForallE type",
                    })?;
                    results.push(ParsedExpr::ForallE(
                        name,
                        Box::new(ty),
                        Box::new(body),
                        info,
                    ));
                }

                ExprWork::BuildLetE(name, nondep) => {
                    let body = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "LetE body",
                    })?;
                    let val = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "LetE value",
                    })?;
                    let ty = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "LetE type",
                    })?;
                    results.push(ParsedExpr::LetE(
                        name,
                        Box::new(ty),
                        Box::new(val),
                        Box::new(body),
                        nondep,
                    ));
                }

                ExprWork::BuildMData => {
                    let inner = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "MData inner",
                    })?;
                    results.push(ParsedExpr::MData(Box::new(inner)));
                }

                ExprWork::BuildProj(name, idx) => {
                    let inner = results.pop().ok_or(OleanError::ExprStackUnderflow {
                        operation: "Proj inner",
                    })?;
                    results.push(ParsedExpr::Proj(name, idx, Box::new(inner)));
                }
            }
        }

        debug_assert_eq!(results.len(), 1);
        results.pop().ok_or(OleanError::ExprStackUnderflow {
            operation: "final result",
        })
    }

    /// Validate that an `Expr` constructor object declares enough pointer
    /// fields to satisfy its tag before any field is read.
    ///
    /// Lean's compacted region stores the number of pointer fields in the
    /// object header's `other` byte. Each `Expr` constructor has a fixed
    /// pointer-field arity:
    ///
    /// | tag | constructor | required boxed pointer fields |
    /// |-----|-------------|-------------------------------|
    /// | 0   | `bvar`      | 0 (index is an unboxed scalar) |
    /// | 1   | `fvar`      | 1 |
    /// | 2   | `mvar`      | 1 |
    /// | 3   | `sort`      | 1 |
    /// | 4   | `const`     | 2 |
    /// | 5   | `app`       | 2 |
    /// | 6   | `lam`       | 3 (+ `binderInfo` scalar) |
    /// | 7   | `forallE`   | 3 (+ `binderInfo` scalar) |
    /// | 8   | `letE`      | 4 (+ `nondep` scalar) |
    /// | 9   | `lit`       | 1 |
    /// | 10  | `mdata`     | 2 |
    /// | 11  | `proj`      | 0 enforced (`idx` is an unboxed scalar) |
    ///
    /// `bvar` and `proj` store at least one inline unboxed scalar (`deBruijnIndex`
    /// / `idx`) rather than only boxed pointer fields, so their `other` byte does
    /// not match a fixed boxed-field arity; they are exempt from the requirement.
    ///
    /// A malformed or truncated `.olean` can present an `Expr` tag whose
    /// `other` is smaller than its arity. Without this check the iterative
    /// reader would (a) read bytes belonging to an adjacent object as a child
    /// expression / name / level pointer, and (b) for the binder constructors
    /// compute `scalar_base = field_base + other * 8` from the wrong `other`,
    /// reading the binder-info / nondep scalar from the wrong location —
    /// silently fabricating an expression rather than failing. Fail closed
    /// with a typed [`OleanError::Region`] instead. This mirrors the `Level`
    /// constructor field-count guard.
    ///
    /// # ENSURES
    /// - Returns `Ok(())` for non-`Expr` tags (rejected by the caller's match)
    ///   and for `Expr` tags whose `header.other >= arity`.
    /// - Returns `OleanError::Region` describing the mismatch otherwise.
    fn require_expr_fields(header: &crate::region::ObjectHeader, offset: usize) -> OleanResult<()> {
        let expected: u8 = match header.tag {
            // `bvar`'s de Bruijn index is stored as an unboxed `usize` scalar in
            // the object's scalar region, not as a boxed pointer field, so a real
            // `bvar` object legitimately reports `other = 0`. It is therefore
            // excluded from the boxed-pointer-field requirement.
            expr_tags::FVAR | expr_tags::MVAR | expr_tags::SORT | expr_tags::LIT => 1,
            expr_tags::CONST | expr_tags::APP | expr_tags::MDATA => 2,
            expr_tags::LAM | expr_tags::FORALL_E => 3,
            expr_tags::LET_E => 4,
            // Unknown tags are rejected by the caller's match arm. `bvar`,
            // `proj`, and any future tag fall through with no requirement.
            _ => return Ok(()),
        };
        if header.other < expected {
            return Err(OleanError::Region(format!(
                "malformed Expr: tag {} at offset {} declares {} field(s), expected at least {}",
                header.tag, offset, header.other, expected
            )));
        }
        Ok(())
    }

    /// Resolve a name pointer.
    ///
    /// Returns an error for invalid pointers (neither scalar nor valid pointer).
    /// This is intentional - invalid pointers in critical loading paths indicate
    /// data corruption and should be detected early.
    ///
    /// For diagnostic functions where graceful degradation is acceptable,
    /// consider wrapping this call with `.unwrap_or_default()`.
    pub fn resolve_name_ptr(&self, ptr: u64) -> OleanResult<String> {
        if is_scalar(ptr) {
            // Name.anonymous encoded as scalar 0
            return Ok(String::new());
        }

        if !is_ptr(ptr) {
            return Err(OleanError::Region(format!(
                "Invalid name pointer: {ptr:#x} (neither scalar nor pointer)"
            )));
        }

        let offset = self.ptr_to_offset(ptr)?;
        self.read_name_at(offset)
    }

    /// Read a list of levels
    pub(crate) fn read_level_list(&self, ptr: u64) -> OleanResult<Vec<ParsedLevel>> {
        const MAX_ITERATIONS: usize = 10_000;

        let mut levels = Vec::new();
        let mut current_ptr = ptr;

        for _i in 0..MAX_ITERATIONS {
            if is_scalar(current_ptr) {
                // Empty list is often scalar 0 (pointer value 1)
                return Ok(levels);
            }

            if !is_ptr(current_ptr) {
                return Ok(levels);
            }

            let offset = self.ptr_to_offset(current_ptr)?;
            let header = self.read_header_at(offset)?;

            // List has two constructors:
            // - nil (tag 0, 0 fields)
            // - cons (tag 1, 2 fields: head, tail)
            match (header.tag, header.other) {
                (0, 0) => {
                    // nil
                    return Ok(levels);
                }
                (1, 2) => {
                    // cons
                    let head_ptr = self.read_u64_at(offset + 8)?;
                    let tail_ptr = self.read_u64_at(offset + 16)?;

                    let level = self.resolve_level_ptr(head_ptr, 0)?;
                    levels.push(level);

                    current_ptr = tail_ptr;
                }
                _ => {
                    // Unknown list structure
                    return Ok(levels);
                }
            }
        }

        // Check if list terminated exactly at the limit (valid case)
        if is_scalar(current_ptr) || !is_ptr(current_ptr) {
            return Ok(levels);
        }

        // List continues beyond limit - this is the error case
        Err(OleanError::IterationLimitExceeded {
            limit: MAX_ITERATIONS,
            context: "level list",
        })
    }

    /// Read a Literal (Nat or String)
    pub(crate) fn read_literal(&self, ptr: u64) -> OleanResult<ParsedLiteral> {
        if is_scalar(ptr) {
            // Small Nat encoded as scalar
            return Ok(ParsedLiteral::Nat(BigNat::from_u64(unbox_scalar(ptr))));
        }

        if !is_ptr(ptr) {
            return Err(OleanError::Region(format!(
                "Invalid literal pointer: {ptr:#x} (neither scalar nor pointer)"
            )));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        // Literal has two constructors:
        // - natVal (tag 0, 1 field: Nat)
        // - strVal (tag 1, 1 field: String)
        match header.tag {
            0 => {
                // natVal - use read_bignat_value for arbitrary precision support
                let nat_ptr = self.read_u64_at(offset + 8)?;
                let val = self.read_bignat_value(nat_ptr)?;
                Ok(ParsedLiteral::Nat(val))
            }
            1 => {
                // strVal
                let str_ptr = self.read_u64_at(offset + 8)?;
                if is_ptr(str_ptr) {
                    let str_off = self.ptr_to_offset(str_ptr)?;
                    let s = self.read_lean_string_at(str_off)?;
                    Ok(ParsedLiteral::String(s.to_string()))
                } else {
                    Ok(ParsedLiteral::String(String::new()))
                }
            }
            tags::STRING => {
                // Direct string (not wrapped in Literal)
                let s = self.read_lean_string_at(offset)?;
                Ok(ParsedLiteral::String(s.to_string()))
            }
            _ => Err(OleanError::InvalidObjectTag {
                tag: header.tag,
                offset,
            }),
        }
    }

    /// Find expression-like objects in the file (exploratory)
    pub fn find_expr_objects(&self) -> Vec<(usize, u8, u8)> {
        let mut results = Vec::new();

        let mut offset = 64;
        while offset + 8 < self.data.len() {
            if let Ok(header) = self.read_header_at(offset) {
                // Check for Expr tags with expected field counts
                let is_expr = matches!(
                    (header.tag, header.other),
                    (expr_tags::BVAR, 0 | 1)
                        | (
                            expr_tags::FVAR | expr_tags::MVAR | expr_tags::SORT | expr_tags::LIT,
                            1
                        )
                        | (expr_tags::CONST | expr_tags::APP | expr_tags::MDATA, 2)
                        | (expr_tags::LAM | expr_tags::FORALL_E, 3)
                        | (expr_tags::LET_E, 4)
                        | (expr_tags::PROJ, 2 | 3)
                );

                if is_expr {
                    results.push((offset, header.tag, header.other));
                }
            }
            offset += 8;
        }

        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_lean_lib_path() -> Option<std::path::PathBuf> {
        let home = std::env::var("HOME").ok()?;
        let elan_path = std::path::PathBuf::from(home).join(".elan/toolchains");

        if elan_path.exists() {
            for entry in std::fs::read_dir(&elan_path).ok()? {
                let entry = entry.ok()?;
                let name = entry.file_name();
                if name.to_string_lossy().contains("lean4") {
                    return Some(entry.path().join("lib/lean"));
                }
            }
        }
        None
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Unit tests for ParsedBinderInfo
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_parsed_binder_info_from_u8() {
        assert_eq!(ParsedBinderInfo::from_u8(0), ParsedBinderInfo::Default);
        assert_eq!(ParsedBinderInfo::from_u8(1), ParsedBinderInfo::Implicit);
        assert_eq!(
            ParsedBinderInfo::from_u8(2),
            ParsedBinderInfo::StrictImplicit
        );
        assert_eq!(ParsedBinderInfo::from_u8(3), ParsedBinderInfo::InstImplicit);
        // Unknown values should return Unknown variant with preserved tag
        assert_eq!(ParsedBinderInfo::from_u8(4), ParsedBinderInfo::Unknown(4));
        assert_eq!(
            ParsedBinderInfo::from_u8(255),
            ParsedBinderInfo::Unknown(255)
        );
    }

    #[test]
    fn test_parsed_binder_info_is_unknown() {
        assert!(!ParsedBinderInfo::Default.is_unknown());
        assert!(!ParsedBinderInfo::Implicit.is_unknown());
        assert!(!ParsedBinderInfo::StrictImplicit.is_unknown());
        assert!(!ParsedBinderInfo::InstImplicit.is_unknown());
        assert!(ParsedBinderInfo::Unknown(42).is_unknown());
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Unit tests for ParsedExpr::kind()
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_parsed_expr_kind() {
        let expr = ParsedExpr::BVar(0);
        assert_eq!(expr.kind(), "bvar");

        let expr = ParsedExpr::Const("Nat".to_string(), vec![]);
        assert_eq!(expr.kind(), "const");
    }

    #[test]
    fn test_parsed_expr_kind_all_variants() {
        // BVar
        assert_eq!(ParsedExpr::BVar(42).kind(), "bvar");
        // FVar
        assert_eq!(ParsedExpr::FVar("x".to_string()).kind(), "fvar");
        // MVar
        assert_eq!(ParsedExpr::MVar("?m".to_string()).kind(), "mvar");
        // Sort
        assert_eq!(ParsedExpr::Sort(ParsedLevel::Zero).kind(), "sort");
        // Const
        assert_eq!(ParsedExpr::Const("f".to_string(), vec![]).kind(), "const");
        // App
        assert_eq!(
            ParsedExpr::App(
                Box::new(ParsedExpr::Const("f".to_string(), vec![])),
                Box::new(ParsedExpr::BVar(0))
            )
            .kind(),
            "app"
        );
        // Lam
        assert_eq!(
            ParsedExpr::Lam(
                "x".to_string(),
                Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
                Box::new(ParsedExpr::BVar(0)),
                ParsedBinderInfo::Default
            )
            .kind(),
            "lam"
        );
        // ForallE
        assert_eq!(
            ParsedExpr::ForallE(
                "x".to_string(),
                Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
                Box::new(ParsedExpr::BVar(0)),
                ParsedBinderInfo::Default
            )
            .kind(),
            "forallE"
        );
        // LetE
        assert_eq!(
            ParsedExpr::LetE(
                "x".to_string(),
                Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
                Box::new(ParsedExpr::BVar(0)),
                Box::new(ParsedExpr::BVar(0)),
                false
            )
            .kind(),
            "letE"
        );
        // Lit
        assert_eq!(
            ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(42))).kind(),
            "lit"
        );
        // MData (metadata wraps expression, kind() returns "mdata")
        assert_eq!(
            ParsedExpr::MData(Box::new(ParsedExpr::BVar(0))).kind(),
            "mdata"
        );
        // Proj
        assert_eq!(
            ParsedExpr::Proj("Prod".to_string(), 0, Box::new(ParsedExpr::BVar(0))).kind(),
            "proj"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Unit tests for ParsedExpr::depth()
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_parsed_expr_depth_atomic() {
        // All atomic expressions have depth 0
        assert_eq!(ParsedExpr::BVar(0).depth(), 0);
        assert_eq!(ParsedExpr::FVar("x".to_string()).depth(), 0);
        assert_eq!(ParsedExpr::MVar("?m".to_string()).depth(), 0);
        assert_eq!(ParsedExpr::Sort(ParsedLevel::Zero).depth(), 0);
        assert_eq!(ParsedExpr::Const("Nat".to_string(), vec![]).depth(), 0);
        assert_eq!(
            ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(42))).depth(),
            0
        );
    }

    #[test]
    fn test_parsed_expr_depth_nested() {
        let nat = ParsedExpr::Const("Nat".to_string(), vec![]);
        let var0 = ParsedExpr::BVar(0);

        // App depth is 1 + max of subexpressions
        let app = ParsedExpr::App(Box::new(nat.clone()), Box::new(var0.clone()));
        assert_eq!(app.depth(), 1);

        // Nested app: f (g x) has depth 2
        let inner = ParsedExpr::App(
            Box::new(ParsedExpr::Const("g".to_string(), vec![])),
            Box::new(ParsedExpr::BVar(0)),
        );
        let outer = ParsedExpr::App(
            Box::new(ParsedExpr::Const("f".to_string(), vec![])),
            Box::new(inner),
        );
        assert_eq!(outer.depth(), 2);
    }

    #[test]
    fn test_parsed_expr_depth_binders() {
        let nat = ParsedExpr::Const("Nat".to_string(), vec![]);
        let var0 = ParsedExpr::BVar(0);

        // Lam (x : Nat) => x has depth 1
        let lam = ParsedExpr::Lam(
            "x".to_string(),
            Box::new(nat.clone()),
            Box::new(var0.clone()),
            ParsedBinderInfo::Default,
        );
        assert_eq!(lam.depth(), 1);

        // ForallE (x : Nat) → x has depth 1
        let forall = ParsedExpr::ForallE(
            "x".to_string(),
            Box::new(nat.clone()),
            Box::new(var0.clone()),
            ParsedBinderInfo::Default,
        );
        assert_eq!(forall.depth(), 1);

        // LetE x : Nat := 0 in x has depth 1
        let let_e = ParsedExpr::LetE(
            "x".to_string(),
            Box::new(nat.clone()),
            Box::new(ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(0)))),
            Box::new(var0.clone()),
            false,
        );
        assert_eq!(let_e.depth(), 1);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Integration tests (require Lean4 installation)
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_find_expr_objects_in_prelude() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let prelude_path = lib_path.join("Init/Prelude.olean");
        if !prelude_path.exists() {
            eprintln!("Skipping test: Init/Prelude.olean not found at {prelude_path:?}");
            return;
        }

        let bytes = std::fs::read(&prelude_path).expect("Failed to read file");
        let header = crate::parse_header(&bytes).expect("Failed to parse header");
        let region = CompactedRegion::new(&bytes, header.base_addr);

        let exprs = region.find_expr_objects();
        println!("Found {} potential Expr objects", exprs.len());

        // Group by tag
        let mut by_tag: std::collections::HashMap<u8, usize> = std::collections::HashMap::new();
        for (_, tag, _) in &exprs {
            *by_tag.entry(*tag).or_insert(0) += 1;
        }

        println!("Expression types found:");
        for (tag, count) in &by_tag {
            let name = match *tag {
                expr_tags::BVAR => "bvar",
                expr_tags::FVAR => "fvar",
                expr_tags::MVAR => "mvar",
                expr_tags::SORT => "sort",
                expr_tags::CONST => "const",
                expr_tags::APP => "app",
                expr_tags::LAM => "lam",
                expr_tags::FORALL_E => "forallE",
                expr_tags::LET_E => "letE",
                expr_tags::LIT => "lit",
                expr_tags::MDATA => "mdata",
                expr_tags::PROJ => "proj",
                _ => "unknown",
            };
            println!("  {name}: {count}");
        }

        let mut bvar_shapes: std::collections::HashMap<(u8, u16), usize> =
            std::collections::HashMap::new();
        for (off, tag, _) in &exprs {
            if *tag == expr_tags::BVAR {
                if let Ok(h) = region.read_header_at(*off) {
                    *bvar_shapes.entry((h.other, h.cs_sz)).or_insert(0) += 1;
                }
            }
        }
        let mut shapes: Vec<_> = bvar_shapes.into_iter().collect();
        shapes.sort_by_key(|(_, count)| std::cmp::Reverse(*count));
        println!("Top bvar shapes (other, cs_sz):");
        for ((other, cs_sz), count) in shapes.iter().take(5) {
            println!("  ({other}, {cs_sz}) -> {count}");
        }

        if let Some((offset, tag, other)) = exprs.iter().find(|(off, tag, _)| {
            *tag == expr_tags::BVAR
                && region
                    .read_header_at(*off)
                    .map(|h| h.cs_sz > 0)
                    .unwrap_or(false)
        }) {
            if let Ok(header) = region.read_header_at(*offset) {
                if let Ok(bytes) = region.bytes_at(*offset, header.cs_sz as usize) {
                    println!(
                        "Sample bvar offset={}, tag={}, other={}, cs_sz={}, bytes={:x?}",
                        offset, tag, other, header.cs_sz, bytes
                    );
                }
            }
        }

        // We expect to find many expression objects
        assert!(
            exprs.len() > 100,
            "Expected > 100 expr objects, got {}",
            exprs.len()
        );
    }

    #[test]
    fn test_read_sample_exprs() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let prelude_path = lib_path.join("Init/Prelude.olean");
        if !prelude_path.exists() {
            return;
        }

        let bytes = std::fs::read(&prelude_path).expect("Failed to read file");
        let header = crate::parse_header(&bytes).expect("Failed to parse header");
        let region = CompactedRegion::new(&bytes, header.base_addr);

        let exprs = region.find_expr_objects();

        // Try to read the first few expressions of each type
        let mut successes = 0;
        let mut failures = 0;

        for (offset, tag, _) in exprs.iter().take(100) {
            match region.read_expr_at(*offset) {
                Ok(expr) => {
                    successes += 1;
                    if successes <= 10 {
                        println!("offset {}: tag {} -> {:?}", offset, tag, expr.kind());
                    }
                }
                Err(_e) => {
                    failures += 1;
                }
            }
        }

        println!("Read {successes} expressions successfully, {failures} failures");

        // We should be able to read at least some expressions
        assert!(
            successes > 0,
            "Should read at least some expressions, got {successes} successes and {failures} failures"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Synthetic-region unit tests for read_literal (Literal.natVal / Literal.strVal)
    //
    // Lean 4 core `Expr.lit` only carries `Literal`, whose two constructors are:
    //   inductive Literal where
    //     | natVal (val : Nat)     -- tag 0
    //     | strVal (val : String)  -- tag 1
    //
    // There is no Char or Float `Literal` in Lean 4 core. Char literals are
    // `Char.ofNat n` applications and Float literals come from
    // `OfScientific.ofScientific` applications. The tests below pin both the
    // existing natVal/strVal deserialization (including multi-limb BigNat and
    // tricky strings) and document that Char/Float are ordinary App/Const trees.
    // ════════════════════════════════════════════════════════════════════════════

    /// Base address used for synthetic region fixtures. Must be even and large
    /// enough that no in-region offset is mistaken for a tagged scalar.
    const TEST_BASE_ADDR: u64 = 0x0010_0000;

    /// Box a small scalar value the way Lean's runtime does: `2 * v + 1`.
    fn boxed_scalar(v: u64) -> u64 {
        (v << 1) | 1
    }

    /// Write an 8-byte object header (rc, cs_sz, other, tag) at `offset`.
    fn write_header(data: &mut [u8], offset: usize, other: u8, tag: u8) {
        data[offset..offset + 4].copy_from_slice(&0i32.to_le_bytes()); // rc
        data[offset + 4..offset + 6].copy_from_slice(&0u16.to_le_bytes()); // cs_sz
        data[offset + 6] = other;
        data[offset + 7] = tag;
    }

    /// Write a Lean String object at `offset` and return the next free offset.
    ///
    /// Layout: header(8) + m_size(8) + m_capacity(8) + m_length(8) + bytes + NUL.
    fn write_lean_string(data: &mut [u8], offset: usize, s: &str) -> usize {
        let bytes = s.as_bytes();
        let m_size = (bytes.len() + 1) as u64; // include NUL terminator
        write_header(data, offset, 0, tags::STRING);
        data[offset + 8..offset + 16].copy_from_slice(&m_size.to_le_bytes());
        data[offset + 16..offset + 24].copy_from_slice(&m_size.to_le_bytes()); // capacity
        data[offset + 24..offset + 32].copy_from_slice(&(bytes.len() as u64).to_le_bytes()); // length
        data[offset + 32..offset + 32 + bytes.len()].copy_from_slice(bytes);
        // trailing NUL is already zero-initialized
        offset + 32 + m_size as usize
    }

    /// Write an MPZ Nat object at `offset` from little-endian limbs and return
    /// the next free offset. Mirrors the layout read by `read_bignat_value`:
    /// header(8) + _mp_alloc(i32 @ +8) + _mp_size(i32 @ +12) + _mp_d(ptr @ +16)
    /// + digits (@ +24).
    fn write_mpz(data: &mut [u8], offset: usize, limbs: &[u64]) -> usize {
        write_header(data, offset, 0, tags::MPZ);
        let size = limbs.len() as i32;
        data[offset + 8..offset + 12].copy_from_slice(&size.to_le_bytes()); // alloc
        data[offset + 12..offset + 16].copy_from_slice(&size.to_le_bytes()); // size
                                                                             // _mp_d pointer (@ +16) left zero; digits are inline starting at +24
        for (i, limb) in limbs.iter().enumerate() {
            let at = offset + 24 + i * 8;
            data[at..at + 8].copy_from_slice(&limb.to_le_bytes());
        }
        offset + 24 + limbs.len() * 8
    }

    #[test]
    fn test_read_literal_natval_small_scalar_roundtrips() {
        // natVal with a small Nat encoded as a boxed scalar field.
        let mut data = vec![0u8; 128];
        let lit_off = 64;
        write_header(&mut data, lit_off, 1, 0); // Literal.natVal, 1 field
        data[lit_off + 8..lit_off + 16].copy_from_slice(&boxed_scalar(42).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect("natVal literal should parse");
        assert_eq!(lit, ParsedLiteral::Nat(BigNat::from_u64(42)));
    }

    #[test]
    fn test_read_literal_natval_zero_scalar_roundtrips() {
        let mut data = vec![0u8; 128];
        let lit_off = 64;
        write_header(&mut data, lit_off, 1, 0);
        data[lit_off + 8..lit_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect("natVal 0 should parse");
        assert_eq!(lit, ParsedLiteral::Nat(BigNat::from_u64(0)));
    }

    #[test]
    fn test_read_literal_bare_scalar_is_natval() {
        // A bare boxed scalar (not pointing at a Literal object) is read as a
        // small Nat literal directly.
        let data = vec![0u8; 64];
        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(boxed_scalar(7))
            .expect("scalar literal should parse");
        assert_eq!(lit, ParsedLiteral::Nat(BigNat::from_u64(7)));
    }

    #[test]
    fn test_read_literal_natval_multilimb_bignat_roundtrips() {
        // natVal pointing at an MPZ object with two limbs -> BigNat::Big.
        // Place the MPZ first, then the Literal that references it.
        let mut data = vec![0u8; 256];
        let mpz_off = 64;
        let limbs = [0x1122_3344_5566_7788u64, 0x0099_aabb_ccdd_eeffu64];
        let after_mpz = write_mpz(&mut data, mpz_off, &limbs);

        // Align the literal object to the next 8-byte boundary.
        let lit_off = after_mpz.next_multiple_of(8);
        write_header(&mut data, lit_off, 1, 0); // Literal.natVal
        let region_first = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let mpz_ptr = region_first.offset_to_ptr(mpz_off);
        data[lit_off + 8..lit_off + 16].copy_from_slice(&mpz_ptr.to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect("multi-limb natVal should parse");
        assert_eq!(lit, ParsedLiteral::Nat(BigNat::from_limbs(limbs.to_vec())));
        // And confirm it does NOT fit in u64 (genuinely big).
        match lit {
            ParsedLiteral::Nat(n) => assert!(n.to_u64().is_none(), "two-limb value must be Big"),
            other => panic!("expected Nat literal, got {other:?}"),
        }
    }

    #[test]
    fn test_read_literal_strval_unicode_roundtrips() {
        let s = "héllo→世界";
        let mut data = vec![0u8; 256];
        let str_off = 64;
        let after_str = write_lean_string(&mut data, str_off, s);

        let lit_off = after_str.next_multiple_of(8);
        write_header(&mut data, lit_off, 1, 1); // Literal.strVal, 1 field
        let region_first = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let str_ptr = region_first.offset_to_ptr(str_off);
        data[lit_off + 8..lit_off + 16].copy_from_slice(&str_ptr.to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect("unicode strVal should parse");
        assert_eq!(lit, ParsedLiteral::String(s.to_string()));
    }

    #[test]
    fn test_read_literal_strval_embedded_quotes_roundtrips() {
        let s = "say \"hi\"\tand\\done";
        let mut data = vec![0u8; 256];
        let str_off = 64;
        let after_str = write_lean_string(&mut data, str_off, s);

        let lit_off = after_str.next_multiple_of(8);
        write_header(&mut data, lit_off, 1, 1);
        let region_first = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let str_ptr = region_first.offset_to_ptr(str_off);
        data[lit_off + 8..lit_off + 16].copy_from_slice(&str_ptr.to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect("strVal with quotes/escapes should parse");
        assert_eq!(lit, ParsedLiteral::String(s.to_string()));
    }

    #[test]
    fn test_read_literal_strval_empty_scalar_field_is_empty_string() {
        // strVal whose String field is a (non-pointer) scalar should degrade to
        // an empty string rather than erroring.
        let mut data = vec![0u8; 128];
        let lit_off = 64;
        write_header(&mut data, lit_off, 1, 1);
        data[lit_off + 8..lit_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect("strVal with scalar field should parse as empty");
        assert_eq!(lit, ParsedLiteral::String(String::new()));
    }

    #[test]
    fn test_read_literal_direct_string_object_is_strval() {
        // A pointer directly at a String object (tag 249), not wrapped in a
        // Literal constructor, is still read as a String literal.
        let mut data = vec![0u8; 128];
        let str_off = 64;
        write_lean_string(&mut data, str_off, "direct");

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit = region
            .read_literal(region.offset_to_ptr(str_off))
            .expect("direct String object should parse as strVal");
        assert_eq!(lit, ParsedLiteral::String("direct".to_string()));
    }

    #[test]
    fn test_read_literal_null_pointer_errors() {
        let data = vec![0u8; 64];
        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        // ptr == 0 is neither scalar nor a valid pointer.
        let err = region
            .read_literal(0)
            .expect_err("null literal pointer must error");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    #[test]
    fn test_read_literal_unknown_constructor_tag_errors() {
        // A constructor object with a tag that is neither natVal (0), strVal (1),
        // nor a String (249) must be rejected as an invalid Literal.
        let mut data = vec![0u8; 128];
        let lit_off = 64;
        write_header(&mut data, lit_off, 1, 7); // bogus Literal tag 7

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_literal(region.offset_to_ptr(lit_off))
            .expect_err("unknown literal tag must error");
        assert!(
            matches!(err, OleanError::InvalidObjectTag { tag: 7, .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn test_lit_expr_wraps_natval_literal() {
        // End-to-end: an Expr.lit (tag 9) referencing a natVal Literal parses
        // into ParsedExpr::Lit(ParsedLiteral::Nat(..)).
        let mut data = vec![0u8; 256];
        let lit_off = 64;
        write_header(&mut data, lit_off, 1, 0); // Literal.natVal
        data[lit_off + 8..lit_off + 16].copy_from_slice(&boxed_scalar(99).to_le_bytes());

        let expr_off = 96;
        write_header(&mut data, expr_off, 1, expr_tags::LIT); // Expr.lit, 1 field
        let region_first = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit_ptr = region_first.offset_to_ptr(lit_off);
        data[expr_off + 8..expr_off + 16].copy_from_slice(&lit_ptr.to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(expr_off)
            .expect("Expr.lit should parse");
        assert_eq!(
            expr,
            ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(99)))
        );
        assert_eq!(expr.kind(), "lit");
    }

    /// Documents that Char literals are NOT `Expr.lit`: in Lean 4 core a char
    /// such as `'A'` elaborates to `Char.ofNat 65`, i.e. an application of the
    /// constant `Char.ofNat` to a `Literal.natVal`. The importer therefore
    /// surfaces it as a `ParsedExpr::App(Const, Lit(Nat))`, never a Char literal.
    #[test]
    fn test_char_surfaces_as_char_ofnat_application_not_literal() {
        // Layout: a natVal Literal (65), the Expr.lit wrapping it, a Const
        // `Char.ofNat`, and the App applying the const to the lit.
        let mut data = vec![0u8; 512];

        // Name "Char.ofNat" — built as Name.str chain is overkill here; we only
        // need the App/Const shape, so use anonymous-name scalar for simplicity
        // and assert structure rather than the resolved name string.
        let lit_off = 64;
        write_header(&mut data, lit_off, 1, 0); // Literal.natVal 65
        data[lit_off + 8..lit_off + 16].copy_from_slice(&boxed_scalar(65).to_le_bytes());

        let expr_lit_off = 96;
        write_header(&mut data, expr_lit_off, 1, expr_tags::LIT);
        let region0 = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let lit_ptr = region0.offset_to_ptr(lit_off);
        data[expr_lit_off + 8..expr_lit_off + 16].copy_from_slice(&lit_ptr.to_le_bytes());

        // Const node: name_ptr (anonymous scalar 0), levels_ptr (scalar nil).
        let const_off = 128;
        write_header(&mut data, const_off, 2, expr_tags::CONST);
        data[const_off + 8..const_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[const_off + 16..const_off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        // App node: fn = Const, arg = Expr.lit.
        let app_off = 160;
        write_header(&mut data, app_off, 2, expr_tags::APP);
        let region1 = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let const_ptr = region1.offset_to_ptr(const_off);
        let expr_lit_ptr = region1.offset_to_ptr(expr_lit_off);
        data[app_off + 8..app_off + 16].copy_from_slice(&const_ptr.to_le_bytes());
        data[app_off + 16..app_off + 24].copy_from_slice(&expr_lit_ptr.to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(app_off)
            .expect("Char.ofNat application should parse");

        // It is an App, with a Const head and a Nat-literal argument — NOT a
        // Char literal (no such variant exists in ParsedLiteral by design).
        match expr {
            ParsedExpr::App(head, arg) => {
                assert!(
                    matches!(*head, ParsedExpr::Const(_, _)),
                    "head must be Const"
                );
                assert_eq!(
                    *arg,
                    ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(65)))
                );
            }
            other => panic!("expected App(Const, Lit), got {other:?}"),
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Fail-closed field-count validation for Expr constructor objects.
    //
    // `read_expr_iterative` reads child-expr / name / level field pointers at fixed
    // `field_base + k*8` offsets, and (for the binder constructors) computes the
    // binder-info / nondep scalar position as `field_base + other*8`. A malformed or
    // truncated `.olean` that declares fewer pointer fields than a constructor's
    // arity would, without a guard, read bytes belonging to an adjacent object as a
    // child pointer (and place the scalar read at the wrong offset) — silently
    // fabricating an expression. These tests pin that each such object fails closed
    // with a typed `OleanError::Region`, mirroring the `Level` field-count guard.
    // ════════════════════════════════════════════════════════════════════════════

    /// A two-field `App` declaring only one field must fail closed rather than
    /// reading the adjacent word as its `arg` child expression.
    #[test]
    fn test_read_expr_app_insufficient_fields_returns_region_error() {
        let mut data = vec![0u8; 128];
        let app_off = 64;
        // App (tag 5) with other=1 but the reader needs two pointer fields.
        write_header(&mut data, app_off, 1, expr_tags::APP);
        // One plausible child word (scalar BVar 0) plus trailing zero bytes that
        // would be misread as the second child without the guard.
        data[app_off + 8..app_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(app_off)
            .expect_err("App with other<2 must be rejected");
        assert!(
            matches!(&err, OleanError::Region(msg) if msg.contains("malformed Expr")),
            "expected malformed-Expr Region error, got {err:?}"
        );
    }

    /// A `Const` declaring zero fields must fail closed (it needs name + levels).
    #[test]
    fn test_read_expr_const_zero_fields_returns_region_error() {
        let mut data = vec![0u8; 128];
        let const_off = 64;
        write_header(&mut data, const_off, 0, expr_tags::CONST);
        data[const_off + 8..const_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[const_off + 16..const_off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(const_off)
            .expect_err("Const with other=0 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// A `Sort` declaring zero fields must fail closed rather than reading the
    /// adjacent word as its universe level.
    #[test]
    fn test_read_expr_sort_zero_fields_returns_region_error() {
        let mut data = vec![0u8; 128];
        let sort_off = 64;
        write_header(&mut data, sort_off, 0, expr_tags::SORT);
        data[sort_off + 8..sort_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(sort_off)
            .expect_err("Sort with other=0 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// A `Lit` declaring zero fields must fail closed.
    #[test]
    fn test_read_expr_lit_zero_fields_returns_region_error() {
        let mut data = vec![0u8; 128];
        let lit_off = 64;
        write_header(&mut data, lit_off, 0, expr_tags::LIT);
        data[lit_off + 8..lit_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(lit_off)
            .expect_err("Lit with other=0 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// An `MData` declaring one field must fail closed: the reader follows the
    /// wrapped expression at the *second* slot (`field_base + 8`).
    #[test]
    fn test_read_expr_mdata_insufficient_fields_returns_region_error() {
        let mut data = vec![0u8; 128];
        let mdata_off = 64;
        write_header(&mut data, mdata_off, 1, expr_tags::MDATA);
        data[mdata_off + 8..mdata_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(mdata_off)
            .expect_err("MData with other<2 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// A `Lam` declaring two fields (instead of three) must fail closed. Beyond
    /// reading the adjacent word as `body`, an under-declared `other` would also
    /// place the `binderInfo` scalar read at the wrong offset.
    #[test]
    fn test_read_expr_lam_insufficient_fields_returns_region_error() {
        let mut data = vec![0u8; 192];
        let lam_off = 64;
        write_header(&mut data, lam_off, 2, expr_tags::LAM); // needs 3
        data[lam_off + 8..lam_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // name
        data[lam_off + 16..lam_off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // type
        data[lam_off + 24..lam_off + 32].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // would-be body

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(lam_off)
            .expect_err("Lam with other<3 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// A `ForallE` declaring two fields (instead of three) must fail closed.
    #[test]
    fn test_read_expr_forall_insufficient_fields_returns_region_error() {
        let mut data = vec![0u8; 192];
        let pi_off = 64;
        write_header(&mut data, pi_off, 2, expr_tags::FORALL_E); // needs 3
        data[pi_off + 8..pi_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[pi_off + 16..pi_off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[pi_off + 24..pi_off + 32].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(pi_off)
            .expect_err("ForallE with other<3 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// A `LetE` declaring three fields (instead of four) must fail closed.
    #[test]
    fn test_read_expr_let_insufficient_fields_returns_region_error() {
        let mut data = vec![0u8; 192];
        let let_off = 64;
        write_header(&mut data, let_off, 3, expr_tags::LET_E); // needs 4
        for k in 0..4 {
            let at = let_off + 8 + k * 8;
            data[at..at + 8].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        }

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(let_off)
            .expect_err("LetE with other<4 must be rejected");
        assert!(matches!(err, OleanError::Region(_)), "got {err:?}");
    }

    /// `Proj` is exempt from the boxed-field requirement: real Lean `proj`
    /// objects report `other = 2` (the `idx` is an unboxed scalar stored in the
    /// scalar region, while the reader still follows `struct` at the third slot
    /// `field_base + 16`). The guard must NOT reject this real shape. Pin that a
    /// well-formed `Proj("", 5, BVar 0)` with `other = 2` round-trips.
    #[test]
    fn test_read_expr_proj_other_two_is_exempt_and_parses() {
        let mut data = vec![0u8; 192];
        let proj_off = 64;
        write_header(&mut data, proj_off, 2, expr_tags::PROJ);
        data[proj_off + 8..proj_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // typeName (anon)
        data[proj_off + 16..proj_off + 24].copy_from_slice(&boxed_scalar(5).to_le_bytes()); // idx = 5
        data[proj_off + 24..proj_off + 32].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // struct = BVar 0

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(proj_off)
            .expect("Proj with other=2 should parse (exempt from boxed-field guard)");
        match expr {
            ParsedExpr::Proj(name, idx, inner) => {
                assert_eq!(name, "");
                assert_eq!(idx, 5);
                assert_eq!(*inner, ParsedExpr::BVar(0));
            }
            other => panic!("expected Proj, got {other:?}"),
        }
    }

    /// `BVar` is exempt from the boxed-field requirement: a real `bvar` object
    /// reports `other = 0` because its de Bruijn index is an unboxed scalar in
    /// the object's scalar region, not a boxed pointer field. The guard must NOT
    /// reject `other = 0` for `bvar`. Pin that such an object still parses (here
    /// the index slot holds a boxed scalar 4).
    #[test]
    fn test_read_expr_bvar_object_zero_fields_is_exempt_and_parses() {
        let mut data = vec![0u8; 128];
        let bvar_off = 64;
        write_header(&mut data, bvar_off, 0, expr_tags::BVAR);
        data[bvar_off + 8..bvar_off + 16].copy_from_slice(&boxed_scalar(4).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(bvar_off)
            .expect("BVar object with other=0 should parse (exempt from guard)");
        assert_eq!(expr, ParsedExpr::BVar(4));
    }

    /// The field-count guard must reject only genuinely malformed objects: a
    /// well-formed `App(BVar 1, BVar 2)` with the correct `other=2` still parses.
    #[test]
    fn test_read_expr_app_correct_fields_still_parses() {
        let mut data = vec![0u8; 128];
        let app_off = 64;
        write_header(&mut data, app_off, 2, expr_tags::APP);
        // fn = scalar BVar 1, arg = scalar BVar 2.
        data[app_off + 8..app_off + 16].copy_from_slice(&boxed_scalar(1).to_le_bytes());
        data[app_off + 16..app_off + 24].copy_from_slice(&boxed_scalar(2).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(app_off)
            .expect("well-formed App(BVar, BVar) should parse");
        assert_eq!(
            expr,
            ParsedExpr::App(Box::new(ParsedExpr::BVar(1)), Box::new(ParsedExpr::BVar(2)))
        );
    }

    /// A constructor declaring *more* fields than its arity is tolerated (the
    /// guard requires `>=`, not `==`): real Lean objects may carry extra inline
    /// scalar payload that bumps the field/usize count. Pin that an `App` with
    /// `other=3` still parses from its first two slots.
    #[test]
    fn test_read_expr_app_extra_fields_still_parses() {
        let mut data = vec![0u8; 128];
        let app_off = 64;
        write_header(&mut data, app_off, 3, expr_tags::APP); // over-declared
        data[app_off + 8..app_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[app_off + 16..app_off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(app_off)
            .expect("App with other>=2 should parse");
        assert_eq!(
            expr,
            ParsedExpr::App(Box::new(ParsedExpr::BVar(0)), Box::new(ParsedExpr::BVar(0)))
        );
    }

    /// Documents the soundness motivation directly: with `Lam other=3` the
    /// binder-info scalar is read from `field_base + 3*8`; an under-declared
    /// `other=2` would read it from `field_base + 2*8` (overlapping the `body`
    /// slot). The guard rejects the malformed object before that mis-read can
    /// fabricate a binder kind, so a well-formed Lam still round-trips its
    /// binder info correctly.
    #[test]
    fn test_read_expr_lam_correct_fields_preserves_binder_info() {
        let mut data = vec![0u8; 192];
        let lam_off = 64;
        write_header(&mut data, lam_off, 3, expr_tags::LAM);
        data[lam_off + 8..lam_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // name (anon)
        data[lam_off + 16..lam_off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // type = BVar 0
        data[lam_off + 24..lam_off + 32].copy_from_slice(&boxed_scalar(0).to_le_bytes()); // body = BVar 0
                                                                                          // binderInfo scalar byte at field_base + 3*8 = lam_off + 8 + 24 = lam_off + 32.
        data[lam_off + 32] = 3; // InstImplicit

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let expr = region
            .read_expr_at(lam_off)
            .expect("well-formed Lam should parse");
        match expr {
            ParsedExpr::Lam(_, _, _, info) => {
                assert_eq!(info, ParsedBinderInfo::InstImplicit);
            }
            other => panic!("expected Lam, got {other:?}"),
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Fail-closed handling of unknown / out-of-range Expr constructor tags.
    //
    // Mainline Lean 4's `Expr` has exactly twelve constructors (tags 0..=11):
    // bvar/fvar/mvar/sort/const/app/lam/forallE/letE/lit/mdata/proj. There is NO
    // `SProp` / `Squash` / `Cubical` `Expr` constructor — strict-prop is
    // `Expr.sort` at level zero, `Squash` is an ordinary `Expr.const`, and there
    // is no cubical mode in mainline Lean 4. Therefore any object tag >= 12 found
    // where an `Expr` is expected is not a higher/future expression kind; it
    // signals a malformed or truncated `.olean` (or a mis-followed pointer).
    //
    // `read_expr_iterative` must fail CLOSED on such a tag: return a typed
    // `OleanError::InvalidObjectTag` carrying the raw tag + offset, never panic
    // and never silently misclassify it as a known constructor. These tests pin
    // that contract so a future refactor cannot regress it into a silent
    // mis-parse.
    // ════════════════════════════════════════════════════════════════════════════

    /// Tag 12 is the first value past the last real `Expr` constructor (`proj`,
    /// tag 11). It is precisely the "tag ~12+" an impredicative/cubical mode was
    /// (incorrectly) imagined to emit. Feeding it must yield a typed
    /// `InvalidObjectTag` error, not a panic or a fabricated expression.
    #[test]
    fn test_read_expr_first_out_of_range_tag_returns_invalid_object_tag() {
        let mut data = vec![0u8; 128];
        let off = 64;
        // tag 12, two plausible-looking field words that the guard must NOT read.
        write_header(&mut data, off, 2, 12);
        data[off + 8..off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[off + 16..off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(off)
            .expect_err("Expr tag 12 (out of range) must be rejected");
        assert!(
            matches!(err, OleanError::InvalidObjectTag { tag: 12, offset } if offset == off),
            "expected InvalidObjectTag {{ tag: 12, offset: {off} }}, got {err:?}"
        );
    }

    /// A high but still in-constructor-range tag (200, below `MAX_CTOR_TAG`) that
    /// happens to sit where an `Expr` was expected must also fail closed.
    #[test]
    fn test_read_expr_high_unknown_tag_returns_invalid_object_tag() {
        let mut data = vec![0u8; 128];
        let off = 64;
        write_header(&mut data, off, 2, 200);
        data[off + 8..off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[off + 16..off + 24].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(off)
            .expect_err("Expr tag 200 (unknown) must be rejected");
        assert!(
            matches!(err, OleanError::InvalidObjectTag { tag: 200, .. }),
            "expected InvalidObjectTag {{ tag: 200, .. }}, got {err:?}"
        );
    }

    /// A non-constructor tag (`STRING` = 249) appearing where an `Expr` is
    /// expected — e.g. a pointer mistakenly followed into a string object — must
    /// be rejected rather than misclassified as a known `Expr` constructor.
    #[test]
    fn test_read_expr_non_constructor_string_tag_returns_invalid_object_tag() {
        let mut data = vec![0u8; 128];
        let off = 64;
        // A String object's bytes, but reached via the Expr reader.
        write_lean_string(&mut data, off, "not an expr");

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let err = region
            .read_expr_at(off)
            .expect_err("a String object (tag 249) is not an Expr and must be rejected");
        assert!(
            matches!(
                err,
                OleanError::InvalidObjectTag {
                    tag: tags::STRING,
                    ..
                }
            ),
            "expected InvalidObjectTag {{ tag: STRING, .. }}, got {err:?}"
        );
    }

    /// The `proj` tag (11) is the last real constructor; tag 11 must still parse
    /// (lower boundary of the valid range stays accepted) while tag 12 is
    /// rejected. This pins the exact boundary so neither side drifts.
    #[test]
    fn test_read_expr_proj_boundary_tag_eleven_parses_twelve_rejected() {
        // tag 11 (proj) parses.
        let mut data = vec![0u8; 192];
        let proj_off = 64;
        write_header(&mut data, proj_off, 2, expr_tags::PROJ);
        data[proj_off + 8..proj_off + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        data[proj_off + 16..proj_off + 24].copy_from_slice(&boxed_scalar(1).to_le_bytes());
        data[proj_off + 24..proj_off + 32].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        assert!(
            region.read_expr_at(proj_off).is_ok(),
            "tag 11 (proj) must remain a valid Expr constructor"
        );

        // tag 12 is rejected.
        let mut data12 = vec![0u8; 128];
        let off12 = 64;
        write_header(&mut data12, off12, 2, 12);
        let region12 = CompactedRegion::new(&data12, TEST_BASE_ADDR);
        assert!(
            matches!(
                region12.read_expr_at(off12),
                Err(OleanError::InvalidObjectTag { tag: 12, .. })
            ),
            "tag 12 must be rejected as an invalid Expr tag"
        );
    }
}

// BigNat type for handling arbitrary-precision natural numbers from .olean files
// Added for issue #1163 - Fix big integer (MPZ) truncation

/// A big natural number that can hold arbitrary-precision values.
///
/// Lean 4 uses GMP for big integers. This type handles both small values
/// (fitting in u64) and arbitrarily large values (multiple 64-bit limbs).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BigNat {
    /// Small value that fits in u64.
    Small(u64),
    /// Large value with multiple limbs (little-endian, lowest limb first).
    Big(Vec<u64>),
}

impl BigNat {
    /// Create a BigNat from a u64 value.
    #[inline]
    pub fn from_u64(val: u64) -> Self {
        BigNat::Small(val)
    }

    /// Create a BigNat from a vector of limbs (little-endian).
    pub fn from_limbs(limbs: Vec<u64>) -> Self {
        match limbs.len() {
            0 => BigNat::Small(0),
            1 => BigNat::Small(limbs[0]),
            _ => {
                let mut limbs = limbs;
                while limbs.len() > 1 && limbs.last() == Some(&0) {
                    limbs.pop();
                }
                if limbs.len() == 1 {
                    BigNat::Small(limbs[0])
                } else {
                    BigNat::Big(limbs)
                }
            }
        }
    }

    /// Try to convert to u64, returning None if too large.
    #[inline]
    pub fn to_u64(&self) -> Option<u64> {
        match self {
            BigNat::Small(v) => Some(*v),
            BigNat::Big(_) => None,
        }
    }

    /// Get the limbs (little-endian).
    pub fn limbs(&self) -> &[u64] {
        match self {
            BigNat::Small(v) => std::slice::from_ref(v),
            BigNat::Big(limbs) => limbs,
        }
    }
}

impl Default for BigNat {
    fn default() -> Self {
        BigNat::Small(0)
    }
}

impl From<u64> for BigNat {
    fn from(val: u64) -> Self {
        BigNat::Small(val)
    }
}

impl std::fmt::Display for BigNat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BigNat::Small(v) => write!(f, "{}", v),
            BigNat::Big(limbs) => {
                write!(f, "0x")?;
                for limb in limbs.iter().rev() {
                    write!(f, "{:016x}", limb)?;
                }
                Ok(())
            }
        }
    }
}
