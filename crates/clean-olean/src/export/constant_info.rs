// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ConstantInfo serialization (axiom, definition, inductive, constructor, recursor, quotient).

use super::OleanExporter;
use crate::error::OleanResult;
use crate::module::DefinitionSafety;
use clean_kernel::env::{ConstantInfo, ConstantKind};
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use clean_kernel::name::Name;
use clean_kernel::quot::{QuotKind, QuotVal};

impl OleanExporter {
    /// Historical Clean-only `DefinitionSafety` tag order used by the legacy
    /// four-boxed-field `DefnVal` writer. Genuine Lean uses unsafe=0, safe=1;
    /// retain this helper solely so already-produced Clean fixtures round-trip.
    fn legacy_definition_safety_tag(safety: DefinitionSafety) -> u64 {
        match safety {
            DefinitionSafety::Safe => 0,
            DefinitionSafety::Unsafe => 1,
            DefinitionSafety::Partial => 2,
        }
    }

    // =========================================================================
    // ConstantInfo Serialization
    // =========================================================================

    /// Write a ConstantInfo object and return its pointer
    ///
    /// Lean 4 ConstantInfo is an inductive with constructors:
    /// - axiomInfo (tag 0): name, levelParams, type
    /// - defnInfo (tag 1): name, levelParams, type, value, hints
    /// - thmInfo (tag 2): name, levelParams, type, value
    /// - opaqueInfo (tag 3): name, levelParams, type, value, isUnsafe
    /// - quotInfo (tag 4): name, levelParams, type, kind
    /// - inductInfo (tag 5): various inductive fields
    /// - ctorInfo (tag 6): constructor fields
    /// - recInfo (tag 7): recursor fields
    ///
    /// # ENSURES
    /// - Returns Ok(pointer) for use in constants array.
    /// - Returns Err(UnsupportedBigNat) if the type or value contains BigNat > u64.
    ///
    /// Lean 4's ConstantInfo is a wrapper inductive:
    /// ```text
    /// inductive ConstantInfo where
    ///   | axiomInfo (val : AxiomVal)      -- tag 0
    ///   | defnInfo (val : DefnVal)        -- tag 1
    ///   | thmInfo (val : TheoremVal)      -- tag 2
    ///   | opaqueInfo (val : OpaqueVal)    -- tag 3
    ///   | quotInfo (val : QuotVal)        -- tag 4
    ///   | inductInfo (val : InductiveVal) -- tag 5
    ///   | ctorInfo (val : ConstructorVal) -- tag 6
    ///   | recInfo (val : RecursorVal)     -- tag 7
    /// ```
    ///
    /// XxxVal structures inherit from ConstantVal. In the object layout:
    /// - XxxVal field 0 is a pointer to a ConstantVal
    /// - ConstantVal has fields: name, levelParams, type
    /// - XxxVal-specific fields follow (value, hints, etc.)
    ///
    /// So we write:
    /// 1. The ConstantVal base object (with tag 0, 3 fields)
    /// 2. The XxxVal object (with tag 0, N fields) referencing ConstantVal
    /// 3. The outer ConstantInfo wrapper (with the appropriate tag 0-7)
    pub(crate) fn write_constant_info(&mut self, info: &ConstantInfo) -> OleanResult<u64> {
        self.write_constant_info_with_definition_safety(info, DefinitionSafety::Safe)
    }

    /// Serialize a constant while preserving an environment-supplied
    /// `DefinitionSafety` for definition values.
    ///
    /// The plain `ConstantInfo` model does not carry this metadata, so
    /// standalone callers remain explicitly safe-by-construction. Environment
    /// export uses this entrypoint and derives the mark from its unsafe/partial
    /// registries.
    pub(crate) fn write_constant_info_with_definition_safety(
        &mut self,
        info: &ConstantInfo,
        definition_safety: DefinitionSafety,
    ) -> OleanResult<u64> {
        let name_offset = self.write_kernel_name(&info.name);
        let name_ptr = self.offset_to_ptr(name_offset);

        let level_params_ptr = self.write_level_params(&info.level_params);
        let type_ptr = self.write_expr(&info.type_)?;

        // Write the shared ConstantVal base (tag 0, 3 fields)
        self.align8();
        let const_val_offset = self.current_offset();
        self.write_header(0, 3, 0);
        self.write_u64(name_ptr);
        self.write_u64(level_params_ptr);
        self.write_u64(type_ptr);
        let const_val_ptr = self.offset_to_ptr(const_val_offset);

        // Determine the kind and write the inner XxxVal
        match &info.value {
            None => {
                // AxiomVal: ConstantVal pointer, isUnsafe
                // (AxiomVal extends ConstantVal with isUnsafe field)
                self.align8();
                let val_offset = self.current_offset();
                self.write_header(0, 2, 0); // 2 fields: ConstantVal ptr + isUnsafe
                self.write_u64(const_val_ptr);
                self.write_u64(Self::scalar_ptr(0)); // isUnsafe = false
                let val_ptr = self.offset_to_ptr(val_offset);

                // ConstantInfo.axiomInfo wrapper (tag 0, 1 field)
                self.align8();
                let wrapper_offset = self.current_offset();
                self.write_header(0, 1, 0);
                self.write_u64(val_ptr);
                Ok(self.offset_to_ptr(wrapper_offset))
            }
            Some(value) => {
                let value_ptr = self.write_expr(value)?;

                // The outer ConstantInfo wrapper tag preserves the Lean 4
                // distinction between definitions, theorems, and opaque
                // constants. All three carry a value, but the kernel treats
                // them differently (theorems are proof-irrelevant; opaque
                // constants hide their value during reduction), so collapsing
                // the tag silently downgrades a theorem/opaque to a plain
                // definition on re-import. `info.kind` carries the distinction
                // that `info.value` alone cannot. See `ConstantKind` in
                // clean-kernel: "both Theorem and Opaque map to
                // Reducibility::Opaque".
                match info.kind {
                    ConstantKind::Theorem => {
                        Ok(self.write_theorem_inner(info, const_val_ptr, value_ptr))
                    }
                    ConstantKind::Opaque => {
                        Ok(self.write_opaque_inner(info, const_val_ptr, value_ptr))
                    }
                    // Definition is the common case. An Axiom carrying a value
                    // is anomalous (axioms have no value); fall through to the
                    // definition encoding so the value is not silently lost.
                    ConstantKind::Definition | ConstantKind::Axiom => Ok(self
                        .write_definition_inner(info, const_val_ptr, value_ptr, definition_safety)),
                }
            }
        }
    }

    /// Write a `DefinitionVal` inner object and its `defnInfo` wrapper
    /// (tag 1), returning the wrapper pointer.
    ///
    /// `DefinitionVal extends ConstantVal` with `value`, `hints`, and
    /// `safety`. Layout (matching the loader's `read_constant_value`,
    /// `read_reducibility_hints`, and `read_definition_safety`):
    ///   +8:  ConstantVal ptr
    ///   +16: value (Expr)
    ///   +24: hints (ReducibilityHints)
    ///   +32: safety (DefinitionSafety scalar; `safe = 0`)
    ///
    /// TRACKING (deferred wire-format decision): this is Clean's LEGACY
    /// layout, not real Lean 4's. Real v4.30 `DefnVal`s carry `all : List
    /// Name` as the fourth boxed field (+32) and `safety` as an unboxed u8
    /// at +40 in Lean's tag order (unsafe=0, safe=1, partial=2 —
    /// `Declaration.lean:116-118`). The reader
    /// (`read_definition_safety`) discriminates both layouts by their exact
    /// object-header shape (`cs_sz=0` legacy, `cs_sz=48` real Lean), so
    /// Clean-exported oleans keep round-tripping; converging this writer on
    /// the real Lean layout is deferred until Clean-exported oleans need to
    /// be consumed by Lean itself.
    fn write_definition_inner(
        &mut self,
        info: &ConstantInfo,
        const_val_ptr: u64,
        value_ptr: u64,
        safety: DefinitionSafety,
    ) -> u64 {
        let hints_ptr = self.write_reducibility_hints(&info.reducibility);

        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 4, 0); // 4 fields: ConstantVal ptr + value + hints + safety
        self.write_u64(const_val_ptr);
        self.write_u64(value_ptr);
        self.write_u64(hints_ptr);
        self.write_u64(Self::scalar_ptr(Self::legacy_definition_safety_tag(safety)));
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.defnInfo wrapper (tag 1, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(1, 1, 0);
        self.write_u64(val_ptr);
        self.offset_to_ptr(wrapper_offset)
    }

    /// Write a `TheoremVal` inner object and its `thmInfo` wrapper (tag 2),
    /// returning the wrapper pointer.
    ///
    /// `TheoremVal extends ConstantVal` with `value` and `all : List Name`.
    /// The value lives at +16 so the loader's `read_constant_value` (which
    /// reads +16 for theorem/opaque) recovers it. Layout:
    ///   +8:  ConstantVal ptr
    ///   +16: value (Expr)
    ///   +24: all (List Name)
    fn write_theorem_inner(
        &mut self,
        info: &ConstantInfo,
        const_val_ptr: u64,
        value_ptr: u64,
    ) -> u64 {
        let all_ptr = self.write_name_list(std::slice::from_ref(&info.name));

        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 3, 0); // 3 fields: ConstantVal ptr + value + all
        self.write_u64(const_val_ptr);
        self.write_u64(value_ptr);
        self.write_u64(all_ptr);
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.thmInfo wrapper (tag 2, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(2, 1, 0);
        self.write_u64(val_ptr);
        self.offset_to_ptr(wrapper_offset)
    }

    /// Write an `OpaqueVal` inner object and its `opaqueInfo` wrapper
    /// (tag 3), returning the wrapper pointer.
    ///
    /// `OpaqueVal extends ConstantVal` with `value`, `isUnsafe`, and
    /// `all : List Name`. The value lives at +16 so the loader recovers it
    /// via `read_constant_value`. Layout:
    ///   +8:  ConstantVal ptr
    ///   +16: value (Expr)
    ///   +24: isUnsafe (Bool scalar; `false = 0`)
    ///   +32: all (List Name)
    fn write_opaque_inner(
        &mut self,
        info: &ConstantInfo,
        const_val_ptr: u64,
        value_ptr: u64,
    ) -> u64 {
        let all_ptr = self.write_name_list(std::slice::from_ref(&info.name));

        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 4, 0); // 4 fields: ConstantVal ptr + value + isUnsafe + all
        self.write_u64(const_val_ptr);
        self.write_u64(value_ptr);
        self.write_u64(Self::scalar_ptr(0)); // isUnsafe = false
        self.write_u64(all_ptr);
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.opaqueInfo wrapper (tag 3, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(3, 1, 0);
        self.write_u64(val_ptr);
        self.offset_to_ptr(wrapper_offset)
    }

    /// Write a `defnInfo` `ConstantInfo` with an explicit
    /// [`DefinitionSafety`], returning its pointer.
    ///
    /// Standalone [`OleanExporter::write_constant_info`] calls default to
    /// `safety = safe` because a bare kernel `ConstantInfo` carries no safety
    /// flag. Whole-environment export supplies the environment's mark through
    /// `write_constant_info_with_definition_safety`. This test-only helper
    /// reproduces the exact `DefnVal` layout while varying the scalar so the loader's
    /// [`CompactedRegion::read_definition_safety`] can be exercised across
    /// all three tags without a real Lean toolchain.
    #[cfg(test)]
    pub(crate) fn write_definition_with_safety(
        &mut self,
        info: &ConstantInfo,
        safety: DefinitionSafety,
    ) -> OleanResult<u64> {
        let name_offset = self.write_kernel_name(&info.name);
        let name_ptr = self.offset_to_ptr(name_offset);

        let level_params_ptr = self.write_level_params(&info.level_params);
        let type_ptr = self.write_expr(&info.type_)?;

        // Value is required for a defnInfo.
        let value = info
            .value
            .as_ref()
            .ok_or_else(|| crate::error::OleanError::Region("defnInfo requires a value".into()))?;
        let value_ptr = self.write_expr(value)?;
        let hints_ptr = self.write_reducibility_hints(&info.reducibility);

        // ConstantVal base (tag 0, 3 fields).
        self.align8();
        let const_val_offset = self.current_offset();
        self.write_header(0, 3, 0);
        self.write_u64(name_ptr);
        self.write_u64(level_params_ptr);
        self.write_u64(type_ptr);
        let const_val_ptr = self.offset_to_ptr(const_val_offset);

        // DefnVal: ConstantVal ptr + value + hints + safety (4 fields).
        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 4, 0);
        self.write_u64(const_val_ptr);
        self.write_u64(value_ptr);
        self.write_u64(hints_ptr);
        self.write_u64(Self::scalar_ptr(Self::legacy_definition_safety_tag(safety)));
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.defnInfo wrapper (tag 1, 1 field).
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(1, 1, 0);
        self.write_u64(val_ptr);
        Ok(self.offset_to_ptr(wrapper_offset))
    }

    /// Write ReducibilityHints and return its pointer
    ///
    /// ReducibilityHints is:
    /// - opaque (tag 0)
    /// - abbrev (tag 1)
    /// - regular (tag 2, 1 scalar: height)
    pub(super) fn write_reducibility_hints(
        &mut self,
        reducibility: &clean_kernel::env::Reducibility,
    ) -> u64 {
        use clean_kernel::env::Reducibility;
        match reducibility {
            Reducibility::Opaque | Reducibility::Irreducible => {
                // Nullary constructors are represented directly as tagged
                // scalars by Lean's runtime.
                Self::scalar_ptr(0)
            }
            Reducibility::Reducible => Self::scalar_ptr(1),
            Reducibility::Regular(height) => {
                // Real Lean ABI: `regular (height : UInt32)` is a 16-byte
                // object with no pointer fields and an unboxed UInt32 at +8.
                self.align8();
                let offset = self.current_offset();
                self.write_header(2, 0, 16);
                self.write_u64(u64::from(*height));
                self.offset_to_ptr(offset)
            }
        }
    }

    /// Write an InductiveVal as ConstantInfo.inductInfo (tag 5)
    ///
    /// Lean 4 InductiveVal fields:
    /// - name: Name
    /// - levelParams: List Name
    /// - type: Expr
    /// - numParams: Nat
    /// - numIndices: Nat
    /// - all: List Name (mutual inductive names)
    /// - ctors: List Name (constructor names)
    /// - isRec: Bool
    /// - isUnsafe: Bool
    /// - isReflexive: Bool
    /// - isNested: Bool
    ///
    /// # ENSURES
    /// - Returns Ok(pointer) for use in constants array.
    /// - Returns Err(UnsupportedBigNat) if a type expression contains BigNat > u64.
    pub(crate) fn write_inductive_info(&mut self, ind: &InductiveVal) -> OleanResult<u64> {
        let name_offset = self.write_kernel_name(&ind.name);
        let name_ptr = self.offset_to_ptr(name_offset);

        let level_params_ptr = self.write_name_list(&ind.level_params);
        let type_ptr = self.write_expr(&ind.type_)?;

        // Write all (mutual inductive names) as List Name
        let all_ptr = self.write_name_list(&ind.all_names);

        // Write ctors (constructor names) as List Name
        let ctors_ptr = self.write_name_list(&ind.constructor_names);

        // ConstantVal base (tag 0, 3 fields)
        self.align8();
        let const_val_offset = self.current_offset();
        self.write_header(0, 3, 0);
        self.write_u64(name_ptr);
        self.write_u64(level_params_ptr);
        self.write_u64(type_ptr);
        let const_val_ptr = self.offset_to_ptr(const_val_offset);

        // InductiveVal field layout (mirrors the loader's
        // `read_inductive_val_data`, which is calibrated against real Lean
        // `.olean` files):
        //   +8:  toConstantVal ptr
        //   +16: numParams   (Nat, scalar)
        //   +24: numIndices  (Nat, scalar)
        //   +32: all         (List Name ptr)
        //   +40: ctors       (List Name ptr)
        //   +48: numNested   (Nat, scalar) -- isNested = numNested > 0
        //   +56: packed bool word: byte0=isRec, byte1=isUnsafe, byte2=isReflexive
        //
        // The trailing booleans are packed as individual `u8`s in one
        // 8-byte word, exactly as Lean's compacted region stores `Bool`
        // (UInt8) scalar fields after the boxed/scalar fields. Writing them
        // as separate boxed scalars (the previous layout) shifted every
        // field and silently dropped `numNested`/`isReflexive` on read.
        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 7, 0);
        self.write_u64(const_val_ptr);
        self.write_u64(Self::scalar_ptr(ind.num_params as u64));
        self.write_u64(Self::scalar_ptr(ind.num_indices as u64));
        self.write_u64(all_ptr);
        self.write_u64(ctors_ptr);
        // numNested: the loader only consults `numNested > 0`, so encode the
        // kernel's `is_nested` flag as 1 (nested) or 0 (not nested).
        self.write_u64(Self::scalar_ptr(u64::from(ind.is_nested)));
        // Packed trailing booleans (isRec, isUnsafe, isReflexive).
        self.write_u64(Self::pack_bools3(ind.is_recursive, false, ind.is_reflexive));
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.inductInfo wrapper (tag 5, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(5, 1, 0);
        self.write_u64(val_ptr);
        Ok(self.offset_to_ptr(wrapper_offset))
    }

    /// Write a ConstructorVal as ConstantInfo.ctorInfo (tag 6)
    ///
    /// Lean 4 ConstructorVal fields:
    /// - name: Name
    /// - levelParams: List Name
    /// - type: Expr
    /// - induct: Name
    /// - cidx: Nat (constructor index)
    /// - numParams: Nat
    /// - numFields: Nat
    /// - isUnsafe: Bool
    ///
    /// # ENSURES
    /// - Returns Ok(pointer) for use in constants array.
    /// - Returns Err(UnsupportedBigNat) if the type contains BigNat > u64.
    pub(crate) fn write_constructor_info(&mut self, ctor: &ConstructorVal) -> OleanResult<u64> {
        let name_offset = self.write_kernel_name(&ctor.name);
        let name_ptr = self.offset_to_ptr(name_offset);

        let level_params_ptr = self.write_name_list(&ctor.level_params);
        let type_ptr = self.write_expr(&ctor.type_)?;

        let induct_offset = self.write_kernel_name(&ctor.inductive_name);
        let induct_ptr = self.offset_to_ptr(induct_offset);

        // ConstantVal base (tag 0, 3 fields)
        self.align8();
        let const_val_offset = self.current_offset();
        self.write_header(0, 3, 0);
        self.write_u64(name_ptr);
        self.write_u64(level_params_ptr);
        self.write_u64(type_ptr);
        let const_val_ptr = self.offset_to_ptr(const_val_offset);

        // ConstructorVal: ConstantVal ptr + extra fields (6 fields total)
        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 6, 0);
        self.write_u64(const_val_ptr);
        self.write_u64(induct_ptr);
        self.write_u64(Self::scalar_ptr(ctor.constructor_idx as u64));
        self.write_u64(Self::scalar_ptr(ctor.num_params as u64));
        self.write_u64(Self::scalar_ptr(ctor.num_fields as u64));
        self.write_u64(Self::scalar_ptr(0)); // isUnsafe = false
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.ctorInfo wrapper (tag 6, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(6, 1, 0);
        self.write_u64(val_ptr);
        Ok(self.offset_to_ptr(wrapper_offset))
    }

    /// Write a RecursorVal as ConstantInfo.recInfo (tag 7)
    ///
    /// Lean 4 RecursorVal fields:
    /// - name: Name
    /// - levelParams: List Name
    /// - type: Expr
    /// - all: List Name (mutual inductive names)
    /// - numParams: Nat
    /// - numIndices: Nat
    /// - numMotives: Nat
    /// - numMinors: Nat
    /// - rules: List RecursorRule
    /// - k: Bool (is K-like eliminator)
    /// - isUnsafe: Bool
    ///
    /// # ENSURES
    /// - Returns Ok(pointer) for use in constants array.
    /// - Returns Err(UnsupportedBigNat) if the type or rules contain BigNat > u64.
    pub(crate) fn write_recursor_info(&mut self, rec: &RecursorVal) -> OleanResult<u64> {
        let name_offset = self.write_kernel_name(&rec.name);
        let name_ptr = self.offset_to_ptr(name_offset);

        let level_params_ptr = self.write_name_list(&rec.level_params);
        let type_ptr = self.write_expr(&rec.type_)?;

        // Write all as List Name (just the single inductive name for non-mutual)
        let all_ptr = self.write_name_list(std::slice::from_ref(&rec.inductive_name));

        // Write recursor rules as List RecursorRule
        let rules_ptr = self.write_recursor_rules(&rec.rules)?;

        // ConstantVal base (tag 0, 3 fields)
        self.align8();
        let const_val_offset = self.current_offset();
        self.write_header(0, 3, 0);
        self.write_u64(name_ptr);
        self.write_u64(level_params_ptr);
        self.write_u64(type_ptr);
        let const_val_ptr = self.offset_to_ptr(const_val_offset);

        // RecursorVal: ConstantVal ptr + extra fields (9 fields total)
        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 9, 0);
        self.write_u64(const_val_ptr);
        self.write_u64(all_ptr);
        self.write_u64(Self::scalar_ptr(rec.num_params as u64));
        self.write_u64(Self::scalar_ptr(rec.num_indices as u64));
        self.write_u64(Self::scalar_ptr(rec.num_motives as u64));
        self.write_u64(Self::scalar_ptr(rec.num_minors as u64));
        self.write_u64(rules_ptr);
        self.write_u64(Self::scalar_ptr(u64::from(rec.is_k)));
        self.write_u64(Self::scalar_ptr(0)); // isUnsafe = false
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.recInfo wrapper (tag 7, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(7, 1, 0);
        self.write_u64(val_ptr);
        Ok(self.offset_to_ptr(wrapper_offset))
    }

    /// Write a QuotVal as ConstantInfo.quotInfo (tag 4)
    ///
    /// Lean 4 QuotVal fields:
    /// - name: Name
    /// - levelParams: List Name
    /// - type: Expr
    /// - kind: QuotKind (0=type, 1=ctor, 2=lift, 3=ind)
    ///
    /// # ENSURES
    /// - Returns Ok(pointer) for use in constants array.
    /// - Returns Err(UnsupportedBigNat) if the type contains BigNat > u64.
    pub(crate) fn write_quotient_info(&mut self, quot: &QuotVal) -> OleanResult<u64> {
        let name_offset = self.write_kernel_name(&quot.name);
        let name_ptr = self.offset_to_ptr(name_offset);

        let level_params_ptr = self.write_name_list(&quot.level_params);
        let type_ptr = self.write_expr(&quot.type_)?;

        // Convert QuotKind to Lean 4 tag
        let kind_tag = match quot.kind {
            QuotKind::Type => 0,
            QuotKind::Mk => 1,
            QuotKind::Lift => 2,
            QuotKind::Ind => 3,
            QuotKind::Sound => 4,
        };

        // ConstantVal base (tag 0, 3 fields)
        self.align8();
        let const_val_offset = self.current_offset();
        self.write_header(0, 3, 0);
        self.write_u64(name_ptr);
        self.write_u64(level_params_ptr);
        self.write_u64(type_ptr);
        let const_val_ptr = self.offset_to_ptr(const_val_offset);

        // QuotVal: ConstantVal ptr + kind (2 fields total)
        self.align8();
        let val_offset = self.current_offset();
        self.write_header(0, 2, 0);
        self.write_u64(const_val_ptr);
        self.write_u64(Self::scalar_ptr(kind_tag));
        let val_ptr = self.offset_to_ptr(val_offset);

        // ConstantInfo.quotInfo wrapper (tag 4, 1 field)
        self.align8();
        let wrapper_offset = self.current_offset();
        self.write_header(4, 1, 0);
        self.write_u64(val_ptr);
        Ok(self.offset_to_ptr(wrapper_offset))
    }

    /// Write a list of recursor rules
    pub(super) fn write_recursor_rules(&mut self, rules: &[RecursorRule]) -> OleanResult<u64> {
        let mut list_ptr = Self::scalar_ptr(0); // nil

        for rule in rules.iter().rev() {
            let rule_ptr = self.write_recursor_rule(rule)?;
            self.align8();
            let cons_offset = self.current_offset();
            self.write_header(1, 2, 0); // cons tag
            self.write_u64(rule_ptr);
            self.write_u64(list_ptr);
            list_ptr = self.offset_to_ptr(cons_offset);
        }

        Ok(list_ptr)
    }

    /// Write a single RecursorRule
    ///
    /// RecursorRule fields:
    /// - ctor: Name (constructor name)
    /// - nfields: Nat
    /// - rhs: Expr
    pub(super) fn write_recursor_rule(&mut self, rule: &RecursorRule) -> OleanResult<u64> {
        let ctor_offset = self.write_kernel_name(&rule.constructor_name);
        let ctor_ptr = self.offset_to_ptr(ctor_offset);
        let rhs_ptr = self.write_expr(&rule.rhs)?;

        self.align8();
        let offset = self.current_offset();
        self.write_header(0, 3, 0); // RecursorRule constructor
        self.write_u64(ctor_ptr);
        self.write_u64(Self::scalar_ptr(rule.num_fields as u64));
        self.write_u64(rhs_ptr);
        Ok(self.offset_to_ptr(offset))
    }

    /// Write a list of Names as Lean List Name
    pub(super) fn write_name_list(&mut self, names: &[Name]) -> u64 {
        let mut list_ptr = Self::scalar_ptr(0); // nil

        for name in names.iter().rev() {
            let name_offset = self.write_kernel_name(name);
            let name_ptr = self.offset_to_ptr(name_offset);
            self.align8();
            let cons_offset = self.current_offset();
            self.write_header(1, 2, 0); // cons tag
            self.write_u64(name_ptr);
            self.write_u64(list_ptr);
            list_ptr = self.offset_to_ptr(cons_offset);
        }

        list_ptr
    }
}
