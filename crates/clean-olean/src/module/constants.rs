// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant-specific readers for CompactedRegion.
//!
//! Parses ConstantInfo, InductiveVal, ConstructorVal, RecursorVal,
//! and their associated data from .olean compacted regions.

use super::{
    ConstantKind, ConstructorValData, DefinitionSafety, InductiveValData, ParsedConstant,
    ParsedQuotKind, RecursorRuleData, RecursorValData, ReducibilityHintsData,
};
use crate::error::{OleanError, OleanResult};
use crate::region::{is_ptr, is_scalar, tags, unbox_scalar, CompactedRegion};

impl<'a> CompactedRegion<'a> {
    /// Read an array of ConstantInfo (v2 - based on actual structure)
    pub(crate) fn read_constant_array_v2(&self, ptr: u64) -> OleanResult<Vec<ParsedConstant>> {
        self.read_constant_array_v2_opts(ptr, false)
    }

    /// Read an array of ConstantInfo (v2), optionally in TYPES-ONLY mode.
    ///
    /// When `skip_proof_values` is `true`, the `value` (proof-term) `Expr` of every
    /// `Theorem`/`Opaque` constant is NOT reconstructed — the resulting
    /// [`ParsedConstant::value`] is `None` for those kinds. Every constant's TYPE,
    /// and the `value` of a non-opaque `Definition` (δ-reducible, kept for
    /// definitional-equality unfolding), are read exactly as in the full path.
    ///
    /// This is the loader lever behind `clean mathverse per-constant-verify`'s
    /// TRUSTED-import closure: the kernel never δ-unfolds a `Theorem`/`Opaque`
    /// value during type-checking, so a trusted dependency's proof body is dead
    /// weight — reconstructing it is what makes analysis-module closures OOM.
    /// Skipping it keeps the load sound (only TYPES flow to the trusted env) while
    /// eliminating the peak-RSS proof-`Expr` reconstruction.
    pub(crate) fn read_constant_array_v2_opts(
        &self,
        ptr: u64,
        skip_proof_values: bool,
    ) -> OleanResult<Vec<ParsedConstant>> {
        if !is_ptr(ptr) {
            return Ok(Vec::new());
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(Vec::new());
        }

        let size = self.read_usize_at(offset + 8, "Constant array")?;
        self.validate_array_bounds(offset, size)?;
        let mut constants = Vec::with_capacity(size);

        for i in 0..size {
            // SAFETY: bounds validated above
            let elem_offset = self.array_elem_offset(offset, i, "Constant array")?;
            let const_ptr = self.read_u64_at(elem_offset)?;
            let constant = self.read_constant_info_v2_opts(const_ptr, skip_proof_values)?;
            constants.push(constant);
        }

        Ok(constants)
    }

    /// Read a single ConstantInfo (v2)
    ///
    /// Structure observed from Init/Prelude.olean:
    /// - Outer wrapper: tag=1, 1 field (pointing to inner)
    /// - Inner: tag=0, 4 fields containing:
    ///   - Field 0: XxxVal (the actual constant data) - tag=0, 3 fields
    ///   - Field 1: some metadata
    ///   - Field 2: scalar
    ///   - Field 3: name reference
    /// - XxxVal: tag=0, 3 fields:
    ///   - Field 0: Name (constant name)
    ///   - Field 1: List Name (level params)
    ///   - Field 2: Expr (type)
    ///   - (for defn/thm) Field 3: Expr (value)
    fn read_constant_info_v2(&self, ptr: u64) -> OleanResult<ParsedConstant> {
        self.read_constant_info_v2_opts(ptr, false)
    }

    /// Read a single ConstantInfo (v2), optionally in TYPES-ONLY mode. See
    /// [`Self::read_constant_array_v2_opts`] for the `skip_proof_values` contract:
    /// when set, a `Theorem`/`Opaque` value `Expr` is left unread (`None`).
    fn read_constant_info_v2_opts(
        &self,
        ptr: u64,
        skip_proof_values: bool,
    ) -> OleanResult<ParsedConstant> {
        if !is_ptr(ptr) {
            return Err(OleanError::Region("Invalid constant pointer".into()));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        // Lean 4 ConstantInfo constructor order:
        // 0 = axiomInfo, 1 = defnInfo, 2 = thmInfo, 3 = opaqueInfo,
        // 4 = quotInfo, 5 = inductInfo, 6 = ctorInfo, 7 = recInfo
        let kind = match header.tag {
            1 => ConstantKind::Definition,
            2 => ConstantKind::Theorem,
            3 => ConstantKind::Opaque,
            4 => ConstantKind::Quot,
            5 => ConstantKind::Inductive,
            6 => ConstantKind::Constructor,
            7 => ConstantKind::Recursor,
            _ => ConstantKind::Axiom,
        };

        // The XxxVal is the first (and only) field
        let val_ptr = self.read_u64_at(offset + 8)?;
        if !is_ptr(val_ptr) {
            return Err(OleanError::Region("Invalid XxxVal pointer".into()));
        }

        let val_offset = self.ptr_to_offset(val_ptr)?;
        let val_header = self.read_header_at(val_offset)?;

        // Fail closed before reading any field if the XxxVal object declares
        // fewer slots than this kind's reader will access.
        Self::require_val_fields(&kind, &val_header, val_offset)?;

        // Read base ConstantVal fields (name, level_params, type)
        let (name, level_params, type_) = self.read_constant_val_fields(val_offset)?;

        // Read value for definitions, theorems, opaques (types-only skips the
        // theorem/opaque proof body — a dead-weight, never-δ-unfolded term).
        let value = self.read_constant_value(&kind, val_offset, &val_header, skip_proof_values)?;

        // Read ReducibilityHints for definitions
        let hints = self.read_reducibility_hints(&kind, val_offset, &val_header)?;

        // Read the DefinitionSafety flag for definitions
        let definition_safety = self.read_definition_safety(&kind, val_offset, &val_header)?;

        // Parse extra fields based on kind
        let (inductive_val, constructor_val, recursor_val) = match kind {
            ConstantKind::Inductive => {
                (Some(self.read_inductive_val_data(val_offset)?), None, None)
            }
            ConstantKind::Constructor => (
                None,
                Some(self.read_constructor_val_data(val_offset)?),
                None,
            ),
            ConstantKind::Recursor => (None, None, Some(self.read_recursor_val_data(val_offset)?)),
            _ => (None, None, None),
        };

        // For quotient primitives, decode the QuotVal.kind discriminant so
        // the specific primitive (Quot / .mk / .lift / .ind / .sound) is
        // preserved rather than collapsed into the bare `Quot` kind.
        let quot_kind = match kind {
            ConstantKind::Quot => self.read_quot_kind(val_offset)?,
            _ => None,
        };

        Ok(ParsedConstant {
            name,
            kind,
            level_params,
            type_,
            value,
            inductive_val,
            constructor_val,
            recursor_val,
            hints,
            definition_safety,
            quot_kind,
        })
    }

    /// Validate that an `XxxVal` constant-info object declares enough *boxed
    /// pointer fields* to satisfy its kind before any field is dereferenced.
    ///
    /// In Lean's compacted region a constructor object's header `other` byte
    /// counts only its *boxed object (pointer) fields*; inline unboxed scalar
    /// fields (the `Nat`/`Bool` members) are stored in a trailing scalar
    /// region and are **not** counted in `other`. Empirically, real Lean 4
    /// `.olean` files report (Init/Core, Init/Prelude, v4.x):
    ///
    /// | kind          | `other` (boxed fields) | pointer fields the reader dereferences |
    /// |---------------|------------------------|----------------------------------------|
    /// | `Recursor`    | 7                      | `toConstantVal` (+8), `all` (+16), `rules` (+56) |
    /// | `Inductive`   | 6                      | `toConstantVal` (+8), `all` (+32), `ctors` (+40) |
    /// | `Constructor` | 5                      | `toConstantVal` (+8), `induct` (+16)   |
    /// | `Definition`  | 4                      | `toConstantVal` (+8), `value` (+16)    |
    /// | `Theorem`     | 3                      | `toConstantVal` (+8), `value` (+16)    |
    /// | `Opaque`      | 3                      | `toConstantVal` (+8), `value` (+16)    |
    /// | `Quot`        | 1                      | `toConstantVal` (+8)                   |
    /// | `Axiom`       | 1                      | `toConstantVal` (+8)                   |
    ///
    /// The fail-closed minimum for each kind is the **number of boxed pointer
    /// fields its reader actually dereferences** (`is_ptr` / `ptr_to_offset` /
    /// list walks) — never the byte offset of a trailing scalar, which can lie
    /// far beyond `other * 8`. A malformed, truncated, or future-version
    /// `.olean` can present an `XxxVal` whose `other` is smaller than this.
    /// Without the guard the per-kind reader would dereference a word belonging
    /// to an adjacent object as an `all` / `ctors` / `rules` / `induct` pointer
    /// — silently fabricating a constant or chasing a bogus pointer rather than
    /// failing. Fail closed with a typed [`OleanError::Region`] instead. This
    /// mirrors the `Expr`/`Level` constructor field-count guards in
    /// [`CompactedRegion::require_expr_fields`], which likewise count only
    /// boxed pointer fields and exempt unboxed scalars.
    ///
    /// The minimum is intentionally `<=` every observed real-olean `other`, so
    /// well-formed data always passes. The kind-specific `value` / `hints` /
    /// `safety` scalar readers already guard their own higher offsets
    /// (`other >= 2/3/4`); only the pointer-field requirement is enforced here.
    ///
    /// # ENSURES
    /// - Returns `Ok(())` when `val_header.other >= expected` for the kind.
    /// - Returns `OleanError::Region` describing the mismatch otherwise.
    fn require_val_fields(
        kind: &ConstantKind,
        val_header: &crate::region::ObjectHeader,
        val_offset: usize,
    ) -> OleanResult<()> {
        // Number of boxed pointer fields the per-kind reader dereferences.
        let expected: u8 = match kind {
            // toConstantVal + all + rules
            ConstantKind::Recursor => 3,
            // toConstantVal + all + ctors
            ConstantKind::Inductive => 3,
            // toConstantVal + induct
            ConstantKind::Constructor => 2,
            // toConstantVal only (kind is an unboxed scalar at +16, read
            // defensively by `read_quot_kind`). Axiom / Definition / Theorem /
            // Opaque and any future kind likewise only require `toConstantVal`
            // here; their optional `value`/`hints`/`safety` slots are guarded
            // individually by the respective scalar readers.
            _ => 1,
        };
        if val_header.other < expected {
            return Err(OleanError::Region(format!(
                "malformed {kind:?}Val at offset {val_offset} declares {} boxed field(s), expected at least {expected}",
                val_header.other
            )));
        }
        Ok(())
    }

    /// Read the base ConstantVal fields: name, level_params, type.
    ///
    /// XxxVal structures inherit from ConstantVal. Field 0 (+8) is a pointer
    /// to the ConstantVal which contains name, levelParams, and type.
    fn read_constant_val_fields(
        &self,
        val_offset: usize,
    ) -> OleanResult<(String, Vec<String>, Option<crate::expr::ParsedExpr>)> {
        let const_val_ptr = self.read_u64_at(val_offset + 8)?;

        let (name_ptr, level_params_ptr, type_ptr) = if is_ptr(const_val_ptr) {
            let cv_offset = self.ptr_to_offset(const_val_ptr)?;
            (
                self.read_u64_at(cv_offset + 8)?,
                self.read_u64_at(cv_offset + 16)?,
                self.read_u64_at(cv_offset + 24)?,
            )
        } else {
            // Fields inline (fallback)
            (
                const_val_ptr,
                self.read_u64_at(val_offset + 16)?,
                self.read_u64_at(val_offset + 24)?,
            )
        };

        let name = self.resolve_name_ptr(name_ptr)?;
        let level_params = self.read_level_param_names(level_params_ptr)?;
        let type_ = if is_ptr(type_ptr) {
            Some(self.read_expr_at(self.ptr_to_offset(type_ptr)?)?)
        } else {
            None
        };

        Ok((name, level_params, type_))
    }

    /// Read the value expression for definitions, theorems, and opaques.
    ///
    /// When `skip_proof_values` is set, the proof body of a `Theorem`/`Opaque`
    /// is NOT reconstructed (returns `None`): the kernel never δ-unfolds those
    /// kinds, so a trusted dependency's proof term is dead weight whose `Expr`
    /// reconstruction is the peak-RSS cost the per-constant loader avoids. A
    /// `Definition` value is ALWAYS read (it is δ-reducible and may be needed for
    /// definitional-equality unfolding of the target).
    fn read_constant_value(
        &self,
        kind: &ConstantKind,
        val_offset: usize,
        val_header: &crate::region::ObjectHeader,
        skip_proof_values: bool,
    ) -> OleanResult<Option<crate::expr::ParsedExpr>> {
        if skip_proof_values && matches!(kind, ConstantKind::Theorem | ConstantKind::Opaque) {
            return Ok(None);
        }
        let needs_value = matches!(
            kind,
            ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
        );
        if needs_value && val_header.other >= 2 {
            let value_ptr = self.read_u64_at(val_offset + 16)?;
            if is_ptr(value_ptr) {
                return Ok(Some(self.read_expr_at(self.ptr_to_offset(value_ptr)?)?));
            }
        }
        Ok(None)
    }

    /// Read ReducibilityHints for definition constants.
    pub(crate) fn read_reducibility_hints(
        &self,
        kind: &ConstantKind,
        val_offset: usize,
        val_header: &crate::region::ObjectHeader,
    ) -> OleanResult<Option<ReducibilityHintsData>> {
        if *kind != ConstantKind::Definition || val_header.other < 3 {
            return Ok(None);
        }
        let hints_ptr = self.read_u64_at(val_offset + 24)?;
        if !is_ptr(hints_ptr) {
            return Ok(None);
        }
        let hints_off = self.ptr_to_offset(hints_ptr)?;
        let hints_header = self.read_header_at(hints_off)?;
        Ok(Some(match hints_header.tag {
            0 => ReducibilityHintsData::Opaque,
            1 => ReducibilityHintsData::Abbrev,
            2 => {
                let height_raw = self.read_u64_at(hints_off + 8)?;
                let height = if height_raw & 1 == 1 {
                    (height_raw >> 1) as u32
                } else {
                    0
                };
                ReducibilityHintsData::Regular(height)
            }
            _ => ReducibilityHintsData::Regular(0),
        }))
    }

    /// Read the `DefinitionSafety` flag for a definition constant.
    ///
    /// Two on-disk `DefnVal` layouts are recognized, discriminated by the
    /// word at `val_offset + 32`:
    ///
    /// **Real Lean 4 layout** (every Lean-produced `.olean`; verified against
    /// v4.30.0-rc2 `src/Lean/Declaration.lean:120-131`): `DefinitionVal
    /// extends ConstantVal where value, hints, safety, all : List Name`. The
    /// compacted object has FOUR boxed fields — `toConstantVal` (+8), `value`
    /// (+16), `hints` (+24), `all` (+32, a List pointer) — with header
    /// `other = 4`, `cs_sz = 48`, and `safety` stored as an UNBOXED `u8` in
    /// the trailing scalar area at `+40` (= `8 + 8*other`). The on-disk tag
    /// order is Lean's declaration order (`Declaration.lean:116-118`:
    /// `inductive DefinitionSafety where | «unsafe» | safe | «partial»`):
    /// **0 = unsafe, 1 = safe, 2 = partial** — NOT Clean's
    /// [`DefinitionSafety::from_tag`] order. Empirically pinned against the
    /// v4.30.0-rc2 toolchain: across `Init/Util` and
    /// `Init/Data/ByteArray/Basic` (base + `.olean.private`, 212 definitions)
    /// every known `unsafe def` reads 0, every ordinary/aux def reads 1, and
    /// every `._unsafe_rec` twin (which Lean marks `partial`) reads 2.
    ///
    /// **Legacy Clean-exporter layout** (`OleanExporter`,
    /// `export/constant_info.rs`): no `all` field; `safety` is a BOXED scalar
    /// at `+32` in Clean's tag order (`safe = 0`, `unsafe = 1`,
    /// `partial = 2`). Kept for round-trip compatibility with Clean-produced
    /// oleans.
    ///
    /// Returns `None` for non-definitions, for `DefnVal` objects that
    /// predate the fourth slot (`other < 4`), or when the header/slot
    /// matches neither known layout — a malformed or future-version payload
    /// degrades gracefully to "safety unknown" (treated as safe by callers,
    /// today's behavior) rather than fabricating a level.
    pub(crate) fn read_definition_safety(
        &self,
        kind: &ConstantKind,
        val_offset: usize,
        val_header: &crate::region::ObjectHeader,
    ) -> OleanResult<Option<DefinitionSafety>> {
        if *kind != ConstantKind::Definition || val_header.other < 4 {
            return Ok(None);
        }
        let raw = self.read_u64_at(val_offset + 32)?;
        // Legacy Clean-exporter layout: boxed safety scalar at +32, Clean
        // tag order (safe=0, unsafe=1, partial=2).
        if is_scalar(raw) {
            return Ok(DefinitionSafety::from_tag(unbox_scalar(raw)));
        }
        // Real Lean layout: +32 is the `all : List Name` pointer; safety is
        // the unboxed u8 at 8 + 8*other, in Lean's on-disk tag order
        // (unsafe=0, safe=1, partial=2). Guarded by the exact header shape
        // probed on real v4.30 oleans (other=4, cs_sz=48) so an unknown
        // future layout degrades to None instead of misreading a byte.
        if is_ptr(raw) && val_header.other == 4 && val_header.cs_sz == 48 {
            let scalar_off = val_offset + 8 + 8 * usize::from(val_header.other);
            return Ok(match self.data.get(scalar_off).copied() {
                Some(0) => Some(DefinitionSafety::Unsafe),
                Some(1) => Some(DefinitionSafety::Safe),
                Some(2) => Some(DefinitionSafety::Partial),
                _ => None,
            });
        }
        Ok(None)
    }

    /// Read InductiveVal extra data
    /// InductiveVal extends ConstantVal with these additional fields:
    ///   numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive
    ///
    /// Actual observed layout (with inheritance and scalar inline):
    ///   +8:  toConstantVal ptr
    ///   +16: numParams (inline scalar Nat)
    ///   +24: numIndices (inline scalar Nat)
    ///   +32: all (List Name ptr)
    ///   +40: ctors (List Name ptr)
    ///   +48: numNested (inline scalar Nat)
    ///   +56: padding or bool flags
    ///   +64: more data...
    pub(crate) fn read_inductive_val_data(
        &self,
        val_offset: usize,
    ) -> OleanResult<InductiveValData> {
        // Observed layout from debug output:
        // +16 and +24 are scalar Nats (numParams, numIndices)
        // +32 and +40 are pointer fields (all, ctors)
        // +48 is scalar Nat (numNested)
        // Bools follow after

        let num_params = self.read_u32_at(val_offset + 16, "numParams")?;
        let num_indices = self.read_u32_at(val_offset + 24, "numIndices")?;

        let all_ptr = self.read_u64_at(val_offset + 32)?;
        let all = if is_ptr(all_ptr) {
            self.read_name_list(all_ptr)?
        } else {
            Vec::new()
        };

        let ctors_ptr = self.read_u64_at(val_offset + 40)?;
        let ctors = if is_ptr(ctors_ptr) {
            self.read_name_list(ctors_ptr)?
        } else {
            Vec::new()
        };

        let num_nested = self.read_nat_at(val_offset + 48)?;
        // Lean 4: isNested = numNested > 0 (see Declaration.lean:317)
        let is_nested = num_nested > 0;

        // Bool flags - they're packed as individual bytes, not as Lean scalars
        // In Lean 4 runtime, Bool is a UInt8 (0 or 1) stored directly
        // Look at raw bytes at +56, +57, +58
        let is_rec = self.data.get(val_offset + 56).copied().unwrap_or(0) != 0;
        let is_unsafe = self.data.get(val_offset + 57).copied().unwrap_or(0) != 0;
        let is_reflexive = self.data.get(val_offset + 58).copied().unwrap_or(0) != 0;

        Ok(InductiveValData {
            num_params,
            num_indices,
            all,
            ctors,
            is_rec,
            is_unsafe,
            is_reflexive,
            is_nested,
        })
    }

    /// Read ConstructorVal extra data
    /// Layout (after ConstantVal pointer at +8):
    ///   +16: induct (Name)
    ///   +24: cidx (Nat, scalar)
    ///   +32: numParams (Nat, scalar)
    ///   +40: numFields (Nat, scalar)
    ///   +48: isUnsafe (Bool, scalar)
    pub(crate) fn read_constructor_val_data(
        &self,
        val_offset: usize,
    ) -> OleanResult<ConstructorValData> {
        let induct_ptr = self.read_u64_at(val_offset + 16)?;
        let induct = self.resolve_name_ptr(induct_ptr)?;

        let cidx = self.read_u32_at(val_offset + 24, "cidx")?;
        let num_params = self.read_u32_at(val_offset + 32, "numParams")?;
        let num_fields = self.read_u32_at(val_offset + 40, "numFields")?;
        let is_unsafe = self.read_bool_at(val_offset + 48)?;

        Ok(ConstructorValData {
            induct,
            cidx,
            num_params,
            num_fields,
            is_unsafe,
        })
    }

    /// Read the `QuotVal.kind` discriminant for a quotient primitive.
    ///
    /// Layout (mirrors `OleanExporter::write_quotient_info`):
    ///   +8:  ConstantVal pointer (name, levelParams, type)
    ///   +16: kind (`QuotKind`, scalar: 0=Type, 1=Mk, 2=Lift, 3=Ind, 4=Sound)
    ///
    /// Returns `None` when the slot is not a scalar or carries an
    /// unrecognized tag, so a malformed payload degrades gracefully to
    /// "kind unknown" instead of erroring or fabricating a kind.
    pub(crate) fn read_quot_kind(&self, val_offset: usize) -> OleanResult<Option<ParsedQuotKind>> {
        let raw = self.read_u64_at(val_offset + 16)?;
        if !is_scalar(raw) {
            return Ok(None);
        }
        Ok(ParsedQuotKind::from_tag(unbox_scalar(raw)))
    }

    /// Read RecursorVal extra data
    /// Layout (after ConstantVal pointer at +8):
    ///   +16: all (List Name)
    ///   +24: numParams (Nat, scalar)
    ///   +32: numIndices (Nat, scalar)
    ///   +40: numMotives (Nat, scalar)
    ///   +48: numMinors (Nat, scalar)
    ///   +56: rules (List RecursorRule)
    ///   +64: k (Bool, scalar)
    ///   +72: isUnsafe (Bool, scalar)
    fn read_recursor_val_data(&self, val_offset: usize) -> OleanResult<RecursorValData> {
        let all_ptr = self.read_u64_at(val_offset + 16)?;
        let all = self.read_name_list(all_ptr)?;

        let num_params = self.read_u32_at(val_offset + 24, "numParams")?;
        let num_indices = self.read_u32_at(val_offset + 32, "numIndices")?;
        let num_motives = self.read_u32_at(val_offset + 40, "numMotives")?;
        let num_minors = self.read_u32_at(val_offset + 48, "numMinors")?;

        let rules_ptr = self.read_u64_at(val_offset + 56)?;
        let rules = self.read_recursor_rules(rules_ptr)?;

        let k = self.read_bool_at(val_offset + 64)?;
        let is_unsafe = self.read_bool_at(val_offset + 72)?;

        Ok(RecursorValData {
            all,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            rules,
            k,
            is_unsafe,
        })
    }

    /// Read a list of RecursorRule
    pub(crate) fn read_recursor_rules(&self, ptr: u64) -> OleanResult<Vec<RecursorRuleData>> {
        const MAX_ITERATIONS: usize = 10_000;

        let mut rules = Vec::new();
        let mut current_ptr = ptr;

        for _i in 0..MAX_ITERATIONS {
            if is_scalar(current_ptr) || !is_ptr(current_ptr) {
                return Ok(rules);
            }

            let offset = self.ptr_to_offset(current_ptr)?;
            let header = self.read_header_at(offset)?;

            match (header.tag, header.other) {
                (1, 2) => {
                    // cons
                    let head_ptr = self.read_u64_at(offset + 8)?;
                    let tail_ptr = self.read_u64_at(offset + 16)?;

                    if is_ptr(head_ptr) {
                        let rule = self.read_recursor_rule(head_ptr)?;
                        rules.push(rule);
                    }
                    current_ptr = tail_ptr;
                }
                _ => return Ok(rules), // nil or unknown
            }
        }

        // Check if list terminated exactly at the limit (valid case)
        if is_scalar(current_ptr) || !is_ptr(current_ptr) {
            return Ok(rules);
        }

        // List continues beyond limit - this is the error case
        Err(OleanError::IterationLimitExceeded {
            limit: MAX_ITERATIONS,
            context: "recursor rules",
        })
    }

    /// Read a single RecursorRule
    /// Layout:
    ///   +8: ctor (Name)
    ///   +16: nfields (Nat, scalar)
    ///   +24: rhs (Expr)
    fn read_recursor_rule(&self, ptr: u64) -> OleanResult<RecursorRuleData> {
        let offset = self.ptr_to_offset(ptr)?;

        let ctor_ptr = self.read_u64_at(offset + 8)?;
        let ctor = self.resolve_name_ptr(ctor_ptr)?;

        let num_fields = self.read_u32_at(offset + 16, "nfields")?;

        let rhs_ptr = self.read_u64_at(offset + 24)?;
        let rhs = if is_ptr(rhs_ptr) {
            let rhs_off = self.ptr_to_offset(rhs_ptr)?;
            Some(self.read_expr_at(rhs_off)?)
        } else {
            None
        };

        Ok(RecursorRuleData {
            ctor,
            num_fields,
            rhs,
        })
    }

    /// Read a Nat at offset
    ///
    /// Returns an error if the value is too large to fit in u64.
    fn read_nat_at(&self, offset: usize) -> OleanResult<u64> {
        let val = self.read_u64_at(offset)?;
        let bignat = self.read_bignat_value(val)?;
        bignat.to_u64().ok_or_else(|| {
            OleanError::Region(format!("Nat value too large for u64 at offset {offset}"))
        })
    }

    /// Read a u32 from a Nat, with overflow checking
    fn read_u32_at(&self, offset: usize, field: &str) -> OleanResult<u32> {
        let val = self.read_nat_at(offset)?;
        u32::try_from(val)
            .map_err(|_| OleanError::Region(format!("{field} value too large: {val}")))
    }

    /// Public wrapper for load-only parser (#2428).
    pub(crate) fn read_u32_at_pub(&self, offset: usize, field: &str) -> OleanResult<u32> {
        self.read_u32_at(offset, field)
    }

    /// Read a `Bool` stored as an *inline scalar field* at `offset`.
    ///
    /// In Lean 4's compact-object layout, trivial scalar fields (`Bool`,
    /// `UInt8`, …) that follow all of an object's boxed pointer fields are
    /// packed into the object's scalar area as raw bytes — a `Bool` is a single
    /// byte holding `1` (`true`) or `0` (`false`). It is NOT a runtime object,
    /// so it carries no pointer tag.
    ///
    /// The previous implementation treated the field as a *boxed tagged scalar*
    /// and applied `unbox_scalar` (i.e. `byte >> 1`), which silently turned the
    /// `true` encoding (`0x01`) into `0` and therefore read every such `Bool`
    /// as `false`. That is why `RecursorVal.k` (the subsingleton /
    /// K-elimination flag, `true` for `Eq.rec` / `HEq.rec`) came back `false`,
    /// disabling K-reduction and making valid heterogeneous-equality terms like
    /// `eq_of_heq` and `cast_eq` fail to type-check (WS7). Reading the raw
    /// inline byte fixes that completeness gap without changing any `false`
    /// case (a `0x00` byte still reads `false`).
    fn read_bool_at(&self, offset: usize) -> OleanResult<bool> {
        // The inline scalar byte is the least-significant byte of the
        // little-endian word at `offset`.
        let val = self.read_u64_at(offset)?;
        Ok((val & 0xFF) != 0)
    }

    /// Public wrapper for load-only parser (#2428).
    pub(crate) fn read_bool_at_pub(&self, offset: usize) -> OleanResult<bool> {
        self.read_bool_at(offset)
    }

    /// Read a list of names
    pub(crate) fn read_name_list(&self, ptr: u64) -> OleanResult<Vec<String>> {
        const MAX_ITERATIONS: usize = 100_000;

        let mut names = Vec::new();
        let mut current_ptr = ptr;

        for _i in 0..MAX_ITERATIONS {
            if is_scalar(current_ptr) || !is_ptr(current_ptr) {
                return Ok(names);
            }

            let offset = self.ptr_to_offset(current_ptr)?;
            let header = self.read_header_at(offset)?;

            match (header.tag, header.other) {
                (1, 2) => {
                    // cons
                    let head_ptr = self.read_u64_at(offset + 8)?;
                    let tail_ptr = self.read_u64_at(offset + 16)?;

                    let name = self.resolve_name_ptr(head_ptr)?;
                    names.push(name);
                    current_ptr = tail_ptr;
                }
                _ => return Ok(names), // nil or unknown
            }
        }

        // Check if list terminated exactly at the limit (valid case)
        if is_scalar(current_ptr) || !is_ptr(current_ptr) {
            return Ok(names);
        }

        // List continues beyond limit - this is the error case
        Err(OleanError::IterationLimitExceeded {
            limit: MAX_ITERATIONS,
            context: "name list",
        })
    }

    /// Read level parameter names (list of names)
    fn read_level_param_names(&self, ptr: u64) -> OleanResult<Vec<String>> {
        self.read_name_list(ptr)
    }
}

#[cfg(test)]
mod inline_scalar_bool_tests {
    //! WS7 regression: inline scalar `Bool` fields (e.g. `RecursorVal.k`) are
    //! stored as raw bytes in the object's scalar area, NOT as boxed tagged
    //! scalars. The decoder must read the raw byte, not `value >> 1`.
    use crate::region::CompactedRegion;

    /// Build a `CompactedRegion` over a little-endian `u64` word so we can
    /// exercise the byte-level `Bool` decode in isolation.
    fn region_from_word(word: u64) -> Vec<u8> {
        word.to_le_bytes().to_vec()
    }

    #[test]
    fn test_read_bool_at_true_byte_decodes_true() {
        // Lean stores `Bool.true` for an inline scalar field as the raw byte
        // 0x01. Before the WS7 fix, `unbox_scalar(0x01) = 0x01 >> 1 = 0` made
        // this read `false`, disabling `Eq.rec`/`HEq.rec` K-reduction.
        let bytes = region_from_word(0x0000_0000_0000_0001);
        let region = CompactedRegion::new(&bytes, 0);
        assert!(
            region.read_bool_at_pub(0).expect("read inline scalar bool"),
            "inline scalar byte 0x01 must decode as true"
        );
    }

    #[test]
    fn test_read_bool_at_false_byte_decodes_false() {
        // A non-K recursor (e.g. `Nat.rec`) stores k = 0x00.
        let bytes = region_from_word(0x0000_0000_0000_0000);
        let region = CompactedRegion::new(&bytes, 0);
        assert!(
            !region.read_bool_at_pub(0).expect("read inline scalar bool"),
            "inline scalar byte 0x00 must decode as false"
        );
    }

    #[test]
    fn test_read_bool_at_ignores_high_bytes() {
        // The scalar area may pack the adjacent `isUnsafe` byte and padding into
        // the high bytes of the word; only the least-significant byte is `k`.
        let bytes = region_from_word(0x0701_0010_0000_0001);
        let region = CompactedRegion::new(&bytes, 0);
        assert!(
            region.read_bool_at_pub(0).expect("read inline scalar bool"),
            "only the low byte determines the Bool; high bytes are unrelated fields"
        );

        let bytes_false = region_from_word(0x0701_0010_0000_0000);
        let region_false = CompactedRegion::new(&bytes_false, 0);
        assert!(
            !region_false
                .read_bool_at_pub(0)
                .expect("read inline scalar bool"),
            "low byte 0x00 must decode false even with non-zero high bytes"
        );
    }
}

#[cfg(test)]
mod definition_safety_layout_tests {
    //! Dual-layout `read_definition_safety` pins (census 2026-07-06 Class 3).
    //!
    //! Real Lean 4 `DefnVal`s (v4.30.0-rc2 `Declaration.lean:120-131`) carry
    //! `all : List Name` as the fourth BOXED field (+32) and `safety` as an
    //! UNBOXED u8 at +40, with Lean's on-disk tag order `| «unsafe» | safe |
    //! «partial»` (`Declaration.lean:116-118`): 0=unsafe, 1=safe, 2=partial.
    //! Clean's own exporter writes a legacy layout instead: a BOXED safety
    //! scalar at +32 in Clean's tag order (safe=0). Both must decode; an
    //! unrecognized shape must degrade to `None` (treated as safe — the
    //! pre-existing behavior), never guess.
    use super::super::{ConstantKind, DefinitionSafety};
    use crate::region::{CompactedRegion, ObjectHeader};

    /// Build a synthetic 48-byte real-Lean `DefnVal` object at offset 0:
    /// header (ignored — passed separately), 4 boxed fields, then the
    /// trailing scalar area whose first byte is `safety`.
    fn real_lean_defn_val(safety_byte: u8) -> Vec<u8> {
        let mut b = vec![0u8; 48];
        // +8 toConstantVal, +16 value, +24 hints, +32 all — plausible even,
        // non-null "pointers" (never dereferenced by the safety reader; +32
        // only needs `is_ptr` to hold, exactly as in a real compacted region).
        for (i, off) in [8usize, 16, 24, 32].iter().enumerate() {
            let fake_ptr = 0x1000u64 + (i as u64) * 0x100;
            b[*off..*off + 8].copy_from_slice(&fake_ptr.to_le_bytes());
        }
        b[40] = safety_byte;
        b
    }

    fn real_lean_header() -> ObjectHeader {
        // Exact header shape probed on every v4.30 DefnVal (212/212).
        ObjectHeader {
            rc: 1,
            cs_sz: 48,
            other: 4,
            tag: 0,
        }
    }

    fn decode(bytes: &[u8], header: &ObjectHeader) -> Option<DefinitionSafety> {
        let region = CompactedRegion::new(bytes, 0);
        region
            .read_definition_safety(&ConstantKind::Definition, 0, header)
            .expect("in-bounds safety read must not error")
    }

    #[test]
    fn test_real_lean_layout_tag_order_unsafe_safe_partial() {
        // Lean's on-disk order (Declaration.lean:116-118): 0=unsafe, 1=safe,
        // 2=partial. E.g. `ptrEqList` (unsafe def) stores 0; a `._unsafe_rec`
        // twin (partial) stores 2.
        assert_eq!(
            decode(&real_lean_defn_val(0), &real_lean_header()),
            Some(DefinitionSafety::Unsafe),
            "on-disk 0 must decode as unsafe (Lean declaration order)"
        );
        assert_eq!(
            decode(&real_lean_defn_val(1), &real_lean_header()),
            Some(DefinitionSafety::Safe),
            "on-disk 1 must decode as safe"
        );
        assert_eq!(
            decode(&real_lean_defn_val(2), &real_lean_header()),
            Some(DefinitionSafety::Partial),
            "on-disk 2 must decode as partial"
        );
        assert_eq!(
            decode(&real_lean_defn_val(3), &real_lean_header()),
            None,
            "an unknown on-disk tag must degrade to None, never guess"
        );
    }

    #[test]
    fn test_real_lean_layout_requires_probed_header_shape() {
        // A pointer at +32 with a header that matches NEITHER known layout
        // (e.g. a hypothetical 5-boxed-field future DefnVal) must return
        // None (safety unknown => treated safe) instead of misreading a byte.
        let bytes = real_lean_defn_val(0);
        let five_fields = ObjectHeader {
            rc: 1,
            cs_sz: 56,
            other: 5,
            tag: 0,
        };
        assert_eq!(
            decode(&bytes, &five_fields),
            None,
            "unknown header shape must fail closed to None"
        );
    }

    #[test]
    fn test_legacy_clean_exporter_layout_boxed_scalar_at_32() {
        // Clean's exporter layout: boxed scalar `(tag << 1) | 1` at +32 in
        // Clean's tag order (safe=0, unsafe=1, partial=2). The full
        // exporter round-trip is pinned separately in `export/tests.rs`;
        // this pins the reader branch in isolation.
        for (tag, expected) in [
            (0u64, DefinitionSafety::Safe),
            (1, DefinitionSafety::Unsafe),
            (2, DefinitionSafety::Partial),
        ] {
            let mut b = vec![0u8; 48];
            let boxed = (tag << 1) | 1;
            b[32..40].copy_from_slice(&boxed.to_le_bytes());
            assert_eq!(
                decode(&b, &real_lean_header()),
                Some(expected),
                "legacy boxed scalar tag {tag} must decode via Clean's from_tag"
            );
        }
    }
}
