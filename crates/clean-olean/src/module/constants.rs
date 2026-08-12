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
    #[cfg(test)]
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
            0 => ConstantKind::Axiom,
            1 => ConstantKind::Definition,
            2 => ConstantKind::Theorem,
            3 => ConstantKind::Opaque,
            4 => ConstantKind::Quot,
            5 => ConstantKind::Inductive,
            6 => ConstantKind::Constructor,
            7 => ConstantKind::Recursor,
            tag => return Err(OleanError::InvalidObjectTag { tag, offset }),
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

        // Read declaration safety for definitions, axioms, and opaques.
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
        if *kind != ConstantKind::Definition {
            return Ok(None);
        }
        if val_header.other < 3 {
            return Err(OleanError::Region(format!(
                "DefinitionVal at offset {val_offset} has no ReducibilityHints field"
            )));
        }
        let hints_ptr = self.read_u64_at(val_offset + 24)?;
        // `opaque` and `abbrev` are nullary constructors, so genuine Lean
        // oleans encode them directly as tagged scalars (1 and 3).  Treating
        // every non-pointer as "hints absent" silently discarded both cases.
        if is_scalar(hints_ptr) {
            return match unbox_scalar(hints_ptr) {
                0 => Ok(Some(ReducibilityHintsData::Opaque)),
                1 => Ok(Some(ReducibilityHintsData::Abbrev)),
                tag => Err(OleanError::Region(format!(
                    "invalid scalar ReducibilityHints constructor tag {tag} at offset {}",
                    val_offset + 24
                ))),
            };
        }
        if !is_ptr(hints_ptr) {
            return Err(OleanError::InvalidPointer {
                ptr: hints_ptr,
                offset: val_offset + 24,
            });
        }

        // Clean's pre-ABI-parity exporter represented all three constructors
        // as heap objects with `cs_sz = 0`, and represented regular's `UInt32`
        // as a tagged scalar word. Preserve that exact legacy shape so old
        // Clean-produced fixtures continue to round-trip. Genuine Lean uses a
        // 16-byte tag-2 object with an unboxed UInt32 at +8.
        let hints_off = self.ptr_to_offset(hints_ptr)?;
        let hints_header = self.read_header_at(hints_off)?;
        let hints = match hints_header.tag {
            0 | 1 => {
                if hints_header.other != 0 || hints_header.cs_sz != 0 {
                    return Err(OleanError::Region(format!(
                        "invalid legacy nullary ReducibilityHints object shape \
                         (tag={}, other={}, cs_sz={}) at offset {hints_off}",
                        hints_header.tag, hints_header.other, hints_header.cs_sz
                    )));
                }
                if hints_header.tag == 0 {
                    ReducibilityHintsData::Opaque
                } else {
                    ReducibilityHintsData::Abbrev
                }
            }
            2 => {
                let height_raw = self.read_u64_at(hints_off + 8)?;
                let height = match (hints_header.other, hints_header.cs_sz) {
                    // Real Lean 4 ABI (`regular (height : UInt32)`): the
                    // UInt32 is an unboxed little-endian scalar in the first
                    // four bytes of the eight-byte scalar area. The remaining
                    // bytes are alignment padding and carry no semantics.
                    (0, 16) => (height_raw & u64::from(u32::MAX)) as u32,
                    // Exact legacy Clean-exporter shape.
                    (0, 0) if is_scalar(height_raw) => u32::try_from(unbox_scalar(height_raw))
                        .map_err(|_| {
                            OleanError::Region(format!(
                                "legacy ReducibilityHints height exceeds UInt32 at offset {}",
                                hints_off + 8
                            ))
                        })?,
                    _ => {
                        return Err(OleanError::Region(format!(
                            "invalid regular ReducibilityHints object shape \
                             (other={}, cs_sz={}, raw={height_raw:#018x}) at offset {hints_off}",
                            hints_header.other, hints_header.cs_sz
                        )));
                    }
                };
                ReducibilityHintsData::Regular(height)
            }
            tag => {
                return Err(OleanError::InvalidObjectTag {
                    tag,
                    offset: hints_off,
                });
            }
        };
        Ok(Some(hints))
    }

    /// Read the declaration-safety authority carried by a constant value.
    ///
    /// Two on-disk `DefnVal` layouts are recognized, discriminated by their
    /// exact `(other, cs_sz)` header shape:
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
    /// **0 = unsafe, 1 = safe, 2 = partial**. Empirically pinned against the
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
    /// `AxiomVal.isUnsafe` and `OpaqueVal.isUnsafe` use the same authority
    /// boundary. Real Lean v4.30 layouts are:
    ///
    /// - `AxiomVal`: `(other=1, cs_sz=24)`, raw Bool at `+16`;
    /// - `OpaqueVal`: `(other=3, cs_sz=40)`, raw Bool at `+32` after
    ///   `toConstantVal`, `value`, and pointer-reordered `all`.
    ///
    /// The legacy Clean writer used an extra boxed field and a tagged Bool:
    /// `(2, 0)` at `+16` for axioms and `(4, 0)` at `+24` for opaques.
    ///
    /// Returns `None` only for kinds with no declaration-safety field. A
    /// missing, malformed, future layout, invalid Bool, or unknown safety tag
    /// is an error: safety metadata must never degrade to `safe`.
    pub(crate) fn read_definition_safety(
        &self,
        kind: &ConstantKind,
        val_offset: usize,
        val_header: &crate::region::ObjectHeader,
    ) -> OleanResult<Option<DefinitionSafety>> {
        let safety = match kind {
            ConstantKind::Axiom => match (val_header.other, val_header.cs_sz) {
                (1, 24) => {
                    if self.read_inline_bool_exact(val_offset + 16, "AxiomVal.isUnsafe")? {
                        DefinitionSafety::Unsafe
                    } else {
                        DefinitionSafety::Safe
                    }
                }
                (2, 0) => {
                    if self.read_boxed_bool_exact(val_offset + 16, "AxiomVal.isUnsafe")? {
                        DefinitionSafety::Unsafe
                    } else {
                        DefinitionSafety::Safe
                    }
                }
                (other, cs_sz) => {
                    return Err(OleanError::Region(format!(
                        "unrecognized AxiomVal safety layout \
                         (other={other}, cs_sz={cs_sz}) at offset {val_offset}"
                    )));
                }
            },
            ConstantKind::Opaque => match (val_header.other, val_header.cs_sz) {
                (3, 40) => {
                    if self.read_inline_bool_exact(val_offset + 32, "OpaqueVal.isUnsafe")? {
                        DefinitionSafety::Unsafe
                    } else {
                        DefinitionSafety::Safe
                    }
                }
                (4, 0) => {
                    if self.read_boxed_bool_exact(val_offset + 24, "OpaqueVal.isUnsafe")? {
                        DefinitionSafety::Unsafe
                    } else {
                        DefinitionSafety::Safe
                    }
                }
                (other, cs_sz) => {
                    return Err(OleanError::Region(format!(
                        "unrecognized OpaqueVal safety layout \
                         (other={other}, cs_sz={cs_sz}) at offset {val_offset}"
                    )));
                }
            },
            ConstantKind::Definition => match (val_header.other, val_header.cs_sz) {
                // Real Lean layout: +32 is `all : List Name`; safety is the
                // unboxed u8 at +40 in Lean declaration order.
                (4, 48) => {
                    let scalar_off = val_offset + 40;
                    let tag =
                        self.data
                            .get(scalar_off)
                            .copied()
                            .ok_or(OleanError::OutOfBounds {
                                offset: scalar_off,
                                size: self.data.len(),
                            })?;
                    DefinitionSafety::from_tag(u64::from(tag)).ok_or_else(|| {
                        OleanError::Region(format!(
                            "invalid DefinitionSafety tag {tag} at offset {scalar_off}"
                        ))
                    })?
                }
                // Exact legacy Clean-exporter layout: a boxed scalar at +32 in
                // the historical Clean order safe=0, unsafe=1, partial=2.
                (4, 0) => {
                    let raw = self.read_u64_at(val_offset + 32)?;
                    if !is_scalar(raw) {
                        return Err(OleanError::Region(format!(
                            "legacy DefinitionSafety at offset {} is not a tagged scalar",
                            val_offset + 32
                        )));
                    }
                    match unbox_scalar(raw) {
                        0 => DefinitionSafety::Safe,
                        1 => DefinitionSafety::Unsafe,
                        2 => DefinitionSafety::Partial,
                        tag => {
                            return Err(OleanError::Region(format!(
                                "invalid legacy DefinitionSafety tag {tag} at offset {}",
                                val_offset + 32
                            )));
                        }
                    }
                }
                (other, cs_sz) => {
                    return Err(OleanError::Region(format!(
                        "unrecognized DefinitionVal safety layout \
                         (other={other}, cs_sz={cs_sz}) at offset {val_offset}"
                    )));
                }
            },
            _ => return Ok(None),
        };
        Ok(Some(safety))
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

        // The header keys the field layout, so it must be read BEFORE
        // `numNested` — two real Lean layouts exist for InductiveVal:
        //
        //   (6, 64) and legacy (7, 0): Lean >= 4.9 — `numNested : Nat` is the
        //   sixth object field (+48) and the three Bool flags follow at +56.
        //
        //   (5, 56): Lean <= 4.8 — `InductiveVal` HAS NO `numNested` field.
        //   The toolchain's own Lean/Declaration.lean (v4.8.0:220-258) ends
        //   `... isRec : Bool, isUnsafe : Bool, isReflexive : Bool,
        //   isNested : Bool`, so there are FOUR flags and they ARE the scalar
        //   area at +48. The
        //   pinned Lean<->Clean bridge toolchain (v4.8.0) emits this shape
        //   for every core inductive — first caught failing on `PEmpty` in
        //   Init.Prelude once the exact-layout check landed.
        //
        // Reading v4.8 bytes through the v4.9+ offsets would return `isRec`
        // as `numNested` (every recursive inductive would read as "nested")
        // and pull the Bool flags from the next object's bytes, so the shape
        // selects the offsets and anything else stays fail-closed.
        let header = self.read_header_at(val_offset)?;
        // `nested_is_a_flag` distinguishes WHERE `isNested` comes from, which the
        // two shapes disagree on: >=4.9 derives it from the `numNested` count,
        // 4.8 stores it as the fourth raw Bool. Deriving it from a hardcoded
        // `numNested = 0` on the 4.8 shape reads EVERY nested inductive as
        // non-nested — silently, since 0 is a legal count.
        let (num_nested, bools_at, nested_is_a_flag) = match (header.other, header.cs_sz) {
            (6, 64) | (7, 0) => (self.read_nat_at(val_offset + 48)?, val_offset + 56, false),
            (5, 56) => (0, val_offset + 48, true),
            (other, cs_sz) => {
                return Err(OleanError::Region(format!(
                    "unrecognized InductiveVal Bool layout (other={other}, cs_sz={cs_sz}) at offset {val_offset}"
                )));
            }
        };
        // Bool flags are consecutive raw bytes in real Lean (both shapes) and
        // Clean's legacy packed-word layout. Validate the exact 0/1 domain: an
        // absent or future encoding must not turn `isUnsafe` into false.
        let is_rec = self.read_inline_bool_exact(bools_at, "InductiveVal.isRec")?;
        let is_unsafe = self.read_inline_bool_exact(bools_at + 1, "InductiveVal.isUnsafe")?;
        let is_reflexive = self.read_inline_bool_exact(bools_at + 2, "InductiveVal.isReflexive")?;
        // >=4.9: `isNested = numNested > 0` (Declaration.lean:317). 4.8: the
        // fourth flag byte, validated to the same exact 0/1 domain as the
        // others so a future encoding cannot silently read as `false`.
        let is_nested = if nested_is_a_flag {
            self.read_inline_bool_exact(bools_at + 3, "InductiveVal.isNested")?
        } else {
            num_nested > 0
        };

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
        let header = self.read_header_at(val_offset)?;
        let is_unsafe = match (header.other, header.cs_sz) {
            (5, 56) => self.read_inline_bool_exact(val_offset + 48, "ConstructorVal.isUnsafe")?,
            (6, 0) => self.read_boxed_bool_exact(val_offset + 48, "ConstructorVal.isUnsafe")?,
            (other, cs_sz) => {
                return Err(OleanError::Region(format!(
                    "unrecognized ConstructorVal Bool layout \
                     (other={other}, cs_sz={cs_sz}) at offset {val_offset}"
                )));
            }
        };

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
    ///   +64: k (Bool, raw byte)
    ///   +65: isUnsafe (Bool, raw byte)
    fn read_recursor_val_data(&self, val_offset: usize) -> OleanResult<RecursorValData> {
        let all_ptr = self.read_u64_at(val_offset + 16)?;
        let all = self.read_name_list(all_ptr)?;

        let num_params = self.read_u32_at(val_offset + 24, "numParams")?;
        let num_indices = self.read_u32_at(val_offset + 32, "numIndices")?;
        let num_motives = self.read_u32_at(val_offset + 40, "numMotives")?;
        let num_minors = self.read_u32_at(val_offset + 48, "numMinors")?;

        let rules_ptr = self.read_u64_at(val_offset + 56)?;
        let rules = self.read_recursor_rules(rules_ptr)?;

        let (k, is_unsafe) = self.read_recursor_bool_flags(val_offset)?;

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

    /// Decode the two trailing `RecursorVal` Bool fields in either supported
    /// ABI. Real Lean packs them as raw bytes at `+64`/`+65` in a
    /// `(other=7, cs_sz=72)` object. The historical Clean writer used tagged
    /// scalar words at `+64`/`+72` with `(other=9, cs_sz=0)`.
    pub(crate) fn read_recursor_bool_flags(&self, val_offset: usize) -> OleanResult<(bool, bool)> {
        let header = self.read_header_at(val_offset)?;
        match (header.other, header.cs_sz) {
            (7, 72) => Ok((
                self.read_inline_bool_exact(val_offset + 64, "RecursorVal.k")?,
                self.read_inline_bool_exact(val_offset + 65, "RecursorVal.isUnsafe")?,
            )),
            (9, 0) => Ok((
                self.read_boxed_bool_exact(val_offset + 64, "RecursorVal.k")?,
                self.read_boxed_bool_exact(val_offset + 72, "RecursorVal.isUnsafe")?,
            )),
            (other, cs_sz) => Err(OleanError::Region(format!(
                "unrecognized RecursorVal Bool layout \
                 (other={other}, cs_sz={cs_sz}) at offset {val_offset}"
            ))),
        }
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

    /// Read an unboxed compact-object Bool and require Lean's exact `0 | 1`
    /// representation.
    fn read_inline_bool_exact(&self, offset: usize, field: &str) -> OleanResult<bool> {
        let value = self
            .data
            .get(offset)
            .copied()
            .ok_or(OleanError::OutOfBounds {
                offset,
                size: self.data.len(),
            })?;
        match value {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(OleanError::Region(format!(
                "invalid {field} Bool byte {value} at offset {offset}"
            ))),
        }
    }

    /// Read a legacy Clean boxed Bool and require a tagged scalar containing
    /// exactly `0 | 1`.
    fn read_boxed_bool_exact(&self, offset: usize, field: &str) -> OleanResult<bool> {
        let raw = self.read_u64_at(offset)?;
        if !is_scalar(raw) {
            return Err(OleanError::Region(format!(
                "{field} at offset {offset} is not a tagged scalar"
            )));
        }
        match unbox_scalar(raw) {
            0 => Ok(false),
            1 => Ok(true),
            value => Err(OleanError::Region(format!(
                "invalid {field} Bool tag {value} at offset {offset}"
            ))),
        }
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
mod reducibility_hints_layout_tests {
    //! Exact dual-layout pins for `ReducibilityHints`.
    //!
    //! Genuine Lean uses tagged scalars for the two nullary constructors and
    //! a 16-byte object with an unboxed `UInt32` for `regular`. Older Clean
    //! exports used heap objects with `cs_sz = 0` and a tagged height word.
    //! No other shape may silently mint reduction metadata.
    use super::super::{ConstantKind, ReducibilityHintsData};
    use crate::region::{CompactedRegion, ObjectHeader};

    const HINTS_OFFSET: usize = 40;

    fn definition_header() -> ObjectHeader {
        ObjectHeader {
            rc: 0,
            cs_sz: 40,
            other: 3,
            tag: 0,
        }
    }

    fn scalar_hints(tagged_constructor: u64) -> Vec<u8> {
        let mut bytes = vec![0u8; 32];
        bytes[24..32].copy_from_slice(&tagged_constructor.to_le_bytes());
        bytes
    }

    fn object_hints(tag: u8, other: u8, cs_sz: u16, payload: Option<u64>) -> Vec<u8> {
        let len = if payload.is_some() {
            HINTS_OFFSET + 16
        } else {
            HINTS_OFFSET + 8
        };
        let mut bytes = vec![0u8; len];
        bytes[24..32].copy_from_slice(&(HINTS_OFFSET as u64).to_le_bytes());
        bytes[HINTS_OFFSET + 4..HINTS_OFFSET + 6].copy_from_slice(&cs_sz.to_le_bytes());
        bytes[HINTS_OFFSET + 6] = other;
        bytes[HINTS_OFFSET + 7] = tag;
        if let Some(payload) = payload {
            bytes[HINTS_OFFSET + 8..HINTS_OFFSET + 16].copy_from_slice(&payload.to_le_bytes());
        }
        bytes
    }

    fn decode(bytes: &[u8]) -> crate::error::OleanResult<Option<ReducibilityHintsData>> {
        CompactedRegion::new(bytes, 0).read_reducibility_hints(
            &ConstantKind::Definition,
            0,
            &definition_header(),
        )
    }

    #[test]
    fn genuine_nullary_scalar_constructors_decode_exactly() {
        assert_eq!(
            decode(&scalar_hints(1)).expect("opaque scalar must decode"),
            Some(ReducibilityHintsData::Opaque)
        );
        assert_eq!(
            decode(&scalar_hints(3)).expect("abbrev scalar must decode"),
            Some(ReducibilityHintsData::Abbrev)
        );
    }

    #[test]
    fn genuine_regular_unboxed_uint32_decodes_without_scalar_shift() {
        let bytes = object_hints(2, 0, 16, Some(17));
        assert_eq!(
            decode(&bytes).expect("real regular object must decode"),
            Some(ReducibilityHintsData::Regular(17))
        );

        // Bytes above the UInt32 are ABI padding, not part of the height.
        let bytes = object_hints(2, 0, 16, Some(0xa5a5_a5a5_0000_0011));
        assert_eq!(
            decode(&bytes).expect("padding must not change the UInt32"),
            Some(ReducibilityHintsData::Regular(17))
        );
    }

    #[test]
    fn exact_legacy_clean_shapes_remain_readable() {
        assert_eq!(
            decode(&object_hints(0, 0, 0, None)).expect("legacy opaque"),
            Some(ReducibilityHintsData::Opaque)
        );
        assert_eq!(
            decode(&object_hints(1, 0, 0, None)).expect("legacy abbrev"),
            Some(ReducibilityHintsData::Abbrev)
        );
        assert_eq!(
            decode(&object_hints(2, 0, 0, Some((17 << 1) | 1))).expect("legacy regular"),
            Some(ReducibilityHintsData::Regular(17))
        );
    }

    #[test]
    fn malformed_or_unknown_hints_fail_closed() {
        let mut missing_field = definition_header();
        missing_field.other = 2;
        assert!(
            CompactedRegion::new(&scalar_hints(1), 0)
                .read_reducibility_hints(&ConstantKind::Definition, 0, &missing_field)
                .is_err(),
            "a definition without reducibility metadata must fail closed"
        );
        assert!(decode(&scalar_hints(5)).is_err(), "tag-2 needs its UInt32");
        assert!(decode(&scalar_hints(0)).is_err(), "null is not a hint");
        assert!(
            decode(&object_hints(7, 0, 8, None)).is_err(),
            "unknown heap constructor must not fabricate Regular(0)"
        );
        assert!(
            decode(&object_hints(2, 1, 16, Some(17))).is_err(),
            "regular has no pointer fields"
        );
        assert!(
            decode(&object_hints(2, 0, 8, Some(17))).is_err(),
            "unknown compact size must fail"
        );
        assert!(
            decode(&object_hints(2, 0, 0, Some(34))).is_err(),
            "legacy height must be a tagged scalar"
        );
        assert!(
            decode(&object_hints(0, 0, 8, None)).is_err(),
            "only the exact legacy heap-nullary shape is accepted"
        );
    }

    #[test]
    fn truncated_regular_payload_fails_closed() {
        let bytes = object_hints(2, 0, 16, None);
        assert!(decode(&bytes).is_err());
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
            region
                .read_inline_bool_exact(0, "Test.bool")
                .expect("read inline scalar bool"),
            "inline scalar byte 0x01 must decode as true"
        );
    }

    #[test]
    fn test_read_bool_at_false_byte_decodes_false() {
        // A non-K recursor (e.g. `Nat.rec`) stores k = 0x00.
        let bytes = region_from_word(0x0000_0000_0000_0000);
        let region = CompactedRegion::new(&bytes, 0);
        assert!(
            !region
                .read_inline_bool_exact(0, "Test.bool")
                .expect("read inline scalar bool"),
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
            region
                .read_inline_bool_exact(0, "Test.bool")
                .expect("read inline scalar bool"),
            "only the low byte determines the Bool; high bytes are unrelated fields"
        );

        let bytes_false = region_from_word(0x0701_0010_0000_0000);
        let region_false = CompactedRegion::new(&bytes_false, 0);
        assert!(
            !region_false
                .read_inline_bool_exact(0, "Test.bool")
                .expect("read inline scalar bool"),
            "low byte 0x00 must decode false even with non-zero high bytes"
        );
    }

    #[test]
    fn test_read_bool_at_rejects_non_bool_byte() {
        let bytes = region_from_word(2);
        let region = CompactedRegion::new(&bytes, 0);
        assert!(region.read_inline_bool_exact(0, "Test.bool").is_err());
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
    //! scalar at +32 in Clean's tag order (safe=0). Both exact layouts decode;
    //! every unknown shape or tag is rejected rather than gaining safe
    //! definitional authority.
    use super::super::{ConstantKind, DefinitionSafety};
    use crate::region::{CompactedRegion, ObjectHeader};

    /// Build a synthetic 48-byte real-Lean `DefnVal` object at offset 0:
    /// header (ignored — passed separately), 4 boxed fields, then the
    /// trailing scalar area whose first byte is `safety`.
    fn real_lean_defn_val(safety_byte: u8) -> Vec<u8> {
        let mut b = vec![0u8; 48];
        // +8 toConstantVal, +16 value, +24 hints, +32 all — plausible even,
        // non-null pointers (never dereferenced by the safety reader).
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

    fn decode(
        bytes: &[u8],
        header: &ObjectHeader,
    ) -> crate::error::OleanResult<Option<DefinitionSafety>> {
        let region = CompactedRegion::new(bytes, 0);
        region.read_definition_safety(&ConstantKind::Definition, 0, header)
    }

    #[test]
    fn test_real_lean_layout_tag_order_unsafe_safe_partial() {
        // Lean's on-disk order (Declaration.lean:116-118): 0=unsafe, 1=safe,
        // 2=partial. E.g. `ptrEqList` (unsafe def) stores 0; a `._unsafe_rec`
        // twin (partial) stores 2.
        assert_eq!(
            decode(&real_lean_defn_val(0), &real_lean_header()).expect("real unsafe"),
            Some(DefinitionSafety::Unsafe),
            "on-disk 0 must decode as unsafe (Lean declaration order)"
        );
        assert_eq!(
            decode(&real_lean_defn_val(1), &real_lean_header()).expect("real safe"),
            Some(DefinitionSafety::Safe),
            "on-disk 1 must decode as safe"
        );
        assert_eq!(
            decode(&real_lean_defn_val(2), &real_lean_header()).expect("real partial"),
            Some(DefinitionSafety::Partial),
            "on-disk 2 must decode as partial"
        );
        assert!(
            decode(&real_lean_defn_val(3), &real_lean_header()).is_err(),
            "an unknown on-disk tag must fail closed"
        );
    }

    #[test]
    fn test_real_lean_layout_requires_probed_header_shape() {
        // A header that matches neither known layout (e.g. a hypothetical
        // 5-boxed-field future DefnVal) must fail instead of misreading a byte.
        let bytes = real_lean_defn_val(0);
        let five_fields = ObjectHeader {
            rc: 1,
            cs_sz: 56,
            other: 5,
            tag: 0,
        };
        assert!(
            decode(&bytes, &five_fields).is_err(),
            "unknown header shape must fail closed"
        );

        let missing_safety = ObjectHeader {
            rc: 1,
            cs_sz: 32,
            other: 3,
            tag: 0,
        };
        assert!(
            decode(&bytes, &missing_safety).is_err(),
            "a DefinitionVal without safety metadata must fail closed"
        );
    }

    #[test]
    fn test_real_layout_all_nil_is_not_misclassified_as_legacy_safety() {
        // `all : List Name` is a boxed field, but `List.nil` itself is the
        // tagged scalar 1. Header-first discrimination must still read the
        // real safety byte at +40.
        let mut bytes = real_lean_defn_val(2);
        bytes[32..40].copy_from_slice(&1u64.to_le_bytes());
        assert_eq!(
            decode(&bytes, &real_lean_header()).expect("real all=nil layout"),
            Some(DefinitionSafety::Partial)
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
                decode(
                    &b,
                    &ObjectHeader {
                        rc: 1,
                        cs_sz: 0,
                        other: 4,
                        tag: 0,
                    },
                )
                .expect("legacy safety"),
                Some(expected),
                "legacy boxed scalar tag {tag} must decode in historical order"
            );
        }
    }

    #[test]
    fn test_legacy_unknown_or_non_scalar_safety_fails_closed() {
        let header = ObjectHeader {
            rc: 1,
            cs_sz: 0,
            other: 4,
            tag: 0,
        };
        let mut unknown = vec![0u8; 48];
        unknown[32..40].copy_from_slice(&((7u64 << 1) | 1).to_le_bytes());
        assert!(decode(&unknown, &header).is_err());

        let mut pointer = vec![0u8; 48];
        pointer[32..40].copy_from_slice(&0x1000u64.to_le_bytes());
        assert!(decode(&pointer, &header).is_err());
    }
}

#[cfg(test)]
mod declaration_safety_layout_tests {
    //! Exact authority-layout pins for AxiomVal, OpaqueVal, and RecursorVal.
    use super::super::{ConstantKind, DefinitionSafety};
    use crate::region::{CompactedRegion, ObjectHeader};

    fn header(other: u8, cs_sz: u16) -> ObjectHeader {
        ObjectHeader {
            rc: 1,
            cs_sz,
            other,
            tag: 0,
        }
    }

    fn tagged_bool(value: u64) -> u64 {
        (value << 1) | 1
    }

    #[test]
    fn axiom_real_and_legacy_bool_layouts_decode_exactly() {
        for (raw, expected) in [(0u8, DefinitionSafety::Safe), (1, DefinitionSafety::Unsafe)] {
            let mut real = vec![0u8; 24];
            real[16] = raw;
            assert_eq!(
                CompactedRegion::new(&real, 0)
                    .read_definition_safety(&ConstantKind::Axiom, 0, &header(1, 24))
                    .expect("real AxiomVal safety"),
                Some(expected)
            );

            let mut legacy = vec![0u8; 24];
            legacy[16..24].copy_from_slice(&tagged_bool(u64::from(raw)).to_le_bytes());
            assert_eq!(
                CompactedRegion::new(&legacy, 0)
                    .read_definition_safety(&ConstantKind::Axiom, 0, &header(2, 0))
                    .expect("legacy AxiomVal safety"),
                Some(expected)
            );
        }
    }

    #[test]
    fn opaque_real_and_legacy_bool_layouts_decode_exactly() {
        for (raw, expected) in [(0u8, DefinitionSafety::Safe), (1, DefinitionSafety::Unsafe)] {
            let mut real = vec![0u8; 40];
            real[32] = raw;
            assert_eq!(
                CompactedRegion::new(&real, 0)
                    .read_definition_safety(&ConstantKind::Opaque, 0, &header(3, 40))
                    .expect("real OpaqueVal safety"),
                Some(expected)
            );

            let mut legacy = vec![0u8; 40];
            legacy[24..32].copy_from_slice(&tagged_bool(u64::from(raw)).to_le_bytes());
            assert_eq!(
                CompactedRegion::new(&legacy, 0)
                    .read_definition_safety(&ConstantKind::Opaque, 0, &header(4, 0))
                    .expect("legacy OpaqueVal safety"),
                Some(expected)
            );
        }
    }

    #[test]
    fn axiom_and_opaque_malformed_authority_fail_closed() {
        let mut invalid_real = vec![0u8; 40];
        invalid_real[16] = 2;
        invalid_real[32] = 2;
        let region = CompactedRegion::new(&invalid_real, 0);
        assert!(region
            .read_definition_safety(&ConstantKind::Axiom, 0, &header(1, 24))
            .is_err());
        assert!(region
            .read_definition_safety(&ConstantKind::Opaque, 0, &header(3, 40))
            .is_err());

        let mut invalid_legacy = vec![0u8; 40];
        invalid_legacy[16..24].copy_from_slice(&tagged_bool(2).to_le_bytes());
        invalid_legacy[24..32].copy_from_slice(&tagged_bool(2).to_le_bytes());
        let region = CompactedRegion::new(&invalid_legacy, 0);
        assert!(region
            .read_definition_safety(&ConstantKind::Axiom, 0, &header(2, 0))
            .is_err());
        assert!(region
            .read_definition_safety(&ConstantKind::Opaque, 0, &header(4, 0))
            .is_err());

        assert!(region
            .read_definition_safety(&ConstantKind::Axiom, 0, &header(1, 16))
            .is_err());
        assert!(region
            .read_definition_safety(&ConstantKind::Opaque, 0, &header(4, 40))
            .is_err());
    }

    fn write_object_header(bytes: &mut [u8], other: u8, cs_sz: u16) {
        bytes[4..6].copy_from_slice(&cs_sz.to_le_bytes());
        bytes[6] = other;
    }

    #[test]
    fn recursor_real_and_legacy_flags_decode_at_their_exact_offsets() {
        let mut real = vec![0u8; 72];
        write_object_header(&mut real, 7, 72);
        real[64] = 1;
        real[65] = 1;
        assert_eq!(
            CompactedRegion::new(&real, 0)
                .read_recursor_bool_flags(0)
                .expect("real RecursorVal flags"),
            (true, true)
        );

        let mut legacy = vec![0u8; 80];
        write_object_header(&mut legacy, 9, 0);
        legacy[64..72].copy_from_slice(&tagged_bool(1).to_le_bytes());
        legacy[72..80].copy_from_slice(&tagged_bool(1).to_le_bytes());
        assert_eq!(
            CompactedRegion::new(&legacy, 0)
                .read_recursor_bool_flags(0)
                .expect("legacy RecursorVal flags"),
            (true, true)
        );
    }

    #[test]
    fn recursor_wrong_offset_splice_and_invalid_bool_fail_closed() {
        let mut real = vec![0u8; 80];
        write_object_header(&mut real, 7, 72);
        // The historical bug read +72. A true byte spliced there must not
        // influence the real `isUnsafe` byte at +65.
        real[72] = 1;
        assert_eq!(
            CompactedRegion::new(&real, 0)
                .read_recursor_bool_flags(0)
                .expect("real RecursorVal flags"),
            (false, false)
        );
        real[65] = 2;
        assert!(CompactedRegion::new(&real, 0)
            .read_recursor_bool_flags(0)
            .is_err());

        write_object_header(&mut real, 8, 72);
        assert!(CompactedRegion::new(&real, 0)
            .read_recursor_bool_flags(0)
            .is_err());
    }
}
