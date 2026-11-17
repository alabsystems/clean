// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The constant-record readers of [`super`]: a part's `constants` array, read
//! into [`LoadConstant`]s that keep raw expression pointers, and the runtime
//! rows the code generator reads.

use super::*;

/// Read an array of constants, preserving raw expression pointers.
pub(super) fn read_load_constant_array(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<(Vec<LoadConstant>, bool)> {
    if !is_ptr(ptr) {
        return Ok((Vec::new(), false));
    }

    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;

    if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
        return Ok((Vec::new(), false));
    }

    let size = region.read_usize_at(offset + 8, "Constant array")?;
    region.validate_array_bounds(offset, size)?;
    let mut constants = Vec::with_capacity(size);

    for i in 0..size {
        let elem_offset = region.array_elem_offset(offset, i, "Constant array")?;
        let const_ptr = region.read_u64_at(elem_offset)?;
        let constant = read_load_constant_info(region, const_ptr)?;
        constants.push(constant);
    }

    Ok((constants, true))
}

/// Read a single ConstantInfo, storing raw expression pointers.
fn read_load_constant_info(region: &CompactedRegion<'_>, ptr: u64) -> OleanResult<LoadConstant> {
    if !is_ptr(ptr) {
        return Err(OleanError::Region("Invalid constant pointer".into()));
    }

    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;

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

    // XxxVal is the first field
    let val_ptr = region.read_u64_at(offset + 8)?;
    if !is_ptr(val_ptr) {
        return Err(OleanError::Region("Invalid XxxVal pointer".into()));
    }

    let val_offset = region.ptr_to_offset(val_ptr)?;
    let val_header = region.read_header_at(val_offset)?;

    // Read base ConstantVal fields: name, level_params, type_ptr (raw)
    let (kernel_name, kernel_level_params, type_ptr) =
        read_constant_val_fields_raw(region, val_offset)?;
    let name = kernel_name.to_string();

    // Read value pointer for definitions, theorems, opaques
    let value_ptr = read_constant_value_ptr(region, &kind, val_offset, &val_header)?;

    // Read reducibility hints
    let hints = region.read_reducibility_hints(&kind, val_offset, &val_header)?;

    // Read declaration safety for definitions, axioms, and opaques.
    let definition_safety = region.read_definition_safety(&kind, val_offset, &val_header)?;

    // Parse extra fields based on kind
    let (inductive_val, constructor_val, recursor_val) = match kind {
        ConstantKind::Inductive => (
            Some(region.read_inductive_val_data(val_offset)?),
            None,
            None,
        ),
        ConstantKind::Constructor => (
            None,
            Some(region.read_constructor_val_data(val_offset)?),
            None,
        ),
        ConstantKind::Recursor => (
            None,
            None,
            Some(read_load_recursor_val_data(region, val_offset)?),
        ),
        _ => (None, None, None),
    };

    let (kernel_all, kernel_ctors, kernel_inductive) = match kind {
        ConstantKind::Inductive => (
            region.read_kernel_name_list(region.read_u64_at(val_offset + 32)?)?,
            region.read_kernel_name_list(region.read_u64_at(val_offset + 40)?)?,
            None,
        ),
        ConstantKind::Constructor => (
            Vec::new(),
            Vec::new(),
            Some(region.read_kernel_name_ptr(region.read_u64_at(val_offset + 16)?)?),
        ),
        _ => (Vec::new(), Vec::new(), None),
    };
    let num_nested = if kind == ConstantKind::Inductive {
        match (val_header.other, val_header.cs_sz) {
            // Preserve exactly the same Nat read already performed by the
            // legacy metadata reader above. The runtime lane independently
            // requires the stricter typed Nat representation below.
            (6, 64) | (7, 0) => Some(
                region
                    .read_bignat_value(region.read_u64_at(val_offset + 48)?)?
                    .to_u64()
                    .ok_or_else(|| OleanError::Region("nested-family count exceeds u64".into()))?,
            ),
            // Older measured ABI stores only the Bool, not a multiplicity.
            (5, 56) => None,
            _ => {
                return Err(OleanError::Region(
                    "unsupported nested-family count layout".into(),
                ))
            }
        }
    } else {
        None
    };
    Ok(LoadConstant {
        name,
        kernel_name,
        kernel_level_params,
        kernel_all,
        kernel_ctors,
        kernel_inductive,
        runtime_mutual: None,
        kind,
        type_ptr,
        value_ptr,
        inductive_val,
        num_nested,
        constructor_val,
        recursor_val,
        hints,
        definition_safety,
    })
}

/// Runtime extraction keeps every array slot, including malformed metadata.
/// This stricter population check is deliberately not a logical-loader change.
pub(super) fn read_runtime_constant_rows(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<Vec<Result<LoadConstant, String>>> {
    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;
    let legacy = region.typed_module_layout()? == TypedModuleLayout::CleanLegacy;
    if !is_ptr(ptr)
        || !ptr.is_multiple_of(8)
        || header.tag != tags::ARRAY
        || header.rc != 0
        || header.other != 0
        || header.cs_sz != if legacy { 0 } else { 1 }
    {
        return Err(OleanError::Region(
            "runtime constants are not an array".into(),
        ));
    }
    let size = region.read_usize_at(offset + 8, "runtime constant array")?;
    let capacity = region.read_usize_at(offset + 16, "runtime constant capacity")?;
    if capacity < size {
        return Err(OleanError::Region(
            "runtime constant capacity is below source count".into(),
        ));
    }
    if size > 1_000_000 {
        return Err(OleanError::Region(
            "runtime declaration limit exceeded".into(),
        ));
    }
    region.validate_array_bounds(offset, size)?;
    let mut rows = Vec::with_capacity(size);
    for index in 0..size {
        let result = (|| {
            let slot = region.array_elem_offset(offset, index, "runtime constant array")?;
            let ptr = region.read_u64_at(slot)?;
            if !is_ptr(ptr) || ptr % 8 != 0 {
                return Err(OleanError::Region(
                    "unaligned runtime ConstantInfo pointer".into(),
                ));
            }
            let info = region.ptr_to_offset(ptr)?;
            let h = region.read_header_at(info)?;
            if h.rc != 0 || h.other != 1 || h.cs_sz != if legacy { 0 } else { 16 } {
                return Err(OleanError::Region(
                    "invalid runtime ConstantInfo header".into(),
                ));
            }
            let mut row = read_load_constant_info(region, ptr)?;
            let val = region.ptr_to_offset(region.read_u64_at(info + 8)?)?;
            let header = region.read_header_at(val)?;
            if (header.tag, header.rc) != (0, 0) || val % 8 != 0 {
                return Err(OleanError::Region(
                    "invalid runtime declaration-value header".into(),
                ));
            }
            let cv = region.ptr_to_offset(region.read_u64_at(val + 8)?)?;
            let cv_header = region.read_header_at(cv)?;
            if (cv_header.tag, cv_header.other, cv_header.rc) != (0, 3, 0)
                || cv_header.cs_sz != if legacy { 0 } else { 32 }
                || cv % 8 != 0
            {
                return Err(OleanError::Region(
                    "invalid runtime ConstantVal header".into(),
                ));
            }
            let all_at = match (&row.kind, header.other, header.cs_sz) {
                (ConstantKind::Definition, 4, 48) => Some(val + 32),
                (ConstantKind::Theorem, 3, 0 | 32) => Some(val + 24),
                (ConstantKind::Opaque, 3, 40) => Some(val + 24),
                (ConstantKind::Definition, 4, 0) => None,
                (ConstantKind::Opaque, 4, 0) => Some(val + 32),
                (ConstantKind::Theorem, _, _) => {
                    return Err(OleanError::Region(
                        "unsupported runtime theorem metadata layout".into(),
                    ))
                }
                _ => None,
            };
            if row.kind == ConstantKind::Inductive && row.num_nested.is_some() {
                row.num_nested = Some(region.read_kernel_nat_u64(region.read_u64_at(val + 48)?)?);
            }
            // The legacy Nat reader accepts null as zero and MPZ magnitude.
            // Runtime rows require the typed encoding, without changing the
            // original logical parser's policy or the source denominator.
            let count_offsets: &[usize] = match row.kind {
                ConstantKind::Inductive => &[16, 24],
                ConstantKind::Constructor => &[24, 32, 40],
                ConstantKind::Recursor => &[24, 32, 40, 48],
                _ => &[],
            };
            for offset in count_offsets {
                region.read_kernel_nat_u64(region.read_u64_at(val + offset)?)?;
            }
            row.runtime_mutual = all_at
                .map(|offset| region.read_kernel_name_list(region.read_u64_at(offset)?))
                .transpose()?;
            if row.kind == ConstantKind::Recursor {
                validate_runtime_recursor_rules(region, ptr)?;
            }
            Ok(row)
        })();
        rows.push(result.map_err(|error: OleanError| error.to_string()));
    }
    Ok(rows)
}

fn validate_runtime_recursor_rules(region: &CompactedRegion<'_>, ptr: u64) -> OleanResult<()> {
    let legacy = region.typed_module_layout()? == TypedModuleLayout::CleanLegacy;
    let info = region.ptr_to_offset(ptr)?;
    let val = region.ptr_to_offset(region.read_u64_at(info + 8)?)?;
    let mut current = region.read_u64_at(val + 56)?;
    let mut seen = std::collections::BTreeSet::new();
    while current != 1 {
        if !is_ptr(current) || !seen.insert(current) || seen.len() > 10_000 {
            return Err(OleanError::Region(
                "invalid runtime recursor rule list".into(),
            ));
        }
        let offset = region.ptr_to_offset(current)?;
        let header = region.read_header_at(offset)?;
        if (header.tag, header.other, header.rc) != (1, 2, 0)
            || header.cs_sz != if legacy { 0 } else { 24 }
        {
            return Err(OleanError::Region(
                "invalid runtime recursor rule cons".into(),
            ));
        }
        let head = region.read_u64_at(offset + 8)?;
        if !is_ptr(head) {
            return Err(OleanError::Region("missing runtime recursor rule".into()));
        }
        let rule = region.read_header_at(region.ptr_to_offset(head)?)?;
        if (rule.tag, rule.other, rule.rc) != (0, 3, 0) || rule.cs_sz != if legacy { 0 } else { 32 }
        {
            return Err(OleanError::Region(
                "invalid runtime recursor rule fields".into(),
            ));
        }
        region.read_kernel_nat_u64(region.read_u64_at(region.ptr_to_offset(head)? + 16)?)?;
        current = region.read_u64_at(offset + 16)?;
    }
    Ok(())
}

/// Read ConstantVal fields: name, level_params, and raw type pointer.
fn read_constant_val_fields_raw(
    region: &CompactedRegion<'_>,
    val_offset: usize,
) -> OleanResult<(Name, Vec<Name>, u64)> {
    let const_val_ptr = region.read_u64_at(val_offset + 8)?;

    let (name_ptr, level_params_ptr, type_ptr) = if is_ptr(const_val_ptr) {
        let cv_offset = region.ptr_to_offset(const_val_ptr)?;
        (
            region.read_u64_at(cv_offset + 8)?,
            region.read_u64_at(cv_offset + 16)?,
            region.read_u64_at(cv_offset + 24)?,
        )
    } else {
        (
            const_val_ptr,
            region.read_u64_at(val_offset + 16)?,
            region.read_u64_at(val_offset + 24)?,
        )
    };

    let name = region.read_kernel_name_ptr(name_ptr)?;
    let level_params = region.read_kernel_name_list(level_params_ptr)?;

    // Keep the raw type pointer instead of calling read_expr_at
    Ok((name, level_params, type_ptr))
}

/// Read the raw value pointer for definitions, theorems, and opaques.
fn read_constant_value_ptr(
    region: &CompactedRegion<'_>,
    kind: &ConstantKind,
    val_offset: usize,
    val_header: &crate::region::ObjectHeader,
) -> OleanResult<u64> {
    let needs_value = matches!(
        kind,
        ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
    );
    if needs_value && val_header.other >= 2 {
        let value_ptr = region.read_u64_at(val_offset + 16)?;
        if is_ptr(value_ptr) {
            return Ok(value_ptr);
        }
    }
    Ok(0)
}

/// Read RecursorVal extra data, preserving raw RHS pointers.
fn read_load_recursor_val_data(
    region: &CompactedRegion<'_>,
    val_offset: usize,
) -> OleanResult<LoadRecursorValData> {
    let all_ptr = region.read_u64_at(val_offset + 16)?;
    let all = region.read_kernel_name_list(all_ptr)?;

    let num_params = region.read_u32_at_pub(val_offset + 24, "numParams")?;
    let num_indices = region.read_u32_at_pub(val_offset + 32, "numIndices")?;
    let num_motives = region.read_u32_at_pub(val_offset + 40, "numMotives")?;
    let num_minors = region.read_u32_at_pub(val_offset + 48, "numMinors")?;

    let rules_ptr = region.read_u64_at(val_offset + 56)?;
    let rules = read_load_recursor_rules(region, rules_ptr)?;

    let (k, is_unsafe) = region.read_recursor_bool_flags(val_offset)?;

    Ok(LoadRecursorValData {
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

/// Read recursor rules, preserving raw RHS pointers.
fn read_load_recursor_rules(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<Vec<LoadRecursorRule>> {
    const MAX_ITERATIONS: usize = 10_000;

    let mut rules = Vec::new();
    let mut current_ptr = ptr;

    for _i in 0..MAX_ITERATIONS {
        if is_scalar(current_ptr) || !is_ptr(current_ptr) {
            return Ok(rules);
        }

        let offset = region.ptr_to_offset(current_ptr)?;
        let header = region.read_header_at(offset)?;

        match (header.tag, header.other) {
            (1, 2) => {
                let head_ptr = region.read_u64_at(offset + 8)?;
                let tail_ptr = region.read_u64_at(offset + 16)?;

                if is_ptr(head_ptr) {
                    let rule = read_load_recursor_rule(region, head_ptr)?;
                    rules.push(rule);
                }
                current_ptr = tail_ptr;
            }
            _ => return Ok(rules),
        }
    }

    if is_scalar(current_ptr) || !is_ptr(current_ptr) {
        return Ok(rules);
    }

    Err(OleanError::IterationLimitExceeded {
        limit: MAX_ITERATIONS,
        context: "recursor rules",
    })
}

/// Read a single recursor rule, preserving the raw RHS pointer.
fn read_load_recursor_rule(
    region: &CompactedRegion<'_>,
    ptr: u64,
) -> OleanResult<LoadRecursorRule> {
    let offset = region.ptr_to_offset(ptr)?;

    let ctor_ptr = region.read_u64_at(offset + 8)?;
    let ctor = region.read_kernel_name_ptr(ctor_ptr)?;

    let num_fields = region.read_u32_at_pub(offset + 16, "nfields")?;

    let rhs_ptr = region.read_u64_at(offset + 24)?;
    let rhs_ptr = if is_ptr(rhs_ptr) { rhs_ptr } else { 0 };

    Ok(LoadRecursorRule {
        ctor,
        num_fields,
        rhs_ptr,
    })
}
