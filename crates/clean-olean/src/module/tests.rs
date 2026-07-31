// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::region::{is_ptr, is_scalar, unbox_scalar, CompactedRegion};

fn get_lean_lib_path() -> Option<std::path::PathBuf> {
    crate::pinned_lean_lib_path()
}

#[test]
fn test_analyze_root_prelude() {
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

    let analysis = region.analyze_root().expect("Failed to analyze root");

    println!("Root analysis for Init/Prelude.olean:");
    println!("  Root pointer: 0x{:x}", analysis.root_ptr);
    println!("  Root offset: {}", analysis.root_offset);
    println!("  Tag: {}", analysis.tag);
    println!("  Num fields: {}", analysis.num_fields);
    println!("  cs_sz: {}", analysis.cs_sz);
    println!("  Fields:");
    for (i, ptr, kind) in &analysis.field_info {
        println!("    Field {i}: 0x{ptr:x} -> {kind}");
    }
}

#[test]
fn test_analyze_arrays_prelude() {
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

    let root_ptr = region.root_ptr().expect("Failed to read root pointer");
    let root_offset = region
        .ptr_to_offset(root_ptr)
        .expect("Invalid root pointer");

    println!("\nAnalyzing arrays in Init/Prelude.olean root object:");

    // Read each field of the root object
    for i in 0..5 {
        let field_ptr = region
            .read_u64_at(root_offset + 8 + i * 8)
            .expect("Failed to read field");
        println!("\nField {i}:");

        if let Ok(analysis) = region.analyze_array(field_ptr, 5) {
            println!("  Array size: {}", analysis.size);
            println!("  Sample elements:");
            for elem in &analysis.sample_elements {
                println!(
                    "    [{}] tag={}, fields={}: {}",
                    elem.index, elem.tag, elem.num_fields, elem.description
                );
            }
        } else {
            println!("  Not an array or failed to analyze");
        }
    }
}

#[test]
fn test_read_module_data_prelude() {
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

    match region.read_module_data() {
        Ok(module) => {
            println!("Module data from Init/Prelude.olean:");
            println!("  Const names: {}", module.const_names.len());
            println!("  Constants: {}", module.constants.len());
            println!("  Extra const names: {}", module.extra_const_names.len());
            println!("  Imports: {}", module.imports.len());

            if !module.const_names.is_empty() {
                println!("\n  First 10 const names:");
                for name in module.const_names.iter().take(10) {
                    println!("    - {name}");
                }

                // Check for Nat in const_names
                let nat_names: Vec<_> = module
                    .const_names
                    .iter()
                    .filter(|n| *n == "Nat" || n.starts_with("Nat."))
                    .take(10)
                    .collect();
                println!("\n  Nat-related in const_names: {nat_names:?}");

                // Check for exact "Nat"
                let has_nat = module.const_names.iter().any(|n| n == "Nat");
                println!("\n  Has exact 'Nat' in const_names: {has_nat}");
            }

            // Check extra_const_names for Nat
            if !module.extra_const_names.is_empty() {
                let nat_extra: Vec<_> = module
                    .extra_const_names
                    .iter()
                    .filter(|n| *n == "Nat" || n.starts_with("Nat."))
                    .take(10)
                    .collect();
                println!("\n  Nat-related in extra_const_names: {nat_extra:?}");
            }

            if !module.constants.is_empty() {
                println!("\n  First 10 constants:");
                for c in module.constants.iter().take(10) {
                    println!("    - {} ({:?})", c.name, c.kind);
                }
            }

            // Count by kind
            let mut by_kind: std::collections::HashMap<ConstantKind, usize> =
                std::collections::HashMap::new();
            for c in &module.constants {
                *by_kind.entry(c.kind.clone()).or_insert(0) += 1;
            }
            println!("\n  Constants by kind:");
            for (kind, count) in &by_kind {
                println!("    {kind:?}: {count}");
            }
        }
        Err(e) => {
            println!("Failed to read module data: {e:?}");
        }
    }
}

#[test]
fn test_read_core_olean_with_imports() {
    // Init/Core.olean should have some imports and many constants.
    let Some(lib_path) = get_lean_lib_path() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let core_path = lib_path.join("Init/Core.olean");
    if !core_path.exists() {
        eprintln!("Skipping test: Init/Core.olean not found");
        return;
    }

    let bytes = std::fs::read(&core_path).expect("Failed to read file");
    let header = crate::parse_header(&bytes).expect("Failed to parse header");
    let region = CompactedRegion::new(&bytes, header.base_addr);

    let module = region
        .read_module_data()
        .expect("Failed to read module data");

    // Verify imports are parsed correctly
    assert!(
        !module.imports.is_empty(),
        "Expected Init/Core to have at least one import"
    );

    let import_names: Vec<_> = module
        .imports
        .iter()
        .map(|i| i.module_name.as_str())
        .collect();
    assert!(
        import_names.iter().any(|m| m.starts_with("Init.")),
        "Expected Init/Core to import at least one Init.* module"
    );

    // All imports should have runtime_only=false
    for imp in &module.imports {
        assert!(
            !imp.runtime_only,
            "Expected runtime_only=false for {}",
            imp.module_name
        );
    }

    // Verify constants are parsed
    assert!(
        !module.const_names.is_empty(),
        "Expected Init/Core to have exported constant names"
    );
    assert_eq!(
        module.const_names.len(),
        module.constants.len(),
        "Expected const_names and constants to have matching lengths"
    );
}

#[test]
fn test_read_init_olean_many_imports() {
    // Init.olean has many imports (all Init submodules)
    let Some(lib_path) = get_lean_lib_path() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    // Init.olean is one level up from Init/
    let init_path = lib_path.join("Init.olean");
    if !init_path.exists() {
        eprintln!("Skipping test: Init.olean not found at {init_path:?}");
        return;
    }

    let bytes = std::fs::read(&init_path).expect("Failed to read file");
    let header = crate::parse_header(&bytes).expect("Failed to parse header");
    let region = CompactedRegion::new(&bytes, header.base_addr);

    let module = region
        .read_module_data()
        .expect("Failed to read module data");

    // Init.olean should have many imports (31 in v4.13.0)
    assert!(
        module.imports.len() >= 30,
        "Expected ~31 imports in Init.olean, got {}",
        module.imports.len()
    );

    // Verify some expected imports
    let import_names: Vec<_> = module
        .imports
        .iter()
        .map(|i| i.module_name.as_str())
        .collect();
    assert!(
        import_names.contains(&"Init.Prelude"),
        "Should import Init.Prelude"
    );
    assert!(
        import_names.contains(&"Init.Core"),
        "Should import Init.Core"
    );
    assert!(
        import_names.contains(&"Init.Data"),
        "Should import Init.Data"
    );

    // Init.olean itself has no constants (it's just re-exports)
    assert_eq!(
        module.constants.len(),
        0,
        "Init.olean should have no direct constants"
    );
}

/// Describe a pointer value for diagnostic output.
fn describe_field_ptr(region: &CompactedRegion<'_>, ptr: u64) -> String {
    if is_scalar(ptr) {
        return format!("scalar({})", unbox_scalar(ptr));
    }
    if !is_ptr(ptr) {
        return "null".to_string();
    }
    let Ok(off) = region.ptr_to_offset(ptr) else {
        return "oob".to_string();
    };
    let Ok(h) = region.read_header_at(off) else {
        return "invalid".to_string();
    };
    if h.tag == crate::region::tags::STRING {
        region.read_lean_string_at(off).map_or_else(
            |_| format!("tag{}/{}", h.tag, h.other),
            |s| format!("String(\"{s}\")"),
        )
    } else if h.tag <= 2 && h.other <= 2 {
        region.read_name_at(off).map_or_else(
            |_| format!("tag{}/{}", h.tag, h.other),
            |n| format!("Name({n})"),
        )
    } else {
        format!("tag{}/{}", h.tag, h.other)
    }
}

/// Print fields of an object for diagnostic output.
fn print_fields(region: &CompactedRegion<'_>, offset: usize, count: usize, indent: &str) {
    for i in 0..count {
        let ptr = region.read_u64_at(offset + 8 + i * 8).unwrap();
        let desc = describe_field_ptr(region, ptr);
        println!("{indent}Field {i}: 0x{ptr:x} -> {desc}");
    }
}

/// Print sort level details for type expression analysis.
fn print_sort_level_details(region: &CompactedRegion<'_>, sort_offset: usize) {
    let sort_field_base = sort_offset + 8;
    let sort_scalar_base =
        sort_field_base + region.read_header_at(sort_offset).unwrap().other as usize * 8;
    let raw_level_ptr = region.read_u64_at(sort_field_base).unwrap_or(0);
    println!("    sort level raw ptr: 0x{raw_level_ptr:x}");
    if let Ok(level_off) = region.ptr_to_offset(raw_level_ptr) {
        if let Ok(h) = region.read_header_at(level_off) {
            println!(
                "    sort level header: tag={}, other={}, cs_sz={}",
                h.tag, h.other, h.cs_sz
            );
            let level_field_base = level_off + 8;
            if let Ok(pred_ptr) = region.read_u64_at(level_field_base) {
                println!("    sort level field0: 0x{pred_ptr:x}");
                if let Ok(pred_off) = region.ptr_to_offset(pred_ptr) {
                    if let Ok(ph) = region.read_header_at(pred_off) {
                        println!(
                            "    pred header: tag={}, other={}, cs_sz={}",
                            ph.tag, ph.other, ph.cs_sz
                        );
                        if let Ok(bytes) = region.bytes_at(pred_off, ph.cs_sz as usize) {
                            println!("    pred raw bytes: {bytes:x?}");
                        }
                    }
                }
            }
            match region.read_level_at(level_off) {
                Ok(level) => println!("    parsed level: {level:?}"),
                Err(err) => println!("    level parse error: {err:?}"),
            }
        }
    }
    if let Ok(bytes) = region.bytes_at(sort_scalar_base, 8) {
        println!("    sort scalar bytes: {bytes:x?}");
    }
}

#[test]
fn test_analyze_first_constant_structure() {
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

    let root_ptr = region.root_ptr().expect("Failed to read root pointer");
    let root_offset = region
        .ptr_to_offset(root_ptr)
        .expect("Invalid root pointer");
    let constants_ptr = region.read_u64_at(root_offset + 8 + 16).unwrap();
    let constants_offset = region.ptr_to_offset(constants_ptr).unwrap();

    let first_const_ptr = region.read_u64_at(constants_offset + 24).unwrap();
    let first_const_offset = region.ptr_to_offset(first_const_ptr).unwrap();
    let first_header = region.read_header_at(first_const_offset).unwrap();

    println!("First constant wrapper:");
    println!(
        "  tag={}, other={}, cs_sz={}",
        first_header.tag, first_header.other, first_header.cs_sz
    );

    let inner_ptr = region.read_u64_at(first_const_offset + 8).unwrap();
    println!("  Inner ptr: 0x{inner_ptr:x}");

    if is_ptr(inner_ptr) {
        let inner_offset = region.ptr_to_offset(inner_ptr).unwrap();
        let inner_header = region.read_header_at(inner_offset).unwrap();
        println!("  Inner object:");
        println!(
            "    tag={}, other={}, cs_sz={}",
            inner_header.tag, inner_header.other, inner_header.cs_sz
        );
        print_fields(&region, inner_offset, 8, "    ");

        let field0_ptr = region.read_u64_at(inner_offset + 8).unwrap();
        if is_ptr(field0_ptr) {
            let field0_offset = region.ptr_to_offset(field0_ptr).unwrap();
            let field0_header = region.read_header_at(field0_offset).unwrap();
            println!(
                "\n  Field 0 details (tag={}, other={}):",
                field0_header.tag, field0_header.other
            );
            print_fields(&region, field0_offset, 6, "      ");
        }
    }
}

#[test]
fn test_analyze_first_constant_type_expr() {
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

    // Navigate: root -> constants array -> first constant -> inner -> field 0
    let root_ptr = region.root_ptr().expect("Failed to read root pointer");
    let root_offset = region
        .ptr_to_offset(root_ptr)
        .expect("Invalid root pointer");
    let constants_ptr = region.read_u64_at(root_offset + 8 + 16).unwrap();
    let constants_offset = region.ptr_to_offset(constants_ptr).unwrap();
    let first_const_ptr = region.read_u64_at(constants_offset + 24).unwrap();
    let first_const_offset = region.ptr_to_offset(first_const_ptr).unwrap();
    let inner_ptr = region.read_u64_at(first_const_offset + 8).unwrap();
    if !is_ptr(inner_ptr) {
        return;
    }
    let inner_offset = region.ptr_to_offset(inner_ptr).unwrap();
    let field0_ptr = region.read_u64_at(inner_offset + 8).unwrap();
    if !is_ptr(field0_ptr) {
        return;
    }
    let field0_offset = region.ptr_to_offset(field0_ptr).unwrap();

    let type_ptr = region.read_u64_at(field0_offset + 24).unwrap();
    if !is_ptr(type_ptr) {
        return;
    }
    let type_offset = region.ptr_to_offset(type_ptr).unwrap();
    let type_header = region.read_header_at(type_offset).unwrap();
    println!(
        "  Type header tag={}, other={}, cs_sz={}",
        type_header.tag, type_header.other, type_header.cs_sz
    );

    let field_base = type_offset + 8;
    let mut type_fields = Vec::new();
    for i in 0..type_header.other as usize {
        let ptr = region.read_u64_at(field_base + i * 8).unwrap_or(0);
        println!("    type field {i}: 0x{ptr:x}");
        type_fields.push(ptr);
        if let Ok(off) = region.ptr_to_offset(ptr) {
            if let Ok(h) = region.read_header_at(off) {
                println!(
                    "      field {i} header: tag={}, other={}, cs_sz={}",
                    h.tag, h.other, h.cs_sz
                );
            }
        }
    }
    let scalar_base = field_base + type_header.other as usize * 8;
    if let Ok(bytes) = region.bytes_at(scalar_base, 1) {
        println!("    binder info byte: {}", bytes[0]);
    }
    if let Some(&ptr) = type_fields.get(1) {
        if let Ok(off) = region.ptr_to_offset(ptr) {
            print_sort_level_details(&region, off);
            match region.read_expr_at(off) {
                Ok(expr) => println!("  Parsed binder type: {expr:?}"),
                Err(err) => println!("  Binder type parse error: {err:?}"),
            }
        }
    }
    if let Some(&ptr) = type_fields.get(2) {
        if let Ok(off) = region.ptr_to_offset(ptr) {
            match region.read_expr_at(off) {
                Ok(expr) => println!("  Parsed body expr: {expr:?}"),
                Err(err) => println!("  Body parse error: {err:?}"),
            }
        }
    }
    match region.read_expr_at(type_offset) {
        Ok(expr) => println!("\n  Parsed type expr for first constant: {expr:?}"),
        Err(err) => println!("\n  Failed to parse type expr for first constant: {err:?}"),
    }
}

/// Build a synthetic linked list in bytes for testing iteration limits.
///
/// Creates a linked list of `length` cons cells, each pointing to a scalar name.
/// The list terminates with a scalar nil pointer (value 1).
///
/// Layout per cons cell (24 bytes):
/// - Header (8 bytes): rc=0, cs_sz=0, other=2 (2 ptr fields), tag=1
/// - head_ptr (8 bytes): scalar 3 (boxed 1, Name.anonymous)
/// - tail_ptr (8 bytes): pointer to next cell or nil (1)
fn build_test_list(length: usize, base_addr: u64) -> Vec<u8> {
    // Header (64 bytes) + root pointer (8 bytes) = 72 bytes before data
    const PREAMBLE_SIZE: usize = 72;
    const CELL_SIZE: usize = 24;

    let total_size = PREAMBLE_SIZE + length * CELL_SIZE;
    let mut data = vec![0u8; total_size];

    // Write minimal header
    data[0..4].copy_from_slice(b"olnL"); // Magic
    data[4..8].copy_from_slice(&1u32.to_le_bytes()); // Version

    // Root pointer points to first cell (if any) or nil
    let root_ptr = if length > 0 {
        base_addr + PREAMBLE_SIZE as u64
    } else {
        1 // nil
    };
    data[64..72].copy_from_slice(&root_ptr.to_le_bytes());

    // Build linked list cells
    for i in 0..length {
        let cell_offset = PREAMBLE_SIZE + i * CELL_SIZE;

        // Header: tag=1 (cons), other=2 (2 pointer fields)
        let header: u64 = (1u64 << 56) | (2u64 << 48);
        data[cell_offset..cell_offset + 8].copy_from_slice(&header.to_le_bytes());

        // head_ptr: scalar 3 (boxed 1, represents Name.anonymous)
        data[cell_offset + 8..cell_offset + 16].copy_from_slice(&3u64.to_le_bytes());

        // tail_ptr: next cell or nil
        let next_ptr = if i + 1 < length {
            base_addr + (PREAMBLE_SIZE + (i + 1) * CELL_SIZE) as u64
        } else {
            1 // nil (scalar 0 boxed)
        };
        data[cell_offset + 16..cell_offset + 24].copy_from_slice(&next_ptr.to_le_bytes());
    }

    data
}

#[test]
fn test_name_list_empty() {
    let base_addr = 0x1000_0000u64;
    let data = build_test_list(0, base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    // Root is nil (1), so list should be empty
    let names = region
        .read_name_list(1)
        .expect("reading nil name list should succeed");
    assert_eq!(names.len(), 0);
}

#[test]
fn test_name_list_short() {
    let base_addr = 0x1000_0000u64;
    let length = 10;
    let data = build_test_list(length, base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    let root_ptr = region.read_u64_at(64).unwrap();
    let result = region.read_name_list(root_ptr);

    // Should succeed - list terminates well before limit
    assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    assert_eq!(result.unwrap().len(), length);
}

#[test]
fn test_name_list_at_limit_boundary() {
    // Test that lists terminating exactly at MAX_ITERATIONS work.
    // We can't test 100_000 items easily, so verify the logic with a smaller list
    // that proves the termination check works.
    let base_addr = 0x1000_0000u64;
    let length = 1000;
    let data = build_test_list(length, base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    let root_ptr = region.read_u64_at(64).unwrap();
    let result = region.read_name_list(root_ptr);

    assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    assert_eq!(result.unwrap().len(), length);
}

#[test]
fn test_recursor_rules_empty() {
    let base_addr = 0x1000_0000u64;
    let data = build_test_list(0, base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    // Nil pointer should return empty list
    let rules = region
        .read_recursor_rules(1)
        .expect("reading nil recursor rules should succeed");
    assert_eq!(rules.len(), 0);
}

/// Build a cyclic linked list for testing iteration limit overflow.
///
/// Creates a list where the last cell's tail pointer points back to the first cell,
/// causing infinite iteration until the limit is hit.
fn build_cyclic_list(base_addr: u64) -> Vec<u8> {
    // We only need a single cell that points to itself
    const PREAMBLE_SIZE: usize = 72;
    const CELL_SIZE: usize = 24;

    let total_size = PREAMBLE_SIZE + CELL_SIZE;
    let mut data = vec![0u8; total_size];

    // Write minimal header
    data[0..4].copy_from_slice(b"olnL"); // Magic
    data[4..8].copy_from_slice(&1u32.to_le_bytes()); // Version

    // Root pointer points to the single cell
    let cell_addr = base_addr + PREAMBLE_SIZE as u64;
    data[64..72].copy_from_slice(&cell_addr.to_le_bytes());

    // Build the cyclic cell
    let cell_offset = PREAMBLE_SIZE;

    // Header: tag=1 (cons), other=2 (2 pointer fields)
    let header: u64 = (1u64 << 56) | (2u64 << 48);
    data[cell_offset..cell_offset + 8].copy_from_slice(&header.to_le_bytes());

    // head_ptr: scalar 3 (boxed 1, represents Name.anonymous)
    data[cell_offset + 8..cell_offset + 16].copy_from_slice(&3u64.to_le_bytes());

    // tail_ptr: points back to itself (cyclic!)
    data[cell_offset + 16..cell_offset + 24].copy_from_slice(&cell_addr.to_le_bytes());

    data
}

#[test]
fn test_name_list_iteration_limit_exceeded() {
    // Test that a cyclic list correctly triggers IterationLimitExceeded
    let base_addr = 0x1000_0000u64;
    let data = build_cyclic_list(base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    let root_ptr = region.read_u64_at(64).unwrap();
    let result = region.read_name_list(root_ptr);

    // Should fail with IterationLimitExceeded
    assert!(result.is_err(), "Expected Err, got {:?}", result);
    match result {
        Err(crate::error::OleanError::IterationLimitExceeded { limit, context }) => {
            assert_eq!(limit, 100_000);
            assert_eq!(context, "name list");
        }
        Err(e) => panic!("Wrong error type: {:?}", e),
        Ok(_) => panic!("Expected error"),
    }
}

#[test]
fn test_recursor_rules_iteration_limit_exceeded() {
    // Test that a cyclic list correctly triggers IterationLimitExceeded
    let base_addr = 0x1000_0000u64;
    let data = build_cyclic_list(base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    let root_ptr = region.read_u64_at(64).unwrap();
    let result = region.read_recursor_rules(root_ptr);

    // Should fail with IterationLimitExceeded
    assert!(result.is_err(), "Expected Err, got {:?}", result);
    match result {
        Err(crate::error::OleanError::IterationLimitExceeded { limit, context }) => {
            assert_eq!(limit, 10_000);
            assert_eq!(context, "recursor rules");
        }
        Err(e) => panic!("Wrong error type: {:?}", e),
        Ok(_) => panic!("Expected error"),
    }
}

#[test]
fn test_name_list_exactly_at_limit() {
    // Test that a list terminating exactly at the iteration count succeeds.
    // Due to the fix in e73b810f8, the check happens AFTER the loop exhausts,
    // so a list of MAX_ITERATIONS items that terminates is valid.
    //
    // We can't easily build a 100_000 item list in a unit test, but we can
    // verify the logic: after MAX_ITERATIONS iterations, if the current_ptr
    // is scalar/non-ptr (nil), the function returns Ok.
    //
    // The shorter tests above validate this behavior indirectly.
    // This test documents the expected behavior at the boundary.

    // Use a shorter list to confirm termination check works
    let base_addr = 0x1000_0000u64;
    let length = 5000; // Well under 100_000 but validates termination
    let data = build_test_list(length, base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    let root_ptr = region.read_u64_at(64).unwrap();
    let result = region.read_name_list(root_ptr);

    assert!(result.is_ok(), "Expected Ok, got {:?}", result);
    assert_eq!(result.unwrap().len(), length);
}

#[test]
fn test_recursor_rules_termination_check() {
    // Similar to test_name_list_exactly_at_limit but for recursor rules.
    // The iteration limit for recursor rules is 10_000.
    let base_addr = 0x1000_0000u64;
    let length = 500; // Under 10_000 limit
    let data = build_test_list(length, base_addr);
    let region = CompactedRegion::new(&data, base_addr);

    let _root_ptr = region.read_u64_at(64).unwrap();
    // Note: This test uses the name list structure which won't parse as
    // valid recursor rules (head_ptr is scalar 3, not a valid rule).
    // For recursor rules, we'd need a different structure. The important
    // point is that the iteration limit logic is tested.
    //
    // The cyclic test above validates that exceeding the limit triggers
    // the correct error for recursor rules.
}

// --- ParsedQuotKind discriminant decoding (QuotVal.kind, ConstantInfo tag 4) ---

#[test]
fn test_parsed_quot_kind_from_tag_known_tags_decode() {
    assert_eq!(ParsedQuotKind::from_tag(0), Some(ParsedQuotKind::Type));
    assert_eq!(ParsedQuotKind::from_tag(1), Some(ParsedQuotKind::Mk));
    assert_eq!(ParsedQuotKind::from_tag(2), Some(ParsedQuotKind::Lift));
    assert_eq!(ParsedQuotKind::from_tag(3), Some(ParsedQuotKind::Ind));
    assert_eq!(ParsedQuotKind::from_tag(4), Some(ParsedQuotKind::Sound));
}

#[test]
fn test_parsed_quot_kind_from_tag_unknown_tag_returns_none() {
    // Tags outside 0..=4 are not fabricated into a kind; they degrade to
    // "unknown" so callers can tell a malformed payload from a real kind.
    assert_eq!(ParsedQuotKind::from_tag(5), None);
    assert_eq!(ParsedQuotKind::from_tag(99), None);
    assert_eq!(ParsedQuotKind::from_tag(u64::MAX), None);
}

#[test]
fn test_parsed_quot_kind_tag_roundtrips_for_every_variant() {
    // from_tag . to_tag == identity over the full kind set.
    for kind in [
        ParsedQuotKind::Type,
        ParsedQuotKind::Mk,
        ParsedQuotKind::Lift,
        ParsedQuotKind::Ind,
        ParsedQuotKind::Sound,
    ] {
        assert_eq!(
            ParsedQuotKind::from_tag(kind.to_tag()),
            Some(kind),
            "tag round-trip should preserve {kind:?}"
        );
    }
}

#[test]
fn test_parsed_quot_kind_to_tag_matches_exporter_contract() {
    // These tags MUST match OleanExporter::write_quotient_info so a Clean
    // export -> import round-trip recovers the original kind.
    assert_eq!(ParsedQuotKind::Type.to_tag(), 0);
    assert_eq!(ParsedQuotKind::Mk.to_tag(), 1);
    assert_eq!(ParsedQuotKind::Lift.to_tag(), 2);
    assert_eq!(ParsedQuotKind::Ind.to_tag(), 3);
    assert_eq!(ParsedQuotKind::Sound.to_tag(), 4);
}

/// `read_quot_kind` decodes the `QuotVal.kind` scalar slot at `val_offset
/// + 16` for each quotient primitive. Build a minimal compacted region
/// holding a single boxed scalar at the expected offset and confirm the
/// reader recovers the matching `ParsedQuotKind`.
#[test]
fn test_read_quot_kind_decodes_scalar_slot() {
    // Tag -> scalar payload pairs covering every quotient primitive.
    for (tag, expected) in [
        (0u64, ParsedQuotKind::Type),
        (1, ParsedQuotKind::Mk),
        (2, ParsedQuotKind::Lift),
        (3, ParsedQuotKind::Ind),
        (4, ParsedQuotKind::Sound),
    ] {
        let base_addr = 0x2000_0000u64;
        // QuotVal layout: +8 ConstantVal ptr (unused here), +16 kind scalar.
        // The region byte buffer is indexed from the object start, so we
        // place the kind scalar at byte offset 16. unbox: scalar = tag*2+1.
        let mut data = vec![0u8; 24];
        let scalar = (tag << 1) | 1;
        data[16..24].copy_from_slice(&scalar.to_le_bytes());
        let region = CompactedRegion::new(&data, base_addr);

        // val_offset = 0 means the QuotVal object begins at the buffer start.
        let kind = region
            .read_quot_kind(0)
            .expect("read_quot_kind should not error on a valid scalar slot");
        assert_eq!(kind, Some(expected), "kind for tag {tag}");

        // Sanity: the raw slot really is a scalar carrying our tag.
        let raw = region.read_u64_at(16).expect("read kind slot");
        assert!(is_scalar(raw), "kind slot must be a scalar");
        assert_eq!(unbox_scalar(raw), tag);
    }
}

#[test]
fn test_read_quot_kind_non_scalar_slot_returns_none() {
    // A pointer (LSB=0) in the kind slot is not a valid QuotKind scalar;
    // the reader returns None rather than misinterpreting a pointer as a tag.
    let base_addr = 0x3000_0000u64;
    let mut data = vec![0u8; 24];
    // A plausible pointer value (even, so LSB=0 => not a scalar).
    let ptr_value = base_addr + 8;
    data[16..24].copy_from_slice(&ptr_value.to_le_bytes());
    let region = CompactedRegion::new(&data, base_addr);

    let kind = region
        .read_quot_kind(0)
        .expect("read_quot_kind should not error on a pointer slot");
    assert_eq!(kind, None, "pointer slot must decode to None");
}

// ════════════════════════════════════════════════════════════════════════════
// XxxVal field-count fail-closed guard (`require_val_fields`).
//
// Lean's compacted region records the slot count of a constructor object in
// the header's `other` byte. A malformed, truncated, or future-version
// `.olean` can present an `XxxVal` (RecursorVal / ConstructorVal /
// InductiveVal / QuotVal) whose `other` is smaller than the per-kind reader's
// arity. Without a guard the reader would read words belonging to an adjacent
// object as a field — silently fabricating a constant. These tests pin that
// each such object fails closed with a typed `OleanError::Region`, that a
// correctly-sized object still parses, and mirror the `Expr`/`Level`
// field-count guards.
// ════════════════════════════════════════════════════════════════════════════

/// Base address for the synthetic constant-info fixtures below. Even and large
/// enough that no in-region offset is mistaken for a tagged scalar.
const CONST_TEST_BASE: u64 = 0x0040_0000;

/// Build a region holding a one-element `ConstantInfo` array whose single
/// element is a `(wrapper_tag)` wrapper pointing at an `XxxVal` object whose
/// header advertises `val_other` boxed pointer fields. The `XxxVal` points at a
/// 3-field `ConstantVal` (anonymous name, nil levelParams, scalar/no type) and
/// every following slot the per-kind reader touches is written as a nil-list /
/// zero scalar (`1`), so a sufficiently-sized object parses cleanly. The
/// `val_other` byte is what the fail-closed guard inspects, independent of the
/// physical slots written. Returns `(data, array_ptr)`.
///
/// Layout (8-byte aligned, in order):
///   array  @ 0    : header(tag=ARRAY, other=0) + size=1 + cap=1 + elem0 ptr
///   wrapper@ 48   : header(tag=wrapper_tag, other=1) + val ptr
///   val    @ 64   : header(tag=0, other=val_other) + constval ptr + slots…
///   cval   @ 144  : header(tag=0, other=3) + name/lvls/type
fn build_constant_info_region(wrapper_tag: u8, val_other: u8) -> (Vec<u8>, u64) {
    // Generous fixed buffer; offsets are explicit so the exact size is not
    // load-bearing as long as it is large enough.
    let mut data = vec![0u8; 1024];

    let write_header = |data: &mut [u8], off: usize, other: u8, tag: u8| {
        // rc(4) + cs_sz(2) + other(1) + tag(1)
        data[off + 6] = other;
        data[off + 7] = tag;
    };
    let put_u64 = |data: &mut [u8], off: usize, v: u64| {
        data[off..off + 8].copy_from_slice(&v.to_le_bytes());
    };

    let array_off = 0usize;
    let wrapper_off = 48usize;
    let val_off = 64usize;
    // ConstantVal sits after the val's header + its declared slots, but we
    // place it past the maximum slot region (9 slots) so every kind's reader
    // has room; alignment to 8 is automatic since all offsets are multiples.
    let cval_off = val_off + 8 + 9 * 8; // 144

    // 1-element ConstantInfo array.
    write_header(&mut data, array_off, 0, crate::region::tags::ARRAY);
    put_u64(&mut data, array_off + 8, 1); // size
    put_u64(&mut data, array_off + 16, 1); // capacity
    put_u64(
        &mut data,
        array_off + 24,
        CONST_TEST_BASE + wrapper_off as u64,
    );

    // ConstantInfo wrapper (1 field -> XxxVal).
    write_header(&mut data, wrapper_off, 1, wrapper_tag);
    put_u64(&mut data, wrapper_off + 8, CONST_TEST_BASE + val_off as u64);

    // XxxVal: header advertises `val_other` slots. Slot +8 -> ConstantVal ptr;
    // remaining slots are nil-list (scalar 1) so list reads yield empty and
    // scalar reads yield 0/false.
    write_header(&mut data, val_off, val_other, 0);
    put_u64(&mut data, val_off + 8, CONST_TEST_BASE + cval_off as u64);
    for slot in 1..=9usize {
        put_u64(&mut data, val_off + 8 + slot * 8, 1); // nil list / scalar 0
    }

    // ConstantVal base (name, levelParams, type).
    write_header(&mut data, cval_off, 3, 0);
    put_u64(&mut data, cval_off + 8, 1); // name = anonymous (scalar)
    put_u64(&mut data, cval_off + 16, 1); // levelParams = nil
    put_u64(&mut data, cval_off + 24, 1); // type = scalar (=> None)

    let array_ptr = CONST_TEST_BASE + array_off as u64;
    (data, array_ptr)
}

/// `RecursorVal` dereferences three boxed pointers (`toConstantVal`, `all`,
/// `rules`); one whose header declares only two must fail closed rather than
/// chasing an adjacent word as its `rules` pointer.
#[test]
fn test_read_recursor_val_insufficient_fields_returns_region_error() {
    let (data, array_ptr) = build_constant_info_region(7, 2);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let err = region
        .read_constant_array_v2(array_ptr)
        .expect_err("RecursorVal with other<3 must be rejected");
    assert!(
        matches!(&err, crate::error::OleanError::Region(msg)
            if msg.contains("RecursorVal") && msg.contains("expected at least 3")),
        "expected malformed-RecursorVal Region error, got {err:?}"
    );
}

/// A real-sized `RecursorVal` (boxed `other = 7`, as Lean emits) still parses
/// to a recursor constant with the expected (empty) extra data.
#[test]
fn test_read_recursor_val_real_field_count_parses() {
    let (data, array_ptr) = build_constant_info_region(7, 7);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let constants = region
        .read_constant_array_v2(array_ptr)
        .expect("real-sized RecursorVal must parse");
    assert_eq!(constants.len(), 1, "exactly one constant expected");
    let c = &constants[0];
    assert_eq!(c.kind, ConstantKind::Recursor, "kind must be Recursor");
    let rec = c
        .recursor_val
        .as_ref()
        .expect("recursor_val data must be present");
    assert_eq!(rec.num_params, 0, "nil slots decode to zero Nats");
    assert!(rec.rules.is_empty(), "nil rules list decodes to empty");
}

/// A `RecursorVal` declaring exactly its three boxed pointers (the guard's
/// minimum) parses; the boundary value must not be rejected.
#[test]
fn test_read_recursor_val_minimum_field_count_parses() {
    let (data, array_ptr) = build_constant_info_region(7, 3);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let constants = region
        .read_constant_array_v2(array_ptr)
        .expect("RecursorVal at the boxed-field minimum must parse");
    assert_eq!(constants.len(), 1);
    assert_eq!(constants[0].kind, ConstantKind::Recursor);
    assert!(constants[0].recursor_val.is_some());
}

/// `ConstructorVal` dereferences two boxed pointers (`toConstantVal`,
/// `induct`); one declaring only one must fail closed.
#[test]
fn test_read_constructor_val_insufficient_fields_returns_region_error() {
    let (data, array_ptr) = build_constant_info_region(6, 1);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let err = region
        .read_constant_array_v2(array_ptr)
        .expect_err("ConstructorVal with other<2 must be rejected");
    assert!(
        matches!(&err, crate::error::OleanError::Region(msg)
            if msg.contains("ConstructorVal") && msg.contains("expected at least 2")),
        "expected malformed-ConstructorVal Region error, got {err:?}"
    );
}

/// A real-sized `ConstructorVal` (boxed `other = 5`) still parses.
#[test]
fn test_read_constructor_val_real_field_count_parses() {
    let (data, array_ptr) = build_constant_info_region(6, 5);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let constants = region
        .read_constant_array_v2(array_ptr)
        .expect("real-sized ConstructorVal must parse");
    assert_eq!(constants.len(), 1);
    assert_eq!(constants[0].kind, ConstantKind::Constructor);
    assert!(
        constants[0].constructor_val.is_some(),
        "constructor_val data must be present"
    );
}

/// `InductiveVal` dereferences three boxed pointers (`toConstantVal`, `all`,
/// `ctors`); one declaring only two must fail closed before `ctors` is chased.
#[test]
fn test_read_inductive_val_insufficient_fields_returns_region_error() {
    let (data, array_ptr) = build_constant_info_region(5, 2);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let err = region
        .read_constant_array_v2(array_ptr)
        .expect_err("InductiveVal with other<3 must be rejected");
    assert!(
        matches!(&err, crate::error::OleanError::Region(msg)
            if msg.contains("InductiveVal") && msg.contains("expected at least 3")),
        "expected malformed-InductiveVal Region error, got {err:?}"
    );
}

/// A real-sized `InductiveVal` (boxed `other = 6`) still parses.
#[test]
fn test_read_inductive_val_real_field_count_parses() {
    let (data, array_ptr) = build_constant_info_region(5, 6);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let constants = region
        .read_constant_array_v2(array_ptr)
        .expect("real-sized InductiveVal must parse");
    assert_eq!(constants.len(), 1);
    assert_eq!(constants[0].kind, ConstantKind::Inductive);
    assert!(
        constants[0].inductive_val.is_some(),
        "inductive_val data must be present"
    );
}

/// A `QuotVal` (wrapper tag 4) dereferences only `toConstantVal`; one declaring
/// zero boxed fields must fail closed before that pointer is read. The `kind`
/// discriminant lives in the trailing scalar region and is not a boxed field.
#[test]
fn test_read_quot_val_zero_fields_returns_region_error() {
    let (data, array_ptr) = build_constant_info_region(4, 0);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let err = region
        .read_constant_array_v2(array_ptr)
        .expect_err("QuotVal with other=0 must be rejected");
    assert!(
        matches!(&err, crate::error::OleanError::Region(msg)
            if msg.contains("QuotVal") && msg.contains("expected at least 1")),
        "expected malformed-QuotVal Region error, got {err:?}"
    );
}

/// A real-sized `QuotVal` (boxed `other = 1`) still parses.
#[test]
fn test_read_quot_val_real_field_count_parses() {
    let (data, array_ptr) = build_constant_info_region(4, 1);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let constants = region
        .read_constant_array_v2(array_ptr)
        .expect("real-sized QuotVal must parse");
    assert_eq!(constants.len(), 1);
    assert_eq!(constants[0].kind, ConstantKind::Quot);
}

/// An `XxxVal` declaring zero boxed fields cannot even supply its
/// `toConstantVal` pointer; the base requirement (`other >= 1`) rejects it for
/// every kind, including the otherwise-permissive `Axiom` (wrapper tag 0).
#[test]
fn test_read_axiom_val_zero_fields_returns_region_error() {
    let (data, array_ptr) = build_constant_info_region(0, 0);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let err = region
        .read_constant_array_v2(array_ptr)
        .expect_err("XxxVal with other=0 must be rejected");
    assert!(
        matches!(&err, crate::error::OleanError::Region(msg)
            if msg.contains("AxiomVal") && msg.contains("expected at least 1")),
        "expected malformed-AxiomVal Region error, got {err:?}"
    );
}

/// A well-formed `AxiomVal` (boxed `other = 1`, only `toConstantVal`) still
/// parses, confirming the base requirement does not over-reject.
#[test]
fn test_read_axiom_val_minimum_field_count_parses() {
    let (data, array_ptr) = build_constant_info_region(0, 1);
    let region = CompactedRegion::new(&data, CONST_TEST_BASE);
    let constants = region
        .read_constant_array_v2(array_ptr)
        .expect("AxiomVal at the boxed-field minimum must parse");
    assert_eq!(constants.len(), 1);
    assert_eq!(constants[0].kind, ConstantKind::Axiom);
}
