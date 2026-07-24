// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::SourceProgram;

#[test]
fn test_source_program_parses_trait_associated_constant() {
    let source = r#"
        trait Bounded {
            const MAX: u32;
            fn value(self) -> u32;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program =
        SourceProgram::parse(source).expect("should parse trait with associated constant");
    let trait_def = program.items().iter().find_map(|item| {
        if let clean_rust_sem::expr::Item::TraitDef(def) = item {
            if def.name == "Bounded" {
                return Some(def);
            }
        }
        None
    });
    let trait_def = trait_def.expect("Bounded trait def should exist");
    assert_eq!(trait_def.associated_constants.len(), 1);
    assert_eq!(trait_def.associated_constants[0].name, "MAX");
    assert!(!trait_def.associated_constants[0].has_default);
}

#[test]
fn test_source_program_parses_trait_associated_constant_with_default() {
    let source = r#"
        trait Config {
            const TIMEOUT: u32 = 30u32;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).expect("should parse trait with default constant");
    let trait_def = program.items().iter().find_map(|item| {
        if let clean_rust_sem::expr::Item::TraitDef(def) = item {
            if def.name == "Config" {
                return Some(def);
            }
        }
        None
    });
    let trait_def = trait_def.expect("Config trait def should exist");
    assert_eq!(trait_def.associated_constants.len(), 1);
    assert_eq!(trait_def.associated_constants[0].name, "TIMEOUT");
    assert!(trait_def.associated_constants[0].has_default);
}

#[test]
fn test_source_program_parses_trait_with_multiple_associated_constants() {
    let source = r#"
        trait Numeric {
            const MIN: i32;
            const MAX: i32;
            const ZERO: i32 = 0i32;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).expect("should parse trait with multiple constants");
    let trait_def = program.items().iter().find_map(|item| {
        if let clean_rust_sem::expr::Item::TraitDef(def) = item {
            if def.name == "Numeric" {
                return Some(def);
            }
        }
        None
    });
    let trait_def = trait_def.expect("Numeric trait def should exist");
    assert_eq!(trait_def.associated_constants.len(), 3);
    assert_eq!(trait_def.associated_constants[0].name, "MIN");
    assert!(!trait_def.associated_constants[0].has_default);
    assert_eq!(trait_def.associated_constants[1].name, "MAX");
    assert!(!trait_def.associated_constants[1].has_default);
    assert_eq!(trait_def.associated_constants[2].name, "ZERO");
    assert!(trait_def.associated_constants[2].has_default);
}
