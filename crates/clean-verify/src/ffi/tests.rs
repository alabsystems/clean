// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for FFI boundary verification.

use super::*;

fn checker() -> FfiBoundaryChecker {
    FfiBoundaryChecker::new()
}

fn verifier() -> FfiVerifier {
    FfiVerifier::new()
}

#[test]
fn safe_repr_c_pointer_contracts_pass() {
    let source = r#"
        #[repr(C)]
        struct Buffer {
            data: *mut u8,
            len: usize,
        }

        extern "C" {
            fn fill_buffer(buf: *mut Buffer) -> *mut Buffer;
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    let function = spec
        .function_mut("fill_buffer")
        .expect("extern function should exist");
    function.require_pointer_validity_for("buf");
    function.require_pointer_valid_return();
    function.require_no_unwind();

    let checks = checker().required_checks(&spec);
    assert!(checks.contains(&FfiSafetyCheck::NoUnwinding {
        function: "fill_buffer".to_string(),
    }));
    assert!(checks.contains(&FfiSafetyCheck::PointerValidity {
        function: "fill_buffer".to_string(),
        target: FfiValueTarget::Param("buf".to_string()),
        non_null: true,
        aligned: true,
        initialized: true,
    }));
    assert!(checks.contains(&FfiSafetyCheck::PointerValidity {
        function: "fill_buffer".to_string(),
        target: FfiValueTarget::ReturnValue,
        non_null: true,
        aligned: true,
        initialized: true,
    }));
    assert!(checks.contains(&FfiSafetyCheck::TypeLayoutCompatibility {
        function: "fill_buffer".to_string(),
        ty: "Buffer".to_string(),
        requires_repr_c: true,
    }));
    assert!(checker().validate(&spec).is_ok());
}

#[test]
fn missing_repr_c_on_struct_is_reported() {
    let source = r#"
        struct Buffer {
            data: *mut u8,
            len: usize,
        }

        extern "C" {
            fn fill_buffer(buf: *mut Buffer);
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    let function = spec
        .function_mut("fill_buffer")
        .expect("extern function should exist");
    function.require_pointer_validity_for("buf");
    function.require_no_unwind();

    let violations = checker()
        .validate(&spec)
        .expect_err("missing repr(C) should be rejected");
    assert!(violations.contains(&FfiBoundaryViolation::MissingReprC {
        function: "fill_buffer".to_string(),
        position: "parameter `buf`".to_string(),
        ty: "Buffer".to_string(),
    }));
}

#[test]
fn reference_types_and_unwind_abi_are_rejected() {
    let source = r#"
        extern "C-unwind" {
            fn borrow(value: &u32) -> &u32;
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    spec.function_mut("borrow")
        .expect("extern function should exist")
        .require_no_unwind();

    let violations = checker()
        .validate(&spec)
        .expect_err("references and unwind-capable ABIs should be rejected");
    assert!(violations.contains(&FfiBoundaryViolation::UnwindAbi {
        function: "borrow".to_string(),
        abi: "C-unwind".to_string(),
    }));
    assert!(
        violations.contains(&FfiBoundaryViolation::ReferenceAcrossFfi {
            function: "borrow".to_string(),
            position: "parameter `value`".to_string(),
            ty: "&u32".to_string(),
        })
    );
    assert!(
        violations.contains(&FfiBoundaryViolation::ReferenceAcrossFfi {
            function: "borrow".to_string(),
            position: "return type".to_string(),
            ty: "&u32".to_string(),
        })
    );
}

#[test]
fn rust_owned_types_and_missing_pointer_contracts_are_reported() {
    let source = r#"
        extern "C" {
            fn take_string(s: String);
            fn read_byte(ptr: *const u8) -> u8;
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    spec.function_mut("take_string")
        .expect("extern function should exist")
        .require_no_unwind();
    spec.function_mut("read_byte")
        .expect("extern function should exist")
        .require_no_unwind();

    let violations = checker()
        .validate(&spec)
        .expect_err("Rust-owned types and missing pointer contracts should be rejected");
    assert!(violations.contains(&FfiBoundaryViolation::NonFfiSafeType {
        function: "take_string".to_string(),
        position: "parameter `s`".to_string(),
        ty: "String".to_string(),
        reason: "owned Rust container types do not have a stable C layout".to_string(),
    }));
    assert!(
        violations.contains(&FfiBoundaryViolation::MissingPointerPrecondition {
            function: "read_byte".to_string(),
            param: "ptr".to_string(),
        })
    );
}

#[test]
fn verifier_null_pointer_rule_requires_non_null_contracts() {
    let source = r#"
        extern "C" {
            fn take_ptr(ptr: *mut u8) -> *mut u8;
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    let function = spec
        .function_mut("take_ptr")
        .expect("extern function should exist");
    function
        .preconditions
        .push(FfiPrecondition::PointerValidity {
            param: "ptr".to_string(),
            non_null: false,
            aligned: true,
            initialized: true,
        });
    function.require_pointer_valid_return();
    function.require_no_unwind();

    let violations = verifier().apply_rules(&spec);
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::NullPointerCheck,
        severity: FfiViolationSeverity::Error,
        description: "raw pointer parameter `ptr` must have an explicit non-null contract"
            .to_string(),
        location: "extern fn `take_ptr` parameter `ptr`".to_string(),
    }));
}

#[test]
fn verifier_size_alignment_rule_checks_layout_and_alignment() {
    let source = r#"
        struct Buffer {
            len: usize,
        }

        extern "C" {
            fn fill(buf: *mut Buffer);
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    let function = spec
        .function_mut("fill")
        .expect("extern function should exist");
    function
        .preconditions
        .push(FfiPrecondition::PointerValidity {
            param: "buf".to_string(),
            non_null: true,
            aligned: false,
            initialized: true,
        });
    function.require_no_unwind();

    let violations = verifier().apply_rules(&spec);
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::SizeAlignment,
        severity: FfiViolationSeverity::Error,
        description:
            "raw pointer parameter `buf` must guarantee aligned memory at the FFI boundary"
                .to_string(),
        location: "extern fn `fill` parameter `buf`".to_string(),
    }));
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::SizeAlignment,
        severity: FfiViolationSeverity::Error,
        description:
            "type `Buffer` is missing #[repr(C)], so its size/alignment is not stable for FFI"
                .to_string(),
        location: "extern fn `fill` parameter `buf`".to_string(),
    }));
}

#[test]
fn verifier_lifetime_escape_rule_rejects_references() {
    let source = r#"
        extern "C" {
            fn borrow(value: &u32) -> &u32;
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    spec.function_mut("borrow")
        .expect("extern function should exist")
        .require_no_unwind();

    let violations = verifier().apply_rules(&spec);
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::LifetimeEscape,
        severity: FfiViolationSeverity::Error,
        description: "Rust reference `&u32` may let a borrow escape across the extern boundary"
            .to_string(),
        location: "extern fn `borrow` parameter `value`".to_string(),
    }));
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::LifetimeEscape,
        severity: FfiViolationSeverity::Error,
        description: "Rust reference `&u32` may let a borrow escape across the extern boundary"
            .to_string(),
        location: "extern fn `borrow` return value".to_string(),
    }));
}

#[test]
fn verifier_unwind_safety_rule_requires_non_unwinding_boundaries() {
    let source = r#"
        extern "C-unwind" {
            fn may_unwind();
        }
    "#;

    let spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    let violations = verifier().apply_rules(&spec);

    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::UnwindSafety,
        severity: FfiViolationSeverity::Error,
        description: "ABI `C-unwind` may unwind across the FFI boundary".to_string(),
        location: "extern fn `may_unwind`".to_string(),
    }));
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::UnwindSafety,
        severity: FfiViolationSeverity::Error,
        description: "extern function is missing an explicit no-unwind postcondition".to_string(),
        location: "extern fn `may_unwind`".to_string(),
    }));
}

#[test]
fn verifier_thread_safety_rule_flags_callback_threads() {
    let source = r#"
        extern "C" {
            fn set_callback(cb: extern "C" fn(i32));
        }
    "#;

    let mut spec = FfiBoundarySpec::from_source(source).expect("source should parse");
    spec.function_mut("set_callback")
        .expect("extern function should exist")
        .require_no_unwind();

    let violations = verifier().apply_rules(&spec);
    assert!(violations.contains(&FfiViolation {
        rule: FfiRule::ThreadSafety,
        severity: FfiViolationSeverity::Warning,
        description:
            "callback type `extern \"C\" fn(i32)` may be invoked from foreign threads without an explicit thread-affinity contract"
                .to_string(),
        location: "extern fn `set_callback` parameter `cb`".to_string(),
    }));
}
