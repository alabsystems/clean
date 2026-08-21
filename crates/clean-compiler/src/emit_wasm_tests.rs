// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the WebAssembly backend.
//!
//! Two kinds of evidence, kept distinct on purpose:
//!
//! * STRUCTURAL — assertions on the emitted `.wat` and on the binary
//!   encoding's sections. These always run.
//! * EXECUTION — the emitted binary module is instantiated and CALLED, and its
//!   results are compared against a Rust reference over a battery that
//!   includes wraparound points. This needs a Wasm host; `node` is probed at
//!   run time. When no host is present the test still validates the binary
//!   structurally, so it never degrades into a no-op.

use std::process::Command;

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, JoinPointId};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn fnid(s: &str) -> FnId {
    FnId(Name::from_string(s))
}

/// `def affineU (a b : W) : W := W.add (W.mul a b) b` at IR width `ty`.
fn affine_decl(name: &str, ty: IRType, prefix: &str) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![(var(0), ty.clone()), (var(1), ty.clone())],
        return_type: ty.clone(),
        body: IRBody::VDecl {
            var: var(2),
            ty: ty.clone(),
            value: IRExpr::Apply {
                fn_id: fnid(&format!("{prefix}.mul")),
                args: vec![IRArg::Var(var(0)), IRArg::Var(var(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(3),
                ty: ty.clone(),
                value: IRExpr::Apply {
                    fn_id: fnid(&format!("{prefix}.add")),
                    args: vec![IRArg::Var(var(2)), IRArg::Var(var(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(3)))),
            }),
        },
    }
}

fn affine_u32() -> IRDecl {
    affine_decl("affineU", IRType::UInt32, "UInt32")
}

/// A one-binding decl: `let x : ty := <value>; return x`.
fn single_binding(name: &str, params: Vec<(VarId, IRType)>, ty: IRType, value: IRExpr) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: ty.clone(),
        body: IRBody::VDecl {
            var: var(9),
            ty,
            value,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(9)))),
        },
    }
}

/// The instruction lines of the emitted `.wat` (no header, no `(local …)`).
fn wat_instrs(wat: &str) -> Vec<String> {
    wat.lines()
        .map(str::trim)
        .filter(|l| {
            !l.is_empty()
                && !l.starts_with(";;")
                && !l.starts_with("(module")
                && !l.starts_with("(func")
                && !l.starts_with("(local")
                && *l != ")"
        })
        .map(ToOwned::to_owned)
        .collect()
}

// ---------------------------------------------------------------------------
// Structure: the accepted fragment
// ---------------------------------------------------------------------------

#[test]
fn test_wat_affine_uint32_exports_and_sequence() {
    let wat = emit_wat(&[affine_u32()]).expect("affineU is in the fragment");
    assert!(
        wat.contains(
            "(func $l_affineU (export \"affineU\") (param $v0 i32) (param $v1 i32) (result i32)"
        ),
        "signature line missing:\n{wat}"
    );
    assert_eq!(
        wat_instrs(&wat),
        vec![
            "local.get $v0",
            "local.get $v1",
            "i32.mul",
            "local.set $v2",
            "local.get $v2",
            "local.get $v1",
            "i32.add",
            "local.set $v3",
            "local.get $v3",
        ],
        "emitted body:\n{wat}"
    );
    // Call-free: the arithmetic is native instructions, not runtime calls.
    assert!(!wat.contains("call"), "unexpected call in:\n{wat}");
}

#[test]
fn test_wat_declares_one_local_per_binding() {
    let wat = emit_wat(&[affine_u32()]).expect("in fragment");
    assert!(wat.contains("(local $v2 i32)"), "{wat}");
    assert!(wat.contains("(local $v3 i32)"), "{wat}");
}

#[test]
fn test_wat_uint64_uses_i64_and_needs_no_mask() {
    let decl = affine_decl("affine64", IRType::UInt64, "UInt64");
    let wat = emit_wat(&[decl]).expect("UInt64 is in the fragment");
    assert!(wat.contains("(result i64)"), "{wat}");
    assert!(wat.contains("i64.mul"), "{wat}");
    assert!(wat.contains("i64.add"), "{wat}");
    // i64 wraps at exactly 64 bits, which IS Lean's UInt64 semantics.
    assert!(!wat.contains("and"), "unexpected mask in:\n{wat}");
}

#[test]
fn test_wat_uint8_masks_result_and_normalizes_params() {
    let decl = affine_decl("affine8", IRType::UInt8, "UInt8");
    let wat = emit_wat(&[decl]).expect("UInt8 is in the fragment");
    assert_eq!(
        wat_instrs(&wat),
        vec![
            // Entry normalization of the two narrow parameters.
            "local.get $v0",
            "i32.const 255",
            "i32.and",
            "local.set $v0",
            "local.get $v1",
            "i32.const 255",
            "i32.and",
            "local.set $v1",
            // `UInt8.mul`: i32.mul wraps at 32 bits, so the result is masked
            // back to 8.
            "local.get $v0",
            "local.get $v1",
            "i32.mul",
            "i32.const 255",
            "i32.and",
            "local.set $v2",
            "local.get $v2",
            "local.get $v1",
            "i32.add",
            "i32.const 255",
            "i32.and",
            "local.set $v3",
            "local.get $v3",
        ],
        "emitted body:\n{wat}"
    );
}

#[test]
fn test_wat_uint16_masks_with_0xffff() {
    let decl = affine_decl("affine16", IRType::UInt16, "UInt16");
    let wat = emit_wat(&[decl]).expect("UInt16 is in the fragment");
    assert!(wat.contains("i32.const 65535"), "{wat}");
    assert!(!wat.contains("i32.const 255\n"), "{wat}");
}

#[test]
fn test_wat_literal_binding() {
    let decl = single_binding(
        "k",
        vec![],
        IRType::UInt32,
        IRExpr::Lit(IRLiteral::UInt32(4_294_967_295)),
    );
    let wat = emit_wat(&[decl]).expect("literal is in the fragment");
    assert!(wat.contains("i32.const 4294967295"), "{wat}");
}

#[test]
fn test_wat_empty_slice_emits_empty_module() {
    let wat = emit_wat(&[]).expect("empty slice");
    assert!(wat.starts_with("(module"), "{wat}");
    assert!(!wat.contains("(func"), "{wat}");
}

// ---------------------------------------------------------------------------
// Refusals: everything outside the fragment, loudly
// ---------------------------------------------------------------------------

/// `def double (n : Nat) : Nat := Nat.add n n` — `Nat` lowers to a heap
/// object, so it is refused at the type, before the call is even reached.
#[test]
fn test_refuses_nat_because_it_has_no_machine_word() {
    let decl = IRDecl {
        name: Name::from_string("double"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fnid("Nat.add"),
                args: vec![IRArg::Var(var(0)), IRArg::Var(var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(1)))),
        },
    };
    let err = emit_wat(&[decl]).expect_err("Nat must be refused");
    assert!(
        matches!(
            err,
            WasmEmitError::UnsupportedType {
                ty: IRType::Object,
                ..
            }
        ),
        "got {err:?}"
    );
    assert!(err.to_string().contains("Nat"), "message: {err}");
}

#[test]
fn test_refuses_usize_as_not_target_stable() {
    let decl = single_binding(
        "u",
        vec![(var(0), IRType::USize)],
        IRType::USize,
        IRExpr::Lit(IRLiteral::USize(1)),
    );
    let err = emit_wat(&[decl]).expect_err("USize must be refused");
    assert!(
        matches!(
            err,
            WasmEmitError::UnsupportedType {
                ty: IRType::USize,
                ..
            }
        ),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_bool_and_float() {
    for ty in [IRType::Bool, IRType::Float64, IRType::Float32] {
        let decl = IRDecl {
            name: Name::from_string("f"),
            params: vec![(var(0), ty.clone())],
            return_type: ty.clone(),
            body: IRBody::Ret(IRArg::Var(var(0))),
        };
        let err = emit_wat(&[decl]).expect_err("must be refused");
        assert!(
            matches!(err, WasmEmitError::UnsupportedType { .. }),
            "{ty:?} gave {err:?}"
        );
    }
}

#[test]
fn test_refuses_call_to_a_user_function() {
    let decl = single_binding(
        "caller",
        vec![(var(0), IRType::UInt32)],
        IRType::UInt32,
        IRExpr::Apply {
            fn_id: fnid("affineU"),
            args: vec![IRArg::Var(var(0)), IRArg::Var(var(0))],
        },
    );
    let err = emit_wat(&[decl]).expect_err("calls are refused");
    match err {
        WasmEmitError::UnsupportedCall { ref callee } => assert_eq!(callee, "affineU"),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_refuses_division_which_has_trap_semantics() {
    let decl = single_binding(
        "d",
        vec![(var(0), IRType::UInt32)],
        IRType::UInt32,
        IRExpr::Apply {
            fn_id: fnid("UInt32.div"),
            args: vec![IRArg::Var(var(0)), IRArg::Var(var(0))],
        },
    );
    let err = emit_wat(&[decl]).expect_err("div is refused");
    assert!(
        matches!(err, WasmEmitError::UnsupportedCall { .. }),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_nat_add_even_at_a_machine_width() {
    // The callee table is keyed on the UIntW prefix, so `Nat.add` is refused
    // as a call even when someone hands it machine-word-typed operands.
    let decl = single_binding(
        "n",
        vec![(var(0), IRType::UInt32)],
        IRType::UInt32,
        IRExpr::Apply {
            fn_id: fnid("Nat.add"),
            args: vec![IRArg::Var(var(0)), IRArg::Var(var(0))],
        },
    );
    let err = emit_wat(&[decl]).expect_err("Nat.add is refused");
    assert!(
        matches!(err, WasmEmitError::UnsupportedCall { .. }),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_case() {
    let ctor = CtorInfo {
        name: Name::from_string("C"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let decl = IRDecl {
        name: Name::from_string("branchy"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor,
                body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            }],
            default: None,
        },
    };
    let err = emit_wat(&[decl]).expect_err("case is refused");
    match err {
        WasmEmitError::UnsupportedBody { form } => assert_eq!(form, "case"),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_refuses_join_points() {
    let decl = IRDecl {
        name: Name::from_string("jumpy"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![],
            body: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![],
            }),
        },
    };
    let err = emit_wat(&[decl]).expect_err("join points are refused");
    match err {
        WasmEmitError::UnsupportedBody { form } => assert_eq!(form, "join point"),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_refuses_unreachable() {
    let decl = IRDecl {
        name: Name::from_string("absurd"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Unreachable,
    };
    let err = emit_wat(&[decl]).expect_err("unreachable is refused");
    match err {
        WasmEmitError::UnsupportedBody { form } => assert_eq!(form, "unreachable"),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_refuses_rc_operations() {
    // An `inc` reaches this backend only in IR the SHARED checker already
    // rejects: rule T1 requires an object operand, and objects never get past
    // `val_type`. So the refusal here is the checker's, surfaced through
    // `WasmEmitError::Ir` — recorded rather than asserted as a fragment
    // refusal, because pretending otherwise would document an arm that no
    // checker-valid module can reach.
    let decl = IRDecl {
        name: Name::from_string("rc"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let err = emit_wat(&[decl]).expect_err("inc is refused");
    assert!(matches!(err, WasmEmitError::Ir(_)), "got {err:?}");
}

#[test]
fn test_refuses_constructor_expression() {
    let decl = single_binding(
        "c",
        vec![],
        IRType::UInt32,
        IRExpr::Ctor {
            info: CtorInfo {
                name: Name::from_string("C"),
                tag: 0,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            args: vec![],
        },
    );
    let err = emit_wat(&[decl]).expect_err("ctor is refused");
    match err {
        WasmEmitError::UnsupportedExpr { form } => assert_eq!(form, "ctor"),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_refuses_width_mismatched_literal() {
    let decl = single_binding(
        "m",
        vec![],
        IRType::UInt32,
        IRExpr::Lit(IRLiteral::UInt64(7)),
    );
    let err = emit_wat(&[decl]).expect_err("width mismatch is refused");
    assert!(
        matches!(err, WasmEmitError::ResultTypeMismatch { .. }),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_mixed_width_operands() {
    let decl = IRDecl {
        name: Name::from_string("mixed"),
        params: vec![(var(0), IRType::UInt32), (var(1), IRType::UInt8)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt32,
            value: IRExpr::Apply {
                fn_id: fnid("UInt32.add"),
                args: vec![IRArg::Var(var(0)), IRArg::Var(var(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(2)))),
        },
    };
    let err = emit_wat(&[decl]).expect_err("mixed widths are refused");
    assert!(
        matches!(err, WasmEmitError::OperandTypeMismatch { .. }),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_return_type_mismatch() {
    let decl = IRDecl {
        name: Name::from_string("r"),
        params: vec![(var(0), IRType::UInt8)],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let err = emit_wat(&[decl]).expect_err("return width mismatch is refused");
    assert!(
        matches!(
            err,
            WasmEmitError::ResultTypeMismatch {
                context: "return",
                ..
            }
        ),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_wrong_operand_count() {
    let decl = single_binding(
        "a1",
        vec![(var(0), IRType::UInt32)],
        IRType::UInt32,
        IRExpr::Apply {
            fn_id: fnid("UInt32.add"),
            args: vec![IRArg::Var(var(0))],
        },
    );
    let err = emit_wat(&[decl]).expect_err("unsaturated add is refused");
    assert!(
        matches!(
            err,
            WasmEmitError::ArityMismatch {
                expected: 2,
                actual: 1,
                ..
            }
        ),
        "got {err:?}"
    );
}

#[test]
fn test_refuses_duplicate_export() {
    let err = emit_wat(&[affine_u32(), affine_u32()]).expect_err("duplicate export is refused");
    match err {
        WasmEmitError::DuplicateExport { ref name } => assert_eq!(name, "affineU"),
        other => panic!("got {other:?}"),
    }
}

#[test]
fn test_refuses_erased_return() {
    let decl = IRDecl {
        name: Name::from_string("e"),
        params: vec![(var(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Erased),
    };
    let err = emit_wat(&[decl]).expect_err("erased return is refused");
    assert!(matches!(err, WasmEmitError::ErasedOperand), "got {err:?}");
}

#[test]
fn test_ir_checker_rejection_is_surfaced() {
    // Use of an unbound variable: caught by the shared L5IR checker, and
    // reported as such rather than as a Wasm-fragment refusal.
    let decl = IRDecl {
        name: Name::from_string("unbound"),
        params: vec![],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Var(var(7))),
    };
    let err = emit_wat(&[decl]).expect_err("unbound var is refused");
    assert!(matches!(err, WasmEmitError::Ir(_)), "got {err:?}");
}

// ---------------------------------------------------------------------------
// Binary encoding
// ---------------------------------------------------------------------------

/// Sections of `module`, in order: id and contents.
fn sections(module: &[u8]) -> Vec<(u8, Vec<u8>)> {
    let mut out = Vec::new();
    let mut i = 8; // past magic + version
    while i < module.len() {
        let id = module[i];
        i += 1;
        let mut size = 0usize;
        let mut shift = 0;
        loop {
            let b = module[i];
            i += 1;
            size |= usize::from(b & 0x7f) << shift;
            shift += 7;
            if b & 0x80 == 0 {
                break;
            }
        }
        out.push((id, module[i..i + size].to_vec()));
        i += size;
    }
    out
}

/// The contents of section `id`.
fn section(module: &[u8], id: u8) -> Vec<u8> {
    sections(module)
        .into_iter()
        .find(|(sid, _)| *sid == id)
        .map(|(_, body)| body)
        .unwrap_or_else(|| panic!("section {id} missing"))
}

#[test]
fn test_binary_header_and_sections() {
    let module = emit_wasm_binary(&[affine_u32()]).expect("in fragment");
    assert_eq!(&module[0..4], b"\0asm", "bad magic");
    assert_eq!(&module[4..8], &[0x01, 0x00, 0x00, 0x00], "bad version");
    let ids: Vec<u8> = sections(&module).iter().map(|(id, _)| *id).collect();
    assert_eq!(ids, vec![1, 3, 7, 10], "sections: {ids:?}");
}

#[test]
fn test_binary_type_and_export_sections_are_exact() {
    let module = emit_wasm_binary(&[affine_u32()]).expect("in fragment");
    assert_eq!(
        section(&module, 1),
        vec![
            0x01, // one functype
            0x60, // functype
            0x02, 0x7f, 0x7f, // (param i32 i32)
            0x01, 0x7f, // (result i32)
        ],
        "type section"
    );
    let mut expected_export = vec![0x01, 0x07];
    expected_export.extend_from_slice(b"affineU");
    expected_export.extend_from_slice(&[0x00, 0x00]); // kind func, index 0
    assert_eq!(section(&module, 7), expected_export, "export section");
}

#[test]
fn test_binary_code_section_is_exact() {
    // The whole body, byte for byte. This is the golden that pins the
    // opcode table, the LEB immediates, and the locals declaration together.
    let module = emit_wasm_binary(&[affine_u32()]).expect("in fragment");
    let body = vec![
        0x02, 0x01, 0x7f, 0x01, 0x7f, // two i32 locals, declared singly
        0x20, 0x00, // local.get $v0
        0x20, 0x01, // local.get $v1
        0x6c, // i32.mul
        0x21, 0x02, // local.set $v2
        0x20, 0x02, // local.get $v2
        0x20, 0x01, // local.get $v1
        0x6a, // i32.add
        0x21, 0x03, // local.set $v3
        0x20, 0x03, // local.get $v3
        0x0b, // end
    ];
    let mut expected = vec![0x01, body.len() as u8];
    expected.extend_from_slice(&body);
    assert_eq!(section(&module, 10), expected, "code section");
}

#[test]
fn test_text_and_binary_agree_on_instruction_count() {
    // Both renderings come from ONE lowering, so they must contain the same
    // number of instructions. This is what makes executing the binary
    // evidence about the text an author reads.
    for decl in [
        affine_u32(),
        affine_decl("affine8", IRType::UInt8, "UInt8"),
        affine_decl("affine64", IRType::UInt64, "UInt64"),
    ] {
        let wat = emit_wat(std::slice::from_ref(&decl)).expect("in fragment");
        let func = lower_decl(&decl).expect("in fragment");
        assert_eq!(
            wat_instrs(&wat).len(),
            func.instrs.len(),
            "instruction count drift for {}",
            decl.name
        );
    }
}

#[test]
fn test_leb_signed_encoding_of_full_width_constant() {
    // `i32.const 4294967295` is SIGNED LEB128 of -1, i.e. the single byte
    // 0x7f. An unsigned encoding here would produce a module a host rejects.
    let decl = single_binding(
        "k",
        vec![],
        IRType::UInt32,
        IRExpr::Lit(IRLiteral::UInt32(u32::MAX)),
    );
    let module = emit_wasm_binary(&[decl]).expect("in fragment");
    let pos = module
        .windows(2)
        .position(|w| w == [0x41, 0x7f])
        .expect("i32.const -1 not found");
    assert!(pos > 8, "constant should live in the code section");
}

// ---------------------------------------------------------------------------
// Execution
// ---------------------------------------------------------------------------

/// A Wasm host binary, if one is on this machine.
fn wasm_host() -> Option<String> {
    let candidate = "node";
    let ok = Command::new(candidate)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    ok.then(|| candidate.to_owned())
}

/// Instantiate `module`, call `export` on each input pair, return the results
/// as unsigned decimal strings. `None` if no host is available.
fn run_u32(module: &[u8], export: &str, inputs: &[(u32, u32)]) -> Option<Vec<String>> {
    let host = wasm_host()?;
    let dir = tempfile::tempdir().expect("tempdir");
    let wasm_path = dir.path().join("m.wasm");
    std::fs::write(&wasm_path, module).expect("write module");
    let cases: Vec<String> = inputs.iter().map(|(a, b)| format!("[{a},{b}]")).collect();
    let js = format!(
        r#"const fs = require('fs');
const bytes = fs.readFileSync({path:?});
const inst = new WebAssembly.Instance(new WebAssembly.Module(bytes), {{}});
const f = inst.exports[{export:?}];
for (const [a, b] of [{cases}]) {{
  console.log((f(a, b) >>> 0).toString());
}}
"#,
        path = wasm_path.to_string_lossy(),
        export = export,
        cases = cases.join(","),
    );
    let js_path = dir.path().join("run.js");
    std::fs::write(&js_path, js).expect("write driver");
    let out = Command::new(&host)
        .arg(&js_path)
        .output()
        .expect("spawn wasm host");
    eprintln!(
        "EXECUTED `{export}` on Wasm host `{host}` ({} bytes)",
        module.len()
    );
    assert!(
        out.status.success(),
        "host rejected the module:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    Some(
        String::from_utf8_lossy(&out.stdout)
            .lines()
            .map(ToOwned::to_owned)
            .collect(),
    )
}

/// The battery: zero, one, small values, and points that wrap at 8, 16 and 32
/// bits. Wraparound is where an emitter that forgot a mask diverges.
const BATTERY: [(u32, u32); 10] = [
    (0, 0),
    (1, 1),
    (2, 3),
    (7, 5),
    (200, 3),
    (255, 255),
    (256, 1),
    (65_535, 65_535),
    (65_536, 3),
    (4_294_967_295, 2),
];

#[test]
fn test_execute_affine_uint32_against_kernel_semantics() {
    let module = emit_wasm_binary(&[affine_u32()]).expect("in fragment");
    let Some(actual) = run_u32(&module, "affineU", &BATTERY) else {
        // No host: still prove the module is well-formed enough to carry the
        // battery, so this test is never a silent no-op.
        assert_eq!(&module[0..4], b"\0asm");
        assert_eq!(
            sections(&module).len(),
            4,
            "module structure must still hold without a host"
        );
        eprintln!("NOTE: no Wasm host found; execution leg SKIPPED, structure checked");
        return;
    };
    // Reference: UInt32 is wrapping 32-bit arithmetic.
    let expected: Vec<String> = BATTERY
        .iter()
        .map(|(a, b)| a.wrapping_mul(*b).wrapping_add(*b).to_string())
        .collect();
    assert_eq!(actual, expected);
}

#[test]
fn test_execute_affine_uint8_wraps_at_eight_bits() {
    // The mask is the whole point: `i32.mul` wraps at 32 bits, so without the
    // `i32.and 255` this returns 603 for (200, 3) instead of 91.
    let decl = affine_decl("affine8", IRType::UInt8, "UInt8");
    let module = emit_wasm_binary(&[decl]).expect("in fragment");
    let Some(actual) = run_u32(&module, "affine8", &BATTERY) else {
        assert!(
            module.iter().filter(|b| **b == 0x71).count() >= 4,
            "narrow module must carry i32.and masks"
        );
        eprintln!("NOTE: no Wasm host found; execution leg SKIPPED, structure checked");
        return;
    };
    // Reference: UInt8 arithmetic wraps at 8 bits, and out-of-range inputs are
    // normalized on entry (the host may hand us any i32).
    let expected: Vec<String> = BATTERY
        .iter()
        .map(|(a, b)| {
            let (a, b) = (*a as u8, *b as u8);
            a.wrapping_mul(b).wrapping_add(b).to_string()
        })
        .collect();
    assert_eq!(actual, expected);
}

// ---------------------------------------------------------------------------
// Target-triple plumbing
// ---------------------------------------------------------------------------

#[test]
fn test_wasm_triple_is_recognized_and_has_its_own_module_extension() {
    use crate::native_codegen_ext2::TargetTriple;
    let wasm = TargetTriple::parse("wasm32-unknown-unknown").expect("parse");
    assert!(wasm.is_wasm());
    assert_eq!(wasm.module_ext(), "wasm");

    let host = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    assert!(!host.is_wasm());
    assert_eq!(host.module_ext(), "dylib");
}

#[test]
fn test_host_jit_pipeline_refuses_a_wasm_target() {
    use crate::native_codegen_ext2::{plan_jit_compile, NativeCompileError, TargetTriple};
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("m.c");
    std::fs::write(&source, "int main(void){return 0;}").expect("write source");

    let wasm = TargetTriple::parse("wasm32-unknown-unknown").expect("parse");
    let err = plan_jit_compile(&source, dir.path(), "m", &wasm, false)
        .expect_err("no cc -shared produces a .wasm");
    assert!(
        matches!(err, NativeCompileError::UnsupportedTarget(ref t) if t == "wasm32-unknown-unknown"),
        "got {err:?}"
    );

    // The host pipeline still plans normally for a native triple.
    let host = TargetTriple::parse("aarch64-apple-darwin").expect("parse");
    plan_jit_compile(&source, dir.path(), "m", &host, false).expect("native target still plans");
}
