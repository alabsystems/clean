// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};
use clean_rust_sem::expr::{AsmOperand, EnumVariantPayload, Expr, InlineAsm, Item, MatchArm, Stmt};

#[test]
fn test_source_program_parses_inline_asm_macro() {
    let source = r#"
        fn main() -> u32 {
            let mut value = 1u32;
            unsafe {
                core::arch::asm!(
                    "mov {out:e}, {input:e}",
                    out = lateout(reg) value,
                    input = in(reg) 7u32,
                    const 3usize,
                    sym main,
                    options(nomem, nostack, preserves_flags),
                    clobber_abi("C"),
                );
            }
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("inline asm should parse");
    let asm = find_main_inline_asm(&program);

    assert_eq!(asm.template, "mov {out:e}, {input:e}");
    assert_eq!(asm.clobbers, vec!["C".to_string()]);
    assert!(asm.options.nomem);
    assert!(asm.options.nostack);
    assert!(asm.options.preserves_flags);
    assert_eq!(asm.operands.len(), 4);

    match &asm.operands[0] {
        AsmOperand::Out {
            constraint,
            expr: Some(Expr::Var { name, .. }),
        } => {
            assert_eq!(constraint, "reg");
            assert_eq!(name, "value");
        }
        other => panic!("expected output operand, got {other:?}"),
    }

    match &asm.operands[1] {
        AsmOperand::In {
            constraint,
            expr: Expr::Literal(Value::Uint { value, ty: _ }),
        } => {
            assert_eq!(constraint, "reg");
            assert_eq!(*value, 7);
        }
        other => panic!("expected input operand, got {other:?}"),
    }

    match &asm.operands[2] {
        AsmOperand::Const(Expr::Literal(Value::Uint { value, ty: _ })) => {
            assert_eq!(*value, 3);
        }
        other => panic!("expected const operand, got {other:?}"),
    }

    match &asm.operands[3] {
        AsmOperand::Sym(symbol) => assert_eq!(symbol, "main"),
        other => panic!("expected sym operand, got {other:?}"),
    }
}

#[test]
fn test_inline_asm_nomem_preserves_other_bindings() {
    let source = r#"
        fn main() -> (u32, u32) {
            let mut out = 1u32;
            let keep = 2u32;
            unsafe {
                core::arch::asm!("nop", lateout(reg) out, options(nomem));
            }
            (keep, out)
        }
    "#;

    let program = SourceProgram::parse(source).expect("inline asm should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![Value::u32(2), Value::Uninit]))
    );
}

#[test]
fn test_inline_asm_without_nomem_havocs_modeled_memory() {
    let source = r#"
        fn main() -> (u32, u32) {
            let mut out = 1u32;
            let keep = 2u32;
            unsafe {
                core::arch::asm!("nop", lateout(reg) out);
            }
            (keep, out)
        }
    "#;

    let program = SourceProgram::parse(source).expect("inline asm should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![Value::Uninit, Value::Uninit]))
    );
}

#[test]
fn test_source_program_parses_and_runs_global_asm_macro() {
    let source = r#"
        core::arch::global_asm!(
            ".globl test_symbol",
            sym main,
            const 4usize,
            options(raw),
            clobber_abi("C"),
        );

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("global_asm should parse");

    let Some(Item::GlobalAsm(asm)) = program.items().first() else {
        panic!(
            "first item should be GlobalAsm, got {:?}",
            program.items().first()
        );
    };
    assert_eq!(asm.template, ".globl test_symbol");
    assert!(asm.options.raw);
    assert_eq!(asm.clobbers, vec!["C".to_string()]);
    assert_eq!(asm.operands.len(), 2);
    assert!(matches!(&asm.operands[0], AsmOperand::Sym(symbol) if symbol == "main"));
    assert!(matches!(
        &asm.operands[1],
        AsmOperand::Const(Expr::Literal(Value::Uint { value: 4, .. }))
    ));

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_unqualified_global_asm_macro() {
    // The bare (single-segment) `global_asm!` path must dispatch the same way
    // as the fully-qualified `core::arch::global_asm!` form.
    let source = r#"
        global_asm!(".att_syntax", options(att_syntax));

        fn main() -> u32 {
            7u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("unqualified global_asm should parse");

    let Some(Item::GlobalAsm(asm)) = program.items().first() else {
        panic!(
            "first item should be GlobalAsm, got {:?}",
            program.items().first()
        );
    };
    assert_eq!(asm.template, ".att_syntax");
    assert!(asm.options.att_syntax);
    assert!(asm.operands.is_empty());

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_global_asm_rejects_register_operand() {
    // `global_asm!` may only carry `const` and `sym` operands; a register
    // input operand is invalid and must surface a parse error rather than
    // silently producing an unsound item.
    let source = r#"
        core::arch::global_asm!("mov {0:e}, 1", in(reg) 5u32);

        fn main() -> u32 {
            0u32
        }
    "#;

    let err = SourceProgram::parse(source)
        .expect_err("global_asm with a register operand should be rejected");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("global_asm"),
        "error should name the global_asm restriction, got: {msg}"
    );
}

#[test]
fn test_unsupported_item_macro_is_skipped() {
    // Unrecognized item-position macros are not item-level builtins, so they
    // are dropped during ingestion (matching the pre-existing macro filter)
    // and must not appear as semantic items or break parsing of `main`.
    let source = r#"
        thread_local!(static FOO: u32 = 1u32);

        fn main() -> u32 {
            9u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("program with unknown item macro should parse");

    assert!(
        program
            .items()
            .iter()
            .all(|item| !matches!(item, Item::GlobalAsm(_))),
        "unrecognized item macro must not become a GlobalAsm item"
    );

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(9)));
}

fn find_main_inline_asm(program: &SourceProgram) -> &InlineAsm {
    let main_body = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::Fn { name, body, .. } if name == "main" => Some(body),
            _ => None,
        })
        .expect("main function should be present");

    find_inline_asm_in_expr(main_body).expect("inline asm should appear in main body")
}

fn find_inline_asm_in_expr(expr: &Expr) -> Option<&InlineAsm> {
    match expr {
        Expr::InlineAsm(asm) => Some(asm),
        Expr::UnOp { expr, .. }
        | Expr::Cast { expr, .. }
        | Expr::Deref(expr)
        | Expr::RawDeref(expr)
        | Expr::AddrOf { expr, .. }
        | Expr::Field { base: expr, .. }
        | Expr::ArrayRepeat { value: expr, .. }
        | Expr::UnionFieldAccess {
            union_expr: expr, ..
        }
        | Expr::Closure { body: expr, .. }
        | Expr::Panic { message: expr }
        | Expr::Loop { body: expr, .. }
        | Expr::Unsafe { block: expr }
        | Expr::Await { base: expr }
        | Expr::Async { body: expr, .. } => find_inline_asm_in_expr(expr),
        Expr::BinOp { left, right, .. }
        | Expr::Assign {
            target: left,
            value: right,
        }
        | Expr::AssignOp {
            target: left,
            value: right,
            ..
        }
        | Expr::Index {
            base: left,
            index: right,
        }
        | Expr::While {
            condition: left,
            body: right,
            ..
        }
        | Expr::For {
            iter: left,
            body: right,
            ..
        } => find_inline_asm_in_expr(left).or_else(|| find_inline_asm_in_expr(right)),
        Expr::Return(expr) | Expr::Break { value: expr, .. } => {
            expr.as_deref().and_then(find_inline_asm_in_expr)
        }
        Expr::Range { start, end, .. } => start
            .as_deref()
            .and_then(find_inline_asm_in_expr)
            .or_else(|| end.as_deref().and_then(find_inline_asm_in_expr)),
        Expr::Call { func, args, .. }
        | Expr::MethodCall {
            receiver: func,
            args,
            ..
        } => find_inline_asm_in_expr(func).or_else(|| find_inline_asm_in_slice(args)),
        Expr::Tuple(exprs) | Expr::Array(exprs) => find_inline_asm_in_slice(exprs),
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => find_inline_asm_in_expr(condition)
            .or_else(|| find_inline_asm_in_expr(then_branch))
            .or_else(|| else_branch.as_deref().and_then(find_inline_asm_in_expr)),
        Expr::Match { scrutinee, arms } => find_inline_asm_in_expr(scrutinee)
            .or_else(|| arms.iter().find_map(find_inline_asm_in_arm)),
        Expr::Block { stmts, expr } => find_inline_asm_in_stmts(stmts)
            .or_else(|| expr.as_deref().and_then(find_inline_asm_in_expr)),
        Expr::Struct { fields, .. } => fields
            .iter()
            .find_map(|(_, expr)| find_inline_asm_in_expr(expr)),
        Expr::UnionInit {
            field: (_, expr), ..
        } => find_inline_asm_in_expr(expr),
        Expr::EnumVariant { payload, .. } => match payload {
            EnumVariantPayload::Unit => None,
            EnumVariantPayload::Tuple(exprs) => find_inline_asm_in_slice(exprs),
            EnumVariantPayload::Struct(fields) => fields
                .iter()
                .find_map(|(_, expr)| find_inline_asm_in_expr(expr)),
        },
        Expr::Literal(_) | Expr::Var { .. } | Expr::Continue { .. } => None,
    }
}

fn find_inline_asm_in_stmts(stmts: &[Stmt]) -> Option<&InlineAsm> {
    stmts.iter().find_map(|stmt| match stmt {
        Stmt::Let {
            init, else_block, ..
        } => init
            .as_deref()
            .and_then(find_inline_asm_in_expr)
            .or_else(|| else_block.as_deref().and_then(find_inline_asm_in_expr)),
        Stmt::Expr(expr) => find_inline_asm_in_expr(expr),
        Stmt::Item(_) => None,
    })
}

fn find_inline_asm_in_slice(exprs: &[Expr]) -> Option<&InlineAsm> {
    exprs.iter().find_map(find_inline_asm_in_expr)
}

fn find_inline_asm_in_arm(arm: &MatchArm) -> Option<&InlineAsm> {
    arm.guard
        .as_ref()
        .and_then(find_inline_asm_in_expr)
        .or_else(|| find_inline_asm_in_expr(&arm.body))
}
