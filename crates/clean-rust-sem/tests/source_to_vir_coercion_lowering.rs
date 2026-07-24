// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for VIR lowering of coercion paths:
//! - `NeverToAny`: diverging expressions in coercion positions lower without error
//! - `RefToRawPtr`: `&mut T → *const T` lowers through AddressOf + Retag
//! - `PointerUnsize`: dyn-trait unsizing lowers through the dedicated cast kind

use clean_rust_sem::vir::{CastKind, Term};
use clean_rust_sem::{LoweredProgram, Rvalue, SourceProgram, Stmt};

fn lowered_program(source: &str) -> LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program.lower_to_vir().expect("source should lower to VIR")
}

#[test]
fn test_never_type_let_binding_lowers_without_error() {
    // A diverging function call in a let binding with a typed destination
    // should lower successfully — the Never source type bypasses coercion
    // and the call terminator handles control flow.
    let source = r#"
        fn diverge() -> ! {
            panic!("gone")
        }

        fn main() -> u32 {
            let x: u32 = diverge();
            x
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // The diverge() call should produce a Call terminator.
    let has_call_to_diverge = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call { func, .. }
                if matches!(
                    func,
                    clean_rust_sem::Operand::Constant(clean_rust_sem::vir::Constant::FnDef { name, .. })
                        if name == "diverge"
                )
        )
    });
    assert!(
        has_call_to_diverge,
        "diverging call should lower to a Term::Call terminator: {body:#?}"
    );
}

#[test]
fn test_never_type_call_arg_lowers_without_error() {
    // Previously, passing a diverging expression as a call argument caused
    // an "operand coercion" error because materialize_operand_as did not
    // handle Never-typed sources. Now it lowers the diverging expr and
    // returns a dummy operand.
    let source = r#"
        fn diverge() -> ! {
            panic!("gone")
        }

        fn consume(x: u32) -> u32 { x }

        fn main() -> u32 {
            consume(diverge())
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // The diverge() call should produce a Call terminator.
    let has_call_to_diverge = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call { func, .. }
                if matches!(
                    func,
                    clean_rust_sem::Operand::Constant(clean_rust_sem::vir::Constant::FnDef { name, .. })
                        if name == "diverge"
                )
        )
    });
    assert!(
        has_call_to_diverge,
        "diverging call as argument should lower to a Term::Call terminator: {body:#?}"
    );

    let has_call_to_consume = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call { func, .. }
                if matches!(
                    func,
                    clean_rust_sem::Operand::Constant(clean_rust_sem::vir::Constant::FnDef { name, .. })
                        if name == "consume"
                )
        )
    });
    assert!(
        !has_call_to_consume,
        "outer call should not lower after a diverging argument: {body:#?}"
    );
}

#[test]
fn test_never_type_call_arg_short_circuits_later_args() {
    let source = r#"
        fn diverge() -> ! {
            panic!("gone")
        }

        fn consume(a: u32, b: u32) -> u32 { a }

        fn main() -> u32 {
            consume(diverge(), { 7u32 })
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_call_to_diverge = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call { func, .. }
                if matches!(
                    func,
                    clean_rust_sem::Operand::Constant(clean_rust_sem::vir::Constant::FnDef { name, .. })
                        if name == "diverge"
                )
        )
    });
    assert!(
        has_call_to_diverge,
        "lowering should stop at the diverging argument and not inspect later args: {body:#?}"
    );
}

#[test]
fn test_never_type_tuple_element_short_circuits_later_elements() {
    let source = r#"
        fn diverge() -> ! {
            panic!("gone")
        }

        fn main() -> (u32, u32) {
            (diverge(), { 7u32 })
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_call_to_diverge = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call { func, .. }
                if matches!(
                    func,
                    clean_rust_sem::Operand::Constant(clean_rust_sem::vir::Constant::FnDef { name, .. })
                        if name == "diverge"
                )
        )
    });
    assert!(
        has_call_to_diverge,
        "tuple lowering should stop at the diverging element and not inspect later elements: {body:#?}"
    );

    let has_tuple_aggregate = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: clean_rust_sem::vir::AggregateKind::Tuple,
                        ..
                    },
                    ..
                }
            )
        });
    assert!(
        !has_tuple_aggregate,
        "tuple aggregate should not lower after a diverging element: {body:#?}"
    );
}

#[test]
fn test_mut_ref_to_const_raw_ptr_coercion_lowers_through_address_of() {
    // &mut T → *const T coerces via RefToRawPtr.
    // The VIR lowering emits AddressOf + Retag.
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 42u32;
            let p: *const u32 = &mut x;
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_address_of = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::AddressOf { .. },
                    ..
                }
            )
        });
    assert!(
        has_address_of,
        "`&mut T → *const T` coercion should lower through AddressOf: {body:#?}"
    );
}

#[test]
fn test_ref_to_dyn_trait_return_lowers_through_pointer_unsize() {
    let source = r#"
        trait Animal {
            fn speak(&self) -> u32;
        }

        struct Dog;

        impl Animal for Dog {
            fn speak(&self) -> u32 { 1u32 }
        }

        fn upcast(dog: &Dog) -> &dyn Animal {
            dog
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("upcast")
        .expect("lowered program should contain `upcast`");

    let has_pointer_unsize = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Cast {
                        kind: CastKind::PointerUnsize,
                        ..
                    },
                    ..
                }
            )
        });
    assert!(
        has_pointer_unsize,
        "`&Dog → &dyn Animal` should lower through a PointerUnsize cast: {body:#?}"
    );
}

#[test]
fn test_box_to_dyn_trait_return_lowers_through_pointer_unsize() {
    let source = r#"
        trait Animal {
            fn speak(&self) -> u32;
        }

        struct Dog;

        impl Animal for Dog {
            fn speak(&self) -> u32 { 1u32 }
        }

        fn upcast_box(dog: Box<Dog>) -> Box<dyn Animal> {
            dog
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("upcast_box")
        .expect("lowered program should contain `upcast_box`");

    let has_pointer_unsize = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Cast {
                        kind: CastKind::PointerUnsize,
                        ..
                    },
                    ..
                }
            )
        });
    assert!(
        has_pointer_unsize,
        "`Box<Dog> → Box<dyn Animal>` should lower through a PointerUnsize cast: {body:#?}"
    );
}

#[test]
fn test_deref_then_dyn_trait_unsize_lowers_as_ref_plus_pointer_unsize() {
    let source = r#"
        trait Animal {
            fn speak(&self) -> u32;
        }

        struct Dog;

        impl Animal for Dog {
            fn speak(&self) -> u32 { 1u32 }
        }

        fn upcast_box_ref(dog: &Box<Dog>) -> &dyn Animal {
            dog
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("upcast_box_ref")
        .expect("lowered program should contain `upcast_box_ref`");

    let has_ref = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Ref { .. },
                    ..
                }
            )
        });
    let has_pointer_unsize = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Cast {
                        kind: CastKind::PointerUnsize,
                        ..
                    },
                    ..
                }
            )
        });
    assert!(
        has_ref && has_pointer_unsize,
        "`&Box<Dog> → &dyn Animal` should lower through deref/reborrow followed by PointerUnsize: {body:#?}"
    );
}

#[test]
fn test_pointer_unsize_cast_kind_exists() {
    // Verify the PointerUnsize variant is accessible and distinct from other kinds.
    assert_ne!(CastKind::PointerUnsize, CastKind::PtrToPtr);
    assert_ne!(CastKind::PointerUnsize, CastKind::Transmute);
}
