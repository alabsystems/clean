// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::expr::{Expr, Pattern};
use crate::memory::{Address, AllocId};
use crate::stmt::{FunctionDef, TraitDef};
use crate::types::{FunctionSignature, Lifetime, Mutability, ReceiverMode, RustType, UintType};
use crate::values::{BinOp, FatPointer, FatPtrMetadata, Value};
use std::collections::BTreeMap;

fn dog_type() -> RustType {
    RustType::Named {
        name: "Dog".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn animal_trait_type() -> RustType {
    RustType::DynTrait {
        trait_name: "Animal".to_string(),
        auto_traits: vec![],
    }
}

fn shared_animal_ref_type() -> RustType {
    RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(animal_trait_type()),
    }
}

fn shared_u32_slice_ref_type() -> RustType {
    RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Slice {
            elem: Box::new(RustType::Uint(UintType::U32)),
        }),
    }
}

fn register_animal_dispatch(interp: &mut Interpreter, speak_value: u32) {
    interp.ctx.register_full_trait_def(TraitDef::new(
        "Animal".to_string(),
        vec![FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    ));
    interp
        .ctx
        .register_trait_impl("Animal".to_string(), dog_type());
    interp.ctx.add_impl_method(
        "Animal",
        "Dog",
        "speak".to_string(),
        "Dog_speak".to_string(),
    );
    interp.ctx.register_function(FunctionDef {
        name: "Dog_speak".to_string(),
        params: vec![("self".to_string(), dog_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(speak_value)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}

#[test]
fn test_ref_to_dyn_trait_coercion_builds_vtable_fat_ptr() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 7);

    let dog_ref = Value::Reference {
        addr: Address::new(AllocId(100), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::Struct {
            name: "Dog".to_string(),
            fields: Default::default(),
        })),
    };

    let coerced = interp
        .coerce_runtime_value(&dog_ref, &shared_animal_ref_type())
        .expect("&Dog should coerce to &dyn Animal");

    match coerced {
        Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::VtablePtr(vtable_ptr),
        }) => {
            assert_eq!(vtable_ptr.trait_name, "Animal");
            match data_pointer.as_ref() {
                Value::Reference {
                    mutability,
                    lifetime,
                    ..
                } => {
                    assert_eq!(*mutability, Mutability::Shared);
                    assert_eq!(*lifetime, Lifetime::Named("a".to_string()));
                }
                other => panic!("expected thin reference inside fat pointer, got {other:?}"),
            }
        }
        other => panic!("expected fat pointer for &dyn coercion, got {other:?}"),
    }
}

#[test]
fn test_array_ref_to_slice_coercion_builds_length_fat_ptr() {
    let interp = Interpreter::new();
    let array_ref = Value::Reference {
        addr: Address::new(AllocId(200), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::Array(vec![
            Value::u32(1),
            Value::u32(2),
            Value::u32(3),
        ]))),
    };

    let coerced = interp
        .coerce_runtime_value(&array_ref, &shared_u32_slice_ref_type())
        .expect("&[u32; 3] should coerce to &[u32]");

    match coerced {
        Value::FatPtr(FatPointer {
            data_pointer,
            metadata: FatPtrMetadata::SliceLen(len),
        }) => {
            assert_eq!(len, 3);
            assert!(matches!(data_pointer.as_ref(), Value::Reference { .. }));
        }
        other => panic!("expected fat slice pointer, got {other:?}"),
    }
}

#[test]
fn test_box_to_dyn_trait_coercion_dispatches_through_fat_ptr() {
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 88);

    let boxed_dyn = interp
        .coerce_runtime_value(
            &Value::Struct {
                name: "Dog".to_string(),
                fields: Default::default(),
            },
            &RustType::Box {
                inner: Box::new(animal_trait_type()),
            },
        )
        .expect("Box<Dog> should coerce to Box<dyn Animal>");

    assert!(matches!(
        boxed_dyn,
        Value::FatPtr(FatPointer {
            metadata: FatPtrMetadata::VtablePtr(_),
            ..
        })
    ));

    let result = interp.eval(&Expr::MethodCall {
        receiver: Box::new(Expr::Literal(boxed_dyn)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    });
    assert_eq!(result.value(), Some(Value::u32(88)));
}

// ---------------------------------------------------------------------------
// Reference-receiver dynamic dispatch (&self / &mut self through dyn Trait).
// ---------------------------------------------------------------------------

fn counter_type() -> RustType {
    RustType::Named {
        name: "Counter".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn shared_counter_ref_type() -> RustType {
    RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(counter_type()),
    }
}

fn mut_counter_ref_type() -> RustType {
    RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Mutable,
        inner: Box::new(counter_type()),
    }
}

fn ticker_trait_type() -> RustType {
    RustType::DynTrait {
        trait_name: "Ticker".to_string(),
        auto_traits: vec![],
    }
}

/// `self.<field>` — relies on the evaluator auto-dereferencing the reference
/// receiver for both reads and writes.
fn self_field(field: &str) -> Expr {
    Expr::Field {
        base: Box::new(Expr::Var {
            name: "self".to_string(),
            local_idx: 0,
        }),
        field: field.to_string(),
    }
}

/// Register a `Ticker` trait with a `&self` reader (`get`) and a `&mut self`
/// mutator (`tick`) implemented for `Counter`.
fn register_ticker_dispatch(interp: &mut Interpreter) {
    interp.ctx.register_full_trait_def(TraitDef::new(
        "Ticker".to_string(),
        vec![
            FunctionSignature {
                name: "get".to_string(),
                receiver: ReceiverMode::ByRef,
                params: vec![],
                ret: RustType::Uint(UintType::U32),
                is_async: false,
                type_params: vec![],
            },
            FunctionSignature {
                name: "tick".to_string(),
                receiver: ReceiverMode::ByMut,
                params: vec![],
                ret: RustType::Uint(UintType::U32),
                is_async: false,
                type_params: vec![],
            },
        ],
    ));
    interp
        .ctx
        .register_trait_impl("Ticker".to_string(), counter_type());
    interp.ctx.add_impl_method(
        "Ticker",
        "Counter",
        "get".to_string(),
        "Counter_get".to_string(),
    );
    interp.ctx.add_impl_method(
        "Ticker",
        "Counter",
        "tick".to_string(),
        "Counter_tick".to_string(),
    );

    // fn get(&self) -> u32 { (*self).n }
    interp.ctx.register_function(FunctionDef {
        name: "Counter_get".to_string(),
        params: vec![("self".to_string(), shared_counter_ref_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: self_field("n"),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });

    // fn tick(&mut self) -> u32 { (*self).n = (*self).n + 1; (*self).n }
    interp.ctx.register_function(FunctionDef {
        name: "Counter_tick".to_string(),
        params: vec![("self".to_string(), mut_counter_ref_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Block {
            stmts: vec![Stmt::Expr(Expr::Assign {
                target: Box::new(self_field("n")),
                value: Box::new(Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(self_field("n")),
                    right: Box::new(Expr::Literal(Value::u32(1))),
                }),
            })],
            expr: Some(Box::new(self_field("n"))),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}

fn counter_value(n: u32) -> Value {
    let mut fields = BTreeMap::new();
    fields.insert("n".to_string(), Value::u32(n));
    Value::Struct {
        name: "Counter".to_string(),
        fields,
    }
}

#[test]
fn test_shared_ref_dyn_dispatch_returns_value() {
    // `let c = Counter { n: 5 }; let t: &dyn Ticker = &c; t.get()`.
    let mut interp = Interpreter::new();
    register_ticker_dispatch(&mut interp);

    let program = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "c".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                ty: Some(counter_type()),
                init: Some(Box::new(Expr::Literal(counter_value(5)))),
                else_block: None,
            },
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "t".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                ty: Some(RustType::Reference {
                    lifetime: Lifetime::Named("a".to_string()),
                    mutability: Mutability::Shared,
                    inner: Box::new(ticker_trait_type()),
                }),
                init: Some(Box::new(Expr::AddrOf {
                    mutability: Mutability::Shared,
                    expr: Box::new(Expr::Var {
                        name: "c".to_string(),
                        local_idx: 0,
                    }),
                })),
                else_block: None,
            },
        ],
        expr: Some(Box::new(Expr::MethodCall {
            receiver: Box::new(Expr::Var {
                name: "t".to_string(),
                local_idx: 0,
            }),
            method: "get".to_string(),
            args: vec![],
            type_args: vec![],
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::u32(5)),
        "&self method through &dyn Ticker should read the referent field"
    );
}

#[test]
fn test_mut_ref_dyn_dispatch_mutates_referent() {
    // `let mut c = Counter { n: 5 }; let t: &mut dyn Ticker = &mut c;
    //  let r = t.tick(); c.n` — the &mut self call must persist through the
    //  shared backing place, so the final `c.n` reflects the increment.
    let mut interp = Interpreter::new();
    // Reference-place tracking (needed for write-back through `&mut self`) is
    // wired up by the aliasing model, so exercise the sound path here.
    interp.aliasing_checks = true;
    register_ticker_dispatch(&mut interp);

    let program = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "c".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: Some(counter_type()),
                init: Some(Box::new(Expr::Literal(counter_value(5)))),
                else_block: None,
            },
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "t".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                ty: Some(RustType::Reference {
                    lifetime: Lifetime::Named("a".to_string()),
                    mutability: Mutability::Mutable,
                    inner: Box::new(ticker_trait_type()),
                }),
                init: Some(Box::new(Expr::AddrOf {
                    mutability: Mutability::Mutable,
                    expr: Box::new(Expr::Var {
                        name: "c".to_string(),
                        local_idx: 0,
                    }),
                })),
                else_block: None,
            },
            Stmt::Expr(Expr::MethodCall {
                receiver: Box::new(Expr::Var {
                    name: "t".to_string(),
                    local_idx: 0,
                }),
                method: "tick".to_string(),
                args: vec![],
                type_args: vec![],
            }),
        ],
        expr: Some(Box::new(Expr::Field {
            base: Box::new(Expr::Var {
                name: "c".to_string(),
                local_idx: 0,
            }),
            field: "n".to_string(),
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::u32(6)),
        "&mut self dispatch through &mut dyn Ticker should mutate the original Counter"
    );
}

#[test]
fn test_mut_ref_dyn_dispatch_returns_updated_value() {
    // The `&mut self` method's own return value should observe the mutation.
    let mut interp = Interpreter::new();
    interp.aliasing_checks = true;
    register_ticker_dispatch(&mut interp);

    let program = Expr::Block {
        stmts: vec![
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "c".to_string(),
                    mutable: true,
                    subpattern: None,
                },
                ty: Some(counter_type()),
                init: Some(Box::new(Expr::Literal(counter_value(40)))),
                else_block: None,
            },
            Stmt::Let {
                pattern: Pattern::Binding {
                    name: "t".to_string(),
                    mutable: false,
                    subpattern: None,
                },
                ty: Some(RustType::Reference {
                    lifetime: Lifetime::Named("a".to_string()),
                    mutability: Mutability::Mutable,
                    inner: Box::new(ticker_trait_type()),
                }),
                init: Some(Box::new(Expr::AddrOf {
                    mutability: Mutability::Mutable,
                    expr: Box::new(Expr::Var {
                        name: "c".to_string(),
                        local_idx: 0,
                    }),
                })),
                else_block: None,
            },
        ],
        expr: Some(Box::new(Expr::MethodCall {
            receiver: Box::new(Expr::Var {
                name: "t".to_string(),
                local_idx: 0,
            }),
            method: "tick".to_string(),
            args: vec![],
            type_args: vec![],
        })),
    };

    let result = interp.eval(&program);
    assert_eq!(
        result.value(),
        Some(Value::u32(41)),
        "&mut self tick should return the incremented count"
    );
}

#[test]
fn test_box_dyn_shared_ref_method_dispatches() {
    // Box<dyn Ticker> holds the concrete value by value; a `&self` method
    // must form a fresh borrow of that owned data rather than rejecting it.
    let mut interp = Interpreter::new();
    register_ticker_dispatch(&mut interp);

    let boxed_dyn = interp
        .coerce_runtime_value(
            &counter_value(99),
            &RustType::Box {
                inner: Box::new(ticker_trait_type()),
            },
        )
        .expect("Box<Counter> should coerce to Box<dyn Ticker>");

    assert!(matches!(
        boxed_dyn,
        Value::FatPtr(FatPointer {
            metadata: FatPtrMetadata::VtablePtr(_),
            ..
        })
    ));

    let result = interp.eval(&Expr::MethodCall {
        receiver: Box::new(Expr::Literal(boxed_dyn)),
        method: "get".to_string(),
        args: vec![],
        type_args: vec![],
    });
    assert_eq!(
        result.value(),
        Some(Value::u32(99)),
        "&self dispatch through Box<dyn Ticker> should read the owned data"
    );
}

#[test]
fn test_trait_object_shared_ref_method_dispatches() {
    // An owned `dyn Ticker` trait object (not a fat pointer) with a `&self`
    // method should borrow its owned data and dispatch.
    let mut interp = Interpreter::new();
    register_ticker_dispatch(&mut interp);

    let trait_obj = interp
        .coerce_runtime_value(&counter_value(12), &ticker_trait_type())
        .expect("Counter should coerce to dyn Ticker");
    assert!(matches!(trait_obj, Value::TraitObject { .. }));

    let result = interp.eval(&Expr::MethodCall {
        receiver: Box::new(Expr::Literal(trait_obj)),
        method: "get".to_string(),
        args: vec![],
        type_args: vec![],
    });
    assert_eq!(
        result.value(),
        Some(Value::u32(12)),
        "&self dispatch through an owned trait object should read its data"
    );
}

#[test]
fn test_by_value_dispatch_through_fat_ptr_still_rejects_reference_for_by_value_receiver() {
    // Soundness guard: a by-value receiver reached through a `&dyn` fat pointer
    // would move out of a borrow and must remain rejected.
    let mut interp = Interpreter::new();
    register_animal_dispatch(&mut interp, 7);

    let dog_ref = Value::Reference {
        addr: Address::new(AllocId(300), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Named("a".to_string()),
        referent: Some(Box::new(Value::Struct {
            name: "Dog".to_string(),
            fields: Default::default(),
        })),
    };
    let fat_ptr = Value::FatPtr(FatPointer::vtable(dog_ref, "Animal"));

    // `speak` is registered with a by-value receiver, but the data pointer is a
    // reference, so dispatch must refuse to move out of the borrow.
    let result = interp.eval(&Expr::MethodCall {
        receiver: Box::new(Expr::Literal(fat_ptr)),
        method: "speak".to_string(),
        args: vec![],
        type_args: vec![],
    });
    match result {
        EvalResult::Error(msg) => {
            assert!(
                msg.contains("by-value receiver"),
                "expected by-value/borrow rejection, got: {msg}"
            );
        }
        other => panic!("expected error for by-value receiver via &dyn, got {other:?}"),
    }
}
