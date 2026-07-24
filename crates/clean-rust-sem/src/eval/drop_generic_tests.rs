// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::tests_support::make_let;
use super::Interpreter;
use crate::expr::{Expr, MatchArm, Pattern, Stmt};
use crate::memory::{Address, AllocId};
use crate::stmt::{FunctionDef, StmtResult};
use crate::types::{IntType, Lifetime, Mutability, RustType, TypeParamDef, TypeVar};
use crate::values::{BinOp, Value};
use std::collections::BTreeMap;

fn make_generic_named_type(name: &str, type_args: Vec<RustType>) -> RustType {
    RustType::Named {
        name: name.to_string(),
        type_args,
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn make_type_param(id: u32, name: &str) -> RustType {
    RustType::TypeParam(TypeVar {
        id,
        name: Some(name.to_string()),
    })
}

fn register_generic_outer_drop(interp: &mut Interpreter) {
    let generic_outer_ty = make_generic_named_type("Outer", vec![make_type_param(0, "T")]);

    interp.ctx.register_function(FunctionDef {
        name: "Outer_drop".to_string(),
        params: vec![(
            "_self".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Static,
                mutability: Mutability::Mutable,
                inner: Box::new(generic_outer_ty),
            },
        )],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: "_dropped".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Field {
                base: Box::new(Expr::Deref(Box::new(Expr::Var {
                    name: "_self".to_string(),
                    local_idx: 0,
                }))),
                field: "marker".to_string(),
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp.ctx.register_function_context_type_params(
        "Outer_drop".to_string(),
        vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
    );
    interp
        .ctx
        .register_drop_impl("Outer".to_string(), "Outer_drop".to_string());
}

fn register_counting_outer_drop(interp: &mut Interpreter) {
    let generic_outer_ty = make_generic_named_type("Outer", vec![make_type_param(0, "T")]);

    interp.ctx.register_function(FunctionDef {
        name: "Outer_drop".to_string(),
        params: vec![(
            "_self".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Static,
                mutability: Mutability::Mutable,
                inner: Box::new(generic_outer_ty),
            },
        )],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: "_drop_count".to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::Var {
                    name: "_drop_count".to_string(),
                    local_idx: 0,
                }),
                right: Box::new(Expr::Literal(Value::i32(1))),
            }),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp.ctx.register_function_context_type_params(
        "Outer_drop".to_string(),
        vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
    );
    interp
        .ctx
        .register_drop_impl("Outer".to_string(), "Outer_drop".to_string());
}

fn register_make_outer(interp: &mut Interpreter) {
    interp.ctx.register_function(FunctionDef {
        name: "make_outer".to_string(),
        params: vec![],
        ret_ty: make_generic_named_type("Outer", vec![make_type_param(0, "T")]),
        body: Expr::Struct {
            name: "Outer".to_string(),
            fields: vec![("marker".to_string(), Expr::Literal(Value::Bool(true)))],
            type_args: vec![make_type_param(0, "T")],
            const_args: vec![],
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
    });
}

fn make_generic_drop_program(binding_ty: Option<RustType>, init_expr: Expr) -> Expr {
    Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let("outer", false, binding_ty, init_expr)],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    }
}

fn run_generic_drop_program(binding_ty: Option<RustType>, init_expr: Expr) -> Option<Value> {
    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);
    register_make_outer(&mut interp);
    let program = make_generic_drop_program(binding_ty, init_expr);
    interp.eval(&program).value()
}

#[test]
fn test_call_drop_invokes_generic_drop_impl_for_annotated_and_inferred_bindings() {
    let outer_bool_ty = make_generic_named_type("Outer", vec![RustType::Bool]);
    let constructor_expr = Expr::Struct {
        name: "Outer".to_string(),
        fields: vec![("marker".to_string(), Expr::Literal(Value::Bool(true)))],
        type_args: vec![RustType::Bool],
        const_args: vec![],
    };

    assert_eq!(
        run_generic_drop_program(Some(outer_bool_ty), constructor_expr.clone()),
        Some(Value::Bool(true)),
        "annotated generic bindings must preserve drop receiver compatibility"
    );
    assert_eq!(
        run_generic_drop_program(None, constructor_expr),
        Some(Value::Bool(true)),
        "unannotated generic constructors must preserve drop receiver compatibility"
    );
}

#[test]
fn test_call_drop_invokes_generic_drop_impl_for_unannotated_call_results() {
    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "make_outer".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![RustType::Bool],
    };

    assert_eq!(
        run_generic_drop_program(None, call_expr),
        Some(Value::Bool(true)),
        "unannotated generic call results must preserve drop receiver compatibility"
    );
}

/// Build a program that binds a generic value through a tuple pattern:
///   let _dropped = false;
///   { let (outer,) = (Outer::<bool> { marker: true },); }
///   _dropped   // should be true if Drop::drop ran
fn make_pattern_drop_program(init_expr: Expr) -> Expr {
    let tuple_init = Expr::Tuple(vec![init_expr]);
    let tuple_pattern = Pattern::Tuple(vec![Pattern::Binding {
        name: "outer".to_string(),
        mutable: false,
        subpattern: None,
    }]);
    Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![Stmt::Let {
                    pattern: tuple_pattern,
                    ty: None,
                    init: Some(Box::new(tuple_init)),
                    else_block: None,
                }],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    }
}

fn make_subpattern_drop_program(init_expr: Expr) -> Expr {
    let pattern = Pattern::Binding {
        name: "outer".to_string(),
        mutable: false,
        subpattern: Some(Box::new(Pattern::Struct {
            name: "Outer".to_string(),
            fields: vec![("marker".to_string(), Pattern::Wildcard)],
            rest: false,
        })),
    };
    Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![Stmt::Let {
                    pattern,
                    ty: None,
                    init: Some(Box::new(init_expr)),
                    else_block: None,
                }],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    }
}

fn register_wrapper_with_outer_field(interp: &mut Interpreter) {
    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Wrapper".to_string(),
        fields: vec![("outer".to_string(), make_type_param(2, "U"))],
        type_params: vec![TypeParamDef {
            id: 2,
            name: "U".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });
}

fn make_struct_pattern_drop_program(init_expr: Expr) -> Expr {
    let pattern = Pattern::Struct {
        name: "Wrapper".to_string(),
        fields: vec![(
            "outer".to_string(),
            Pattern::Binding {
                name: "outer".to_string(),
                mutable: false,
                subpattern: None,
            },
        )],
        rest: false,
    };
    Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![Stmt::Let {
                    pattern,
                    ty: None,
                    init: Some(Box::new(init_expr)),
                    else_block: None,
                }],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    }
}

fn make_match_binding_drop_count_program() -> Expr {
    let tuple_call = Expr::Tuple(vec![Expr::Call {
        func: Box::new(Expr::Var {
            name: "make_outer".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![RustType::Bool],
    }]);
    let tuple_pattern = Pattern::Tuple(vec![Pattern::Binding {
        name: "outer".to_string(),
        mutable: false,
        subpattern: None,
    }]);
    Expr::Block {
        stmts: vec![
            make_let(
                "_drop_count",
                true,
                Some(RustType::Int(IntType::I32)),
                Expr::Literal(Value::i32(0)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![
                    make_let("tuple", false, None, tuple_call),
                    Stmt::Expr(Expr::Match {
                        scrutinee: Box::new(Expr::Var {
                            name: "tuple".to_string(),
                            local_idx: 0,
                        }),
                        arms: vec![
                            MatchArm {
                                pattern: tuple_pattern,
                                guard: None,
                                body: Expr::Literal(Value::Unit),
                            },
                            MatchArm {
                                pattern: Pattern::Wildcard,
                                guard: None,
                                body: Expr::Literal(Value::Unit),
                            },
                        ],
                    }),
                ],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_drop_count".to_string(),
            local_idx: 0,
        })),
    }
}

#[test]
fn test_call_drop_invokes_generic_drop_impl_for_tuple_pattern_bound_constructor() {
    let constructor_expr = Expr::Struct {
        name: "Outer".to_string(),
        fields: vec![("marker".to_string(), Expr::Literal(Value::Bool(true)))],
        type_args: vec![RustType::Bool],
        const_args: vec![],
    };

    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);
    let program = make_pattern_drop_program(constructor_expr);
    let result = interp.eval(&program).value();

    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "generic value bound through tuple pattern must run custom Drop::drop"
    );
}

#[test]
fn test_call_drop_invokes_generic_drop_impl_for_tuple_pattern_bound_call_result() {
    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "make_outer".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![RustType::Bool],
    };

    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);
    register_make_outer(&mut interp);
    let program = make_pattern_drop_program(call_expr);
    let result = interp.eval(&program).value();

    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "generic call result bound through tuple pattern must run custom Drop::drop"
    );
}

#[test]
fn test_call_drop_invokes_generic_drop_impl_for_subpattern_bound_call_result() {
    let call_expr = Expr::Call {
        func: Box::new(Expr::Var {
            name: "make_outer".to_string(),
            local_idx: 0,
        }),
        args: vec![],
        type_args: vec![RustType::Bool],
    };

    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);
    register_make_outer(&mut interp);
    let program = make_subpattern_drop_program(call_expr);
    let result = interp.eval(&program).value();

    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "whole-value subpattern bindings must preserve generic drop receiver compatibility"
    );
}

#[test]
fn test_match_arm_bindings_preserve_generic_drop_type_for_var_scrutinee() {
    let mut interp = Interpreter::new();
    register_counting_outer_drop(&mut interp);
    register_make_outer(&mut interp);
    let program = make_match_binding_drop_count_program();
    let result = interp.eval(&program).value();

    assert_eq!(
        result,
        Some(Value::i32(2)),
        "match arm bindings should drop both the arm-bound value and the original tuple element"
    );
}

#[test]
fn test_call_drop_invokes_generic_drop_impl_for_struct_pattern_field_binding() {
    let outer_bool_ty = make_generic_named_type("Outer", vec![RustType::Bool]);
    let wrapper_init = Expr::Struct {
        name: "Wrapper".to_string(),
        fields: vec![(
            "outer".to_string(),
            Expr::Struct {
                name: "Outer".to_string(),
                fields: vec![("marker".to_string(), Expr::Literal(Value::Bool(true)))],
                type_args: vec![RustType::Bool],
                const_args: vec![],
            },
        )],
        type_args: vec![outer_bool_ty.clone()],
        const_args: vec![],
    };

    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);
    register_wrapper_with_outer_field(&mut interp);
    let program = make_struct_pattern_drop_program(wrapper_init);
    let result = interp.eval(&program).value();

    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "generic values projected through struct field patterns must preserve their concrete drop type"
    );
}

#[test]
fn test_collect_typed_pattern_bindings_peels_reference_hint() {
    let outer_bool_ty = make_generic_named_type("Outer", vec![RustType::Bool]);
    let ref_ty = RustType::Reference {
        lifetime: Lifetime::Static,
        mutability: Mutability::Shared,
        inner: Box::new(outer_bool_ty.clone()),
    };
    let referent = Value::Struct {
        name: "Outer".to_string(),
        fields: BTreeMap::from([("marker".to_string(), Value::Bool(true))]),
    };
    let value = Value::Reference {
        addr: Address::new(AllocId(1), 0),
        mutability: Mutability::Shared,
        lifetime: Lifetime::Static,
        referent: Some(Box::new(referent.clone())),
    };
    let pattern = Pattern::Ref {
        mutability: Mutability::Shared,
        pattern: Box::new(Pattern::Binding {
            name: "outer".to_string(),
            mutable: false,
            subpattern: None,
        }),
    };

    let interp = Interpreter::new();
    let bindings = interp
        .collect_typed_pattern_bindings(&pattern, &value, Some(&ref_ty))
        .expect("reference patterns should peel one type layer for inner bindings");

    assert_eq!(bindings.bindings.len(), 1);
    assert_eq!(bindings.bindings[0].0, "outer");
    assert_eq!(bindings.bindings[0].1, referent);
    assert_eq!(bindings.bindings[0].3.as_ref(), Some(&outer_bool_ty));
}

fn register_droppable_with_flag(interp: &mut Interpreter, flag_name: &str) {
    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Droppable".to_string(),
        fields: vec![("tag".to_string(), RustType::Bool)],
        type_params: vec![TypeParamDef {
            id: 1,
            name: "U".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });
    interp.ctx.register_function(FunctionDef {
        name: "Droppable_drop".to_string(),
        params: vec![(
            "_self".to_string(),
            RustType::Reference {
                lifetime: Lifetime::Static,
                mutability: Mutability::Mutable,
                inner: Box::new(make_generic_named_type(
                    "Droppable",
                    vec![make_type_param(1, "U")],
                )),
            },
        )],
        ret_ty: RustType::Unit,
        body: Expr::Assign {
            target: Box::new(Expr::Var {
                name: flag_name.to_string(),
                local_idx: 0,
            }),
            value: Box::new(Expr::Literal(Value::Bool(true))),
        },
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
    interp.ctx.register_function_context_type_params(
        "Droppable_drop".to_string(),
        vec![TypeParamDef {
            id: 1,
            name: "U".to_string(),
            bounds: vec![],
        }],
    );
    interp
        .ctx
        .register_drop_impl("Droppable".to_string(), "Droppable_drop".to_string());
}

fn register_container_with_inner_field(interp: &mut Interpreter) {
    interp.ctx.register_type(crate::stmt::TypeDef::Struct {
        name: "Container".to_string(),
        fields: vec![("inner".to_string(), make_type_param(0, "T"))],
        type_params: vec![TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        }],
        const_params: vec![],
    });
}

fn make_container_with_droppable_program() -> Expr {
    let droppable_bool = make_generic_named_type("Droppable", vec![RustType::Bool]);
    Expr::Block {
        stmts: vec![
            make_let(
                "_inner_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![make_let(
                    "c",
                    false,
                    Some(make_generic_named_type(
                        "Container",
                        vec![droppable_bool.clone()],
                    )),
                    Expr::Struct {
                        name: "Container".to_string(),
                        fields: vec![(
                            "inner".to_string(),
                            Expr::Struct {
                                name: "Droppable".to_string(),
                                fields: vec![("tag".to_string(), Expr::Literal(Value::Bool(true)))],
                                type_args: vec![RustType::Bool],
                                const_args: vec![],
                            },
                        )],
                        type_args: vec![droppable_bool],
                        const_args: vec![],
                    },
                )],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_inner_dropped".to_string(),
            local_idx: 0,
        })),
    }
}

#[test]
fn test_call_drop_invokes_generic_drop_on_struct_field_with_generic_type() {
    let mut interp = Interpreter::new();
    register_droppable_with_flag(&mut interp, "_inner_dropped");
    register_container_with_inner_field(&mut interp);
    let program = make_container_with_droppable_program();
    let result = interp.eval(&program).value();
    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "generic struct field with its own Drop impl must be dropped recursively"
    );
}

#[test]
fn test_drop_children_in_rust_order_substitutes_generic_struct_field_type() {
    let mut interp = Interpreter::new();
    register_container_with_inner_field(&mut interp);

    let droppable_bool = make_generic_named_type("Droppable", vec![RustType::Bool]);
    let stmt = make_let(
        "c",
        false,
        Some(make_generic_named_type(
            "Container",
            vec![droppable_bool.clone()],
        )),
        Expr::Struct {
            name: "Container".to_string(),
            fields: vec![(
                "inner".to_string(),
                Expr::Struct {
                    name: "Droppable".to_string(),
                    fields: vec![("tag".to_string(), Expr::Literal(Value::Bool(true)))],
                    type_args: vec![RustType::Bool],
                    const_args: vec![],
                },
            )],
            type_args: vec![droppable_bool.clone()],
            const_args: vec![],
        },
    );
    assert!(matches!(interp.exec_stmt(&stmt), StmtResult::Ok));

    let place = interp.place_for_name("c");
    let container_ty = interp
        .binding_drop_type("c")
        .expect("binding should keep its annotated generic container type");
    let children = interp.drop_children_in_rust_order(&place, &container_ty);

    assert_eq!(children.len(), 1);
    assert_eq!(children[0].1, droppable_bool);
}

#[test]
fn test_for_loop_tuple_iterable_preserves_generic_drop_type() {
    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);

    let constructor = Expr::Struct {
        name: "Outer".to_string(),
        fields: vec![("marker".to_string(), Expr::Literal(Value::Bool(true)))],
        type_args: vec![RustType::Bool],
        const_args: vec![],
    };

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![Stmt::Expr(Expr::For {
                    label: None,
                    pattern: Box::new(Pattern::Binding {
                        name: "outer".to_string(),
                        mutable: false,
                        subpattern: None,
                    }),
                    iter: Box::new(Expr::Tuple(vec![constructor])),
                    body: Box::new(Expr::Literal(Value::Unit)),
                })],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program).value();
    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "for-loop over tuple iterable must preserve Outer<bool> drop type"
    );
}

#[test]
fn test_for_loop_array_literal_iterable_preserves_generic_drop_type() {
    let mut interp = Interpreter::new();
    register_generic_outer_drop(&mut interp);

    let constructor = Expr::Struct {
        name: "Outer".to_string(),
        fields: vec![("marker".to_string(), Expr::Literal(Value::Bool(true)))],
        type_args: vec![RustType::Bool],
        const_args: vec![],
    };

    let program = Expr::Block {
        stmts: vec![
            make_let(
                "_dropped",
                true,
                Some(RustType::Bool),
                Expr::Literal(Value::Bool(false)),
            ),
            Stmt::Expr(Expr::Block {
                stmts: vec![Stmt::Expr(Expr::For {
                    label: None,
                    pattern: Box::new(Pattern::Binding {
                        name: "outer".to_string(),
                        mutable: false,
                        subpattern: None,
                    }),
                    iter: Box::new(Expr::Array(vec![constructor])),
                    body: Box::new(Expr::Literal(Value::Unit)),
                })],
                expr: Some(Box::new(Expr::Literal(Value::Unit))),
            }),
        ],
        expr: Some(Box::new(Expr::Var {
            name: "_dropped".to_string(),
            local_idx: 0,
        })),
    };

    let result = interp.eval(&program).value();
    assert_eq!(
        result,
        Some(Value::Bool(true)),
        "for-loop over array literal iterable must preserve Outer<bool> drop type"
    );
}
