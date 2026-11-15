// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

fn value_ty() -> Ty {
    Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 1)))
}

fn declaration(operands: Vec<OperandType>) -> DialectSchema {
    DialectSchema {
        namespace: "example".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "collect".into(),
            operands,
            results: vec![Ty::Bool],
            attributes: vec![],
        }],
    }
}

fn operation(count: usize) -> DialectInst {
    DialectInst::new("example", "collect")
        .with_operands((0..count).map(|i| ValueId::new(i as u32)))
        .with_result_ty(Ty::Bool)
}

#[test]
fn variadic_zero_one_and_wide_tails_use_one_borrowed_contract() {
    let registry = DialectSchemaRegistry::new([declaration(vec![
        Ty::U64.into(),
        OperandType::VariadicExact(value_ty()),
    ])])
    .unwrap();
    let prefix = Ty::U64;
    let tail = value_ty();
    for count in [0, 1, 4096] {
        let lookups = Cell::new(0);
        let checked = registry
            .validate_op(&operation(count + 1), 1, |id| {
                lookups.set(lookups.get() + 1);
                Some(if id.index() == 0 { &prefix } else { &tail })
            })
            .unwrap();
        assert_eq!(lookups.get(), count + 1);
        assert_eq!(checked.operands.len(), 2, "tail is not expanded");
        assert!(checked.is_variadic());
        assert_eq!(checked.minimum_operand_count(), 1);
        assert!(!checked.accepts_operand_count(0));
        assert!(checked.accepts_operand_count(usize::MAX));
        assert!(std::ptr::eq(
            checked.operand_type_at(1).unwrap(),
            checked.operand_type_at(usize::MAX).unwrap(),
        ));
    }
}

#[test]
fn variadic_only_schema_accepts_empty_without_operand_lookup() {
    let registry =
        DialectSchemaRegistry::new([declaration(vec![OperandType::VariadicExact(value_ty())])])
            .unwrap();
    let checked = registry
        .validate_op(&operation(0), 1, |_| panic!("empty tail has no operand"))
        .unwrap();
    assert_eq!(checked.minimum_operand_count(), 0);
    assert!(checked.accepts_operand_count(0));
}

#[test]
fn variadic_underflow_preserves_precise_fixed_arity_diagnostics() {
    let prefix = vec![Ty::U64.into(), Ty::Bool.into()];
    let fixed = DialectSchemaRegistry::new([declaration(prefix.clone())]).unwrap();
    let mut with_tail = prefix;
    with_tail.push(OperandType::VariadicExact(value_ty()));
    let variadic = DialectSchemaRegistry::new([declaration(with_tail)]).unwrap();
    for count in [0, 1] {
        assert_eq!(
            variadic
                .validate_op(&operation(count), 1, |_| panic!("count checked first"))
                .unwrap_err(),
            SchemaError::OperandCountAtLeast {
                minimum: 2,
                actual: count,
            }
        );
    }
    for count in [0, 1, 3, 4096] {
        assert_eq!(
            fixed
                .validate_op(&operation(count), 1, |_| panic!("count checked first"))
                .unwrap_err(),
            SchemaError::OperandCount {
                expected: 2,
                actual: count,
            }
        );
    }
    let schema = declaration(vec![Ty::U64.into()]).operations.remove(0);
    assert!(!schema.is_variadic());
    assert_eq!(schema.minimum_operand_count(), 1);
    assert!(schema.operand_type_at(1).is_none());
    assert!(schema.operand_type_at(usize::MAX).is_none());
}

#[test]
fn variadic_tail_checks_every_absolute_type_and_undefined_operand() {
    let registry = DialectSchemaRegistry::new([declaration(vec![
        Ty::U64.into(),
        OperandType::VariadicExact(value_ty()),
    ])])
    .unwrap();
    let prefix = Ty::U64;
    let tail = value_ty();
    let wrong = Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 2)));
    for index in [1, 4, 8] {
        assert_eq!(
            registry
                .validate_op(&operation(9), 1, |id| {
                    Some(if id.index() == 0 {
                        &prefix
                    } else if id.index() == index {
                        &wrong
                    } else {
                        &tail
                    })
                })
                .unwrap_err(),
            SchemaError::OperandType {
                index: index as usize,
                expected: tail.clone(),
                actual: wrong.clone(),
            }
        );
        assert_eq!(
            registry
                .validate_op(&operation(9), 1, |id| {
                    (id.index() != index).then_some(if id.index() == 0 { &prefix } else { &tail })
                })
                .unwrap_err(),
            SchemaError::UndefinedOperand(ValueId::new(index))
        );
    }
    assert_eq!(
        registry
            .validate_op(&operation(1), 1, |_| Some(&tail))
            .unwrap_err(),
        SchemaError::OperandType {
            index: 0,
            expected: prefix,
            actual: tail,
        }
    );
}

#[test]
fn variadic_registration_rejects_ambiguous_layouts() {
    let tail = OperandType::VariadicExact(value_ty());
    for (operands, expected) in [
        (
            vec![tail.clone(), Ty::Bool.into()],
            SchemaError::NonTerminalVariadicOperand { index: 0 },
        ),
        (
            vec![Ty::U64.into(), tail.clone(), Ty::Bool.into()],
            SchemaError::NonTerminalVariadicOperand { index: 1 },
        ),
        (
            vec![tail.clone(), tail.clone()],
            SchemaError::RepeatedVariadicOperand {
                first: 0,
                repeated: 1,
            },
        ),
        (
            vec![tail.clone(), Ty::Bool.into(), tail],
            SchemaError::RepeatedVariadicOperand {
                first: 0,
                repeated: 2,
            },
        ),
    ] {
        assert_eq!(
            DialectSchemaRegistry::new([declaration(operands)]).unwrap_err(),
            expected
        );
    }
}

#[test]
fn variadic_empty_tail_still_requires_a_closed_nominal_element_type() {
    for ty in [
        Ty::Func(FuncTyId::new(0)),
        Ty::Struct(crate::StructId::new(0)),
        Ty::Tuple(vec![Ty::Func(FuncTyId::new(0))]),
        Ty::Dialect(Box::new(crate::DialectTy::new("invalid.name", "value", 1))),
    ] {
        assert_eq!(
            DialectSchemaRegistry::new([declaration(vec![
                OperandType::VariadicExact(ty.clone(),)
            ])])
            .unwrap_err(),
            SchemaError::NonClosedType(ty)
        );
    }
}

#[test]
fn variadic_value_tail_does_not_weaken_fixed_callback_signatures() {
    let registry = DialectSchemaRegistry::new([declaration(vec![
        OperandType::Function {
            params: vec![value_ty()],
            returns: vec![Ty::Bool],
        },
        OperandType::VariadicExact(value_ty()),
    ])])
    .unwrap();
    let callback = Ty::Func(FuncTyId::new(7));
    let value = value_ty();
    let signature = FuncTy {
        params: vec![value_ty()],
        returns: vec![Ty::Bool],
        abi: None,
        is_vararg: false,
    };
    for count in [1, 4] {
        let operation = operation(count);
        let lookup = |id: ValueId| Some(if id.index() == 0 { &callback } else { &value });
        assert!(
            registry
                .validate_op_with_func_types(&operation, 1, lookup, |_| Some(&signature))
                .is_ok()
        );
        assert!(matches!(
            registry.validate_op(&operation, 1, lookup),
            Err(SchemaError::FunctionTypeUnavailable { index: 0, .. })
        ));
        let mut wrong = signature.clone();
        wrong.is_vararg = true;
        assert!(matches!(
            registry.validate_op_with_func_types(&operation, 1, lookup, |_| Some(&wrong)),
            Err(SchemaError::FunctionSignature { index: 0, .. })
        ));
    }
}

#[test]
fn variadic_arity_does_not_relax_result_or_attribute_checks() {
    let mut declared = declaration(vec![OperandType::VariadicExact(value_ty())]);
    declared.operations[0].attributes.push(AttributeSchema {
        name: "site".into(),
        kind: AttributeKind::U64,
    });
    let registry = DialectSchemaRegistry::new([declared]).unwrap();
    let op = operation(0).with_attr("site", AttrValue::U64(7));
    assert!(registry.validate_op(&op, 1, |_| None).is_ok());
    let mut bad = op.clone();
    bad.result_tys.clear();
    assert_eq!(
        registry.validate_op(&bad, 1, |_| None),
        Err(SchemaError::ResultTypes)
    );
    assert_eq!(
        registry.validate_op(&op, 0, |_| None),
        Err(SchemaError::ResultCount {
            expected: 1,
            actual: 0
        })
    );
    bad = op.clone();
    bad.attrs.clear();
    assert_eq!(
        registry.validate_op(&bad, 1, |_| None),
        Err(SchemaError::MissingAttribute("site".into()))
    );
    bad = op.with_attr("site", AttrValue::U64(8));
    assert_eq!(
        registry.validate_op(&bad, 1, |_| None),
        Err(SchemaError::DuplicateAttribute("site".into()))
    );
}
