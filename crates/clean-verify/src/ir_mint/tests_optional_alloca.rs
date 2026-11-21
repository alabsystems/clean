// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual optional-operand producer, checked-source consumer and refusal controls.
//! These do not construct an alternate model or qualify a complete EvalIR world.

use super::Decoder;
use crate::ir_mint::{core, mint, project, read_emitted_with_self, SelfFunc, Sx, Tags};
use crate::spec::Specification;
use crate::spec_axiom_closure::computed_axiom_closure;
use clean_kernel::{ConstantKind, DeclarationVerification, Expr, ExprKind, Name, TypeChecker};
use std::collections::{BTreeMap, BTreeSet};

fn fixture(some: bool) -> (Sx, Tags, Sx) {
    let count = if some { ", %0" } else { "" };
    let text = format!(
        "rustcc fn @opt_count(functy.0) {{\nbb0(%0: u64):\n  %1 = alloca u8{count}\n  ret\n}}\n"
    );
    let (read, observed) = read_emitted_with_self(&text, SelfFunc::Pinned(0))
        .expect("the real ReaderB optional-count form must read");
    let tags = Tags {
        body: "opt_count".to_string(),
        funcs: BTreeMap::from([(0, (0, "opt_count".to_string()))]),
        interface: observed.interface,
        ..Tags::default()
    };
    let projected = project(&text, &tags).expect("the actual interface must match its pin");
    assert_eq!(projected.core, read, "project must retain ReaderB's core");
    let mut allocas = Vec::new();
    core::for_each_inst(&read, |_, _, instruction| {
        if instruction.tagged("alloca").is_ok() {
            allocas.push(instruction.clone());
        }
        Ok(())
    })
    .expect("actual projected instruction walk");
    assert_eq!(allocas.len(), 1, "one actual alloca, never an empty probe");
    let allocation = allocas.pop().expect("the asserted one instruction");
    let fields = allocation.tagged("alloca").expect("typed alloca form");
    assert_eq!(fields.len(), 2, "type and optional operand only");
    assert_eq!(
        fields[1],
        if some {
            Sx::tag("some", vec![Sx::a("0")])
        } else {
            Sx::tag("none", vec![])
        }
    );
    (read, tags, allocation)
}

fn checked_value(spec: &Specification, text: &str) -> Expr {
    let name = Name::from_string(text);
    let record = spec
        .get_definition(text)
        .expect("actual stored source definition");
    let kernel = spec
        .env()
        .get_const(&name)
        .expect("actual live kernel declaration");
    assert_eq!(record.name, text);
    assert!(!record.is_axiom);
    assert_ne!(kernel.kind, ConstantKind::Axiom);
    let ty = record
        .elaborated_type
        .as_ref()
        .expect("stored elaborated type");
    let value = record
        .elaborated_value
        .as_ref()
        .expect("stored elaborated value");
    assert_eq!(&kernel.type_, ty);
    assert_eq!(kernel.value.as_ref(), Some(value));
    assert_eq!(
        spec.env().declaration_verification(&name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    assert!(!value.collect_constants().contains(&name));
    for expression in [ty, value] {
        assert!(!expression.has_fvar_quick());
        assert!(!expression.has_loose_bvars());
        assert!(!expression.has_expr_mvar_quick());
        assert!(!expression.has_level_mvar_quick());
    }
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker
        .infer_type_full(ty)
        .expect("the actual declared type fully checks");
    assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
    checker
        .check_type(value, ty)
        .expect("public full value check");
    assert!(!checker.heartbeat_spent());
    let domain = spec.env().axiom_deps(&name).expect("actual domain closure");
    let foundational = spec
        .env()
        .foundational_axiom_deps(&name)
        .expect("actual foundation closure");
    let computed = computed_axiom_closure(spec, text);
    let rendered: BTreeSet<_> = domain.iter().map(Name::to_unambiguous_string).collect();
    assert_eq!(computed, rendered);
    assert!(domain.is_empty() && foundational.is_empty() && computed.is_empty());
    value.clone()
}

fn checked_round_trip(some: bool) {
    let (core, tags, allocation) = fixture(some);
    let script = mint(&core, "ir_optional_count_probe", &tags).expect("real public mint caller");
    let args = allocation
        .tagged("alloca")
        .expect("actual allocation fields");
    let ty = mint::arg(crate::ir_mint::shape::Arg::Ty, &args[0], &tags)
        .expect("the same production type renderer");
    let count = mint::arg(crate::ir_mint::shape::Arg::OptVal, &args[1], &tags)
        .expect("the same production optional renderer");
    assert!(script
        .text()
        .contains(&format!("(IRInst.alloca {ty} {count})")));
    // The actual production syntax owner supplies IRInst/IROption. No source
    // seed, fake axiom, replacement family or partial-Full shortcut is used.
    let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
        .expect("the actual checked syntax owner must initialize before this probe");
    let source = format!(
        "def optional_count_probe (ir_d0 : Nat) (ir_d8 : Nat) : IRInst := IRInst.alloca {ty} {count}"
    );
    spec.add_recursive_def(&source, "actual optional count checked-source probe")
        .expect("the real rendered operand must type-check in its actual constructor field");
    let value = checked_value(&spec, "optional_count_probe");
    let applied = Expr::apps(value, [Expr::nat_lit(0), Expr::nat_lit(8)]);
    let ir_inst = Expr::const_(Name::from_string("IRInst"), vec![]);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    checker
        .check_type(&applied, &ir_inst)
        .expect("full applied data check");
    assert!(!checker.heartbeat_spent());
    let decoder = Decoder {
        env: spec.env(),
        tags: &tags,
    };
    assert_eq!(
        decoder
            .inst(&applied)
            .expect("actual ReaderC instruction decoder"),
        allocation
    );
}

#[test]
fn none_checks_through_actual_source_owner_and_reader_c() {
    checked_round_trip(false);
}

#[test]
fn some_checks_through_actual_source_owner_and_reader_c() {
    checked_round_trip(true);
}

#[test]
fn wrong_option_carrier_refuses_after_valid_source_setup() {
    let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
        .expect("successful actual syntax-owner setup is mandatory");
    spec.add_recursive_def(
        "def optional_good (ty : IRTy) : IRInst := IRInst.alloca ty (@IROption.some Nat 0)",
        "actual valid allocation field companion",
    )
    .expect("the actual constructor must accept the valid Nat option first");
    let _ = checked_value(&spec, "optional_good");
    spec.add_recursive_def(
        "def optional_bool : IROption Bool := @IROption.some Bool Bool.true",
        "actual valid Bool option companion",
    )
    .expect("a valid Bool option must be admitted before testing the changed carrier");
    let _ = checked_value(&spec, "optional_bool");
    let error = spec
        .add_recursive_def(
            "def optional_bad (ty : IRTy) : IRInst := IRInst.alloca ty optional_bool",
            "only the allocation field carrier is wrong",
        )
        .expect_err("the actual IROption Nat field must refuse a valid IROption Bool");
    assert!(
        format!("{error}").contains("IROption"),
        "unexpected refusal: {error}"
    );
    assert!(spec
        .env()
        .get_const(&Name::from_string("optional_bad"))
        .is_none());
}

fn malformed_refuses(replacement: Sx) {
    let (core, tags, _) = fixture(true);
    mint(&core, "ir_optional_valid", &tags).expect("successful public-mint setup is mandatory");
    fn replace(sx: &Sx, replacement: &Sx, count: &mut usize) -> Sx {
        match sx {
            Sx::List(items) if items.first().and_then(|x| x.atom().ok()) == Some("alloca") => {
                assert_eq!(items.len(), 3);
                *count += 1;
                Sx::tag("alloca", vec![items[1].clone(), replacement.clone()])
            }
            Sx::List(items) => Sx::List(
                items
                    .iter()
                    .map(|x| replace(x, replacement, count))
                    .collect(),
            ),
            atom => atom.clone(),
        }
    }
    let mut changed = 0;
    let bad = replace(&core, &replacement, &mut changed);
    assert_eq!(changed, 1, "one actual optional field is changed");
    assert_ne!(bad, core);
    let error = mint(&bad, "ir_optional_bad", &tags)
        .expect_err("malformed optional operands must refuse, never panic or discard fields");
    assert!(format!("{error}").contains("some") || format!("{error}").contains("none"));
}

#[test]
fn malformed_none_extra_refuses() {
    malformed_refuses(Sx::tag("none", vec![Sx::a("0")]));
}

#[test]
fn malformed_some_empty_refuses() {
    malformed_refuses(Sx::tag("some", vec![]));
}

#[test]
fn malformed_some_extra_refuses() {
    malformed_refuses(Sx::tag("some", vec![Sx::a("0"), Sx::a("1")]));
}
