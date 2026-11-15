// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Checked operational terms over hand-authored SSA modules, not source
//! correspondence, native execution, catalog authentication or provider proof.

use crate::spec::Specification;
use clean_elab::ElabCtx;
use clean_kernel::{Expr, Level, Name, TypeChecker, TypeError};
use std::sync::OnceLock;

const ROOTS: &[&str] = &[
    "ir_byte_gep_index_limit_v1",
    "ir_byte_gep_typed_index_v1",
    "ir_byte_gep_typed_indices_v1",
    "ir_byte_gep_typed_v1",
    "ir_byte_gep_site_v1",
    "ir_byte_gep_site_mk_legacy_v1",
    "ir_byte_gep_site_mkt_legacy_v1",
    "ir_byte_gep_site_mki_selected_v1",
];
const NONE: &str = "IROption.none Nat";
const PARAMS: &str =
    "(providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat)";
const MEMORY_PARAMS: &str = "(bytes : Nat -> IROption Nat)";
const EMPTY: &str = "(IRList.nil Nat)";
const RESULTS: &str = "(IRList.cons Nat 99 (IRList.nil Nat))";
const PTR_RESULTS: &str = "(IRList.cons IRTy IRTy.ptr_ (IRList.nil IRTy))";
const TAIL: &str = "(IRList.cons IRFrame (IRFrame.mk 3 4 5 (IRList.nil IRBinding)
  (IRList.cons Nat 123 (IRList.nil Nat))) (IRList.nil IRFrame))";
const ALLOCS: &str = "(IRList.cons IRByteAllocationV1
  (IRByteAllocationV1.mk 16 64 1 Bool.true) (IRList.nil IRByteAllocationV1))";
const MEMORY: &str = "(IRByteMemoryV1.mk typed_gep_allocs bytes 128)";
const WORLD: &str = "(IRByteWorldV1.mk Nat (IRByteMemoryV1.mk typed_gep_allocs bytes 128)
  host (IRList.cons Nat 2 (IRList.cons Nat 1 (IRList.nil Nat))) 3)";

fn checked(spec: &Specification, name: &str) {
    let def = spec.get_definition(name).expect("actual registered value");
    assert!(!def.is_axiom && def.elaborated_value.is_some());
    spec.verify_definition(name).expect("stored kernel check");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Typed GEP operational witness")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn specification() -> Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("actual public default ByteV1 vocabulary");
        add(
            &mut spec,
            &format!("def typed_gep_allocs : IRList IRByteAllocationV1 := {ALLOCS}"),
        );
        spec
    })
    .clone()
}

fn elaborate(spec: &Specification, source: &str) -> Expr {
    let surface = clean_parser::parse_expr(source).expect("independent endpoint parses");
    let mut ctx = ElabCtx::new(spec.env());
    let term = ctx
        .elaborate(&surface)
        .expect("independent endpoint elaborates");
    let term = ctx.metas().instantiate(&term);
    let term = ctx.metas().instantiate_levels(&term);
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!term.has_expr_mvar_quick() && !term.has_level_mvar_quick());
    term
}

fn replay(
    spec: &Specification,
    params: &str,
    ty: &str,
    actual: &str,
    expected: &str,
    accepts: bool,
) {
    let eq = format!("Eq ({ty}) ({actual}) ({expected})");
    let refl = format!("Eq.refl ({ty}) ({expected})");
    let (claim, proof) = if params.is_empty() {
        (eq, refl)
    } else {
        (
            format!("forall {params}, {eq}"),
            format!("fun {params} => {refl}"),
        )
    };
    let claim = elaborate(spec, &claim);
    let proof = elaborate(spec, &proof);
    let mut tc = TypeChecker::new(spec.env());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    assert_eq!(
        tc.heartbeat_limit(),
        clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT
    );
    assert_eq!(tc.heartbeat_limit(), 2_000_000);
    tc.check_type(&claim, &Expr::sort(Level::zero()))
        .expect("independent proposition");
    let result = tc.check_type(&proof, &claim);
    assert!(!tc.heartbeat_spent(), "not a resource verdict: {result:?}");
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    if accepts {
        result.expect("strict independent endpoint replay");
        let audit = spec.env().audit_certification(&claim, &proof);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        assert!(
            matches!(result, Err(TypeError::TypeMismatch { .. })),
            "{result:?}"
        );
    }
}

fn equal(
    spec: &mut Specification,
    name: &str,
    params: &str,
    ty: &str,
    actual: &str,
    expected: &str,
) {
    replay(spec, params, ty, actual, expected, true);
    add(spec, &format!("def {name} {params} : Eq ({ty}) ({actual}) ({expected}) := Eq.refl ({ty}) ({expected})"));
}

fn list(ty: &str, values: &[String]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("(IRList.nil {ty})"), |tail, value| {
            format!("(IRList.cons {ty} ({value}) {tail})")
        })
}

fn ids(values: &[u64]) -> String {
    list(
        "Nat",
        &values.iter().map(u64::to_string).collect::<Vec<_>>(),
    )
}

fn rows(values: &[(u64, &str)]) -> String {
    list(
        "IRByteOperandV1",
        &values
            .iter()
            .map(|(id, ty)| format!("IRByteOperandV1.mk {id} ({ty})"))
            .collect::<Vec<_>>(),
    )
}

fn frame(left: &str, right: &str, base: &str) -> String {
    let locals = list(
        "IRBinding",
        &[
            format!("IRBinding.mk 40 ({base})"),
            format!("IRBinding.mk 78 ({left})"),
            format!("IRBinding.mk 79 ({right})"),
            "IRBinding.mk 88 (IRScalar.bool_ Bool.true)".into(),
        ],
    );
    format!("(IRFrame.mk 9 7 1 {locals} (IRList.cons Nat 77 {EMPTY}))")
}

fn machine(frame: &str) -> String {
    format!("(IRMachine.mk (IRList.cons IRFrame {frame} {TAIL}) (IRList.nil IRMemSlot) 91)")
}

fn site(constructor: &str, operands: &str, result_types: &str) -> String {
    let extension = if constructor == "mk" {
        String::new()
    } else {
        format!(" {operands}")
    };
    format!("(IRByteSiteV1.{constructor} 9 7 1 0 1 {result_types}{extension})")
}

fn context(site: &str, indices: &[u64], inbounds: bool, stride: u64) -> String {
    let instruction = format!(
        "IRInst.gep (IRTy.int_ 64) 40 {} Bool.{}",
        ids(indices),
        if inbounds { "true" } else { "false" }
    );
    let nodes = list(
        "IRNode",
        &[
            format!("IRNode.mk IRInst.unreachable {EMPTY}"),
            format!("IRNode.mk ({instruction}) {RESULTS}"),
            format!("IRNode.mk (IRInst.ret {RESULTS}) {EMPTY}"),
        ],
    );
    format!("(IRByteContextV1.mk
  (IRModule.mk (IRList.cons IRFunc (IRFunc.mk 9 {} 7
    (IRList.cons IRBlock (IRBlock.mk 7 {EMPTY} {nodes}) (IRList.nil IRBlock))) (IRList.nil IRFunc)) (IRList.nil IRGlobal))
  (IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.int_ 64) {stride} 8 (IRList.nil IRTy) {EMPTY}) (IRList.nil IRByteLayoutV1))
  (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1)
  (IRList.cons IRByteSiteV1 {site} (IRList.nil IRByteSiteV1)))", ids(&[40, 78, 79]))
}

fn run(ctx: &str, current: &str) -> String {
    format!(
        "ir_byte_step_v1 Nat {ctx} providers (IRByteConfigV1.running Nat {} {WORLD})",
        machine(current)
    )
}

fn running(current: &str, address: u64) -> String {
    let next = format!(
        "(ir_frame_advance (ir_frame_set_many {current} {RESULTS}
      (IRList.cons IRScalar (IRScalar.ptr_ {address}) (IRList.nil IRScalar))))"
    );
    format!("IRByteConfigV1.running Nat {} {WORLD}", machine(&next))
}

fn halted(outcome: &str) -> String {
    format!("IRByteConfigV1.halted Nat ({outcome}) {WORLD}")
}

#[test]
fn byte_typed_gep_public_roots_and_legacy_equations_are_checked_without_axioms() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
        let operands = rows(&[(78, "IRTy.int_ 32"), (79, "IRTy.uint_ 16")]);
        let current = frame("IRScalar.int_ 3", "IRScalar.int_ 2", "IRScalar.ptr_ 16");
        let s = machine(&current);
        let indices = ids(&[78, 79]);
        let typed = site("mki", &operands, PTR_RESULTS);
        let ctx = context(&typed, &[78, 79], true, 8);
        let params = MEMORY_PARAMS;
        let actual = format!(
            "ir_byte_gep_site_v1 {ctx} {typed} (IRTy.int_ 64) {s} 40 {indices} Bool.true {MEMORY}"
        );
        let expected = format!("ir_byte_gep_typed_v1 {ctx} (IRTy.int_ 64) (ir_getd {s} 40) (IROption.some Nat 5) Bool.true {MEMORY}");
        add(&mut spec, &format!("def typed_gep_selected_law {params} : Eq IRByteMemoryResultV1 ({actual}) ({expected}) :=
  ir_byte_gep_site_mki_selected_v1 {ctx} 9 7 1 0 1 {PTR_RESULTS} {operands} (IRTy.int_ 64) {s} 40 {indices} Bool.true {MEMORY} 5
    (Eq.refl (IROption Nat) (IROption.some Nat 5))"));
        for constructor in ["mk", "mkt"] {
            let old = site(constructor, &operands, PTR_RESULTS);
            let actual = format!("ir_byte_gep_site_v1 {ctx} {old} (IRTy.int_ 64) {s} 40 {indices} Bool.true {MEMORY}");
            let expected = format!("ir_byte_gep_v1 {ctx} (IRTy.int_ 64) (ir_getd {s} 40) (ir_resolve {s} {indices}) Bool.true {MEMORY}");
            equal(
                &mut spec,
                &format!("typed_gep_legacy_{constructor}"),
                params,
                "IRByteMemoryResultV1",
                &actual,
                &expected,
            );
        }
    });
}

#[test]
fn byte_typed_gep_nominal_widths_signed_halves_and_unsigned_ranges_are_exact() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (signed, family) in [(true, "int_"), (false, "uint_")] {
            for width in [8, 16, 32, 64] {
                let limit = 1_u128
                    << if signed || width == 64 {
                        width - 1
                    } else {
                        width
                    };
                for (case, value) in [0, limit - 1, limit, (1_u128 << width) - 1, 1_u128 << width]
                    .into_iter()
                    .enumerate()
                {
                    let actual = format!("ir_byte_gep_typed_index_v1 (IRTy.{family} {width}) (IRScalar.int_ {value})");
                    let expected = if value < limit {
                        format!("IROption.some Nat {value}")
                    } else {
                        NONE.into()
                    };
                    equal(
                        &mut spec,
                        &format!("typed_gep_{family}_{width}_{case}"),
                        "",
                        "IROption Nat",
                        &actual,
                        &expected,
                    );
                }
            }
        }
        replay(
            &spec,
            "",
            "IROption Nat",
            "ir_byte_gep_typed_index_v1 (IRTy.int_ 32) (IRScalar.int_ 4294967295)",
            "IROption.some Nat 4294967295",
            false,
        );
    });
}

#[test]
fn byte_typed_gep_wrong_types_and_noninteger_carriers_never_infer_nominal_types() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (case, ty) in [
            "IRTy.bool_",
            "IRTy.ptr_",
            "IRTy.usize_ 64",
            "IRTy.int_ 0",
            "IRTy.uint_ 7",
            "IRTy.int_ 128",
            "IRTy.uint_ 128",
            "IRTy.ref_ (IRTy.int_ 8)",
            "IRTy.float_ 64",
        ]
        .into_iter()
        .enumerate()
        {
            equal(
                &mut spec,
                &format!("typed_gep_wrong_ty_{case}"),
                "",
                "IROption Nat",
                &format!("ir_byte_gep_typed_index_v1 ({ty}) (IRScalar.int_ 1)"),
                NONE,
            );
        }
        for (case, value) in [
            "IRScalar.bool_ Bool.true",
            "IRScalar.ptr_ 1",
            "IRScalar.nullptr_",
            "IRScalar.undef_",
            "IRScalar.float_ 1",
            "IRScalar.fat_ 1 2",
            "IRScalar.fnptr_ 0",
            "IRScalar.unit_",
        ]
        .into_iter()
        .enumerate()
        {
            equal(
                &mut spec,
                &format!("typed_gep_wrong_carrier_{case}"),
                "",
                "IROption Nat",
                &format!("ir_byte_gep_typed_index_v1 (IRTy.uint_ 32) ({value})"),
                NONE,
            );
        }
        equal(
            &mut spec,
            "typed_gep_unsigned_upper",
            "",
            "IROption Nat",
            "ir_byte_gep_typed_index_v1 (IRTy.uint_ 32) (IRScalar.int_ 2147483648)",
            "IROption.some Nat 2147483648",
        );
        replay(
            &spec,
            "",
            "IROption Nat",
            "ir_byte_gep_typed_index_v1 (IRTy.int_ 8) (IRScalar.int_ 256)",
            "IROption.some Nat 0",
            false,
        );
    });
}

#[test]
fn byte_typed_gep_catalog_uniqueness_missing_values_repeats_and_sum_overflow_are_checked() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let s = machine(&frame(
            "IRScalar.int_ 3",
            "IRScalar.int_ 2",
            "IRScalar.ptr_ 16",
        ));
        let valid = rows(&[(78, "IRTy.int_ 32"), (79, "IRTy.uint_ 16")]);
        for (case, operands, indices, expected) in [
            ("sum", valid.clone(), ids(&[78, 79]), "IROption.some Nat 5"),
            (
                "repeated",
                valid.clone(),
                ids(&[78, 78, 79]),
                "IROption.some Nat 8",
            ),
            ("empty", rows(&[]), ids(&[]), "IROption.some Nat 0"),
            (
                "missing_row",
                rows(&[(78, "IRTy.int_ 32")]),
                ids(&[78, 79]),
                NONE,
            ),
            (
                "missing_local",
                rows(&[(80, "IRTy.int_ 32")]),
                ids(&[80]),
                NONE,
            ),
            (
                "duplicates",
                rows(&[(78, "IRTy.int_ 32"), (78, "IRTy.int_ 32")]),
                ids(&[78]),
                NONE,
            ),
            (
                "conflict",
                rows(&[(78, "IRTy.int_ 32"), (78, "IRTy.uint_ 32")]),
                ids(&[78]),
                NONE,
            ),
            (
                "unused_duplicate",
                rows(&[(80, "IRTy.int_ 32"), (80, "IRTy.int_ 32")]),
                ids(&[]),
                NONE,
            ),
        ] {
            equal(
                &mut spec,
                &format!("typed_gep_catalog_{case}"),
                "",
                "IROption Nat",
                &format!("ir_byte_gep_typed_indices_v1 {operands} {s} {indices}"),
                expected,
            );
        }
        let big = machine(&frame(
            "IRScalar.int_ 9223372036854775807",
            "IRScalar.int_ 2",
            "IRScalar.ptr_ 16",
        ));
        let operands = rows(&[(78, "IRTy.uint_ 64")]);
        equal(
            &mut spec,
            "typed_gep_sum_boundary",
            "",
            "IROption Nat",
            &format!(
                "ir_byte_gep_typed_indices_v1 {operands} {big} {}",
                ids(&[78, 78])
            ),
            "IROption.some Nat 18446744073709551614",
        );
        equal(
            &mut spec,
            "typed_gep_sum_overflow",
            "",
            "IROption Nat",
            &format!(
                "ir_byte_gep_typed_indices_v1 {operands} {big} {}",
                ids(&[78, 78, 78])
            ),
            NONE,
        );
        replay(
            &spec,
            "",
            "IROption Nat",
            &format!(
                "ir_byte_gep_typed_indices_v1 {valid} {s} {}",
                ids(&[78, 78])
            ),
            "IROption.some Nat 3",
            false,
        );
    });
}

#[test]
fn byte_typed_gep_layout_stride_address_and_inbounds_keep_complete_memory() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let typed = site("mki", &rows(&[(78, "IRTy.int_ 32")]), PTR_RESULTS);
        for (case, stride, base, index, inbounds, expected) in [
            (
                "stride",
                8,
                "IRScalar.ptr_ 16",
                "IROption.some Nat 5",
                "Bool.true",
                "IRByteMemoryResultV1.value (IRScalar.ptr_ 56)",
            ),
            (
                "flat_other_stride",
                3,
                "IRScalar.ptr_ 16",
                "IROption.some Nat 5",
                "Bool.true",
                "IRByteMemoryResultV1.value (IRScalar.ptr_ 31)",
            ),
            (
                "one_past",
                8,
                "IRScalar.ptr_ 16",
                "IROption.some Nat 8",
                "Bool.true",
                "IRByteMemoryResultV1.value (IRScalar.ptr_ 80)",
            ),
            (
                "outside",
                8,
                "IRScalar.ptr_ 16",
                "IROption.some Nat 9",
                "Bool.true",
                "IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr)",
            ),
            (
                "unconfined",
                8,
                "IRScalar.ptr_ 16",
                "IROption.some Nat 9",
                "Bool.false",
                "IRByteMemoryResultV1.value (IRScalar.ptr_ 88)",
            ),
            (
                "not_ptr",
                8,
                "IRScalar.int_ 16",
                "IROption.some Nat 1",
                "Bool.false",
                "IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.not_ptr)",
            ),
            (
                "null",
                8,
                "IRScalar.nullptr_",
                "IROption.some Nat 0",
                "Bool.false",
                "IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr)",
            ),
            (
                "stride_overflow",
                8,
                "IRScalar.ptr_ 16",
                "IROption.some Nat 2305843009213693952",
                "Bool.false",
                "IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr)",
            ),
            (
                "address_overflow",
                1,
                "IRScalar.ptr_ 18446744073709551615",
                "IROption.some Nat 1",
                "Bool.false",
                "IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr)",
            ),
            (
                "zero_layout",
                0,
                "IRScalar.bool_ Bool.true",
                NONE,
                "Bool.false",
                "IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded)",
            ),
            (
                "index_before_pointer",
                8,
                "IRScalar.bool_ Bool.true",
                NONE,
                "Bool.false",
                "IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded)",
            ),
        ] {
            let pointee = if stride == 3 {
                "(IRTy.array_ (IRTy.uint_ 8) 3)"
            } else {
                "(IRTy.int_ 64)"
            };
            let ctx = context(&typed, &[78], false, stride).replace("(IRTy.int_ 64)", pointee);
            let actual = format!(
                "ir_byte_gep_typed_v1 {ctx} {pointee} ({base}) ({index}) {inbounds} {MEMORY}"
            );
            equal(
                &mut spec,
                &format!("typed_gep_address_{case}"),
                MEMORY_PARAMS,
                "IRByteMemoryResultV1",
                &actual,
                &format!("{expected} {MEMORY}"),
            );
        }
        let ctx = context(&typed, &[78], false, 8);
        equal(&mut spec, "typed_gep_missing_layout", MEMORY_PARAMS, "IRByteMemoryResultV1", &format!("ir_byte_gep_typed_v1 {ctx} (IRTy.int_ 16) (IRScalar.ptr_ 16) (IROption.some Nat 1) Bool.false {MEMORY}"), &format!("IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) {MEMORY}"));
    });
}

#[test]
fn byte_typed_gep_actual_fetched_step_uses_original_ids_and_preserves_whole_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let operands = rows(&[(78, "IRTy.int_ 32"), (79, "IRTy.uint_ 16")]);
        let current = frame("IRScalar.int_ 3", "IRScalar.int_ 2", "IRScalar.ptr_ 16");
        for (case, indices, address) in
            [("flat", vec![78, 79], 56), ("repeat", vec![78, 78, 79], 80)]
        {
            let typed = site("mki", &operands, PTR_RESULTS);
            let ctx = context(&typed, &indices, true, 8);
            let actual = run(&ctx, &current);
            let expected = running(&current, address);
            equal(
                &mut spec,
                &format!("typed_gep_fetched_{case}"),
                PARAMS,
                "IRByteConfigV1 Nat",
                &actual,
                &expected,
            );
            replay(
                &spec,
                PARAMS,
                "IRByteConfigV1 Nat",
                &actual,
                &running(&current, address + 1),
                false,
            );
            replay(
                &spec,
                PARAMS,
                "IRByteConfigV1 Nat",
                &actual,
                &expected.replace("host", "(Nat.succ host)"),
                false,
            );
            replay(
                &spec,
                PARAMS,
                "IRByteConfigV1 Nat",
                &actual,
                &expected.replace("bytes", "(ir_byte_write_word_v1 bytes 112 1 7)"),
                false,
            );
        }
    });
}

#[test]
fn byte_typed_gep_fetched_faults_retain_world_and_cannot_rebind_a_wrong_lane() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let current = frame("IRScalar.int_ 3", "IRScalar.int_ 2", "IRScalar.ptr_ 16");
        for (case, operands, result_types, indices, outcome) in [
            (
                "missing",
                rows(&[(78, "IRTy.int_ 32")]),
                PTR_RESULTS,
                vec![78, 79],
                "IROutcome.unmodelled IRFault.width_bounded",
            ),
            (
                "duplicate",
                rows(&[(78, "IRTy.int_ 32"), (78, "IRTy.uint_ 32")]),
                PTR_RESULTS,
                vec![78],
                "IROutcome.unmodelled IRFault.width_bounded",
            ),
            (
                "nominal_bool",
                rows(&[(78, "IRTy.bool_")]),
                PTR_RESULTS,
                vec![78],
                "IROutcome.unmodelled IRFault.width_bounded",
            ),
            (
                "result_lane",
                rows(&[(78, "IRTy.int_ 32")]),
                "(IRList.cons IRTy (IRTy.uint_ 64) (IRList.nil IRTy))",
                vec![78],
                "IROutcome.type_error IRFault.bad_field",
            ),
            (
                "inbounds",
                rows(&[(78, "IRTy.int_ 32"), (79, "IRTy.uint_ 16")]),
                PTR_RESULTS,
                vec![78, 78, 78],
                "IROutcome.ub IRFault.bad_addr",
            ),
        ] {
            let typed = site("mki", &operands, result_types);
            let actual = run(&context(&typed, &indices, true, 8), &current);
            equal(
                &mut spec,
                &format!("typed_gep_fetched_fault_{case}"),
                PARAMS,
                "IRByteConfigV1 Nat",
                &actual,
                &halted(outcome),
            );
            replay(
                &spec,
                PARAMS,
                "IRByteConfigV1 Nat",
                &actual,
                &running(&current, 40),
                false,
            );
        }
    });
}

#[test]
fn byte_typed_gep_opt_in_signed_rejection_does_not_reinterpret_old_site_metadata() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let operands = rows(&[(78, "IRTy.int_ 32")]);
        let negative = frame(
            "IRScalar.int_ 4294967295",
            "IRScalar.int_ 0",
            "IRScalar.ptr_ 16",
        );
        let typed = site("mki", &operands, PTR_RESULTS);
        let actual = run(&context(&typed, &[78], false, 8), &negative);
        equal(
            &mut spec,
            "typed_gep_narrow_negative",
            PARAMS,
            "IRByteConfigV1 Nat",
            &actual,
            &halted("IROutcome.unmodelled IRFault.width_bounded"),
        );
        for constructor in ["mk", "mkt"] {
            // Old sites deliberately do not authenticate nominal I32 metadata.
            // Their unchanged erased scalar rule still accepts this Nat word.
            let old = site(constructor, &operands, PTR_RESULTS);
            equal(
                &mut spec,
                &format!("typed_gep_old_{constructor}_unchanged"),
                PARAMS,
                "IRByteConfigV1 Nat",
                &run(&context(&old, &[78], false, 8), &negative),
                &running(&negative, 34_359_738_376),
            );
        }
        for family in ["int_", "uint_"] {
            let current = frame(
                "IRScalar.int_ 9223372036854775808",
                "IRScalar.int_ 0",
                "IRScalar.ptr_ 16",
            );
            let operands = rows(&[(78, &format!("IRTy.{family} 64"))]);
            for constructor in ["mki", "mkt", "mk"] {
                let site = site(constructor, &operands, PTR_RESULTS);
                equal(
                    &mut spec,
                    &format!("typed_gep_high64_{family}_{constructor}"),
                    PARAMS,
                    "IRByteConfigV1 Nat",
                    &run(&context(&site, &[78], false, 8), &current),
                    &halted("IROutcome.unmodelled IRFault.width_bounded"),
                );
            }
        }
    });
}
