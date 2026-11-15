// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Preserve the original full-width truncation Eq and exact fuel goals while
//! discharging arithmetic through checked equalities. The evaluator, kernel,
//! fixture inputs and candidate answers remain the original ones.
//!
//! The arithmetic packages supply their checked sources from a supported
//! ByteV1 owner. Only missing dependencies are re-elaborated in the original
//! EvalIR owner, whose complete model closure remains exact. Numeric
//! answers have no implicit premises, and every stored proof is independently
//! rechecked with its complete authority closure. Wrong values and fuel remain
//! kernel refusals.

use std::collections::BTreeSet;
use std::error::Error;

use clean_kernel::{ConstantKind, Declaration, Expr, ExprKind, Name, TypeChecker};
use clean_verify::ir_semdiff::wide::{wide_args, wide_int, wide_value_obligation, WideEncoding};
use clean_verify::ir_semdiff::{DiffError, RunResult};
use clean_verify::spec::Specification;

use super::wide_chains::WideChain;

const INPUTS: [(u64, u64); 5] = [
    (0, 0),
    (1, 1),
    (4_294_967_295, 4_294_967_295),
    (4_294_967_296, 0),
    (u64::MAX, 4_294_967_295),
];

fn verify(spec: &Specification, root: &str, expected: usize) -> Result<(), Box<dyn Error>> {
    let info = spec
        .env()
        .get_const(&Name::from_string(root))
        .expect("actual stored declaration");
    let definition = spec.get_definition(root).expect("actual stored definition");
    let value = info.value.as_ref().expect("actual checked value");
    assert!(!definition.is_axiom);
    assert_eq!(definition.elaborated_type.as_ref(), Some(&info.type_));
    assert_eq!(definition.elaborated_value.as_ref(), Some(value));
    assert!(!info.type_.has_fvar_quick() && !value.has_fvar_quick());
    assert!(info.level_params.is_empty());
    let mut arity = 0;
    let mut body = &info.type_;
    while let ExprKind::Pi(_, _, result) = body.kind() {
        arity += 1;
        body = result.as_ref();
    }
    assert_eq!(arity, expected, "unexpected implicit premise in {root}");
    assert!(matches!(info.kind, ConstantKind::Definition));
    let declaration = Declaration::Definition {
        name: info.name.clone(),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
        value: value.clone(),
        is_reducible: info.is_reducible,
    };
    spec.verify_definition(root)?;
    spec.env().check_decl_readonly_strict(&declaration)?;
    for closure in [
        spec.env().axiom_deps(&info.name),
        spec.env().trust_marker_deps(&info.name),
    ] {
        assert!(
            closure.expect("actual transitive closure").is_empty(),
            "untrusted premise in {root}"
        );
    }
    let sort = TypeChecker::new(spec.env()).infer_sort(&info.type_)?;
    let term = Expr::const_(info.name.clone(), vec![]);
    let (goal, witness) = if sort.is_zero() {
        (info.type_.clone(), term)
    } else {
        (
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![sort.clone()]),
                [info.type_.clone(), term.clone(), term.clone()],
            ),
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![sort]),
                [info.type_.clone(), term],
            ),
        )
    };
    let audit = spec.env().audit_certification(&goal, &witness);
    assert!(
        audit.is_certified(),
        "rooted audit refused {root}: {:?}",
        audit.issues
    );
    Ok(())
}

fn add(spec: &mut Specification, source: &str, expected: usize) -> Result<(), Box<dyn Error>> {
    let root = source.split_whitespace().nth(1).expect("definition name");
    assert!(
        spec.get_definition(root).is_none(),
        "transport name collision: {root}"
    );
    assert!(spec.env().get_const(&Name::from_string(root)).is_none());
    spec.add_recursive_def(
        source,
        "A3 original evaluator equality via checked arithmetic transport",
    )?;
    verify(spec, root, expected)
}

fn values(n: &str) -> String {
    format!("(IRList.cons IRScalar (IRScalar.int_ {n}) (IRList.nil IRScalar))")
}

fn ret(n: &str) -> String {
    format!("(IROutcome.ret {})", values(n))
}

fn tail(n: u64) -> String {
    format!(
        "{} ir_mem0 ir_d0",
        wide_args(&["IRScalar.undef_".to_owned(), wide_int(n)])
    )
}

fn input(tail: &str) -> u64 {
    INPUTS
        .iter()
        .find_map(|(n, _)| (self::tail(*n) == tail).then_some(*n))
        .unwrap_or_else(|| panic!("truncation transport input inventory changed: {tail}"))
}

fn compare_model(original: &Specification, proof: &Specification) {
    let mut closure = BTreeSet::new();
    for root in [
        "ir_eval",
        "ir_run",
        "ir_wrap",
        "ir_nat_rem",
        "ir_nat_div",
        "ir_nat_pow2",
    ] {
        let info = original
            .env()
            .get_const(&Name::from_string(root))
            .expect("original model root");
        let term = Expr::const_(info.name.clone(), vec![]);
        let sort = TypeChecker::new(original.env())
            .infer_sort(&info.type_)
            .expect("typed model root");
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![sort.clone()]),
            [info.type_.clone(), term.clone(), term.clone()],
        );
        let witness = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![sort]),
            [info.type_.clone(), term],
        );
        let audit = original.env().audit_certification(&goal, &witness);
        assert!(
            audit.is_certified(),
            "original model audit refused {root}: {:?}",
            audit.issues
        );
        closure.extend(audit.dependencies);
    }
    assert!(!closure.is_empty());
    for name in &closure {
        let before = original
            .env()
            .get_const(name)
            .expect("original model closure");
        let after = proof
            .env()
            .get_const(name)
            .unwrap_or_else(|| panic!("model closure missing: {name}"));
        assert_eq!(before.type_, after.type_, "model type changed: {name}");
        assert_eq!(before.value, after.value, "model body changed: {name}");
        assert_eq!(
            before.kind, after.kind,
            "model declaration kind changed: {name}"
        );
        assert_eq!(
            before.level_params, after.level_params,
            "model universes changed: {name}"
        );
        assert_eq!(
            before.is_reducible, after.is_reducible,
            "model reducibility changed: {name}"
        );
    }
    eprintln!(
        "A3 truncation original model closure: {} exact declarations",
        closure.len()
    );
}

fn import_checked_source(
    spec: &mut Specification,
    donor: &Specification,
    name: &Name,
    arithmetic_names: &BTreeSet<Name>,
    visiting: &mut BTreeSet<Name>,
) -> Result<(), Box<dyn Error>> {
    // Existing declarations remain the original model's declarations. Only
    // the arithmetic package owns importable sources. Donor-specific syntax
    // classes (for example OfNat) are not copied: the original elaborator
    // resolves the source, and any actual missing dependency remains a refusal.
    if spec.env().get_const(name).is_some() || !arithmetic_names.contains(name) {
        return Ok(());
    }
    assert!(
        visiting.insert(name.clone()),
        "cyclic arithmetic source: {name}"
    );
    let info = donor
        .env()
        .get_const(name)
        .expect("checked arithmetic source");
    assert!(matches!(info.kind, ConstantKind::Definition));
    let value = info.value.as_ref().unwrap_or_else(|| {
        panic!(
            "arithmetic source has no value: {name}; kind={:?}",
            info.kind
        )
    });
    let mut dependencies: BTreeSet<_> = info.type_.collect_constants().into_iter().collect();
    dependencies.extend(value.collect_constants());
    for dependency in dependencies {
        import_checked_source(spec, donor, &dependency, arithmetic_names, visiting)?;
    }
    let root = name.to_string();
    let source = &donor
        .get_definition(&root)
        .expect("arithmetic source metadata")
        .type_src;
    assert_eq!(source.split_whitespace().nth(1), Some(root.as_str()));
    assert!(
        source.starts_with("def "),
        "unexpected arithmetic source form: {root}"
    );
    let mut arity = 0;
    let mut result = &info.type_;
    while let ExprKind::Pi(_, _, body) = result.kind() {
        arity += 1;
        result = body.as_ref();
    }
    // No cached term or donor declaration is installed: the original owner
    // elaborates this source and its kernel checks the resulting value again.
    add(spec, source, arity)?;
    assert!(visiting.remove(name));
    Ok(())
}

pub(super) fn new_spec() -> Specification {
    build_spec()
        .unwrap_or_else(|error| panic!("checked truncation arithmetic setup failed: {error}"))
}

fn build_spec() -> Result<Specification, Box<dyn Error>> {
    let original = clean_verify::test_utils::build_eval_ir_spec_with_stack();
    let mut donor = clean_verify::eval_ir::build_byte_prelude_spec_v1_with_stack()?;
    let vocabulary_names: BTreeSet<_> = donor.definitions().keys().cloned().collect();
    donor.install_eval_ir_positive_division_laws_v1()?;
    donor.install_eval_ir_total_restoring_division_laws_v1()?;
    let arithmetic_names: BTreeSet<_> = donor
        .definitions()
        .keys()
        .filter(|name| !vocabulary_names.contains(*name))
        .map(|name| Name::from_string(name))
        .collect();
    let mut spec = original.clone();
    import_checked_source(
        &mut spec,
        &donor,
        &Name::from_string("ir_nat_rem_total_agrees_v1"),
        &arithmetic_names,
        &mut BTreeSet::new(),
    )?;
    compare_model(&original, &spec);
    add(
        &mut spec,
        "def a3_trunc_pow2_step (w : Nat) : Eq Nat (ir_nat_pow2 (Nat.succ w)) \
         (Nat.add (ir_nat_pow2 w) (ir_nat_pow2 w)) := \
         Eq.refl Nat (Nat.add (ir_nat_pow2 w) (ir_nat_pow2 w))",
        1,
    )?;
    add(
        &mut spec,
        "def a3_trunc_double_eq (a b : Nat) (h : Eq Nat a b) : \
         Eq Nat (Nat.add a a) (Nat.add b b) := \
         Eq.trans Nat (Nat.add a a) (Nat.add a b) (Nat.add b b) \
          (ir_eq_cong Nat Nat (fun (z : Nat) => Nat.add a z) a b h) \
          (ir_eq_cong Nat Nat (fun (z : Nat) => Nat.add z b) a b h)",
        3,
    )?;
    add(
        &mut spec,
        "def a3_trunc_pow_0 : Eq Nat (ir_nat_pow2 0) 1 := Eq.refl Nat 1",
        0,
    )?;
    for k in 1..=32 {
        let previous = k - 1;
        let value = 1u64 << k;
        let half = value / 2;
        let name = format!("a3_trunc_pow_{k}");
        let source = format!(
            "def {name} : Eq Nat (ir_nat_pow2 {k}) {value} := \
             Eq.trans Nat (ir_nat_pow2 {k}) \
              (Nat.add (ir_nat_pow2 {previous}) (ir_nat_pow2 {previous})) {value} \
              (a3_trunc_pow2_step {previous}) \
              (Eq.trans Nat \
                (Nat.add (ir_nat_pow2 {previous}) (ir_nat_pow2 {previous})) \
                (Nat.add {half} {half}) {value} \
                (a3_trunc_double_eq (ir_nat_pow2 {previous}) {half} a3_trunc_pow_{previous}) \
                (Eq.refl Nat {value}))"
        );
        add(&mut spec, &source, 0)?;
    }
    add(
        &mut spec,
        "def a3_trunc_wrap32 (n : Nat) : \
         Eq Nat (ir_wrap 32 n) (ir_nat_rem_total_v1 n 4294967296) := \
         Eq.trans Nat (ir_wrap 32 n) (ir_nat_rem n 4294967296) \
          (ir_nat_rem_total_v1 n 4294967296) \
          (ir_eq_cong Nat Nat (fun (d : Nat) => ir_nat_rem n d) \
            (ir_nat_pow2 32) 4294967296 a3_trunc_pow_32) \
          (ir_nat_rem_total_agrees_v1 n 4294967296)",
        1,
    )?;
    Ok(spec)
}

pub(super) fn register(spec: &mut Specification, chain: &WideChain) {
    assert_eq!(chain.name, "get_char_val_trunc");
    assert_eq!(chain.clean_module, "ir_gc_module");
    assert_eq!(chain.clean_fid, "ir_d0");
    let actual: BTreeSet<_> = chain
        .inputs
        .iter()
        .map(|row| input(&row.clean_tail))
        .collect();
    let expected: BTreeSet<_> = INPUTS.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        actual.len(),
        chain.inputs.len(),
        "duplicate truncation inputs"
    );
    assert_eq!(
        actual, expected,
        "original truncation input inventory changed"
    );
    let source = format!(
        "def a3_trunc_symbolic (n : Nat) : Eq IROutcome \
         (ir_eval ir_d2 ir_gc_module ir_d0 \
          (IRList.cons IRScalar IRScalar.undef_ {}) ir_mem0 ir_d0) {} \
         := Eq.refl IROutcome {}",
        values("n"),
        ret("(ir_wrap 32 n)"),
        ret("(ir_wrap 32 n)")
    );
    add(spec, &source, 1).expect("original minted evaluator symbolic equality");
    for (i, row) in chain.inputs.iter().enumerate() {
        let n = input(&row.clean_tail);
        let answer = INPUTS
            .iter()
            .find_map(|(value, answer)| (*value == n).then_some(*answer))
            .expect("original input");
        for (kind, value, fuel) in [("wrong_value", answer ^ 1, 2), ("wrong_fuel", answer, 1)] {
            let name = format!("a3_trunc_{kind}_{i}");
            let source = value_obligation(
                &name,
                chain.clean_module,
                chain.clean_fid,
                fuel,
                &row.clean_tail,
                &RunResult::Int(value),
                WideEncoding::Scalar,
            )
            .expect("mapped negative goal");
            let count = spec.definitions().len();
            assert!(
                spec.add_recursive_def(
                    &source,
                    "original Eq negative arithmetic-transport control"
                )
                .is_err(),
                "kernel accepted {kind} for truncation input {n}"
            );
            assert_eq!(spec.definitions().len(), count);
            assert!(spec.get_definition(&name).is_none());
            assert!(spec.env().get_const(&Name::from_string(&name)).is_none());
        }
    }
}

pub(super) fn value_obligation(
    name: &str,
    module: &str,
    fid: &str,
    fuel: u32,
    tail: &str,
    result: &RunResult,
    encoding: WideEncoding,
) -> Result<String, DiffError> {
    assert_eq!(module, "ir_gc_module");
    assert_eq!(fid, "ir_d0");
    assert!(matches!(fuel, 1 | 2));
    assert!(matches!(encoding, WideEncoding::Scalar));
    let original = wide_value_obligation(name, module, fid, fuel, tail, result, encoding)?;
    let (goal, reflexive) = original
        .rsplit_once(" := ")
        .expect("original Eq declaration");
    let rhs = reflexive
        .strip_prefix("Eq.refl IROutcome ")
        .expect("original candidate");
    let n = input(tail);
    let lhs = format!("(ir_eval ir_d{fuel} {module} {fid} {tail})");
    let middle = ret(&format!("(ir_wrap 32 {n})"));
    let fast = format!("(ir_nat_rem_total_v1 {n} 4294967296)");
    let normalized = ret(&fast);
    let body = format!(
        "Eq.trans IROutcome {lhs} {middle} {rhs} (a3_trunc_symbolic {n}) \
         (Eq.trans IROutcome {middle} {normalized} {rhs} \
           (ir_eq_cong Nat IROutcome (fun (z : Nat) => {}) \
             (ir_wrap 32 {n}) {fast} (a3_trunc_wrap32 {n})) \
           (Eq.refl IROutcome {rhs}))",
        ret("z")
    );
    let transported = format!("{goal} := {body}");
    assert_eq!(
        transported.rsplit_once(" := ").map(|(goal, _)| goal),
        Some(goal)
    );
    Ok(transported)
}

pub(super) fn verify_closed(spec: &Specification, name: &str) {
    verify(spec, name, 0)
        .unwrap_or_else(|error| panic!("original numeric Eq audit failed: {error}"));
}
