// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-executed fixtures for the generic byte/Core machine. These tests
//! construct ordinary IR modules and exact typed catalogs by hand; they are
//! not evidence that a TLA+ source program, runtime helper, or native artifact
//! has been proved equivalent. The actual-TY reflection tests own that separate
//! integration boundary.

use crate::spec::Specification;
use clean_kernel::Name;

fn list(ty: &str, values: impl IntoIterator<Item = impl AsRef<str>>) -> String {
    let values: Vec<_> = values.into_iter().collect();
    values
        .iter()
        .rev()
        .fold(format!("IRList.nil {ty}"), |tail, value| {
            format!("IRList.cons {ty} ({}) ({tail})", value.as_ref())
        })
}

fn ids(values: &[u64]) -> String {
    list("Nat", values.iter().map(u64::to_string))
}

fn types(values: &[&str]) -> String {
    list("IRTy", values.iter().copied())
}

fn scalar_values(values: &[&str]) -> String {
    list("IRScalar", values.iter().copied())
}

fn returned(values: &[&str]) -> String {
    format!("IROutcome.ret ({})", scalar_values(values))
}

#[derive(Clone)]
struct Node {
    inst: String,
    results: Vec<u64>,
    types: Vec<&'static str>,
    align: u64,
    cc: u64,
    operands: Option<Vec<(u64, &'static str)>>,
}

impl Node {
    fn new(inst: impl Into<String>, results: &[u64], types: &[&'static str]) -> Self {
        Self {
            inst: inst.into(),
            results: results.to_vec(),
            types: types.to_vec(),
            align: 0,
            cc: 1,
            operands: None,
        }
    }

    fn constant(ty: &'static str, value: &str, result: u64) -> Self {
        Self::new(format!("IRInst.const_ ({ty}) ({value})"), &[result], &[ty])
    }

    fn with_cc(mut self, cc: u64) -> Self {
        self.cc = cc;
        self
    }

    fn with_operands(mut self, operands: &[(u64, &'static str)]) -> Self {
        self.operands = Some(operands.to_vec());
        self
    }

    fn ret(results: &[u64]) -> Self {
        Self::new(format!("IRInst.ret ({})", ids(results)), &[], &[])
    }

    fn ir(&self) -> String {
        format!("IRNode.mk ({}) ({})", self.inst, ids(&self.results))
    }
}

struct Function {
    id: u64,
    signature: u64,
    params: Vec<&'static str>,
    returns: Vec<&'static str>,
    nodes: Vec<Node>,
    imported: bool,
    cc: u64,
}

impl Function {
    fn local(id: u64, params: &[&'static str], returns: &[&'static str], nodes: Vec<Node>) -> Self {
        Self {
            id,
            signature: id,
            params: params.to_vec(),
            returns: returns.to_vec(),
            nodes,
            imported: false,
            cc: 1,
        }
    }

    fn import(id: u64, params: &[&'static str], returns: &[&'static str]) -> Self {
        Self {
            id,
            signature: id,
            params: params.to_vec(),
            returns: returns.to_vec(),
            nodes: vec![],
            imported: true,
            cc: 0,
        }
    }

    fn ir(&self) -> String {
        let params: Vec<u64> = (0..self.params.len() as u64).collect();
        let blocks = if self.imported {
            list("IRBlock", std::iter::empty::<&str>())
        } else {
            list(
                "IRBlock",
                [format!(
                    "IRBlock.mk 0 ({}) ({})",
                    ids(&params),
                    list("IRNode", self.nodes.iter().map(Node::ir))
                )],
            )
        };
        format!("IRFunc.mk {} ({}) 0 ({blocks})", self.id, ids(&params))
    }

    fn signature(&self) -> String {
        format!(
            "IRByteSignatureV1.mk {} ({}) ({}) Bool.false",
            self.signature,
            types(&self.params),
            types(&self.returns)
        )
    }

    fn binding(&self) -> String {
        format!(
            "IRByteFunctionV1.mk {} {} {} {} Bool.{}",
            self.id,
            self.signature,
            4096 + 32 * self.id,
            self.cc,
            if self.imported { "true" } else { "false" }
        )
    }

    fn sites(&self) -> Vec<String> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(pc, node)| {
                let extension = node.operands.as_ref().map(|rows| {
                    list(
                        "IRByteOperandV1",
                        rows.iter()
                            .map(|(id, ty)| format!("IRByteOperandV1.mk {id} ({ty})")),
                    )
                });
                let constructor = if extension.is_some() { "mkt" } else { "mk" };
                let mut site = format!(
                    "IRByteSiteV1.{constructor} {} 0 {pc} {} {} ({})",
                    self.id,
                    node.align,
                    node.cc,
                    types(&node.types)
                );
                if let Some(rows) = extension {
                    site.push_str(&format!(" ({rows})"));
                }
                site
            })
            .collect()
    }
}

fn register(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(
        source,
        "Generic byte-machine executable fixture; not source or native correctness evidence",
    )
    .expect("machine fixture must elaborate and check");
}

fn check(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    register(
        spec,
        &format!("def {name} : Eq ({ty}) ({actual}) ({expected}) := Eq.refl ({ty}) ({expected})"),
    );
    spec.verify_definition(name)
        .expect("kernel replay of actual machine execution");
    assert!(spec
        .env()
        .axiom_deps(&Name::from_string(name))
        .expect("witness exists")
        .is_empty());
    assert!(spec
        .env()
        .trust_marker_deps(&Name::from_string(name))
        .expect("witness exists")
        .is_empty());
}

fn context(spec: &mut Specification, name: &str, functions: &[Function]) {
    let mut layouts = Vec::new();
    for (ty, size, align) in [
        ("IRTy.bool_", 1, 1),
        ("IRTy.int_ 8", 1, 1),
        ("IRTy.uint_ 8", 1, 1),
        ("IRTy.int_ 64", 8, 8),
        ("IRTy.uint_ 64", 8, 8),
        ("IRTy.ptr_", 8, 8),
        ("IRTy.array_ (IRTy.int_ 8) 16", 16, 1),
    ] {
        layouts.push(format!(
            "IRByteLayoutV1.mk ({ty}) {size} {align} ({}) ({})",
            types(&[]),
            ids(&[])
        ));
    }
    layouts.push(format!(
        "IRByteLayoutV1.mk (IRTy.struct_ 9) 16 8 ({}) ({})",
        types(&["IRTy.uint_ 64", "IRTy.int_ 64"]),
        ids(&[0, 8])
    ));
    for function in functions {
        layouts.push(format!(
            "IRByteLayoutV1.mk (IRTy.func_ {}) 8 8 ({}) ({})",
            function.signature,
            types(&[]),
            ids(&[])
        ));
    }
    register(spec, &format!("def {name} : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk ({}) (IRList.nil IRGlobal)) ({}) ({}) ({}) ({})",
        list("IRFunc", functions.iter().map(Function::ir)),
        list("IRByteLayoutV1", layouts),
        list("IRByteSignatureV1", functions.iter().map(Function::signature)),
        list("IRByteFunctionV1", functions.iter().map(Function::binding)),
        list("IRByteSiteV1", functions.iter().flat_map(Function::sites))));
}

fn machine_spec() -> Specification {
    let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("production checked byte-profile constructor");
    register(&mut spec, "def byte_machine_no_import : IRByteProvidersV1 Nat := fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) => IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) mem host");
    register(&mut spec, "def byte_machine_external_mem : IRByteMemoryV1 := IRByteMemoryV1.mk (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 0 Bool.true) (IRList.nil IRByteAllocationV1)) (fun (_ : Nat) => IROption.none Nat) 64");
    register(&mut spec, "def byte_machine_after_memory (r : IRByteMemoryResultV1) : IRByteMemoryV1 := match r with\n| IRByteMemoryResultV1.value v mem => mem\n| IRByteMemoryResultV1.fault outcome mem => mem");
    register(&mut spec, "def byte_machine_memory_outcome (r : IRByteMemoryResultV1) : IROutcome := match r with\n| IRByteMemoryResultV1.value v mem => IROutcome.ret (IRList.cons IRScalar v (IRList.nil IRScalar))\n| IRByteMemoryResultV1.fault outcome mem => outcome");
    spec
}

fn run(
    context: &str,
    provider: &str,
    root: u64,
    args: &[&str],
    mem: &str,
    host: u64,
    fuel: u64,
) -> String {
    format!("ir_byte_run_v1 Nat {context} {provider} {fuel} (ir_byte_init_v1 Nat {context} {root} ({}) ({mem}) {host})", scalar_values(args))
}

fn outcome(config: &str) -> String {
    format!("ir_byte_outcome_v1 Nat ({config})")
}

fn world(config: &str) -> String {
    format!("ir_byte_final_world_v1 Nat ({config})")
}

mod casts;
mod copy;
mod scalar_ops;
mod work_budget;

const FIVE: &[&str] = &[
    "IRTy.ptr_",
    "IRTy.uint_ 64",
    "IRTy.int_ 64",
    "IRTy.uint_ 64",
    "IRTy.uint_ 64",
];
const FIVE_VALUES: &[&str] = &[
    "IRScalar.ptr_ 128",
    "IRScalar.int_ 0",
    "IRScalar.int_ 18446744073709551615",
    "IRScalar.int_ 3",
    "IRScalar.int_ 5",
];

fn five_callee(id: u64) -> Function {
    Function::local(
        id,
        &["IRTy.ptr_"],
        FIVE,
        vec![
            Node::constant("IRTy.uint_ 64", "IRConst.int_ 0", 1),
            Node::constant("IRTy.int_ 64", "IRConst.int_ 18446744073709551615", 2),
            Node::constant("IRTy.uint_ 64", "IRConst.int_ 3", 3),
            Node::constant("IRTy.uint_ 64", "IRConst.int_ 5", 4),
            Node::ret(&[0, 1, 2, 3, 4]),
        ],
    )
}

#[test]
fn exact_local_and_typed_indirect_calls_keep_all_five_return_lanes() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        let direct = Function::local(
            10,
            &["IRTy.ptr_"],
            FIVE,
            vec![
                Node::new(
                    format!("IRInst.call 20 ({})", ids(&[0])),
                    &[11, 12, 13, 14, 15],
                    FIVE,
                ),
                Node::ret(&[11, 12, 13, 14, 15]),
            ],
        );
        let indirect = Function::local(
            11,
            &["IRTy.ptr_"],
            FIVE,
            vec![
                Node::constant("IRTy.func_ 20", "IRConst.func_ 20", 1),
                Node::new(
                    format!("IRInst.callindirect 1 20 ({}) 1", ids(&[0])),
                    &[21, 22, 23, 24, 25],
                    FIVE,
                ),
                Node::ret(&[21, 22, 23, 24, 25]),
            ],
        );
        context(
            &mut spec,
            "byte_machine_five_ctx",
            &[direct, five_callee(20), indirect],
        );
        for (name, root) in [
            ("byte_machine_direct_five", 10),
            ("byte_machine_indirect_five", 11),
        ] {
            let executed = run(
                "byte_machine_five_ctx",
                "byte_machine_no_import",
                root,
                &["IRScalar.ptr_ 128"],
                "ir_byte_memory_empty_v1 64",
                0,
                32,
            );
            check(
                &mut spec,
                name,
                "IROutcome",
                &outcome(&executed),
                &returned(FIVE_VALUES),
            );
            check(
                &mut spec,
                &format!("{name}_owners"),
                "IRList Nat",
                &format!("ir_byte_world_owners_v1 Nat ({})", world(&executed)),
                &ids(&[]),
            );
        }
    });
}

fn provider_fixture(spec: &mut Specification) {
    let mut call = Node::new(
        format!("IRInst.call 31 ({})", ids(&[])),
        &[0],
        &["IRTy.struct_ 9"],
    );
    call.cc = 0;
    let root = Function::local(
        30,
        &[],
        &["IRTy.uint_ 64", "IRTy.int_ 64"],
        vec![
            call,
            Node::new(
                "IRInst.extractfield (IRTy.uint_ 64) 0 0",
                &[1],
                &["IRTy.uint_ 64"],
            )
            .with_operands(&[(0, "IRTy.struct_ 9")]),
            Node::new(
                "IRInst.extractfield (IRTy.int_ 64) 0 1",
                &[2],
                &["IRTy.int_ 64"],
            )
            .with_operands(&[(0, "IRTy.struct_ 9")]),
            Node::ret(&[1, 2]),
        ],
    );
    context(
        spec,
        "byte_machine_provider_ctx",
        &[root, Function::import(31, &[], &["IRTy.struct_ 9"])],
    );
    let pair = "IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 0) (IRScalar.vcons (IRScalar.int_ 18446744073709551615) IRScalar.vnil))";
    for (name, result) in [
        ("byte_machine_provider_ok", returned(&[pair])),
        (
            "byte_machine_provider_fail",
            "IROutcome.ub IRFault.assert_failed".to_owned(),
        ),
        (
            "byte_machine_provider_flat",
            returned(&["IRScalar.int_ 0", "IRScalar.int_ 18446744073709551615"]),
        ),
    ] {
        register(spec, &format!("def {name} : IRByteProvidersV1 Nat := fun (fid : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 Nat) (IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) mem host) (IRByteImportResultV1.mk Nat ({result}) (byte_machine_after_memory (ir_byte_store_v1 byte_machine_provider_ctx (IRTy.uint_ 8) (IRScalar.ptr_ 16) (IRScalar.int_ (Nat.succ host)) 0 Bool.false mem)) (Nat.succ host)) (ir_nat_eqb fid 31)"));
    }
}

#[test]
fn c_import_is_one_ssa_struct_and_keeps_updated_world_on_success_and_failure() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        provider_fixture(&mut spec);
        for (name, provider, expected) in [
            (
                "byte_machine_import_success",
                "byte_machine_provider_ok",
                returned(&["IRScalar.int_ 0", "IRScalar.int_ 18446744073709551615"]),
            ),
            (
                "byte_machine_import_failure",
                "byte_machine_provider_fail",
                "IROutcome.ub IRFault.assert_failed".to_owned(),
            ),
            (
                "byte_machine_import_wrong_flat_abi",
                "byte_machine_provider_flat",
                "IROutcome.type_error IRFault.bad_field".to_owned(),
            ),
        ] {
            let executed = run(
                "byte_machine_provider_ctx",
                provider,
                30,
                &[],
                "byte_machine_external_mem",
                7,
                32,
            );
            check(&mut spec, name, "IROutcome", &outcome(&executed), &expected);
            check(
                &mut spec,
                &format!("{name}_host"),
                "Nat",
                &format!("ir_byte_world_host_v1 Nat ({})", world(&executed)),
                "8",
            );
            check(
                &mut spec,
                &format!("{name}_byte"),
                "IROption Nat",
                &format!(
                    "ir_byte_mem_bytes_v1 (ir_byte_world_memory_v1 Nat ({})) 16",
                    world(&executed)
                ),
                "IROption.some Nat 8",
            );
        }
    });
}

#[test]
fn fuel_exhaustion_retains_running_world_and_resumes_through_the_shared_driver() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        provider_fixture(&mut spec);
        let initial = "ir_byte_init_v1 Nat byte_machine_provider_ctx 30 (IRList.nil IRScalar) byte_machine_external_mem 7";
        check(&mut spec, "byte_machine_zero_fuel", "IRByteConfigV1 Nat",
            &format!("ir_byte_run_v1 Nat byte_machine_provider_ctx byte_machine_provider_ok 0 ({initial})"), initial);
        let partial = run(
            "byte_machine_provider_ctx",
            "byte_machine_provider_ok",
            30,
            &[],
            "byte_machine_external_mem",
            7,
            1,
        );
        check(
            &mut spec,
            "byte_machine_partial_outcome",
            "IROutcome",
            &outcome(&partial),
            "IROutcome.fuel_out",
        );
        check(
            &mut spec,
            "byte_machine_partial_host",
            "Nat",
            &format!("ir_byte_world_host_v1 Nat ({})", world(&partial)),
            "8",
        );
        check(
            &mut spec,
            "byte_machine_partial_byte",
            "IROption Nat",
            &format!(
                "ir_byte_mem_bytes_v1 (ir_byte_world_memory_v1 Nat ({})) 16",
                world(&partial)
            ),
            "IROption.some Nat 8",
        );
        let resumed = format!(
            "ir_byte_run_v1 Nat byte_machine_provider_ctx byte_machine_provider_ok 32 ({partial})"
        );
        check(
            &mut spec,
            "byte_machine_resumed_returns",
            "IROutcome",
            &outcome(&resumed),
            &returned(&["IRScalar.int_ 0", "IRScalar.int_ 18446744073709551615"]),
        );
        let whole = run(
            "byte_machine_provider_ctx",
            "byte_machine_provider_ok",
            30,
            &[],
            "byte_machine_external_mem",
            7,
            33,
        );
        check(
            &mut spec,
            "byte_machine_resume_same_config",
            "IRByteConfigV1 Nat",
            &resumed,
            &whole,
        );
    });
}

#[test]
fn byte_array_capture_survives_nested_callees_and_retires_with_its_owner() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        let mut allocation = Node::new(
            "IRInst.alloca (IRTy.array_ (IRTy.int_ 8) 16) (IROption.none Nat)",
            &[0],
            &["IRTy.ptr_"],
        );
        allocation.align = 8;
        let owner = Function::local(
            40,
            &[],
            &["IRTy.int_ 64", "IRTy.int_ 64"],
            vec![
                allocation,
                Node::constant("IRTy.func_ 41", "IRConst.func_ 41", 1),
                Node::constant("IRTy.int_ 64", "IRConst.int_ 99", 2),
                Node::new("IRInst.store (IRTy.int_ 64) 0 2 Bool.false", &[], &[]),
                Node::constant("IRTy.int_ 64", "IRConst.int_ 8", 3),
                Node::new(
                    format!("IRInst.gep (IRTy.int_ 8) 0 ({}) Bool.true", ids(&[3])),
                    &[4],
                    &["IRTy.ptr_"],
                ),
                Node::new("IRInst.store (IRTy.func_ 41) 4 1 Bool.false", &[], &[]),
                Node::new(
                    format!("IRInst.call 42 ({})", ids(&[0])),
                    &[5],
                    &["IRTy.int_ 64"],
                ),
                // This load occurs AFTER both callees have returned. Merely
                // returning the previously loaded callback result would not expose
                // a premature retirement of the caller's capture storage.
                Node::new(
                    "IRInst.load (IRTy.int_ 64) 0 Bool.false",
                    &[6],
                    &["IRTy.int_ 64"],
                ),
                Node::ret(&[5, 6]),
            ],
        );
        let callback = Function::local(
            41,
            &["IRTy.ptr_"],
            &["IRTy.int_ 64"],
            vec![
                Node::new(
                    "IRInst.load (IRTy.int_ 64) 0 Bool.false",
                    &[1],
                    &["IRTy.int_ 64"],
                ),
                Node::ret(&[1]),
            ],
        );
        let forward = Function::local(
            42,
            &["IRTy.ptr_"],
            &["IRTy.int_ 64"],
            vec![
                Node::constant("IRTy.int_ 64", "IRConst.int_ 8", 1),
                Node::new(
                    format!("IRInst.gep (IRTy.int_ 8) 0 ({}) Bool.true", ids(&[1])),
                    &[2],
                    &["IRTy.ptr_"],
                ),
                Node::new(
                    "IRInst.load (IRTy.func_ 41) 2 Bool.false",
                    &[3],
                    &["IRTy.func_ 41"],
                ),
                Node::new(
                    format!("IRInst.callindirect 3 41 ({}) 1", ids(&[0])),
                    &[4],
                    &["IRTy.int_ 64"],
                ),
                Node::ret(&[4]),
            ],
        );
        context(
            &mut spec,
            "byte_machine_capture_ctx",
            &[owner, forward, callback],
        );
        let executed = run(
            "byte_machine_capture_ctx",
            "byte_machine_no_import",
            40,
            &[],
            "ir_byte_memory_empty_v1 64",
            0,
            64,
        );
        check(
            &mut spec,
            "byte_machine_capture_results",
            "IROutcome",
            &outcome(&executed),
            &returned(&["IRScalar.int_ 99", "IRScalar.int_ 99"]),
        );
        let memory = format!("ir_byte_world_memory_v1 Nat ({})", world(&executed));
        check(
            &mut spec,
            "byte_machine_capture_final_bytes",
            "IROption Nat",
            &format!("ir_byte_mem_bytes_v1 ({memory}) 64"),
            "IROption.some Nat 99",
        );
        check(&mut spec, "byte_machine_capture_owner_retired", "IROutcome",
            &format!("byte_machine_memory_outcome (ir_byte_load_v1 byte_machine_capture_ctx (IRTy.int_ 64) (IRScalar.ptr_ 64) 0 Bool.false ({memory}))"),
            "IROutcome.ub IRFault.bad_addr");
        check(
            &mut spec,
            "byte_machine_capture_owners_popped",
            "IRList Nat",
            &format!("ir_byte_world_owners_v1 Nat ({})", world(&executed)),
            &ids(&[]),
        );
    });
}

#[test]
fn returning_a_local_byte_pointer_does_not_extend_its_activation_lifetime() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        let mut allocation = Node::new(
            "IRInst.alloca (IRTy.array_ (IRTy.int_ 8) 16) (IROption.none Nat)",
            &[0],
            &["IRTy.ptr_"],
        );
        allocation.align = 8;
        let callee = Function::local(
            50,
            &[],
            &["IRTy.ptr_"],
            vec![
                allocation,
                Node::constant("IRTy.int_ 64", "IRConst.int_ 77", 1),
                Node::new("IRInst.store (IRTy.int_ 64) 0 1 Bool.false", &[], &[]),
                Node::ret(&[0]),
            ],
        );
        let caller = Function::local(
            51,
            &[],
            &["IRTy.int_ 64"],
            vec![
                Node::new(
                    format!("IRInst.call 50 ({})", ids(&[])),
                    &[0],
                    &["IRTy.ptr_"],
                ),
                Node::new(
                    "IRInst.load (IRTy.int_ 64) 0 Bool.false",
                    &[1],
                    &["IRTy.int_ 64"],
                ),
                Node::ret(&[1]),
            ],
        );
        context(&mut spec, "byte_machine_escape_ctx", &[caller, callee]);
        let executed = run(
            "byte_machine_escape_ctx",
            "byte_machine_no_import",
            51,
            &[],
            "ir_byte_memory_empty_v1 64",
            0,
            32,
        );
        check(
            &mut spec,
            "byte_machine_use_after_return",
            "IROutcome",
            &outcome(&executed),
            "IROutcome.ub IRFault.bad_addr",
        );
        check(
            &mut spec,
            "byte_machine_use_after_return_keeps_bytes",
            "IROption Nat",
            &format!(
                "ir_byte_mem_bytes_v1 (ir_byte_world_memory_v1 Nat ({})) 64",
                world(&executed)
            ),
            "IROption.some Nat 77",
        );
    });
}

#[test]
fn call_signature_convention_and_exact_arity_are_not_erased() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        for (name, nodes, expected) in [
            (
                "wrong_nominal_signature",
                vec![
                    Node::constant("IRTy.func_ 20", "IRConst.func_ 20", 1),
                    Node::new(
                        format!("IRInst.callindirect 1 21 ({}) 1", ids(&[0])),
                        &[21, 22, 23, 24, 25],
                        FIVE,
                    ),
                    Node::ret(&[21, 22, 23, 24, 25]),
                ],
                "IROutcome.type_error IRFault.not_fnptr",
            ),
            (
                "wrong_calling_convention",
                vec![
                    Node::constant("IRTy.func_ 20", "IRConst.func_ 20", 1),
                    Node::new(
                        format!("IRInst.callindirect 1 20 ({}) 0", ids(&[0])),
                        &[21, 22, 23, 24, 25],
                        FIVE,
                    )
                    .with_cc(0),
                    Node::ret(&[21, 22, 23, 24, 25]),
                ],
                "IROutcome.type_error IRFault.not_fnptr",
            ),
            (
                "missing_argument",
                vec![
                    Node::new(
                        format!("IRInst.call 20 ({})", ids(&[])),
                        &[21, 22, 23, 24, 25],
                        FIVE,
                    ),
                    Node::ret(&[21, 22, 23, 24, 25]),
                ],
                "IROutcome.type_error IRFault.not_fnptr",
            ),
            (
                "missing_result_destination",
                vec![
                    Node::new(
                        format!("IRInst.call 20 ({})", ids(&[0])),
                        &[21, 22, 23, 24],
                        &FIVE[..4],
                    ),
                    Node::ret(&[21, 22, 23, 24]),
                ],
                "IROutcome.type_error IRFault.not_fnptr",
            ),
            (
                "missing_return_lane",
                vec![
                    Node::new(
                        format!("IRInst.call 20 ({})", ids(&[0])),
                        &[21, 22, 23, 24, 25],
                        FIVE,
                    ),
                    Node::ret(&[21, 22, 23, 24]),
                ],
                "IROutcome.type_error IRFault.bad_field",
            ),
        ] {
            let ctx = format!("byte_machine_{name}_ctx");
            let caller = Function::local(11, &["IRTy.ptr_"], FIVE, nodes);
            // Signature 21 deliberately exists and has the same structural
            // lane types as 20. A wrong nominal signature is not merely an
            // absent-table-entry check or a width mismatch.
            context(&mut spec, &ctx, &[caller, five_callee(20), five_callee(21)]);
            let executed = run(
                &ctx,
                "byte_machine_no_import",
                11,
                &["IRScalar.ptr_ 128"],
                "ir_byte_memory_empty_v1 64",
                0,
                32,
            );
            check(
                &mut spec,
                &format!("byte_machine_{name}"),
                "IROutcome",
                &outcome(&executed),
                expected,
            );
        }
    });
}

#[test]
fn fresh_root_owner_does_not_reuse_historical_allocations() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = machine_spec();
        let root = Function::local(
            60,
            &[],
            &["IRTy.int_ 64"],
            vec![
                Node::constant("IRTy.int_ 64", "IRConst.int_ 1", 0),
                Node::ret(&[0]),
            ],
        );
        context(&mut spec, "byte_machine_owner_ctx", &[root]);
        let retired = "IRByteMemoryV1.mk (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 7 Bool.false) (IRList.nil IRByteAllocationV1)) (fun (_ : Nat) => IROption.none Nat) 64";
        let initial = format!(
            "ir_byte_init_v1 Nat byte_machine_owner_ctx 60 (IRList.nil IRScalar) ({retired}) 0"
        );
        check(
            &mut spec,
            "byte_machine_root_owner_fresh",
            "IRList Nat",
            &format!("ir_byte_world_owners_v1 Nat ({})", world(&initial)),
            &ids(&[8]),
        );
        check(
            &mut spec,
            "byte_machine_root_next_fresh",
            "Nat",
            &format!("ir_byte_world_next_v1 Nat ({})", world(&initial)),
            "9",
        );
        let executed = run(
            "byte_machine_owner_ctx",
            "byte_machine_no_import",
            60,
            &[],
            retired,
            0,
            8,
        );
        check(
            &mut spec,
            "byte_machine_historical_owner_runs",
            "IROutcome",
            &outcome(&executed),
            &returned(&["IRScalar.int_ 1"]),
        );
        let live = "IRByteMemoryV1.mk (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 7 Bool.true) (IRList.nil IRByteAllocationV1)) (fun (_ : Nat) => IROption.none Nat) 64";
        let rejected = run(
            "byte_machine_owner_ctx",
            "byte_machine_no_import",
            60,
            &[],
            live,
            0,
            8,
        );
        check(
            &mut spec,
            "byte_machine_foreign_live_owner_rejected",
            "IROutcome",
            &outcome(&rejected),
            "IROutcome.type_error IRFault.bad_addr",
        );
        check(
            &mut spec,
            "byte_machine_foreign_live_memory_retained",
            "IRByteMemoryV1",
            &format!("ir_byte_world_memory_v1 Nat ({})", world(&rejected)),
            live,
        );
    });
}
