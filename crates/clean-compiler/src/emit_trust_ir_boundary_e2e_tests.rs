// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.9 end to end: the proof program's `area` (p06) and `dot` (p07),
//! elaborated from Lean source by Clean's own front end, exported through the
//! typed boundary, executed, linked against a Rust-producer module under
//! `validate_linked_module`, and CALLED from that module: the Rust client's
//! body runs in the interpreter and its call to the body-less carrier
//! declaration is served by the Clean module's typed wrapper.
//!
//! A child of `emit_trust_ir::boundary::tests`, so the `trust-ir-backend-lib`
//! gate leg (`-- emit_trust_ir`) runs it.
//!
//! # The executable differential
//!
//! No single engine runs a Clean module: the reference interpreter has no
//! model of Clean's C runtime (`clean_alloc_ctor` is a variadic runtime
//! import), and trust-cg refuses a by-value enum parameter (F-112) and every
//! `Ungated` body. So the chain is split at the one seam the design puts
//! there, and each half runs on a real engine:
//!
//! * the MARSHAL-IN HELPERS (allocation, constructor field order, RC) are the
//!   same L5IR the trust-ir module lowers, compiled by Clean's C back end,
//!   linked against the Clean runtime, and run natively;
//! * the TYPED WRAPPER (tag dispatch, lane projection, argument order) runs in
//!   trust-ir's reference interpreter, on by-value `Ty::Struct` / `Ty::Enum`
//!   arguments, with each helper call served by that native binary (one
//!   process per call; the run is host-assisted, which the outcome counts).
//!
//! Every expected value is first CERTIFIED by the kernel (`f args = r := rfl`
//! in the elaborated environment), and the off-by-one twin is refused by the
//! kernel and by the comparison.
//!
//! MUTATION CONTROL: swapping two same-typed lanes in the marshaller (Pt's
//! `x`/`y`, Shape.rect's `w`/`h`) is caught by the differential on the
//! asymmetric roots (`skew`, `tilt`), whose vectors pick distinct field
//! values; it is invisible on the symmetric `dot`/`area`, which is why the
//! asymmetric roots are here.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;
use crate::emit_c::{emit_c_with_config, CEmitConfig};
use crate::mangle::mangle_name;
use crate::pass_manager::compile_lcnf_decls;
use crate::rc_repair::e2e_support::{closure_decls_of, elaborated_env_with, o0, SHIMS_C};
use clean_kernel::Level;
use trust_ir::interpret::{
    HostCalls, HostState, InterpretError, InterpretErrorCode, InterpretInt, InterpretResult,
    InterpretValue, InterpretValueKind, Interpreter,
};
use trust_ir::proof::RejectingModuleProofAuthority;
use trust_ir::ty::FuncTy;
use trust_ir::{Function, ModuleImport, Producer};
use trust_ir_build::{validate_linked_module, ModuleSet};

/// p06 and p07 verbatim, plus two ASYMMETRIC roots for the mutation control.
const SOURCE: &str = "inductive Shape where
  | sq (s : UInt64)
  | rect (w h : UInt64)

def area : Shape → UInt64
  | .sq s => s * s
  | .rect w h => w * h

def areaOfRect (w h : UInt64) : UInt64 := area (.rect w h)

structure Pt where
  x : UInt64
  y : UInt64

def dot (p q : Pt) : UInt64 := p.x * q.x + p.y * q.y
def dotOf (a b c d : UInt64) : UInt64 := dot ⟨a, b⟩ ⟨c, d⟩

def tilt : Shape → UInt64
  | .sq s => s + 1
  | .rect w h => w * 3 + h

def skew (p : Pt) : UInt64 := p.x * 3 + p.y
";

const EXPORTS: [&str; 6] = ["area", "dot", "tilt", "skew", "areaOfRect", "dotOf"];

/// A boundary argument.
#[derive(Clone, Copy, Debug)]
enum Arg {
    Sq(u64),
    Rect(u64, u64),
    Pt(u64, u64),
    U64(u64),
}

/// `(export, args, kernel-certified result)`.
const VECTORS: &[(&str, &[Arg], u64)] = &[
    ("area", &[Arg::Sq(7)], 49),
    ("area", &[Arg::Rect(3, 5)], 15),
    ("area", &[Arg::Rect(6, 7)], 42),
    ("dot", &[Arg::Pt(1, 2), Arg::Pt(3, 4)], 11),
    ("dot", &[Arg::Pt(5, 6), Arg::Pt(7, 9)], 89),
    ("tilt", &[Arg::Sq(9)], 10),
    ("tilt", &[Arg::Rect(4, 5)], 17),
    ("skew", &[Arg::Pt(4, 5)], 17),
    ("skew", &[Arg::Pt(2, 11)], 17),
    ("areaOfRect", &[Arg::U64(3), Arg::U64(5)], 15),
    (
        "dotOf",
        &[Arg::U64(1), Arg::U64(2), Arg::U64(3), Arg::U64(4)],
        11,
    ),
];

fn u64_lit(n: u64) -> Expr {
    Expr::app(Expr::const_str("UInt64.ofNat"), Expr::nat_lit(n))
}

fn arg_expr(arg: Arg) -> Expr {
    match arg {
        Arg::Sq(s) => Expr::app(Expr::const_str("Shape.sq"), u64_lit(s)),
        Arg::Rect(w, h) => Expr::apps(Expr::const_str("Shape.rect"), [u64_lit(w), u64_lit(h)]),
        Arg::Pt(x, y) => Expr::apps(Expr::const_str("Pt.mk"), [u64_lit(x), u64_lit(y)]),
        Arg::U64(v) => u64_lit(v),
    }
}

/// Does the kernel accept `theorem <name> : f args = r := rfl`?
fn kernel_certifies(env: &mut Environment, name: &str, f: &str, args: &[Arg], r: u64) -> bool {
    let lvl = vec![Level::succ(Level::zero())];
    let u64t = Expr::const_str("UInt64");
    let lhs = Expr::apps(Expr::const_str(f), args.iter().map(|a| arg_expr(*a)));
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(Name::from_string("Eq"), lvl.clone()),
            [u64t.clone(), lhs, u64_lit(r)],
        ),
        value: Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), lvl),
            [u64t, u64_lit(r)],
        ),
    })
    .is_ok()
}

/// The elaborated environment, every vector certified (and its off-by-one
/// twin refused) by the kernel.
fn certified_env() -> Environment {
    let mut env = elaborated_env_with(SOURCE);
    for (i, (f, args, r)) in VECTORS.iter().enumerate() {
        assert!(
            !kernel_certifies(&mut env, &format!("ws69_off_{i}"), f, args, r + 1),
            "the kernel must REFUSE {f} {args:?} = {}",
            r + 1
        );
        assert!(
            kernel_certifies(&mut env, &format!("ws69_vec_{i}"), f, args, *r),
            "the kernel must certify {f} {args:?} = {r}"
        );
    }
    env
}

fn exports() -> Vec<Name> {
    EXPORTS.iter().map(|e| Name::from_string(e)).collect()
}

fn extern_config() -> TrustIrConfig {
    TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

struct Lowered {
    env: Environment,
    decls: Vec<Decl>,
    module: Module,
    plan: Vec<CarrierExport>,
}

fn lowered() -> &'static Lowered {
    static LOWERED: std::sync::OnceLock<Lowered> = std::sync::OnceLock::new();
    LOWERED.get_or_init(|| {
        let env = certified_env();
        let decls = closure_decls_of(&env, &o0(), &EXPORTS);
        let (module, _, plan) = compile_lcnf_to_trust_ir_with_carrier_exports(
            &decls,
            &env,
            &o0(),
            &extern_config(),
            &exports(),
        )
        .unwrap_or_else(|e| panic!("the six exports must lower: {e}"));
        Lowered {
            env,
            decls,
            module,
            plan,
        }
    })
}

// ---- the native helper lane ------------------------------------------------------

fn cc() -> String {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let found = Command::new(&cc)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    assert!(
        found,
        "a C compiler is required by the WS6.9 differential ({cc}); it asserts executed \
         values and must not skip"
    );
    cc
}

/// Compile the plan's helpers (and the boxed bodies they call) through Clean's
/// C back end, with a driver `bin <helper index> <u64 args..>` that prints
/// the helper's result. Returns the binary and the helper-symbol -> index map.
fn native_helpers(dir: &Path) -> (PathBuf, BTreeMap<String, usize>) {
    let l = lowered();
    // The SAME plan the trust-ir module was lowered from (deterministic).
    let plan = plan_carrier_exports(&l.env, &l.decls, &exports()).expect("plans");
    let ir = compile_lcnf_decls(&plan.decls, &plan.env, &o0())
        .expect("helpers compile and pass verify_rc_linearity")
        .boxed_ir_decls;
    let emitted = emit_c_with_config(
        &ir,
        CEmitConfig {
            check_ir: true,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C");
    let mut index = BTreeMap::new();
    let mut cases = String::new();
    for export in &plan.exports {
        for helper in &export.helpers {
            let scalars: Vec<CarrierScalar> = export
                .params
                .iter()
                .zip(&helper.choice)
                .flat_map(|(p, &arm)| arm_scalars(p, arm))
                .collect();
            assert!(
                scalars.iter().all(|s| *s == CarrierScalar::U64),
                "the fixture's helpers take UInt64 only"
            );
            let k = index.len();
            index.insert(wire_name(&helper.name), k);
            let args = (0..scalars.len())
                .map(|j| format!("a[{j}]"))
                .collect::<Vec<_>>()
                .join(", ");
            cases.push_str(&format!(
                "    case {k}: r = (uint64_t){}({args}); break;\n",
                mangle_name(&helper.name)
            ));
        }
    }
    let driver = format!(
        "#include <inttypes.h>\n#include <stdlib.h>\n\
         int main(int argc, char** argv) {{\n\
           uint64_t a[8] = {{0}}; uint64_t r = 0;\n\
           if (argc < 2 || argc > 10) return 2;\n\
           for (int i = 2; i < argc; i++) a[i - 2] = strtoull(argv[i], 0, 10);\n\
           switch (atoi(argv[1])) {{\n{cases}    default: return 3;\n  }}\n\
           printf(\"%\" PRIu64 \"\\n\", r);\n  return 0;\n}}\n"
    );
    std::fs::write(dir.join("clean_runtime.h"), clean_runtime::runtime_header())
        .expect("write header");
    std::fs::write(
        dir.join("clean_runtime.c"),
        clean_runtime::runtime_source().replacen(
            "../include/clean_runtime.h",
            "clean_runtime.h",
            1,
        ),
    )
    .expect("write runtime");
    let program = dir.join("ws69.c");
    std::fs::write(
        &program,
        format!("#include <stdio.h>\n#include \"clean_runtime.h\"\n{SHIMS_C}\n{emitted}\n{driver}"),
    )
    .expect("write program");
    let bin = dir.join("ws69");
    let out = Command::new(cc())
        .arg("-std=c11")
        .arg("-o")
        .arg(&bin)
        .arg(&program)
        .arg(dir.join("clean_runtime.c"))
        .arg("-I")
        .arg(dir)
        .arg("-lm")
        .output()
        .expect("spawn cc");
    assert!(
        out.status.success(),
        "cc failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    (bin, index)
}

/// Serves each helper call by running the native helper binary.
struct NativeHelpers {
    bin: PathBuf,
    index: BTreeMap<String, usize>,
}

impl HostCalls for NativeHelpers {
    fn call(
        &self,
        callee: &Function,
        sig: &FuncTy,
        args: &[InterpretValue],
        _host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        let k = *self.index.get(&callee.name)?;
        if sig.returns != [Ty::U64] || sig.params.iter().any(|t| *t != Ty::U64) {
            return None;
        }
        let mut cmd = Command::new(&self.bin);
        cmd.arg(k.to_string());
        for a in args {
            let InterpretValueKind::Int(i) = &a.kind else {
                return Some(Err(InterpretError::new(
                    InterpretErrorCode::TypeError,
                    "helper argument is not an integer",
                )));
            };
            cmd.arg(i.as_unsigned().to_string());
        }
        let out = cmd.output().expect("run the native helper");
        if !out.status.success() {
            return Some(Err(InterpretError::new(
                InterpretErrorCode::UnsupportedCall,
                format!("native helper {} failed: {:?}", callee.name, out.status),
            )));
        }
        let v: u64 = String::from_utf8_lossy(&out.stdout)
            .trim()
            .parse()
            .expect("the helper prints a u64");
        Some(InterpretValue::int(Ty::U64, i128::from(v)).map(|v| vec![v]))
    }
}

/// The module the interpreter runs: the helpers made bodyless, so each call
/// to one reaches the host (the native helper), and nothing else changed.
fn interpretable(module: &Module, plan: &[CarrierExport]) -> Module {
    let mut m = module.clone();
    let helpers: Vec<String> = plan
        .iter()
        .flat_map(|e| e.helpers.iter().map(|h| wire_name(&h.name)))
        .collect();
    for f in &mut m.functions {
        if helpers.contains(&f.name) {
            f.blocks.clear();
        }
    }
    m
}

fn u64v(v: u64) -> InterpretValue {
    InterpretValue {
        ty: Ty::U64,
        kind: InterpretValueKind::Int(InterpretInt {
            bits: 64,
            signed: false,
            raw: u128::from(v),
        }),
    }
}

fn u8v(v: u8) -> InterpretValue {
    InterpretValue {
        ty: Ty::U8,
        kind: InterpretValueKind::Int(InterpretInt {
            bits: 8,
            signed: false,
            raw: u128::from(v),
        }),
    }
}

/// A by-value boundary argument at the wrapper's parameter type.
fn arg_value(arg: Arg, ty: &Ty) -> InterpretValue {
    let kind = match arg {
        Arg::U64(v) => return u64v(v),
        Arg::Pt(x, y) => InterpretValueKind::Aggregate(vec![u64v(x), u64v(y)]),
        Arg::Sq(s) => InterpretValueKind::Aggregate(vec![u8v(0), u64v(s)]),
        Arg::Rect(w, h) => InterpretValueKind::Aggregate(vec![u8v(1), u64v(w), u64v(h)]),
    };
    InterpretValue {
        ty: ty.clone(),
        kind,
    }
}

/// Run every vector through `module`'s typed wrappers; `(vector, result)`.
fn run_vectors(module: &Module, host: &NativeHelpers) -> Vec<(String, Result<u64, String>)> {
    let interp = Interpreter::with_module(module).with_host(host);
    VECTORS
        .iter()
        .map(|(f, args, _)| {
            let symbol = carrier_symbol(&Name::from_string(f));
            let func = module
                .functions
                .iter()
                .find(|g| g.name == symbol)
                .unwrap_or_else(|| panic!("no wrapper {symbol}"));
            let sig = &module.func_types[func.ty.as_usize()];
            let values: Vec<InterpretValue> = args
                .iter()
                .zip(&sig.params)
                .map(|(a, t)| arg_value(*a, t))
                .collect();
            let got = interp
                .execute_function(func, values)
                .map_err(|e| e.to_string())
                .and_then(|out| {
                    assert!(out.host_calls > 0, "a helper call is host-assisted");
                    match out.returns.as_slice() {
                        [InterpretValue {
                            kind: InterpretValueKind::Int(i),
                            ..
                        }] => Ok(u64::try_from(i.as_unsigned()).expect("u64")),
                        other => Err(format!("unexpected returns {other:?}")),
                    }
                });
            (format!("{f} {args:?}"), got)
        })
        .collect()
}

/// GAP row `GENERAL.representation` (PRODUCER-GAP -> PASS for the
/// non-recursive rows).
///
/// The proof program measured the as-emitted Clean module with
/// `enums = structs = 0`: every inductive and structure was a boxed `ptr`, and
/// Rust enums and Lean inductives had no shared spelling. Requested as
/// boundary exports, `area : Shape → UInt64` and `dot : Pt → Pt → UInt64`
/// now cross as a `Ty::Enum` with a normative descriptor and a `#[repr(C)]`
/// `Ty::Struct`; the module validates; and the typed wrappers compute the
/// kernel-certified value of every vector (off-by-one twins refused).
/// `FORMAT_HOME.native.struct` / `.enum` stay with WS7 (F-111/F-112).
#[test]
fn general_representation() {
    let l = lowered();
    assert_eq!(
        validate_module(&l.module),
        Vec::<ValidationError>::new(),
        "the boundary module validates"
    );
    assert_eq!(l.module.structs.len(), 1, "Pt is a Ty::Struct now");
    assert_eq!(l.module.enums.len(), 1, "Shape is a Ty::Enum now");
    assert!(
        l.module.enums[0].layout.is_some(),
        "with a normative descriptor"
    );
    // The boxed bodies keep their symbols and their boxed signatures.
    for f in ["area", "dot"] {
        let func = l
            .module
            .functions
            .iter()
            .find(|g| g.name == f)
            .unwrap_or_else(|| panic!("the boxed body {f} keeps its symbol"));
        let sig = &l.module.func_types[func.ty.as_usize()];
        assert!(sig.params.iter().all(|t| *t == Ty::Ptr), "{f}: {sig:?}");
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let (bin, index) = native_helpers(dir.path());
    let host = NativeHelpers { bin, index };
    let module = interpretable(&l.module, &l.plan);
    for ((vector, got), (_, _, want)) in run_vectors(&module, &host).into_iter().zip(VECTORS) {
        let got = got.unwrap_or_else(|e| panic!("{vector}: {e}"));
        assert_eq!(got, *want, "{vector}");
        assert_ne!(
            got,
            want + 1,
            "{vector}: the comparison rejects the off-by-one twin"
        );
    }
}

/// MUTATION CONTROL: swap two same-typed lanes in the marshaller. The
/// differential catches it on the asymmetric roots (the vectors pick distinct
/// field values), so the passing run above is evidence about field order.
#[test]
fn a_swapped_marshaller_lane_is_caught_by_the_differential() {
    let l = lowered();
    let dir = tempfile::tempdir().expect("tempdir");
    let (bin, index) = native_helpers(dir.path());
    let host = NativeHelpers { bin, index };
    let mut module = l.module.clone();
    let mut swapped = 0;
    for root in ["skew", "tilt"] {
        let symbol = carrier_symbol(&Name::from_string(root));
        let func = module
            .functions
            .iter_mut()
            .find(|g| g.name == symbol)
            .expect("wrapper");
        // The two U64 lanes the struct (lanes 0, 1) or the rect arm (lanes 1,
        // 2) projects: exchange their field indices.
        let (a, b) = if root == "skew" { (0, 1) } else { (1, 2) };
        for block in &mut func.blocks {
            let is_lane = |inst: &Inst| {
                matches!(inst, Inst::ExtractField { field, ty, .. }
                    if (*field == a || *field == b) && *ty == Ty::U64)
            };
            if block.instructions().filter(|n| is_lane(&n.inst)).count() != 2 {
                continue;
            }
            for node in block.instructions_mut() {
                if let Inst::ExtractField { field, ty, .. } = &mut node.inst {
                    if *ty == Ty::U64 && (*field == a || *field == b) {
                        *field = if *field == a { b } else { a };
                    }
                }
            }
            swapped += 1;
        }
    }
    assert_eq!(swapped, 2, "one swap per mutated wrapper");
    assert!(
        validate_module(&module).is_empty(),
        "the mutant is well-formed: only the differential can see it"
    );
    let module = interpretable(&module, &l.plan);
    let mut caught = Vec::new();
    for ((vector, got), (f, _, want)) in run_vectors(&module, &host).into_iter().zip(VECTORS) {
        let got = got.unwrap_or_else(|e| panic!("{vector}: {e}"));
        if got != *want {
            caught.push(vector.clone());
        }
        if !matches!(*f, "skew" | "tilt") {
            assert_eq!(got, *want, "{vector}: an unmutated wrapper is unaffected");
        }
    }
    assert_eq!(
        caught,
        [
            "tilt [Rect(4, 5)]".to_string(),
            "skew [Pt(4, 5)]".to_string(),
            "skew [Pt(2, 11)]".to_string(),
        ],
        "exactly the vectors whose swapped lanes differ are caught"
    );
}

// ---- the two-producer link ------------------------------------------------------

/// A Rust-producer client: its own copies of the carrier definitions (`pt`,
/// `shape`), a body-less typed declaration of each carrier symbol it calls,
/// one import row naming the Clean module by digest, and one body per call.
fn rust_client(clean: &Module, shape_layout: EnumLayoutDescriptor) -> Module {
    let mut mb = ModuleBuilder::new("rust_client");
    mb.set_default_producer(Producer::TRust);
    let pt = mb.add_struct(clean.structs[0].clone());
    let mut shape = clean.enums[0].clone();
    shape.layout = Some(shape_layout);
    let shape = mb.add_enum(shape);
    for (root, params) in [
        ("dot", vec![Ty::Struct(pt), Ty::Struct(pt)]),
        ("area", vec![Ty::Enum(shape)]),
    ] {
        let fty = mb.intern_func_type(FuncTy {
            params: params.clone(),
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        });
        let decl = mb
            .function(carrier_symbol(&Name::from_string(root)), fty)
            .build();
        let mut fb = mb.function(format!("use_{root}"), fty);
        fb.set_body_gate(BodyGate::Ungated);
        let entry = fb.create_block();
        let args: Vec<ValueId> = params
            .iter()
            .map(|t| fb.add_block_param(entry, t.clone()))
            .collect();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let r = fb.call(decl, args);
        fb.ret(vec![r]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = clean.target_info.clone();
    module
        .intern_import(
            ModuleImport::new(clean.name.clone(), clean.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    module
}

/// Two producers, one carrier: a Rust-producer module declaring the carrier
/// symbols with ITS OWN, structurally equal `Pt` / `Shape` definitions links
/// against the Clean module under `validate_linked_module`, which binds each
/// call edge to the authenticated dependency's export.
#[test]
fn a_rust_producer_links_the_typed_carrier() {
    let l = lowered();
    let client = rust_client(&l.module, l.module.enums[0].layout.clone().expect("layout"));
    assert!(
        validate_module(&client).is_empty(),
        "{:?}",
        validate_module(&client)
    );
    let deps = [l.module.clone()];
    let verdict = validate_linked_module(
        &client,
        &ModuleSet::new(deps.iter()),
        &RejectingModuleProofAuthority,
    );
    assert!(verdict.is_ok(), "{:?}", verdict.errors());

    // And the linked call RUNS: the Rust client's `use_area` / `use_dot` are
    // executed by the interpreter, each call to a body-less carrier
    // declaration served by the Clean module's typed wrapper (itself served
    // by the native helpers), and every result is the kernel-certified one.
    let dir = tempfile::tempdir().expect("tempdir");
    let (bin, index) = native_helpers(dir.path());
    let native = NativeHelpers { bin, index };
    let clean = interpretable(&l.module, &l.plan);
    let clean_side = CleanWrappers {
        module: &clean,
        native: &native,
    };
    let interp = Interpreter::with_module(&client).with_host(&clean_side);
    let mut ran = 0;
    for (f, args, want) in VECTORS
        .iter()
        .filter(|(f, ..)| matches!(*f, "area" | "dot"))
    {
        let func = client
            .functions
            .iter()
            .find(|g| g.name == format!("use_{f}"))
            .expect("client body");
        let sig = &client.func_types[func.ty.as_usize()];
        let values: Vec<InterpretValue> = args
            .iter()
            .zip(&sig.params)
            .map(|(a, t)| arg_value(*a, t))
            .collect();
        let out = interp
            .execute_function(func, values)
            .unwrap_or_else(|e| panic!("use_{f} {args:?}: {e}"));
        assert_eq!(out.host_calls, 1, "one call crosses into the Clean module");
        let [InterpretValue {
            kind: InterpretValueKind::Int(i),
            ..
        }] = out.returns.as_slice()
        else {
            panic!("use_{f} {args:?}: unexpected returns {:?}", out.returns)
        };
        assert_eq!(i.as_unsigned(), u128::from(*want), "use_{f} {args:?}");
        ran += 1;
    }
    assert_eq!(ran, 5, "every area / dot vector ran from the Rust side");
}

/// Serves a Rust client's call to a carrier symbol by running the Clean
/// module's typed wrapper of that symbol, at the Clean side's own parameter
/// types (the link test above proved them structurally equal).
struct CleanWrappers<'a> {
    module: &'a Module,
    native: &'a NativeHelpers,
}

impl HostCalls for CleanWrappers<'_> {
    fn call(
        &self,
        callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        _host: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        let func = self
            .module
            .functions
            .iter()
            .find(|g| g.name == callee.name && !g.blocks.is_empty())?;
        let sig = &self.module.func_types[func.ty.as_usize()];
        let values: Vec<InterpretValue> = args
            .iter()
            .zip(&sig.params)
            .map(|(a, t)| InterpretValue {
                ty: t.clone(),
                kind: a.kind.clone(),
            })
            .collect();
        Some(
            Interpreter::with_module(self.module)
                .with_host(self.native)
                .execute_function(func, values)
                .map(|out| out.returns),
        )
    }
}

/// NEGATIVE TWIN: a CONSISTENT descriptor that differs from the Clean
/// producer's (rustc may reorder fields: `rect`'s `w` after `h`) validates on
/// its own and is refused at linked validation, because the signatures are
/// not structurally equal.
#[test]
fn a_rust_producer_with_a_different_layout_is_refused_at_link() {
    let l = lowered();
    let mut reordered = l.module.enums[0].layout.clone().expect("layout");
    reordered.variant_field_offsets[1].reverse();
    let client = rust_client(&l.module, reordered);
    assert!(
        validate_module(&client).is_empty(),
        "the reordered descriptor is internally consistent: {:?}",
        validate_module(&client)
    );
    let deps = [l.module.clone()];
    let verdict = validate_linked_module(
        &client,
        &ModuleSet::new(deps.iter()),
        &RejectingModuleProofAuthority,
    );
    let area = carrier_symbol(&Name::from_string("area"));
    let errors = verdict.errors();
    assert!(!errors.is_empty(), "a layout disagreement must be refused");
    for e in errors {
        assert!(
            matches!(
                e,
                ValidationError::UnauthenticatedImport { site, detail, .. }
                    if *site == "call"
                        && detail.contains(&format!("call edge @{area}"))
                        && detail.contains("signature mismatch")
            ),
            "only the enum call edge is refused, as a signature mismatch: {errors:?}"
        );
    }
}
