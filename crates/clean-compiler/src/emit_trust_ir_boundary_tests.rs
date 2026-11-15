// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.9 — typed boundary carriers, the kernel-built half.
//!
//! A child of `emit_trust_ir::boundary`, so the `trust-ir-backend-lib` gate
//! leg (`-- emit_trust_ir`) runs it. The source-elaborated half (the proof
//! program's `area` / `dot`, the executable differential and the
//! two-producer link) is the child module `e2e`.
//!
//! Pinned here, over inductives built directly in the kernel:
//!
//! * the layout rule (`#[repr(C)]` structs; `#[repr(C, u8)]` enums, equal to
//!   trust-ir's canonical tagged union) and the carrier symbol's disjointness
//!   from every user symbol;
//! * the positive emission: a struct and an enum export each get a validated
//!   wrapper, the boxed body keeps its symbol and its `Ptr` signature, and the
//!   wrapper calls exactly the kernel-checked helpers;
//! * every `carrier/no-total-carrier` refusal arm, each by its named reason;
//! * the negative twin of the layout: an internally inconsistent descriptor
//!   on the emitted module is refused by trust-ir's own validator.

use super::*;
use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
use crate::pass_manager::{compile_lcnf_to_trust_ir_with_carrier_exports, PipelineConfig};
use clean_kernel::{Constructor, InductiveDecl, InductiveType};
use trust_ir::inst::Inst;
use trust_ir::Module;
use trust_ir_build::{validate_module, ValidationError};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn u64t() -> Expr {
    Expr::const_str("UInt64")
}

fn add_inductive(env: &mut Environment, ind: &str, ctors: &[(&str, Vec<Expr>)]) {
    let self_ty = Expr::const_str(ind);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name(ind),
            type_: Expr::type_(),
            constructors: ctors
                .iter()
                .map(|(c, fields)| Constructor {
                    name: name(&format!("{ind}.{c}")),
                    type_: fields
                        .iter()
                        .rev()
                        .fold(self_ty.clone(), |acc, f| Expr::arrow(f.clone(), acc)),
                })
                .collect(),
        }],
    })
    .unwrap_or_else(|e| panic!("inductive {ind} should register: {e:?}"));
}

/// The prelude plus `Pt` (structure), `Shape` (two variants), `Tree`
/// (recursive) and `NatBox` (a `Nat` field).
fn env() -> Environment {
    let mut env = Environment::with_prelude();
    add_inductive(&mut env, "Pt", &[("mk", vec![u64t(), u64t()])]);
    env.register_structure_fields(name("Pt"), vec![name("x"), name("y")])
        .expect("Pt fields register");
    add_inductive(
        &mut env,
        "Shape",
        &[("sq", vec![u64t()]), ("rect", vec![u64t(), u64t()])],
    );
    add_inductive(
        &mut env,
        "Tree",
        &[
            ("leaf", vec![]),
            ("node", vec![Expr::const_str("Tree"), u64t()]),
        ],
    );
    add_inductive(&mut env, "NatBox", &[("mk", vec![Expr::const_str("Nat")])]);
    env
}

/// `def <n> : <params> -> UInt64 := fun .. => 7` — a body that ignores its
/// arguments, so the decl compiles whatever the parameter types are.
fn def_const7(env: &mut Environment, n: &str, params: &[Expr]) -> Decl {
    let seven = Expr::app(Expr::const_str("UInt64.ofNat"), Expr::nat_lit(7));
    let (ty, value) = params.iter().rev().fold((u64t(), seven), |(t, v), p| {
        (
            Expr::pi(BinderInfo::Default, p.clone(), t),
            Expr::lam(BinderInfo::Default, p.clone(), v),
        )
    });
    env.add_decl(Declaration::Definition {
        name: name(n),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("{n} should type-check: {e:?}"));
    let info = env.get_const(&name(n)).expect("just added").clone();
    crate::to_lcnf::constant_to_decl(env, &info)
        .expect("lowers")
        .expect("has a body")
}

fn config() -> TrustIrConfig {
    TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

fn compile(
    env: &Environment,
    decls: &[Decl],
    exports: &[&str],
) -> Result<(Module, Vec<CarrierExport>), TrustIrError> {
    let exports: Vec<Name> = exports.iter().map(|e| name(e)).collect();
    match compile_lcnf_to_trust_ir_with_carrier_exports(
        decls,
        env,
        &PipelineConfig::default(),
        &config(),
        &exports,
    ) {
        Ok((module, _, plan)) => Ok((module, plan)),
        Err(crate::pass_manager::PipelineError::TrustIr(e)) => Err(e),
        Err(other) => panic!("unexpected pipeline error: {other}"),
    }
}

fn no_carrier_reason(result: Result<(Module, Vec<CarrierExport>), TrustIrError>) -> String {
    match result {
        Err(e @ TrustIrError::NoTotalCarrier { .. }) => {
            let text = e.to_string();
            assert!(text.contains(NO_TOTAL_CARRIER), "{text}");
            text
        }
        Err(other) => panic!("expected {NO_TOTAL_CARRIER}, got {other}"),
        Ok(_) => panic!("expected {NO_TOTAL_CARRIER}, got a module"),
    }
}

// ---- layout -----------------------------------------------------------------

#[test]
fn struct_carrier_is_repr_c() {
    use CarrierScalar::*;
    assert_eq!(c_layout(&[U64, U64]), (vec![0, 8], 16, 8));
    assert_eq!(c_layout(&[U8, U64, U16]), (vec![0, 8, 16], 24, 8));
    assert_eq!(c_layout(&[Bool, U32, U8]), (vec![0, 4, 8], 12, 4));
}

#[test]
fn enum_carrier_is_repr_c_u8() {
    use CarrierScalar::*;
    let shape = enum_layout(&[vec![U64], vec![U64, U64]]);
    assert_eq!(shape.encoding, EnumTagEncoding::Direct { tag_offset: 0 });
    assert_eq!((shape.size, shape.align), (24, 8));
    assert_eq!(shape.variant_field_offsets, vec![vec![8], vec![8, 16]]);
    // A u8-only payload sits right after the tag.
    let small = enum_layout(&[vec![U8], vec![]]);
    assert_eq!((small.size, small.align), (2, 1));
    assert_eq!(small.variant_field_offsets, vec![vec![1], vec![]]);
    // Field-less constructors only: the tag alone.
    let tags = enum_layout(&[vec![], vec![], vec![]]);
    assert_eq!((tags.size, tags.align), (1, 1));
}

#[test]
fn carrier_symbol_is_disjoint_from_every_user_symbol() {
    let area = name("area");
    let symbol = carrier_symbol(&area);
    assert_eq!(symbol, "__clean_typed_v1_carrier_area");
    // A user who NAMES a declaration exactly that gets it escaped.
    let forged = name(&symbol);
    assert_ne!(wire_name(&forged), symbol);
    assert!(wire_name(&forged).starts_with("__clean_typed_v1_a"));
    // And the boxed body keeps its own symbol.
    assert_eq!(wire_name(&area), "area");
}

// ---- positive emission ----------------------------------------------------------

#[test]
fn struct_and_enum_exports_get_validated_typed_wrappers() {
    let mut env = env();
    let decls = vec![
        def_const7(&mut env, "ptScore", &[Expr::const_str("Pt")]),
        def_const7(
            &mut env,
            "shapeScore",
            &[Expr::const_str("Shape"), Expr::const_str("UInt8")],
        ),
    ];
    let (module, plan) =
        compile(&env, &decls, &["ptScore", "shapeScore"]).expect("both exports have carriers");
    assert_eq!(validate_module(&module), Vec::<ValidationError>::new());
    assert_eq!(plan.len(), 2);
    assert_eq!(plan[0].helpers.len(), 1, "a structure has one arm");
    assert_eq!(plan[1].helpers.len(), 2, "Shape has two arms; UInt8 one");

    // The definitions: one repr(C) struct, one u8-tagged enum with a
    // normative descriptor.
    let [pt] = module.structs.as_slice() else {
        panic!("one struct: {:?}", module.structs)
    };
    assert_eq!(pt.name, "Pt");
    assert_eq!(pt.repr, StructRepr::C);
    assert_eq!(
        pt.fields
            .iter()
            .map(|f| (f.name.as_str(), f.offset))
            .collect::<Vec<_>>(),
        vec![("x", Some(0)), ("y", Some(8))]
    );
    let [shape] = module.enums.as_slice() else {
        panic!("one enum: {:?}", module.enums)
    };
    assert_eq!(shape.name, "Shape");
    assert_eq!(
        shape
            .variants
            .iter()
            .map(|v| v.name.as_str())
            .collect::<Vec<_>>(),
        ["sq", "rect"]
    );
    assert_eq!(shape.repr, Some(EnumTagRepr::U8));
    assert_eq!(
        shape.layout,
        Some(enum_layout(&[
            vec![CarrierScalar::U64],
            vec![CarrierScalar::U64, CarrierScalar::U64]
        ]))
    );

    // The boxed bodies keep their symbols and their boxed signatures.
    let func = |sym: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == sym)
            .unwrap_or_else(|| panic!("no function {sym}"))
    };
    let sig = |f: &trust_ir::Function| module.func_types[f.ty.as_usize()].clone();
    assert_eq!(sig(func("ptScore")).params, vec![Ty::Ptr]);
    assert_eq!(sig(func("shapeScore")).params, vec![Ty::Ptr, Ty::U8]);

    // The wrappers: typed parameters, a scalar result, the Ungated license,
    // the source as display path.
    let w = func("__clean_typed_v1_carrier_ptScore");
    assert_eq!(sig(w).params, vec![Ty::Struct(pt.id)]);
    assert_eq!(sig(w).returns, vec![Ty::U64]);
    assert_eq!(w.body_gate, Some(BodyGate::Ungated));
    assert_eq!(w.display_path.as_deref(), Some("ptScore"));
    let w = func("__clean_typed_v1_carrier_shapeScore");
    assert_eq!(sig(w).params, vec![Ty::Enum(shape.id), Ty::U8]);

    // The enum wrapper allocates nothing: no call except to its two helpers.
    let helper_syms: Vec<String> = plan[1].helpers.iter().map(|h| wire_name(&h.name)).collect();
    let mut called = Vec::new();
    for block in &w.blocks {
        for node in block.instructions() {
            if let Inst::Call { callee, .. } = &node.inst {
                called.push(module.functions[callee.as_usize()].name.clone());
            }
            assert!(
                !matches!(
                    node.inst,
                    Inst::HeapAlloc { .. } | Inst::Retain { .. } | Inst::Release { .. }
                ),
                "the wrapper must not allocate or count references"
            );
        }
    }
    called.sort();
    let mut want = helper_syms.clone();
    want.sort();
    assert_eq!(called, want);
    // Each helper is a real, bodied function of the module.
    for h in &helper_syms {
        assert!(!func(h).is_declaration(), "{h} has a body");
    }
}

// ---- refusals -------------------------------------------------------------------

#[test]
fn a_recursive_inductive_has_no_total_carrier() {
    let mut env = env();
    let decls = vec![def_const7(
        &mut env,
        "treeScore",
        &[Expr::const_str("Tree")],
    )];
    let why = no_carrier_reason(compile(&env, &decls, &["treeScore"]));
    assert!(why.contains("recursive"), "{why}");
}

#[test]
fn nat_has_no_total_carrier() {
    let mut env = env();
    let decls = vec![def_const7(&mut env, "natScore", &[Expr::const_str("Nat")])];
    let why = no_carrier_reason(compile(&env, &decls, &["natScore"]));
    assert!(why.contains("trust_bignum::Nat"), "{why}");
}

#[test]
fn a_structure_with_a_nat_field_has_no_total_carrier() {
    let mut env = env();
    let decls = vec![def_const7(
        &mut env,
        "boxScore",
        &[Expr::const_str("NatBox")],
    )];
    let why = no_carrier_reason(compile(&env, &decls, &["boxScore"]));
    assert!(why.contains("not a carrier scalar"), "{why}");
}

#[test]
fn a_carrier_typed_result_is_refused_until_unmarshalling_lands() {
    let mut env = env();
    let pt = Expr::const_str("Pt");
    let mk = Expr::apps(Expr::const_str("Pt.mk"), [Expr::bvar(0), Expr::bvar(0)]);
    env.add_decl(Declaration::Definition {
        name: name("diag"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, u64t(), pt),
        value: Expr::lam(BinderInfo::Default, u64t(), mk),
        is_reducible: false,
    })
    .expect("diag type-checks");
    let info = env.get_const(&name("diag")).unwrap().clone();
    let decls = vec![crate::to_lcnf::constant_to_decl(&env, &info)
        .unwrap()
        .unwrap()];
    let why = no_carrier_reason(compile(&env, &decls, &["diag"]));
    assert!(why.contains("RESULT is not carried yet"), "{why}");
}

#[test]
fn an_export_outside_the_slice_is_refused() {
    let mut env = env();
    let decls = vec![def_const7(&mut env, "ptScore", &[Expr::const_str("Pt")])];
    let why = no_carrier_reason(compile(&env, &decls, &["missing"]));
    assert!(why.contains("not among the compiled declarations"), "{why}");
}

#[test]
fn a_helper_name_collision_is_refused_by_the_kernel() {
    let mut env = env();
    let decls = vec![def_const7(&mut env, "ptScore", &[Expr::const_str("Pt")])];
    // A user declaration squatting on the first helper's name.
    def_const7(&mut env, "ptScore.__clean_carrier_in_0", &[]);
    let why = no_carrier_reason(compile(&env, &decls, &["ptScore"]));
    assert!(
        why.contains("the kernel refused marshal-in helper"),
        "{why}"
    );
}

#[test]
fn the_variant_product_is_bounded() {
    let mut env = env();
    let shape = Expr::const_str("Shape");
    // 2^7 = 128 > MAX_VARIANT_COMBINATIONS.
    let decls = vec![def_const7(&mut env, "many", &vec![shape; 7])];
    let why = no_carrier_reason(compile(&env, &decls, &["many"]));
    assert!(why.contains("constructor combinations"), "{why}");
}

// ---- the layout's negative twin (trust-ir's validator) --------------------------

/// MUTATION CONTROL for the descriptor: the emitted module validates (above);
/// the same module with one variant field moved onto the tag (an overlap) or
/// off its natural alignment is refused by trust-ir's own layout validation,
/// so the descriptor the producer writes is checked, not trusted.
#[test]
fn an_inconsistent_enum_descriptor_is_refused_by_trust_ir() {
    let mut env = env();
    let decls = vec![def_const7(
        &mut env,
        "shapeScore",
        &[Expr::const_str("Shape")],
    )];
    let (module, _) = compile(&env, &decls, &["shapeScore"]).expect("emits");
    assert!(validate_module(&module).is_empty());
    for (offset, reason) in [(0u64, "tag overlaps variant 1 field 0"), (9, "offset 9")] {
        let mut bad = module.clone();
        bad.enums[0]
            .layout
            .as_mut()
            .expect("descriptor")
            .variant_field_offsets[1][0] = offset;
        let errors = validate_module(&bad);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::ConstTypeMismatch { location, actual, .. }
                    if location == "enum.0 (Shape) layout" && actual == reason
            )),
            "rect.w at offset {offset} must be refused as `{reason}` on Shape's layout: \
             {errors:?}"
        );
    }
}

// ---- review: adversarial inputs the implementation was not written against -----

/// `def <n> : <params> -> <ret> := fun .. => <value>`, lowered.
fn def_const(env: &mut Environment, n: &str, params: &[Expr], ret: Expr, value: Expr) -> Decl {
    let (ty, value) = params.iter().rev().fold((ret, value), |(t, v), p| {
        (
            Expr::pi(BinderInfo::Default, p.clone(), t),
            Expr::lam(BinderInfo::Default, p.clone(), v),
        )
    });
    env.add_decl(Declaration::Definition {
        name: name(n),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("{n} should type-check: {e:?}"));
    let info = env.get_const(&name(n)).expect("just added").clone();
    crate::to_lcnf::constant_to_decl(env, &info)
        .expect("lowers")
        .expect("has a body")
}

/// REVIEW 1. Every carrier scalar the design names, at mixed widths: a
/// structure of `Bool` / `UInt8` / `UInt16` / `UInt32` / `UInt64` / `Float`
/// fields, a `Bool` parameter and a `Bool` result read back out of the
/// structure's `Bool` field. The kernel-built tests
/// above only ever used `UInt64` fields, so a lowering that spells `Bool` or
/// `Float` differently from the carrier would have refused a legitimate
/// export unnoticed. The wrapper must validate, the struct must carry the
/// `#[repr(C)]` offsets, and trust-ir's own layout of the struct must agree.
#[test]
fn review_every_carrier_scalar_crosses_at_its_repr_c_offset() {
    let mut env = env();
    let fields = ["Bool", "UInt64", "UInt8", "Float", "UInt16", "UInt32"];
    add_inductive(
        &mut env,
        "Mix",
        &[("mk", fields.iter().map(|f| Expr::const_str(f)).collect())],
    );
    let decls = vec![def_const(
        &mut env,
        "mixScore",
        &[Expr::const_str("Mix"), Expr::const_str("Bool")],
        Expr::const_str("Bool"),
        // `fun m _ => m.0`: the boxed body READS the `Bool` field back.
        Expr::proj(name("Mix"), 0, Expr::bvar(1)),
    )];
    // Before the review fix this was `Invalid([CallArgTypeMismatch {
    // callee: "clean_ctor_set_uint8", expected: "u8", actual: "bool" }])`: the
    // general back end handed a `Bool` to the one-byte setter (measured). The
    // getter had the mirror defect, returning the one-byte `U8` at a `Bool`
    // result; this body's `m.0` exercises the fixed reader.
    let (module, plan) = compile(&env, &decls, &["mixScore"]).expect("every scalar has a carrier");
    assert_eq!(validate_module(&module), Vec::<ValidationError>::new());
    let [mix] = module.structs.as_slice() else {
        panic!("one struct: {:?}", module.structs)
    };
    assert_eq!(
        mix.fields
            .iter()
            .map(|f| (f.ty.clone(), f.offset))
            .collect::<Vec<_>>(),
        vec![
            (Ty::Bool, Some(0)),
            (Ty::U64, Some(8)),
            (Ty::U8, Some(16)),
            (Ty::F64, Some(24)),
            (Ty::U16, Some(32)),
            (Ty::U32, Some(36)),
        ]
    );
    assert_eq!((mix.size, mix.align), (Some(40), Some(8)));
    for (j, off) in [0u64, 8, 16, 24, 32, 36].into_iter().enumerate() {
        assert_eq!(
            module
                .struct_field_offset_bits(mix.id, u32::try_from(j).unwrap())
                .ok(),
            Some(off * 8),
            "trust-ir's own layout of field {j}"
        );
    }
    let w = module
        .functions
        .iter()
        .find(|f| f.name == plan[0].symbol)
        .expect("wrapper");
    let sig = &module.func_types[w.ty.as_usize()];
    assert_eq!(sig.params, vec![Ty::Struct(mix.id), Ty::Bool]);
    assert_eq!(sig.returns, vec![Ty::Bool]);
}

/// REVIEW 2. An inductive whose constructors carry NO fields (`Color`), so
/// every marshal-in helper is NULLARY (`fun => colorScore Color.red`). A
/// zero-parameter helper is the one shape the pipeline might compile as a
/// closed constant rather than a function; the wrapper must still dispatch
/// to three real, bodied helper functions, and the enum is the tag alone.
#[test]
fn review_a_fieldless_enum_dispatches_to_nullary_helpers() {
    let mut env = env();
    add_inductive(
        &mut env,
        "Color",
        &[("red", vec![]), ("green", vec![]), ("blue", vec![])],
    );
    let decls = vec![def_const7(
        &mut env,
        "colorScore",
        &[Expr::const_str("Color")],
    )];
    let (module, plan) = compile(&env, &decls, &["colorScore"]).expect("Color has a carrier");
    assert_eq!(validate_module(&module), Vec::<ValidationError>::new());
    let [color] = module.enums.as_slice() else {
        panic!("one enum: {:?}", module.enums)
    };
    let layout = color.layout.as_ref().expect("descriptor");
    assert_eq!((layout.size, layout.align), (1, 1));
    assert_eq!(plan[0].helpers.len(), 3);
    for h in &plan[0].helpers {
        let f = module
            .functions
            .iter()
            .find(|f| f.name == wire_name(&h.name))
            .unwrap_or_else(|| panic!("helper {} is a function", h.name));
        assert!(!f.is_declaration(), "{} has a body", h.name);
        assert!(module.func_types[f.ty.as_usize()].params.is_empty());
    }
}

/// Serves each helper call by recording which helper ran with which scalar
/// arguments, and returns the helper's index in the plan.
struct RecordingHost {
    index: BTreeMap<String, usize>,
    calls: std::sync::Mutex<Vec<(usize, Vec<u128>)>>,
}

impl trust_ir::interpret::HostCalls for RecordingHost {
    fn call(
        &self,
        callee: &trust_ir::Function,
        _sig: &trust_ir::ty::FuncTy,
        args: &[trust_ir::interpret::InterpretValue],
        _host: &mut trust_ir::interpret::HostState,
    ) -> Option<trust_ir::interpret::InterpretResult<Vec<trust_ir::interpret::InterpretValue>>>
    {
        let k = *self.index.get(&callee.name)?;
        let raw = args
            .iter()
            .map(|a| match &a.kind {
                trust_ir::interpret::InterpretValueKind::Int(i) => i.as_unsigned(),
                other => panic!("helper argument is not a scalar: {other:?}"),
            })
            .collect();
        self.calls.lock().expect("lock").push((k, raw));
        Some(
            trust_ir::interpret::InterpretValue::int(Ty::U64, i128::try_from(k).expect("small"))
                .map(|v| vec![v]),
        )
    }
}

fn int_value(ty: Ty, v: u128) -> trust_ir::interpret::InterpretValue {
    let bits = match ty {
        Ty::U8 => 8,
        Ty::U64 => 64,
        ref other => panic!("no fixture value of {other}"),
    };
    trust_ir::interpret::InterpretValue {
        ty,
        kind: trust_ir::interpret::InterpretValueKind::Int(trust_ir::interpret::InterpretInt {
            bits,
            signed: false,
            raw: v,
        }),
    }
}

/// REVIEW 3. Several enum parameters, of two DIFFERENT types and one repeated
/// (`pair : Shape → Color → Pt → Shape → UInt64`, 2 · 3 · 1 · 2 = 12
/// combinations). The planner numbers helpers in mixed radix and the emitter
/// re-derives the same number while it nests switches; nothing else ties the
/// two together. Every one of the twelve tag combinations is RUN through the
/// wrapper in the interpreter (helpers served by a recording host), and the
/// helper that runs must be the one whose `choice` is exactly those tags, fed
/// exactly the active variants' fields in parameter order. A planner/emitter
/// disagreement — or a repeated enum registered twice — fails here.
#[test]
fn review_nested_enum_dispatch_calls_the_helper_of_exactly_the_active_variants() {
    let mut env = env();
    add_inductive(
        &mut env,
        "Color",
        &[("red", vec![]), ("green", vec![]), ("blue", vec![])],
    );
    let params = ["Shape", "Color", "Pt", "Shape"].map(Expr::const_str);
    let decls = vec![def_const7(&mut env, "pair", &params)];
    let (module, plan) = compile(&env, &decls, &["pair"]).expect("pair has a carrier");
    assert_eq!(validate_module(&module), Vec::<ValidationError>::new());
    assert_eq!(
        module.enums.len(),
        2,
        "Shape is registered once, Color once"
    );
    assert_eq!(module.structs.len(), 1);
    let export = &plan[0];
    assert_eq!(export.helpers.len(), 12);

    let mut interp_module = module.clone();
    let mut index = BTreeMap::new();
    for (k, h) in export.helpers.iter().enumerate() {
        index.insert(wire_name(&h.name), k);
    }
    for f in &mut interp_module.functions {
        if index.contains_key(&f.name) {
            f.blocks.clear();
        }
    }
    let host = RecordingHost {
        index,
        calls: std::sync::Mutex::new(Vec::new()),
    };
    let wrapper = interp_module
        .functions
        .iter()
        .find(|f| f.name == export.symbol)
        .expect("wrapper");
    let sig = interp_module.func_types[wrapper.ty.as_usize()].clone();
    let interp = trust_ir::interpret::Interpreter::with_module(&interp_module).with_host(&host);
    // Distinct field values per parameter, so an argument-order slip shows.
    let shape = |ty: &Ty, tag: usize, base: u128| {
        let fields: Vec<_> = (0..=tag as u128)
            .map(|j| int_value(Ty::U64, base + j))
            .collect();
        trust_ir::interpret::InterpretValue {
            ty: ty.clone(),
            kind: trust_ir::interpret::InterpretValueKind::Aggregate(
                std::iter::once(int_value(Ty::U8, tag as u128))
                    .chain(fields)
                    .collect(),
            ),
        }
    };
    for (k, helper) in export.helpers.iter().enumerate() {
        let c = &helper.choice;
        let args = vec![
            shape(&sig.params[0], c[0], 100),
            trust_ir::interpret::InterpretValue {
                ty: sig.params[1].clone(),
                kind: trust_ir::interpret::InterpretValueKind::Aggregate(vec![int_value(
                    Ty::U8,
                    c[1] as u128,
                )]),
            },
            trust_ir::interpret::InterpretValue {
                ty: sig.params[2].clone(),
                kind: trust_ir::interpret::InterpretValueKind::Aggregate(vec![
                    int_value(Ty::U64, 300),
                    int_value(Ty::U64, 301),
                ]),
            },
            shape(&sig.params[3], c[3], 400),
        ];
        let out = interp
            .execute_function(wrapper, args)
            .unwrap_or_else(|e| panic!("choice {c:?}: {e}"));
        assert_eq!(out.host_calls, 1, "choice {c:?}: one helper call");
        let (ran, got_args) = host.calls.lock().expect("lock").pop().expect("a call");
        assert_eq!(ran, k, "tags {c:?} must run helper {k}, ran {ran}");
        let mut want: Vec<u128> = (0..=c[0] as u128).map(|j| 100 + j).collect();
        want.extend([300, 301]);
        want.extend((0..=c[3] as u128).map(|j| 400 + j));
        assert_eq!(
            got_args, want,
            "choice {c:?}: the active variants' fields, in order"
        );
    }
}

#[path = "emit_trust_ir_boundary_e2e_tests.rs"]
mod e2e;
