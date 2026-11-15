// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored dependency-census fixtures, not executable-admission or source proofs.
//! Deliberately malformed rows test that diagnostics do not silently lose edges;
//! an empty refusal list is not a module-validation verdict.
//!
//! The second half tests the spawn census's reachability engine (design
//! 2026-09-29 §13): fixpoint soundness against a brute-force path search,
//! precision (only RUN paths claim a spawn), every pool rule, certificate
//! tampering, witnesses, thread closures, the trust-ir walk, and the trust-mc
//! tests it replaces, each restated as an engine fact graph.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use trust_ir::analysis::{ArgClass, CarriedKey, FnShape, MethodKey, PoolKey, PrincipalKey};
use trust_ir::function_dependencies::{
    CertificateError, DeclClassifier, DefinitionKey, DependencyNode as N,
    DependencyRefusalKind as R, DependencySite as S, EdgeClass, FunctionClass, Locality, NodeBody,
    NodeOrigin, ReachCensus, ReachDefect, ReachEdge, ReachFallback, ReachGraph, ReachNode,
    ReachNodeKind, ReachNodeSpec, ReachSite, RuntimeService, ServiceClass, Verdict,
    check_reach_certificate, inspect_function_dependencies, inspect_module_reachability,
};
use trust_ir::inst::{AssertKind, CastOp, SwitchCase};
use trust_ir::value::GlobalId;
// The primitive tests' names (Trust design 2026-10-02, "C1", §3.2).
use trust_ir::function_dependencies::{ModuleReachability, PrimitiveInvoke, PrimitiveSummary};
use trust_ir::{
    Block, BlockId, CallingConv, ClosureTy, ClosureTyId, Constant, EnumDef, EnumId, EnumVariant,
    FatPtrKind, FieldDef, FuncId, FuncTy, FuncTyId, Function, Global, Inst, InstrNode, Linkage,
    Module, ModuleCompleteness, Pred, PredId, RecordDef, RecordId, Space, StructDef, StructId,
    StructRepr, Ty, TyId, UnivId, Universe, ValueId, Visibility,
};

fn f(id: u32) -> FuncId {
    FuncId::new(id)
}
fn b(id: u32) -> BlockId {
    BlockId::new(id)
}
fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn ft(id: u32) -> FuncTyId {
    FuncTyId::new(id)
}

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}
fn ret() -> InstrNode {
    node(Inst::Return { values: vec![] })
}
fn function(id: u32, body: Vec<InstrNode>) -> Function {
    let mut fun = Function::new(f(id), format!("symbol_{id}"), ft(0), b(7));
    let mut block = Block::new(b(7));
    block.body = body;
    fun.blocks.push(block);
    fun
}
fn module(body: Vec<InstrNode>) -> Module {
    let mut m = Module::new("authored_dependency_census");
    m.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    m.functions.push(function(37, body));
    m
}
fn constant(value: Constant) -> InstrNode {
    node(Inst::Const { ty: Ty::Ptr, value }).with_result(v(11))
}
fn address(symbol: &str) -> Constant {
    Constant::SymbolAddr {
        symbol: symbol.into(),
        addend: 5,
    }
}
fn global(name: &str, initializer: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty: Ty::Ptr,
        mutable: false,
        initializer,
        linkage: Linkage::Internal,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}
fn field(ty: Ty) -> FieldDef {
    FieldDef {
        name: "field".into(),
        ty,
        offset: Some(0),
    }
}
fn structure(id: u32, ty: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("struct_{id}"),
        fields: vec![field(ty)],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn site(block: u32, index: usize) -> S {
    S::Instruction {
        function: f(37),
        block: b(block),
        index,
    }
}
fn refuses(m: &Module, kind: R) {
    let before = m.clone();
    let census = inspect_function_dependencies(m, f(37));
    assert!(
        census.refusals().iter().any(|r| r.kind == kind),
        "{kind:?}: {:?}",
        census.refusals()
    );
    assert!(std::ptr::eq(census.module(), m));
    assert_eq!(*m, before, "census must not repair or clear its input");
}

#[test]
fn sparse_ids_cycles_and_original_metadata_are_preserved() {
    let mut m = module(vec![
        node(Inst::Call {
            callee: f(101),
            args: vec![],
        }),
        ret(),
    ]);
    m.functions.insert(
        0,
        function(
            101,
            vec![
                node(Inst::Call {
                    callee: f(37),
                    args: vec![],
                }),
                ret(),
            ],
        ),
    );
    // An unrelated declaration is retained in the module but is not a root dependency.
    let mut unrelated = function(999, vec![]);
    unrelated.blocks.clear();
    m.functions.push(unrelated);
    m.completeness = Some(ModuleCompleteness::Complete);
    m.functions[1].display_path = Some("actual::diagnostic_name_only".into());
    m.functions[1].attrs.cold = true;
    m.files.push("original.rs".into());
    let before = m.clone();
    let c = inspect_function_dependencies(&m, f(37));
    assert_eq!(c.root(), f(37));
    assert!(std::ptr::eq(c.module(), &m));
    assert_eq!(
        c.nodes(),
        &BTreeSet::from([
            N::Function(f(37)),
            N::Function(f(101)),
            N::FunctionType(ft(0))
        ])
    );
    assert!(c.refusals().is_empty(), "{:?}", c.refusals());
    assert!(
        c.edges()
            .iter()
            .any(|e| e.site == site(7, 0) && e.target == N::Function(f(101)))
    );
    assert_eq!(m, before);
    let again = inspect_function_dependencies(&m, f(37));
    assert_eq!(c.nodes(), again.nodes());
    assert_eq!(c.edges(), again.edges());
    assert_eq!(c.refusals(), again.refusals());
}

#[test]
fn all_blocks_and_instruction_slots_including_dead_slots_are_scanned() {
    let mut m = module(vec![ret()]);
    let mut dead = Block::new(b(90));
    dead.body = vec![
        ret(),
        node(Inst::Call {
            callee: f(1234),
            args: vec![],
        }),
    ];
    m.functions[0].blocks.push(dead);
    let c = inspect_function_dependencies(&m, f(37));
    assert!(
        c.refusals()
            .iter()
            .any(|r| r.site == S::Definition(N::Function(f(1234)))
                && r.kind == R::Missing(N::Function(f(1234))))
    );
    assert!(
        c.edges()
            .iter()
            .any(|e| e.site == site(90, 1) && e.target == N::Function(f(1234)))
    );
}

#[test]
fn invoke_seqmap_and_nested_switch_constants_keep_their_targets() {
    let mut m = module(vec![
        node(Inst::Invoke {
            callee: f(101),
            args: vec![],
            normal_dest: b(7),
            normal_args: vec![],
            unwind_dest: b(7),
        }),
        node(Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(1),
            fwd: f(202),
        }),
        // Not a valid scalar switch case: even malformed input must retain this edge.
        node(Inst::Switch {
            value: v(1),
            default: b(7),
            default_args: vec![],
            exhaustive_enum_unreachable: false,
            cases: vec![SwitchCase {
                value: Constant::Array(vec![Constant::FnDef(f(303))]),
                target: b(7),
                args: vec![],
            }],
        }),
    ]);
    m.types.push(Ty::U8);
    for id in [101, 202, 303] {
        m.functions.push(function(id, vec![ret()]));
    }
    let c = inspect_function_dependencies(&m, f(37));
    for (index, target) in [(0, 101), (1, 202), (2, 303)] {
        assert!(
            c.edges()
                .iter()
                .any(|e| e.site == site(7, index) && e.target == N::Function(f(target)))
        );
    }
}

#[test]
fn nested_constant_families_and_global_initializer_cycles_are_followed() {
    let nested = Constant::Aggregate(vec![Constant::Array(vec![Constant::Vector(vec![
        Constant::Sequence(vec![Constant::Set(vec![Constant::Record(vec![(
            "capture".into(),
            Constant::Closure {
                func: f(101),
                captures: vec![Constant::FnDef(f(202)), address("first")],
            },
        )])])]),
    ])])]);
    let mut m = module(vec![
        constant(nested),
        node(Inst::GlobalAddr {
            global: GlobalId::new(1),
        }),
        ret(),
    ]);
    m.functions.extend([
        function(101, vec![ret()]),
        function(202, vec![ret()]),
        function(303, vec![ret()]),
    ]);
    m.globals = vec![
        global(
            "first",
            Some(Constant::Aggregate(vec![
                address("second"),
                address("symbol_303"),
            ])),
        ),
        global("second", Some(address("first"))),
    ];
    let before = m.clone();
    let c = inspect_function_dependencies(&m, f(37));
    for target in [
        N::Function(f(101)),
        N::Function(f(202)),
        N::Function(f(303)),
        N::Global(GlobalId::new(0)),
        N::Global(GlobalId::new(1)),
    ] {
        assert!(c.nodes().contains(&target), "{target:?}");
    }
    assert!(c.refusals().is_empty(), "{:?}", c.refusals());
    assert_eq!(
        m, before,
        "nonzero relocation addends must not be normalized"
    );
}

#[test]
fn signatures_named_types_closure_captures_and_slice_elements_reach_a_fixpoint() {
    let mut m = module(vec![
        node(Inst::Undef {
            ty: Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        }),
        ret(),
    ]);
    m.types = vec![
        Ty::Struct(StructId::new(81)),
        Ty::Tuple(vec![
            Ty::U8,
            Ty::Ref(Box::new(Ty::Struct(StructId::new(81)))),
        ]),
    ];
    m.structs = vec![structure(81, Ty::Enum(EnumId::new(67)))];
    m.enums = vec![EnumDef::new(
        EnumId::new(67),
        "sum",
        vec![EnumVariant {
            name: "only".into(),
            fields: vec![Ty::Record(RecordId::new(53))],
            field_names: vec![],
        }],
    )];
    m.records = vec![RecordDef {
        id: RecordId::new(53),
        name: "record".into(),
        fields: vec![field(Ty::Closure(ClosureTyId::new(0)))],
    }];
    m.closure_types.push(ClosureTy {
        func: ft(1),
        captures: vec![Ty::Array(TyId::new(1), 3)],
    });
    m.func_types.push(FuncTy {
        params: vec![Ty::PtrConst(Box::new(Ty::Struct(StructId::new(81))))],
        returns: vec![Ty::Func(ft(0))],
        abi: None,
        is_vararg: false,
    });
    m.functions[0].blocks[0]
        .params
        .push((v(7), Ty::Func(ft(1))));
    let c = inspect_function_dependencies(&m, f(37));
    for target in [
        N::Type(TyId::new(0)),
        N::Type(TyId::new(1)),
        N::Struct(StructId::new(81)),
        N::Enum(EnumId::new(67)),
        N::Record(RecordId::new(53)),
        N::ClosureType(ClosureTyId::new(0)),
        N::FunctionType(ft(1)),
    ] {
        assert!(c.nodes().contains(&target), "{target:?}");
    }
    assert!(c.refusals().is_empty(), "{:?}", c.refusals());
}

#[test]
fn refinement_predicate_and_universe_references_are_not_dropped() {
    let mut m = module(vec![
        node(Inst::Undef {
            ty: Ty::Refine(TyId::new(0), PredId::new(2)),
        }),
        ret(),
    ]);
    m.types.push(Ty::U64);
    // These deliberately noncanonical extensions test reference inventory, not validity.
    m.predicates = vec![
        Pred::FiniteSet(vec![Constant::FnDef(f(101))]),
        Pred::InUniverse(UnivId::new(0), Space::Member),
        Pred::Conj(vec![PredId::new(0), PredId::new(1)]),
    ];
    m.universes
        .push(Universe::Members(vec![Constant::Array(vec![
            Constant::FnDef(f(202)),
        ])]));
    m.functions
        .extend([function(101, vec![ret()]), function(202, vec![ret()])]);
    let c = inspect_function_dependencies(&m, f(37));
    for target in [
        N::Predicate(PredId::new(0)),
        N::Predicate(PredId::new(1)),
        N::Predicate(PredId::new(2)),
        N::Universe(UnivId::new(0)),
        N::Function(f(101)),
        N::Function(f(202)),
    ] {
        assert!(c.nodes().contains(&target), "{target:?}");
    }
    m.predicates[2] = Pred::Disj(vec![PredId::new(2), PredId::new(99)]);
    refuses(&m, R::Missing(N::Predicate(PredId::new(99))));
}

#[test]
fn missing_and_ambiguous_function_id_never_select_an_arbitrary_body() {
    let mut m = module(vec![
        node(Inst::Call {
            callee: f(101),
            args: vec![],
        }),
        ret(),
    ]);
    refuses(&m, R::Missing(N::Function(f(101))));
    let missing_root = inspect_function_dependencies(&m, f(555));
    assert!(
        missing_root
            .refusals()
            .iter()
            .any(|r| r.site == S::Definition(N::Function(f(555)))
                && r.kind == R::Missing(N::Function(f(555))))
    );
    assert!(
        missing_root
            .edges()
            .iter()
            .any(|e| e.site == S::Root && e.target == N::Function(f(555)))
    );
    m.functions
        .extend([function(101, vec![ret()]), function(101, vec![ret()])]);
    refuses(&m, R::Ambiguous(N::Function(f(101))));
    m.functions.push(function(37, vec![ret()]));
    refuses(&m, R::Ambiguous(N::Function(f(37))));
}

#[test]
fn sparse_named_type_duplicates_and_missing_table_entries_are_refused() {
    for (ty, target) in [
        (Ty::Struct(StructId::new(81)), N::Struct(StructId::new(81))),
        (Ty::Enum(EnumId::new(67)), N::Enum(EnumId::new(67))),
        (Ty::Record(RecordId::new(53)), N::Record(RecordId::new(53))),
        (
            Ty::Closure(ClosureTyId::new(4)),
            N::ClosureType(ClosureTyId::new(4)),
        ),
        (Ty::Array(TyId::new(4), 1), N::Type(TyId::new(4))),
        (Ty::Func(ft(4)), N::FunctionType(ft(4))),
    ] {
        let mut m = module(vec![node(Inst::Undef { ty }), ret()]);
        refuses(&m, R::Missing(target));
        match target {
            N::Struct(id) => m.structs = vec![structure(id.index(), Ty::U8); 2],
            N::Enum(id) => m.enums = vec![EnumDef::new(id, "duplicate", vec![]); 2],
            N::Record(id) => {
                m.records = vec![
                    RecordDef {
                        id,
                        name: "duplicate".into(),
                        fields: vec![]
                    };
                    2
                ]
            }
            _ => continue,
        }
        refuses(&m, R::Ambiguous(target));
    }
}

#[test]
fn external_bodies_and_missing_global_storage_are_explicit_frontiers() {
    let mut m = module(vec![
        node(Inst::Call {
            callee: f(101),
            args: vec![],
        }),
        node(Inst::GlobalAddr {
            global: GlobalId::new(0),
        }),
        ret(),
    ]);
    let mut declaration = function(101, vec![]);
    declaration.blocks.clear();
    m.functions.push(declaration);
    refuses(&m, R::BodylessFunction(f(101)));
    refuses(&m, R::Missing(N::Global(GlobalId::new(0))));
    m.globals.push(global("external_storage", None));
    refuses(&m, R::MissingGlobalInitializer(GlobalId::new(0)));
}

#[test]
fn symbol_resolution_refuses_missing_duplicate_and_cross_kind_names() {
    let mut m = module(vec![constant(address("collision")), ret()]);
    refuses(&m, R::UnresolvedSymbol("collision".into()));
    m.globals = vec![global("collision", Some(Constant::Int(0))); 2];
    refuses(&m, R::AmbiguousSymbol("collision".into()));
    m.globals.truncate(1);
    let mut callee = function(101, vec![ret()]);
    callee.name = "collision".into();
    m.functions.push(callee.clone());
    refuses(&m, R::AmbiguousSymbol("collision".into()));
    m.globals.clear();
    callee.id = f(202);
    m.functions.push(callee);
    refuses(&m, R::AmbiguousSymbol("collision".into()));
}

fn indirect_module() -> Module {
    let mut m = module(vec![
        node(Inst::Const {
            ty: Ty::Func(ft(0)),
            value: Constant::FnDef(f(101)),
        })
        .with_result(v(9)),
        node(Inst::Copy {
            ty: Ty::Func(ft(0)),
            operand: v(9),
        })
        .with_result(v(17)),
        node(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: Ty::Func(ft(0)),
            dst_ty: Ty::Ptr,
            operand: v(17),
        })
        .with_result(v(23)),
        node(Inst::CallIndirect {
            callee: v(23),
            sig: ft(0),
            args: vec![],
            calling_conv: CallingConv::C,
        }),
        ret(),
    ]);
    m.functions.push(function(101, vec![ret()]));
    m
}

#[test]
fn exact_typed_indirect_chain_resolves_but_signature_and_convention_changes_refuse() {
    let m = indirect_module();
    let c = inspect_function_dependencies(&m, f(37));
    assert!(c.refusals().is_empty(), "{:?}", c.refusals());
    assert!(
        c.edges()
            .iter()
            .any(|e| e.site == site(7, 3) && e.target == N::Function(f(101)))
    );
    for mode in 0..3 {
        let mut changed = m.clone();
        changed.func_types.push(changed.func_types[0].clone());
        if let Inst::CallIndirect {
            sig, calling_conv, ..
        } = &mut changed.functions[0].blocks[0].body[3].inst
        {
            if mode == 0 {
                *sig = ft(1);
            }
            if mode == 2 {
                *calling_conv = CallingConv::Rust;
            }
        } else {
            panic!("fixture call changed");
        }
        if mode == 1 {
            changed.functions[1].ty = ft(1);
        }
        refuses(&changed, R::IndirectSignatureMismatch);
    }
}

#[test]
fn dynamic_closure_forward_duplicate_and_dead_indirect_uses_refuse() {
    for mode in 0..5 {
        let mut m = indirect_module();
        match mode {
            0 => m.functions[0].blocks[0].params.push((v(23), Ty::Ptr)),
            1 => m.functions[0].blocks[0].body.swap(2, 3),
            2 => {
                m.functions[0].blocks[0].body[0].inst = Inst::Const {
                    ty: Ty::Closure(ClosureTyId::new(0)),
                    value: Constant::Closure {
                        func: f(101),
                        captures: vec![],
                    },
                }
            }
            3 => m.functions[0].blocks[0].body[2].inst = Inst::NullPtr,
            4 => {
                let call = m.functions[0].blocks[0].body[3].clone();
                let mut dead = Block::new(b(90));
                dead.body = vec![call, ret()];
                m.functions[0].blocks.push(dead);
            }
            _ => unreachable!(),
        }
        m.closure_types.push(ClosureTy::bare(ft(0)));
        refuses(&m, R::IndirectCall);
    }
}

#[test]
fn opaque_operations_types_global_assembly_and_bad_block_identity_are_visible() {
    let mut m = module(vec![
        node(Inst::DialectOp(Box::new(
            trust_ir::dialect::DialectInst::new("opaque", "call"),
        ))),
        ret(),
    ]);
    refuses(&m, R::OpaqueDialectOperation);
    for ty in [
        Ty::Error,
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 9 }),
        Ty::handle("Nat", "runtime::Nat"),
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("opaque", "type", 1))),
    ] {
        let m = module(vec![node(Inst::Undef { ty }), ret()]);
        refuses(&m, R::OpaqueType);
    }
    m.global_asm.push("opaque assembly retained".into());
    refuses(&m, R::GlobalAssembly);
    m.functions[0].blocks.push(Block::new(b(7)));
    refuses(&m, R::AmbiguousBlock(b(7)));
    m.functions[0].entry = b(404);
    refuses(&m, R::MissingEntryBlock(b(404)));
}

#[test]
fn drop_is_refused_as_an_implicit_destructor_not_silently_dropped() {
    let m = module(vec![
        node(Inst::Drop {
            ty: Ty::Struct(StructId::new(81)),
            ptr: v(1),
        }),
        ret(),
    ]);
    let c = inspect_function_dependencies(&m, f(37));
    assert!(
        c.refusals().iter().any(|r| r.site == site(7, 0)
            && r.kind == R::ImplicitDestructor(Ty::Struct(StructId::new(81)))),
        "{:?}",
        c.refusals()
    );
}

/// Amendment D (§20): a drop RESOLVED through the drop-glue table is a call
/// edge to its glue, and the glue is walked like any callee.
#[test]
fn a_resolved_drop_is_a_call_edge_to_its_glue() {
    let dropped = Ty::Struct(StructId::new(81));
    let mut m = module(vec![
        node(Inst::Drop {
            ty: dropped.clone(),
            ptr: v(1),
        }),
        node(Inst::DropInvoke {
            ty: dropped.clone(),
            ptr: v(1),
            normal_dest: b(7),
            normal_args: vec![],
            unwind_dest: b(7),
        }),
    ]);
    m.functions.push(function(5, vec![ret()]));
    m.set_drop_glue(dropped, f(5)).unwrap();
    let c = inspect_function_dependencies(&m, f(37));
    for index in [0, 1] {
        assert!(
            c.edges()
                .iter()
                .any(|e| e.site == site(7, index) && e.target == N::Function(f(5))),
            "drop {index} must reach its glue: {:?}",
            c.edges()
        );
    }
    assert!(
        !c.refusals()
            .iter()
            .any(|r| matches!(r.kind, R::ImplicitDestructor(_))),
        "{:?}",
        c.refusals()
    );
}

/// Without a row, the same drop is still an implicit destructor: refused,
/// never silently dropped.
#[test]
fn an_unresolved_drop_is_still_an_implicit_destructor() {
    let dropped = Ty::Struct(StructId::new(81));
    let mut m = module(vec![
        node(Inst::Drop {
            ty: dropped.clone(),
            ptr: v(1),
        }),
        ret(),
    ]);
    m.functions.push(function(5, vec![ret()]));
    // A row for ANOTHER type resolves nothing here.
    m.set_drop_glue(Ty::Struct(StructId::new(82)), f(5))
        .unwrap();
    let c = inspect_function_dependencies(&m, f(37));
    assert!(
        c.refusals()
            .iter()
            .any(|r| r.site == site(7, 0) && r.kind == R::ImplicitDestructor(dropped.clone())),
        "{:?}",
        c.refusals()
    );
}

// ===========================================================================
// The reachability engine, on adapter facts
// ===========================================================================

/// An engine fact graph with named MIR-lane nodes.
struct Facts {
    graph: ReachGraph,
    names: BTreeMap<&'static str, ReachNode>,
    sites: u64,
}

impl Facts {
    fn new() -> Self {
        Self {
            graph: ReachGraph::new(),
            names: BTreeMap::new(),
            sites: 0,
        }
    }

    fn add(
        &mut self,
        name: &'static str,
        definition: u128,
        locality: Locality,
        body: NodeBody,
    ) -> ReachNode {
        let id = u32::try_from(self.names.len()).expect("small");
        let node = self.graph.add_node(ReachNodeSpec {
            origin: NodeOrigin::Mir(id),
            definition: Some(DefinitionKey(definition)),
            locality,
            body,
        });
        assert!(self.names.insert(name, node).is_none(), "{name} twice");
        node
    }

    fn next_definition(&self) -> u128 {
        1000 + self.names.len() as u128
    }

    fn local(&mut self, name: &'static str) -> ReachNode {
        self.add(
            name,
            self.next_definition(),
            Locality::Local,
            NodeBody::Walked,
        )
    }

    fn external(&mut self, name: &'static str) -> ReachNode {
        self.add(
            name,
            self.next_definition(),
            Locality::External,
            NodeBody::Walked,
        )
    }

    fn seed(&mut self, name: &'static str) -> ReachNode {
        self.add(
            name,
            self.next_definition(),
            Locality::External,
            NodeBody::Seed,
        )
    }

    fn foreign(&mut self, name: &'static str) -> ReachNode {
        self.add(
            name,
            self.next_definition(),
            Locality::External,
            NodeBody::Opaque,
        )
    }

    fn primitive(&mut self, name: &'static str) -> ReachNode {
        self.add(
            name,
            self.next_definition(),
            Locality::External,
            NodeBody::Primitive,
        )
    }

    fn n(&self, name: &str) -> ReachNode {
        self.names[name]
    }

    fn site(&mut self) -> ReachSite {
        self.sites += 1;
        ReachSite::Mir(self.sites)
    }

    fn edge(&mut self, from: &str, to: &str, class: EdgeClass, via_drop: bool) {
        let site = self.site();
        let (from, to) = (self.n(from), self.n(to));
        self.graph.add_edge(from, to, class, site, via_drop);
    }

    fn run(&mut self, from: &str, to: &str) {
        self.edge(from, to, EdgeClass::Run, false);
    }

    fn drop_glue(&mut self, from: &str, to: &str) {
        self.edge(from, to, EdgeClass::Run, true);
    }

    fn unknown(&mut self, from: &str, reason: R) {
        let site = self.site();
        let from = self.n(from);
        self.graph
            .add_unknown(from, reason, EdgeClass::Run, site, false);
    }

    fn create(&mut self, creator: &str, member: &str, key: PoolKey, confined: bool) {
        let site = self.site();
        let (creator, member) = (self.n(creator), self.n(member));
        self.graph.add_create(creator, member, key, confined, site);
    }

    fn invoke(&mut self, node: &str, key: PoolKey) {
        self.invoke_carrying(node, key, Vec::new());
    }

    fn invoke_carrying(&mut self, node: &str, key: PoolKey, carried: Vec<CarriedKey>) {
        let site = self.site();
        let node = self.n(node);
        self.graph.add_invoke(node, key, carried, site, false);
    }

    fn handoff(&mut self, node: &str, callee: &str, carried: Vec<CarriedKey>) {
        let site = self.site();
        let (node, callee) = (self.n(node), self.n(callee));
        self.graph.add_handoff(node, callee, carried, site, false);
    }

    fn solve(self) -> Solved {
        let census = self.graph.solve();
        assert_eq!(census.fallback(), None);
        assert_eq!(
            check_reach_certificate(census.expanded(), census.certificate()),
            Ok(())
        );
        Solved {
            census,
            names: self.names,
        }
    }
}

struct Solved {
    census: ReachCensus,
    names: BTreeMap<&'static str, ReachNode>,
}

impl Solved {
    fn n(&self, name: &str) -> ReachNode {
        self.names[name]
    }

    fn verdict(&self, name: &str) -> Verdict {
        self.census.verdict(self.n(name))
    }

    fn verdicts(&self, expected: &[(&str, Verdict)]) {
        for (name, verdict) in expected {
            assert_eq!(self.verdict(name), *verdict, "{name}");
        }
    }

    /// The witness's nodes, by name (a sink is `"<sink>"`).
    fn witness_names(&self, name: &str) -> Vec<String> {
        let witness = self
            .census
            .witness(self.n(name))
            .expect("a refusal has a witness");
        let by_node: BTreeMap<ReachNode, &str> = self.names.iter().map(|(k, v)| (*v, *k)).collect();
        witness
            .path
            .iter()
            .map(|edge| {
                by_node
                    .get(&edge.to)
                    .map_or("<sink>".to_owned(), |name| (*name).to_owned())
            })
            .collect()
    }
}

/// The reason of the sink a node's witness ends at, if it ends at one.
fn sink_reason(census: &ReachCensus, node: ReachNode) -> Option<R> {
    let last = census.witness(node)?.path.last()?.to;
    match census.expanded().node(last)? {
        ReachNodeKind::Sink(reason) => Some(reason.clone()),
        // A witness looks through hubs, so it never ends at one.
        ReachNodeKind::Program(_) | ReachNodeKind::Hub => None,
    }
}

fn fn_key(params: &[ArgClass]) -> PoolKey {
    PoolKey::Fn(FnShape {
        abi: Some(0),
        variadic: Some(false),
        params: Some(params.to_vec()),
    })
}

fn dyn_method(principal: u64, method: u64) -> PoolKey {
    PoolKey::DynMethod {
        principal: PrincipalKey(principal),
        method: MethodKey(method),
    }
}

/// The verdict table (design §5.5): each reachability admits more edge
/// classes than the one before, PARAM is admitted by none, and only a RUN
/// path claims a spawn.
#[test]
fn verdicts_follow_the_admitted_edge_classes_and_only_run_claims_a_spawn() {
    let mut g = Facts::new();
    g.seed("spawn");
    for name in [
        "runs",
        "names",
        "reads",
        "calls_namer",
        "names_namer",
        "param",
        "sink_caller",
        "names_sink_caller",
        "quiet",
        "invoker",
        "member",
    ] {
        g.local(name);
    }
    g.run("runs", "spawn");
    g.edge("names", "spawn", EdgeClass::Create, false);
    g.edge("reads", "runs", EdgeClass::Read, false);
    g.run("calls_namer", "names");
    g.edge("names_namer", "names", EdgeClass::Create, false);
    g.edge("param", "runs", EdgeClass::Param, false);
    g.unknown("sink_caller", R::UnresolvedExtern);
    g.edge("names_sink_caller", "sink_caller", EdgeClass::Create, false);
    g.run("member", "spawn");
    g.create("names", "member", fn_key(&[]), false);
    g.invoke("invoker", fn_key(&[]));
    let s = g.solve();
    s.verdicts(&[
        ("spawn", Verdict::Spawns),
        ("runs", Verdict::Spawns),
        ("names", Verdict::Escapes),
        ("reads", Verdict::Escapes),
        ("calls_namer", Verdict::Escapes),
        ("names_namer", Verdict::Escapes),
        ("param", Verdict::Quiet),
        ("sink_caller", Verdict::Unknown),
        ("names_sink_caller", Verdict::Unknown),
        ("quiet", Verdict::Quiet),
        ("invoker", Verdict::Indirect),
    ]);
    for (name, node) in &s.names {
        assert_eq!(
            s.census.verdict(*node).claims_spawn(),
            ["spawn", "runs", "member"].contains(name),
            "{name}"
        );
    }
    assert_eq!(s.witness_names("calls_namer"), ["names", "spawn"]);
    assert_eq!(s.witness_names("sink_caller"), ["<sink>"]);
    assert_eq!(s.witness_names("invoker"), ["member", "spawn"]);
}

/// R1 and the per-definition join (c04): the identity instance reaches the
/// seed only through PARAM and stays QUIET; `go::<A>` spawns, `go::<B>` does
/// not, and the definition reads SPAWNS via `go::<A>`.
#[test]
fn param_only_reach_is_quiet_and_concrete_instances_join_their_definition() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.add("go<T>", 7, Locality::Local, NodeBody::Walked);
    g.add("go::<A>", 7, Locality::Local, NodeBody::Walked);
    g.add("go::<B>", 7, Locality::Local, NodeBody::Walked);
    g.add("only_identity<T>", 8, Locality::Local, NodeBody::Walked);
    g.local("<A as Run>::run");
    g.local("<B as Run>::run");
    g.run("<A as Run>::run", "spawn");
    g.edge("go<T>", "<A as Run>::run", EdgeClass::Param, false);
    g.run("go::<A>", "<A as Run>::run");
    g.run("go::<B>", "<B as Run>::run");
    g.edge(
        "only_identity<T>",
        "<A as Run>::run",
        EdgeClass::Param,
        false,
    );
    let s = g.solve();
    s.verdicts(&[
        ("go<T>", Verdict::Quiet),
        ("go::<A>", Verdict::Spawns),
        ("go::<B>", Verdict::Quiet),
        ("only_identity<T>", Verdict::Quiet),
    ]);
    assert_eq!(
        s.census.definition_verdict(DefinitionKey(7)),
        Some(Verdict::Spawns)
    );
    assert_eq!(
        s.census.definition_verdict(DefinitionKey(8)),
        Some(Verdict::Quiet)
    );
    assert_eq!(s.census.definition_verdict(DefinitionKey(99)), None);
}

/// A tiny deterministic generator (no external dependency).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

/// A solved random fact graph, with what the pool invariants need.
struct RandomCensus {
    census: ReachCensus,
    /// Nodes with an invoke fact.
    invokers: Vec<ReachNode>,
    /// Whether the adapter added an UNKNOWN sink.
    adapter_sink: bool,
}

/// A random fact graph that has no defect: edges leave only non-seed program
/// nodes, pool facts use a handful of keys, and some calls hand keys to
/// external code.
fn random_census(rng: &mut Rng) -> RandomCensus {
    let mut graph = ReachGraph::new();
    let count = 2 + rng.below(30);
    let mut nodes = Vec::new();
    let mut bodies = Vec::new();
    for id in 0..count {
        // A primitive is an ordinary node to the solver: the fixpoint,
        // certificate and tamper tests below cover it as they cover walked
        // code.
        let body = match rng.below(10) {
            0 => NodeBody::Seed,
            1 => NodeBody::Opaque,
            2 => NodeBody::Primitive,
            _ => NodeBody::Walked,
        };
        let locality = if rng.chance(70) {
            Locality::Local
        } else {
            Locality::External
        };
        nodes.push(graph.add_node(ReachNodeSpec {
            origin: NodeOrigin::Mir(id as u32),
            definition: Some(DefinitionKey(rng.below(count / 2 + 1) as u128)),
            locality,
            body,
        }));
        bodies.push(body);
    }
    let sources: Vec<usize> = (0..count)
        .filter(|i| bodies[*i] != NodeBody::Seed)
        .collect();
    let mut invokers = Vec::new();
    let sinks = if sources.is_empty() { 0 } else { rng.below(4) };
    if sources.is_empty() {
        return RandomCensus {
            census: graph.solve(),
            invokers,
            adapter_sink: false,
        };
    }
    let keys = [
        fn_key(&[]),
        fn_key(&[ArgClass::Int(32)]),
        dyn_method(1, 1),
        dyn_method(2, 1),
        PoolKey::DynDrop(PrincipalKey(1)),
    ];
    let classes = [
        EdgeClass::Run,
        EdgeClass::Create,
        EdgeClass::Read,
        EdgeClass::Param,
    ];
    let mut site = 0;
    let mut next_site = || {
        site += 1;
        ReachSite::Mir(site)
    };
    for _ in 0..rng.below(count * 3) {
        let from = nodes[sources[rng.below(sources.len())]];
        let to = nodes[rng.below(count)];
        let class = classes[rng.below(classes.len())];
        graph.add_edge(from, to, class, next_site(), rng.chance(20));
    }
    for _ in 0..sinks {
        let from = nodes[sources[rng.below(sources.len())]];
        graph.add_unknown(
            from,
            R::UnresolvedExtern,
            EdgeClass::Run,
            next_site(),
            false,
        );
    }
    for _ in 0..rng.below(count) {
        let creator = nodes[sources[rng.below(sources.len())]];
        let member = nodes[rng.below(count)];
        let key = keys[rng.below(keys.len())].clone();
        if rng.chance(50) {
            graph.add_create(creator, member, key, rng.chance(40), next_site());
        } else {
            graph.add_pool_member(member, key, rng.chance(40));
        }
    }
    for _ in 0..rng.below(count) {
        let node = nodes[sources[rng.below(sources.len())]];
        let key = keys[rng.below(keys.len())].clone();
        let carried = match rng.below(10) {
            0..=2 => vec![CarriedKey::AnyFn],
            3 => vec![CarriedKey::Laundered],
            _ => Vec::new(),
        };
        graph.add_invoke(node, key, carried, next_site(), rng.chance(10));
        invokers.push(node);
    }
    for _ in 0..rng.below(3) {
        let node = nodes[sources[rng.below(sources.len())]];
        let callee = nodes[rng.below(count)];
        let carried = match rng.below(4) {
            0 => vec![CarriedKey::Any],
            1 => vec![CarriedKey::Principal(PrincipalKey(1))],
            2 => vec![CarriedKey::Laundered],
            _ => vec![CarriedKey::Key(fn_key(&[]))],
        };
        graph.add_handoff(node, callee, carried, next_site(), false);
    }
    match rng.below(20) {
        0..=2 => graph.add_launder(next_site()),
        // A keyed LAUNDER (design §10, "typed LAUNDER").
        3..=5 => {
            let key = keys[rng.below(keys.len())].clone();
            graph.add_launder_keys(next_site(), vec![CarriedKey::Key(key)]);
        }
        _ => {}
    }
    if rng.chance(30) {
        graph.add_upcast(PrincipalKey(2), PrincipalKey(1));
    }
    if rng.chance(20) {
        graph.add_lifetime_erase(PrincipalKey(1));
    }
    RandomCensus {
        census: graph.solve(),
        invokers,
        adapter_sink: sinks > 0,
    }
}

fn kind(census: &ReachCensus, node: usize) -> &ReachNodeKind {
    census.expanded().nodes().nth(node).expect("in range").1
}

fn is_seed(census: &ReachCensus, node: usize) -> bool {
    matches!(
        kind(census, node),
        ReachNodeKind::Program(ReachNodeSpec {
            body: NodeBody::Seed,
            ..
        })
    )
}

fn is_sink(census: &ReachCensus, node: usize) -> bool {
    matches!(kind(census, node), ReachNodeKind::Sink(_))
}

/// Forward breadth-first distance from `node` to a base of `level` over the
/// edges `level` admits, straight from the design's table: SPAWNS admits
/// RUN; ESCAPES adds CREATE and READ; INDIRECT adds APPROX; UNKNOWN admits
/// the same and also ends at a sink. PARAM is never admitted. The edges are
/// the logical ones: a derived edge is itself, not its two hops through a
/// hub.
fn reference_distance(
    census: &ReachCensus,
    edges: &[ReachEdge],
    node: usize,
    level: Verdict,
) -> Option<usize> {
    let admitted = |class: EdgeClass| match level {
        Verdict::Spawns => class == EdgeClass::Run,
        Verdict::Escapes => matches!(class, EdgeClass::Run | EdgeClass::Create | EdgeClass::Read),
        Verdict::Indirect | Verdict::Unknown => class != EdgeClass::Param,
        Verdict::Quiet => false,
    };
    let base = |n: usize| is_seed(census, n) || (level == Verdict::Unknown && is_sink(census, n));
    let mut seen = BTreeSet::from([node]);
    let mut queue = VecDeque::from([(node, 0)]);
    while let Some((current, distance)) = queue.pop_front() {
        if base(current) {
            return Some(distance);
        }
        for edge in edges {
            if edge.from.index() == current && admitted(edge.class) && seen.insert(edge.to.index())
            {
                queue.push_back((edge.to.index(), distance + 1));
            }
        }
    }
    None
}

/// Fixpoint soundness and precision against an independent path search:
/// every node with a path to a seed is labelled by the strongest class its
/// path needs, a node that reaches only a sink is UNKNOWN, and nothing else
/// refuses. Every witness is a shortest admitted path to a base.
#[test]
fn the_fixpoint_agrees_with_a_brute_force_path_search_on_random_graphs() {
    let mut rng = Rng(0x5eed_cafe_f00d_d00d);
    let mut seen: BTreeMap<Verdict, usize> = BTreeMap::new();
    let mut derived = 0;
    let mut unclosed = 0;
    for _ in 0..300 {
        let RandomCensus {
            census,
            invokers,
            adapter_sink,
        } = random_census(&mut rng);
        assert_eq!(census.fallback(), None);
        // Unclosed pools: any sink or open principal, and then every invoke
        // refuses (a callable minted by unenumerated code may be in any pool).
        let pools = census.expanded().pools();
        assert_eq!(
            pools.unclosed(),
            adapter_sink || !pools.open_principals().is_empty()
        );
        if pools.unclosed() {
            unclosed += 1;
            for invoker in &invokers {
                assert!(census.verdict(*invoker) >= Verdict::Unknown);
            }
        }
        let edges = census.expanded().logical_edges();
        derived += edges.len() - census.expanded().adapter_edge_count();
        let handles: Vec<ReachNode> = census
            .expanded()
            .nodes()
            .map(|(handle, _)| handle)
            .collect();
        for (node, reach) in handles.into_iter().enumerate() {
            if census.expanded().is_hub(reach) {
                // A hub is no code: it has no witness, and no logical edge
                // names it.
                assert_eq!(census.witness(reach), None);
                continue;
            }
            let expected = Verdict::LEVELS
                .into_iter()
                .find(|level| reference_distance(&census, &edges, node, *level).is_some())
                .unwrap_or(Verdict::Quiet);
            assert_eq!(census.verdict(reach), expected, "node {node}");
            *seen.entry(expected).or_default() += 1;
            let Some(witness) = census.witness(reach) else {
                assert_eq!(expected, Verdict::Quiet);
                continue;
            };
            assert_eq!(witness.verdict, expected);
            assert_eq!(
                Some(witness.path.len()),
                reference_distance(&census, &edges, node, expected)
            );
            let mut at = node;
            for edge in &witness.path {
                assert_eq!(edge.from.index(), at);
                assert!(
                    edge.class.cap() >= expected,
                    "{edge:?} is not admitted at {expected:?}"
                );
                at = edge.to.index();
            }
            assert!(is_seed(&census, at) || (expected == Verdict::Unknown && is_sink(&census, at)));
            assert_eq!(
                witness.via_drop,
                witness.path.iter().any(|edge| edge.via_drop)
            );
        }
    }
    // Not vacuous: every verdict occurs, and the pools derived edges.
    for verdict in [
        Verdict::Quiet,
        Verdict::Unknown,
        Verdict::Indirect,
        Verdict::Escapes,
        Verdict::Spawns,
    ] {
        assert!(
            seen.get(&verdict).copied().unwrap_or(0) > 20,
            "{verdict:?}: {seen:?}"
        );
    }
    assert!(derived > 100, "{derived}");
    assert!((30..270).contains(&unclosed), "{unclosed}");
}

/// The labelling is the least fixpoint, so the checker accepts the solver's
/// certificate and rejects EVERY single-label change to it.
#[test]
fn every_single_label_change_to_a_solved_certificate_is_rejected() {
    let mut rng = Rng(0x0dd_ba11);
    for _ in 0..120 {
        let census = random_census(&mut rng).census;
        let certificate = census.certificate().clone();
        assert_eq!(
            check_reach_certificate(census.expanded(), &certificate),
            Ok(())
        );
        for node in 0..certificate.labels.len() {
            for forged in [
                Verdict::Quiet,
                Verdict::Unknown,
                Verdict::Indirect,
                Verdict::Escapes,
                Verdict::Spawns,
            ] {
                if forged == certificate.labels[node] {
                    continue;
                }
                let mut tampered = certificate.clone();
                tampered.labels[node] = forged;
                assert!(
                    check_reach_certificate(census.expanded(), &tampered).is_err(),
                    "node {node} relabelled {forged:?} was accepted"
                );
            }
        }
    }
}

/// Tamper tests (design §13): a missing label, an unjustified label, a
/// self-supporting cycle, base violations, a justification through a
/// foreign or inadmissible edge, and a forged definition join.
#[test]
fn forged_certificates_are_rejected() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("caller");
    g.local("isolated");
    g.local("left");
    g.local("right");
    g.local("param");
    g.run("caller", "spawn");
    g.run("left", "right");
    g.run("right", "left");
    g.edge("param", "caller", EdgeClass::Param, false);
    let s = g.solve();
    let graph = s.census.expanded();
    let good = s.census.certificate().clone();
    let index = |name: &str| s.n(name).index();
    let edge_index = |from: &str, to: &str| {
        graph
            .edges()
            .iter()
            .position(|edge| edge.from == s.n(from) && edge.to == s.n(to))
            .expect("edge") as u32
    };
    let justification =
        |rank, edge| Some(trust_ir::function_dependencies::Justification { rank, edge });

    // A node that reaches a seed, labelled QUIET.
    let mut missing = good.clone();
    missing.labels[index("caller")] = Verdict::Quiet;
    missing.justifications[index("caller")] = None;
    assert!(matches!(
        check_reach_certificate(graph, &missing),
        Err(CertificateError::Unclosed { .. })
    ));

    // A node with no path, labelled SPAWNS with a justification it does not own.
    let mut unjustified = good.clone();
    unjustified.labels[index("isolated")] = Verdict::Spawns;
    unjustified.justifications[index("isolated")] = justification(1, edge_index("caller", "spawn"));
    assert_eq!(
        check_reach_certificate(graph, &unjustified),
        Err(CertificateError::Unjustified(s.n("isolated")))
    );

    // A cycle that justifies itself. Closure (ii) holds for it, so only the
    // well-founded ranks reject it.
    let mut cycle = good.clone();
    cycle.labels[index("left")] = Verdict::Spawns;
    cycle.labels[index("right")] = Verdict::Spawns;
    cycle.justifications[index("left")] = justification(2, edge_index("left", "right"));
    cycle.justifications[index("right")] = justification(1, edge_index("right", "left"));
    for edge in graph.edges() {
        let (from, to) = (
            cycle.labels[edge.from.index()],
            cycle.labels[edge.to.index()],
        );
        assert!(
            from >= to.min(edge.class.cap()),
            "the forged cycle is closed"
        );
    }
    assert!(matches!(
        check_reach_certificate(graph, &cycle),
        Err(CertificateError::Unjustified(_))
    ));

    // Bases: a seed must be SPAWNS and carries no justification.
    let mut seed = good.clone();
    seed.labels[index("spawn")] = Verdict::Escapes;
    assert_eq!(
        check_reach_certificate(graph, &seed),
        Err(CertificateError::Base(s.n("spawn")))
    );
    let mut based = good.clone();
    based.justifications[index("spawn")] = justification(1, edge_index("caller", "spawn"));
    assert_eq!(
        check_reach_certificate(graph, &based),
        Err(CertificateError::Base(s.n("spawn")))
    );

    // A justification through a PARAM edge, which no verdict admits.
    let mut param = good.clone();
    param.labels[index("param")] = Verdict::Spawns;
    param.justifications[index("param")] = justification(2, edge_index("param", "caller"));
    assert_eq!(
        check_reach_certificate(graph, &param),
        Err(CertificateError::Unjustified(s.n("param")))
    );

    // A QUIET node carrying a justification is malformed.
    let mut quiet = good.clone();
    quiet.justifications[index("isolated")] = justification(1, edge_index("caller", "spawn"));
    assert_eq!(
        check_reach_certificate(graph, &quiet),
        Err(CertificateError::Unjustified(s.n("isolated")))
    );

    // The definition join must follow the labels.
    let mut join = good.clone();
    join.definitions[0].1 = Verdict::Spawns;
    join.definitions
        .retain(|(_, verdict)| *verdict == Verdict::Spawns);
    assert_eq!(
        check_reach_certificate(graph, &join),
        Err(CertificateError::Definitions)
    );

    let mut short = good.clone();
    short.labels.pop();
    assert_eq!(
        check_reach_certificate(graph, &short),
        Err(CertificateError::Shape)
    );
    assert_eq!(check_reach_certificate(graph, &good), Ok(()));
}

/// The certificate is checked against the engine-derived APPROX edges too.
#[test]
fn a_forged_label_below_a_derived_approx_edge_is_rejected() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("member");
    g.local("creator");
    g.local("invoker");
    g.run("member", "spawn");
    g.create("creator", "member", fn_key(&[]), false);
    g.invoke("invoker", fn_key(&[]));
    let s = g.solve();
    assert_eq!(s.verdict("invoker"), Verdict::Indirect);
    let graph = s.census.expanded();
    assert!(graph.edges().len() > graph.adapter_edge_count());
    let mut forged = s.census.certificate().clone();
    forged.labels[s.n("invoker").index()] = Verdict::Quiet;
    forged.justifications[s.n("invoker").index()] = None;
    let Err(CertificateError::Unclosed { edge }) = check_reach_certificate(graph, &forged) else {
        panic!("a QUIET invoker of a spawning pool must be rejected");
    };
    assert!(
        edge >= graph.adapter_edge_count(),
        "rejected on the derived edge"
    );
    assert_eq!(graph.edges()[edge].class, EdgeClass::Approx);
}

/// A malformed fact turns every node UNKNOWN and claims no spawn.
#[test]
fn malformed_facts_fall_back_to_unknown_everywhere() {
    for case in 0..6 {
        let mut other = ReachGraph::new();
        let foreign = (0..9)
            .map(|id| {
                other.add_node(ReachNodeSpec {
                    origin: NodeOrigin::Mir(id),
                    definition: None,
                    locality: Locality::Local,
                    body: NodeBody::Walked,
                })
            })
            .last()
            .expect("nodes");
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("caller");
        g.local("callee");
        g.run("caller", "spawn");
        let site = ReachSite::Mir(0);
        let (spawn, caller, callee) = (g.n("spawn"), g.n("caller"), g.n("callee"));
        let expected = match case {
            0 => {
                g.graph.add_node(ReachNodeSpec {
                    origin: NodeOrigin::TrustIr(N::Function(f(1))),
                    definition: None,
                    locality: Locality::Local,
                    body: NodeBody::Walked,
                });
                ReachDefect::MixedOrigins
            }
            1 => {
                g.graph.add_edge(spawn, caller, EdgeClass::Run, site, false);
                ReachDefect::EdgeFromTerminal(spawn)
            }
            2 => {
                g.graph
                    .add_edge(caller, foreign, EdgeClass::Run, site, false);
                ReachDefect::ForeignNode(foreign)
            }
            3 => {
                g.graph
                    .add_edge(caller, callee, EdgeClass::Approx, site, false);
                ReachDefect::AdapterApprox
            }
            4 => {
                g.graph.add_spawn(caller, callee, None, site, false);
                ReachDefect::SpawnOfNonSeed(callee)
            }
            _ => {
                let sink = g
                    .graph
                    .add_unknown(caller, R::InlineAsm, EdgeClass::Run, site, false);
                g.graph
                    .add_invoke(sink, fn_key(&[]), Vec::new(), site, false);
                ReachDefect::NotAProgramNode(sink)
            }
        };
        let census = g.graph.solve();
        assert_eq!(
            census.fallback(),
            Some(&ReachFallback::Defects(vec![expected])),
            "{case}"
        );
        for node in g.names.values() {
            assert_eq!(census.verdict(*node), Verdict::Unknown);
            assert!(census.witness(*node).is_none());
        }
        assert!(!census.thread_closure(Some(caller)).modelable());
    }
}

// --- pools -----------------------------------------------------------------

/// FnPool keys (§5.4): a call reaches only members of a matching shape; an
/// unstated component matches everything; a LAUNDER leaves them so.
#[test]
fn fn_pools_stay_keyed_by_shape_after_a_launder() {
    let build = |launder: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("launch");
        g.local("creator");
        for name in [
            "same_shape",
            "other_shape",
            "other_arity",
            "unstated_abi",
            "unclassified_param",
        ] {
            g.local(name);
        }
        g.run("launch", "spawn");
        g.create("creator", "launch", fn_key(&[ArgClass::ThinPointer]), false);
        g.invoke("same_shape", fn_key(&[ArgClass::ThinPointer]));
        g.invoke("other_shape", fn_key(&[ArgClass::Float(64)]));
        g.invoke("other_arity", fn_key(&[]));
        g.invoke(
            "unstated_abi",
            PoolKey::Fn(FnShape {
                abi: None,
                variadic: Some(false),
                params: Some(vec![ArgClass::ThinPointer]),
            }),
        );
        g.invoke("unclassified_param", fn_key(&[ArgClass::Unclassified]));
        if launder {
            let site = g.site();
            g.graph.add_launder(site);
        }
        g.solve()
    };
    let s = build(false);
    s.verdicts(&[
        ("creator", Verdict::Escapes),
        ("same_shape", Verdict::Indirect),
        ("other_shape", Verdict::Quiet),
        ("other_arity", Verdict::Quiet),
        ("unstated_abi", Verdict::Indirect),
        ("unclassified_param", Verdict::Indirect),
    ]);
    assert!(!s.census.expanded().pools().laundered());
    // A LAUNDER puts callables into data, not into other shapes' pools: a
    // callable called back at a shape its own does not match is UB (R4).
    let s = build(true);
    assert!(s.census.expanded().pools().laundered());
    s.verdicts(&[
        ("creator", Verdict::Escapes),
        ("same_shape", Verdict::Indirect),
        ("other_shape", Verdict::Quiet),
        ("other_arity", Verdict::Quiet),
        ("unstated_abi", Verdict::Indirect),
        ("unclassified_param", Verdict::Indirect),
    ]);
}

/// Confinement: a confined member is visible only to invokers in local
/// bodies; a LIFETIME-ERASE of its principal, or any LAUNDER, demotes it.
#[test]
fn confined_members_are_visible_only_locally_until_demoted() {
    let build = |demotion: u8| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("closure_body");
        g.local("frame");
        g.local("local_invoker");
        g.external("std_invoker");
        g.run("closure_body", "spawn");
        g.create("frame", "closure_body", dyn_method(1, 9), true);
        g.invoke("local_invoker", dyn_method(1, 9));
        g.invoke("std_invoker", dyn_method(1, 9));
        match demotion {
            1 => g.graph.add_lifetime_erase(PrincipalKey(1)),
            2 => g.graph.add_lifetime_erase(PrincipalKey(2)),
            3 => {
                let site = g.site();
                g.graph.add_launder(site);
            }
            _ => {}
        }
        g.solve()
    };
    build(0).verdicts(&[
        ("local_invoker", Verdict::Indirect),
        ("std_invoker", Verdict::Quiet),
    ]);
    build(1).verdicts(&[("std_invoker", Verdict::Indirect)]);
    build(2).verdicts(&[("std_invoker", Verdict::Quiet)]);
    build(3).verdicts(&[("std_invoker", Verdict::Indirect)]);
}

/// Rule H (the judge's j02 case): a local frame handing a callable to
/// external code is charged with the callable's pool only when that code
/// invokes the key. `fmt::write(w, ..)` is charged; `vec.push(&mut hooks)`
/// is not; foreign code with no body invokes every key.
#[test]
fn rule_h_charges_a_handoff_only_when_the_callee_invokes_the_key() {
    let write = || CarriedKey::Principal(PrincipalKey(4));
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("<Spawner as Write>::write_str");
    g.local("l");
    g.local("pusher");
    g.local("to_c");
    g.local("hands_int");
    g.external("fmt::write");
    g.external("fmt::write_inner");
    g.external("Vec::push");
    g.foreign("qsort");
    g.run("<Spawner as Write>::write_str", "spawn");
    // `&mut w as &mut dyn Write` in `l`: a confined member.
    g.create("l", "<Spawner as Write>::write_str", dyn_method(4, 1), true);
    g.run("fmt::write", "fmt::write_inner");
    g.invoke("fmt::write_inner", dyn_method(4, 1));
    g.handoff("l", "fmt::write", vec![write()]);
    g.create(
        "pusher",
        "<Spawner as Write>::write_str",
        dyn_method(4, 1),
        true,
    );
    g.handoff("pusher", "Vec::push", vec![write()]);
    g.create(
        "to_c",
        "<Spawner as Write>::write_str",
        dyn_method(4, 1),
        true,
    );
    g.handoff("to_c", "qsort", vec![CarriedKey::AnyDyn]);
    g.handoff("hands_int", "qsort", Vec::new());
    let s = g.solve();
    s.verdicts(&[
        ("fmt::write_inner", Verdict::Quiet),
        ("fmt::write", Verdict::Quiet),
        ("hands_int", Verdict::Quiet),
    ]);
    // `l` and `pusher` create the member, so they are ESCAPES regardless;
    // what rule H adds is the APPROX edge, visible in the expanded graph.
    let approx_from = |name: &str| {
        s.census
            .expanded()
            .edges()
            .iter()
            .any(|edge| edge.class == EdgeClass::Approx && edge.from == s.n(name))
    };
    assert!(approx_from("l"), "fmt::write invokes Write::write_str");
    assert!(!approx_from("pusher"), "Vec::push invokes no key");
    assert!(approx_from("to_c"), "foreign code invokes every key");
}

/// Rule H reaches through the callee's whole closure, including an indirect
/// call whose pool member is external code (the hand-off then goes to it).
#[test]
fn rule_h_follows_the_callee_closure_and_indirect_calls_into_external_code() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("hook");
    g.local("registrar");
    g.local("frame");
    g.local("caller_of_ptr");
    g.external("std::panicking::run_hook");
    g.external("std::panicking::begin_panic");
    g.external("std::iter::for_each");
    g.run("hook", "spawn");
    g.create("registrar", "hook", fn_key(&[]), true);
    g.run("std::panicking::begin_panic", "std::panicking::run_hook");
    g.invoke("std::panicking::run_hook", fn_key(&[]));
    // `frame` hands the hook to begin_panic directly.
    g.handoff(
        "frame",
        "std::panicking::begin_panic",
        vec![CarriedKey::Key(fn_key(&[]))],
    );
    // `caller_of_ptr` calls `for_each` through a fn pointer, handing it the hook.
    g.create(
        "registrar",
        "std::iter::for_each",
        fn_key(&[ArgClass::ThinPointer]),
        false,
    );
    g.run("std::iter::for_each", "std::panicking::run_hook");
    g.invoke_carrying(
        "caller_of_ptr",
        fn_key(&[ArgClass::ThinPointer]),
        vec![CarriedKey::Key(fn_key(&[]))],
    );
    let s = g.solve();
    s.verdicts(&[
        ("std::panicking::run_hook", Verdict::Quiet),
        ("frame", Verdict::Indirect),
        ("caller_of_ptr", Verdict::Indirect),
    ]);
    assert_eq!(s.witness_names("frame"), ["hook", "spawn"]);
}

/// Upcasts merge `dyn` pools, and an upcast from a principal with no recorded
/// member opens its target (and what that upcasts to): UNKNOWN, never an
/// empty pool (trust-mc `dyn_universe.rs`, `close_over_upcasts` and
/// `open_principals`). An open principal stands for runtime types the census
/// did not enumerate, so it also leaves every other pool unclosed.
#[test]
fn upcasts_merge_dyn_pools_and_an_unrecorded_source_opens_the_target() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("SB::m");
    g.local("coerce");
    g.local("call_on_super");
    g.local("call_on_sub_drop");
    g.local("call_on_open");
    g.local("call_on_open_chain");
    g.local("drop_dyn_open");
    g.run("SB::m", "spawn");
    // SB is coerced only to `dyn Sub` (2); an upcast makes it a `dyn Super` (1).
    g.create("coerce", "SB::m", dyn_method(2, 7), false);
    g.graph.add_upcast(PrincipalKey(2), PrincipalKey(1));
    g.invoke("call_on_super", dyn_method(1, 7));
    // Sub is recorded, but no member fills its drop slot: an empty pool.
    g.invoke("call_on_sub_drop", PoolKey::DynDrop(PrincipalKey(2)));
    let closed = g.solve();
    closed.verdicts(&[
        ("call_on_super", Verdict::Indirect),
        ("call_on_sub_drop", Verdict::Quiet),
    ]);
    assert!(!closed.census.expanded().pools().unclosed());

    let mut g = Facts::new();
    g.seed("spawn");
    g.local("SB::m");
    g.local("coerce");
    g.local("call_on_super");
    g.local("call_on_open");
    g.local("call_on_open_chain");
    g.local("drop_dyn_open");
    g.run("SB::m", "spawn");
    g.create("coerce", "SB::m", dyn_method(2, 7), false);
    g.graph.add_upcast(PrincipalKey(2), PrincipalKey(1));
    g.invoke("call_on_super", dyn_method(1, 7));
    // `dyn Stubbed` (5) has no recorded member and is upcast to 6, then 6 to 8.
    g.graph.add_upcast(PrincipalKey(5), PrincipalKey(6));
    g.graph.add_upcast(PrincipalKey(6), PrincipalKey(8));
    g.invoke("call_on_open", dyn_method(6, 7));
    g.invoke("call_on_open_chain", dyn_method(8, 7));
    g.invoke("drop_dyn_open", PoolKey::DynDrop(PrincipalKey(6)));
    let s = g.solve();
    s.verdicts(&[
        ("call_on_super", Verdict::Indirect),
        ("call_on_open", Verdict::Unknown),
        ("call_on_open_chain", Verdict::Unknown),
        ("drop_dyn_open", Verdict::Unknown),
    ]);
    let pools = s.census.expanded().pools();
    assert_eq!(
        pools.open_principals(),
        &BTreeSet::from([PrincipalKey(6), PrincipalKey(8)])
    );
    assert!(pools.unclosed());
    assert!(pools.is_open(&dyn_method(8, 1)));
    assert!(pools.is_open(&dyn_method(1, 7)), "every pool is unclosed");
    assert_eq!(pools.pool(&dyn_method(1, 7)).count(), 1);
}

/// A principal some fact names but no member records is open whether or not
/// it is upcast: the `dyn` value was minted by code the census did not
/// enumerate, never by nothing (trust-mc opens only upcast targets).
#[test]
fn an_invoked_or_carried_principal_with_no_member_is_open() {
    let mut g = Facts::new();
    g.local("call_on_unrecorded");
    g.invoke("call_on_unrecorded", dyn_method(3, 7));
    let s = g.solve();
    s.verdicts(&[("call_on_unrecorded", Verdict::Unknown)]);
    assert_eq!(
        s.census.expanded().pools().open_principals(),
        &BTreeSet::from([PrincipalKey(3)])
    );
    assert_eq!(
        sink_reason(&s.census, s.n("call_on_unrecorded")),
        Some(R::OpenPrincipal)
    );

    let mut g = Facts::new();
    g.local("hands_unrecorded");
    g.foreign("qsort");
    g.handoff(
        "hands_unrecorded",
        "qsort",
        vec![CarriedKey::Principal(PrincipalKey(4))],
    );
    let s = g.solve();
    s.verdicts(&[("hands_unrecorded", Verdict::Unknown)]);
}

/// The `&`-erasure rule: a vtable drop slot minted through a shared `&`
/// joins its DynDropPool but is no CREATE at the erasure site, so the
/// erasing frame stays QUIET while `drop_in_place::<dyn T>` is charged.
#[test]
fn a_shared_ref_erased_drop_slot_joins_the_pool_without_a_create_edge() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("<Job as Drop>::drop");
    g.local("format_debug");
    g.external("drop_in_place::<dyn Any>");
    g.run("<Job as Drop>::drop", "spawn");
    let member = g.n("<Job as Drop>::drop");
    g.graph
        .add_pool_member(member, PoolKey::DynDrop(PrincipalKey(3)), false);
    let site = g.site();
    let dropper = g.n("drop_in_place::<dyn Any>");
    g.graph.add_invoke(
        dropper,
        PoolKey::DynDrop(PrincipalKey(3)),
        Vec::new(),
        site,
        true,
    );
    let s = g.solve();
    s.verdicts(&[
        ("format_debug", Verdict::Quiet),
        ("drop_in_place::<dyn Any>", Verdict::Indirect),
    ]);
    let witness = s
        .census
        .witness(s.n("drop_in_place::<dyn Any>"))
        .expect("refused");
    assert!(witness.via_drop);
}

/// A callable minted inside code the census did not enumerate (an UNKNOWN
/// sink: here a bodyless `store::<Spawner>()` returning `Spawner::go as
/// fn()`) is in no recorded pool. Any sink therefore leaves every pool
/// unclosed, and an invoke that could call such a callable refuses as
/// UNKNOWN(`UnclosedPool`), never QUIET; its closure is not modelable.
#[test]
fn a_sink_leaves_every_pool_unclosed() {
    let build = |sink: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("Spawner::go");
        g.local("main");
        g.external("store::<Spawner>");
        g.local("h");
        g.run("Spawner::go", "spawn");
        g.run("main", "store::<Spawner>");
        if sink {
            g.unknown("store::<Spawner>", R::UnresolvedExtern);
        }
        g.run("main", "h");
        g.invoke("h", fn_key(&[]));
        g.solve()
    };
    let closed = build(false);
    closed.verdicts(&[("h", Verdict::Quiet), ("main", Verdict::Quiet)]);
    assert!(!closed.census.expanded().pools().unclosed());
    assert!(
        closed
            .census
            .thread_closure(Some(closed.n("h")))
            .modelable()
    );

    let s = build(true);
    s.verdicts(&[
        ("main", Verdict::Unknown),
        ("h", Verdict::Unknown),
        ("Spawner::go", Verdict::Spawns),
    ]);
    assert!(s.census.expanded().pools().unclosed());
    assert_eq!(sink_reason(&s.census, s.n("h")), Some(R::UnclosedPool));
    assert!(!s.census.thread_closure(Some(s.n("h"))).modelable());
}

/// Rule H under unclosed pools: foreign code handed a value that may carry
/// a callable may call one no CREATE records; a value that carries nothing
/// it could call (data before any LAUNDER) is not charged.
#[test]
fn rule_h_charges_unclosed_pools_only_for_values_that_may_carry_a_callable() {
    let mut g = Facts::new();
    g.local("elsewhere");
    g.local("hands_fn");
    g.local("hands_int");
    g.foreign("qsort");
    g.unknown("elsewhere", R::InlineAsm);
    g.handoff("hands_fn", "qsort", vec![CarriedKey::AnyFn]);
    g.handoff("hands_int", "qsort", vec![CarriedKey::Laundered]);
    let s = g.solve();
    s.verdicts(&[
        ("hands_fn", Verdict::Unknown),
        ("hands_int", Verdict::Quiet),
    ]);
    assert_eq!(
        sink_reason(&s.census, s.n("hands_fn")),
        Some(R::UnclosedPool)
    );
}

/// Rule H charges what the callee's closure invokes, and nothing is assumed
/// about a RUN edge to it: a hand-off alone, to code that invokes a carried
/// key while the pools are unclosed, refuses; a hand-off to code resolved
/// per instance (PARAM, R1) invokes nothing here.
#[test]
fn rule_h_charges_a_handoff_by_what_the_callee_invokes_without_assuming_a_call() {
    let mut g = Facts::new();
    g.local("elsewhere");
    g.local("hands_to_invoker");
    g.local("hands_to_generic");
    g.external("Iterator::for_each");
    g.add("F::call<T>", 99, Locality::External, NodeBody::Param);
    g.unknown("elsewhere", R::InlineAsm);
    g.invoke("Iterator::for_each", fn_key(&[]));
    g.handoff(
        "hands_to_invoker",
        "Iterator::for_each",
        vec![CarriedKey::Key(fn_key(&[]))],
    );
    g.handoff("hands_to_generic", "F::call<T>", vec![CarriedKey::Any]);
    let s = g.solve();
    s.verdicts(&[
        ("Iterator::for_each", Verdict::Unknown),
        ("hands_to_invoker", Verdict::Unknown),
        ("hands_to_generic", Verdict::Quiet),
    ]);
    assert_eq!(
        sink_reason(&s.census, s.n("hands_to_invoker")),
        Some(R::UnclosedPool)
    );
}

/// R3 and LAUNDER: `spawner as usize` handed to C (`libc::signal`), which
/// calls it back. Data carries a callable only after a LAUNDER; a LAUNDER the
/// adapter cannot key (`add_launder`, a LAUNDER of `Any`) lets it carry any.
#[test]
fn laundered_data_handed_to_foreign_code_is_charged_after_a_launder() {
    let build = |launder: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("handler");
        g.local("installer");
        g.foreign("libc::signal");
        g.run("handler", "spawn");
        g.create("installer", "handler", fn_key(&[ArgClass::Int(32)]), false);
        if launder {
            let site = g.site();
            g.graph.add_launder(site);
        }
        g.local("register");
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    build(false).verdicts(&[("register", Verdict::Quiet)]);
    let s = build(true);
    s.verdicts(&[("register", Verdict::Indirect)]);
    assert_eq!(s.witness_names("register"), ["handler", "spawn"]);
    assert!(s.census.expanded().pools().launder_site().is_some());
}

/// An unkeyed LAUNDER of one callable (`seed_source as usize`, which the MIR
/// lane records with `add_launder` until its value LAUNDERs are keyed) lets
/// data hold EVERY callable, a spawning one of the same shape included: a
/// LAUNDER's keys are the reinterpreted bytes' type's, never one known
/// callable's. Before any LAUNDER, data holds none.
#[test]
fn a_launder_of_one_callable_lets_data_hold_every_callable() {
    let build = |launder: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("launch");
        g.local("seed_source");
        g.local("installer");
        g.local("register");
        g.foreign("libc::signal");
        g.run("launch", "spawn");
        g.create("installer", "launch", fn_key(&[]), false);
        g.create("installer", "seed_source", fn_key(&[]), false);
        if launder {
            let site = g.site();
            g.graph.add_launder(site);
        }
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    build(false).verdicts(&[("register", Verdict::Quiet)]);
    let s = build(true);
    assert!(s.census.expanded().pools().laundered());
    s.verdicts(&[("register", Verdict::Indirect)]);
    assert_eq!(s.witness_names("register"), ["launch", "spawn"]);
}

/// Typed LAUNDER (design §10): data holds what the LAUNDERs' keys admit. A
/// LAUNDER of the zero-argument shape (a pun of `f: fn()` read as an
/// integer) lets data hold `launch` (`fn()`), not `handler` (`fn(i32)`); one
/// of a shape no member has lets it hold nothing.
#[test]
fn a_keyed_launder_admits_only_its_keys() {
    let build = |keys: Vec<CarriedKey>| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("launch");
        g.local("handler");
        g.local("installer");
        g.local("register");
        g.foreign("libc::signal");
        g.run("launch", "spawn");
        g.run("handler", "spawn");
        g.create("installer", "launch", fn_key(&[]), false);
        g.create("installer", "handler", fn_key(&[ArgClass::Int(32)]), false);
        let site = g.site();
        g.graph.add_launder_keys(site, keys);
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    let s = build(vec![CarriedKey::Key(fn_key(&[]))]);
    s.verdicts(&[("register", Verdict::Indirect)]);
    assert_eq!(s.witness_names("register"), ["launch", "spawn"]);
    let pools = s.census.expanded().pools();
    assert!(pools.laundered());
    assert_eq!(
        pools.laundered_keys().keys().collect::<Vec<_>>(),
        [&CarriedKey::Key(fn_key(&[]))]
    );
    let s = build(vec![CarriedKey::Key(fn_key(&[ArgClass::Int(32)]))]);
    s.verdicts(&[("register", Verdict::Indirect)]);
    assert_eq!(s.witness_names("register"), ["handler", "spawn"]);
    // A shape no member has: data holds nothing a spawn is reached through.
    build(vec![CarriedKey::Key(fn_key(&[ArgClass::Float(64)]))])
        .verdicts(&[("register", Verdict::Quiet)]);
    // `Laundered` among the keys is dropped, and no keys is no fact.
    let s = build(vec![CarriedKey::Laundered]);
    s.verdicts(&[("register", Verdict::Quiet)]);
    assert!(!s.census.expanded().pools().laundered());
    assert_eq!(s.census.expanded().pools().launder_site(), None);
    build(Vec::new()).verdicts(&[("register", Verdict::Quiet)]);
}

/// Keyed admission is checked against each member's OWN key: shape matching
/// is not transitive, so a member of an unclassified shape that a laundered
/// key admits is what an invoke of a shape that key does not admit may call.
/// External code invoking `fn(f64)` handed data that holds a laundered
/// `fn(i32)` reaches a member created at `fn(_)`.
#[test]
fn a_keyed_launder_admits_a_member_a_nontransitive_shape_matches() {
    let build = |laundered: PoolKey| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("spawner");
        g.local("installer");
        g.local("register");
        g.external("calls_f64");
        g.run("spawner", "spawn");
        g.create(
            "installer",
            "spawner",
            fn_key(&[ArgClass::Unclassified]),
            false,
        );
        g.invoke("calls_f64", fn_key(&[ArgClass::Float(64)]));
        let site = g.site();
        g.graph
            .add_launder_keys(site, vec![CarriedKey::Key(laundered)]);
        g.handoff("register", "calls_f64", vec![CarriedKey::Laundered]);
        g.solve()
    };
    let s = build(fn_key(&[ArgClass::Int(32)]));
    s.verdicts(&[("register", Verdict::Indirect)]);
    assert_eq!(s.witness_names("register"), ["spawner", "spawn"]);
    // Two arguments: no member of that shape is in `fn(f64)`'s pool.
    build(fn_key(&[ArgClass::Int(32), ArgClass::Int(32)]))
        .verdicts(&[("register", Verdict::Quiet)]);
}

/// `add_launder` is a LAUNDER of `Any`, its meaning before typed LAUNDERs:
/// data holds every member, confined ones included, and every confined
/// member is demoted.
#[test]
fn add_launder_is_a_launder_of_any() {
    let build = |keyed: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("closure_body");
        g.local("frame");
        g.local("launch");
        g.local("register");
        g.external("std_invoker");
        g.foreign("libc::signal");
        g.run("closure_body", "spawn");
        g.run("launch", "spawn");
        g.create("frame", "closure_body", dyn_method(1, 9), true);
        g.create("frame", "launch", fn_key(&[ArgClass::Int(64)]), false);
        g.invoke("std_invoker", dyn_method(1, 9));
        let site = g.site();
        if keyed {
            g.graph.add_launder_keys(site, vec![CarriedKey::Any]);
        } else {
            g.graph.add_launder(site);
        }
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    for keyed in [false, true] {
        let s = build(keyed);
        s.verdicts(&[
            ("register", Verdict::Indirect),
            ("std_invoker", Verdict::Indirect),
        ]);
        let pools = s.census.expanded().pools();
        assert!(pools.laundered());
        assert_eq!(
            pools.laundered_keys().keys().collect::<Vec<_>>(),
            [&CarriedKey::Any]
        );
        assert!(pools.members().iter().all(|member| !member.confined));
    }
}

/// Confinement under typed LAUNDERs: a LAUNDER demotes the confined members
/// of the principals its keys name (and of every principal an upcast makes
/// of them), `Any` and `AnyDyn` demote every one, and a LAUNDER of fn keys or
/// of an untyped pointer demotes none.
#[test]
fn a_keyed_launder_demotes_only_the_principals_it_names() {
    let build = |keys: Vec<CarriedKey>| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("closure_body");
        g.local("frame");
        g.local("local_invoker");
        g.external("std_invoker");
        g.run("closure_body", "spawn");
        g.create("frame", "closure_body", dyn_method(1, 9), true);
        g.invoke("local_invoker", dyn_method(1, 9));
        g.invoke("std_invoker", dyn_method(1, 9));
        let site = g.site();
        g.graph.add_launder_keys(site, keys);
        g.solve()
    };
    for (keys, demoted) in [
        (vec![CarriedKey::Key(fn_key(&[]))], false),
        (vec![CarriedKey::AnyFn], false),
        (vec![CarriedKey::Untyped], false),
        (vec![CarriedKey::Principal(PrincipalKey(1))], true),
        (vec![CarriedKey::Key(dyn_method(1, 9))], true),
        (
            vec![CarriedKey::Key(PoolKey::DynDrop(PrincipalKey(1)))],
            true,
        ),
        (vec![CarriedKey::AnyDyn], true),
        (vec![CarriedKey::Any], true),
    ] {
        let label = format!("{keys:?}");
        let s = build(keys);
        assert!(!s.census.expanded().pools().unclosed(), "{label}");
        let expected = if demoted {
            Verdict::Indirect
        } else {
            Verdict::Quiet
        };
        assert_eq!(s.verdict("std_invoker"), expected, "{label}");
        assert_eq!(s.verdict("local_invoker"), Verdict::Indirect, "{label}");
    }
}

/// An untyped pointer's key in a LAUNDER: data then holds every member but a
/// confined one, and nothing is demoted. A LAUNDER of `Any` holds the
/// confined one too.
#[test]
fn an_untyped_launder_holds_no_confined_member_and_demotes_none() {
    let build = |key: CarriedKey| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("closure_body");
        g.local("frame");
        g.local("register");
        g.foreign("libc::signal");
        g.run("closure_body", "spawn");
        g.create("frame", "closure_body", dyn_method(1, 9), true);
        let site = g.site();
        g.graph.add_launder_keys(site, vec![key]);
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    let s = build(CarriedKey::Untyped);
    s.verdicts(&[("register", Verdict::Quiet)]);
    assert!(
        s.census
            .expanded()
            .pools()
            .members()
            .iter()
            .all(|member| member.confined)
    );
    build(CarriedKey::Any).verdicts(&[("register", Verdict::Indirect)]);
}

/// A laundered `dyn` key admits what its principal admits: every principal
/// an upcast chain makes of it, and the members filed there.
#[test]
fn a_principal_launder_admits_its_upcasts() {
    let build = |laundered: u64| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("spawner");
        g.local("other");
        g.local("frame");
        g.local("register");
        g.foreign("libc::signal");
        g.run("spawner", "spawn");
        // `spawner` is a member of principal 1 only; principal 2 upcasts to
        // 1; principal 3 is unrelated. Each has a member, so none is open.
        g.create("frame", "spawner", dyn_method(1, 1), false);
        g.create("frame", "other", dyn_method(2, 1), false);
        g.create("frame", "other", dyn_method(3, 1), false);
        g.graph.add_upcast(PrincipalKey(2), PrincipalKey(1));
        let site = g.site();
        g.graph
            .add_launder_keys(site, vec![CarriedKey::Principal(PrincipalKey(laundered))]);
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    for (laundered, expected) in [
        (1, Verdict::Indirect),
        (2, Verdict::Indirect),
        (3, Verdict::Quiet),
    ] {
        let s = build(laundered);
        assert!(!s.census.expanded().pools().unclosed());
        assert_eq!(s.verdict("register"), expected, "principal {laundered}");
    }
}

/// A principal a LAUNDER puts into data but no member records is open: a
/// `dyn` value of it may be one no CREATE records, so the pools are not
/// closed.
#[test]
fn a_laundered_principal_no_member_records_is_open() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("spawner");
    g.local("frame");
    g.local("register");
    g.foreign("libc::signal");
    g.run("spawner", "spawn");
    g.create("frame", "spawner", dyn_method(1, 1), false);
    let site = g.site();
    g.graph
        .add_launder_keys(site, vec![CarriedKey::Principal(PrincipalKey(5))]);
    g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
    let s = g.solve();
    let pools = s.census.expanded().pools();
    assert!(pools.open_principals().contains(&PrincipalKey(5)));
    assert!(pools.unclosed());
    s.verdicts(&[("register", Verdict::Unknown)]);
}

/// In an unclosed graph, data handed to code that invokes every key reaches
/// the `UnclosedPool` sink as soon as any LAUNDER exists, whatever its keys:
/// an unenumerated callable of a laundered key may be in data. Before any
/// LAUNDER, data carries nothing.
#[test]
fn a_keyed_launder_in_an_unclosed_graph_reaches_the_sink() {
    let build = |launder: bool| {
        let mut g = Facts::new();
        g.local("elsewhere");
        g.local("register");
        g.foreign("libc::signal");
        g.unknown("elsewhere", R::InlineAsm);
        if launder {
            let site = g.site();
            g.graph
                .add_launder_keys(site, vec![CarriedKey::Key(fn_key(&[ArgClass::Int(8)]))]);
        }
        g.handoff("register", "libc::signal", vec![CarriedKey::Laundered]);
        g.solve()
    };
    build(false).verdicts(&[("register", Verdict::Quiet)]);
    let s = build(true);
    s.verdicts(&[("register", Verdict::Unknown)]);
    assert_eq!(
        sink_reason(&s.census, s.n("register")),
        Some(R::UnclosedPool)
    );
}

/// An untyped pointer handed to external code reaches every member a key
/// admits but a confined one: memory holding a confined erasure is reached
/// through a pointer only after a cast that demotes it. An opaque value
/// (`CarriedKey::Any`) still reaches it, and a demoted member is reached.
#[test]
fn an_untyped_pointer_reaches_no_confined_member() {
    let build = |carried: CarriedKey, demote: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("closure_body");
        g.local("creator");
        g.external("std_call");
        g.local("hander");
        g.run("closure_body", "spawn");
        g.create("creator", "closure_body", dyn_method(1, 1), true);
        g.invoke("std_call", dyn_method(1, 1));
        g.handoff("hander", "std_call", vec![carried]);
        if demote {
            g.graph.add_lifetime_erase(PrincipalKey(1));
        }
        g.solve()
    };
    build(CarriedKey::Untyped, false).verdicts(&[
        ("creator", Verdict::Escapes),
        ("std_call", Verdict::Quiet),
        ("hander", Verdict::Quiet),
    ]);
    build(CarriedKey::Any, false).verdicts(&[("hander", Verdict::Indirect)]);
    build(CarriedKey::Untyped, true).verdicts(&[
        ("std_call", Verdict::Indirect),
        ("hander", Verdict::Indirect),
    ]);
}

/// A witness's `via_drop` flag does not depend on fact order: two invokes at
/// one node share one derived edge, flagged only if every one runs in drop
/// glue.
#[test]
fn a_derived_edge_is_via_drop_only_if_every_fact_behind_it_is() {
    let build = |drop_first: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("member");
        g.local("creator");
        g.local("invoker");
        g.run("member", "spawn");
        g.create("creator", "member", fn_key(&[]), false);
        for via_drop in [drop_first, !drop_first] {
            let site = g.site();
            let invoker = g.n("invoker");
            g.graph
                .add_invoke(invoker, fn_key(&[]), Vec::new(), site, via_drop);
        }
        let s = g.solve();
        let witness = s.census.witness(s.n("invoker")).expect("refused");
        (witness.verdict, witness.via_drop)
    };
    assert_eq!(build(true), (Verdict::Indirect, false));
    assert_eq!(build(false), (Verdict::Indirect, false));
}

/// A hand-off to a seed is charged unless the call that makes it is the RUN
/// edge into the seed, which outranks it; nothing is assumed.
#[test]
fn a_handoff_to_a_seed_without_a_run_edge_is_charged() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("only_handoff");
    g.local("calls_and_hands");
    g.handoff("only_handoff", "spawn", vec![CarriedKey::Any]);
    let site = g.site();
    let (caller, seed) = (g.n("calls_and_hands"), g.n("spawn"));
    g.graph.add_spawn(caller, seed, None, site, false);
    g.handoff("calls_and_hands", "spawn", vec![CarriedKey::Any]);
    let s = g.solve();
    s.verdicts(&[
        ("only_handoff", Verdict::Indirect),
        ("calls_and_hands", Verdict::Spawns),
    ]);
    let sites = s.census.spawn_sites().expect("no fallback");
    assert_eq!(sites.len(), 2);
    assert_eq!(
        sites
            .iter()
            .filter(|site| site.edge.from == s.n("calls_and_hands"))
            .count(),
        1,
        "no derived duplicate of the RUN site"
    );
}

/// A handle is valid only in the graph that issued it: an in-range handle
/// from another graph is a defect, never an alias, and a census asked about
/// one answers UNKNOWN.
#[test]
fn a_handle_from_another_graph_never_aliases() {
    let mut other = ReachGraph::new();
    let alien = other.add_node(ReachNodeSpec {
        origin: NodeOrigin::Mir(0),
        definition: None,
        locality: Locality::External,
        body: NodeBody::Seed,
    });
    let mut g = Facts::new();
    g.local("a");
    g.local("b");
    assert_eq!(alien.index(), g.n("a").index());
    let site = g.site();
    let b = g.n("b");
    g.graph.add_edge(b, alien, EdgeClass::Run, site, false);
    let census = g.graph.solve();
    assert_eq!(
        census.fallback(),
        Some(&ReachFallback::Defects(vec![ReachDefect::ForeignNode(
            alien
        )]))
    );
    assert_eq!(
        census.spawn_sites(),
        None,
        "a malformed graph lists no sites"
    );

    let mut g = Facts::new();
    g.local("a");
    let s = g.solve();
    assert_eq!(s.census.verdict(alien), Verdict::Unknown);
    assert!(s.census.witness(alien).is_none());
    assert!(!s.census.thread_closure(Some(alien)).modelable());
    assert_eq!(s.census.expanded().node(alien), None);
}

// --- ported from trust-mc ---------------------------------------------------

/// `reachability_test.rs`, `test_collect_reachable_items_includes_local_...`:
/// local helpers are followed, and a body past trust-mc's abstraction
/// boundary is an UNKNOWN sink here, never a quiet omission.
#[test]
fn ported_reachable_items_follow_locals_and_never_drop_an_unwalked_body() {
    let mut g = Facts::new();
    g.local("reachability_probe");
    g.local("local_add_one");
    g.external("HashMap::insert");
    g.run("reachability_probe", "local_add_one");
    g.run("reachability_probe", "HashMap::insert");
    g.unknown("HashMap::insert", R::UnresolvedExtern);
    let s = g.solve();
    s.verdicts(&[
        ("reachability_probe", Verdict::Unknown),
        ("local_add_one", Verdict::Quiet),
    ]);
    assert_eq!(
        s.witness_names("reachability_probe"),
        ["HashMap::insert", "<sink>"]
    );
}

/// `reachability_test.rs`, `loop_contract_reach_*`, with `contracted`
/// starting a thread: generic code, a vtable, a fn pointer and a direct call
/// each reach it; an unrelated function does not; and a path through an
/// abstracted (unwalked) `count` is UNKNOWN, never clear.
#[test]
fn ported_loop_contract_reach_through_generics_vtables_and_fn_pointers() {
    let build = |count_abstracted: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("contracted");
        g.local("<MyIter as Iterator>::next");
        g.external("Iterator::count::<MyIter>");
        g.local("via_generic_code");
        g.local("via_vtable");
        g.local("call_next");
        g.local("via_fn_pointer");
        g.external("Option::map::<fn(u32) -> u32>");
        g.local("direct_only");
        g.local("unrelated");
        g.run("contracted", "spawn");
        g.run("<MyIter as Iterator>::next", "contracted");
        if count_abstracted {
            g.unknown("Iterator::count::<MyIter>", R::UnresolvedExtern);
        } else {
            g.run("Iterator::count::<MyIter>", "<MyIter as Iterator>::next");
        }
        g.run("via_generic_code", "Iterator::count::<MyIter>");
        g.create(
            "via_vtable",
            "<MyIter as Iterator>::next",
            dyn_method(1, 1),
            true,
        );
        g.invoke("via_vtable", dyn_method(1, 1));
        g.invoke("call_next", dyn_method(1, 1));
        g.create(
            "via_fn_pointer",
            "contracted",
            fn_key(&[ArgClass::Int(32)]),
            false,
        );
        g.run("via_fn_pointer", "Option::map::<fn(u32) -> u32>");
        g.invoke(
            "Option::map::<fn(u32) -> u32>",
            fn_key(&[ArgClass::Int(32)]),
        );
        g.run("direct_only", "contracted");
        g.solve()
    };
    let s = build(false);
    s.verdicts(&[
        ("via_generic_code", Verdict::Spawns),
        ("via_vtable", Verdict::Escapes),
        ("call_next", Verdict::Indirect),
        ("via_fn_pointer", Verdict::Escapes),
        ("Option::map::<fn(u32) -> u32>", Verdict::Indirect),
        ("direct_only", Verdict::Spawns),
        ("unrelated", Verdict::Quiet),
    ]);
    assert_eq!(
        s.witness_names("via_generic_code"),
        [
            "Iterator::count::<MyIter>",
            "<MyIter as Iterator>::next",
            "contracted",
            "spawn"
        ]
    );
    let s = build(true);
    s.verdicts(&[
        ("via_generic_code", Verdict::Unknown),
        ("direct_only", Verdict::Spawns),
    ]);
}

/// `reachability_test.rs`, `test_collect_reachable_items_follows_smart_pointer_unsize_coercions`:
/// `Box`/`Rc`/`Arc<dyn Shape>` coercions make `<Square as Shape>::area` a
/// pool member; a slice coercion has no vtable.
#[test]
fn ported_smart_pointer_unsize_coercions_file_the_vtable_method() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("<Square as Shape>::area");
    g.run("<Square as Shape>::area", "spawn");
    for probe in ["probe_box_dyn", "probe_rc_dyn", "probe_arc_dyn"] {
        g.local(probe);
        g.create(probe, "<Square as Shape>::area", dyn_method(11, 1), false);
        g.invoke(probe, dyn_method(11, 1));
    }
    g.local("probe_nonnull_slice");
    g.local("area_of");
    g.invoke("area_of", dyn_method(11, 1));
    let s = g.solve();
    s.verdicts(&[
        ("probe_box_dyn", Verdict::Escapes),
        ("probe_rc_dyn", Verdict::Escapes),
        ("probe_arc_dyn", Verdict::Escapes),
        ("probe_nonnull_slice", Verdict::Quiet),
        ("area_of", Verdict::Indirect),
    ]);
}

/// Soundness dual `walker_dyn_upcast_dual.rs`, each harness given a spawning
/// `dyn` method: a runtime type reaching `dyn Super` only by upcast (and
/// `dyn Tr + Send` → `dyn Tr`, and `dyn MyFn` → `dyn Fn`) is in the
/// dispatch's pool, so the cross-function dispatch is INDIRECT; the safe
/// twins stay QUIET.
#[test]
fn ported_walker_dyn_upcast_dual() {
    const SUPER: u64 = 1;
    const SUB: u64 = 2;
    const TR: u64 = 3;
    const TR_SEND: u64 = 4;
    const FN: u64 = 5;
    const MY_FN: u64 = 6;
    let build = |bug: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        for body in [
            "SA::m",
            "SB::m",
            "SC::m",
            "SA::t",
            "SB::t",
            "safe_closure",
            "bug_closure",
        ] {
            g.local(body);
        }
        for body in ["SB::m", "SB::t", "bug_closure"] {
            g.run(body, "spawn");
        }
        let sub_member = if bug { "SB::m" } else { "SC::m" };
        g.local("harness");
        g.local("upcast_in_helper");
        g.create("harness", "SA::m", dyn_method(SUPER, 1), true);
        g.create("upcast_in_helper", sub_member, dyn_method(SUB, 1), true);
        g.graph.add_upcast(PrincipalKey(SUB), PrincipalKey(SUPER));
        g.create("harness", "SA::t", dyn_method(TR, 2), true);
        g.create(
            "harness",
            if bug { "SB::t" } else { "SA::t" },
            dyn_method(TR_SEND, 2),
            true,
        );
        g.graph.add_upcast(PrincipalKey(TR_SEND), PrincipalKey(TR));
        g.create("harness", "safe_closure", dyn_method(FN, 3), false);
        g.create(
            "harness",
            if bug { "bug_closure" } else { "safe_closure" },
            dyn_method(MY_FN, 3),
            false,
        );
        g.graph.add_upcast(PrincipalKey(MY_FN), PrincipalKey(FN));
        g.local("call_m");
        g.local("call_t");
        g.local("call_fn");
        g.invoke("call_m", dyn_method(SUPER, 1));
        g.invoke("call_t", dyn_method(TR, 2));
        g.invoke("call_fn", dyn_method(FN, 3));
        g.solve()
    };
    build(true).verdicts(&[
        ("call_m", Verdict::Indirect),
        ("call_t", Verdict::Indirect),
        ("call_fn", Verdict::Indirect),
        ("upcast_in_helper", Verdict::Escapes),
    ]);
    build(false).verdicts(&[
        ("call_m", Verdict::Quiet),
        ("call_t", Verdict::Quiet),
        ("call_fn", Verdict::Quiet),
        ("harness", Verdict::Quiet),
    ]);
}

/// Soundness dual `devirt_missed_bug_1.rs`: the nested field `outer.inner`
/// is coerced to `&dyn Identity` and dispatched in another function. The
/// pool holds the COERCED type's method, not the parametric impl's.
#[test]
fn ported_devirt_missed_bug_1() {
    let build = |inner_spawns: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("<Inner as Identity>::id");
        g.local("<Outer<T> as Identity>::id");
        g.run(
            if inner_spawns {
                "<Inner as Identity>::id"
            } else {
                "<Outer<T> as Identity>::id"
            },
            "spawn",
        );
        g.local("check_inner_dyn_coercion");
        g.local("id_from_dyn");
        g.create(
            "check_inner_dyn_coercion",
            "<Inner as Identity>::id",
            dyn_method(7, 1),
            true,
        );
        g.run("check_inner_dyn_coercion", "id_from_dyn");
        g.invoke("id_from_dyn", dyn_method(7, 1));
        g.solve()
    };
    build(true).verdicts(&[("id_from_dyn", Verdict::Indirect)]);
    // Outer is never coerced, so its spawning impl is not in the pool.
    build(false).verdicts(&[
        ("id_from_dyn", Verdict::Quiet),
        ("check_inner_dyn_coercion", Verdict::Quiet),
    ]);
}

/// Negative pack `dyn_ifelse_dispatch.rs`: both arms of an if/else coerce,
/// the dispatch is one or two call boundaries away, or boxed. Every arm is in
/// the pool; with neither arm spawning, everything is QUIET.
#[test]
fn ported_dyn_ifelse_dispatch() {
    let build = |two_spawns: bool| {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("<One as Val>::v");
        g.local("<Two as Val>::v");
        if two_spawns {
            g.run("<Two as Val>::v", "spawn");
        }
        g.local("ifelse_harness");
        g.local("boxed_harness");
        g.local("call_v");
        g.local("outer");
        for (harness, confined) in [("ifelse_harness", true), ("boxed_harness", false)] {
            g.create(harness, "<One as Val>::v", dyn_method(8, 1), confined);
            g.create(harness, "<Two as Val>::v", dyn_method(8, 1), confined);
        }
        g.invoke("boxed_harness", dyn_method(8, 1));
        g.run("ifelse_harness", "outer");
        g.run("outer", "call_v");
        g.invoke("call_v", dyn_method(8, 1));
        g.solve()
    };
    build(true).verdicts(&[
        ("call_v", Verdict::Indirect),
        ("outer", Verdict::Indirect),
        ("ifelse_harness", Verdict::Escapes),
        ("boxed_harness", Verdict::Escapes),
    ]);
    build(false).verdicts(&[
        ("call_v", Verdict::Quiet),
        ("outer", Verdict::Quiet),
        ("ifelse_harness", Verdict::Quiet),
        ("boxed_harness", Verdict::Quiet),
    ]);
}

/// The aterm pre-fix graph of `tools/main-thread-purity`, with the blocking
/// leaf the census cares about: `Session::drop` starts a thread. The spawn is
/// reached only through drop glue, so the witness is flagged `via_drop`.
fn aterm_teardown(safe: bool) -> Facts {
    let mut g = Facts::new();
    g.seed("std::thread::Builder::spawn");
    for name in [
        "aterm_gui::main",
        "drop_in_place::<App>",
        "drop_in_place::<Vec<Session>>",
        "drop_in_place::<Session>",
        "<Session as Drop>::drop",
        "<App as ApplicationHandler>::window_event",
        "App::close_active_tab",
        "<App as ApplicationHandler>::about_to_wait",
        "App::render",
        "Session::spawn_reader_thread::{closure#0}",
        "reap_pty::{closure#0}",
    ] {
        g.local(name);
    }
    for name in [
        "libc::close",
        "libc::read",
        "libc::waitpid",
        "libc::kill",
        "Renderer::present",
    ] {
        g.foreign(name);
    }
    g.drop_glue("aterm_gui::main", "drop_in_place::<App>");
    g.drop_glue("drop_in_place::<App>", "drop_in_place::<Vec<Session>>");
    g.drop_glue("drop_in_place::<Vec<Session>>", "drop_in_place::<Session>");
    g.drop_glue("drop_in_place::<Session>", "<Session as Drop>::drop");
    g.run(
        "<App as ApplicationHandler>::window_event",
        "App::close_active_tab",
    );
    g.drop_glue("App::close_active_tab", "drop_in_place::<Session>");
    g.run("<App as ApplicationHandler>::about_to_wait", "App::render");
    g.run("App::render", "Renderer::present");
    g.run("Session::spawn_reader_thread::{closure#0}", "libc::read");
    if safe {
        // Hang up, then hand the blocking close to a detached reaper.
        g.run("<Session as Drop>::drop", "libc::kill");
        let site = g.site();
        let (caller, seed, entry) = (
            g.n("<Session as Drop>::drop"),
            g.n("std::thread::Builder::spawn"),
            g.n("reap_pty::{closure#0}"),
        );
        g.graph.add_spawn(caller, seed, Some(entry), site, false);
        g.run("reap_pty::{closure#0}", "libc::close");
        g.run("reap_pty::{closure#0}", "libc::waitpid");
    } else {
        g.run("<Session as Drop>::drop", "libc::close");
    }
    g
}

#[test]
fn ported_main_thread_purity_spawn_reached_through_drop_glue_is_flagged() {
    let s = aterm_teardown(true).solve();
    s.verdicts(&[
        ("aterm_gui::main", Verdict::Spawns),
        ("<App as ApplicationHandler>::window_event", Verdict::Spawns),
        ("<App as ApplicationHandler>::about_to_wait", Verdict::Quiet),
        ("Session::spawn_reader_thread::{closure#0}", Verdict::Quiet),
    ]);
    let main = s.census.witness(s.n("aterm_gui::main")).expect("refused");
    assert!(main.via_drop, "the spawn is invisible at the source site");
    assert_eq!(
        s.witness_names("aterm_gui::main"),
        [
            "drop_in_place::<App>",
            "drop_in_place::<Vec<Session>>",
            "drop_in_place::<Session>",
            "<Session as Drop>::drop",
            "std::thread::Builder::spawn",
        ]
    );
    assert!(
        s.census
            .witness(s.n("<App as ApplicationHandler>::window_event"))
            .expect("refused")
            .via_drop
    );
    assert!(
        !s.census
            .witness(s.n("<Session as Drop>::drop"))
            .expect("refused")
            .via_drop
    );
}

/// The purity tool's own question, as thread closures: which code runs on
/// the main thread. Pre-fix, `libc::close` runs there through drop glue;
/// after the fix it runs only on the reaper thread the spawn starts, and the
/// worker's `read` never runs on main. Each closure holds foreign code, whose
/// effects are not enumerated, so none feeds a model (R8).
#[test]
fn ported_main_thread_purity_thread_closures() {
    let pre = aterm_teardown(false).solve();
    let main = pre.census.thread_closure(Some(pre.n("aterm_gui::main")));
    assert!(main.contains(pre.n("libc::close")));
    assert!(!main.contains(pre.n("libc::read")));
    assert!(!main.contains(pre.n("Renderer::present")));
    let path = main.path_to(pre.n("libc::close")).expect("reached");
    assert!(path.iter().any(|edge| edge.via_drop));
    assert!(!main.modelable(), "libc::close is foreign code");

    let safe = aterm_teardown(true).solve();
    let main = safe.census.thread_closure(Some(safe.n("aterm_gui::main")));
    assert!(!main.contains(safe.n("libc::close")));
    assert!(!main.contains(safe.n("libc::waitpid")));
    assert!(main.contains(safe.n("std::thread::Builder::spawn")));
    let sites = safe.census.spawn_sites().expect("no fallback");
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].entry, Some(safe.n("reap_pty::{closure#0}")));
    let reaper = safe.census.thread_closure(sites[0].entry);
    assert!(reaper.contains(safe.n("libc::close")));
    assert!(reaper.contains(safe.n("libc::waitpid")));
    assert!(!reaper.modelable(), "foreign code");
    assert!(
        !safe.census.thread_closure(None).modelable(),
        "an unnamed entry"
    );
}

/// R8: a thread closure holding an UNKNOWN or INDIRECT node, foreign code, or
/// a node with a PARAM edge (whose code the closure does not contain) never
/// feeds a model; a closure of walked code that starts a thread does.
#[test]
fn thread_closures_that_are_not_complete_are_not_modelable() {
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("spawner");
    g.local("entry");
    g.local("generic<T>");
    g.local("calls_c");
    g.local("pure");
    g.local("pure_leaf");
    g.foreign("libc::write");
    let site = g.site();
    let (spawner, seed, entry) = (g.n("spawner"), g.n("spawn"), g.n("entry"));
    g.graph.add_spawn(spawner, seed, Some(entry), site, false);
    g.edge("entry", "generic<T>", EdgeClass::Param, false);
    // The PARAM target both refuses and starts a nested thread.
    g.unknown("generic<T>", R::UnresolvedExtern);
    g.run("generic<T>", "spawn");
    g.run("calls_c", "libc::write");
    g.run("pure", "pure_leaf");
    g.run("pure", "spawn");
    let s = g.solve();
    s.verdicts(&[
        ("entry", Verdict::Quiet),
        ("calls_c", Verdict::Quiet),
        ("pure", Verdict::Spawns),
    ]);
    let entry = s.census.thread_closure(Some(s.n("entry")));
    assert!(!entry.contains(s.n("generic<T>")), "PARAM is not followed");
    assert!(!entry.modelable(), "the closure omits the PARAM code");
    assert!(!s.census.thread_closure(Some(s.n("calls_c"))).modelable());
    let pure = s.census.thread_closure(Some(s.n("pure")));
    assert!(pure.contains(s.n("spawn")));
    assert!(pure.modelable(), "a spawn starts ANOTHER thread");

    let mut g = Facts::new();
    g.seed("spawn");
    g.local("worker");
    g.local("unknown_callee");
    g.local("member");
    g.local("indirect_caller");
    g.local("clean");
    g.run("member", "spawn");
    g.create("indirect_caller", "member", fn_key(&[]), false);
    g.unknown("unknown_callee", R::InlineAsm);
    g.run("worker", "unknown_callee");
    let s = g.solve();
    assert!(!s.census.thread_closure(Some(s.n("worker"))).modelable());
    assert!(s.census.thread_closure(Some(s.n("clean"))).modelable());
    let mut g = Facts::new();
    g.seed("spawn");
    g.local("member");
    g.local("creator");
    g.local("worker");
    g.run("member", "spawn");
    g.create("creator", "member", fn_key(&[]), false);
    g.invoke("worker", fn_key(&[]));
    let s = g.solve();
    let closure = s.census.thread_closure(Some(s.n("worker")));
    assert!(closure.contains(s.n("member")));
    assert!(!closure.modelable());
}

// ===========================================================================
// The trust-ir walk
// ===========================================================================

/// Bodyless declarations by id; bodied functions walk; services by table.
#[derive(Clone, Default)]
struct Classes {
    classes: BTreeMap<u32, FunctionClass>,
    services: HashMap<RuntimeService, ServiceClass>,
}

impl Classes {
    fn with(mut self, id: u32, class: FunctionClass) -> Self {
        self.classes.insert(id, class);
        self
    }

    fn service(mut self, service: RuntimeService, class: ServiceClass) -> Self {
        self.services.insert(service, class);
        self
    }
}

impl DeclClassifier for Classes {
    fn classify(&self, function: &Function) -> FunctionClass {
        self.classes
            .get(&function.id.index())
            .cloned()
            .unwrap_or(FunctionClass::Walk)
    }

    fn definition(&self, function: &Function) -> DefinitionKey {
        DefinitionKey(u128::from(function.id.index()))
    }

    fn runtime_service(&self, service: RuntimeService) -> ServiceClass {
        self.services
            .get(&service)
            .cloned()
            .unwrap_or(ServiceClass::Unknown(R::UnresolvedExtern))
    }
}

fn declaration(id: u32) -> Function {
    let mut declaration = function(id, vec![]);
    declaration.blocks.clear();
    declaration
}

const SPAWN: u32 = 900;

fn call(callee: u32) -> InstrNode {
    node(Inst::Call {
        callee: f(callee),
        args: vec![],
    })
}

/// A module whose root 37 runs `body`, with the seed declaration 900 and a
/// function 101 that calls it.
fn spawn_module(body: Vec<InstrNode>) -> Module {
    let mut m = module(body);
    m.functions.push(declaration(SPAWN));
    m.functions.push(function(101, vec![call(SPAWN), ret()]));
    m
}

fn seeds() -> Classes {
    Classes::default().with(
        SPAWN,
        FunctionClass::Seed {
            spawned: None,
            child: None,
        },
    )
}

fn walk<'m>(
    m: &'m Module,
    classes: &Classes,
) -> trust_ir::function_dependencies::ModuleReachability<'m> {
    let reach = inspect_module_reachability(m, classes);
    assert_eq!(reach.census().fallback(), None);
    assert_eq!(
        check_reach_certificate(reach.census().expanded(), reach.census().certificate()),
        Ok(())
    );
    reach
}

fn sink_reasons(
    reach: &trust_ir::function_dependencies::ModuleReachability<'_>,
    id: u32,
) -> Vec<R> {
    let witness = reach
        .census()
        .witness(reach.node(N::Function(f(id))).expect("reached"))
        .expect("refused");
    let last = witness.path.last().expect("a path").to;
    match reach.census().expanded().node(last) {
        Some(ReachNodeKind::Sink(reason)) => vec![reason.clone()],
        Some(ReachNodeKind::Program(_) | ReachNodeKind::Hub) | None => vec![],
    }
}

#[test]
fn trust_ir_calls_dead_blocks_and_drops_are_labelled() {
    let mut m = spawn_module(vec![call(101), ret()]);
    let classes = seeds();
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Spawns));
    assert_eq!(reach.function_verdict(f(101)), Some(Verdict::Spawns));
    assert_eq!(reach.function_verdict(f(555)), None, "never read as QUIET");

    // A call in a dead block still "reaches" (j05: a const-false branch).
    let mut dead = Block::new(b(90));
    dead.body = vec![ret(), call(101)];
    m.functions[0].blocks[0].body = vec![ret()];
    m.functions[0].blocks.push(dead);
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Spawns));

    // A drop is UNKNOWN until drops are calls to glue, and flagged via_drop.
    let m = spawn_module(vec![
        node(Inst::Drop {
            ty: Ty::U8,
            ptr: v(1),
        }),
        ret(),
    ]);
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Unknown));
    assert_eq!(sink_reasons(&reach, 37), [R::ImplicitDestructor(Ty::U8)]);
    let root = reach.node(N::Function(f(37))).expect("root");
    assert!(reach.census().witness(root).expect("refused").via_drop);
}

/// Every bodyless class and every missing callee: absent is never quiet.
#[test]
fn trust_ir_declarations_follow_their_class() {
    let mut m = spawn_module(vec![
        call(201),
        call(202),
        call(203),
        call(204),
        call(205),
        ret(),
    ]);
    for id in [201, 202, 203, 204] {
        m.functions.push(declaration(id));
    }
    m.functions.push(function(205, vec![ret()]));
    m.functions.push(function(206, vec![call(SPAWN), ret()]));
    let classes = seeds()
        .with(201, FunctionClass::Foreign)
        .with(202, FunctionClass::CallerTypeParameter)
        .with(203, FunctionClass::LinkResolved(f(206)))
        .with(205, FunctionClass::WalkDropsElided);
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(201)), Some(Verdict::Quiet), "R3");
    assert_eq!(reach.function_verdict(f(202)), Some(Verdict::Quiet));
    assert_eq!(reach.function_verdict(f(203)), Some(Verdict::Spawns));
    assert_eq!(
        reach.function_verdict(f(204)),
        Some(Verdict::Unknown),
        "a bodyless Walk"
    );
    assert_eq!(sink_reasons(&reach, 204), [R::BodylessFunction(f(204))]);
    assert_eq!(reach.function_verdict(f(205)), Some(Verdict::Unknown));
    assert_eq!(sink_reasons(&reach, 205), [R::ElidedDrops]);
    assert_eq!(
        reach.function_verdict(f(37)),
        Some(Verdict::Spawns),
        "via the link-resolved shim"
    );

    let m = spawn_module(vec![call(1234), ret()]);
    let reach = walk(&m, &seeds());
    assert_eq!(sink_reasons(&reach, 37), [R::Missing(N::Function(f(1234)))]);
    let mut m = spawn_module(vec![call(301), ret()]);
    m.functions.push(declaration(301));
    let classes = seeds().with(301, FunctionClass::Unknown(R::UnresolvedExtern));
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Unknown));
}

/// The fn signatures the pool tests use: 0 `fn()`, 1 `fn(u32)`, 2
/// `fn(fn())`, 3 `fn(u32) -> ()` reached through a struct-free int.
fn pool_module(root_body: Vec<InstrNode>) -> Module {
    let mut m = spawn_module(root_body);
    m.func_types.push(FuncTy {
        abi: None,
        params: vec![Ty::U32],
        returns: vec![],
        is_vararg: false,
    });
    m.func_types.push(FuncTy {
        abi: None,
        params: vec![Ty::Func(ft(0))],
        returns: vec![],
        is_vararg: false,
    });
    // 202 names the spawner 101 as a value; 37 calls through its argument.
    m.functions.push(function(
        202,
        vec![
            node(Inst::Const {
                ty: Ty::Func(ft(0)),
                value: Constant::FnDef(f(101)),
            })
            .with_result(v(9)),
            ret(),
        ],
    ));
    m
}

fn indirect(sig: u32) -> InstrNode {
    node(Inst::CallIndirect {
        callee: v(1),
        sig: ft(sig),
        args: vec![],
        calling_conv: CallingConv::C,
    })
}

#[test]
fn trust_ir_indirect_calls_resolve_exactly_else_pool_else_unknown() {
    // Exact: the existing resolver's typed chain makes it a RUN.
    let mut m = indirect_module();
    m.functions[1].blocks[0].body = vec![call(SPAWN), ret()];
    m.functions.push(declaration(SPAWN));
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Spawns));

    // Pooled: the callee is the function's argument.
    let mut m = pool_module(vec![indirect(0), ret()]);
    m.functions[0].blocks[0]
        .params
        .push((v(1), Ty::Func(ft(0))));
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(202)), Some(Verdict::Escapes));
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Indirect));

    // Another shape is not in that pool, and a transmute to it does not put
    // it there: a call through an ABI-incompatible type is UB (R4).
    let mut m = pool_module(vec![indirect(1), ret()]);
    m.functions[0].blocks[0]
        .params
        .push((v(1), Ty::Func(ft(1))));
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Quiet));
    m.functions[3].blocks[0].body.insert(
        1,
        node(Inst::Cast {
            op: CastOp::Transmute,
            src_ty: Ty::Func(ft(0)),
            dst_ty: Ty::Func(ft(1)),
            operand: v(9),
        })
        .with_result(v(10)),
    );
    let reach = walk(&m, &seeds());
    assert!(reach.census().expanded().pools().laundered());
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Quiet));

    // Exact, but the call's convention disagrees with its target's: the RUN
    // edge stays and the mismatch is UNKNOWN on top of it.
    let mut m = indirect_module();
    if let Inst::CallIndirect { calling_conv, .. } = &mut m.functions[0].blocks[0].body[3].inst {
        *calling_conv = CallingConv::Rust;
    }
    let reach = walk(&m, &seeds());
    assert_eq!(sink_reasons(&reach, 37), [R::IndirectSignatureMismatch]);
    m.functions[1].blocks[0].body = vec![call(SPAWN), ret()];
    m.functions.push(declaration(SPAWN));
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Spawns));

    // A closure constant joins the pool of its stated closure type's
    // apparent signature (`fn(u32)`), not of its body's physical one.
    let closure_pool = |sig: u32| {
        let mut m = pool_module(vec![indirect(sig), ret()]);
        m.functions[0].blocks[0]
            .params
            .push((v(1), Ty::Func(ft(sig))));
        m.closure_types.push(ClosureTy::bare(ft(1)));
        m.functions[3].blocks[0].body[0] = node(Inst::Const {
            ty: Ty::Closure(ClosureTyId::new(0)),
            value: Constant::Closure {
                func: f(101),
                captures: vec![],
            },
        })
        .with_result(v(9));
        let reach = walk(&m, &seeds());
        assert_eq!(reach.function_verdict(f(202)), Some(Verdict::Escapes));
        reach.function_verdict(f(37))
    };
    assert_eq!(closure_pool(1), Some(Verdict::Indirect));
    assert_eq!(closure_pool(0), Some(Verdict::Quiet));

    // A signature the module does not define is UNKNOWN.
    let mut m = pool_module(vec![indirect(77), ret()]);
    m.functions[0].blocks[0].params.push((v(1), Ty::Ptr));
    let reach = walk(&m, &seeds());
    assert_eq!(
        sink_reasons(&reach, 37),
        [R::Missing(N::FunctionType(ft(77)))]
    );
}

/// Rule H on the trust-ir lane: foreign code handed a function pointer may
/// call it (R3), so the caller is charged with the pointer's pool.
#[test]
fn trust_ir_foreign_handoffs_are_charged_by_rule_h() {
    let mut m = pool_module(vec![call(303), call(304), ret()]);
    let mut takes_callback = declaration(303);
    takes_callback.ty = ft(2);
    let mut takes_int = declaration(304);
    takes_int.ty = ft(1);
    m.functions.push(takes_callback);
    m.functions.push(takes_int);
    let classes = seeds()
        .with(303, FunctionClass::Foreign)
        .with(304, FunctionClass::Foreign);
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Indirect));
    // Only the callback-taking call is charged.
    m.functions[0].blocks[0].body.remove(0);
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Quiet));
}

/// Globals are READ, their initializers CREATE (a function pointer in memory
/// is a non-confined member), and a global with no initializer is UNKNOWN.
#[test]
fn trust_ir_globals_read_their_initializers() {
    let mut m = spawn_module(vec![
        node(Inst::GlobalAddr {
            global: GlobalId::new(0),
        }),
        ret(),
    ]);
    m.globals.push(global(
        "TABLE",
        Some(Constant::Aggregate(vec![address("symbol_101")])),
    ));
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Escapes));
    let members = reach.census().expanded().pools().members();
    assert!(members.iter().all(|member| !member.confined));
    assert_eq!(members.len(), 1);
    m.globals[0].initializer = None;
    let reach = walk(&m, &seeds());
    assert_eq!(
        sink_reasons(&reach, 37),
        [R::MissingGlobalInitializer(GlobalId::new(0))]
    );
}

/// Runtime services are classified, never silently skipped: a failed
/// `Assert` runs the panic hook (p04), `HeapAlloc` the global allocator (j04).
#[test]
fn trust_ir_runtime_services_are_classified() {
    let m = spawn_module(vec![
        node(Inst::Assert {
            cond: v(1),
            kind: AssertKind::Unspecified,
            site: None,
        }),
        ret(),
    ]);
    let reach = walk(&m, &seeds());
    assert_eq!(sink_reasons(&reach, 37), [R::UnresolvedExtern]);
    let quiet = seeds().service(RuntimeService::Panic, ServiceClass::Foreign);
    assert_eq!(
        walk(&m, &quiet).function_verdict(f(37)),
        Some(Verdict::Quiet)
    );

    let m = spawn_module(vec![
        node(Inst::HeapAlloc {
            ty: Ty::U8,
            count: None,
            align: None,
            origin: trust_ir::inst::AllocOrigin::RustHeap,
        }),
        ret(),
    ]);
    let allocator = seeds().service(
        RuntimeService::Allocate(trust_ir::inst::AllocOrigin::RustHeap),
        ServiceClass::Resolved(f(101)),
    );
    assert_eq!(
        walk(&m, &allocator).function_verdict(f(37)),
        Some(Verdict::Spawns)
    );
}

#[test]
fn trust_ir_opaque_operations_and_global_assembly_are_unknown() {
    let m = spawn_module(vec![
        node(Inst::DialectOp(Box::new(
            trust_ir::dialect::DialectInst::new("opaque", "call"),
        ))),
        ret(),
    ]);
    let reach = walk(&m, &seeds());
    assert_eq!(sink_reasons(&reach, 37), [R::OpaqueDialectOperation]);
    let mut m = spawn_module(vec![ret()]);
    m.global_asm.push("retained".into());
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Unknown));
    // A path to a seed outranks the module-wide sink.
    assert_eq!(reach.function_verdict(f(101)), Some(Verdict::Spawns));
    assert_eq!(reach.function_verdict(f(SPAWN)), Some(Verdict::Spawns));
}

/// A seed declaration that names its spawned callable gives the thread an
/// entry: one node per seed, where the thread starts, which runs the callable
/// (Trust design 2026-10-02, "C1", N-4). The root's closure stops at the seed;
/// the entry's closure runs on the new thread. It is modelable only with a
/// summary of the std code around the callable; without one the start is
/// opaque. Either way no function's verdict moves.
#[test]
fn trust_ir_seed_declarations_name_their_thread_entry() {
    let mut m = spawn_module(vec![call(SPAWN), ret()]);
    m.functions.push(function(606, vec![call(707), ret()]));
    m.functions.push(function(707, vec![ret()]));
    let seed = |child: Option<PrimitiveSummary>| {
        Classes::default().with(
            SPAWN,
            FunctionClass::Seed {
                spawned: Some(f(606)),
                child,
            },
        )
    };
    let summarized = walk(&m, &seed(Some(PrimitiveSummary::default())));
    let unsummarized = walk(&m, &seed(None));
    for (reach, body, modelable) in [
        (&summarized, NodeBody::Primitive, true),
        (&unsummarized, NodeBody::Opaque, false),
    ] {
        let sites = reach.census().spawn_sites().expect("no fallback");
        assert_eq!(sites.len(), 2, "37 and 101 each call the seed");
        let start = sites[0].entry.expect("named");
        assert!(sites.iter().all(|site| site.entry == Some(start)));
        assert_eq!(
            reach.census().expanded().node(start),
            Some(&ReachNodeKind::Program(ReachNodeSpec {
                origin: NodeOrigin::TrustIrThreadStart(f(SPAWN)),
                definition: None,
                locality: Locality::Local,
                body,
            }))
        );
        let root = reach
            .census()
            .thread_closure(reach.node(N::Function(f(37))));
        assert!(!root.contains(start));
        assert!(!root.contains(reach.node(N::Function(f(707))).expect("walked")));
        let thread = reach.census().thread_closure(Some(start));
        assert!(thread.contains(reach.node(N::Function(f(606))).expect("walked")));
        assert!(thread.contains(reach.node(N::Function(f(707))).expect("walked")));
        assert_eq!(thread.modelable(), modelable);
        assert_eq!(sites[0].edge.class, EdgeClass::Run, "the call itself");
    }
    for function in &m.functions {
        assert_eq!(
            summarized.function_verdict(function.id),
            unsummarized.function_verdict(function.id)
        );
    }
}

/// N-4: the std code a seed's thread runs around its callable is part of
/// what that thread runs. Root 37 calls the seed 900, which starts the quiet
/// 606. 303 makes the quiet 505 a `fn()` callable, 304 the spawning 707 one
/// (with `spawning_hook`); 616 is a callback that spawns; 808, the glue of
/// `Struct(81)`, is quiet; 313 is foreign code of signature 1, `fn(fn())`,
/// which 314 makes a callable of.
fn thread_start_module(spawning_hook: bool) -> Module {
    let mut m = spawn_module(vec![call(SPAWN), ret()]);
    m.func_types.push(FuncTy {
        abi: None,
        params: vec![Ty::Func(ft(0))],
        returns: vec![],
        is_vararg: false,
    });
    for id in [606, 505, 808] {
        m.functions.push(function(id, vec![ret()]));
    }
    m.functions.push(function(616, vec![call(SPAWN), ret()]));
    m.functions.push(function(707, vec![call(101), ret()]));
    let creator = |id: u32, sig: u32, callable: u32| {
        function(
            id,
            vec![
                node(Inst::Const {
                    ty: Ty::Func(ft(sig)),
                    value: Constant::FnDef(f(callable)),
                })
                .with_result(v(9)),
                ret(),
            ],
        )
    };
    m.functions.push(creator(303, 0, 505));
    if spawning_hook {
        m.functions.push(creator(304, 0, 707));
    }
    let mut foreign = declaration(FOREIGN);
    foreign.ty = ft(1);
    m.functions.push(foreign);
    m.functions.push(creator(314, 1, FOREIGN));
    m.set_drop_glue(Ty::Struct(StructId::new(GLUED)), f(808))
        .expect("a glue row");
    m
}

#[test]
fn trust_ir_a_threads_closure_holds_the_std_code_around_its_callable() {
    let hooks = || PrimitiveInvoke {
        key: unit_fn_key(),
        carried: vec![],
    };
    let full = PrimitiveSummary {
        runs: vec![],
        services: vec![RuntimeService::Panic],
        invokes: vec![hooks()],
        glue: vec![Ty::Struct(StructId::new(GLUED))],
    };
    // (name, child summary, a spawning hook, the start's verdict, modelable)
    let cases: Vec<(&str, PrimitiveSummary, bool, Verdict, bool)> = vec![
        (
            "quiet hooks and glue",
            full.clone(),
            false,
            Verdict::Quiet,
            true,
        ),
        (
            "a spawning hook",
            full.clone(),
            true,
            Verdict::Indirect,
            false,
        ),
        (
            "glue with no row",
            PrimitiveSummary {
                glue: vec![Ty::Struct(StructId::new(UNGLUED))],
                ..full.clone()
            },
            false,
            Verdict::Unknown,
            false,
        ),
        (
            "an open principal",
            PrimitiveSummary {
                invokes: vec![PrimitiveInvoke {
                    key: PoolKey::DynDrop(PrincipalKey(5)),
                    carried: vec![],
                }],
                ..full.clone()
            },
            false,
            Verdict::Unknown,
            false,
        ),
        (
            "a spawning hook handed to foreign code",
            PrimitiveSummary {
                invokes: vec![PrimitiveInvoke {
                    key: callback_fn_key(),
                    carried: vec![CarriedKey::Key(unit_fn_key())],
                }],
                ..full.clone()
            },
            true,
            Verdict::Indirect,
            false,
        ),
        (
            "a callback that starts another thread",
            PrimitiveSummary {
                runs: vec![f(616)],
                ..full.clone()
            },
            false,
            Verdict::Spawns,
            true,
        ),
    ];
    for (name, child, spawning_hook, verdict, modelable) in cases {
        let m = thread_start_module(spawning_hook);
        let classes = Classes::default()
            .with(
                SPAWN,
                FunctionClass::Seed {
                    spawned: Some(f(606)),
                    child: Some(child.clone()),
                },
            )
            .with(FOREIGN, FunctionClass::Foreign)
            .service(RuntimeService::Panic, ServiceClass::Foreign);
        let reach = walk(&m, &classes);
        let node = |id: u32| reach.node(N::Function(f(id))).expect("a node");
        let sites = reach.census().spawn_sites().expect("no fallback");
        let start = sites
            .iter()
            .find(|site| site.edge.from == node(37))
            .and_then(|site| site.entry)
            .expect("named");
        assert_eq!(reach.census().verdict(start), verdict, "{name}");
        let thread = reach.census().thread_closure(Some(start));
        assert_eq!(thread.modelable(), modelable, "{name}");
        // The callable alone is quiet and modelable: only the start's
        // closure holds the code around it.
        let callable = reach.census().thread_closure(Some(node(606)));
        assert!(callable.modelable(), "{name}");
        assert_eq!(
            reach.function_verdict(f(37)),
            Some(Verdict::Spawns),
            "{name}"
        );
        assert!(!callable.contains(node(505)), "{name}");
        assert!(!callable.contains(node(808)), "{name}");
        if child.invokes == [hooks()] {
            assert!(thread.contains(node(505)), "{name}: the hook pool");
        }
        if child.glue == [Ty::Struct(StructId::new(GLUED))] {
            assert!(thread.contains(node(808)), "{name}: the glue");
        }
        // Its facts are ordinary ones: a sink among them, or an invoke of an
        // open principal, leaves the pools unclosed, as anywhere else.
        assert_eq!(
            reach.census().expanded().pools().unclosed(),
            matches!(name, "glue with no row" | "an open principal"),
            "{name}"
        );
        if !child.runs.is_empty() {
            assert!(thread.contains(node(616)), "{name}: the callback");
            assert!(thread.contains(node(SPAWN)), "{name}: a nested spawn");
            assert!(
                sites.iter().any(|site| site.edge.from == node(616)),
                "{name}: the callback is a spawn site"
            );
        }
    }
}

/// A callable value the walk cannot name — minted inside a bodyless callee
/// the classifier calls UNKNOWN, or named by an unresolved symbol, a missing
/// function id, or a global whose contents are not in the module — leaves
/// every pool unclosed: its invoker is UNKNOWN, never QUIET.
#[test]
fn trust_ir_an_unnamed_callable_leaves_its_invoker_unknown() {
    // 37: let f = store(); h(f);   h (302): f()   store (301): bodyless.
    let mut m = pool_module(vec![
        call(301).with_result(v(5)),
        node(Inst::Call {
            callee: f(302),
            args: vec![v(5)],
        }),
        ret(),
    ]);
    m.functions.retain(|function| function.id != f(202));
    m.functions.push(declaration(301));
    let mut h = function(302, vec![indirect(0), ret()]);
    h.blocks[0].params.push((v(1), Ty::Func(ft(0))));
    m.functions.push(h);
    // Foreign code returns only a callable it was handed or its own (R3).
    let closed = walk(&m, &seeds().with(301, FunctionClass::Foreign));
    assert_eq!(closed.function_verdict(f(302)), Some(Verdict::Quiet));
    let classes = seeds().with(301, FunctionClass::Unknown(R::UnresolvedExtern));
    let reach = walk(&m, &classes);
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Unknown));
    assert_eq!(reach.function_verdict(f(302)), Some(Verdict::Unknown));
    assert_eq!(sink_reasons(&reach, 302), [R::UnclosedPool]);

    // 202 mints the value from a name the module cannot resolve; 37 calls
    // through its argument.
    let unnamed = |value: Constant, global: Option<Global>| {
        let mut m = pool_module(vec![indirect(0), ret()]);
        m.functions[0].blocks[0]
            .params
            .push((v(1), Ty::Func(ft(0))));
        m.functions[3].blocks[0].body[0] = node(Inst::Const {
            ty: Ty::Func(ft(0)),
            value,
        })
        .with_result(v(9));
        if let Some(global) = global {
            m.functions[3].blocks[0].body.insert(
                0,
                node(Inst::GlobalAddr {
                    global: GlobalId::new(0),
                })
                .with_result(v(12)),
            );
            m.globals.push(global);
        }
        let reach = walk(&m, &seeds());
        assert_eq!(reach.function_verdict(f(202)), Some(Verdict::Unknown));
        reach.function_verdict(f(37))
    };
    for (value, global) in [
        (address("not_in_module"), None),
        (Constant::FnDef(f(1234)), None),
        (Constant::Int(0), Some(global("vtable", None))),
    ] {
        assert_eq!(
            unnamed(value.clone(), global),
            Some(Verdict::Unknown),
            "{value:?}"
        );
    }
}

/// The producer leaves bodies at the default convention (C) and stamps
/// `Rust` on fn-pointer calls, so trust-ir pools state no convention: a
/// Rust-convention call through a pointer still reaches the member.
#[test]
fn trust_ir_pools_ignore_the_producers_conventions() {
    for conv in [CallingConv::C, CallingConv::Rust] {
        let mut call = indirect(0);
        if let Inst::CallIndirect { calling_conv, .. } = &mut call.inst {
            *calling_conv = conv;
        }
        let mut m = pool_module(vec![call, ret()]);
        m.functions[0].blocks[0]
            .params
            .push((v(1), Ty::Func(ft(0))));
        let reach = walk(&m, &seeds());
        assert_eq!(
            reach.function_verdict(f(37)),
            Some(Verdict::Indirect),
            "{conv:?}"
        );
    }
}

/// Rule H on C varargs: the variadic part has no stated type, so it may
/// carry any callable, and foreign code handed one may call it (R3).
#[test]
fn trust_ir_callables_passed_through_c_varargs_are_charged() {
    let build = |variadic: bool| {
        let mut m = pool_module(vec![call(303), ret()]);
        // 3: fn(i32, ...); 4: fn(i32)
        for is_vararg in [true, false] {
            m.func_types.push(FuncTy {
                abi: None,
                params: vec![Ty::I32],
                returns: vec![],
                is_vararg,
            });
        }
        let mut printf = declaration(303);
        printf.ty = ft(if variadic { 3 } else { 4 });
        m.functions.push(printf);
        let reach = walk(&m, &seeds().with(303, FunctionClass::Foreign));
        reach.function_verdict(f(37))
    };
    assert_eq!(build(false), Some(Verdict::Quiet));
    assert_eq!(build(true), Some(Verdict::Indirect));
}

/// `spawner as usize` (a LAUNDER) handed to foreign code that calls it back:
/// after a LAUNDER, data may hold any callable.
#[test]
fn trust_ir_a_laundered_integer_handed_to_foreign_code_is_charged() {
    let build = |launder: bool| {
        let mut m = pool_module(vec![call(304), ret()]);
        if launder {
            m.functions[3].blocks[0].body.insert(
                1,
                node(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Func(ft(0)),
                    dst_ty: Ty::Usize,
                    operand: v(9),
                })
                .with_result(v(10)),
            );
        }
        let mut signal = declaration(304);
        signal.ty = ft(1);
        m.functions.push(signal);
        let reach = walk(&m, &seeds().with(304, FunctionClass::Foreign));
        assert_eq!(reach.census().expanded().pools().laundered(), launder);
        reach.function_verdict(f(37))
    };
    assert_eq!(build(false), Some(Verdict::Quiet));
    assert_eq!(build(true), Some(Verdict::Indirect));
}

/// The walk covers the whole module, so a CREATE in a function nothing calls
/// still fills its pool, and every function has a verdict.
#[test]
fn trust_ir_every_function_and_global_is_walked() {
    let mut m = pool_module(vec![indirect(0), ret()]);
    m.functions[0].blocks[0]
        .params
        .push((v(1), Ty::Func(ft(0))));
    m.globals
        .push(global("UNREFERENCED", Some(address("symbol_101"))));
    let reach = walk(&m, &seeds());
    for function in &m.functions {
        assert!(reach.function_verdict(function.id).is_some());
    }
    assert_eq!(reach.function_verdict(f(202)), Some(Verdict::Escapes));
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Indirect));
    let global = reach.node(N::Global(GlobalId::new(0))).expect("walked");
    assert_eq!(reach.census().verdict(global), Verdict::Escapes);
}

/// Any two zero-sized, 1-aligned types are ABI-compatible: a call through
/// `fn([u8; 0])` may reach a callable created as `fn(S)` for `struct S;`.
#[test]
fn trust_ir_zero_sized_argument_shapes_share_a_pool() {
    let mut m = pool_module(vec![indirect(4), ret()]);
    m.structs.push(StructDef {
        fields: vec![],
        size: Some(0),
        align: Some(1),
        ..structure(1, Ty::Unit)
    });
    m.types.push(Ty::U8);
    // 3: fn(S); 4: fn([u8; 0])
    for param in [Ty::Struct(StructId::new(1)), Ty::Array(TyId::new(0), 0)] {
        m.func_types.push(FuncTy {
            abi: None,
            params: vec![param],
            returns: vec![],
            is_vararg: false,
        });
    }
    m.functions[2].ty = ft(3);
    m.functions[3].blocks[0].body[0] = node(Inst::Const {
        ty: Ty::Func(ft(3)),
        value: Constant::FnDef(f(101)),
    })
    .with_result(v(9));
    m.functions[0].blocks[0]
        .params
        .push((v(1), Ty::Func(ft(4))));
    let reach = walk(&m, &seeds());
    assert!(!reach.census().expanded().pools().laundered());
    assert_eq!(reach.function_verdict(f(202)), Some(Verdict::Escapes));
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Indirect));
}

/// An id two definitions share is one node standing for both: UNKNOWN, its
/// bodies not walked, so the pools are unclosed too.
#[test]
fn trust_ir_an_ambiguous_function_id_is_one_unknown_node() {
    let mut m = pool_module(vec![call(505), ret()]);
    m.functions.push(function(505, vec![ret()]));
    m.functions.push(function(505, vec![call(SPAWN), ret()]));
    let reach = walk(&m, &seeds());
    assert_eq!(reach.function_verdict(f(505)), Some(Verdict::Unknown));
    assert_eq!(reach.function_verdict(f(37)), Some(Verdict::Unknown));
    assert_eq!(
        sink_reasons(&reach, 505),
        [R::Ambiguous(N::Function(f(505)))]
    );
    assert!(reach.census().expanded().pools().unclosed());
}

// ===========================================================================
// Primitives (Trust design 2026-10-02, "C1", §3.2; T-ir2, T-ir3)
// ===========================================================================

const PRIMITIVE: u32 = 800;
/// `Struct(81)` has drop glue (808); `Struct(82)` has none.
const GLUED: u32 = 81;
const UNGLUED: u32 = 82;

/// The trust-ir lane's `fn()` pool key: what a `CallIndirect` through
/// signature 0 is charged by.
fn unit_fn_key() -> PoolKey {
    PoolKey::Fn(FnShape {
        abi: None,
        variadic: Some(false),
        params: Some(vec![]),
    })
}

/// Foreign code of signature 1, `fn(fn())`: a member of that pool, which
/// may call back the `fn()` it is handed (R3).
const FOREIGN: u32 = 313;

/// The trust-ir lane's `fn(fn())` pool key: what a `CallIndirect` through
/// signature 1 is charged by.
fn callback_fn_key() -> PoolKey {
    PoolKey::Fn(FnShape {
        abi: None,
        variadic: Some(false),
        params: Some(vec![ArgClass::ThinPointer]),
    })
}

/// Root 37 calls the primitive 800. 606 is a callback, 707 a `fn()`
/// callable that 303 creates, and 808 the glue of `Struct(81)`; each calls
/// 101, which spawns. 314 makes the foreign 313 a `fn(fn())` callable. With
/// `twin`, 800 is a walked body doing what `summary` lists through
/// instructions; without, a declaration. Classify 313 as foreign.
fn primitive_module(summary: &PrimitiveSummary, twin: bool) -> Module {
    let mut m = spawn_module(vec![call(PRIMITIVE), ret()]);
    m.func_types.push(FuncTy {
        abi: None,
        params: vec![Ty::Func(ft(0))],
        returns: vec![],
        is_vararg: false,
    });
    for id in [606, 707, 808] {
        m.functions.push(function(id, vec![call(101), ret()]));
    }
    m.functions.push(function(
        303,
        vec![
            node(Inst::Const {
                ty: Ty::Func(ft(0)),
                value: Constant::FnDef(f(707)),
            })
            .with_result(v(9)),
            ret(),
        ],
    ));
    let mut foreign = declaration(FOREIGN);
    foreign.ty = ft(1);
    m.functions.push(foreign);
    m.functions.push(function(
        314,
        vec![
            node(Inst::Const {
                ty: Ty::Func(ft(1)),
                value: Constant::FnDef(f(FOREIGN)),
            })
            .with_result(v(9)),
            ret(),
        ],
    ));
    m.set_drop_glue(Ty::Struct(StructId::new(GLUED)), f(808))
        .expect("a glue row");
    if !twin {
        m.functions.push(declaration(PRIMITIVE));
        return m;
    }
    let mut body: Vec<InstrNode> = summary
        .runs
        .iter()
        .map(|callback| call(callback.index()))
        .collect();
    for service in &summary.services {
        assert_eq!(*service, RuntimeService::Panic, "the twin spells only this");
        body.push(node(Inst::Assert {
            cond: v(2),
            kind: AssertKind::Unspecified,
            site: None,
        }));
    }
    for invoke in &summary.invokes {
        // A `CallIndirect` through signature `sig` carries what the
        // signature's arguments carry.
        let sig = if invoke.key == unit_fn_key() {
            assert_eq!(invoke.carried, [], "the twin spells only this");
            0
        } else {
            assert_eq!(invoke.key, callback_fn_key(), "the twin spells only this");
            assert_eq!(
                invoke.carried,
                [CarriedKey::Key(unit_fn_key())],
                "the twin spells only this"
            );
            1
        };
        body.push(indirect(sig));
    }
    for ty in &summary.glue {
        body.push(node(Inst::Drop {
            ty: ty.clone(),
            ptr: v(3),
        }));
    }
    body.push(ret());
    let mut twin = function(PRIMITIVE, body);
    twin.blocks[0].params.push((v(1), Ty::Func(ft(0))));
    m.functions.push(twin);
    m
}

/// What a witness says, without its sites: per edge, the class, the drop
/// flag and where it lands (a function or global, or a sink's reason).
type WitnessShape = (Verdict, bool, Vec<(EdgeClass, bool, Result<N, R>)>);

fn witness_shape(reach: &ModuleReachability<'_>, id: u32) -> Option<WitnessShape> {
    let census = reach.census();
    let witness = census.witness(reach.node(N::Function(f(id)))?)?;
    let path = witness
        .path
        .iter()
        .map(|edge| {
            let to = match census.expanded().node(edge.to) {
                Some(ReachNodeKind::Program(ReachNodeSpec {
                    origin: NodeOrigin::TrustIr(node),
                    ..
                })) => Ok(*node),
                Some(ReachNodeKind::Sink(reason)) => Err(reason.clone()),
                other => panic!("not a trust-ir node: {other:?}"),
            };
            (edge.class, edge.via_drop, to)
        })
        .collect();
    Some((witness.verdict, witness.via_drop, path))
}

/// T-ir2: each item of a primitive's summary is the ordinary fact its
/// instruction adds in a walked body. The primitive and its walked twin get
/// the same verdict and witness for every function, the same spawn sites and
/// the same modelable closure; the certificate checker accepts both (`walk`).
/// An invoke whose pool holds foreign code is charged by rule H with what it
/// carries, as the twin's indirect call is: the primitive is a local node.
#[test]
fn trust_ir_a_primitive_summary_adds_the_facts_a_walked_body_would() {
    let cases: Vec<(&str, PrimitiveSummary, Classes, Verdict)> = vec![
        (
            "nothing",
            PrimitiveSummary::default(),
            seeds(),
            Verdict::Quiet,
        ),
        (
            "runs a spawning callback",
            PrimitiveSummary {
                runs: vec![f(606)],
                ..PrimitiveSummary::default()
            },
            seeds(),
            Verdict::Spawns,
        ),
        (
            "uses an unclassified panic service",
            PrimitiveSummary {
                services: vec![RuntimeService::Panic],
                ..PrimitiveSummary::default()
            },
            seeds(),
            Verdict::Unknown,
        ),
        (
            "uses a spawning panic hook",
            PrimitiveSummary {
                services: vec![RuntimeService::Panic],
                ..PrimitiveSummary::default()
            },
            seeds().service(RuntimeService::Panic, ServiceClass::Resolved(f(101))),
            Verdict::Spawns,
        ),
        (
            "uses a foreign panic runtime",
            PrimitiveSummary {
                services: vec![RuntimeService::Panic],
                ..PrimitiveSummary::default()
            },
            seeds().service(RuntimeService::Panic, ServiceClass::Foreign),
            Verdict::Quiet,
        ),
        (
            "invokes a pool holding a spawning callable",
            PrimitiveSummary {
                invokes: vec![PrimitiveInvoke {
                    key: unit_fn_key(),
                    carried: vec![],
                }],
                ..PrimitiveSummary::default()
            },
            seeds(),
            Verdict::Indirect,
        ),
        (
            "hands a spawning callable to foreign code it invokes",
            PrimitiveSummary {
                invokes: vec![PrimitiveInvoke {
                    key: callback_fn_key(),
                    carried: vec![CarriedKey::Key(unit_fn_key())],
                }],
                ..PrimitiveSummary::default()
            },
            seeds(),
            Verdict::Indirect,
        ),
        (
            "runs spawning drop glue",
            PrimitiveSummary {
                glue: vec![Ty::Struct(StructId::new(GLUED))],
                ..PrimitiveSummary::default()
            },
            seeds(),
            Verdict::Spawns,
        ),
        (
            "drops a type with no glue row",
            PrimitiveSummary {
                glue: vec![Ty::Struct(StructId::new(UNGLUED))],
                ..PrimitiveSummary::default()
            },
            seeds(),
            Verdict::Unknown,
        ),
        (
            "all of it",
            PrimitiveSummary {
                runs: vec![f(606)],
                services: vec![RuntimeService::Panic],
                invokes: vec![
                    PrimitiveInvoke {
                        key: unit_fn_key(),
                        carried: vec![],
                    },
                    PrimitiveInvoke {
                        key: callback_fn_key(),
                        carried: vec![CarriedKey::Key(unit_fn_key())],
                    },
                ],
                glue: vec![
                    Ty::Struct(StructId::new(GLUED)),
                    Ty::Struct(StructId::new(UNGLUED)),
                ],
            },
            seeds(),
            Verdict::Spawns,
        ),
    ];
    for (name, summary, classes, expected) in cases {
        let classes = classes.with(FOREIGN, FunctionClass::Foreign);
        let declared = primitive_module(&summary, false);
        let walked = primitive_module(&summary, true);
        let as_primitive = classes
            .clone()
            .with(PRIMITIVE, FunctionClass::Primitive(summary.clone()));
        let primitive = walk(&declared, &as_primitive);
        let twin = walk(&walked, &classes);
        assert_eq!(
            primitive.function_verdict(f(PRIMITIVE)),
            Some(expected),
            "{name}"
        );
        for function in &walked.functions {
            let id = function.id.index();
            assert_eq!(
                primitive.function_verdict(function.id),
                twin.function_verdict(function.id),
                "{name}: {id}"
            );
            if summary.runs.len()
                + summary.services.len()
                + summary.invokes.len()
                + summary.glue.len()
                == 1
            {
                assert_eq!(
                    witness_shape(&primitive, id),
                    witness_shape(&twin, id),
                    "{name}: {id}"
                );
            }
        }
        let sites = |reach: &ModuleReachability<'_>| {
            reach
                .census()
                .spawn_sites()
                .expect("no fallback")
                .iter()
                .map(
                    |site| match reach.census().expanded().node(site.edge.from) {
                        Some(ReachNodeKind::Program(spec)) => spec.origin,
                        other => panic!("{other:?}"),
                    },
                )
                .collect::<Vec<_>>()
        };
        assert_eq!(sites(&primitive), sites(&twin), "{name}");
        let closure = |reach: &ModuleReachability<'_>| {
            reach
                .census()
                .thread_closure(reach.node(N::Function(f(37))))
                .modelable()
        };
        assert_eq!(closure(&primitive), closure(&twin), "{name}");
        assert!(matches!(
            primitive
                .census()
                .expanded()
                .node(primitive.node(N::Function(f(PRIMITIVE))).expect("a node")),
            Some(ReachNodeKind::Program(ReachNodeSpec {
                body: NodeBody::Primitive,
                locality: Locality::Local,
                ..
            }))
        ));
    }
}

/// T-ir2: a primitive is never a spawn claim. It reaches a seed only through
/// what its summary runs, so its witness leaves it by that RUN edge; a spawn
/// fact into it is a defect, as is any edge out of a seed into it.
#[test]
fn a_primitive_is_never_a_spawn_claim() {
    let summary = PrimitiveSummary {
        runs: vec![f(606)],
        ..PrimitiveSummary::default()
    };
    let m = primitive_module(&summary, false);
    let reach = walk(
        &m,
        &seeds().with(PRIMITIVE, FunctionClass::Primitive(summary)),
    );
    let (verdict, _, path) = witness_shape(&reach, PRIMITIVE).expect("refused");
    assert_eq!(verdict, Verdict::Spawns);
    assert_eq!(path[0], (EdgeClass::Run, false, Ok(N::Function(f(606)))));
    let primitive = reach.node(N::Function(f(PRIMITIVE))).expect("a node");
    let sites = reach.census().spawn_sites().expect("no fallback");
    assert!(sites.iter().all(|site| site.edge.to != primitive));
    assert!(
        sites
            .iter()
            .all(|site| site.edge.from == reach.node(N::Function(f(101))).expect("walked"))
    );

    for spawn_into in [true, false] {
        let mut g = Facts::new();
        g.seed("spawn");
        g.local("caller");
        g.primitive("scope");
        let (seed, caller, scope) = (g.n("spawn"), g.n("caller"), g.n("scope"));
        let expected = if spawn_into {
            g.graph
                .add_spawn(caller, scope, None, ReachSite::Mir(0), false);
            ReachDefect::SpawnOfNonSeed(scope)
        } else {
            g.run("spawn", "scope");
            ReachDefect::EdgeFromTerminal(seed)
        };
        let census = g.graph.solve();
        assert_eq!(
            census.fallback(),
            Some(&ReachFallback::Defects(vec![expected]))
        );
        assert_eq!(census.spawn_sites(), None);
        assert_eq!(census.verdict(scope), Verdict::Unknown);
    }
}

/// T-ir3: a closure through a primitive is modelable, and stays so while the
/// pools its summary invokes are closed. An invoke of an open principal, or
/// of any key once a sink leaves the pools unclosed, ends at an UNKNOWN sink
/// and is not.
#[test]
fn trust_ir_a_closure_through_a_primitive_is_modelable_until_a_pool_is_open() {
    let build = |invokes: Vec<PrimitiveInvoke>, unclosed: bool| {
        // 37 runs the primitive, which runs 606; 606 starts 707; 303
        // creates the quiet `fn()` callable 505.
        let mut m = spawn_module(vec![call(PRIMITIVE), ret()]);
        m.functions.push(declaration(PRIMITIVE));
        m.functions.push(function(606, vec![call(SPAWN), ret()]));
        m.functions.push(function(707, vec![ret()]));
        m.functions.push(function(505, vec![ret()]));
        m.functions.push(function(
            303,
            vec![
                node(Inst::Const {
                    ty: Ty::Func(ft(0)),
                    value: Constant::FnDef(f(505)),
                })
                .with_result(v(9)),
                ret(),
            ],
        ));
        let mut classes = Classes::default()
            .with(
                SPAWN,
                FunctionClass::Seed {
                    spawned: Some(f(707)),
                    child: Some(PrimitiveSummary::default()),
                },
            )
            .with(
                PRIMITIVE,
                FunctionClass::Primitive(PrimitiveSummary {
                    runs: vec![f(606)],
                    invokes,
                    ..PrimitiveSummary::default()
                }),
            );
        if unclosed {
            m.functions.push(declaration(405));
            classes = classes.with(405, FunctionClass::Unknown(R::UnresolvedExtern));
        }
        (m, classes)
    };
    let fn_invoke = || PrimitiveInvoke {
        key: unit_fn_key(),
        carried: vec![],
    };
    let cases = [
        ("no invoke", vec![], false, true),
        ("a closed pool", vec![fn_invoke()], false, true),
        (
            "an open principal",
            vec![PrimitiveInvoke {
                key: PoolKey::DynDrop(PrincipalKey(5)),
                carried: vec![],
            }],
            false,
            false,
        ),
        ("an unclosed pool", vec![fn_invoke()], true, false),
    ];
    for (name, invokes, unclosed, modelable) in cases {
        let (m, classes) = build(invokes, unclosed);
        let reach = walk(&m, &classes);
        let node = |id: u32| reach.node(N::Function(f(id))).expect("a node");
        let root = reach.census().thread_closure(Some(node(37)));
        assert!(root.contains(node(PRIMITIVE)), "{name}");
        assert!(root.contains(node(606)), "{name}");
        assert!(!root.contains(node(707)), "{name}: another thread");
        assert_eq!(root.modelable(), modelable, "{name}");
        let sites = reach.census().spawn_sites().expect("no fallback");
        assert_eq!(sites.len(), 2, "{name}: 101 and 606 call the seed");
        let child = reach.census().thread_closure(sites[0].entry);
        assert!(child.contains(node(707)), "{name}");
        assert!(child.modelable(), "{name}");
    }
}

#[path = "function_dependencies/defined_roots.rs"]
mod defined_roots;
