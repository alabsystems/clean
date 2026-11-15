// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_tables_and_independent_seedless_cycles_match_all_original_bits() {
    parity(
        &Module::new(""),
        &[Ty::Bool, array(0), Ty::Func(FuncTyId::new(99))],
    );
    let mut m = Module::new("");
    m.types = vec![array(1), array(0), array(2)];
    parity(&m, &m.types);
}
#[test]
fn every_table_edge_and_three_independent_axes_match_exact_original_fixpoints() {
    let m = fixture();
    parity(
        &m,
        &[
            array(0),
            array(1),
            array(2),
            array(3),
            array(4),
            Ty::Struct(StructId::new(70)),
            Ty::Enum(EnumId::new(90)),
            Ty::Record(RecordId::new(100)),
            Ty::Closure(ClosureTyId::new(0)),
        ],
    );
}
#[test]
fn duplicate_ids_combine_all_physical_definitions_at_the_first_vertex() {
    let mut m = Module::new("");
    m.structs = vec![
        structure(9, Ty::Bool),
        structure(9, dialect()),
        structure(9, handle()),
    ];
    m.enums = vec![enumeration(19, dialect()), enumeration(19, handle())];
    m.records = vec![record(29, handle()), record(29, dialect())];
    parity(
        &m,
        &[
            Ty::Struct(StructId::new(9)),
            Ty::Enum(EnumId::new(19)),
            Ty::Record(RecordId::new(29)),
        ],
    );
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert!(out.reachable[0][0] && out.reachable[1][0]);
    assert!(!out.reachable[0][1] && !out.reachable[1][2]);
    out.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn sparse_off_index_names_and_namespace_collisions_remain_exact() {
    let mut m = Module::new("");
    m.types = vec![dialect()];
    m.structs = vec![structure(u32::MAX, handle())];
    m.enums = vec![enumeration(u32::MAX, dialect())];
    m.records = vec![record(u32::MAX, Ty::Func(FuncTyId::new(99)))];
    parity(
        &m,
        &[
            array(0),
            Ty::Struct(StructId::new(u32::MAX)),
            Ty::Enum(EnumId::new(u32::MAX)),
            Ty::Record(RecordId::new(u32::MAX)),
            Ty::Struct(StructId::new(0)),
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(0)),
        ],
    );
}
#[test]
fn closure_signature_edges_and_captures_are_both_propagated() {
    let mut m = Module::new("");
    m.func_types = vec![FuncTy::unrecorded(vec![dialect()], vec![handle()], false)];
    m.closure_types = vec![
        ClosureTy::bare(FuncTyId::new(0)),
        ClosureTy {
            func: FuncTyId::new(999),
            captures: vec![dialect(), handle()],
        },
        ClosureTy::bare(FuncTyId::new(999)),
    ];
    parity(
        &m,
        &[
            Ty::Func(FuncTyId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Closure(ClosureTyId::new(1)),
            Ty::Closure(ClosureTyId::new(2)),
        ],
    );
}
#[test]
fn every_inline_container_and_table_referent_uses_original_preorder_rules() {
    let mut m = Module::new("");
    m.types = vec![Ty::Tuple(vec![
        dialect(),
        handle(),
        Ty::Func(FuncTyId::new(99)),
    ])];
    let roots = vec![
        Ty::Array(TyId::new(0), 1),
        Ty::Set(TyId::new(0), SetRepr::Bitset),
        Ty::Sequence(TyId::new(0)),
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::FatPtr(crate::FatPtrKind::Slice(TyId::new(0))),
        Ty::Vector(Box::new(array(0)), 4),
        Ty::Ref(Box::new(array(0))),
        Ty::RefMut(Box::new(array(0))),
        Ty::PtrConst(Box::new(array(0))),
        Ty::PtrMut(Box::new(array(0))),
        Ty::Rc(Box::new(array(0))),
        Ty::Tuple(vec![Ty::Bool, array(0)]),
    ];
    m.types.extend(roots.iter().cloned());
    parity(&m, &roots);
}
#[test]
fn long_actual_reference_chain_has_no_recursive_graph_walk_or_cutoff() {
    let mut m = Module::new("");
    m.types = (0..512).map(|i| array(i + 1)).collect();
    m.types.push(dialect());
    parity(&m, &[array(0), array(256), array(512), array(513)]);
}
#[test]
fn unrelated_names_and_non_type_module_payloads_do_not_enter_graph_reads() {
    let a = fixture();
    let mut b = a.clone();
    b.name = "λ\0opaque".repeat(10_000);
    for row in &mut b.structs {
        row.name = "raw structure".repeat(10_000);
    }
    for row in &mut b.enums {
        row.name = "raw enum".repeat(10_000);
    }
    for row in &mut b.records {
        row.name = "raw record".repeat(10_000);
    }
    assert_eq!(build_events(&a).0.events, build_events(&b).0.events);
    parity(&b, &[array(0), array(2)]);
}
