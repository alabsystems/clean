// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn unique_sparse_missing_and_permanently_ambiguous_rows_match_actual_borrowed_declarations() {
    let m = fixture();
    let plain = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    for id in [0, 1, 3, 8, 19, 20, u32::MAX] {
        let expected = plain.unique(FuncId::new(id));
        let actual = a.unique_observed(FuncId::new(id), &mut s, site()).unwrap();
        match (expected, actual) {
            (None, None) => {}
            (Some(e), Some(a)) => assert!(core::ptr::eq(e, a)),
            _ => panic!("same exact unique result"),
        }
    }
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn same_ids_in_other_module_never_substitute_for_this_catalog_source() {
    let m = fixture();
    let mut other = m.clone();
    for f in &mut other.functions {
        f.name = "foreign".into();
    }
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    assert!(core::ptr::eq(a.source_module(), &m));
    let f = a
        .unique_observed(FuncId::new(8), &mut s, site())
        .unwrap()
        .unwrap();
    assert_eq!(f.name, "only");
    assert!(!core::ptr::eq(f, &other.functions[2]));
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn ambiguity_roster_preserves_numeric_order_instead_of_physical_arrival() {
    let m = fixture();
    run(&m);
    let plain = ModuleFunctionCatalog::new(&m);
    assert_eq!(plain.ambiguous_ids().collect::<Vec<_>>(), vec![3, 19]);
}
#[test]
fn empty_catalog_lookup_and_roster_match_original_empty_results() {
    let m = Module::new("");
    run(&m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    assert!(
        a.unique_observed(FuncId::new(u32::MAX), &mut s, site())
            .unwrap()
            .is_none()
    );
    a.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn lookup_and_census_do_not_traverse_unrelated_function_payloads() {
    let m = fixture();
    let mut huge = m.clone();
    for f in &mut huge.functions {
        f.name = "λ raw\0".repeat(10000);
    }
    let (a, ab, ae) = run(&m);
    let (b, bb, be) = run(&huge);
    assert_eq!(a.events[ab..ae], b.events[bb..be]);
}
#[test]
fn complete_roster_stays_owned_across_later_borrowed_queries_until_explicit_retirement() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let a = setup(&m, &mut s);
    let out = a.ambiguous_ids_observed(&mut s, site()).unwrap();
    assert_eq!(out, vec![3, 19]);
    assert!(
        a.unique_observed(FuncId::new(8), &mut s, site())
            .unwrap()
            .is_some()
    );
    assert_eq!(out, vec![3, 19]);
    Work {
        session: &mut s,
        site: site(),
    }
    .rows(out);
    a.retire_observed(&mut s, site()).unwrap();
}
