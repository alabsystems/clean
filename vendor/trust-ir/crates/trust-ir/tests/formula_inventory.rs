//! Borrowed formula inventory: independent order, duplicate sites, early
//! consumer refusal and scoped allocation evidence, not proof authority.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::hint::black_box;
use trust_ir::proof::{
    FormulaSiteRef as Site, ObligationKind, ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::{
    BlockId, FuncId, FuncTyId, Function, FunctionSummary, Module, ProofId, SpecInvariant,
    SpecModule, SpecTemporal, TemporalForm,
};

// This integration-test executable alone counts allocations, and only on the
// thread executing an explicit measurement scope. Other tests/threads cannot
// add noise; const TLS initialization itself needs no heap allocation.
thread_local! {
    static ALLOCATIONS: Cell<Option<usize>> = const { Cell::new(None) };
}

struct ScopedAllocator;

fn record_allocation() {
    let _ = ALLOCATIONS.try_with(|count| {
        if let Some(value) = count.get() {
            count.set(Some(value + 1));
        }
    });
}

unsafe impl GlobalAlloc for ScopedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        record_allocation();
        unsafe { System.realloc(pointer, layout, size) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: ScopedAllocator = ScopedAllocator;

fn measured<T>(operation: impl FnOnce() -> T) -> (T, usize) {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            ALLOCATIONS.with(|count| count.set(None));
        }
    }
    ALLOCATIONS.with(|count| {
        assert_eq!(count.get(), None, "allocation measurements do not nest");
        count.set(Some(0));
    });
    let reset = Reset;
    let result = operation();
    let count = ALLOCATIONS.with(|count| count.get().expect("measurement active"));
    drop(reset);
    (result, count)
}

fn function(id: u32, summary: Option<FunctionSummary>) -> Function {
    let mut function = Function::new(
        FuncId::new(id),
        format!("f{id}"),
        FuncTyId::new(0),
        BlockId::new(0),
    );
    function.summary = summary;
    function
}

fn inventory_fixture(disagreements: bool) -> Module {
    let formula = |label: &str, bad: bool| {
        let mut formula = ProofFormula::smtlib2(label, "Bool");
        if disagreements && bad {
            formula.smtlib = Some(format!("other_{label}"));
        }
        formula
    };
    let obligation = |id, label, bad| {
        ProofObligation::new(
            ProofId::new(id),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "fixture",
        )
        .with_formula(formula(label, bad))
    };
    let mut module = Module::new("formula_inventory");
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(7),
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        "no formula",
    ));
    module
        .proof_obligations
        .push(obligation(9, "obligation_bad", true));
    module
        .proof_obligations
        .push(obligation(3, "obligation_good", false));
    module.functions.push(function(30, None));
    module.functions.push(function(
        8,
        Some(
            FunctionSummary::new()
                .requiring(formula("requires_good", false))
                .requiring(formula("requires_bad", true))
                .ensuring(formula("ensures_bad", true))
                .decreasing(formula("decreases_good", false)),
        ),
    ));
    module.functions.push(function(
        2,
        Some(FunctionSummary::new().decreasing(formula("decreases_only_bad", true))),
    ));
    let mut first = SpecModule::design_only("first");
    first.invariants.push(SpecInvariant::new("untyped", "text"));
    first
        .invariants
        .push(SpecInvariant::new("typed", "text").with_typed(formula("invariant_bad", true)));
    first.temporal = vec![
        SpecTemporal::new(
            "always",
            TemporalForm::Always(formula("always_good", false)),
        ),
        SpecTemporal::new(
            "eventually",
            TemporalForm::Eventually(formula("eventually_bad", true)),
        ),
        SpecTemporal::new(
            "leads",
            TemporalForm::LeadsTo(formula("left_bad", true), formula("right_bad", true)),
        ),
        SpecTemporal::new(
            "weak",
            TemporalForm::WeakFair {
                action: "step".into(),
                relation: Some(formula("weak_good", false)),
            },
        ),
        SpecTemporal::new(
            "weak_missing",
            TemporalForm::WeakFair {
                action: "step".into(),
                relation: None,
            },
        ),
        SpecTemporal::new(
            "strong",
            TemporalForm::StrongFair {
                action: "step".into(),
                relation: Some(formula("strong_bad", true)),
            },
        ),
        SpecTemporal::new(
            "strong_missing",
            TemporalForm::StrongFair {
                action: "step".into(),
                relation: None,
            },
        ),
    ];
    let mut second = SpecModule::design_only("second");
    second
        .invariants
        .push(SpecInvariant::new("typed", "text").with_typed(formula("second_good", false)));
    second.temporal.push(SpecTemporal::new(
        "eventually",
        TemporalForm::Eventually(formula("last_bad", true)),
    ));
    module.spec_modules = vec![first, second];
    module
}

fn summary(function: u32, clause: &'static str, index: usize) -> Site<'static> {
    Site::SummaryClause {
        function: FuncId::new(function),
        clause,
        index,
    }
}

fn temporal(machine: &'static str, property: &'static str) -> Site<'static> {
    Site::SpecTemporal { machine, property }
}

fn expected_inventory() -> Vec<(Site<'static>, &'static str)> {
    // Deliberately independent of every inventory API, including legacy ones.
    vec![
        (Site::Obligation(ProofId::new(9)), "obligation_bad"),
        (Site::Obligation(ProofId::new(3)), "obligation_good"),
        (summary(8, "requires", 0), "requires_good"),
        (summary(8, "requires", 1), "requires_bad"),
        (summary(8, "ensures", 0), "ensures_bad"),
        (summary(8, "decreases", 0), "decreases_good"),
        (summary(2, "decreases", 0), "decreases_only_bad"),
        (
            Site::SpecInvariant {
                machine: "first",
                invariant: "typed",
            },
            "invariant_bad",
        ),
        (temporal("first", "always"), "always_good"),
        (temporal("first", "eventually"), "eventually_bad"),
        (temporal("first", "leads"), "left_bad"),
        (temporal("first", "leads"), "right_bad"),
        (temporal("first", "weak"), "weak_good"),
        (temporal("first", "strong"), "strong_bad"),
        (
            Site::SpecInvariant {
                machine: "second",
                invariant: "typed",
            },
            "second_good",
        ),
        (temporal("second", "eventually"), "last_bad"),
    ]
}

#[test]
fn borrowed_and_compatibility_inventory_match_independent_order() {
    let module = inventory_fixture(true);
    let expected = expected_inventory();
    let actual: Vec<_> = module
        .stated_formulas_iter()
        .map(|(site, formula)| (site, formula.payload.as_str()))
        .collect();
    assert_eq!(actual, expected);
    let owned = module.stated_formulas();
    let compatibility: Vec<_> = owned
        .iter()
        .map(|(site, formula)| (site.as_ref(), formula.payload.as_str()))
        .collect();
    assert_eq!(compatibility, expected);
    for ((site, borrowed), (owned_site, owned_formula)) in module.stated_formulas_iter().zip(&owned)
    {
        assert!(
            std::ptr::eq(borrowed, *owned_formula),
            "must borrow the actual formula"
        );
        assert_eq!(site.into_owned(), *owned_site);
        assert_eq!(site.to_string(), owned_site.to_string());
    }
}

#[test]
fn disagreement_order_preserves_duplicate_temporal_sites() {
    let module = inventory_fixture(true);
    let expected = vec![
        Site::Obligation(ProofId::new(9)),
        summary(8, "requires", 1),
        summary(8, "ensures", 0),
        summary(2, "decreases", 0),
        Site::SpecInvariant {
            machine: "first",
            invariant: "typed",
        },
        temporal("first", "eventually"),
        temporal("first", "leads"),
        temporal("first", "leads"),
        temporal("first", "strong"),
        temporal("second", "eventually"),
    ];
    assert_eq!(
        module.formulas_stating_two_texts_iter().collect::<Vec<_>>(),
        expected
    );
    assert_eq!(
        module.formulas_stating_two_texts(),
        expected
            .iter()
            .copied()
            .map(Site::into_owned)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        module.first_formula_stating_two_texts(),
        expected.first().copied()
    );
    assert_eq!(
        inventory_fixture(false).first_formula_stating_two_texts(),
        None
    );
    assert_eq!(Module::new("empty").stated_formulas_iter().next(), None);
}

#[test]
fn equal_payloads_and_equal_sites_remain_distinct_leaves() {
    let mut formula = ProofFormula::smtlib2("false", "Bool");
    formula.smtlib = Some("true".into());
    let mut spec = SpecModule::design_only("same");
    spec.temporal.push(SpecTemporal::new(
        "same",
        TemporalForm::LeadsTo(formula.clone(), formula),
    ));
    let mut module = Module::new("duplicates");
    module.spec_modules.push(spec);
    let site = temporal("same", "same");
    assert_eq!(
        module.formulas_stating_two_texts_iter().collect::<Vec<_>>(),
        vec![site, site]
    );
    let formulas: Vec<_> = module
        .stated_formulas_iter()
        .map(|(_, formula)| formula)
        .collect();
    assert_eq!(formulas[0], formulas[1]);
    assert!(!std::ptr::eq(formulas[0], formulas[1]));
}

#[test]
fn borrowed_site_keeps_the_original_diagnostic_spelling() {
    for (site, expected) in [
        (Site::Obligation(ProofId::new(9)), "obligation #9"),
        (
            summary(8, "requires", 1),
            "function f8 summary requires clause 1",
        ),
        (
            Site::SpecInvariant {
                machine: "m",
                invariant: "i",
            },
            "spec machine \"m\" invariant \"i\" typed carrier",
        ),
        (
            temporal("m", "p"),
            "spec machine \"m\" temporal property \"p\"",
        ),
    ] {
        assert_eq!(site.to_string(), expected);
        assert_eq!(site.into_owned().to_string(), expected);
    }
}

#[test]
fn opaque_and_unrendered_formulas_remain_carried_without_disagreement() {
    let mut opaque = ProofFormula::new("other-schema", "opaque-payload");
    opaque.smtlib = Some("unrelated rendering".into());
    let mut unrendered = ProofFormula::smtlib2("true", "Bool");
    unrendered.smtlib = None;
    let function = function(
        19,
        Some(
            FunctionSummary::new()
                .requiring(opaque)
                .ensuring(unrendered),
        ),
    );
    assert_eq!(function.stated_formulas_iter().count(), 2);
    assert_eq!(function.first_formula_stating_two_texts(), None);
    let mut module = Module::new("carried");
    module.functions.push(function);
    assert_eq!(module.stated_formulas_iter().count(), 2);
    assert_eq!(module.first_formula_stating_two_texts(), None);
}

#[test]
fn actual_function_query_covers_detached_and_decreases_only_summaries() {
    let module = inventory_fixture(false);
    assert_eq!(module.functions[0].stated_formulas_iter().next(), None);
    let mut detached = module.functions[1].clone();
    detached.summary.as_mut().unwrap().requires[0].smtlib = Some("other".into());
    assert_eq!(module.first_formula_stating_two_texts(), None);
    assert_eq!(
        detached.first_formula_stating_two_texts(),
        Some(summary(8, "requires", 0))
    );
    let bad = inventory_fixture(true);
    let decreases_only = &bad.functions[2];
    assert_eq!(
        decreases_only.first_formula_stating_two_texts(),
        Some(summary(2, "decreases", 0))
    );
}

#[test]
fn temporal_iterators_preserve_action_flags_and_missing_relations() {
    let module = inventory_fixture(true);
    let expected = [
        vec![("always_good", false)],
        vec![("eventually_bad", false)],
        vec![("left_bad", false), ("right_bad", false)],
        vec![("weak_good", true)],
        vec![],
        vec![("strong_bad", true)],
        vec![],
    ];
    for (property, expected) in module.spec_modules[0].temporal.iter().zip(expected) {
        let observed: Vec<_> = property
            .form
            .formulas_iter()
            .map(|(formula, action)| (formula.payload.as_str(), action))
            .collect();
        assert_eq!(observed, expected, "{}", property.name);
        let legacy: Vec<_> = property
            .form
            .formulas()
            .into_iter()
            .map(|(formula, action)| (formula.payload.as_str(), action))
            .collect();
        assert_eq!(legacy, expected, "{}", property.name);
    }
}

#[test]
fn borrowed_inventory_and_first_queries_allocate_nothing_in_scoped_measurement() {
    let module = inventory_fixture(false);
    let bad = inventory_fixture(true);
    let expected_count = expected_inventory().len();
    let (count, allocations) = measured(|| {
        let mut count = 0;
        for pair in module.stated_formulas_iter() {
            black_box(pair);
            count += 1;
        }
        black_box(module.first_formula_stating_two_texts());
        black_box(bad.first_formula_stating_two_texts());
        for function in &module.functions {
            black_box(function.stated_formulas_iter().count());
            black_box(function.first_formula_stating_two_texts());
        }
        for spec in &module.spec_modules {
            for property in &spec.temporal {
                black_box(property.form.formulas_iter().count());
            }
        }
        count
    });
    assert_eq!(count, expected_count);
    assert_eq!(allocations, 0);
    // Positive control: the same scoped counter must observe a real collector.
    let (owned, allocations) = measured(|| black_box(module.stated_formulas()));
    assert_eq!(owned.len(), expected_count);
    assert!(
        allocations > 0,
        "allocation counter must not silently do nothing"
    );
}
