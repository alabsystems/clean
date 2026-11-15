// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_language_subset_and_every_producer_match_ordinary_coverage() {
    let languages = [
        NativeSourceLanguage::Unknown,
        NativeSourceLanguage::Rust,
        NativeSourceLanguage::Swift,
        NativeSourceLanguage::C,
        NativeSourceLanguage::TrustIr,
        NativeSourceLanguage::Other,
        NativeSourceLanguage::Lean,
        NativeSourceLanguage::Clean,
    ];
    let module = module(&all_producers());
    for bits in 0..(1usize << languages.len()) {
        let selected: Vec<_> = languages
            .iter()
            .enumerate()
            .filter(|(index, _)| bits & (1 << index) != 0)
            .map(|(_, language)| *language)
            .collect();
        let provenance = provenance(&selected);
        assert_eq!(
            functions(&provenance, &module),
            provenance.uncovered_functions(&module),
            "{bits}"
        );
        assert_eq!(
            imports(&provenance, &module),
            provenance.uncovered_imports(&module),
            "{bits}"
        );
    }
}

#[test]
fn absent_producer_requires_explicit_unknown_and_clean_accepts_either_language() {
    let module = module(&[None, Some(Producer::Clean)]);
    for language in [NativeSourceLanguage::Lean, NativeSourceLanguage::Clean] {
        let provenance = provenance(&[language]);
        assert_eq!(
            functions(&provenance, &module),
            vec![(None, vec![FuncId::new(0)])]
        );
        assert_eq!(
            imports(&provenance, &module),
            vec![(ImportId::new(0), "dependency-0".into(), None)]
        );
    }
    let provenance = provenance(&[NativeSourceLanguage::Unknown]);
    assert_eq!(
        functions(&provenance, &module),
        vec![(Some(Producer::Clean), vec![FuncId::new(1)])]
    );
}

#[test]
fn long_other_values_group_exactly_in_first_seen_order_and_keep_function_ids() {
    let mut module = long_module();
    module.functions[0].id = FuncId::new(91);
    module.functions[1].id = FuncId::new(2);
    module.functions[2].id = FuncId::new(7);
    module.functions[3].id = FuncId::new(91);
    let provenance = provenance(&[]);
    let actual = functions(&provenance, &module);
    assert_eq!(actual, provenance.uncovered_functions(&module));
    assert_eq!(actual.len(), 4);
    assert_eq!(actual[0].1, [FuncId::new(91), FuncId::new(7)]);
    assert_eq!(actual[1].0, Some(Producer::TRust));
    assert_eq!(actual[2].1, [FuncId::new(91)]);
    assert_eq!(actual[3].0, None);
}

#[test]
fn equal_length_other_names_with_late_difference_remain_distinct() {
    let mut left = "λ".repeat(2400);
    left.push('a');
    let mut right = "λ".repeat(2400);
    right.push('b');
    let module = module(&[
        Some(Producer::Other(left.clone())),
        Some(Producer::Other(right)),
        Some(Producer::Other(left)),
    ]);
    let provenance = provenance(&[]);
    let actual = functions(&provenance, &module);
    assert_eq!(actual, provenance.uncovered_functions(&module));
    assert_eq!(actual.len(), 2);
    assert_eq!(actual[0].1, [FuncId::new(0), FuncId::new(2)]);
}

#[test]
fn empty_and_embedded_nul_other_names_remain_verbatim_and_distinct_from_none() {
    let module = module(&[
        None,
        Some(Producer::Other(String::new())),
        Some(Producer::Other("tool\0λ".into())),
        Some(Producer::Other(String::new())),
    ]);
    let provenance = provenance(&[]);
    let rows = functions(&provenance, &module);
    assert_eq!(rows, provenance.uncovered_functions(&module));
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[1].1, [FuncId::new(1), FuncId::new(3)]);
    assert_eq!(
        imports(&provenance, &module),
        provenance.uncovered_imports(&module)
    );
}

#[test]
fn import_rows_keep_names_duplicates_and_original_gapped_table_ids() {
    let mut module = module(&[
        None,
        Some(Producer::TRust),
        Some(Producer::Other("x".into())),
        None,
    ]);
    module.imports[0].name = "κ🦀".repeat(900);
    module.imports[2].name = module.imports[0].name.clone();
    module.imports[3].name.clear();
    let provenance = provenance(&[NativeSourceLanguage::Rust]);
    let actual = imports(&provenance, &module);
    assert_eq!(actual, provenance.uncovered_imports(&module));
    assert_eq!(
        actual.iter().map(|row| row.0).collect::<Vec<_>>(),
        [ImportId::new(0), ImportId::new(2), ImportId::new(3)]
    );
    assert_eq!(actual[0].1, actual[1].1);
    assert_eq!(actual[2].1, "");
}

#[test]
fn empty_modules_publish_empty_diagnostics_without_consuming_interpreter_fuel() {
    let provenance = provenance(&[]);
    let module = Module::new("empty");
    assert!(functions(&provenance, &module).is_empty());
    assert!(imports(&provenance, &module).is_empty());
}

#[test]
fn covered_long_strings_are_not_copied_or_grouped() {
    let provenance = provenance(&[NativeSourceLanguage::Other]);
    let module = module(&[Some(Producer::Other("🦀".repeat(5000)))]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(
        provenance
            .uncovered_functions_observed(&module, &mut session, site())
            .unwrap()
            .is_empty()
    );
    assert!(
        provenance
            .uncovered_imports_observed(&module, &mut session, site())
            .unwrap()
            .is_empty()
    );
    assert!(observer.bytes < 1024);
}

#[test]
fn exact_producer_comparison_is_chunked_and_does_not_clone() {
    let value = Producer::Other("λ🦀".repeat(1000));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(producer_equal(Some(&value), Some(&value), &mut session, site()).unwrap());
    assert!(observer.events.len() > 5);
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.copy_bytes == 0 && event.work <= 2048)
    );
}

#[test]
fn import_id_conversion_accepts_u32_max_without_wrapping() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        checked_import_id(u32::MAX as usize, &mut session, site()).unwrap(),
        ImportId::new(u32::MAX)
    );
    if let Some(too_large) = (u32::MAX as usize).checked_add(1) {
        assert_eq!(
            checked_import_id(too_large, &mut session, site()),
            Err(ObservedValueError::CapacityOverflow)
        );
        assert!(session.first_refusal().is_none());
    }
}

#[test]
fn both_calls_accumulate_actual_work_in_one_unchanged_session() {
    let provenance = provenance(&[]);
    let module = long_module();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let first = provenance
        .uncovered_functions_observed(&module, &mut session, site())
        .unwrap();
    let second = provenance
        .uncovered_imports_observed(&module, &mut session, site())
        .unwrap();
    assert_eq!(first, provenance.uncovered_functions(&module));
    assert_eq!(second, provenance.uncovered_imports(&module));
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.bytes > 10000);
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|event| event.phase == ExecutionPhase::Publication)
            .count(),
        2
    );
}
