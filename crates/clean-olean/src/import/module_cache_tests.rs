// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{ModuleCache, MAX_MODULE_CACHE_ENTRIES};
use crate::module::ParsedModule;
use std::fs;
use tempfile::NamedTempFile;

fn dummy_module() -> ParsedModule {
    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

#[test]
fn module_cache_bounds_size_when_entry_limit_is_exceeded() {
    let cache = ModuleCache::new();
    let file = NamedTempFile::new().expect("temp file");
    fs::write(file.path(), b"shared").expect("write temp module source");

    let module_names: Vec<String> = (0..=MAX_MODULE_CACHE_ENTRIES)
        .map(|i| format!("Init.Overflow.{i}"))
        .collect();

    for module in &module_names {
        cache.insert(module, file.path(), dummy_module());
    }

    let expected_len = MAX_MODULE_CACHE_ENTRIES - (MAX_MODULE_CACHE_ENTRIES / 4) + 1;
    assert_eq!(
        cache.len(),
        expected_len,
        "overflow should evict one quarter of cached modules before inserting the new entry"
    );

    let newest = module_names.last().expect("non-empty module list");
    assert!(
        cache.get(newest, file.path()).is_some(),
        "newest entry should remain cached after overflow eviction"
    );

    let evicted_entries = module_names
        .iter()
        .filter(|module| cache.get(module, file.path()).is_none())
        .count();
    assert!(
        evicted_entries >= MAX_MODULE_CACHE_ENTRIES / 4,
        "overflow insertions should evict at least one quarter of the prior entries"
    );
}
