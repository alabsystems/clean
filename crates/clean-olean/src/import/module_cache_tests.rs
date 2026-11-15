// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::module_cache_direct::CapturedModule;
use super::{ModuleCache, MAX_MODULE_CACHE_ENTRIES};
use clean_kernel::env::Environment;
use std::path::PathBuf;

#[test]
fn module_cache_bounds_size_when_entry_limit_is_exceeded() {
    let cache = ModuleCache::new();
    let file = tempfile::NamedTempFile::new().expect("temp file");
    let bytes = crate::OleanExporter::export_with_env(
        &Environment::default(),
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .expect("export");
    std::fs::write(file.path(), bytes).expect("write captured module");
    for i in 0..=MAX_MODULE_CACHE_ENTRIES {
        let captured = CapturedModule::read(file.path()).expect("capture");
        cache.insert_direct(
            PathBuf::from(format!("private-cache-fixture/{i}.olean")),
            captured.parse().expect("parse"),
        );
    }
    assert_eq!(
        cache.len(),
        MAX_MODULE_CACHE_ENTRIES - MAX_MODULE_CACHE_ENTRIES / 4 + 1
    );
    let entries = cache.entries.read().expect("cache lock");
    assert!(entries.contains_key(&PathBuf::from(format!(
        "private-cache-fixture/{MAX_MODULE_CACHE_ENTRIES}.olean"
    ))));
}
