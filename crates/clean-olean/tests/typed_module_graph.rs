// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{env::Environment, name::Name};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_module_with_deps_cached, load_module_with_deps_parallel, ModuleCache};

/// The `module_twins` family (`tests/fixtures/lean/v4.30.0-rc2/module_twins/README.md`),
/// compiled by the pinned Lean on first use: `Root` imports the quoted twin
/// `«Module.part»` (`Module.part.olean`) and the hierarchical twin `Module.part`
/// (`Module/part.olean`), all three `prelude`, so the root is the only search path
/// the loader needs. Fails closed when the pinned toolchain is absent.
#[test]
fn actual_quoted_and_hierarchical_imports_remain_distinct_cold_and_warm() {
    let root = compiled_fixture_dir("module_twins");
    for parallel in [false, true] {
        let cache = ModuleCache::new();
        for _ in 0..2 {
            let mut env = Environment::default();
            let summaries = if parallel {
                load_module_with_deps_parallel(
                    &mut env,
                    "Root",
                    std::slice::from_ref(&root),
                    &cache,
                )
            } else {
                load_module_with_deps_cached(&mut env, "Root", std::slice::from_ref(&root), &cache)
            }
            .expect("load original typed module graph");
            assert!(
                summaries.iter().all(|s| s.skipped_constants.is_empty()),
                "{summaries:?}"
            );
            assert_eq!(
                env.constants().count(),
                4,
                "two dependencies and both root definitions must remain"
            );
            for (reader, target) in [("fromQuoted", "quotedTag"), ("fromNested", "nestedTag")] {
                let name = Name::anon().str(target);
                assert!(
                    env.get_const(&name).is_some(),
                    "missing exact dependency {target}"
                );
                let item = env
                    .get_const(&Name::anon().str(reader))
                    .expect("root definition");
                assert_eq!(
                    item.value.as_ref().expect("root body").collect_constants(),
                    [name].into_iter().collect()
                );
            }
            assert_eq!(cache.len(), 3);
        }
    }
}
