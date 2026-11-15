// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-olean `Lean.structureExt` decode + restore (2026-09-10).
//!
//! Before this decoder an imported structure had NO field-name table (the
//! projection-derived recovery in `register_structure_fields_from_projections`
//! was the only source, and it needs every direct projection to be a loaded
//! `λ*. Proj` constant) and NO `extends` parents at all — the module-level
//! comment in `load_register.rs` said "raw `.olean`s carry no Clean-decodable
//! `structureExt`". So `{ … le := … } : LinearOrder α` on an olean-imported
//! `LinearOrder` was `Unknown structure field le` (an inherited field has no
//! `LinearOrder.le` projection to decompile) and
//! `rewrite_parent_subobject_construction` returned `None` for every import.
//! Measured on `Mathlib/Order/Basic.lean`: `Pi.preorder`, `Prod.instPreorder`,
//! `LinearOrder.ofSubsingleton`, `Function.Injective.preorder` and their
//! downstream stopped there.
//!
//! Ground truth: `Lean/Structure.lean` (`StructureInfo`, `StructureFieldInfo`,
//! `StructureParentInfo`, `structureExt`), pinned against the v4.30.0-rc2
//! toolchain oleans; the tests skip with a message when that toolchain is
//! absent. The decode is layout-validated, so a different toolchain degrades
//! to counted `undecoded_entries`, never wrong data.

use super::{load_module_with_deps, parse_module};
use crate::module::{is_structure_extension_name, ParsedExtensionEntry, ParsedStructureEntry};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

fn v4_30_lib_path() -> Option<std::path::PathBuf> {
    crate::pinned_lean_lib_path()
}

/// Decode the `Lean.structureExt` entries of one `.olean` (relative path under
/// `lib/lean`), or `None` to skip.
fn decode_structure_entries(rel: &str) -> Option<(Vec<ParsedStructureEntry>, usize)> {
    let lib = v4_30_lib_path()?;
    let bytes = std::fs::read(lib.join(rel)).ok()?;
    let module = parse_module(&bytes).unwrap_or_else(|e| panic!("{rel} should parse: {e}"));
    let ext = module
        .entries
        .iter()
        .find(|ext| is_structure_extension_name(&ext.extension_name))
        .unwrap_or_else(|| {
            let present: Vec<&str> = module
                .entries
                .iter()
                .map(|e| e.extension_name.as_str())
                .filter(|n| n.contains("tructure"))
                .collect();
            panic!(
                "{rel} should carry a Lean.structureExt entry array; \
                 structure-named extensions present: {present:?}"
            )
        });
    let decoded = ext
        .entries
        .iter()
        .map(|entry| match entry {
            ParsedExtensionEntry::Structure(s) => s.clone(),
            other => panic!("structureExt should decode every entry as Structure, got {other:?}"),
        })
        .collect();
    Some((decoded, ext.undecoded_entries))
}

fn find_struct<'a>(decoded: &'a [ParsedStructureEntry], name: &str) -> &'a ParsedStructureEntry {
    decoded
        .iter()
        .find(|s| s.struct_name == name)
        .unwrap_or_else(|| panic!("{name} should be a persisted structureExt entry"))
}

#[test]
fn test_structure_ext_decoder_prelude_entries_fully_decoded() {
    // SELF-SKIP OK: the pinned leanprover--lean4---v4.30.0-rc2 toolchain (elan, outside the tree) supplies the Init/Prelude.olean under test; absent it there is nothing to decode, and every decode defect panics inside decode_structure_entries.
    let Some((decoded, undecoded)) = decode_structure_entries("Init/Prelude.olean") else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    assert!(
        decoded.len() >= 50,
        "expected >= 50 decoded structure entries in Init.Prelude, got {}",
        decoded.len()
    );
    assert_eq!(
        undecoded, 0,
        "the pinned v4.30 StructureInfo layout should decode every entry"
    );

    // A plain structure: direct fields in constructor order, no parents.
    let prod = find_struct(&decoded, "Prod");
    assert_eq!(prod.field_names, vec!["fst".to_string(), "snd".to_string()]);
    assert!(
        prod.parents.is_empty(),
        "Prod extends nothing: {:?}",
        prod.parents
    );
    assert!(
        prod.fields.iter().all(|f| f.subobject.is_none()),
        "no Prod field is a subobject"
    );
    let fst = prod
        .fields
        .iter()
        .find(|f| f.field_name == "fst")
        .expect("fst is a field");
    assert_eq!(fst.proj_fn, "Prod.fst");
    assert_eq!(fst.binder_info, 0, "fst is an explicit (default) binder");

    // A class with `extends`: `class Monad (m) extends Applicative m, Bind m`.
    // Both parents are SUBOBJECTS (`toApplicative`, `toBind`), in `extends`
    // order, and the field table sees each as ONE field.
    let monad = find_struct(&decoded, "Monad");
    let parents: Vec<(&str, bool, &str)> = monad
        .parents
        .iter()
        .map(|p| (p.struct_name.as_str(), p.subobject, p.proj_fn.as_str()))
        .collect();
    assert_eq!(
        parents,
        vec![
            ("Applicative", true, "Monad.toApplicative"),
            ("Bind", true, "Monad.toBind"),
        ]
    );
    assert_eq!(
        monad.field_names,
        vec!["toApplicative".to_string(), "toBind".to_string()]
    );
    let to_app = monad
        .fields
        .iter()
        .find(|f| f.field_name == "toApplicative")
        .expect("toApplicative is a field");
    assert_eq!(to_app.subobject.as_deref(), Some("Applicative"));
    assert_eq!(
        to_app.binder_info, 3,
        "a class parent slot is an instance-implicit binder"
    );

    // Five parents on Applicative, all subobjects, `extends` order preserved.
    let applicative = find_struct(&decoded, "Applicative");
    let names: Vec<&str> = applicative
        .parents
        .iter()
        .map(|p| p.struct_name.as_str())
        .collect();
    assert_eq!(names, vec!["Functor", "Pure", "Seq", "SeqLeft", "SeqRight"]);
    assert!(applicative.parents.iter().all(|p| p.subobject));
}

#[test]
fn test_imported_structure_gets_field_table_and_parents() {
    // SELF-SKIP OK: needs the pinned leanprover--lean4---v4.30.0-rc2 toolchain's lib/lean (elan, outside the tree) to import Init.Prelude; absent it the import cannot run, and every measured result is expect/assert once it is present.
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut env = Environment::new();
    let summaries = load_module_with_deps(&mut env, "Init.Prelude", &[lib])
        .expect("Init.Prelude should import");
    // Every `Lean.structureExt` row decodes. (Extensions the typed decoder
    // does not model are retained `Unmeasured` and counted per extension, so
    // the module-wide undecoded total is no longer zero by design.)
    let structure_rows: Vec<_> = summaries
        .iter()
        .flat_map(|summary| &summary.extension_accounting)
        .filter(|row| is_structure_extension_name(&row.extension_name.to_string()))
        .collect();
    assert!(
        !structure_rows.is_empty(),
        "Init.Prelude must carry a structureExt extension"
    );
    for row in structure_rows {
        assert!(row.decoded_rows > 0, "structureExt rows must decode");
        assert_eq!(row.undecoded_rows, 0, "{:?}", row.undecoded_reasons);
    }

    // The field table comes straight from Lean's `fieldNames`, in constructor
    // order, so `s.2` and `get_structure_field_index` agree with Lean.
    let monad = Name::interned("Monad");
    let fields = env
        .get_structure_field_names(&monad)
        .expect("Monad must carry a field table after importing Init.Prelude");
    assert_eq!(
        fields.iter().map(ToString::to_string).collect::<Vec<_>>(),
        vec!["toApplicative".to_string(), "toBind".to_string()]
    );
    assert_eq!(
        env.get_structure_field_index(&monad, &Name::from_string("toBind")),
        Some(1)
    );

    // The parents are what an IMPORTED structure never had: the `toParent`
    // slot name paired with the parent, in `extends` order — exactly what
    // `rewrite_parent_subobject_construction` reads to route an inherited
    // field (`pure := …` on a `Monad`) into `toApplicative`.
    let parents = env
        .get_structure_parents(&monad)
        .expect("Monad must carry extends parents after importing Init.Prelude");
    let parents: Vec<(String, String)> = parents
        .iter()
        .map(|(to, p)| (to.to_string(), p.to_string()))
        .collect();
    assert_eq!(
        parents,
        vec![
            ("toApplicative".to_string(), "Applicative".to_string()),
            ("toBind".to_string(), "Bind".to_string()),
        ]
    );

    // A parent-less structure records NO parents (the kernel keeps the map
    // sparse), and its table is the plain field list.
    let prod = Name::interned("Prod");
    assert!(env.get_structure_parents(&prod).is_none());
    assert_eq!(
        env.get_structure_field_names(&prod)
            .expect("Prod field table")
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        vec!["fst".to_string(), "snd".to_string()]
    );
}
