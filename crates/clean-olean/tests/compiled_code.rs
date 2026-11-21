// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The negative controls of the compiled-checker refusal
//! (`support/compiled_code.rs`; plan unit E2's follow-up part 2,
//! `docs/DECISIONS.md`, "Compiled-checker packages refuse what changes executed
//! code without moving a pin"). `kcheck_core.rs` and `kcheck_labelled.rs` run
//! the refusal over the packages Trust is to compile and run and require it to
//! find nothing; this test shows that it finds each construct it refuses.
//!
//! The fixture family `compiled_code` holds one module per refused construct
//! (`@[implemented_by]`, `@[extern]`, `@[csimp]`, `@[export]`, `initialize`,
//! `builtin_initialize`, `opaque`, `partial def`, `unsafe def`, a hand-written
//! `<d>._unsafe_rec`, `@[cpass]`, a constant folder, and `import Lean` with a
//! metaprogram that forges a partial `<d>._unsafe_rec`) and one with none but
//! a well-founded recursive definition, whose compiler copy is the one
//! exception, compiled by the pinned Lean. None imports another. The modules
//! that import only `Init` are read by one load (and `Init` once); the three
//! that import `Lean` are not loaded, since a load of their closure reads all
//! of `Lean` (65 s and 6.2 GB for the release `clean` binary on 2026-11-19), so
//! their refusals come from the parser's reading of their compiled data and
//! include the missing load summary. Each module's refusals must be exactly
//! the ones the fixture's README lists: a refusal that stops firing, or one
//! that fires on the clean module, fails the test. In particular the forged
//! copy passes every rule but the import rule (it is counted as a compiler
//! copy), so removing that rule fails `CompiledCodeImportLean`'s control, and
//! removing the `@[cpass]` or the folder table fails its module's.

#[path = "support/compiled_code.rs"]
mod compiled_code;

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_modules_with_deps, require_pinned_lean_lib_path};
use compiled_code::{CompiledCodeRefusal, REFUSED_TABLES};

/// A refusal without its row count: `(kind, table or declaration)`.
fn shape(refusal: &CompiledCodeRefusal) -> (&'static str, String) {
    match refusal {
        CompiledCodeRefusal::Attribute { table, rows, .. } => {
            assert!(*rows >= 1, "{refusal}: a refused table with no row");
            ("attribute", table.clone())
        }
        CompiledCodeRefusal::Import { import, .. } => ("import", import.clone()),
        CompiledCodeRefusal::MultiPart { module, .. } => ("multi-part", module.clone()),
        CompiledCodeRefusal::NotLoaded { module } => ("not-loaded", module.clone()),
        CompiledCodeRefusal::NotRead { module, .. } => ("not-read", module.clone()),
        CompiledCodeRefusal::Opaque { name, .. } => ("opaque", name.clone()),
        CompiledCodeRefusal::Unsafe { name, .. } => ("unsafe", name.clone()),
        CompiledCodeRefusal::Partial { name, .. } => ("partial", name.clone()),
        CompiledCodeRefusal::CompiledReplacement { name, .. } => ("replacement", name.clone()),
    }
}

/// `(module, its refusals)`, as the fixture's README lists them.
const EXPECTED: &[(&str, &[(&str, &str)])] = &[
    ("CompiledCodeClean", &[]),
    (
        "CompiledCodeImplementedBy",
        &[("attribute", "Lean.Compiler.implementedByAttr")],
    ),
    ("CompiledCodeExtern", &[("attribute", "Lean.externAttr")]),
    (
        "CompiledCodeCSimp",
        &[("attribute", "Lean.Compiler.CSimp.ext")],
    ),
    ("CompiledCodeExport", &[("attribute", "Lean.exportAttr")]),
    (
        "CompiledCodeInit",
        &[
            ("attribute", "Lean.regularInitAttr"),
            ("opaque", "CC.Init.probe"),
        ],
    ),
    (
        "CompiledCodeBuiltinInit",
        &[
            ("attribute", "Lean.builtinInitAttr"),
            ("opaque", "CC.BuiltinInit.probe"),
        ],
    ),
    ("CompiledCodeOpaque", &[("opaque", "CC.Opaque.hidden")]),
    (
        "CompiledCodePartial",
        &[
            ("opaque", "CC.Partial.loop"),
            ("partial", "CC.Partial.loop._unsafe_rec"),
            ("replacement", "CC.Partial.loop._unsafe_rec"),
        ],
    ),
    ("CompiledCodeUnsafe", &[("unsafe", "CC.Unsafe.raw")]),
    (
        "CompiledCodeUnsafeRec",
        &[("replacement", "CC.UnsafeRec.spec._unsafe_rec")],
    ),
    (
        "CompiledCodeCPass",
        &[
            ("attribute", "Lean.Compiler.LCNF.passManagerExt"),
            ("import", "Lean"),
            ("not-loaded", "CompiledCodeCPass"),
        ],
    ),
    (
        "CompiledCodeFolder",
        &[
            (
                "attribute",
                "Lean.Compiler.LCNF.Simp.ConstantFold.folderExt",
            ),
            ("import", "Lean"),
            ("not-loaded", "CompiledCodeFolder"),
        ],
    ),
    (
        "CompiledCodeImportLean",
        &[("import", "Lean"), ("not-loaded", "CompiledCodeImportLean")],
    ),
];

/// Whether the test loads `module`: every control but the ones whose stated
/// refusals include the missing load summary, which import `Lean`.
fn loaded(refusals: &[(&str, &str)]) -> bool {
    !refusals.iter().any(|(kind, _)| *kind == "not-loaded")
}

/// The compiler copies each module may hold: the clean module's well-founded
/// definition has one; the forged copy of `CompiledCodeImportLean` has the
/// same shape and is counted as one, so only the import rule refuses it;
/// nothing else has one.
fn expected_copies(module: &str) -> BTreeSet<String> {
    match module {
        "CompiledCodeClean" => BTreeSet::from(["CC.Clean.halve._unsafe_rec".to_owned()]),
        "CompiledCodeImportLean" => BTreeSet::from(["CC.ImportLean.spec._unsafe_rec".to_owned()]),
        _ => BTreeSet::new(),
    }
}

#[test]
fn compiled_code_refusal_names_each_construct_and_spares_the_clean_module() {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir("compiled_code");

    // Every refused table has a module that carries it.
    let tables_carried: BTreeSet<&str> = EXPECTED
        .iter()
        .flat_map(|(_, refusals)| refusals.iter())
        .filter(|(kind, _)| *kind == "attribute")
        .map(|(_, table)| *table)
        .collect();
    let tables_refused: BTreeSet<&str> = REFUSED_TABLES.iter().map(|(table, _)| *table).collect();
    // Every mismatch is collected and reported together, so a rule removed
    // names each control it fails.
    let mut failures: Vec<String> = Vec::new();
    if tables_carried != tables_refused {
        failures.push(format!(
            "the refused tables ({tables_refused:?}) are not the ones the controls carry \
             ({tables_carried:?})"
        ));
    }

    let modules: Vec<String> = EXPECTED
        .iter()
        .map(|(module, _)| (*module).to_owned())
        .collect();
    let order_path = clean_olean::test_support::fixture_root()
        .join("compiled_code")
        .join("ORDER");
    let order = std::fs::read_to_string(&order_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", order_path.display()));
    assert_eq!(
        order
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect::<Vec<_>>(),
        modules.iter().map(String::as_str).collect::<Vec<_>>(),
        "every module the fixture compiles has its stated refusals, in ORDER's order"
    );
    let search = [compiled.clone(), lib];
    let loaded_modules: Vec<String> = EXPECTED
        .iter()
        .filter(|(_, refusals)| loaded(refusals))
        .map(|(module, _)| (*module).to_owned())
        .collect();
    assert_eq!(
        modules.len() - loaded_modules.len(),
        3,
        "the three controls that import Lean are the ones not loaded"
    );
    let mut env = Environment::for_lean_replay();
    let summaries = load_modules_with_deps(&mut env, &loaded_modules, &search)
        .unwrap_or_else(|error| panic!("load the control modules: {error}"));
    drop(env);
    for (module, expected) in EXPECTED {
        let census = compiled_code::refusals(&compiled, &[(*module).to_owned()], &summaries);
        let found: BTreeSet<(&'static str, String)> = census.refusals.iter().map(shape).collect();
        let wanted: BTreeSet<(&'static str, String)> = expected
            .iter()
            .map(|(kind, subject)| (*kind, (*subject).to_owned()))
            .collect();
        if found != wanted {
            failures.push(format!(
                "{module}: the refusals found ({}) are not the ones its control states \
                 (missing {:?}, unexpected {:?})",
                census
                    .refusals
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; "),
                wanted.difference(&found).collect::<Vec<_>>(),
                found.difference(&wanted).collect::<Vec<_>>()
            ));
            continue;
        }
        assert!(
            census.tables > 0,
            "{module}: the parser read no extension table"
        );
        assert!(census.imports > 0, "{module}: the parser read no import");
        assert_eq!(
            census.compiler_copies,
            expected_copies(module),
            "{module}: the compiler copies allowed"
        );
        if expected.is_empty() {
            eprintln!("{}", compiled_code::require_none(&census, module));
        } else {
            for refusal in &census.refusals {
                eprintln!("refused {refusal}");
            }
        }
    }
    assert!(
        failures.is_empty(),
        "the controls fail:\n{}",
        failures.join("\n")
    );

    // The loader's reading is consulted as well as the parser's: a module the
    // load did not read is refused, and so is one whose tables it skipped.
    let clean = "CompiledCodeClean".to_owned();
    let unread = compiled_code::refusals(&compiled, std::slice::from_ref(&clean), &[]);
    assert_eq!(
        unread.refusals,
        vec![CompiledCodeRefusal::NotLoaded {
            module: clean.clone()
        }],
        "a package module with no load summary is refused"
    );
    // A package module outside the test root's import closure is loaded into
    // a scratch environment for its summary, and then passes as it should.
    let completed = compiled_code::complete_summaries(&[], std::slice::from_ref(&clean), &search);
    let completed_census =
        compiled_code::refusals(&compiled, std::slice::from_ref(&clean), &completed);
    assert!(
        completed_census.refusals.is_empty() && completed_census.tables > 0,
        "a module outside the root's closure is read by the loader too: {:?}",
        completed_census.refusals
    );
    let mut summaries = summaries;
    let summary = summaries
        .iter_mut()
        .find(|summary| summary.module_name.as_deref() == Some(clean.as_str()))
        .expect("the clean module's summary");
    let tables = summary.extension_accounting.len();
    assert!(tables > 0, "the load read the clean module's tables");
    summary.extension_accounting.clear();
    let skipped = compiled_code::refusals(&compiled, std::slice::from_ref(&clean), &summaries);
    assert!(
        matches!(
            skipped.refusals.as_slice(),
            [CompiledCodeRefusal::NotRead { module, .. }] if *module == clean
        ),
        "a load that read none of a module's tables is refused: {:?}",
        skipped.refusals
    );
    eprintln!(
        "compiled-code controls: {} modules, each refused as its control states; the clean \
         module's {tables} tables read by the load",
        EXPECTED.len()
    );
}
