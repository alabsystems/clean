// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The writer against the reader: Lean-minted fixtures re-written and read
//! back, the cone of a loaded export written from the kernel's records, the
//! record kinds the fixtures lack, and the writer's refusals.
//!
//! The fixtures under `tests/fixtures/lean/v4.30.0-rc2/ndjson_minted/` were
//! minted inside pinned Lean (`MintExports.lean`). The writer's bytes differ
//! from theirs in exactly these ways, each asserted or stated here:
//!
//! - binder names: the fixtures name every `lam`/`forallE` binder; the kernel
//!   keeps none, so the writer writes the anonymous name (index 0). Fewer
//!   name, level and expression records follow (terms that differed only in
//!   a binder name share one record), never more.
//! - the `all` of a `def` or `thm`: written as the declaration alone.
//! - indices: both number in order of first use, but over different record
//!   sets, so the numbers differ.
//!
//! Everything else is equal after the reader, which the tests assert.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;

use clean_kernel::expr::{BinderData, BinderInfo, Expr, ExprKind, Multiplicity};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

use super::tables::Spelling;
use super::{check_export_round_trip, write_cone, write_declarations, write_export};
use super::{ExportWriteError, ExportWriteMeta, ExportWriteSummary};
use crate::module::{DefinitionSafety, ParsedQuotKind, ReducibilityHintsData};
use crate::ndjson::decl::{ExportDeclaration, ExportHeader};
use crate::ndjson::json::{parse_line, JsonValue};
use crate::ndjson::load::load_export;
use crate::ndjson::source::{ExportSource, NdjsonSource};

const PLAIN_FIXTURES: [&str; 3] = [
    "nat_add_literal.ndjson",
    "nested_reflexive.ndjson",
    "sigma_const_nested.ndjson",
];

fn fixture(name: &str) -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean/v4.30.0-rc2/ndjson_minted")
        .join(name);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    if name.ends_with(".gz") {
        let mut out = Vec::new();
        flate2::read::GzDecoder::new(bytes.as_slice())
            .read_to_end(&mut out)
            .expect("a gzip stream");
        out
    } else {
        bytes
    }
}

fn all_fixtures() -> Vec<(&'static str, Vec<u8>)> {
    PLAIN_FIXTURES
        .into_iter()
        .chain(["init_dotted_names.ndjson.gz"])
        .map(|name| (name, fixture(name)))
        .collect()
}

fn meta() -> ExportWriteMeta {
    ExportWriteMeta {
        lean_version: "4.30.0-rc2".to_owned(),
        lean_githash: "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc".to_owned(),
    }
}

fn read(bytes: &[u8]) -> Vec<ExportDeclaration> {
    let mut source = NdjsonSource::new(bytes).expect("a readable header");
    let mut out = Vec::new();
    while let Some((_, declaration)) = source.next_declaration().expect("a readable export") {
        out.push(declaration);
    }
    assert!(source.level_taint().0.is_none(), "a level was rebuilt");
    out
}

/// The reader's record of the names of `bytes` it stores otherwise than
/// written (R118).
fn spelling(bytes: &[u8]) -> Spelling {
    let mut source = NdjsonSource::new(bytes).expect("a readable header");
    while source
        .next_declaration()
        .expect("a readable export")
        .is_some()
    {}
    source.written_names()
}

fn write(declarations: &[ExportDeclaration], spelling: Spelling) -> (Vec<u8>, ExportWriteSummary) {
    let mut out = Vec::new();
    let summary = write_declarations(
        &meta(),
        declarations.iter().cloned().map(Ok),
        spelling,
        &mut out,
    )
    .expect("writable declarations");
    (out, summary)
}

/// How many records of each table (`in`, `il`, `ie`) an export has.
fn table_sizes(bytes: &[u8]) -> BTreeMap<String, usize> {
    let mut sizes = BTreeMap::new();
    for line in bytes.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
        let JsonValue::Object(entries) = parse_line(line).expect("a JSON line") else {
            panic!("a line that is not an object");
        };
        for (key, _) in entries {
            if matches!(key.as_str(), "in" | "il" | "ie") {
                *sizes.entry(key).or_default() += 1;
            }
        }
    }
    sizes
}

#[test]
fn test_writer_lean_minted_fixtures_rewritten_read_back_equal() {
    for (name, minted) in all_fixtures() {
        let from_lean = read(&minted);
        assert!(!from_lean.is_empty(), "{name}");
        let (written, summary) = write(&from_lean, spelling(&minted));
        let from_clean = read(&written);
        assert_eq!(
            from_lean, from_clean,
            "{name}: declarations differ after the reader"
        );
        check_export_round_trip(written.as_slice(), &summary)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(summary.records, from_lean.len(), "{name}");

        // The explained differences: no table grows, and the name and
        // expression tables shrink exactly when the fixture names a binder.
        let (lean_sizes, clean_sizes) = (table_sizes(&minted), table_sizes(&written));
        for table in ["in", "il", "ie"] {
            let (lean, clean) = (
                lean_sizes.get(table).copied().unwrap_or(0),
                clean_sizes.get(table).copied().unwrap_or(0),
            );
            assert!(
                clean <= lean,
                "{name}: table {table} grew from {lean} to {clean}"
            );
        }
        assert_eq!(clean_sizes.get("in").copied().unwrap_or(0), summary.names);
        assert_eq!(clean_sizes.get("il").copied().unwrap_or(0), summary.levels);
        assert_eq!(clean_sizes.get("ie").copied().unwrap_or(0), summary.exprs);
    }
}

#[test]
fn test_writer_output_is_deterministic_with_dense_indices_in_order() {
    for (name, minted) in all_fixtures() {
        let declarations = read(&minted);
        let (first, _) = write(&declarations, spelling(&minted));
        let (second, _) = write(&declarations, spelling(&minted));
        assert_eq!(first, second, "{name}: two writings differ");
        let mut next: BTreeMap<&str, u64> = BTreeMap::from([("in", 1), ("il", 1), ("ie", 0)]);
        for line in first.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
            let JsonValue::Object(entries) = parse_line(line).expect("a JSON line") else {
                panic!("a line that is not an object");
            };
            for (key, value) in &entries {
                let Some(expected) = next.get_mut(key.as_str()) else {
                    continue;
                };
                let JsonValue::Number(n) = value else {
                    panic!("{name}: a table index that is not a number");
                };
                assert_eq!(n.as_u64(), Some(*expected), "{name}: table {key}");
                *expected += 1;
            }
        }
    }
}

/// `declaration` with the fields the kernel does not keep as Lean stored them
/// set to one value: a definition's unfolding hint.
fn without_hints(declaration: &ExportDeclaration) -> ExportDeclaration {
    let mut out = declaration.clone();
    if let ExportDeclaration::Definition { hints, .. } = &mut out {
        *hints = ReducibilityHintsData::Opaque;
    }
    out
}

#[test]
fn test_writer_cone_of_a_loaded_export_is_the_export() {
    for (name, minted) in all_fixtures() {
        let from_lean = read(&minted);
        let loaded = load_export(NdjsonSource::new(minted.as_slice()).expect("a header"))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert!(loaded.refused.is_empty(), "{name}: {:?}", loaded.refused);
        let targets: BTreeSet<Name> = loaded.declared.iter().map(|d| d.name.clone()).collect();
        let mut written = Vec::new();
        let summary = write_cone(
            &loaded.env,
            &targets,
            &meta(),
            loaded.written_names.clone(),
            &mut written,
        )
        .unwrap_or_else(|e| panic!("{name}: {e}"));
        check_export_round_trip(written.as_slice(), &summary)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(summary.declarations, targets.len(), "{name}");

        // The same declarations, in the planner's order instead of Lean's:
        // compared by name. A hint is the kernel's unfolding priority, which
        // the loader may have adjusted, and is compared only for its kind of
        // difference below.
        let key = |d: &ExportDeclaration| d.declared_names()[0].to_unambiguous_string();
        let lean: BTreeMap<String, ExportDeclaration> = from_lean
            .iter()
            .map(|d| (key(d), without_hints(d)))
            .collect();
        let from_clean = read(&written);
        let clean: BTreeMap<String, ExportDeclaration> = from_clean
            .iter()
            .map(|d| (key(d), without_hints(d)))
            .collect();
        assert_eq!(
            lean.keys().collect::<Vec<_>>(),
            clean.keys().collect::<Vec<_>>(),
            "{name}"
        );
        for (declared, expected) in &lean {
            assert_eq!(Some(expected), clean.get(declared), "{name}: {declared}");
        }
        let hints = |all: &[ExportDeclaration]| -> BTreeMap<String, ReducibilityHintsData> {
            all.iter()
                .filter_map(|d| match d {
                    ExportDeclaration::Definition { hints, .. } => Some((key(d), *hints)),
                    _ => None,
                })
                .collect()
        };
        let (lean_hints, clean_hints) = (hints(&from_lean), hints(&from_clean));
        for (declared, stored) in &lean_hints {
            let written = clean_hints[declared];
            assert!(
                written == *stored || written == ReducibilityHintsData::Abbrev,
                "{name}: {declared} stored {stored:?}, written {written:?}"
            );
        }
        // Every record's references are to earlier records.
        let mut declared: BTreeSet<Name> = BTreeSet::new();
        for declaration in &from_clean {
            let own: BTreeSet<Name> = declaration.declared_names().into_iter().cloned().collect();
            let refs = &loaded.refs[own.iter().next().expect("a declared name")];
            for mentioned in refs {
                assert!(
                    declared.contains(mentioned) || own.contains(mentioned),
                    "{name}: {mentioned} is used before it is declared"
                );
            }
            declared.extend(own);
        }
    }
}

fn header(name: &str, level_params: &[&str], type_: Expr) -> ExportHeader {
    ExportHeader {
        name: Name::from_string(name),
        level_params: level_params.iter().map(|p| Name::from_string(p)).collect(),
        type_,
    }
}

fn definition(name: &str, type_: Expr, value: Expr) -> ExportDeclaration {
    ExportDeclaration::Definition {
        header: header(name, &[], type_),
        value,
        hints: ReducibilityHintsData::Regular(7),
        safety: DefinitionSafety::Safe,
    }
}

/// Records of the kinds no minted fixture has: an axiom, an opaque constant,
/// the four `quot` kinds, an `imax` level, a numeric name component.
fn handwritten() -> Vec<ExportDeclaration> {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let prop = Expr::sort(Level::zero());
    let numbered = Name::from_string("_private").str("M").num(0).str("ax");
    let mut out = vec![
        ExportDeclaration::Axiom {
            header: ExportHeader {
                name: numbered,
                level_params: vec![Name::from_string("u"), Name::from_string("v")],
                type_: Expr::sort(Level::imax(u.clone(), v.clone())),
            },
            is_unsafe: false,
        },
        ExportDeclaration::Opaque {
            header: header("O", &[], Expr::sort(Level::succ(Level::zero()))),
            value: prop.clone(),
            is_unsafe: false,
        },
        definition(
            "D",
            prop.clone(),
            Expr::let_named(
                Name::from_string("x"),
                prop.clone(),
                Expr::mdata(Vec::new(), Expr::str_lit("a\"b\\c\nd")),
                Expr::app(
                    Expr::lam(BinderInfo::InstImplicit, prop.clone(), Expr::bvar(0)),
                    Expr::proj(
                        Name::from_string("O"),
                        3,
                        Expr::bignat_lit(clean_kernel::expr::BigNat::from_limbs(vec![5, 9])),
                    ),
                ),
                true,
            ),
        ),
    ];
    for (name, kind) in [
        ("Quot", ParsedQuotKind::Type),
        ("Quot.mk", ParsedQuotKind::Mk),
        ("Quot.lift", ParsedQuotKind::Lift),
        ("Quot.ind", ParsedQuotKind::Ind),
    ] {
        // The kernel-built types name `Eq`, which this list does not declare;
        // the record's shape is under test here, not the quotient's types.
        out.push(ExportDeclaration::Quot {
            header: header(name, &["u"], Expr::sort(u.clone())),
            kind,
        });
    }
    out
}

#[test]
fn test_writer_record_kinds_the_fixtures_lack_read_back_equal() {
    let declarations = handwritten();
    let (written, summary) = write(&declarations, Spelling::new());
    assert_eq!(read(&written), declarations);
    check_export_round_trip(written.as_slice(), &summary).expect("a fixed point");
    assert_eq!(summary.axioms, vec!["_private.M.0.ax".to_owned()]);
    let text = String::from_utf8(written).expect("UTF-8");
    for expected in [
        r#"{"il":3,"imax":[1,2]}"#,
        r#""num":{"i":0,"pre":"#,
        r#"{"opaque":{"all":["#,
        r#""kind":"ctor""#,
        r#""hints":{"regular":7}"#,
        r#""natVal":"166020696663385964549""#,
        r#""strVal":"a\"b\\c\nd""#,
        r#""binderInfo":"instImplicit""#,
        r#""mdata":{"data":{},"expr":"#,
        r#""nondep":true"#,
    ] {
        assert!(text.contains(expected), "missing {expected} in\n{text}");
    }
}

/// lean4export's own export of a cone of `Init.Prelude` that reaches the
/// quotient (`tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/`).
fn lean4export_prelude_roots() -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/prelude_roots.ndjson.gz");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut out = Vec::new();
    flate2::read::GzDecoder::new(bytes.as_slice())
        .read_to_end(&mut out)
        .expect("a gzip stream");
    out
}

/// The names the export in `bytes` declares, in record order.
fn declared_in_order(bytes: &[u8]) -> Vec<String> {
    read(bytes)
        .iter()
        .flat_map(ExportDeclaration::declared_names)
        .map(Name::to_unambiguous_string)
        .collect()
}

#[test]
fn test_writer_cone_reaching_one_quotient_constant_writes_the_package() {
    let minted = lean4export_prelude_roots();
    let loaded = load_export(NdjsonSource::new(minted.as_slice()).expect("a header"))
        .expect("lean4export's export loads");
    assert!(loaded.refused.is_empty(), "{:?}", loaded.refused);
    let package = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
    let cone = |target: &str| -> Vec<String> {
        let targets: BTreeSet<Name> = [Name::from_string(target)].into();
        let mut out = Vec::new();
        let summary = write_cone(
            &loaded.env,
            &targets,
            &meta(),
            loaded.written_names.clone(),
            &mut out,
        )
        .unwrap_or_else(|e| panic!("{target}: {e}"));
        check_export_round_trip(out.as_slice(), &summary).expect("a fixed point");
        declared_in_order(&out)
    };

    // `Quot.lift` mentions `Quot` and `Eq`, not `Quot.mk` or `Quot.ind`; the
    // cone has all four, each after `Eq`, as lean4export writes it.
    let lifted = cone("Quot.lift");
    let eq = lifted
        .iter()
        .position(|n| n == "Eq")
        .expect("Eq is in the cone");
    for name in package {
        let at = lifted
            .iter()
            .position(|n| n == name)
            .unwrap_or_else(|| panic!("{name} is not in the cone: {lifted:?}"));
        assert!(eq < at, "{name} is written before Eq: {lifted:?}");
    }

    // Control: a cone that reaches no quotient constant has none of them.
    let added = cone("Nat.add");
    assert!(added.iter().any(|n| n == "Nat.add"));
    for name in package {
        assert!(!added.iter().any(|n| n == name), "{name} in {added:?}");
    }
}

mod refusals;
