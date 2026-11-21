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

#[test]
fn measured_world_export_keeps_its_own_header_when_replay_declines_it() {
    let meta = ExportWriteMeta::for_source_world(clean_kernel::LeanWorld::Lean435)
        .expect("measured source world");
    let mut env = clean_kernel::Environment::new();
    let name = Name::from_string("Statement");
    env.add_decl(clean_kernel::env::Declaration::Definition {
        name: name.clone(),
        level_params: Vec::new(),
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::sort(Level::zero()),
        is_reducible: true,
    })
    .expect("checked definition");
    let mut output = Vec::new();
    let summary = write_export(&env, &BTreeSet::from([name]), &meta, &mut output)
        .expect("write the checked declaration");
    assert_eq!(summary.declarations, 1);
    let header: serde_json::Value =
        serde_json::from_slice(output.split(|b| *b == b'\n').next().unwrap())
            .expect("export header");
    assert_eq!(header["meta"]["lean"]["version"], "4.35.0");
    assert_eq!(
        header["meta"]["lean"]["githash"],
        "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
    );
    let verdict = crate::ndjson::check_export_reader(output.as_slice(), Default::default());
    assert_eq!(verdict.exit, crate::ndjson::ExitClass::Decline);
    assert_eq!(
        verdict.reader_error.expect("version decline").rule,
        "lean-version-unmapped"
    );
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

        // The dependency planner may reorder declarations. Compare every field by name.
        let key = |d: &ExportDeclaration| d.declared_names()[0].to_unambiguous_string();
        let from_clean = read(&written);
        let lean: BTreeMap<_, _> = from_lean.iter().map(|d| (key(d), d)).collect();
        let clean: BTreeMap<_, _> = from_clean.iter().map(|d| (key(d), d)).collect();
        assert_eq!(lean, clean, "{name}");
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
        all: vec![Name::from_string(name)],
    }
}

fn source_inductive() -> clean_kernel::Environment {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = clean_kernel::Environment::new();
    let name = Name::from_string("Chain");
    let chain = Expr::const_(name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name.clone().str("nil"),
                    type_: chain.clone(),
                },
                Constructor {
                    name: name.str("cons"),
                    type_: Expr::arrow(chain.clone(), chain),
                },
            ],
        }],
    })
    .expect("source inductive registers its two wrapper definitions");
    env
}

#[test]
fn source_eliminator_export_preserves_the_resident_definitions() {
    let env = source_inductive();
    let chain = Name::from_string("Chain");
    let primitive = chain.clone().str("rec");
    let targets = BTreeSet::from([chain.clone().str("casesOn"), chain.clone().str("recOn")]);
    let mut bytes = Vec::new();
    write_export(&env, &targets, &meta(), &mut bytes).expect("export source eliminators");
    let declarations = read(&bytes);
    let [ExportDeclaration::Inductive(block), definitions @ ..] = declarations.as_slice() else {
        panic!("the primitive block precedes the definitions that use it");
    };
    assert_eq!(block.recs.len(), 1);
    assert_eq!(block.recs[0].header.name, primitive);
    let mut found = BTreeSet::new();
    for definition in definitions {
        let ExportDeclaration::Definition { header, value, .. } = definition else {
            panic!("a wrapper must carry its definitional body");
        };
        let resident = env.get_const(&header.name).expect("resident wrapper");
        assert_eq!(header.type_, resident.type_);
        assert_eq!(header.level_params, resident.level_params);
        assert_eq!(Some(value), resident.value.as_ref());
        assert!(found.insert(header.name.clone()));
    }
    assert_eq!(found, targets);

    bytes.clear();
    write_export(&env, &BTreeSet::from([chain]), &meta(), &mut bytes).expect("primitive block");
    assert!(matches!(
        read(&bytes).as_slice(),
        [ExportDeclaration::Inductive(_)]
    ));
}

#[test]
fn source_eliminator_export_refuses_a_bodyless_or_foreign_mirror() {
    use clean_kernel::env::{Declaration, TrustedEnvExt};

    let env = source_inductive();
    let family = Name::from_string("Chain");
    let cases = family.clone().str("casesOn");
    let mut bodyless = env.clone();
    assert!(bodyless.forget_value(&cases));

    // A similarly named definition in another namespace is not this family's
    // eliminator, even when its resident type, body and mirror agree.
    let foreign_name = Name::from_string("Foreign.casesOn");
    let mut foreign = env;
    let mut mirror = foreign.get_recursor(&cases).expect("native mirror").clone();
    mirror.name = foreign_name.clone();
    let value = foreign.get_const(&cases).unwrap().value.clone().unwrap();
    foreign
        .add_decl(Declaration::Definition {
            name: foreign_name.clone(),
            level_params: mirror.level_params.clone(),
            type_: mirror.type_.clone(),
            value,
            is_reducible: false,
        })
        .expect("foreign definition");
    foreign.register_recursor(mirror);

    for (env, bad) in [(bodyless, cases), (foreign, foreign_name)] {
        let err = write_export(
            &env,
            &BTreeSet::from([family.clone()]),
            &meta(),
            &mut Vec::new(),
        )
        .expect_err("an unrepresentable primitive stops the export");
        assert!(
            matches!(err, ExportWriteError::BlockShape { block, problem }
            if block == "Chain" && problem.contains(&bad.to_unambiguous_string()))
        );
    }
}

/// Export serializes a resident rule body. Its ordinary constant reference
/// must therefore be declared even when the constructors never mention it.
#[test]
fn export_cone_follows_a_resident_recursor_rule() {
    let mut nat = read(&fixture("nat_add_literal.ndjson")).remove(0);
    let ExportDeclaration::Inductive(block) = &mut nat else {
        panic!("the minted first record is the Nat block");
    };
    assert_eq!(block.types[0].header.name, Name::from_string("Nat"));
    let name = Name::from_string("OnlyInRule");
    let type_ = Expr::sort(Level::succ(Level::zero()));
    let rhs = &mut block.recs[0].rules[0].rhs;
    // The importer checks this rule against the one it regenerates. The
    // unused argument keeps the written dependency and beta-reduces away.
    *rhs = Expr::app(
        Expr::lam(BinderInfo::Default, type_.clone(), rhs.clone()),
        Expr::const_(name.clone(), vec![]),
    );
    let helper = definition("OnlyInRule", type_, Expr::sort(Level::zero()));
    let (source, _) = write(&[helper, nat.clone()], Spelling::new());
    let loaded = load_export(NdjsonSource::new(source.as_slice()).expect("a header"))
        .expect("the structural records load");
    assert!(loaded.refused.is_empty(), "{:?}", loaded.refused);
    let mut bytes = Vec::new();
    write_export(
        &loaded.env,
        &[Name::from_string("Nat")].into(),
        &meta(),
        &mut bytes,
    )
    .expect("the recursor rule's dependency is included");
    let exported = read(&bytes);
    assert_eq!(exported.len(), 2);
    assert_eq!(exported[0].declared_names(), [&name]);
    assert_eq!(exported[1], nat);
}

/// The same environment has both conversion helpers available. A String
/// constant reference uses the type alone. A literal leaf uses the helpers.
#[test]
fn export_cone_includes_support_for_literal_leaves() {
    let prop = Expr::sort(Level::zero());
    let type_ = Expr::sort(Level::succ(Level::zero()));
    let string = Expr::const_(Name::from_string("String"), vec![]);
    let mut declarations = Vec::new();
    for name in ["String", "Nat", "Char.ofNat", "String.ofList"] {
        declarations.push(definition(name, type_.clone(), prop.clone()));
    }
    declarations.push(definition("TypeOnly", type_.clone(), string.clone()));
    declarations.push(definition("Text", string, Expr::str_lit("text")));
    // Exercise an implicit Nat reference independently of the declared type.
    declarations.push(definition("Number", type_, Expr::nat_lit(7)));
    let (source, _) = write(&declarations, Spelling::new());
    let loaded = load_export(NdjsonSource::new(source.as_slice()).expect("a header"))
        .expect("the structural records load");
    for (root, expected) in [
        ("TypeOnly", &["String", "TypeOnly"][..]),
        (
            "Text",
            &["Char.ofNat", "String", "String.ofList", "Text"][..],
        ),
        ("Number", &["Nat", "Number"][..]),
    ] {
        let mut bytes = Vec::new();
        write_export(
            &loaded.env,
            &[Name::from_string(root)].into(),
            &meta(),
            &mut bytes,
        )
        .expect("the single root exports");
        let declarations = read(&bytes);
        let actual: BTreeSet<_> = declarations
            .iter()
            .flat_map(ExportDeclaration::declared_names)
            .map(ToString::to_string)
            .collect();
        assert_eq!(
            actual,
            expected.iter().map(|s| (*s).to_owned()).collect(),
            "{root}"
        );
        assert_eq!(
            declarations.last().expect("root").declared_names()[0],
            &Name::from_string(root)
        );
    }
}

#[test]
fn ordinary_mutual_names_round_trip_without_declaring_their_siblings() {
    let sibling = Name::from_string("Sibling").num(3);
    let prop = Expr::sort(Level::zero());
    let type_ = Expr::sort(Level::succ(Level::zero()));
    let declarations = vec![
        ExportDeclaration::Definition {
            header: header("D", &[], type_.clone()),
            value: prop.clone(),
            hints: ReducibilityHintsData::Regular(7),
            safety: DefinitionSafety::Safe,
            all: vec![sibling.clone(), Name::from_string("D"), sibling.clone()],
        },
        ExportDeclaration::Theorem {
            header: header("T", &[], type_.clone()),
            value: prop.clone(),
            all: vec![sibling, Name::from_string("T")],
        },
        ExportDeclaration::Opaque {
            header: header("O", &[], type_),
            value: prop,
            is_unsafe: false,
            all: Vec::new(),
        },
    ];
    let (written, summary) = write(&declarations, Spelling::new());
    assert_eq!(summary.declarations, 3);
    assert_eq!(read(&written), declarations);
    check_export_round_trip(written.as_slice(), &summary).expect("identical mutual-name records");

    let mut loaded =
        load_export(NdjsonSource::new(written.as_slice()).expect("header")).expect("load");
    assert!(loaded.refused.is_empty());
    let name = Name::from_string("D");
    let targets = loaded.declared.iter().map(|d| d.name.clone()).collect();
    let mut output = Vec::new();
    write_cone(
        &loaded.env,
        &targets,
        &meta(),
        loaded.written_names.clone(),
        &mut output,
    )
    .expect("export installed declarations");
    let expected: BTreeMap<_, _> = declarations
        .iter()
        .map(|d| (d.declared_names()[0].clone(), d))
        .collect();
    let resident = read(&output);
    for d in &resident {
        assert_eq!(*expected.get(d.declared_names()[0]).expect("source"), d);
    }
    assert_eq!(resident.len(), declarations.len());

    // Reusing even the identical syntax in a freshly installed definition must retire
    // its imported annotations, also when the old environment still exists in a clone.
    let old = loaded.env.clone();
    assert!(loaded.env.forget_decl(&name));
    loaded
        .env
        .add_decl(clean_kernel::env::Declaration::Definition {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            is_reducible: true,
        })
        .expect("replacement definition");
    assert!(crate::import::export_fields::ExportFields::for_constant(&old, &name).is_some());
    output.clear();
    write_export(
        &loaded.env,
        &BTreeSet::from([name.clone()]),
        &meta(),
        &mut output,
    )
    .expect("replacement export");
    assert!(
        matches!(&read(&output)[0], ExportDeclaration::Definition { all, hints: ReducibilityHintsData::Abbrev, .. }
        if all == std::slice::from_ref(&name))
    );
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
            all: vec![Name::from_string("O")],
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
