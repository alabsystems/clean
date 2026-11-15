// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Computational content only. No extracted object is admitted to a kernel.
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::import::runtime::{
    extract_olean_runtime_parts_with_limits, RuntimeExtractionLimits,
};
use clean_olean::module::{ConstantKind, DefinitionSafety};
use clean_olean::test_support::{compiled_fixture_dir, run_oracle};
use clean_olean::{
    extract_olean_runtime_parts, OleanExporter, RuntimeBody, RuntimeDeclaration, RuntimeFamily,
    RuntimeOleanInput, RuntimePartExtraction,
};
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::OnceLock;

fn input(label: &str, bytes: Vec<u8>) -> RuntimeOleanInput {
    RuntimeOleanInput {
        label: label.into(),
        bytes: bytes.into(),
    }
}
fn simple() -> Vec<u8> {
    let mut env = Environment::default();
    for name in [
        Name::anon().str("Quoted.item"),
        Name::anon().str("Quoted").str("item"),
    ] {
        env.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            value: Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            is_reducible: true,
        })
        .unwrap();
    }
    OleanExporter::export_with_env(&env, &[], &[], "0000000000000000000000000000000000000000")
        .unwrap()
}

fn typed_reference_twins() -> (Vec<u8>, Name, Name, Name, Expr) {
    let dotted = Name::anon().str("Quoted.item");
    let segmented = Name::anon().str("Quoted").str("item");
    let witness = Name::anon().str("UsesBoth");
    assert_eq!(dotted.to_string(), segmented.to_string());
    assert_ne!(dotted, segmented);

    let mut env = Environment::default();
    for name in [&dotted, &segmented] {
        env.add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();
    }
    let value = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::const_(dotted.clone(), vec![]),
        ),
        Expr::const_(segmented.clone(), vec![]),
    );
    env.add_decl(Declaration::Definition {
        name: witness.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        value: value.clone(),
        is_reducible: true,
    })
    .unwrap();
    let bytes =
        OleanExporter::export_with_env(&env, &[], &[], "0000000000000000000000000000000000000000")
            .unwrap();
    (bytes, dotted, segmented, witness, value)
}
fn word(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}
fn base(bytes: &[u8]) -> u64 {
    word(bytes, if bytes[5] == 1 { 48 } else { 80 })
}
fn root(bytes: &[u8]) -> u64 {
    word(bytes, if bytes[5] == 1 { 56 } else { 88 })
}
fn read(parts: &[Vec<u8>], ptr: u64) -> u64 {
    for bytes in parts {
        if let Some(off) = ptr
            .checked_sub(base(bytes))
            .and_then(|v| usize::try_from(v).ok())
        {
            if off.checked_add(8).is_some_and(|end| end <= bytes.len()) {
                return word(bytes, off);
            }
        }
    }
    panic!("uncaptured pointer {ptr}");
}
fn write(parts: &mut [Vec<u8>], ptr: u64, value: u64) {
    for bytes in parts {
        if let Some(off) = ptr
            .checked_sub(base(bytes))
            .and_then(|v| usize::try_from(v).ok())
        {
            if off.checked_add(8).is_some_and(|end| end <= bytes.len()) {
                bytes[off..off + 8].copy_from_slice(&value.to_le_bytes());
                return;
            }
        }
    }
    panic!("uncaptured mutation {ptr}");
}
fn array(parts: &[Vec<u8>], part: usize) -> u64 {
    read(parts, root(&parts[part]) + 24)
}
fn info(parts: &[Vec<u8>], part: usize, index: usize) -> u64 {
    read(parts, array(parts, part) + 24 + 8 * index as u64)
}
fn val(parts: &[Vec<u8>], part: usize, index: usize) -> u64 {
    read(parts, info(parts, part, index) + 8)
}
/// `ModuleData.entries` (field 4 of the root: `imports`, `constNames`,
/// `constants`, `extraConstNames`, `entries`, then the scalar `isModule`).
fn entries(parts: &[Vec<u8>], part: usize) -> u64 {
    read(parts, root(&parts[part]) + 40)
}
/// The part whose captured range `[base, base + len)` holds `ptr`: ownership
/// of a compacted object is decided by the range it was written into.
fn owner(parts: &[Vec<u8>], ptr: u64) -> Option<usize> {
    parts.iter().position(|bytes| {
        ptr.checked_sub(base(bytes))
            .and_then(|off| usize::try_from(off).ok())
            .is_some_and(|off| off < bytes.len())
    })
}
/// Distinct objects reachable from the object at `from`, counted per owning
/// part. Lean's 8-byte header (`lean.h`, `lean_object`) puts the tag in byte 7
/// and the pointer-field count of a constructor object (tag `0..=243`) in byte
/// 6; an `Array` (tag 246) carries its size at +8 and its elements from +24;
/// scalar arrays, strings and MPZ digits (248..=250) hold no pointers; any
/// other tag is refused rather than skipped. A boxed scalar (low bit set) is
/// not an object and an uncaptured pointer panics in `read`.
fn reachable_census(parts: &[Vec<u8>], from: u64) -> Vec<usize> {
    let mut census = vec![0; parts.len()];
    let mut seen = BTreeSet::new();
    let mut stack = vec![from];
    while let Some(ptr) = stack.pop() {
        if ptr % 2 == 1 || !seen.insert(ptr) {
            continue;
        }
        let part = owner(parts, ptr).unwrap_or_else(|| panic!("uncaptured pointer {ptr:#x}"));
        census[part] += 1;
        let header = read(parts, ptr);
        let fields = (header >> 48) & 0xff;
        match header >> 56 {
            0..=243 => stack.extend((0..fields).map(|i| read(parts, ptr + 8 + 8 * i))),
            246 => {
                let size = read(parts, ptr + 8);
                stack.extend((0..size).map(|i| read(parts, ptr + 24 + 8 * i)));
            }
            248..=250 => {}
            tag => panic!("object at {ptr:#x} carries tag {tag}, which this walk does not decode"),
        }
    }
    census
}
fn extract(parts: &[Vec<u8>]) -> Vec<RuntimePartExtraction> {
    extract_olean_runtime_parts(
        input("base", parts[0].clone()),
        parts.get(1).map(|b| input("server", b.clone())),
        parts.get(2).map(|b| input("private", b.clone())),
    )
}
fn row<'a>(part: &'a RuntimePartExtraction, name: &Name) -> (usize, &'a RuntimeDeclaration) {
    part.rows
        .iter()
        .find_map(|row| {
            row.declaration
                .as_ref()
                .ok()
                .filter(|value| &value.name == name)
                .map(|value| (row.index, value))
        })
        .expect("typed row")
}
/// The `runtime_probe` family (`tests/fixtures/lean/v4.30.0-rc2/runtime_probe/
/// README.md`), compiled by the pinned Lean on first use into the content-addressed
/// fixture cache. Fails closed when the toolchain is absent.
fn fixture_dir() -> PathBuf {
    compiled_fixture_dir("runtime_probe")
}

/// The module-system triple `RuntimeProbe.olean{,.server,.private}` and the
/// independent upstream oracle's reading of the same three files
/// (`oracle/DumpOlean.lean`, raw mode, base → server → private — the only order
/// Lean reads the parts of one module in). Read once per process; every count a
/// test below compares against comes from this oracle or from an unmutated
/// extraction of the same bytes, never from a literal — the one stated
/// exception is the object-provenance census that
/// `actual_private_provenance_binds_borrowed_base_and_server_bytes` derives by
/// its own pointer walk and pins (see its doc). Measured 2026-09-15 with
/// `lean --run DumpOlean.lean` over the family compiled by the recipe in its
/// README: `parts[*].constants.len()` = 24 / 24 / 25 and the union of `kind`
/// over the three parts is 7 (`axiom constructor definition inductive opaque
/// recursor theorem`) — numbers the tests derive, quoted here only so a drift
/// can be recognised.
fn fixture() -> (Vec<Vec<u8>>, Value) {
    static FIXTURE: OnceLock<(Vec<Vec<u8>>, Value)> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let dir = fixture_dir();
            let paths: Vec<PathBuf> = ["", ".server", ".private"]
                .iter()
                .map(|suffix| dir.join(format!("RuntimeProbe.olean{suffix}")))
                .collect();
            let parts = paths
                .iter()
                .map(|path| std::fs::read(path).expect("pinned-Lean compiled RuntimeProbe part"))
                .collect();
            let args: Vec<&str> = paths
                .iter()
                .map(|path| path.to_str().expect("utf-8 fixture path"))
                .collect();
            (parts, run_oracle(&args))
        })
        .clone()
}
/// Clean's kind in the oracle's `kind` vocabulary (`DumpOlean.lean`, `kindString`).
fn kind_label(kind: &ConstantKind) -> &'static str {
    match kind {
        ConstantKind::Axiom => "axiom",
        ConstantKind::Definition => "definition",
        ConstantKind::Theorem => "theorem",
        ConstantKind::Opaque => "opaque",
        ConstantKind::Quot => "quotient",
        ConstantKind::Inductive => "inductive",
        ConstantKind::Constructor => "constructor",
        ConstantKind::Recursor => "recursor",
        other => panic!("kind {other:?} has no upstream oracle spelling"),
    }
}
fn typed(value: &Value) -> Name {
    value
        .as_array()
        .unwrap()
        .iter()
        .fold(Name::anon(), |name, component| {
            match component["kind"].as_str().unwrap() {
                "str" => name.str(component["value"].as_str().unwrap()),
                "num" => name.num(component["value"].as_u64().unwrap()),
                _ => panic!("unknown upstream Name constructor"),
            }
        })
}
fn generated() -> Name {
    Name::anon()
        .str("RuntimeProbe")
        .str("count")
        .str("_unsafe_rec")
}

fn levels(value: &Value) -> Vec<Level> {
    value.as_array().unwrap().iter().map(level).collect()
}
fn level(value: &Value) -> Level {
    match value["tag"].as_str().unwrap() {
        "zero" => Level::zero(),
        "succ" => Level::succ(level(&value["inner"])),
        "param" => Level::param(typed(&value["name"])),
        // The oracle dumps the stored node; the decoder keeps it verbatim
        // (DECISIONS R150), so the expectation does not collapse it either.
        "max" => Level::Max(level(&value["left"]).into(), level(&value["right"]).into()),
        "imax" => Level::IMax(level(&value["left"]).into(), level(&value["right"]).into()),
        tag => panic!("unrepresented upstream Level {tag}"),
    }
}
fn core(value: &Value) -> Expr {
    let binder = || match value["binder"].as_u64().unwrap() {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => panic!(),
    };
    match value["tag"].as_str().unwrap() {
        "bvar" => Expr::bvar(value["index"].as_u64().unwrap().try_into().unwrap()),
        "sort" => Expr::sort(level(&value["level"])),
        "const" => Expr::const_(typed(&value["name"]), levels(&value["levels"])),
        "app" => Expr::app(core(&value["fun"]), core(&value["arg"])),
        "lam" => Expr::lam(binder(), core(&value["type"]), core(&value["body"])),
        "pi" => Expr::pi(binder(), core(&value["type"]), core(&value["body"])),
        "let" => Expr::let_named(
            typed(&value["name"]),
            core(&value["type"]),
            core(&value["value"]),
            core(&value["body"]),
            value["nondep"].as_bool().unwrap(),
        ),
        "proj" => Expr::proj(
            typed(&value["name"]),
            value["index"].as_u64().unwrap().try_into().unwrap(),
            core(&value["value"]),
        ),
        "nat" => Expr::nat_lit(value["value"].as_u64().expect("fixture Nat must fit u64")),
        "str" => Expr::str_lit(value["value"].as_str().unwrap()),
        "mdata-unmeasured" => {
            Expr::mdata(clean_kernel::expr::MDataMap::new(), core(&value["value"]))
        }
        tag => panic!("unrepresented upstream core Expr {tag}"),
    }
}
fn expected_refs(value: &Value, refs: &mut BTreeSet<Name>) {
    match value {
        Value::Object(fields) => {
            if matches!(value["tag"].as_str(), Some("const" | "proj")) {
                refs.insert(typed(&value["name"]));
            }
            for field in fields.values() {
                expected_refs(field, refs);
            }
        }
        Value::Array(values) => {
            for field in values {
                expected_refs(field, refs);
            }
        }
        _ => {}
    }
}
fn names(value: &Value) -> Vec<Name> {
    value.as_array().unwrap().iter().map(typed).collect()
}
fn family_oracle(d: &RuntimeDeclaration, expected: &Value, refs: &mut BTreeSet<Name>) {
    if let Some(all) = &d.mutual_declarations {
        assert_eq!(*all, names(&expected["all"]));
        refs.extend(all.iter().cloned());
    }
    let n = |key: &str| expected[key].as_u64().unwrap();
    let b = |key: &str| expected[key].as_bool().unwrap();
    match &d.family {
        RuntimeFamily::Inductive {
            all,
            constructors,
            num_params,
            num_indices,
            num_nested,
            is_nested,
            is_recursive,
            is_unsafe,
            is_reflexive,
        } => {
            assert_eq!(*all, names(&expected["all"]));
            assert_eq!(*constructors, names(&expected["constructors"]));
            assert_eq!(*num_params as u64, n("num_params"));
            assert_eq!(*num_indices as u64, n("num_indices"));
            assert_eq!(*num_nested, Some(n("num_nested")));
            assert_eq!(*is_nested, n("num_nested") != 0);
            assert_eq!(*is_recursive, b("is_recursive"));
            assert_eq!(*is_unsafe, b("is_unsafe"));
            assert_eq!(*is_reflexive, b("is_reflexive"));
            refs.extend(all.iter().chain(constructors).cloned());
        }
        RuntimeFamily::Constructor {
            inductive,
            index,
            num_params,
            num_fields,
            is_unsafe,
        } => {
            assert_eq!(*inductive, typed(&expected["inductive"]));
            refs.insert(inductive.clone());
            assert_eq!(*index as u64, n("index"));
            assert_eq!(*num_params as u64, n("num_params"));
            assert_eq!(*num_fields as u64, n("num_fields"));
            assert_eq!(*is_unsafe, b("is_unsafe"));
        }
        RuntimeFamily::Recursor {
            all,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            k,
            is_unsafe,
            rules,
        } => {
            assert_eq!(*all, names(&expected["all"]));
            refs.extend(all.iter().cloned());
            assert_eq!(*num_params as u64, n("num_params"));
            assert_eq!(*num_indices as u64, n("num_indices"));
            assert_eq!(*num_motives as u64, n("num_motives"));
            assert_eq!(*num_minors as u64, n("num_minors"));
            assert_eq!(*k, b("k"));
            assert_eq!(*is_unsafe, b("is_unsafe"));
            let wanted = expected["rules"].as_array().unwrap();
            assert_eq!(rules.len(), wanted.len());
            for (rule, oracle) in rules.iter().zip(wanted) {
                assert_eq!(rule.constructor, typed(&oracle["constructor"]));
                refs.insert(rule.constructor.clone());
                assert_eq!(
                    rule.num_fields as u64,
                    oracle["num_fields"].as_u64().unwrap()
                );
                assert_eq!(rule.rhs.as_ref().unwrap(), &core(&oracle["rhs"]));
                expected_refs(&oracle["rhs"], refs);
            }
        }
        RuntimeFamily::None => {}
        RuntimeFamily::UnsupportedQuotientMetadata => {
            panic!("fixture unexpectedly contains unsupported quotient metadata")
        }
    }
}

#[test]
fn owned_legacy_bodies_keep_exact_names_and_format_limitations() {
    let bytes = simple();
    let result = extract(std::slice::from_ref(&bytes));
    let part = &result[0];
    assert!(part.error.is_none());
    assert_eq!(part.source_row_count, Some(2));
    assert_eq!(part.identity.blake3, *blake3::hash(&bytes).as_bytes());
    assert_eq!(part.captured.bytes.as_ref(), bytes);
    let names: BTreeSet<_> = part
        .rows
        .iter()
        .map(|r| {
            let d = r.declaration.as_ref().unwrap();
            assert!(matches!(&d.body, RuntimeBody::Stored(Ok(_))));
            assert_eq!(
                d.type_.as_ref().unwrap(),
                &Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_())
            );
            assert!(
                !d.represented_fields_complete,
                "legacy mutual field is absent, not invented"
            );
            assert_eq!(d.issues.len(), 1);
            d.name.clone()
        })
        .collect();
    assert_eq!(names.len(), 2);
}

#[test]
fn raw_expression_references_keep_distinct_typed_names_and_mutation_is_visible() {
    let (bytes, dotted, segmented, witness, value) = typed_reference_twins();
    let mut parts = vec![bytes];
    let before = extract(&parts);
    let (index, declaration) = row(&before[0], &witness);
    assert_eq!(
        declaration.dependencies,
        [dotted.clone(), segmented.clone()].into()
    );
    assert!(matches!(&declaration.body, RuntimeBody::Stored(Ok(body)) if body == &value));
    assert_ne!(row(&before[0], &dotted).0, row(&before[0], &segmented).0);

    // Redirect only the right Const's raw Name pointer to the left Const's
    // Name object. A string-projected inventory would miss this distinction.
    let app = read(&parts, val(&parts, 0, index) + 16);
    let lam = read(&parts, app + 8);
    let right_const = read(&parts, app + 16);
    let left_const = read(&parts, lam + 24);
    let left_name = read(&parts, left_const + 8);
    write(&mut parts, right_const + 8, left_name);
    let changed = extract(&parts);
    let (_, declaration) = row(&changed[0], &witness);
    assert_eq!(declaration.dependencies, [dotted.clone()].into());
    assert!(matches!(&declaration.body, RuntimeBody::Stored(Ok(body)) if body != &value));

    write(&mut parts, right_const + 8, 3);
    let malformed = extract(&parts);
    let (_, declaration) = row(&malformed[0], &witness);
    assert!(!declaration.represented_fields_complete);
    assert!(matches!(declaration.body, RuntimeBody::Stored(Err(_))));
    assert_eq!(malformed[0].source_row_count, before[0].source_row_count);
}

#[test]
fn capture_limits_keep_over_budget_parts_as_unsupported_captures() {
    let bytes = simple();
    let part = extract_olean_runtime_parts_with_limits(
        input("base", bytes.clone()),
        None,
        None,
        RuntimeExtractionLimits {
            max_part_bytes: bytes.len() - 1,
            max_captured_bytes: bytes.len() * 2,
        },
    );
    assert_eq!(part[0].captured.bytes.as_ref(), bytes);
    assert!(part[0].error.as_ref().unwrap().contains("part has"));
    assert_eq!(part[0].source_row_count, None);
    assert!(part[0].rows.is_empty());

    let parts = extract_olean_runtime_parts_with_limits(
        input("base", bytes.clone()),
        Some(input("server", bytes.clone())),
        Some(input("private", bytes.clone())),
        RuntimeExtractionLimits {
            max_part_bytes: bytes.len(),
            max_captured_bytes: bytes.len(),
        },
    );
    assert_eq!(parts[0].source_row_count, Some(2));
    for part in &parts[1..] {
        assert!(part.error.as_ref().unwrap().contains("captured prefix"));
        assert_eq!(part.source_row_count, None);
        assert!(part.rows.is_empty());
        assert_eq!(part.captured.bytes.as_ref(), bytes);
    }
    assert_eq!(parts[2].borrowed_prefix.len(), 2);
}

#[test]
fn malformed_metadata_retains_exact_slot_and_good_siblings() {
    let mut parts = vec![simple()];
    let ptr = info(&parts, 0, 0);
    // ConstantInfo's final header byte is its constructor tag.
    let off = (ptr - base(&parts[0])) as usize;
    parts[0][off + 7] = 255;
    let result = extract(&parts);
    assert!(result[0].error.is_none());
    assert_eq!(result[0].source_row_count, Some(2));
    assert_eq!(result[0].rows.len(), 2);
    assert!(result[0].rows[0].declaration.is_err());
    assert!(result[0].rows[1].declaration.is_ok());
}

#[test]
fn missing_and_malformed_bodies_are_not_stubs_or_unit_values() {
    for pointer in [0, u64::MAX - 7] {
        let mut parts = vec![simple()];
        let at = val(&parts, 0, 0) + 16;
        write(&mut parts, at, pointer);
        let result = extract(&parts);
        let d = result[0].rows[0].declaration.as_ref().unwrap();
        assert!(!d.represented_fields_complete);
        assert!(if pointer == 0 {
            matches!(d.body, RuntimeBody::MissingRequiredValue)
        } else {
            matches!(d.body, RuntimeBody::Stored(Err(_)))
        });
        assert!(matches!(
            result[0].rows[1].declaration.as_ref().unwrap().body,
            RuntimeBody::Stored(Ok(_))
        ));
    }
}

#[test]
fn malformed_array_and_part_are_not_successful_empty_populations() {
    let mut parts = vec![simple()];
    let at = root(&parts[0]) + 24;
    write(&mut parts, at, 1);
    let result = extract(&parts);
    assert!(result[0].error.is_some());
    assert_eq!(result[0].source_row_count, None);
    let result = extract_olean_runtime_parts(
        input("bad", vec![0]),
        None,
        Some(input("also retained", vec![1])),
    );
    assert_eq!(result.len(), 2);
    assert!(result.iter().all(|p| p.error.is_some()));
    assert_eq!(result[1].borrowed_prefix, vec![result[0].identity.clone()]);
}

#[test]
fn capacity_and_array_header_mutations_refuse_without_relabeling_empty() {
    for mutation in 0..5 {
        let mut parts = vec![simple()];
        let ptr = array(&parts, 0);
        let off = (ptr - base(&parts[0])) as usize;
        match mutation {
            0 => write(&mut parts, ptr + 16, 1),
            1 => parts[0][off] = 1,
            2 => parts[0][off + 6] = 1,
            3 => parts[0][off + 4] = 1,
            _ => parts[0][off + 7] = 247,
        }
        let result = extract(&parts);
        assert!(result[0].error.is_some(), "mutation {mutation}");
        assert_eq!(result[0].source_row_count, None);
        assert_eq!(result[0].captured.bytes.as_ref(), parts[0]);
    }
}

/// The row count per part is the oracle's, not a literal: the lost original's
/// `[24, 24, 25]` happens to be reproduced by the re-authored source (see the
/// family README), but the oracle is the witness and stays so under a re-author.
#[test]
fn actual_all_part_rows_match_independent_upstream_identity_kind_and_body_presence() {
    let (parts, oracle) = fixture();
    let result = extract(&parts);
    assert_eq!(result.len(), 3);
    for (index, part) in result.iter().enumerate() {
        assert!(part.error.is_none(), "{:?}", part.error);
        let expected = oracle["parts"][index]["constants"].as_array().unwrap();
        assert!(!expected.is_empty(), "part {index} has upstream rows");
        assert_eq!(part.source_row_count, Some(expected.len()));
        assert_eq!(part.rows.len(), expected.len());
        for (slot, wanted) in part.rows.iter().zip(expected) {
            let d = slot.declaration.as_ref().unwrap();
            assert_eq!(d.name, typed(&wanted["name"]));
            assert_eq!(kind_label(&d.kind), wanted["kind"].as_str().unwrap());
            assert_eq!(
                d.level_params,
                wanted["levels"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(typed)
                    .collect::<Vec<_>>()
            );
            assert!(d.type_.is_ok(), "{:?}: {:?}", d.name, d.issues);
            assert_eq!(
                d.type_.as_ref().unwrap(),
                &core(&wanted["type_core"]),
                "whole type {:?}",
                d.name
            );
            if let RuntimeBody::Stored(value) = &d.body {
                assert_eq!(
                    value.as_ref().unwrap(),
                    &core(&wanted["value_core"]),
                    "whole body {:?}",
                    d.name
                );
            }
            let mut references = BTreeSet::new();
            expected_refs(&wanted["type_core"], &mut references);
            expected_refs(&wanted["value_core"], &mut references);
            family_oracle(d, &wanted["family"], &mut references);
            assert_eq!(
                d.dependencies, references,
                "whole typed reference set {:?}",
                d.name
            );
            assert_eq!(
                matches!(d.body, RuntimeBody::Stored(Ok(_))),
                !wanted["value"].is_null(),
                "{:?}: {:?}",
                d.name,
                d.issues
            );
            for key in ["type_refs", "value_refs"] {
                if let Some(refs) = wanted[key].as_array() {
                    for name in refs {
                        assert!(d.dependencies.contains(&typed(name)));
                    }
                }
            }
        }
    }
}

#[test]
fn actual_generated_partial_body_and_safe_quoted_twins_remain_distinct() {
    let (parts, _) = fixture();
    let result = extract(&parts);
    let (_, partial) = row(&result[2], &generated());
    assert_eq!(partial.declaration_safety, Some(DefinitionSafety::Partial));
    assert!(matches!(partial.body, RuntimeBody::Stored(Ok(_))));
    assert!(
        partial.dependencies.contains(&generated()),
        "actual recursive body retained"
    );
    for name in [
        Name::anon().str("RuntimeProbe").str("count._unsafe_rec"),
        Name::anon()
            .str("RuntimeProbe")
            .str("safe")
            .str("_unsafe_rec"),
    ] {
        let (_, safe) = row(&result[2], &name);
        assert_eq!(safe.declaration_safety, Some(DefinitionSafety::Safe));
        assert!(matches!(safe.body, RuntimeBody::Stored(Ok(_))));
        assert_ne!(safe.name, partial.name);
        assert_ne!(format!("{:?}", safe.body), format!("{:?}", partial.body));
    }
    for part in &result[..2] {
        let (_, stub) = row(part, &generated());
        assert_eq!(stub.kind, ConstantKind::Axiom);
        assert!(matches!(stub.body, RuntimeBody::NoStoredValueForKind));
    }
}

#[test]
fn actual_recursor_rhs_and_family_names_are_not_dropped_from_dependencies() {
    let (parts, _) = fixture();
    let result = extract(&parts);
    let (_, d) = row(&result[2], &Name::anon().str("Unary").str("rec"));
    let RuntimeFamily::Recursor { all, rules, .. } = &d.family else {
        panic!("missing recursor")
    };
    assert_eq!(rules.len(), 2);
    assert_eq!(all, &[Name::anon().str("Unary")]);
    for rule in rules {
        assert!(rule.rhs.is_ok());
        assert!(d.dependencies.contains(&rule.constructor));
    }
    assert!(d.dependencies.contains(&Name::anon().str("Unary")));
}

#[test]
fn exact_nested_family_counts_zero_one_two_do_not_collapse_to_bool() {
    let (original, _) = fixture();
    let before = extract(&original);
    let (index, _) = row(&before[0], &Name::anon().str("Unary"));
    for count in [0, 1, 2] {
        let mut parts = original.clone();
        let at = val(&parts, 0, index) + 48;
        write(&mut parts, at, count * 2 + 1);
        let result = extract(&parts);
        let (_, d) = row(&result[0], &Name::anon().str("Unary"));
        let RuntimeFamily::Inductive {
            num_nested,
            is_nested,
            ..
        } = &d.family
        else {
            panic!()
        };
        assert_eq!(*num_nested, Some(count));
        assert_eq!(*is_nested, count != 0);
    }
}

/// The second half used to extract base + private with NO server and demand a
/// refusal or an incomplete row. That asks the fixture's private CONSTANTS to
/// name a server-owned object, and on the pinned toolchain they never do:
/// `reachable_census` walks every object reachable from the private part's
/// `constants` array and finds 617 base-owned, 150 private-owned and **0**
/// server-owned objects — the 2256-byte server part owns only its root, decl
/// ranges and a module-doc slot, which the runtime extractor does not read. The
/// census is DERIVED below on every run (until 2026-09-15 it was quoted from a
/// one-off Python walk that was nowhere in the tree) and the three figures are
/// asserted, so this sentence cannot rot; they are a property of the
/// sha256-pinned triple in the family README, not of a lost original. The
/// control beside it walks the same part's `entries`, through which server
/// objects ARE reachable, so the zero is a fact about `constants` and not about
/// a walker blind to the server range. So, as
/// `companion_extension_tests::borrowed_roots_require_captured_objects_not_zero_filled_gaps`
/// does for the loader, the server dependency is made explicit instead of
/// assumed: the private root is redirected at the authentic server root, which
/// resolves while the server is captured and must not read as a success without it.
#[test]
fn actual_private_provenance_binds_borrowed_base_and_server_bytes() {
    let (original, _) = fixture();
    let census = reachable_census(&original, array(&original, 2));
    assert_eq!(
        census[1], 0,
        "no server-owned object is reachable from the private `constants`: {census:?}"
    );
    let via_entries = reachable_census(&original, entries(&original, 2));
    assert!(
        via_entries[1] > 0,
        "control: server objects must be reachable from the private `entries` ({via_entries:?})"
    );
    assert_eq!(
        (census[0], census[2]),
        (617, 150),
        "base-owned / private-owned objects reachable from the private `constants` \
         (update the doc comment above with the derived census)"
    );
    let before = extract(&original);
    for part in [0, 1] {
        let mut mutated = original.clone();
        mutated[part][40] ^= 1;
        let after = extract(&mutated);
        assert_eq!(before[2].identity, after[2].identity);
        assert_ne!(before[2].borrowed_prefix, after[2].borrowed_prefix);
        assert!(after[2].error.is_some(), "part header disagreement refuses");
        assert_eq!(after[2].captured.bytes, before[2].captured.bytes);
    }
    let mut borrowed = original.clone();
    borrowed[2][88..96].copy_from_slice(&original[1][88..96]);
    let with_server = extract(&borrowed);
    assert_eq!(with_server.len(), 3);
    assert!(
        with_server[2].error.is_none(),
        "captured authentic server root resolves: {:?}",
        with_server[2].error
    );
    assert_eq!(with_server[2].source_row_count, before[1].source_row_count);
    assert!(with_server[2].rows.iter().all(|r| r.declaration.is_ok()));
    let missing = extract_olean_runtime_parts(
        input("base", borrowed[0].clone()),
        None,
        Some(input("private", borrowed[2].clone())),
    );
    assert_eq!(missing.len(), 2);
    assert_eq!(
        missing[1].borrowed_prefix,
        vec![missing[0].identity.clone()]
    );
    assert!(
        missing[1].error.is_some()
            || missing[1].rows.iter().any(|r| r.declaration.is_err()
                || r.declaration
                    .as_ref()
                    .is_ok_and(|d| !d.represented_fields_complete)),
        "no fake success through missing captured server"
    );
}

/// "Sibling population unchanged" is measured against the unmutated extraction
/// of the same bytes, not against a literal row count.
#[test]
fn malformed_recursor_rule_list_retains_error_and_unchanged_sibling_population() {
    let (mut parts, _) = fixture();
    let before = extract(&parts);
    let (index, _) = row(&before[2], &Name::anon().str("Unary").str("rec"));
    let at = val(&parts, 2, index) + 56;
    write(&mut parts, at, 3);
    let result = extract(&parts);
    assert!(before[2].source_row_count.is_some());
    assert_eq!(result[2].source_row_count, before[2].source_row_count);
    assert!(result[2].rows[index].declaration.is_err());
    assert!(row(&result[2], &generated()).1.type_.is_ok());
}

#[test]
fn actual_valid_body_pointer_mutation_changes_owned_content_not_authority() {
    let (mut parts, _) = fixture();
    let before = extract(&parts);
    let (target, old) = row(&before[2], &generated());
    let (other, safe) = row(
        &before[2],
        &Name::anon().str("RuntimeProbe").str("count._unsafe_rec"),
    );
    let ptr = read(&parts, val(&parts, 2, other) + 16);
    let at = val(&parts, 2, target) + 16;
    write(&mut parts, at, ptr);
    let after = extract(&parts);
    let (_, changed) = row(&after[2], &generated());
    let RuntimeBody::Stored(Ok(old)) = &old.body else {
        panic!()
    };
    let RuntimeBody::Stored(Ok(expected)) = &safe.body else {
        panic!()
    };
    let RuntimeBody::Stored(Ok(actual)) = &changed.body else {
        panic!()
    };
    assert_eq!(actual, expected);
    assert_ne!(actual, old);
    assert_eq!(changed.declaration_safety, Some(DefinitionSafety::Partial));
    assert_ne!(before[2].identity, after[2].identity);
    assert_eq!(after[2].rows.len(), before[2].rows.len());
}

#[path = "runtime_declarations/refusals.rs"]
mod refusals;
