// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The mdata payload reader, against real pinned-toolchain `.olean` files
//! (expected values from the pinned binary's `repr` of the stored type) and
//! against hand-built objects for the refusals.

use super::*;
use crate::expr::ParsedExpr;
use clean_kernel::name::Name;

/// The pinned toolchain's parsed `module`. These tests read Lean's own
/// `.olean` files, so a missing pinned toolchain FAILS them rather than
/// letting them pass without measuring anything.
fn olean(module: &str) -> crate::ParsedModule {
    let lib = crate::pinned_lean_lib_path().expect(crate::test_support::PINNED_LEAN_REQUIRED);
    let path = lib.join(format!("{}.olean", module.replace('.', "/")));
    crate::parse_module_file(&path).expect("pinned .olean must parse")
}

fn constant_type(module: &crate::ParsedModule, name: &str) -> ParsedExpr {
    module
        .constants
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("{name} must be in the module"))
        .type_
        .clone()
        .unwrap_or_else(|| panic!("{name} must have a parsed type"))
}

/// Every part of `module` (`.olean`, `.olean.server`, `.olean.private`), parsed
/// the way the importer parses them: under Lean 4.30's module system a private
/// declaration lives only in `.olean.private`, an incremental region over the
/// base.
/// The pinned toolchain's `module` as parts; fails without the toolchain
/// (see [`olean`]).
fn olean_parts(module: &str) -> Vec<crate::ParsedModulePart> {
    let lib = crate::pinned_lean_lib_path().expect(crate::test_support::PINNED_LEAN_REQUIRED);
    let path = lib.join(format!("{}.olean", module.replace('.', "/")));
    crate::parse_module_parts(&path).expect("pinned .olean parts must parse")
}

/// The one constant, in any part, whose name ends with `suffix` (a private
/// name carries a module-dependent prefix).
fn constant_type_by_suffix(parts: &[crate::ParsedModulePart], suffix: &str) -> ParsedExpr {
    let found: Vec<_> = parts
        .iter()
        .flat_map(|part| part.module.constants.iter())
        .filter(|c| c.name.ends_with(suffix))
        .collect();
    assert_eq!(
        found.len(),
        1,
        "exactly one constant must end with {suffix}"
    );
    found[0]
        .type_
        .clone()
        .unwrap_or_else(|| panic!("{suffix} must have a parsed type"))
}

/// Every mdata map in `e`, in traversal order.
fn maps(e: &ParsedExpr, out: &mut Vec<MDataMap>) {
    match e {
        ParsedExpr::MData(map, inner) => {
            out.push(map.clone());
            maps(inner, out);
        }
        ParsedExpr::App(f, a) => {
            maps(f, out);
            maps(a, out);
        }
        ParsedExpr::Lam(_, t, b, _) | ParsedExpr::ForallE(_, t, b, _) => {
            maps(t, out);
            maps(b, out);
        }
        ParsedExpr::LetE(_, t, v, b, _) => {
            maps(t, out);
            maps(v, out);
            maps(b, out);
        }
        ParsedExpr::Proj(_, _, s) => maps(s, out),
        _ => {}
    }
}

fn key(s: &str) -> Name {
    Name::anon().str(s)
}

/// `Nat.toUInt8 : (n : @& Nat) → UInt8` — Lean stores
/// `forallE n (mdata {borrowed := true} Nat) UInt8`.
#[test]
fn test_nat_to_uint8_domain_carries_borrowed() {
    let module = olean("Init.Data.UInt.BasicAux");
    let ParsedExpr::ForallE(_, domain, _, _) = constant_type(&module, "Nat.toUInt8") else {
        panic!("Nat.toUInt8's type must be a Pi");
    };
    match domain.as_ref() {
        ParsedExpr::MData(map, inner) => {
            assert_eq!(map, &vec![(key("borrowed"), MDataValue::Bool(true))]);
            assert_eq!(inner.as_ref(), &ParsedExpr::Const("Nat".into(), vec![]));
        }
        other => panic!("Nat.toUInt8's domain must be mdata-wrapped, got {other:?}"),
    }
}

/// `UInt8.toNat_ofNat` wraps its numeral in `no_index`, i.e.
/// `mdata {noindex := true}`.
#[test]
fn test_uint8_tonat_ofnat_carries_noindex() {
    let module = olean("Init.Data.UInt.Lemmas");
    let mut found = Vec::new();
    maps(&constant_type(&module, "UInt8.toNat_ofNat"), &mut found);
    assert_eq!(found, vec![vec![(key("noindex"), MDataValue::Bool(true))]]);
}

/// A stored TYPE carrying `DataValue.ofSyntax`. The pinned binary prints its
/// four `_patWithRef` payloads as the node `Lean.Parser.Term.hole` with the
/// single atom `_` (pre-order: `[N:Lean.Parser.Term.hole, A:_]`). `Syntax` is
/// one of the kinds carried under the reserved key (module doc).
#[test]
fn test_pat_with_ref_syntax_payload_is_decoded() {
    let parts = olean_parts("Init.Data.List.Impl");
    let ty = constant_type_by_suffix(&parts, "List.zipIdx_eq_zipIdxTR.match_1_2");
    let mut found = Vec::new();
    maps(&ty, &mut found);
    let carried = Name::anon()
        .str(RESERVED_KEY_ROOT)
        .str("syntax")
        .str("_patWithRef");
    assert!(
        found
            .iter()
            .flatten()
            .all(|(k, _)| k != &key("_patWithRef")),
        "a Syntax payload must never sit under Lean's own key: {found:?}"
    );
    let payloads: Vec<&str> = found
        .iter()
        .flatten()
        .filter(|(k, _)| k == &carried)
        .map(|(_, v)| match v {
            MDataValue::String(s) => s.as_ref(),
            other => panic!("a carried Syntax payload is a String, got {other:?}"),
        })
        .collect();
    assert_eq!(payloads.len(), 4, "{found:?}");
    for p in payloads {
        assert!(p.starts_with("(N "), "{p}");
        assert!(p.contains("\"Lean.Parser.Term.hole\" [(A "), "{p}");
        assert!(p.ends_with(" \"_\")])"), "{p}");
    }
}

// ---------------------------------------------------------------------------
// Refusals, on hand-built objects (no name objects needed).
// ---------------------------------------------------------------------------

const BASE: u64 = 0x1000;

/// A constructor object header: rc 0, cs_sz 0, `fields` pointer fields.
fn header(data: &mut [u8], at: usize, fields: u8, tag: u8) {
    data[at..at + 4].copy_from_slice(&0i32.to_le_bytes());
    data[at + 4..at + 6].copy_from_slice(&0u16.to_le_bytes());
    data[at + 6] = fields;
    data[at + 7] = tag;
}

fn word(data: &mut [u8], at: usize, value: u64) {
    data[at..at + 8].copy_from_slice(&value.to_le_bytes());
}

fn value_of(data: &[u8], at: usize) -> OleanResult<Carried> {
    CompactedRegion::new(data, BASE).read_data_value(BASE + at as u64)
}

#[test]
fn test_data_value_small_nat_and_bool_decode() {
    let mut data = vec![0u8; 64];
    header(&mut data, 8, 1, 3); // ofNat
    word(&mut data, 16, boxed(42));
    assert_eq!(
        value_of(&data, 8).expect("ofNat"),
        Carried::Exact(MDataValue::Nat(42))
    );

    header(&mut data, 32, 0, 1); // ofBool, scalar byte
    data[40] = 1;
    assert_eq!(
        value_of(&data, 32).expect("ofBool"),
        Carried::Exact(MDataValue::Bool(true))
    );
}

#[test]
fn test_data_value_small_negative_int_decodes() {
    let mut data = vec![0u8; 32];
    header(&mut data, 8, 1, 4); // ofInt
                                // lean_box((size_t)(int)-7): the low 32 bits carry the value.
    let raw = u64::from((-7i32) as u32);
    word(&mut data, 16, boxed(raw));
    assert_eq!(
        value_of(&data, 8).expect("ofInt"),
        Carried::Reserved("int", "-7".into())
    );
}

#[test]
fn test_data_value_refusals() {
    let mut data = vec![0u8; 96];
    header(&mut data, 8, 1, 9); // no such DataValue constructor
    let err = value_of(&data, 8).expect_err("unknown tag must be refused");
    assert!(
        err.to_string().contains("unknown DataValue constructor"),
        "{err}"
    );

    header(&mut data, 24, 1, 4); // ofInt pointing at a heap object
    word(&mut data, 32, BASE + 48);
    header(&mut data, 48, 0, tags::MPZ);
    let err = value_of(&data, 24).expect_err("a heap Int must be refused");
    assert!(err.to_string().contains("heap (big) Int"), "{err}");

    header(&mut data, 64, 0, 1); // ofBool with a non-Bool byte
    data[72] = 2;
    let err = value_of(&data, 64).expect_err("a non-Bool byte must be refused");
    assert!(err.to_string().contains("non-Bool"), "{err}");
}

/// A `List` that is neither `nil` nor `cons` is refused, not truncated.
#[test]
fn test_kvmap_malformed_list_is_refused() {
    let mut data = vec![0u8; 32];
    header(&mut data, 8, 3, 1); // tag 1 but three fields: not List.cons
    let region = CompactedRegion::new(&data, BASE);
    let err = region
        .read_mdata_map(BASE + 8)
        .expect_err("malformed KVMap list must be refused");
    assert!(err.to_string().contains("not a List.cons"), "{err}");
    assert_eq!(
        region.read_mdata_map(boxed(0)).expect("empty KVMap"),
        MDataMap::new()
    );
}

/// The reserved key keeps every component of Lean's key, numeric ones
/// included, under a per-kind namespace — so two different (kind, key) pairs
/// never meet, and a Lean key is recoverable from its carried form.
#[test]
fn test_reserved_key_is_injective_over_kind_and_key() {
    let lean_key = Name::anon().str("a").num(3).str("b");
    let syntax = reserved_key("syntax", &lean_key);
    assert_eq!(
        syntax,
        Name::anon()
            .str(RESERVED_KEY_ROOT)
            .str("syntax")
            .str("a")
            .num(3)
            .str("b")
    );
    assert_ne!(syntax, reserved_key("int", &lean_key));
    assert_ne!(
        syntax,
        reserved_key("syntax", &Name::anon().str("a").str("3").str("b"))
    );
    assert_eq!(root_component(&syntax), Some(RESERVED_KEY_ROOT));
    assert_eq!(root_component(&lean_key), Some("a"));
    assert_eq!(root_component(&Name::anon().num(1).str("x")), None);
}

/// A Lean key already in the reserved namespace is REFUSED (it would be
/// indistinguishable from a carried payload); every other key passes, including
/// one that merely CONTAINS the reserved component later.
#[test]
fn test_lean_key_in_reserved_namespace_is_refused() {
    let err = refuse_reserved_lean_key(&Name::anon().str(RESERVED_KEY_ROOT).str("x"))
        .expect_err("a reserved-namespace Lean key must be refused");
    assert!(err.to_string().contains("reserved namespace"), "{err}");
    refuse_reserved_lean_key(&key("borrowed")).expect("an ordinary Lean key passes");
    refuse_reserved_lean_key(&Name::anon().str("a").str(RESERVED_KEY_ROOT))
        .expect("the reserved component is reserved only as the ROOT");
}
