// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked declarations exported without a CleanPayload bypass, then consumed
//! through the public parsed and dependency-checked direct import paths.

use clean_kernel::env::ConstantInfo;
use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::{Declaration, Environment, Expr, Name};
use clean_olean::header::HEADER_SIZE;
use clean_olean::region::CompactedRegion;
use clean_olean::{
    load_modules_with_deps_checked, load_parsed_module, parse_header, parse_module, LeanWorldScope,
    OleanExporter,
};

const INFOS: [BinderInfo; 4] = [
    BinderInfo::Default,
    BinderInfo::Implicit,
    BinderInfo::StrictImplicit,
    BinderInfo::InstImplicit,
];

struct Roundtrip {
    bytes: Vec<u8>,
    parsed: ConstantInfo,
    direct: ConstantInfo,
}

fn roundtrip(name: &str, type_: Expr, value: Expr, level_params: Vec<Name>) -> Roundtrip {
    let name = Name::from_string(name);
    let mut source = Environment::default();
    source
        .add_decl(Declaration::Definition {
            name: name.clone(),
            level_params,
            type_,
            value,
            is_reducible: true,
        })
        .expect("check the original declaration before export");
    // This API uses the legacy object representation, without a CleanPayload
    // footer that could replace the serialized expression on import.
    let bytes = OleanExporter::export_with_env(
        &source,
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .expect("normal environment export");

    let mut world = LeanWorldScope::new();
    world.admit_part("Layout", &bytes).unwrap();
    let mut parsed_env = Environment::default();
    world.bind_environment(&mut parsed_env).unwrap();
    let module = parse_module(&bytes).expect("parse exported bytes");
    load_parsed_module(&mut parsed_env, &module, Some("Layout".into()))
        .expect("load parsed declarations");

    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("Layout.olean"), &bytes).unwrap();
    let mut direct_env = Environment::default();
    load_modules_with_deps_checked(
        &mut direct_env,
        &["Layout".into()],
        &[dir.path().into()],
        &mut |_, _, _| Ok(()),
        &mut |_, _, _| Ok(()),
    )
    .expect("checked graph import of the same raw objects");
    Roundtrip {
        bytes,
        parsed: parsed_env.get_const(&name).unwrap().clone(),
        direct: direct_env.get_const(&name).unwrap().clone(),
    }
}

fn identity(info: BinderInfo) -> (Expr, Expr) {
    let sort = Expr::sort(Level::param(Name::from_string("u")));
    let type_ = Expr::pi(
        info,
        sort.clone(),
        Expr::pi(info, Expr::bvar(0), Expr::bvar(1)),
    );
    let value = Expr::lam(info, sort, Expr::lam(info, Expr::bvar(0), Expr::bvar(0)));
    (type_, value)
}

fn expression_offset(bytes: &[u8], value: bool) -> usize {
    let header = parse_header(bytes).unwrap();
    let region = CompactedRegion::new(bytes, header.base_addr);
    let offset = |slot| {
        region
            .ptr_to_offset(region.read_u64_at(slot).unwrap())
            .unwrap()
    };
    let root = offset(HEADER_SIZE);
    let constants = offset(root + 24);
    assert_eq!(region.read_u64_at(constants + 8).unwrap(), 1);
    let info = offset(constants + 24);
    let definition = offset(info + 8);
    if value {
        offset(definition + 16)
    } else {
        let constant = offset(definition + 8);
        offset(constant + 24)
    }
}

fn assert_lambda_infos(expr: &Expr, expected: BinderInfo) {
    let ExprKind::Lam(outer, _, body) = expr.kind() else {
        panic!("original lambda shape was lost")
    };
    let ExprKind::Lam(inner, _, _) = body.kind() else {
        panic!("original inner lambda shape was lost")
    };
    assert_eq!(outer.info, expected);
    assert_eq!(inner.info, expected);
}

fn assert_forall_infos(expr: &Expr, expected: BinderInfo) {
    let ExprKind::Pi(outer, _, body) = expr.kind() else {
        panic!("original forall shape was lost")
    };
    let ExprKind::Pi(inner, _, _) = body.kind() else {
        panic!("original inner forall shape was lost")
    };
    assert_eq!(outer.info, expected);
    assert_eq!(inner.info, expected);
}

#[test]
fn exported_lambda_preserves_all_binder_kinds_in_both_import_paths() {
    for info in INFOS {
        let (type_, value) = identity(info);
        let got = roundtrip("Layout.lambda", type_, value, vec![Name::from_string("u")]);
        for constant in [&got.parsed, &got.direct] {
            assert_lambda_infos(constant.value.as_ref().unwrap(), info);
        }
    }
}

#[test]
fn exported_forall_preserves_all_binder_kinds_in_both_import_paths() {
    for info in INFOS {
        let (type_, value) = identity(info);
        let got = roundtrip("Layout.forall", type_, value, vec![Name::from_string("u")]);
        for constant in [&got.parsed, &got.direct] {
            assert_forall_infos(&constant.type_, info);
        }
    }
}

#[test]
fn exported_let_preserves_dependent_and_nondependent_flags() {
    for nondep in [false, true] {
        let body = if nondep { Expr::prop() } else { Expr::bvar(0) };
        let value = Expr::let_named(
            Name::from_string("x"),
            Expr::type_(),
            Expr::prop(),
            body,
            nondep,
        );
        let expected_cache = value.cached_metadata_word();
        let got = roundtrip("Layout.let", Expr::type_(), value, vec![]);
        for constant in [&got.parsed, &got.direct] {
            let ExprKind::Let(_, _, _, _, actual) = constant.value.as_ref().unwrap().kind() else {
                panic!("original let expression was lost")
            };
            assert_eq!(*actual, nondep);
        }
        let offset = expression_offset(&got.bytes, true);
        let region = CompactedRegion::new(&got.bytes, parse_header(&got.bytes).unwrap().base_addr);
        assert_eq!(region.read_u64_at(offset + 40).unwrap(), expected_cache);
        assert_eq!(got.bytes[offset + 48], u8::from(nondep));
    }
}

#[test]
fn exported_binder_cache_words_are_original_computed_metadata() {
    let (type_, value) = identity(BinderInfo::Implicit);
    let got = roundtrip(
        "Layout.cache",
        type_.clone(),
        value.clone(),
        vec![Name::from_string("u")],
    );
    let header = parse_header(&got.bytes).unwrap();
    let region = CompactedRegion::new(&got.bytes, header.base_addr);
    for (source, is_value) in [(&type_, false), (&value, true)] {
        let offset = expression_offset(&got.bytes, is_value);
        let actual = region.read_u64_at(offset + 32).unwrap();
        assert_eq!(actual, source.cached_metadata_word());
        assert_ne!(
            actual & (1 << 43),
            0,
            "retain the actual universe-param flag"
        );
        assert_eq!(got.bytes[offset + 40], 1);
        let body = match source.kind() {
            ExprKind::Lam(_, _, body) | ExprKind::Pi(_, _, body) => body,
            _ => unreachable!(),
        };
        let inner = region
            .ptr_to_offset(region.read_u64_at(offset + 24).unwrap())
            .unwrap();
        let inner_cache = region.read_u64_at(inner + 32).unwrap();
        assert_eq!(inner_cache, body.cached_metadata_word());
        assert_eq!(inner_cache >> 44, 1, "preserve the inner loose-bvar range");
        assert_eq!(got.bytes[inner + 40], 1);
    }
}
