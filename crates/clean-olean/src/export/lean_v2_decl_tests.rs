// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::header::OleanHeader;
use crate::region::CompactedRegion;
use clean_kernel::{BinderInfo, LevelVec};

const PLAIN: &[u8] =
    include_bytes!("../../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean");

fn writer() -> LeanV2RegionWriter {
    LeanV2RegionWriter::new(&OleanHeader::parse(PLAIN).unwrap(), 0x10000).unwrap()
}

fn region(bytes: &[u8]) -> CompactedRegion<'_> {
    CompactedRegion::new(bytes, OleanHeader::parse(bytes).unwrap().base_addr)
}

fn word(region: &CompactedRegion<'_>, offset: usize) -> u64 {
    region.read_u64_at(offset).unwrap()
}

fn field(region: &CompactedRegion<'_>, object: usize, index: usize) -> u64 {
    word(region, object + 8 * (index + 1))
}

fn object(region: &CompactedRegion<'_>, object: usize, index: usize) -> usize {
    region.ptr_to_offset(field(region, object, index)).unwrap()
}

fn root(region: &CompactedRegion<'_>) -> usize {
    region.ptr_to_offset(region.root_ptr().unwrap()).unwrap()
}

fn constant(region: &CompactedRegion<'_>, index: usize) -> usize {
    // An array has boxed element pointers after the size and capacity.
    object(region, object(region, root(region), 2), index + 2)
}

fn compare_object(
    written: &CompactedRegion<'_>,
    ours: usize,
    official: &CompactedRegion<'_>,
    theirs: usize,
) {
    let header = official.read_header_at(theirs).unwrap();
    assert_eq!(
        written.bytes_at(ours, 8).unwrap(),
        official.bytes_at(theirs, 8).unwrap()
    );
    let scalar_offset = 8 * (usize::from(header.other) + 1);
    let scalar_len = usize::from(header.cs_sz) - scalar_offset;
    assert_eq!(
        written.bytes_at(ours + scalar_offset, scalar_len).unwrap(),
        official
            .bytes_at(theirs + scalar_offset, scalar_len)
            .unwrap()
    );
}

#[test]
fn stable_theorem_matches_official_record_and_proof_layout() {
    let levels: LevelVec = [Level::succ(Level::zero())].into_iter().collect();
    let nat = Expr::const_str("Nat");
    let zero = Expr::const_str("Nat.zero");
    let lhs = Expr::app(Expr::const_str("StablePlain.successor"), zero.clone());
    let rhs = Expr::app(Expr::const_str("Nat.succ"), zero);
    let info = ConstantInfo::new_with_reducibility(
        Name::from_string("StablePlain.successor_zero"),
        Vec::new(),
        Expr::apps(
            Expr::const_str_levels("Eq", levels.clone()),
            [nat.clone(), lhs, rhs.clone()],
        ),
        Some(Expr::apps(
            Expr::const_str_levels("Eq.refl", levels),
            [nat, rhs],
        )),
        Reducibility::Opaque,
        ConstantKind::Theorem,
    );
    let mut writer = writer();
    let value = writer
        .write_constant_info(&info, DefinitionSafety::Safe)
        .unwrap();
    let bytes = writer
        .finish_ordinary_module(&[], std::slice::from_ref(&info.name), &[value], &[], &[])
        .unwrap();
    let written = region(&bytes);
    let official = region(PLAIN);
    let (ours, theirs) = (constant(&written, 0), constant(&official, 0));
    compare_object(&written, ours, &official, theirs);
    let (ours, theirs) = (object(&written, ours, 0), object(&official, theirs, 0));
    compare_object(&written, ours, &official, theirs);
    for index in 0..3 {
        compare_object(
            &written,
            object(&written, ours, index),
            &official,
            object(&official, theirs, index),
        );
    }
    assert_eq!(
        written
            .read_kernel_name_list(field(&written, ours, 2))
            .unwrap(),
        [info.name]
    );
}

#[test]
fn stable_opaque_safety_and_ordered_groups_match_measured_layout() {
    let info = ConstantInfo::new_with_reducibility(
        Name::from_string("Layout.opaqueUnsafe"),
        Vec::new(),
        Expr::const_str("Nat"),
        Some(Expr::nat_lit(27)),
        Reducibility::Opaque,
        ConstantKind::Opaque,
    );
    let mut proof = info.clone();
    proof.name = Name::from_string("Layout.proof");
    proof.kind = ConstantKind::Theorem;
    proof.type_ = Expr::const_str("True");
    proof.value = Some(Expr::const_str("True.intro"));
    let numeric = Name::from_string("Layout").num(0);
    let quoted = Name::from_string("Layout").str("0");
    let opaque_group = [quoted.clone(), info.name.clone(), numeric.clone()];
    let theorem_group = [numeric, proof.name.clone(), quoted];
    for (info, all, safety, tag, size, is_unsafe) in [
        (
            &info,
            &opaque_group,
            DefinitionSafety::Unsafe,
            3,
            40,
            Some(1),
        ),
        (&info, &opaque_group, DefinitionSafety::Safe, 3, 40, Some(0)),
        (&proof, &theorem_group, DefinitionSafety::Safe, 2, 32, None),
    ] {
        let mut writer = writer();
        let record = writer
            .write_constant_info_with_group(info, safety, all)
            .unwrap();
        let bytes = writer
            .finish_ordinary_module(&[], std::slice::from_ref(&info.name), &[record], &[], &[])
            .unwrap();
        let written = region(&bytes);
        let outer = constant(&written, 0);
        let header = written.read_header_at(outer).unwrap();
        assert_eq!((header.tag, header.other, header.cs_sz), (tag, 1, 16));
        let inner = object(&written, outer, 0);
        let header = written.read_header_at(inner).unwrap();
        assert_eq!((header.tag, header.other, header.cs_sz), (0, 3, size));
        assert_eq!(
            written
                .read_kernel_name_list(field(&written, inner, 2))
                .unwrap(),
            *all
        );
        if let Some(is_unsafe) = is_unsafe {
            assert_eq!(word(&written, inner + 32), is_unsafe);
        }
    }
}

#[test]
fn stable_constant_records_refuse_bad_groups_shapes_and_safety() {
    let info = ConstantInfo::new_with_reducibility(
        Name::from_string("Layout.proof"),
        Vec::new(),
        Expr::const_str("True"),
        Some(Expr::const_str("True.intro")),
        Reducibility::Opaque,
        ConstantKind::Theorem,
    );
    let mut writer = writer();
    let sibling = Name::from_string("Layout.sibling");
    let this = info.name.clone();
    for invalid in [
        Vec::new(),
        vec![sibling.clone()],
        vec![this.clone(), this.clone()],
        vec![this.clone(), sibling.clone(), sibling],
        vec![this.clone(), Name::anon()],
    ] {
        assert!(writer
            .write_constant_info_with_group(&info, DefinitionSafety::Safe, &invalid)
            .is_err());
    }
    for safety in [DefinitionSafety::Partial, DefinitionSafety::Unsafe] {
        assert!(writer.write_constant_info(&info, safety).is_err());
    }
    let mut opaque = info.clone();
    opaque.kind = ConstantKind::Opaque;
    assert!(writer
        .write_constant_info(&opaque, DefinitionSafety::Partial)
        .is_err());
    opaque.value = None;
    assert!(writer
        .write_constant_info(&opaque, DefinitionSafety::Safe)
        .is_err());
    opaque.kind = ConstantKind::Axiom;
    assert!(writer
        .write_constant_info_with_group(&opaque, DefinitionSafety::Safe, &[this])
        .is_err());
    assert!(writer
        .write_constant_info_with_group(&opaque, DefinitionSafety::Safe, &[])
        .is_ok());
}

#[test]
fn stable_successor_matches_official_definition_and_expression_layouts() {
    let nat = Expr::const_str("Nat");
    let info = ConstantInfo::new_with_reducibility(
        Name::from_string("StablePlain.successor"),
        Vec::new(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        Some(Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
        )),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    );
    let mut writer = writer();
    let value = writer
        .write_constant_info(&info, DefinitionSafety::Safe)
        .unwrap();
    let bytes = writer
        .finish_ordinary_module(&[], &[info.name], &[value], &[], &[])
        .unwrap();

    let official = region(PLAIN);
    let written = region(&bytes);
    let input = constant(&official, 1);
    let output = constant(&written, 0);
    compare_object(&written, output, &official, input);
    let (defn, lean_defn) = (object(&written, output, 0), object(&official, input, 0));
    compare_object(&written, defn, &official, lean_defn);
    let (base, lean_base) = (object(&written, defn, 0), object(&official, lean_defn, 0));
    compare_object(&written, base, &official, lean_base);
    assert_eq!(field(&written, base, 1), 1); // List.nil
    let (ty, lean_ty) = (object(&written, base, 2), object(&official, lean_base, 2));
    let (value, lean_value) = (object(&written, defn, 1), object(&official, lean_defn, 1));
    let (hints, lean_hints) = (object(&written, defn, 2), object(&official, lean_defn, 2));
    let (all, lean_all) = (object(&written, defn, 3), object(&official, lean_defn, 3));
    let (app, lean_app) = (object(&written, value, 2), object(&official, lean_value, 2));
    for (ours, theirs) in [
        (ty, lean_ty),
        (value, lean_value),
        (hints, lean_hints),
        (all, lean_all),
        (app, lean_app),
        (object(&written, ty, 1), object(&official, lean_ty, 1)),
        (object(&written, app, 0), object(&official, lean_app, 0)),
        (object(&written, app, 1), object(&official, lean_app, 1)),
    ] {
        compare_object(&written, ours, &official, theirs);
    }
    assert_eq!(field(&written, ty, 0), 1); // Anonymous forall binder.
    assert_eq!(field(&written, value, 0), 1); // Anonymous lambda binder.
    assert_eq!(field(&written, all, 0), field(&written, base, 0));
    assert_eq!(field(&written, all, 1), 1);
    assert_eq!(field(&written, object(&written, app, 1), 0), 1); // BVar 0.
    assert!(crate::decode_clean_payload(&bytes).unwrap().is_none());
}

#[test]
fn stable_axioms_and_literals_match_measured_official_lean_words() {
    // Stable 4.36.0:
    // universe u
    // axiom tm : Sort (u + 1)
    // unsafe axiom one : Prop
    // def txt : String := "eight bytes✓"
    let u = Name::from_string("u");
    let tm = ConstantInfo::new_with_reducibility(
        Name::from_string("tm"),
        vec![u.clone()],
        Expr::sort(Level::succ(Level::param(u))),
        None,
        Reducibility::Opaque,
        ConstantKind::Axiom,
    );
    let one = ConstantInfo::new_with_reducibility(
        Name::from_string("one"),
        Vec::new(),
        Expr::sort(Level::zero()),
        None,
        Reducibility::Opaque,
        ConstantKind::Axiom,
    );
    let txt = ConstantInfo::new_with_reducibility(
        Name::from_string("txt"),
        Vec::new(),
        Expr::const_str("String"),
        Some(Expr::str_lit("eight bytes✓")),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    );
    let mut writer = writer();
    let values = [
        writer
            .write_constant_info(&tm, DefinitionSafety::Safe)
            .unwrap(),
        writer
            .write_constant_info(&one, DefinitionSafety::Unsafe)
            .unwrap(),
        writer
            .write_constant_info(&txt, DefinitionSafety::Safe)
            .unwrap(),
    ];
    let bytes = writer
        .finish_ordinary_module(&[], &[tm.name, one.name, txt.name], &values, &[], &[])
        .unwrap();
    let written = region(&bytes);
    let axiom = object(&written, constant(&written, 0), 0);
    let base = object(&written, axiom, 0);
    let sort = object(&written, base, 2);
    let succ = object(&written, sort, 0);
    let param = object(&written, succ, 0);
    assert_eq!(field(&written, axiom, 1), 0);
    assert_eq!(field(&written, sort, 1), 0x0000_0800_f4b5_65c8);
    assert_eq!(field(&written, succ, 1), 0x0000_0102_8762_4c44);
    assert_eq!(field(&written, param, 1), 0x0000_0002_9afc_6914);
    assert_eq!(
        field(&written, object(&written, base, 1), 0),
        field(&written, param, 0)
    );

    let axiom = object(&written, constant(&written, 1), 0);
    let sort = object(&written, object(&written, axiom, 0), 2);
    assert_eq!(field(&written, axiom, 1), 1);
    assert_eq!(field(&written, sort, 0), 1); // Level.zero
    assert_eq!(field(&written, sort, 1), 0xeb1b_d69c);

    let defn = object(&written, constant(&written, 2), 0);
    let lit = object(&written, defn, 1);
    assert_eq!(field(&written, lit, 1), 0x76b1_b92b);
    assert_eq!(
        written
            .read_header_at(object(&written, lit, 0))
            .unwrap()
            .tag,
        1
    );
}

#[test]
fn stable_let_and_projection_match_official_raw_terms() {
    let nat = Expr::const_str("Nat");
    let mut writer = writer();
    // Measured by passing these raw Expr forms to Lean 4.36.0's addDecl.
    let let_expr = Expr::let_named(
        Name::from_string("x"),
        nat.clone(),
        Expr::nat_lit_u128((1 << 64) + 1),
        Expr::bvar(0),
        false,
    );
    let levels: LevelVec = [Level::zero(), Level::zero()].into_iter().collect();
    let pair = Expr::apps(
        Expr::const_str_levels("Prod.mk", levels),
        [nat.clone(), nat.clone(), Expr::bvar(0), Expr::bvar(0)],
    );
    let projection = Expr::proj(Name::from_string("Prod"), 0, pair);
    let lambda = Expr::lam(BinderInfo::StrictImplicit, nat.clone(), projection);
    let let_info = ConstantInfo::new_with_reducibility(
        Name::from_string("rawNat"),
        Vec::new(),
        nat.clone(),
        Some(let_expr),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    );
    let proj_info = ConstantInfo::new_with_reducibility(
        Name::from_string("rawProj"),
        Vec::new(),
        Expr::pi(BinderInfo::StrictImplicit, nat.clone(), nat),
        Some(lambda),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    );
    let values = [
        writer
            .write_constant_info(&let_info, DefinitionSafety::Safe)
            .unwrap(),
        writer
            .write_constant_info(&proj_info, DefinitionSafety::Safe)
            .unwrap(),
    ];
    let bytes = writer
        .finish_ordinary_module(&[], &[let_info.name, proj_info.name], &values, &[], &[])
        .unwrap();
    let written = region(&bytes);
    let let_expr = object(&written, object(&written, constant(&written, 0), 0), 1);
    let lambda = object(&written, object(&written, constant(&written, 1), 0), 1);
    assert_eq!(field(&written, let_expr, 4), 0x0000_0001_713f_07fe);
    assert_eq!(field(&written, let_expr, 5), 0);
    let lit = object(&written, let_expr, 2);
    assert_eq!(field(&written, lit, 1), 0x11e9_9612);
    let mpz = object(&written, object(&written, lit, 0), 0);
    assert_eq!(
        written.read_header_at(mpz).unwrap().tag,
        crate::region::tags::MPZ
    );
    assert_eq!(field(&written, mpz, 2), 1);
    assert_eq!(field(&written, mpz, 3), 1);
    assert_eq!(field(&written, lambda, 3), 0x0000_0006_d6b8_b691);
    assert_eq!(field(&written, lambda, 4), 2); // Strict-implicit binder.
    let proj = object(&written, lambda, 2);
    assert_eq!(field(&written, proj, 1), 1); // Projection index 0.
    assert_eq!(field(&written, proj, 3), 0x0000_1005_615c_9cdf);
}

#[test]
fn term_writes_refuse_open_declarations_and_non_lean_binders() {
    let mut writer = writer();
    let info = ConstantInfo::new_with_reducibility(
        Name::from_string("open"),
        Vec::new(),
        Expr::bvar(0),
        None,
        Reducibility::Opaque,
        ConstantKind::Axiom,
    );
    assert!(writer
        .write_constant_info(&info, DefinitionSafety::Safe)
        .is_err());
    let linear = Expr::lam(
        BinderData {
            info: BinderInfo::Default,
            mult: Multiplicity::One,
        },
        Expr::const_str("Nat"),
        Expr::bvar(0),
    );
    assert!(writer.write_expr(&linear).is_err());
    assert!(writer.write_level(&Level::zero()).is_ok());
}
