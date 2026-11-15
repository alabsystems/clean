// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent unchanged flat-serde differential for non-Expr legacy atoms.
use super::*;
use crate::env::aesop::{AesopIndexMode, AesopRuleBuilder, AesopRulePhase};
use crate::env::origin::{ConstantOrigin, OriginTrust};
use crate::env::types::{
    ConstantKind, EnvExtensionEntryData, GrindAttrKind, Reducibility, SimpPriority,
    TransparencyMode,
};
use crate::expr::{BigNat, BinderData, BinderInfo, Literal, MDataValue, Multiplicity};
use crate::inductive::RecursorArgOrder;
use crate::mode::CleanMode;
use crate::quot::QuotKind;
use serde::Serialize;
use std::fmt::Debug;

fn check<T>(value: T, tag: u32)
where
    T: ToWire + FromWire<T::Wire> + Serialize + Debug + PartialEq,
{
    let mut p = Projection::default();
    let wire = value.to_wire(&mut p).unwrap();
    assert!(
        p.nodes.is_empty(),
        "the flat oracle cannot encode DAG child references"
    );
    let mut out = Encoder::new(Encoding::Legacy);
    wire.write(&mut out).unwrap();
    let bytes = out.finish();
    let old = bincode::serde::encode_to_vec(&value, bincode::config::standard()).unwrap();
    assert_eq!(
        bytes, old,
        "owned legacy bytes differ from ordinary serde for {value:?}"
    );
    assert_eq!(
        Decoder::new(&bytes, Encoding::Legacy)
            .unwrap()
            .u32()
            .unwrap(),
        tag
    );
    let mut decoder = Decoder::new(&bytes, Encoding::Legacy).unwrap();
    let restored = <T::Wire as Wire>::read(&mut decoder).unwrap();
    decoder.finish().unwrap();
    assert_eq!(
        T::from_wire(restored, &mut Restoration::new(0).unwrap()).unwrap(),
        value
    );
}

#[test]
fn all_82_non_expression_enum_variants_match_original_flat_wire_shapes() {
    let mut cases = 0;
    macro_rules! one {
        ($value:expr,$tag:expr) => {{
            check($value, $tag);
            cases += 1;
        }};
    }
    for (v, t) in [
        (ConstantKind::Definition, 0),
        (ConstantKind::Theorem, 1),
        (ConstantKind::Opaque, 2),
        (ConstantKind::Axiom, 3),
    ] {
        one!(v, t);
    }
    for (v, t) in [
        (Reducibility::Reducible, 0),
        (Reducibility::Regular(251), 1),
        (Reducibility::Irreducible, 2),
        (Reducibility::Opaque, 3),
    ] {
        one!(v, t);
    }
    one!(EnvExtensionEntryData::Scalar(u64::MAX), 0);
    one!(EnvExtensionEntryData::Object(vec![0, 251, 255]), 1);
    for (v, t) in [
        (TransparencyMode::Reducible, 0),
        (TransparencyMode::Instances, 1),
        (TransparencyMode::Default, 2),
        (TransparencyMode::All, 3),
    ] {
        one!(v, t);
    }
    one!(SimpPriority::Default, 0);
    one!(SimpPriority::Custom(65536), 1);
    for (v, t) in [
        (GrindAttrKind::Infer, 0),
        (GrindAttrKind::EqLhs, 1),
        (GrindAttrKind::Forward, 2),
        (GrindAttrKind::Backward, 3),
        (GrindAttrKind::Cases, 4),
        (GrindAttrKind::Ext, 5),
        (GrindAttrKind::Intro, 6),
        (GrindAttrKind::Unmodeled("unchanged λ payload".into()), 7),
    ] {
        one!(v, t);
    }
    for (v, t) in [
        (OriginTrust::KernelChecked, 0),
        (OriginTrust::OleanUnpinned, 1),
        (OriginTrust::CleanPayloadUnpinned, 2),
    ] {
        one!(v, t);
    }
    one!(
        ConstantOrigin::Kernel {
            trust: OriginTrust::KernelChecked
        },
        0
    );
    one!(
        ConstantOrigin::Olean {
            module: None,
            trust: OriginTrust::OleanUnpinned
        },
        1
    );
    one!(
        ConstantOrigin::CleanPayload {
            module: Some("exact.module".into()),
            trust: OriginTrust::CleanPayloadUnpinned
        },
        2
    );
    for (v, t) in [
        (AesopRulePhase::Safe, 0),
        (AesopRulePhase::Unsafe, 1),
        (AesopRulePhase::Norm, 2),
    ] {
        one!(v, t);
    }
    for (v, t) in [
        (AesopRuleBuilder::Apply, 0),
        (AesopRuleBuilder::Cases, 1),
        (AesopRuleBuilder::Constructors, 2),
        (AesopRuleBuilder::Destruct, 3),
        (AesopRuleBuilder::Forward, 4),
        (AesopRuleBuilder::Simp, 5),
        (AesopRuleBuilder::Tactic, 6),
        (AesopRuleBuilder::Unfold, 7),
    ] {
        one!(v, t);
    }
    for (v, t) in [
        (AesopIndexMode::Target, 0),
        (AesopIndexMode::Hyps, 1),
        (AesopIndexMode::Unindexed, 2),
    ] {
        one!(v, t);
    }
    one!(RecursorArgOrder::MajorAfterMinors, 0);
    one!(RecursorArgOrder::MajorAfterMotive, 1);
    for (v, t) in [
        (QuotKind::Type, 0),
        (QuotKind::Mk, 1),
        (QuotKind::Lift, 2),
        (QuotKind::Ind, 3),
        (QuotKind::Sound, 4),
    ] {
        one!(v, t);
    }
    for (v, t) in [
        (CleanMode::Constructive, 0),
        (CleanMode::Impredicative, 1),
        (CleanMode::Cubical, 2),
        (CleanMode::Directed, 3),
        (CleanMode::Classical, 4),
        (CleanMode::SetTheoretic, 5),
    ] {
        one!(v, t);
    }
    one!(LeanLevelProfile::Lean48, 0);
    one!(LeanLevelProfile::Lean430, 1);
    one!(Name::anon(), 0);
    one!(Name::anon().str("a.b").num(17).str("17"), 1);
    one!(Name::anon().str("a").num(u64::MAX), 2);
    let u = Level::Param(Name::anon().str("u"));
    one!(Level::Zero, 0);
    one!(Level::Succ(u.clone().into()), 1);
    one!(Level::Max(Level::Zero.into(), u.clone().into()), 2);
    one!(
        Level::IMax(Level::Succ(Level::Zero.into()).into(), u.clone().into()),
        3
    );
    one!(u, 4);
    for (v, t) in [
        (BinderInfo::Default, 0),
        (BinderInfo::Implicit, 1),
        (BinderInfo::StrictImplicit, 2),
        (BinderInfo::InstImplicit, 3),
    ] {
        one!(v, t);
    }
    for (v, t) in [
        (Multiplicity::Zero, 0),
        (Multiplicity::One, 1),
        (Multiplicity::Many, 2),
    ] {
        one!(v, t);
    }
    one!(BigNat::Small(u64::MAX), 0);
    one!(BigNat::Big(vec![0, 1, u64::MAX]), 1);
    one!(Literal::Nat(BigNat::Big(vec![0, 1, u64::MAX])), 0);
    one!(Literal::String("\0λ/../exact".into()), 1);
    one!(MDataValue::Bool(true), 0);
    one!(MDataValue::Nat(u64::MAX), 1);
    one!(MDataValue::String("λ".into()), 2);
    one!(MDataValue::Name(Name::anon().num(17).str("17")), 3);
    assert_eq!(cases, 82);
}

#[test]
fn binder_information_and_multiplicity_are_both_retained() {
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        for mult in [Multiplicity::Zero, Multiplicity::One, Multiplicity::Many] {
            let value = BinderData::new(info, mult);
            let mut p = Projection::default();
            let wire = value.to_wire(&mut p).unwrap();
            let mut out = Encoder::new(Encoding::Legacy);
            wire.write(&mut out).unwrap();
            assert_eq!(
                out.finish(),
                bincode::serde::encode_to_vec(value, bincode::config::standard()).unwrap()
            );
        }
    }
}
