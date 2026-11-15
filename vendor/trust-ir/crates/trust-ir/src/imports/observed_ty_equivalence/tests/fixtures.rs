// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset: Some(8),
    }
}
pub(super) fn strukt(id: u32, name: &str, ty: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![field("lane", ty)],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    }
}
pub(super) fn origin(name: &str) -> TypeOrigin {
    TypeOrigin::Clean {
        decl: name.into(),
        env_digest: ProofDigest {
            algorithm: crate::ProofDigestAlgorithm::Sha256,
            bytes: [7; 32],
        },
    }
}
pub(super) fn structure_pair() -> (Module, Ty, Module, Ty) {
    let mut a = Module::new("left");
    let mut b = Module::new("right");
    a.structs.push(strukt(3, "S", Ty::I64));
    b.structs.push(strukt(8, "S", Ty::I64));
    (
        a,
        Ty::Struct(StructId::new(3)),
        b,
        Ty::Struct(StructId::new(8)),
    )
}
pub(super) fn enm(id: u32) -> EnumDef {
    EnumDef::new(
        EnumId::new(id),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::I64],
                field_names: vec!["left".into()],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::Bool],
                field_names: vec![],
            },
        ],
    )
    .with_discriminants(vec![Some(-3), None])
}
pub(super) fn enum_pair() -> (Module, Ty, Module, Ty) {
    let mut a = Module::new("left");
    let mut b = Module::new("right");
    a.enums.push(enm(3));
    b.enums.push(enm(8));
    a.enums[0].layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 32,
        align: 8,
        variant_field_offsets: vec![vec![8, 16], vec![24]],
    });
    b.enums[0].layout = a.enums[0].layout.clone();
    (a, Ty::Enum(EnumId::new(3)), b, Ty::Enum(EnumId::new(8)))
}
pub(super) fn pred_pair(a: Vec<Pred>, pa: u32, b: Vec<Pred>, pb: u32) -> (Module, Ty, Module, Ty) {
    let mut left = Module::new("left");
    let mut right = Module::new("right");
    left.types.push(Ty::I64);
    right.types.extend([Ty::Bool, Ty::I64]);
    left.predicates = a;
    right.predicates = b;
    (
        left,
        Ty::Refine(TyId::new(0), PredId::new(pa)),
        right,
        Ty::Refine(TyId::new(1), PredId::new(pb)),
    )
}
pub(super) fn conflict_pair() -> (Module, Ty, Module, Ty) {
    let (mut a, ta, mut b, tb) = structure_pair();
    a.structs[0].origin = Some(origin(&"source λ".repeat(400)));
    b.structs[0].origin = a.structs[0].origin.clone();
    a.structs[0].name = "left λ".repeat(400);
    b.structs[0].name = "right λ".repeat(400);
    (a, ta, b, tb)
}
pub(super) fn baseline(a: &Module, ta: &Ty, b: &Module, tb: &Ty) -> Observer {
    let mut observer = Observer::default();
    {
        let mut session = ObservedSession::new(options(), &mut observer);
        let answer = ty_equivalence_across_observed(a, ta, b, tb, &mut session, site()).unwrap();
        if let TyEquivalence::OriginConflict(conflict) = answer {
            conflict.retire_observed(&mut session, site()).unwrap();
        }
        assert!(session.first_refusal().is_none());
    }
    observer
}
pub(super) fn assert_state_empty(s: &State<'_>) {
    assert!(
        s.tasks.is_empty()
            && s.active.is_empty()
            && s.conflict.is_none()
            && s.pending_origin.is_none()
    );
    assert!(
        s.pending_left.is_empty()
            && s.pending_right.is_empty()
            && s.discs_a.is_none()
            && s.discs_b.is_none()
    );
    assert_eq!(s.tasks.capacity(), 0);
    assert_eq!(s.active.capacity(), 0);
    assert_eq!(s.pending_left.capacity(), 0);
    assert_eq!(s.pending_right.capacity(), 0);
}
