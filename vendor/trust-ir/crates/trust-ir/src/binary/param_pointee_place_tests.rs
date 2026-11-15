// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roadmap DG-63 (the trust-ir prerequisite of WS5.5):
//! `ClausePlace::ParamPointeeEntry { index }`, the entry-state pointee of a
//! reference parameter, at clause-place tag 10, read-gated on
//! `PARAM_POINTEE_PLACE_FORMAT_VERSION`.

use super::*;
use crate::{Function, SpecInvariant, SpecModule, SpecVar};

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn relabel(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut forged = bytes.to_vec();
    forged[8..12].copy_from_slice(&version.to_le_bytes());
    forged
}

/// `(bvult x_entry #x..10)` with the one binding `x_entry: BitVec(64)` at
/// `place`.
fn clause(place: ClausePlace) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2("(bvult x_entry #x0000000000000010)", "Bool");
    formula.bindings = vec![(
        "x_entry".to_string(),
        ClauseBinding {
            sort: ClauseSort::BitVec(64),
            place,
        },
    )];
    formula
}

/// `bump(x: &u64, p: &mut u64)`: a body-less declaration whose summary
/// `requires` the clause bound at `place`.
fn summary_module(place: ClausePlace) -> Module {
    let mut module = Module::new("param_pointee_codec");
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ref(Box::new(Ty::U64)), Ty::RefMut(Box::new(Ty::U64))],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::declaration(
            FuncId::new(0),
            "bump",
            sig,
            FunctionSummary::new()
                .with_params(vec!["x".to_string(), "p".to_string()])
                .requiring(clause(place)),
        ))
        .expect("Module::try_add_function: test fixture");
    module
}

const POINTEE: ClausePlace = ClausePlace::ParamPointeeEntry { index: 0 };
/// The twin: the same clause at a v41 place, so every difference between the
/// two modules is the place.
const CONTROL: ClausePlace = ClausePlace::Param { index: 0 };

#[test]
fn the_place_round_trips_at_its_version() {
    let module = summary_module(POINTEE);
    let bytes = serialize_module(&module).expect("serialize_module");
    assert_eq!(header_version(&bytes), PARAM_POINTEE_PLACE_FORMAT_VERSION);
    assert_eq!(deserialize_module(&bytes).expect("lossless place"), module);
}

/// Every carrier of a clause binding selects the version: a summary clause,
/// a module obligation's formula, and a spec carrier (which the validator
/// refuses it on, but the codec must still carry losslessly, never drop).
#[test]
fn every_binding_carrier_selects_the_version() {
    let mut obligation = Module::new("param_pointee_obligation");
    obligation.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "entry pointee",
        )
        .with_formula(clause(POINTEE)),
    );
    let mut spec = Module::new("param_pointee_spec");
    let mut machine = SpecModule::design_only("m");
    machine.vars = vec![SpecVar::new("x_entry", "BitVec(64)")];
    machine.invariants = vec![
        SpecInvariant::new("I", "(bvult x_entry #x0000000000000010)").with_typed(clause(POINTEE)),
    ];
    spec.spec_modules.push(machine);
    for module in [summary_module(POINTEE), obligation, spec] {
        let bytes = serialize_module(&module).expect("serialize_module");
        assert_eq!(
            header_version(&bytes),
            PARAM_POINTEE_PLACE_FORMAT_VERSION,
            "{}",
            module.name
        );
        assert_eq!(deserialize_module(&bytes).expect("lossless"), module);
    }
}

/// The exact spelling: tag 10, then the parameter index as a v32. Pinned
/// byte for byte so a renumbering is a failure, not a silent re-encoding.
#[test]
fn the_wire_spelling_is_pinned() {
    let spell = |place: ClausePlace| {
        SealedStringPool::by_replay(|_, bytes| write_clause_place(bytes, &place))
    };
    assert_eq!(
        spell(ClausePlace::ParamPointeeEntry { index: 3 }),
        vec![10, 3]
    );
    assert_eq!(
        spell(ClausePlace::ParamPointeeEntry { index: 300 }),
        vec![10, 0xAC, 0x02]
    );
    // `Param` and `MutParamExit` at the same index keep their own tags: the
    // entry pointee is a third place, never a re-spelling of either.
    assert_eq!(spell(ClausePlace::Param { index: 3 }), vec![0, 3]);
    assert_eq!(spell(ClausePlace::MutParamExit { index: 3 }), vec![2, 3]);
}

/// Tag 10 reads only under a header at or above its version, at EVERY
/// accepted version: below it the reader refuses the byte by name.
#[test]
fn the_tag_is_read_gated_at_every_version() {
    for version in MIN_READ_VERSION..=VERSION {
        let mut reader = Reader::new(&[10, 3]);
        reader.version = version;
        let read = read_clause_place(&mut reader);
        if version >= PARAM_POINTEE_PLACE_FORMAT_VERSION {
            assert_eq!(
                read,
                Ok(ClausePlace::ParamPointeeEntry { index: 3 }),
                "v{version}"
            );
        } else {
            assert_eq!(read, Err(BinaryError::InvalidTag(10)), "v{version}");
        }
    }
    // A whole blob relabelled one version down is refused at the place.
    let bytes = serialize_module(&summary_module(POINTEE)).expect("serialize_module");
    assert_eq!(
        deserialize_module(&relabel(&bytes, PARAM_POINTEE_PLACE_FORMAT_VERSION - 1)),
        Err(BinaryError::InvalidTag(10))
    );
}

/// A module that binds no entry pointee is written exactly as before, at its
/// own minimum version, with the same bytes and digests.
#[test]
fn a_module_without_the_place_keeps_its_bytes_and_digests() {
    let control = summary_module(CONTROL);
    let bytes = serialize_module(&control).expect("serialize_module");
    assert_eq!(header_version(&bytes), CONTRACT_SURFACE_FORMAT_VERSION);
    let back = deserialize_module(&bytes).unwrap();
    assert_eq!(back, control);
    assert_eq!(back.stable_digest(), control.stable_digest());
}

/// The stable digest separates the entry pointee from the parameter itself,
/// and survives a round trip.
#[test]
fn the_digests_separate_the_pointee_from_the_parameter() {
    let pointee = summary_module(POINTEE);
    let control = summary_module(CONTROL);
    assert_ne!(pointee.stable_digest(), control.stable_digest());
    let back = deserialize_module(&serialize_module(&pointee).expect("serialize_module")).unwrap();
    assert_eq!(pointee.stable_digest(), back.stable_digest());
}

/// The obligation content digest (`Module::obligation_digest`) of one row
/// scoped to `bump`, bound at each place in turn: the entry pointee is
/// neither the parameter, nor its exit value, nor another parameter's
/// pointee.
#[cfg(feature = "fmt")]
#[test]
fn the_obligation_digest_separates_the_pointee() {
    let digest = |place| {
        let mut module = summary_module(CONTROL);
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "entry pointee",
            )
            .with_function(FuncId::new(0))
            .with_formula(clause(place)),
        );
        module
            .obligation_digest(ProofId::new(0))
            .expect("one row, one digest")
    };
    assert_ne!(digest(POINTEE), digest(CONTROL));
    assert_ne!(
        digest(POINTEE),
        digest(ClausePlace::MutParamExit { index: 0 })
    );
    assert_ne!(
        digest(POINTEE),
        digest(ClausePlace::ParamPointeeEntry { index: 1 })
    );
}

#[test]
fn v38_projections_refuse_the_place() {
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let options = ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(&summary_module(POINTEE), options).err(),
            Some(BinaryProjectionError::ParamPointeePlaceRequiresV62)
        );
        // The control's v41 summary is refused as the contract surface, not
        // as this place: the refusal names the feature that forbids it.
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(&summary_module(CONTROL), options).err(),
            Some(BinaryProjectionError::ContractSurfaceRequiresV41)
        );
    }
}
