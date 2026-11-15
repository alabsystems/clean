// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IMPORT AUTHENTICATION, layer 1 (`trust_ir::imports`).
//!
//! Every test here is a contrast or a refusal: the format lets each of these
//! forgeries be SPELLED, and the API must name the exact check that refuses
//! it. The verdict is always computed over the dependency module's stable
//! digest under the fixed domain — never over a name.

use std::collections::BTreeSet;

use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofDigest, ProofDigestAlgorithm, ProofEvidence,
    ProofObligation, ProofStatus,
};
use trust_ir::ty::{
    DialectTy, EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FatPtrKind, FieldDef, FuncTy, RecordDef, StructDef, StructRepr, Ty,
};
use trust_ir::value::{EnumId, FuncId, ImportId, PredId, ProofId, RecordId, StructId, TyId};
use trust_ir::{
    Block, CallingConv, Endianness, ExternRef, ExternRefSite, Function, FunctionSummary,
    ImportVerificationError, Linkage, MODULE_IDENTITY_DOMAIN, Module, ModuleImport, ParamAttrs,
    Pred, Producer, TargetInfo, signatures_compatible, ty_structurally_eq_across,
};

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

fn target(pointer_size: u32) -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn i64_to_i64(module: &mut Module) -> trust_ir::value::FuncTyId {
    module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture")
}

fn obligation(
    id: u32,
    kind: ObligationKind,
    status: ProofStatus,
    function: Option<u32>,
) -> ProofObligation {
    let mut obligation = ProofObligation::new(ProofId::new(id), kind, status, "o");
    if let Some(function) = function {
        obligation = obligation.with_function(FuncId::new(function));
    }
    obligation
}

/// `fn(i64) -> i64` with a real body: `bb0(%0: i64): return %0`. R4 requires
/// the far side to be a DEFINITION, so every fixture a positive test resolves
/// against must carry one — a body-less declaration proves nothing about a
/// body it does not have.
fn defined(id: u32, name: &str, ft: trust_ir::value::FuncTyId) -> Function {
    let entry = trust_ir::value::BlockId(0);
    let mut function = Function::new(FuncId::new(id), name, ft, entry);
    let mut block = Block::new(entry);
    block.params.push((trust_ir::value::ValueId(0), Ty::I64));
    block.body.push(trust_ir::node::InstrNode::new(
        trust_ir::inst::Inst::Return {
            values: vec![trust_ir::value::ValueId(0)],
        },
    ));
    function.blocks.push(block);
    function.producer = Some(Producer::TRust);
    function
}

/// The dependency: `f: fn(i64) -> i64` (id 0, producer tRust) and `g` (id 1),
/// both DEFINITIONS, with a spread of obligations that exercise every R7 arm.
fn dependency() -> Module {
    let mut m = Module::new("dep");
    m.target_info = Some(target(8));
    let ft = i64_to_i64(&mut m);
    let f = defined(0, "f", ft);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let g = defined(1, "g", ft);
    m.try_add_function(g)
        .expect("Module::try_add_function: test fixture");
    m.proof_obligations.extend([
        obligation(
            3,
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            Some(0),
        ),
        obligation(
            4,
            ObligationKind::MemorySafety,
            ProofStatus::Discharged,
            Some(0),
        ),
        obligation(
            5,
            ObligationKind::Custom {
                namespace: "trust.concurrency".into(),
                name: "send".into(),
            },
            ProofStatus::Discharged,
            Some(0),
        ),
        obligation(
            6,
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            Some(0),
        ),
        obligation(
            7,
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            None,
        ),
        obligation(
            8,
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            Some(1),
        ),
        obligation(
            9,
            ObligationKind::Postcondition,
            ProofStatus::Failed,
            Some(0),
        ),
        obligation(
            10,
            ObligationKind::Postcondition,
            ProofStatus::Trusted,
            Some(0),
        ),
    ]);
    m
}

/// The importer: declares `f` (id 0, producer tRust) and records `dep`.
fn importer(dep: &Module) -> (Module, ImportId) {
    let mut m = Module::new("root");
    m.target_info = Some(target(8));
    let id = m
        .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let ft = i64_to_i64(&mut m);
    let mut f = Function::declaration(FuncId::new(0), "f", ft, FunctionSummary::new());
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    (m, id)
}

fn reference(id: ImportId, obligation: u32) -> ExternRef {
    ExternRef::new(id, "f").relying_on(ProofId::new(obligation))
}

// ---------------------------------------------------------------------------
// verify_import: C1–C6
// ---------------------------------------------------------------------------

#[test]
fn a_binary_round_tripped_candidate_authenticates() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let loaded =
        deserialize_module(&serialize_module(&dep).expect("serialize_module: test fixture"))
            .expect("round trip");
    let verified = root
        .verify_import(id, &loaded)
        .expect("the loaded artifact IS the recorded module");
    assert_eq!(verified.id(), id);
    assert_eq!(verified.digest(), dep.stable_digest());
    assert_eq!(verified.digest().algorithm, ProofDigestAlgorithm::Sha256);
    assert_eq!(verified.import().name, "dep");
    assert!(std::ptr::eq(verified.module(), &loaded));
    // The identity IS the stable digest under the row's scheme (V3, the
    // portable identity, for a row minted by `ModuleImport::new`), not a name.
    assert_eq!(verified.import().scheme, trust_ir::IdentityScheme::V3);
    assert_eq!(MODULE_IDENTITY_DOMAIN, "trust_ir.module.v3");
}

#[test]
fn one_obligation_status_flip_is_a_digest_mismatch() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let mut rebuilt = dep.clone();
    rebuilt.proof_obligations[0].status = ProofStatus::Failed;
    let error = root.verify_import(id, &rebuilt).unwrap_err();
    assert!(
        matches!(
            &error,
            ImportVerificationError::DigestMismatch { import: 0, recorded, actual }
                if *recorded == dep.stable_digest() && *actual == rebuilt.stable_digest()
        ),
        "a rebuilt dependency with the same name is a different module: {error}"
    );
}

#[test]
fn a_relabelled_artifact_is_a_name_mismatch_after_the_digest_matched() {
    let dep = dependency();
    let mut root = Module::new("root");
    root.target_info = Some(target(8));
    let id = root
        .intern_import(
            ModuleImport::new("other", dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let error = root.verify_import(id, &dep).unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::NameMismatch {
            import: 0,
            recorded: "other".into(),
            actual: "dep".into(),
        }
    );
}

#[test]
fn a_dangling_import_id_is_unresolved() {
    let dep = dependency();
    let (root, _) = importer(&dep);
    assert_eq!(
        root.verify_import(ImportId::new(9), &dep).unwrap_err(),
        ImportVerificationError::UnresolvedImport { import: 9 }
    );
}

#[test]
fn a_checksum_digest_never_identifies_a_module() {
    let dep = dependency();
    let mut root = Module::new("root");
    root.target_info = Some(target(8));
    let checksum = ProofDigest::trust_ir_stable("trust_ir.test", b"dep");
    let id = root
        .intern_import(ModuleImport::new("dep", checksum).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    assert_eq!(
        root.verify_import(id, &dep).unwrap_err(),
        ImportVerificationError::UnsupportedDigestAlgorithm {
            import: 0,
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        }
    );
}

#[test]
fn an_unrecorded_import_producer_is_refused_not_wildcarded() {
    let dep = dependency();
    let mut root = Module::new("root");
    root.target_info = Some(target(8));
    let id = root
        .intern_import(ModuleImport::new("dep", dep.stable_digest()))
        .expect("Module::intern_import: test fixture");
    assert_eq!(
        root.verify_import(id, &dep).unwrap_err(),
        ImportVerificationError::ProducerUnrecorded {
            import: 0,
            side: "import",
        }
    );
}

#[test]
fn a_pointer_width_disagreement_is_a_target_mismatch() {
    let mut dep = dependency();
    dep.target_info = Some(target(4));
    let (root, id) = importer(&dep);
    let error = root.verify_import(id, &dep).unwrap_err();
    assert!(
        matches!(
            error,
            ImportVerificationError::TargetMismatch { import: 0, .. }
        ),
        "a Usize proof must not cross pointer widths: {error}"
    );
}

#[test]
fn an_absent_target_on_either_side_or_both_is_a_target_mismatch() {
    let mut dep = dependency();
    dep.target_info = None;
    let (root, id) = importer(&dep);
    let error = root.verify_import(id, &dep).unwrap_err();
    assert!(
        matches!(error, ImportVerificationError::TargetMismatch { .. }),
        "{error}"
    );

    let dep = dependency();
    let (mut root2, id2) = importer(&dep);
    root2.target_info = None;
    let error = root2.verify_import(id2, &dep).unwrap_err();
    assert!(
        matches!(error, ImportVerificationError::TargetMismatch { .. }),
        "{error}"
    );

    let mut dep = dependency();
    dep.target_info = None;
    let mut root3 = Module::new("root");
    let id3 = root3
        .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let error = root3.verify_import(id3, &dep).unwrap_err();
    assert!(
        matches!(error, ImportVerificationError::TargetMismatch { .. }),
        "two absent targets are not agreement: {error}"
    );
}

// ---------------------------------------------------------------------------
// resolve_extern_ref: R1–R7
// ---------------------------------------------------------------------------

fn resolve(
    root: &Module,
    dep: &Module,
    id: ImportId,
    reference: &ExternRef,
    site: ExternRefSite,
) -> Result<(), ImportVerificationError> {
    let verified = root.verify_import(id, dep).expect("edge authenticates");
    root.resolve_extern_ref(reference, FuncId::new(0), site, &verified)
        .map(|_| ())
}

#[test]
fn a_backed_by_citation_of_a_certified_postcondition_resolves() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let verified = root.verify_import(id, &dep).unwrap();
    let resolved = root
        .resolve_extern_ref(
            &reference(id, 3),
            FuncId::new(0),
            ExternRefSite::SummaryBackedBy,
            &verified,
        )
        .expect("scoped, certified Postcondition");
    assert_eq!(resolved.local.name, "f");
    assert_eq!(resolved.far.id, FuncId::new(0));
    assert_eq!(resolved.obligation.map(|o| o.id), Some(ProofId::new(3)));
    // An inheritance may rely on MemorySafety; a summary may not.
    assert!(
        root.resolve_extern_ref(
            &reference(id, 4),
            FuncId::new(0),
            ExternRefSite::InheritedFromCallee,
            &verified,
        )
        .is_ok()
    );
}

#[test]
fn a_verified_import_cannot_be_replayed_for_another_importer() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let verified = root
        .verify_import(id, &dep)
        .expect("original import authenticates");
    let reference = reference(id, 3);

    let twin = root.clone();
    assert_eq!(twin.import(id), root.import(id));
    assert!(
        root.resolve_extern_ref(
            &reference,
            FuncId::new(0),
            ExternRefSite::SummaryBackedBy,
            &verified,
        )
        .is_ok()
    );
    assert_eq!(
        twin.resolve_extern_ref(
            &reference,
            FuncId::new(0),
            ExternRefSite::SummaryBackedBy,
            &verified,
        )
        .unwrap_err(),
        ImportVerificationError::VerifiedImportForOtherModule { import: id.index() }
    );
    let twin_verified = twin
        .verify_import(id, &dep)
        .expect("twin re-earns its own import");
    assert!(
        twin.resolve_extern_ref(
            &reference,
            FuncId::new(0),
            ExternRefSite::SummaryBackedBy,
            &twin_verified,
        )
        .is_ok()
    );

    let mut other_target = root.clone();
    other_target.target_info = Some(target(4));
    assert_eq!(other_target.import(id), root.import(id));
    assert!(matches!(
        other_target.verify_import(id, &dep),
        Err(ImportVerificationError::TargetMismatch { .. })
    ));
    assert_eq!(
        other_target
            .resolve_extern_ref(
                &reference,
                FuncId::new(0),
                ExternRefSite::SummaryBackedBy,
                &verified,
            )
            .unwrap_err(),
        ImportVerificationError::VerifiedImportForOtherModule { import: id.index() }
    );
}

#[test]
fn a_reference_into_another_import_is_an_id_mismatch() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let verified = root.verify_import(id, &dep).unwrap();
    let error = root
        .resolve_extern_ref(
            &ExternRef::new(ImportId::new(1), "f"),
            FuncId::new(0),
            ExternRefSite::SummaryBackedBy,
            &verified,
        )
        .unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::ImportIdMismatch {
            expected: 0,
            actual: 1
        }
    );

    // A `VerifiedImport` minted by ANOTHER importer (same id, different
    // record) cannot be replayed here either.
    let mut other = Module::new("other_root");
    other.target_info = Some(target(8));
    let other_id = other
        .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::Clean))
        .expect("Module::intern_import: test fixture");
    let foreign = other.verify_import(other_id, &dep).unwrap();
    let error = root
        .resolve_extern_ref(
            &ExternRef::new(id, "f"),
            FuncId::new(0),
            ExternRefSite::SummaryBackedBy,
            &foreign,
        )
        .unwrap_err();
    assert!(
        matches!(error, ImportVerificationError::ImportIdMismatch { .. }),
        "{error}"
    );
}

#[test]
fn a_local_site_with_a_body_is_refused() {
    let dep = dependency();
    let (mut root, id) = importer(&dep);
    root.functions[0]
        .blocks
        .push(Block::new(trust_ir::value::BlockId(0)));
    let error = resolve(
        &root,
        &dep,
        id,
        &ExternRef::new(id, "f"),
        ExternRefSite::SummaryBackedBy,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::LocalSiteHasBody { function: 0 }
    );
}

#[test]
fn a_local_declaration_whose_symbol_differs_is_refused() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let error = resolve(
        &root,
        &dep,
        id,
        &ExternRef::new(id, "g"),
        ExternRefSite::SummaryBackedBy,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::LinkSymbolMismatch {
            function: 0,
            local: "f".into(),
            symbol: "g".into(),
        }
    );
}

#[test]
fn a_renamed_far_symbol_is_unresolved() {
    let mut dep = dependency();
    dep.functions[0].name = "f_v2".into();
    let (root, id) = importer(&dep);
    let error = resolve(
        &root,
        &dep,
        id,
        &ExternRef::new(id, "f"),
        ExternRefSite::SummaryBackedBy,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::SymbolUnresolved { symbol: "f".into() }
    );
}

#[test]
fn a_duplicated_far_symbol_is_ambiguous() {
    let mut dep = dependency();
    dep.functions[1].name = "f".into();
    let (root, id) = importer(&dep);
    let error = resolve(
        &root,
        &dep,
        id,
        &ExternRef::new(id, "f"),
        ExternRefSite::SummaryBackedBy,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::SymbolAmbiguous {
            symbol: "f".into(),
            count: 2
        }
    );
}

#[test]
fn an_unexported_far_symbol_is_refused() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        let mut dep = dependency();
        dep.functions[0].linkage = linkage;
        let (root, id) = importer(&dep);
        let error = resolve(
            &root,
            &dep,
            id,
            &ExternRef::new(id, "f"),
            ExternRefSite::SummaryBackedBy,
        )
        .unwrap_err();
        assert_eq!(
            error,
            ImportVerificationError::SymbolNotExported {
                symbol: "f".into(),
                linkage
            }
        );
    }
}

#[test]
fn a_far_producer_that_is_unrecorded_or_differs_is_refused() {
    let mut dep = dependency();
    dep.functions[0].producer = None;
    let (root, id) = importer(&dep);
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &ExternRef::new(id, "f"),
            ExternRefSite::SummaryBackedBy
        )
        .unwrap_err(),
        ImportVerificationError::ProducerUnrecorded {
            import: 0,
            side: "function"
        }
    );

    let mut dep = dependency();
    dep.functions[0].producer = Some(Producer::Clean);
    let (root, id) = importer(&dep);
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &ExternRef::new(id, "f"),
            ExternRefSite::SummaryBackedBy
        )
        .unwrap_err(),
        ImportVerificationError::ProducerMismatch {
            symbol: "f".into(),
            recorded: Producer::TRust,
            actual: Producer::Clean,
        }
    );
}

#[test]
fn every_signature_axis_is_checked() {
    fn expect_signature(dep: Module, needle: &str) {
        let (root, id) = importer(&dep);
        let error = resolve(
            &root,
            &dep,
            id,
            &ExternRef::new(id, "f"),
            ExternRefSite::SummaryBackedBy,
        )
        .unwrap_err();
        match &error {
            ImportVerificationError::SignatureMismatch { symbol, detail } => {
                assert_eq!(symbol, "f");
                assert!(detail.contains(needle), "expected {needle:?} in {detail:?}");
            }
            other => panic!("expected SignatureMismatch, got {other:?}"),
        }
    }

    let mut dep = dependency();
    dep.functions[0].calling_conv = CallingConv::Rust;
    expect_signature(dep, "calling convention");

    let mut dep = dependency();
    let two = dep
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    dep.functions[0].ty = two;
    expect_signature(dep, "parameter arity");

    let mut dep = dependency();
    let vararg = dep
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    dep.functions[0].ty = vararg;
    expect_signature(dep, "is_vararg");

    let mut dep = dependency();
    let narrower = dep
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    dep.functions[0].ty = narrower;
    expect_signature(dep, "parameter 0 type");

    let mut dep = dependency();
    dep.functions[0].attrs.params = vec![ParamAttrs {
        sret: true,
        ..ParamAttrs::default()
    }];
    expect_signature(dep, "sret");

    // v45 (WS3.11): the per-slot ABI facts are byte-level ABI like `byval`.
    // An UNRECORDED fact on the local side against a recorded one on the far
    // side is a disagreement, never a wildcard — on a parameter and on the
    // return slot alike.
    let mut dep = dependency();
    dep.functions[0].attrs.params = vec![ParamAttrs {
        ext: trust_ir::ArgExt::SignExt,
        ..ParamAttrs::default()
    }];
    expect_signature(dep, "parameter 0 ext");

    let mut dep = dependency();
    dep.functions[0].attrs.params = vec![ParamAttrs {
        pass: Some(trust_ir::PassMode::Direct),
        ..ParamAttrs::default()
    }];
    expect_signature(dep, "parameter 0 pass mode");

    let mut dep = dependency();
    dep.functions[0].attrs.ret = ParamAttrs {
        ext: trust_ir::ArgExt::ZeroExt,
        ..ParamAttrs::default()
    };
    expect_signature(dep, "return slot ext");

    let mut dep = dependency();
    dep.functions[0].attrs.ret = ParamAttrs {
        pass: Some(trust_ir::PassMode::Direct),
        ..ParamAttrs::default()
    };
    expect_signature(dep, "return slot pass mode");
}

#[test]
fn a_missing_trailing_param_attrs_row_reads_as_default() {
    let mut dep = dependency();
    dep.functions[0].attrs.params = vec![ParamAttrs::default()];
    let (root, _) = importer(&dep);
    assert!(root.functions[0].attrs.params.is_empty());
    assert_eq!(
        signatures_compatible(&root, &root.functions[0], &dep, &dep.functions[0]),
        Ok(())
    );
}

#[test]
fn every_obligation_axis_is_checked() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let site = ExternRefSite::SummaryBackedBy;

    assert_eq!(
        resolve(&root, &dep, id, &reference(id, 99), site).unwrap_err(),
        ImportVerificationError::ObligationUnresolved {
            symbol: "f".into(),
            obligation: 99
        }
    );
    // A renumbered ProofId lands on a different obligation — or none.
    assert_eq!(
        resolve(&root, &dep, id, &reference(id, 7), site).unwrap_err(),
        ImportVerificationError::ObligationScopeMismatch {
            obligation: 7,
            expected: 0,
            actual: None
        }
    );
    assert_eq!(
        resolve(&root, &dep, id, &reference(id, 8), site).unwrap_err(),
        ImportVerificationError::ObligationScopeMismatch {
            obligation: 8,
            expected: 0,
            actual: Some(1)
        }
    );
    for (obligation, status) in [
        (6, ProofStatus::Pending),
        (9, ProofStatus::Failed),
        (10, ProofStatus::Trusted),
    ] {
        assert_eq!(
            resolve(&root, &dep, id, &reference(id, obligation), site).unwrap_err(),
            ImportVerificationError::ObligationNotDischarged { obligation, status }
        );
    }
    assert_eq!(
        resolve(&root, &dep, id, &reference(id, 4), site).unwrap_err(),
        ImportVerificationError::ObligationKindInadmissible {
            obligation: 4,
            site,
            kind: "memory_safety".into(),
        }
    );
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 5),
            ExternRefSite::InheritedFromCallee
        )
        .unwrap_err(),
        ImportVerificationError::ObligationKindInadmissible {
            obligation: 5,
            site: ExternRefSite::InheritedFromCallee,
            kind: "custom:trust.concurrency/send".into(),
        }
    );
}

// ---------------------------------------------------------------------------
// ty_structurally_eq_across
// ---------------------------------------------------------------------------

fn point(id: u32, name: &str) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![
            FieldDef {
                name: "x".into(),
                ty: Ty::I64,
                offset: Some(0),
            },
            FieldDef {
                name: "y".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    }
}

#[test]
fn the_same_struct_at_different_ids_is_equal_and_a_different_one_is_not() {
    let mut a = Module::new("a");
    a.add_struct(point(0, "Point"));
    let mut b = Module::new("b");
    b.add_struct(point(0, "Other"));
    b.add_struct(point(1, "Point"));
    assert!(ty_structurally_eq_across(
        &a,
        &Ty::Struct(StructId::new(0)),
        &b,
        &Ty::Struct(StructId::new(1))
    ));
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::Struct(StructId::new(0)),
        &b,
        &Ty::Struct(StructId::new(0))
    ));
    // repr / layout participate.
    let mut c = Module::new("c");
    c.add_struct(point(0, "Point").with_repr(StructRepr::Rust));
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::Struct(StructId::new(0)),
        &c,
        &Ty::Struct(StructId::new(0))
    ));
}

fn option_like(id: u32, field_names: bool) -> EnumDef {
    let mut some = EnumVariant {
        name: "Some".into(),
        fields: vec![Ty::I64],
        field_names: vec![],
    };
    if field_names {
        some.field_names = vec!["value".into()];
    }
    EnumDef::new(
        EnumId::new(id),
        "Opt",
        vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: vec![],
            },
            some,
        ],
    )
}

#[test]
fn enums_differing_only_in_field_names_are_equal_but_layout_repr_and_discriminants_count() {
    let mut a = Module::new("a");
    a.add_enum(option_like(0, false));
    let mut b = Module::new("b");
    b.add_enum(option_like(0, true));
    let e0 = Ty::Enum(EnumId::new(0));
    assert!(ty_structurally_eq_across(&a, &e0, &b, &e0));

    let mut with_layout = Module::new("l");
    let mut def = option_like(0, false);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![], vec![8]],
    });
    with_layout.add_enum(def);
    assert!(!ty_structurally_eq_across(&a, &e0, &with_layout, &e0));

    let mut with_repr = Module::new("r");
    with_repr.add_enum(option_like(0, false).with_repr(EnumTagRepr::U32));
    assert!(!ty_structurally_eq_across(&a, &e0, &with_repr, &e0));

    let mut with_discs = Module::new("d");
    with_discs.add_enum(option_like(0, false).with_discriminants(vec![Some(5), Some(6)]));
    assert!(!ty_structurally_eq_across(&a, &e0, &with_discs, &e0));

    // Spelling the implicit default explicitly IS the same enum.
    let mut explicit = Module::new("x");
    explicit.add_enum(option_like(0, false).with_discriminants(vec![Some(0), Some(1)]));
    assert!(ty_structurally_eq_across(&a, &e0, &explicit, &e0));
}

#[test]
fn a_self_referential_struct_terminates() {
    fn node(id: u32) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: "Node".into(),
            fields: vec![FieldDef {
                name: "next".into(),
                ty: Ty::PtrMut(Box::new(Ty::Struct(StructId::new(id)))),
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        }
    }
    let mut a = Module::new("a");
    a.add_struct(node(0));
    let mut b = Module::new("b");
    b.add_struct(point(0, "pad"));
    b.add_struct(node(1));
    assert!(ty_structurally_eq_across(
        &a,
        &Ty::Struct(StructId::new(0)),
        &b,
        &Ty::Struct(StructId::new(1))
    ));

    // ... and through the `types` table too.
    let mut c = Module::new("c");
    let slot = c
        .add_type(Ty::Unit)
        .expect("Module::add_type: test fixture");
    c.types[slot.as_usize()] = Ty::Array(slot, 1);
    let mut d = Module::new("d");
    d.add_type(Ty::Bool)
        .expect("Module::add_type: test fixture");
    let slot_d = d
        .add_type(Ty::Unit)
        .expect("Module::add_type: test fixture");
    d.types[slot_d.as_usize()] = Ty::Array(slot_d, 1);
    assert!(ty_structurally_eq_across(
        &c,
        &Ty::Array(slot, 1),
        &d,
        &Ty::Array(slot_d, 1)
    ));
}

#[test]
fn dialect_types_are_nominal() {
    let a = Module::new("a");
    let b = Module::new("b");
    let nat = Ty::Dialect(Box::new(DialectTy::new("clean", "Nat", 1)));
    assert!(!ty_structurally_eq_across(&a, &Ty::Ptr, &b, &nat));
    assert!(!ty_structurally_eq_across(&a, &nat, &b, &Ty::Ptr));
    assert!(ty_structurally_eq_across(&a, &nat, &b, &nat.clone()));
    assert!(!ty_structurally_eq_across(
        &a,
        &nat,
        &b,
        &Ty::Dialect(Box::new(DialectTy::new("clean", "Nat", 2)))
    ));
    assert!(!ty_structurally_eq_across(
        &a,
        &nat,
        &b,
        &Ty::Dialect(Box::new(DialectTy::new("trust", "Nat", 1)))
    ));
    assert!(!ty_structurally_eq_across(&a, &Ty::Error, &b, &Ty::Error));
}

/// `FatPtrKind::TraitObject` is compared by EXACT `trait_id`, so equal ids
/// AGREE across the crate boundary. The comparator's rustdoc used to assert
/// the opposite — that the arm "fails CLOSED across crates" because `trait_id`
/// was "a producer-local number with no nominal identity yet" — while the code
/// said `ta == tb` and `ty::stable_trait_object_id` had already ratified the id
/// as a content-derived identity. This pins what the arm actually does, in both
/// directions and in a signature position, so the contract and the code cannot
/// drift apart again.
#[test]
fn trait_object_identity_is_exact_trait_id_agreement_across_modules() {
    let a = Module::new("importer");
    let b = Module::new("dependency");
    let dyn_ty = |id: u32| Ty::FatPtr(FatPtrKind::TraitObject { trait_id: id });

    // Equal ids AGREE across two unrelated modules. Measured for the id a
    // positional numbering scheme would hand out first, and for two real
    // mints.
    for id in [
        0,
        1,
        trust_ir::ty::stable_trait_object_id("core::fmt::Display"),
        trust_ir::ty::stable_trait_object_id("core::fmt::Debug"),
    ] {
        assert!(
            ty_structurally_eq_across(&a, &dyn_ty(id), &b, &dyn_ty(id)),
            "trait_id {id} must compare EQUAL across modules"
        );
        // And inside a reference, which is the position a signature uses.
        assert!(ty_structurally_eq_across(
            &a,
            &Ty::Ref(Box::new(dyn_ty(id))),
            &b,
            &Ty::Ref(Box::new(dyn_ty(id)))
        ));
    }

    // Distinct ids disagree, and the kind is nominal against every sibling
    // fat-pointer kind and against a thin pointer.
    let display = trust_ir::ty::stable_trait_object_id("core::fmt::Display");
    let debug = trust_ir::ty::stable_trait_object_id("core::fmt::Debug");
    assert_ne!(display, debug);
    assert!(!ty_structurally_eq_across(
        &a,
        &dyn_ty(display),
        &b,
        &dyn_ty(debug)
    ));
    for other in [
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::FatPtr(FatPtrKind::ContainerLen),
        Ty::FatPtr(FatPtrKind::ContainerVtable),
    ] {
        assert!(!ty_structurally_eq_across(&a, &dyn_ty(display), &b, &other));
        assert!(!ty_structurally_eq_across(&a, &other, &b, &dyn_ty(display)));
    }

    // The consequence the rustdoc's trusted-assumption paragraph now names: a
    // producer that numbers trait objects POSITIONALLY rather than minting
    // them makes two different trait objects agree, and R6's signature check
    // is built on this comparator.
    let mut importer = Module::new("importer");
    let local_sig = importer
        .add_func_type(FuncTy {
            params: vec![Ty::Ref(Box::new(dyn_ty(0)))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut dependency = Module::new("dependency");
    let far_sig = dependency
        .add_func_type(FuncTy {
            params: vec![Ty::Ref(Box::new(dyn_ty(0)))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert!(ty_structurally_eq_across(
        &importer,
        &Ty::Func(local_sig),
        &dependency,
        &Ty::Func(far_sig)
    ));
    // Had both sides minted from their real def paths, the same two
    // declarations would NOT agree — which is the whole content of the
    // producer obligation.
    let mut minted = Module::new("dependency");
    let minted_sig = minted
        .add_func_type(FuncTy {
            params: vec![Ty::Ref(Box::new(dyn_ty(debug)))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut minted_importer = Module::new("importer");
    let minted_local = minted_importer
        .add_func_type(FuncTy {
            params: vec![Ty::Ref(Box::new(dyn_ty(display)))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert!(!ty_structurally_eq_across(
        &minted_importer,
        &Ty::Func(minted_local),
        &minted,
        &Ty::Func(minted_sig)
    ));
}

#[test]
fn a_refinement_with_the_same_predicate_at_a_different_pred_id_is_equal() {
    let mut a = Module::new("a");
    let base_a = a.add_type(Ty::I64).expect("Module::add_type: test fixture");
    let pred_a = a
        .intern_pred(Pred::Interval { lo: 0, hi: 10 })
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    let mut b = Module::new("b");
    b.add_type(Ty::Bool)
        .expect("Module::add_type: test fixture");
    let base_b = b.add_type(Ty::I64).expect("Module::add_type: test fixture");
    b.intern_pred(Pred::NonZero)
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    let pred_b = b
        .intern_pred(Pred::Interval { lo: 0, hi: 10 })
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    assert_eq!(pred_a, PredId::new(0));
    assert_eq!(pred_b, PredId::new(1));
    assert!(ty_structurally_eq_across(
        &a,
        &Ty::Refine(base_a, pred_a),
        &b,
        &Ty::Refine(base_b, pred_b)
    ));
    let pred_c = b
        .intern_pred(Pred::Interval { lo: 0, hi: 11 })
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::Refine(base_a, pred_a),
        &b,
        &Ty::Refine(base_b, pred_c)
    ));
    // A dangling id on either side is `false`, never "unknown therefore equal".
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::Refine(TyId::new(7), pred_a),
        &b,
        &Ty::Refine(base_b, pred_b)
    ));
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::Sequence(TyId::new(7)),
        &b,
        &Ty::Sequence(base_b)
    ));
}

#[test]
fn records_fat_pointers_and_trait_objects() {
    let mut a = Module::new("a");
    a.add_record(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![FieldDef {
            name: "k".into(),
            ty: Ty::Bool,
            offset: None,
        }],
    });
    let mut b = Module::new("b");
    b.add_record(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![FieldDef {
            name: "k".into(),
            ty: Ty::Bool,
            offset: None,
        }],
    });
    assert!(ty_structurally_eq_across(
        &a,
        &Ty::Record(RecordId::new(0)),
        &b,
        &Ty::Record(RecordId::new(0))
    ));
    assert!(ty_structurally_eq_across(
        &a,
        &Ty::FatPtr(FatPtrKind::Str),
        &b,
        &Ty::FatPtr(FatPtrKind::Str)
    ));
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::FatPtr(FatPtrKind::Str),
        &b,
        &Ty::FatPtr(FatPtrKind::ContainerLen)
    ));
    // A producer-local trait id has no nominal identity: exact or refused.
    assert!(ty_structurally_eq_across(
        &a,
        &Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 3 }),
        &b,
        &Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 3 })
    ));
    assert!(!ty_structurally_eq_across(
        &a,
        &Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 3 }),
        &b,
        &Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 4 })
    ));
}

#[test]
fn a_bare_far_re_declaration_cannot_back_a_cross_crate_claim() {
    // R4, the DEFINITION clause. Before it, R3 picked any far function
    // carrying the symbol and R4 only refused `Internal`/`Private` linkage,
    // so a dependency that merely RE-DECLARED `f` — one `External` bodyless
    // row plus a `Certified` obligation scoped to it — satisfied every check
    // while proving nothing: there is no body for the obligation to be about
    // and no further module named that has one. (Measured: with the clause
    // removed this returns `Ok(())`.)
    let mut dep = dependency();
    // Strip `f`'s body, keeping its `External` linkage, producer, signature
    // and its `Certified` Postcondition #3 — every other rule still passes.
    dep.functions[0].blocks.clear();
    assert!(dep.functions[0].is_declaration());
    assert_eq!(dep.functions[0].linkage, Linkage::External);
    assert!(dep.functions[0].summary.is_none());

    let (root, id) = importer(&dep);
    for site in [
        ExternRefSite::SummaryBackedBy,
        ExternRefSite::InheritedFromCallee,
    ] {
        assert_eq!(
            resolve(&root, &dep, id, &reference(id, 3), site),
            Err(ImportVerificationError::FarSiteIsUnbackedDeclaration { symbol: "f".into() }),
            "a bare body-less far `f` must not authenticate at {site:?}"
        );
    }

    // The contrast: the SAME module with the body restored resolves. The
    // refusal is about the missing body, not about anything else in the shape.
    let dep = dependency();
    let (root, id) = importer(&dep);
    assert!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::SummaryBackedBy
        )
        .is_ok()
    );
}

#[test]
fn a_far_declaration_that_records_a_backing_is_the_ratified_transitive_shape() {
    // R4 admits a body-less far function that HANDS THE CLAIM ONWARDS, in
    // either recorded spelling. This is the shape `validate_linked_module`'s
    // chain tests rely on, so the rule above must not refuse it: the citation
    // names the module where the proof lives, and the closure walk follows it.
    // Only a declaration recording NEITHER is a bare re-declaration.
    let further = ExternRef::new(ImportId::new(0), "f").relying_on(ProofId::new(0));

    // (a) the summary's `backed_by`.
    let mut dep = dependency();
    dep.functions[0].blocks.clear();
    dep.functions[0].summary = Some(FunctionSummary::new().backed_by(further.clone()));
    let (root, id) = importer(&dep);
    assert!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::SummaryBackedBy
        )
        .is_ok(),
        "a far declaration citing another module with `backed_by` is admitted"
    );

    // (b) an `InheritedFromCallee { external: Some }` certificate naming it.
    let mut dep = dependency();
    dep.functions[0].blocks.clear();
    dep.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(3),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(3),
            external: Some(further),
        },
        assurance: None,
    });
    let (root, id) = importer(&dep);
    assert!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::InheritedFromCallee
        )
        .is_ok(),
        "a far declaration whose obligation is an inheritance is admitted"
    );

    // (c) NEITHER — and the same module is refused. `backed_by: None` with no
    // certificate is NOT RECORDED, never a wildcard.
    let mut dep = dependency();
    dep.functions[0].blocks.clear();
    dep.functions[0].summary = Some(FunctionSummary::new());
    let (root, id) = importer(&dep);
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::SummaryBackedBy
        ),
        Err(ImportVerificationError::FarSiteIsUnbackedDeclaration { symbol: "f".into() })
    );
}

// ---------------------------------------------------------------------------
// WS8.14 (F-126, `core-arch-0916-b/18-fact-link-bound`): an interposable site
// on either end of the edge cannot carry a cross-crate proof
// ---------------------------------------------------------------------------

const BOTH_SITES: [ExternRefSite; 2] = [
    ExternRefSite::SummaryBackedBy,
    ExternRefSite::InheritedFromCallee,
];

#[test]
fn an_external_far_definition_still_resolves_at_both_sites() {
    let dep = dependency();
    assert_eq!(dep.functions[0].linkage, Linkage::External);
    let (root, id) = importer(&dep);
    assert_eq!(root.functions[0].linkage, Linkage::External);
    for site in BOTH_SITES {
        assert_eq!(resolve(&root, &dep, id, &reference(id, 3), site), Ok(()));
    }
}

#[test]
fn an_interposable_far_definition_cannot_back_a_cross_crate_claim() {
    for linkage in [Linkage::ExternalWeak, Linkage::Weak, Linkage::LinkOnce] {
        let mut dep = dependency();
        dep.functions[0].linkage = linkage;
        // The far `f` keeps its body: the refusal is about the LINKER's
        // freedom to bind another definition, not a missing body.
        assert!(!dep.functions[0].is_declaration());
        let (root, id) = importer(&dep);
        for site in BOTH_SITES {
            let error = resolve(&root, &dep, id, &reference(id, 3), site).unwrap_err();
            assert_eq!(
                error,
                ImportVerificationError::InterposableFarSite {
                    symbol: "f".into(),
                    linkage,
                    side: "far",
                },
                "{linkage:?} at {site:?}"
            );
            assert_eq!(
                error.to_string(),
                format!(
                    "far symbol `f` has interposable linkage {linkage:?}: the linker may bind \
                     a different definition (or null), so a proof about this body does not \
                     transfer"
                )
            );
        }
    }
}

#[test]
fn an_interposable_local_declaration_cannot_rely_on_a_cross_crate_claim() {
    for linkage in [Linkage::ExternalWeak, Linkage::Weak, Linkage::LinkOnce] {
        let dep = dependency();
        assert_eq!(dep.functions[0].linkage, Linkage::External);
        let (mut root, id) = importer(&dep);
        root.functions[0].linkage = linkage;
        for site in BOTH_SITES {
            let error = resolve(&root, &dep, id, &reference(id, 3), site).unwrap_err();
            assert_eq!(
                error,
                ImportVerificationError::InterposableFarSite {
                    symbol: "f".into(),
                    linkage,
                    side: "local",
                },
                "{linkage:?} at {site:?}"
            );
            assert!(
                error
                    .to_string()
                    .starts_with("local symbol `f` has interposable"),
                "{error}"
            );
        }
    }
}

#[test]
fn odr_and_available_externally_far_linkage_stay_admitted() {
    // Mutation control against an over-broad rule: the ODR spellings (how
    // Rust generic instances link) and `AvailableExternally` are admitted
    // under the disclosed one-definition-rule premise.
    for linkage in [
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
        Linkage::AvailableExternally,
    ] {
        let mut dep = dependency();
        dep.functions[0].linkage = linkage;
        let (root, id) = importer(&dep);
        for site in BOTH_SITES {
            assert_eq!(
                resolve(&root, &dep, id, &reference(id, 3), site),
                Ok(()),
                "{linkage:?} at {site:?}"
            );
        }
    }
    // The same for the local declaration's ODR spellings.
    for linkage in [Linkage::WeakOdr, Linkage::LinkOnceOdr] {
        let dep = dependency();
        let (mut root, id) = importer(&dep);
        root.functions[0].linkage = linkage;
        for site in BOTH_SITES {
            assert_eq!(
                resolve(&root, &dep, id, &reference(id, 3), site),
                Ok(()),
                "local {linkage:?} at {site:?}"
            );
        }
    }
}

#[test]
fn the_interposability_rule_runs_after_export_and_backing_checks() {
    // Check order, pinned: an unexported far symbol is still named
    // `SymbolNotExported` ...
    let mut dep = dependency();
    dep.functions[0].linkage = Linkage::Internal;
    let (root, id) = importer(&dep);
    for site in BOTH_SITES {
        assert_eq!(
            resolve(&root, &dep, id, &reference(id, 3), site),
            Err(ImportVerificationError::SymbolNotExported {
                symbol: "f".into(),
                linkage: Linkage::Internal,
            })
        );
    }

    // ... and a bare far re-declaration spelled `ExternalWeak` names the
    // substantive defect (no body, no backing) first.
    let mut dep = dependency();
    dep.functions[0].blocks.clear();
    dep.functions[0].linkage = Linkage::ExternalWeak;
    let (root, id) = importer(&dep);
    for site in BOTH_SITES {
        assert_eq!(
            resolve(&root, &dep, id, &reference(id, 3), site),
            Err(ImportVerificationError::FarSiteIsUnbackedDeclaration { symbol: "f".into() })
        );
    }

    // A far declaration that DOES record a backing but is spelled
    // `ExternalWeak` passes R4's definition clause and is then refused as
    // interposable: a weak declaration may bind to null.
    let further = ExternRef::new(ImportId::new(0), "f").relying_on(ProofId::new(0));
    let mut dep = dependency();
    dep.functions[0].blocks.clear();
    dep.functions[0].summary = Some(FunctionSummary::new().backed_by(further));
    dep.functions[0].linkage = Linkage::ExternalWeak;
    let (root, id) = importer(&dep);
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::SummaryBackedBy
        ),
        Err(ImportVerificationError::InterposableFarSite {
            symbol: "f".into(),
            linkage: Linkage::ExternalWeak,
            side: "far",
        })
    );
}

#[test]
fn an_available_externally_local_declaration_stays_admitted() {
    // Review (mutation control on the LOCAL leg): the local rule refuses the
    // same three linkages as the far one and nothing else. An
    // `AvailableExternally` local row binds to the one external definition
    // under the same disclosed ODR premise, so it is admitted at both sites;
    // `External` is the baseline.
    for linkage in [Linkage::External, Linkage::AvailableExternally] {
        let dep = dependency();
        let (mut root, id) = importer(&dep);
        root.functions[0].linkage = linkage;
        for site in BOTH_SITES {
            assert_eq!(
                resolve(&root, &dep, id, &reference(id, 3), site),
                Ok(()),
                "local {linkage:?} at {site:?}"
            );
        }
    }
}

#[test]
fn the_local_interposability_rule_runs_after_the_body_and_symbol_checks() {
    // Review (check order on the LOCAL leg): a local row that is a
    // DEFINITION, or that carries the wrong link symbol, is named for that
    // substantive defect even when it is also spelled `ExternalWeak`; and the
    // local leg fires before any far-side defect (here an unexported far
    // symbol), because R2 precedes R3/R4.
    let dep = dependency();
    let (mut root, id) = importer(&dep);
    root.functions[0].name = "g".into();
    root.functions[0].linkage = Linkage::ExternalWeak;
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::SummaryBackedBy
        ),
        Err(ImportVerificationError::LinkSymbolMismatch {
            function: root.functions[0].id.index(),
            local: "g".into(),
            symbol: "f".into(),
        })
    );

    let mut dep = dependency();
    dep.functions[0].linkage = Linkage::Internal;
    let (mut root, id) = importer(&dep);
    root.functions[0].linkage = Linkage::ExternalWeak;
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::InheritedFromCallee
        ),
        Err(ImportVerificationError::InterposableFarSite {
            symbol: "f".into(),
            linkage: Linkage::ExternalWeak,
            side: "local",
        })
    );
}

// ---------------------------------------------------------------------------
// WS3.3 (F-048): the hardened R4 at `ExternRefSite::HandleDeclaration`
// ---------------------------------------------------------------------------

/// The entity-only binding an import-backed handle declaration carries.
fn entity(id: ImportId) -> ExternRef {
    ExternRef::new(id, "f")
}

#[test]
fn the_handle_declaration_site_is_claim_free_and_labelled() {
    let site = ExternRefSite::HandleDeclaration;
    assert_eq!(site.label(), "handle");
    assert_eq!(site.to_string(), "handle");
    for kind in [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::MemorySafety,
        ObligationKind::Termination,
        ObligationKind::Ownership,
    ] {
        assert!(!site.admits(&kind), "{kind}");
    }
}

#[test]
fn the_handle_declaration_site_admits_a_far_definition() {
    let dep = dependency();
    let (root, id) = importer(&dep);
    let verified = root.verify_import(id, &dep).unwrap();
    let resolved = root
        .resolve_handle_declaration(&entity(id), FuncId::new(0), &verified, &BTreeSet::new())
        .expect("an External far definition");
    assert_eq!(resolved.far.id, FuncId::new(0));
    assert!(
        resolved.obligation.is_none(),
        "the site is about the entity"
    );
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &entity(id),
            ExternRefSite::HandleDeclaration
        ),
        Ok(())
    );
    // A cited obligation is ignored by the vouched form (the entity is what
    // the site is about) and REFUSED by the generic one, which runs R7 at a
    // site that admits no kind — R7 cannot be skipped by mistake.
    assert!(
        root.resolve_handle_declaration(
            &reference(id, 3),
            FuncId::new(0),
            &verified,
            &BTreeSet::new()
        )
        .is_ok()
    );
    assert!(matches!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::HandleDeclaration
        ),
        Err(ImportVerificationError::ObligationKindInadmissible { .. })
    ));
}

#[test]
fn the_handle_declaration_site_refuses_a_far_declaration_the_caller_does_not_vouch_for() {
    // mid re-declares `f` with an ENTITY-ONLY `backed_by`: the general R4
    // admits it at every other site ("records a backing"), and that is exactly
    // the weakness the handle site closes.
    let mut dep = dependency();
    dep.functions[0].blocks.clear();
    dep.functions[0].summary =
        Some(FunctionSummary::new().backed_by(ExternRef::new(ImportId::new(0), "f")));
    let (root, id) = importer(&dep);
    assert_eq!(
        resolve(&root, &dep, id, &entity(id), ExternRefSite::CallEdge),
        Ok(()),
        "the general R4 admits a re-declaration that records a backing"
    );
    let refused = Err(ImportVerificationError::FarSiteIsUnbackedDeclaration { symbol: "f".into() });
    // The generic entry point holds no dependency verdict: every far
    // declaration is refused.
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &entity(id),
            ExternRefSite::HandleDeclaration
        ),
        refused
    );
    let verified = root.verify_import(id, &dep).unwrap();
    let vouched = |set: BTreeSet<FuncId>| {
        root.resolve_handle_declaration(&entity(id), FuncId::new(0), &verified, &set)
            .map(|_| ())
    };
    assert_eq!(vouched(BTreeSet::new()), refused);
    assert_eq!(
        vouched(BTreeSet::from([FuncId::new(1)])),
        refused,
        "vouching is per function"
    );
    assert_eq!(vouched(BTreeSet::from([FuncId::new(0)])), Ok(()));
}

#[test]
fn the_handle_declaration_site_refuses_an_available_externally_copy() {
    let mut dep = dependency();
    dep.functions[0].linkage = Linkage::AvailableExternally;
    assert!(!dep.functions[0].is_declaration());
    let (root, id) = importer(&dep);
    let error = resolve(
        &root,
        &dep,
        id,
        &entity(id),
        ExternRefSite::HandleDeclaration,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ImportVerificationError::FarSiteIsAvailableExternallyCopy { symbol: "f".into() }
    );
    assert!(
        error
            .to_string()
            .contains("`available_externally` body copy"),
        "{error}"
    );
    // Every other site keeps the disclosed ODR premise (TRUST.md item 10).
    assert_eq!(
        resolve(&root, &dep, id, &entity(id), ExternRefSite::CallEdge),
        Ok(())
    );
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &reference(id, 3),
            ExternRefSite::SummaryBackedBy
        ),
        Ok(())
    );
}

#[test]
fn the_handle_declaration_site_refuses_a_weak_local_declaration() {
    let dep = dependency();
    let (mut root, id) = importer(&dep);
    root.functions[0].linkage = Linkage::ExternalWeak;
    assert_eq!(
        resolve(
            &root,
            &dep,
            id,
            &entity(id),
            ExternRefSite::HandleDeclaration
        ),
        Err(ImportVerificationError::InterposableFarSite {
            symbol: "f".into(),
            linkage: Linkage::ExternalWeak,
            side: "local",
        })
    );
    // The claim-free call edge admits the same weak import.
    assert_eq!(
        resolve(&root, &dep, id, &entity(id), ExternRefSite::CallEdge),
        Ok(())
    );
}
