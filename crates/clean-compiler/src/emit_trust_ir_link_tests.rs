// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the first real producer of `trust_ir::Module::imports`.
//!
//! The load-bearing test is the ROUND TRIP: the consumer
//! (`validate_linked_module`) must RE-EARN the verdict over the rows this
//! producer wrote. Beside it sits the negative that makes the digest mean
//! something — the same producer output against a REBUILT dependency (same
//! name, same symbol, same signature, different body) must be refused.

use super::*;

use clean_kernel::{BinderInfo, Expr};

use crate::emit_trust_ir::emit_trust_ir;
use crate::emit_trust_ir_tv::certify_backend_translation;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name as KName;

use trust_ir::proof::{ClausePlace, ClauseSort};
use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};

// ---------------------------------------------------------------------------
// fixtures — one LIBRARY and one CLIENT, from the same corpus shape the TV
// suite already certifies (`helper_caller_decls`'s helper: UInt32 -> UInt32).
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::default(),
    }
}

/// `helper(y : UInt32) : UInt32 := y` (the identity), or with `bump` a body
/// that ADDS a constant, so the rebuilt-library negative moves the digest for a
/// real reason rather than a cosmetic one.
fn helper_decl(bump: Option<u32>) -> IRDecl {
    let body = match bump {
        None => IRBody::Ret(IRArg::Var(VarId(0))),
        Some(k) => IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::Lit(IRLiteral::UInt32(k)),
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::UInt32,
                value: IRExpr::Apply {
                    fn_id: FnId(KName::from_string("UInt32.add")),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    IRDecl {
        name: KName::from_string("helper"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body,
    }
}

/// `fun (y : UInt32) => y` — the identity helper's source.
fn helper_identity_source() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::bvar(0),
    )
}

/// `fun (y : UInt32) => UInt32.add y (UInt32.ofNat k)` — the bumped source.
fn helper_bumped_source(k: u64) -> Expr {
    let of_nat = Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(k));
    Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::apps(Expr::const_str("UInt32.add"), [Expr::bvar(0), of_nat]),
    )
}

/// Emit `helper` as a standalone LIBRARY artifact with its `Certified`
/// `TranslationValidation` obligation minted by the real kernel path.
fn library(bump: Option<u32>) -> Module {
    let mut module = emit_trust_ir(&[helper_decl(bump)]).expect("helper lowers");
    module.target_info = Some(target());
    let source = match bump {
        None => helper_identity_source(),
        Some(k) => helper_bumped_source(u64::from(k)),
    };
    let report = certify_backend_translation(&mut module, &[("helper".to_string(), source)]);
    assert!(
        report.certified.contains(&"helper".to_string()),
        "the library fixture must really certify (kernel-decided), got {report:?}"
    );
    module
}

/// The CLIENT this backend emits: a module that defines nothing of its own yet
/// and will import `helper`. Kept deliberately minimal — the point of these
/// tests is the import rows, not a body.
/// Drop every license's `GateEvidence` (trust-ir v61): what a fixture that
/// demotes the TV row the evidence cites must do to stay the honest module it
/// models.
fn drop_license_evidence(module: &mut Module) {
    let dropped = module
        .functions
        .iter_mut()
        .map(Function::invalidate_gate_evidence)
        .filter(|dropped| *dropped)
        .count();
    assert_eq!(dropped, 1, "the library fixture licenses exactly `helper`");
}

fn client_shell() -> Module {
    let mut m = Module::new("client");
    m.target_info = Some(target());
    m
}

/// `helper`, wanted with the CLIENT's own elaboration of it: the identity
/// source, i.e. the same definition the default library certifies.
fn wanted() -> Vec<WantedSymbol> {
    vec![WantedSymbol::with_source(
        "helper",
        helper_identity_source(),
    )]
}

fn dep(module: Module, path: &str) -> LinkedArtifact {
    LinkedArtifact {
        path: path.to_string(),
        module,
    }
}

/// The client `link_imported_modules` must leave behind when it refuses: the
/// untouched shell — no import row, no declaration, no claim.
fn assert_client_untouched(client: &Module) {
    assert!(client.imports.is_empty(), "no import row may be written");
    assert!(client.functions.is_empty(), "no declaration may be written");
    assert!(
        client.proof_obligations.is_empty(),
        "no obligation may be written"
    );
    assert!(
        client.proof_certificates.is_empty(),
        "no certificate may be written"
    );
}

/// The single consumer refusal the producer's final gate returned, or a panic
/// naming what came back instead.
fn sole_consumer_refusal(result: Result<LinkReport, LinkError>) -> String {
    match result {
        Err(LinkError::ConsumerRefused(errors)) => {
            let [only] = errors.as_slice() else {
                panic!("expected exactly one consumer refusal, got {errors:?}");
            };
            only.clone()
        }
        other => panic!("expected the producer's final gate to refuse, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// the round trip
// ---------------------------------------------------------------------------

#[test]
fn a_consumer_re_earns_the_verdict_over_the_rows_this_producer_wrote() {
    let lib = library(None);
    let lib_digest = lib.stable_digest();
    let mut client = client_shell();
    let report = link_imported_modules(&mut client, &[dep(lib.clone(), "lib.tmbc")], &wanted())
        .expect("the link must succeed");

    // Exactly one import row, and its digest is the one MEASURED over the
    // artifact that was read — not a name, not a path.
    assert_eq!(client.imports.len(), 1, "one dependency, one row");
    assert_eq!(
        client.imports[0].digest, lib_digest,
        "the recorded digest must be `stable_digest()` of the artifact actually read"
    );
    assert_eq!(client.imports[0].name, lib.name);
    assert_eq!(
        client.imports[0].producer,
        Some(Producer::Clean),
        "the producer is written only when measured, and never as `None`"
    );

    // One typed body-less declaration carrying the FAR signature.
    let decl = client
        .functions
        .iter()
        .find(|f| f.name == "helper")
        .expect("the declaration must exist");
    assert!(
        decl.is_declaration(),
        "an import declares, it does not define"
    );
    let far = lib.functions.iter().find(|f| f.name == "helper").unwrap();
    assert_eq!(
        client.func_types[decl.ty.as_usize()],
        lib.func_types[far.ty.as_usize()],
        "the declaration takes the FAR signature, not a boxed extern-fallback shape"
    );
    assert!(
        decl.body_gate.is_none(),
        "a declaration is not a codegen subject and makes no licensing claim"
    );

    // One proof claim, earned.
    assert_eq!(report.proved.len(), 1, "{report:?}");
    assert!(report.identity_only.is_empty(), "{report:?}");
    let restatement = report.proved[0].restatement.expect("a proved row restates");
    let local = client
        .proof_obligations
        .iter()
        .find(|o| o.id == restatement)
        .expect("the restatement must be in the table");
    assert_eq!(local.kind, ObligationKind::TranslationValidation);
    assert_eq!(
        local.status,
        ProofStatus::Discharged,
        "`LinkedAuthority` admits an authenticated inheritance into the Discharged \
         tier and no other; `Certified` would be laundering and `Pending` would be a \
         certificate with nothing to discharge"
    );

    // The evidence's `obligation` is the LOCAL restatement (linked.rs refuses
    // inequality with ExternInheritanceRestatementMismatch); the FAR id lives
    // only in the ExternRef.
    let cert = client
        .proof_certificates
        .iter()
        .find(|c| c.obligation == restatement)
        .expect("the restatement must carry a certificate");
    match &cert.evidence {
        ProofEvidence::InheritedFromCallee {
            obligation,
            external: Some(ext),
            ..
        } => {
            assert_eq!(*obligation, restatement, "evidence restates the LOCAL row");
            assert_eq!(ext.symbol, "helper");
            assert!(ext.obligation.is_some(), "the far row must be named");
        }
        other => panic!("expected an external inheritance, got {other:?}"),
    }

    // THE POINT: a consumer re-earns it, against the dependency bound by digest.
    let deps = [lib];
    let set = ModuleSet::new(deps.iter());
    let verdict = validate_linked_module(&client, &set, &RejectingModuleProofAuthority);
    assert!(
        verdict.is_ok(),
        "the consumer must re-earn the producer's rows: {:?}",
        verdict.errors()
    );

    // And `Module::verify_import` authenticates the row on its own terms: it
    // recomputes the candidate's digest here rather than being handed one, so
    // C3 compares a measurement with the record.
    let import_id = ImportId::new(0);
    assert!(
        client.verify_import(import_id, &deps[0]).is_ok(),
        "the row must authenticate against the artifact it names"
    );
    // The same call against the REBUILT artifact refuses, and names the digest.
    let rebuilt = library(Some(3));
    assert!(matches!(
        client.verify_import(import_id, &rebuilt),
        Err(trust_ir::ImportVerificationError::DigestMismatch { .. })
    ));
}

#[test]
fn the_client_alone_fails_the_faith_floor() {
    let lib = library(None);
    let mut client = client_shell();
    link_imported_modules(&mut client, &[dep(lib, "lib.tmbc")], &wanted()).expect("links");
    // Asserted, not worked around: a cross-crate `Discharged` row is grounded
    // only under the linked walk. If this ever passed, the row would be
    // laundering.
    let errors = trust_ir_build::validate_module(&client);
    assert!(
        !errors.is_empty(),
        "a cross-crate Discharged row must NOT stand on its own"
    );
}

// ---------------------------------------------------------------------------
// negatives
// ---------------------------------------------------------------------------

#[test]
fn the_same_output_against_a_rebuilt_dependency_is_refused() {
    let lib = library(None);
    let rebuilt = library(Some(1));
    assert_eq!(lib.name, rebuilt.name, "the rebuild keeps the module name");
    assert_ne!(
        lib.stable_digest(),
        rebuilt.stable_digest(),
        "the rebuild must move the digest, or this test proves nothing"
    );

    let mut client = client_shell();
    link_imported_modules(&mut client, &[dep(lib, "lib.tmbc")], &wanted()).expect("links");

    // The client's row cites the ORIGINAL. Hand the consumer the rebuild.
    let deps = [rebuilt];
    let set = ModuleSet::new(deps.iter());
    let verdict = validate_linked_module(&client, &set, &RejectingModuleProofAuthority);
    assert!(
        !verdict.is_ok(),
        "a rebuilt dependency with the same name must NOT satisfy the row"
    );
}

#[test]
fn a_dependency_with_no_recorded_producer_is_refused_rather_than_written_as_none() {
    let mut lib = library(None);
    for f in &mut lib.functions {
        f.producer = None;
    }
    let mut client = client_shell();
    let err = link_imported_modules(&mut client, &[dep(lib, "lib.tmbc")], &wanted())
        .expect_err("an unrecorded producer must refuse");
    assert_eq!(
        err,
        LinkError::Artifact {
            path: "lib.tmbc".to_string(),
            why: LinkRefusal::ProducerUnrecorded
        }
    );
    assert!(
        client.imports.is_empty(),
        "a refused artifact leaves the client untouched"
    );
}

#[test]
fn a_target_absent_on_either_side_is_not_agreement() {
    let mut lib = library(None);
    lib.target_info = None;
    let mut client = client_shell();
    let err = link_imported_modules(&mut client, &[dep(lib, "lib.tmbc")], &wanted())
        .expect_err("absence is not agreement");
    assert!(matches!(
        err,
        LinkError::Artifact {
            why: LinkRefusal::TargetMismatch,
            ..
        }
    ));
}

#[test]
fn a_far_formula_mutated_by_one_byte_is_refused_at_the_producer() {
    let mut lib = library(None);
    // The importer DERIVES the formula from the far name + signature and
    // requires byte-equality. Moving the recorded text also unbinds the far
    // certificate's lineage from its obligation, so the dependency no longer
    // validates on its own.
    for o in &mut lib.proof_obligations {
        if let Some(f) = o.formula.as_mut() {
            f.payload.push('!');
        }
    }
    let mut client = client_shell();
    // Since trust-ir WS1.7 (da6ff616) the linked walk validates EVERY import
    // row recursively (L1-L4), cited or not, so an identity-only row naming an
    // artifact that does not validate is itself a refusal: the producer's
    // final gate (the consumer's check) refuses the whole link and writes
    // nothing — no row, no declaration, no claim.
    let refusal = sole_consumer_refusal(link_imported_modules(
        &mut client,
        &[dep(lib, "lib.tmbc")],
        &wanted(),
    ));
    assert!(
        refusal.starts_with("ImportedModuleInvalid { import: 0,")
            && refusal.contains("lineage is not bound to this obligation"),
        "the refusal must name the unbound far certificate: {refusal}"
    );
    assert_client_untouched(&client);
}

#[test]
fn a_far_row_whose_status_is_only_trusted_grounds_nothing() {
    let mut lib = library(None);
    for o in &mut lib.proof_obligations {
        if o.kind == ObligationKind::TranslationValidation {
            o.status = ProofStatus::Trusted;
        }
    }
    // A Trusted row is not license evidence (trust-ir v61 `GateEvidence`
    // must cite a Certified TV row), so the honest library this models
    // carries none; the stale-evidence refusal is pinned in the TV suite.
    drop_license_evidence(&mut lib);
    // Synthetic attributed faith satisfies the structural metadata rule;
    // it is deliberately NOT the kernel-rechecked certificate it replaces.
    for certificate in &mut lib.proof_certificates {
        certificate.evidence =
            ProofEvidence::Trusted("test-only attributed faith, not a certified proof".into());
    }
    assert!(trust_ir_build::validate_module(&lib).is_empty());
    assert_eq!(lib.trusted_evidence_census().len(), 1);
    let dependency = dep(lib, "lib.tmbc");
    let original = dependency.module.clone();
    let mut client = client_shell();
    let report = link_imported_modules(&mut client, std::slice::from_ref(&dependency), &wanted())
        .expect("identity rows are still honest");
    assert!(
        report.proved.is_empty(),
        "a status label is not proof authority"
    );
    assert_eq!(
        report.identity_only[0].1,
        LinkRefusal::FarDischargeNotUnique,
        "a Trusted row is not a Certified one"
    );
    assert!(client.proof_obligations.is_empty());
    assert!(client.proof_certificates.is_empty());
    assert_eq!(dependency.module, original);
}

#[test]
fn a_far_trusted_label_without_attributed_faith_is_refused_unchanged() {
    for blank_justification in [false, true] {
        let mut lib = library(None);
        let obligation = lib
            .proof_obligations
            .iter_mut()
            .find(|o| o.kind == ObligationKind::TranslationValidation)
            .expect("real TV fixture has a row");
        obligation.status = ProofStatus::Trusted;
        let obligation_id = obligation.id.index();
        // As above: a Trusted row backs no license evidence.
        drop_license_evidence(&mut lib);
        if blank_justification {
            for certificate in &mut lib.proof_certificates {
                certificate.evidence = ProofEvidence::Trusted(" \t\n".into());
            }
        }
        assert_eq!(
            trust_ir_build::validate_module(&lib),
            [
                trust_ir_build::ValidationError::TrustedWithoutJustification {
                    obligation: obligation_id,
                }
            ],
        );
        let dependency = dep(lib, "lib.tmbc");
        let original_dependency = dependency.module.clone();
        let mut client = client_shell();
        let original_client = client.clone();
        let refusal = sole_consumer_refusal(link_imported_modules(
            &mut client,
            std::slice::from_ref(&dependency),
            &wanted(),
        ));
        assert!(refusal.starts_with("ImportedModuleInvalid { import: 0, errors: 1,"));
        assert!(refusal.contains("status is Trusted but no certificate carries ProofEvidence::Trusted with a non-blank justification"));
        assert_eq!(client, original_client);
        assert_client_untouched(&client);
        assert_eq!(dependency.module, original_dependency);
    }
}

#[test]
fn a_far_site_that_only_declares_is_refused() {
    let mut lib = library(None);
    for f in &mut lib.functions {
        if f.name == "helper" {
            f.blocks.clear();
            // Removing the body rewrites it, so its license's evidence
            // (trust-ir v61) is dropped, as every body rewrite must; left in
            // place it would be refused first, as a stale license.
            assert!(
                f.invalidate_gate_evidence(),
                "the minted license had evidence"
            );
        }
    }
    let mut client = client_shell();
    // The producer declines the symbol (`FarSiteIsUnbackedDeclaration`), but
    // the artifact still carries a `Certified` row whose kernel re-check now
    // has no body to run against, so it does not validate — and since trust-ir
    // WS1.7 (da6ff616) every import row is recursively validated. The final
    // gate refuses the link, and a re-declaration backs nothing.
    let refusal = sole_consumer_refusal(link_imported_modules(
        &mut client,
        &[dep(lib, "lib.tmbc")],
        &wanted(),
    ));
    assert!(
        refusal.starts_with("ImportedModuleInvalid { import: 0,")
            && refusal.contains("function 'helper' has no entry block"),
        "the refusal must name the body-less far site: {refusal}"
    );
    assert_client_untouched(&client);
}

#[test]
fn a_symbol_the_client_already_declares_is_refused_not_duplicated() {
    // The emitter mints a boxed `fn(Ptr) -> Ptr` extern fallback for every
    // dropped callee. Importing the same link symbol on top of it would put two
    // functions in one module under one symbol, which v41's
    // `DuplicateFunctionSymbol` rule rejects — so the producer must refuse
    // rather than write a module no consumer can accept.
    let lib = library(None);
    let mut client = client_shell();
    let boxed = client
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut fallback = Function::declaration(
        FuncId::new(0),
        "helper",
        boxed,
        trust_ir::FunctionSummary::new(),
    );
    fallback.summary = None;
    fallback.producer = Some(Producer::Clean);
    client
        .try_add_function(fallback)
        .expect("Module::try_add_function: test fixture");

    let before = client.clone();
    // The producer declines to add a second `helper`
    // (`ClientAlreadyDeclaresSymbol`), but the import row it wrote makes the
    // artifact an authenticated definer of `helper`, and since trust-ir WS1.7
    // (da6ff616, L10) every call edge binds implicitly to the one
    // authenticated artifact that defines and exports its symbol. The boxed
    // `fn(Ptr) -> Ptr` fallback does not match the far `fn(U32) -> U32`, so the
    // producer's final gate refuses the whole link and leaves the client as
    // it was found.
    let refusal = sole_consumer_refusal(link_imported_modules(
        &mut client,
        &[dep(lib, "lib.tmbc")],
        &wanted(),
    ));
    assert!(
        refusal.starts_with("UnauthenticatedImport { import: 0, site: \"call\",")
            && refusal.contains("call edge @helper")
            && refusal.contains("signature mismatch"),
        "the refusal must name the mismatched call edge: {refusal}"
    );
    assert_eq!(client, before, "a refused link leaves the client unchanged");
    assert_eq!(
        client
            .functions
            .iter()
            .filter(|f| f.name == "helper")
            .count(),
        1,
        "exactly one function may carry a link symbol"
    );
    assert!(
        trust_ir_build::validate_module(&client).is_empty(),
        "the refusal must leave a module that still validates: {:?}",
        trust_ir_build::validate_module(&client)
    );
}

// ---------------------------------------------------------------------------
// the formula constructor's own contract
// ---------------------------------------------------------------------------

#[test]
fn the_tv_formula_is_a_function_of_symbol_arity_and_width_only() {
    let a = clean_reflect::tv_statement_formula("helper", 1, 32);
    let b = clean_reflect::tv_statement_formula("helper", 1, 32);
    assert_eq!(a, b, "the derivation must be deterministic");
    assert_ne!(a, clean_reflect::tv_statement_formula("other", 1, 32));
    assert_ne!(a, clean_reflect::tv_statement_formula("helper", 2, 32));
    assert_ne!(a, clean_reflect::tv_statement_formula("helper", 1, 64));
    assert_eq!(a.schema, clean_reflect::CLEAN_TV_FORMULA_SCHEMA);
    // No SMT rendering exists for a kernel definitional-equality judgment, so
    // there is none recorded. That absence is a fact, not a stand-in.
    assert!(a.smtlib.is_none() && a.sort.is_none());
}

#[test]
fn every_clause_binding_index_is_in_range_for_its_own_signature() {
    // Load-bearing: the validator resolves bindings on SUMMARY clauses only,
    // so a wrong `Param` index on an obligation formula would be carried
    // silently and read as checkable. This is the producer-side check.
    for arity in 0u32..6 {
        let f = clean_reflect::tv_statement_formula("f", arity, 32);
        assert_eq!(f.bindings.len(), arity as usize);
        for (i, (name, binding)) in f.bindings.iter().enumerate() {
            assert_eq!(*name, format!("x{i}"));
            match binding.place {
                ClausePlace::Param { index } => {
                    assert!(
                        index < arity,
                        "index {index} out of range for arity {arity}"
                    );
                    assert_eq!(index as usize, i);
                }
                ref other => panic!("a TV parameter binding must be a Param place, got {other:?}"),
            }
            assert_eq!(binding.sort, ClauseSort::BitVec(32));
        }
    }
}

#[test]
fn nothing_is_written_when_nothing_was_asked_for() {
    let lib = library(None);
    let mut client = client_shell();
    let report = link_imported_modules(&mut client, &[dep(lib, "lib.tmbc")], &[]).expect("no-op");
    assert!(report.imports.is_empty());
    assert!(
        client.imports.is_empty(),
        "an unused dependency is not a row"
    );
}

// WS6.8: the source binding, the emitter's imported-callee arm, adoption, and
// the review's transitive / bypass cases live in a child module that shares
// the fixtures above (kept apart so neither file crosses 1000 lines).
#[path = "emit_trust_ir_link_ws6_8_tests.rs"]
mod ws6_8;
