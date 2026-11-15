// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS6.8 tests of the import producer: the source binding, the emitter's
//! imported-callee arm, adoption of its declaration, the CLI-facing import
//! table, and the review's transitive / bypass cases. A child of
//! `emit_trust_ir_link_tests.rs` (split out so neither file crosses the
//! paragon 1000-line threshold); it shares that file's fixtures.

use super::*;

// ---------------------------------------------------------------------------
// WS6.8: the source binding, the emitter's imported-callee arm, adoption
// ---------------------------------------------------------------------------

/// The proof row a successful link wrote, if any.
fn restatement_rows(client: &Module) -> usize {
    client
        .proof_obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::TranslationValidation)
        .count()
}

#[test]
fn a_far_certificate_honestly_minted_against_a_different_body_backs_no_claim() {
    // `helper y := y + 3`, certified by the real kernel path: every step 1-5
    // measurement holds (same symbol, same signature, same derived formula, a
    // replayed Certified row). Only the comparand differs from the client's
    // own elaboration (`helper y := y`). Without the source binding this
    // dependency would back the CLIENT's meaning of `helper`.
    let other_body = library(Some(3));
    let mut client = client_shell();
    let report = link_imported_modules(
        &mut client,
        &[dep(other_body.clone(), "lib.bin")],
        &wanted(),
    )
    .expect("identity rows are still honest");
    assert!(report.proved.is_empty(), "{report:?}");
    assert_eq!(
        report.identity_only.len(),
        1,
        "the symbol keeps its identity rows: {report:?}"
    );
    assert_eq!(
        report.identity_only[0].1,
        LinkRefusal::FarComparandDisagreesWithClientSource
    );
    assert_eq!(client.imports.len(), 1, "the import row is written");
    assert_eq!(client.imports[0].digest, other_body.stable_digest());
    assert_eq!(restatement_rows(&client), 0, "NO proof row");
    assert!(client.proof_certificates.is_empty(), "NO certificate");

    // MUTATION CONTROL: the client whose elaboration IS the bumped body gets
    // the proof row from the same artifact, so the refusal above is the
    // comparand check and nothing else.
    let mut agreeing = client_shell();
    let report = link_imported_modules(
        &mut agreeing,
        &[dep(other_body, "lib.bin")],
        &[WantedSymbol::with_source("helper", helper_bumped_source(3))],
    )
    .expect("links");
    assert_eq!(report.proved.len(), 1, "{report:?}");
    assert_eq!(restatement_rows(&agreeing), 1);
}

#[test]
fn a_wanted_symbol_without_a_client_source_is_identity_only() {
    let mut client = client_shell();
    let report = link_imported_modules(
        &mut client,
        &[dep(library(None), "lib.bin")],
        &[WantedSymbol {
            symbol: "helper".to_string(),
            client_source: None,
        }],
    )
    .expect("identity rows are still honest");
    assert!(report.proved.is_empty());
    assert!(matches!(
        report.identity_only[0].1,
        LinkRefusal::ClientSourceUnavailable(_)
    ));
    assert_eq!(restatement_rows(&client), 0);
}

/// `caller(x : UInt32) : UInt32 := helper x` — the client's own decl.
fn caller_decl() -> IRDecl {
    IRDecl {
        name: KName::from_string("caller"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::Apply {
                fn_id: FnId(KName::from_string("helper")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

/// The emitter config that imports `helper` at `far`.
fn importing(far: FuncTy) -> crate::emit_trust_ir::TrustIrConfig {
    let mut imported_callees = BTreeMap::new();
    imported_callees.insert("helper".to_string(), far);
    crate::emit_trust_ir::TrustIrConfig {
        target_info: Some(target()),
        imported_callees,
        ..crate::emit_trust_ir::TrustIrConfig::default()
    }
}

fn u32_to_u32() -> FuncTy {
    FuncTy {
        params: vec![Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    }
}

#[test]
fn the_emitter_declares_an_imported_callee_at_the_far_signature_and_the_link_adopts_it() {
    let lib = library(None);
    let mut client = crate::emit_trust_ir::emit_trust_ir_with_config(
        &[caller_decl(), helper_decl(None)],
        &importing(u32_to_u32()),
    )
    .expect("the client lowers with `helper` imported");
    let helper = client
        .functions
        .iter()
        .find(|f| f.name == "helper")
        .expect("the import is declared");
    assert!(
        helper.is_declaration(),
        "the imported body is NOT re-embedded"
    );
    assert_eq!(client.func_types[helper.ty.as_usize()], u32_to_u32());

    let report = link_imported_modules(&mut client, &[dep(lib.clone(), "lib.bin")], &wanted())
        .expect("the link adopts the emitter's declaration");
    assert_eq!(report.proved.len(), 1, "{report:?}");
    assert!(report.declined.is_empty(), "{report:?}");
    assert_eq!(
        client
            .functions
            .iter()
            .filter(|f| f.name == "helper")
            .count(),
        1,
        "adopted, never duplicated"
    );
    assert_eq!(client.imports.len(), 1);
    assert_eq!(client.imports[0].digest, lib.stable_digest());
    let deps = [lib];
    let verdict = validate_linked_module(
        &client,
        &ModuleSet::new(deps.iter()),
        &RejectingModuleProofAuthority,
    );
    assert!(verdict.is_ok(), "{:?}", verdict.errors());
}

#[test]
fn a_client_call_shape_that_disagrees_with_the_far_signature_refuses_the_compile() {
    // The far artifact was built under a configuration that boxed `helper`:
    // `fn(Ptr) -> Ptr`. The client's lowering is `fn(U32) -> U32`, the shape
    // its call site was emitted against. Refused by name, never re-boxed.
    let boxed = FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::Ptr],
        is_vararg: false,
        abi: None,
    };
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(
        &[caller_decl(), helper_decl(None)],
        &importing(boxed),
    )
    .expect_err("a disagreeing call shape must refuse the compile");
    match err {
        crate::emit_trust_ir::TrustIrError::ImportRefused { symbol, why } => {
            assert_eq!(symbol, "helper");
            assert!(
                matches!(
                    why,
                    LinkRefusal::CallShapeDisagreesWithFarSignature { ref local, ref far }
                        if local == "fn(u32) -> (u32)" && far == "fn(ptr) -> (ptr)"
                ),
                "{why:?}"
            );
        }
        other => panic!("expected ImportRefused, got {other:?}"),
    }
}

#[test]
fn a_boxed_extern_fallback_is_still_not_adopted() {
    // Adoption is for a declaration EQUAL to the far signature only; the
    // boxed fallback keeps `ClientAlreadyDeclaresSymbol`. (The link as a whole
    // is then refused by the consumer's call-edge rule — pinned by
    // `a_symbol_the_client_already_declares_is_refused_not_duplicated`.)
    let lib = library(None);
    let far = lib.functions.iter().find(|f| f.name == "helper").unwrap();
    let far_ft = lib.func_types[far.ty.as_usize()].clone();
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
    client
        .try_add_function(fallback)
        .expect("Module::try_add_function: test fixture");
    assert!(!adoptable_import_declaration(
        &client,
        &client.functions[0],
        &far_ft
    ));
    // Same declaration at the far signature: adoptable.
    let typed = client
        .add_func_type(far_ft.clone())
        .expect("Module::add_func_type: test fixture");
    client.functions[0].ty = typed;
    assert!(adoptable_import_declaration(
        &client,
        &client.functions[0],
        &far_ft
    ));
}

#[test]
fn a_dependency_is_imported_only_when_exactly_one_artifact_defines_it() {
    let lib = library(None);
    let symbol = link_symbol(&KName::from_string("helper"));
    assert_eq!(symbol, "helper");
    let far_ft = {
        let far = lib.functions.iter().find(|f| f.name == "helper").unwrap();
        lib.func_types[far.ty.as_usize()].clone()
    };
    assert_eq!(
        importable_symbols(&[dep(lib.clone(), "a.bin")]).get(&symbol),
        Some(&ArtifactLookup::Import(far_ft))
    );
    assert_eq!(
        importable_symbols(&[dep(lib.clone(), "a.bin"), dep(library(Some(1)), "b.bin")])
            .get(&symbol),
        Some(&ArtifactLookup::Ambiguous),
        "two definers are never resolved by picking one"
    );
    assert_eq!(
        importable_symbols(&[dep(lib.clone(), "a.bin")]).get("other"),
        None,
        "a symbol no artifact carries is compiled locally"
    );
    // A far definition no other module may link is compiled locally.
    let mut internal = lib;
    for f in &mut internal.functions {
        if f.name == "helper" {
            f.linkage = Linkage::Internal;
        }
    }
    assert_eq!(
        importable_symbols(&[dep(internal, "a.bin")]).get(&symbol),
        None
    );
}

#[test]
fn a_tmbc_container_is_refused_by_name_at_decode() {
    let lib = library(None);
    let module_bytes = trust_ir::binary::serialize_module(&lib).expect("serialize lib module");
    let decoded = LinkedArtifact::decode("lib.bin", &module_bytes).expect("plain bytes decode");
    assert_eq!(decoded.module.stable_digest(), lib.stable_digest());
    let mut tmbc = b"tMBC".to_vec();
    tmbc.extend_from_slice(&1u32.to_le_bytes());
    tmbc.extend_from_slice(&module_bytes);
    let err = LinkedArtifact::decode("lib.tmbc", &tmbc).expect_err("a container is refused");
    assert!(err.contains("`.tmbc` container"), "{err}");
}

// ---------------------------------------------------------------------------
// WS6.8 review: a transitive build, and a client that bypassed the table
// ---------------------------------------------------------------------------

/// REVIEW (legitimate composition wrongly refused). A dependency that was
/// itself linked against `lib` DECLARES `helper` — that declaration is its own
/// import of the symbol, not a second definition. Counting it as a carrier
/// refused every import chain longer than one edge (`mid` -> `lib`, then a
/// client linked against both) as `SymbolAmbiguous`, although the consumer
/// binds the call edge to the one dependency that defines the symbol.
#[test]
fn a_declaration_in_another_artifact_is_not_a_second_definer() {
    let lib = library(None);
    let far_ft = {
        let far = lib.functions.iter().find(|f| f.name == "helper").unwrap();
        lib.func_types[far.ty.as_usize()].clone()
    };
    // `mid`: a module that imported `helper` from `lib` (one import row, one
    // typed body-less declaration).
    let mut mid = client_shell();
    mid.name = "mid".to_string();
    link_imported_modules(&mut mid, &[dep(lib.clone(), "lib.bin")], &wanted())
        .expect("mid links against lib");
    assert!(mid
        .functions
        .iter()
        .any(|f| f.name == "helper" && f.is_declaration()));
    let linked = [dep(lib.clone(), "lib.bin"), dep(mid.clone(), "mid.bin")];
    assert_eq!(
        importable_symbols(&linked).get("helper"),
        Some(&ArtifactLookup::Import(far_ft)),
        "lib DEFINES helper; mid only declares it"
    );
    // The producer binds the client to `lib`, and the consumer agrees.
    let mut client = client_shell();
    let report = link_imported_modules(&mut client, &linked, &wanted())
        .expect("the client links against lib and mid");
    assert!(report.declined.is_empty(), "{report:?}");
    assert_eq!(report.proved.len(), 1, "{report:?}");
    assert_eq!(client.imports.len(), 1, "only lib is cited");
    assert_eq!(client.imports[0].digest, lib.stable_digest());
    assert!(linked_verdict(&client, &[lib, mid]).is_empty());

    // Two DEFINITIONS are still never resolved by picking one.
    assert_eq!(
        importable_symbols(&[dep(library(None), "a.bin"), dep(library(Some(1)), "b.bin")])
            .get("helper"),
        Some(&ArtifactLookup::Ambiguous)
    );
}

/// REVIEW (wrong emitted module). The emitter declares every symbol a linked
/// artifact defines; a client that nonetheless DEFINES one (any path that
/// bypassed the import table) is a duplicate definition at native link time,
/// and no import row makes that sound. Before the review, a client with
/// nothing wanted was written unchanged with both definitions in place.
#[test]
fn a_client_that_defines_an_artifact_symbol_is_refused() {
    let lib = library(None);
    let mut client = emit_trust_ir(&[helper_decl(Some(7))]).expect("client lowers");
    client.target_info = Some(target());
    assert!(client
        .functions
        .iter()
        .any(|f| f.name == "helper" && !f.is_declaration()));
    let before = client.clone();
    let err = link_imported_modules_for_cli(&mut client, &[dep(lib, "lib.bin")], &[])
        .expect_err("a second definition of an artifact symbol must refuse");
    assert!(
        err.contains("the client DEFINES `helper`, which a linked artifact already defines"),
        "{err}"
    );
    assert_eq!(client, before, "nothing is written");

    // MUTATION CONTROL: the same client against an artifact that defines
    // `helper` with INTERNAL linkage (nobody else can link it) is not a
    // collision.
    let mut internal = library(None);
    for f in &mut internal.functions {
        f.linkage = Linkage::Internal;
    }
    let mut client = before.clone();
    link_imported_modules_for_cli(&mut client, &[dep(internal, "lib.bin")], &[])
        .expect("an unexported far definition does not collide");
}

/// `spare(y : UInt32) : UInt32 := y` as its own artifact: a dependency that
/// defines nothing the client wants.
fn spare_artifact() -> Module {
    let decl = IRDecl {
        name: KName::from_string("spare"),
        ..helper_decl(None)
    };
    let mut module = emit_trust_ir(&[decl]).expect("spare lowers");
    module.name = "spare".to_string();
    module.target_info = Some(target());
    module
}

/// WS6.8: review — a supplied artifact nothing is imported from is NOT a
/// dependency, so it gets no import row (the producer used to intern a row
/// for EVERY supplied artifact as soon as one symbol was wanted, recording a
/// dependency the client does not have). It is still CHECKED: a supplied
/// artifact for another target refuses the link rather than being ignored.
#[test]
fn a_supplied_artifact_nothing_is_imported_from_is_checked_but_not_recorded() {
    let lib = library(None);
    let spare = spare_artifact();
    for linked in [
        vec![dep(lib.clone(), "lib.bin"), dep(spare.clone(), "spare.bin")],
        vec![dep(spare.clone(), "spare.bin"), dep(lib.clone(), "lib.bin")],
    ] {
        let mut client = client_shell();
        let report =
            link_imported_modules(&mut client, &linked, &wanted()).expect("links against lib");
        assert_eq!(report.proved.len(), 1, "{report:?}");
        assert_eq!(report.imports.len(), 1, "{report:?}");
        assert_eq!(client.imports.len(), 1, "only the artifact used is a row");
        assert_eq!(client.imports[0].digest, lib.stable_digest());
        assert!(linked_verdict(&client, &[lib.clone(), spare.clone()]).is_empty());
    }

    // MUTATION CONTROL: the unused artifact built for no recorded target is
    // still refused by name, and the client is left as it was.
    let mut foreign = spare;
    foreign.target_info = None;
    let mut client = client_shell();
    let before = client.clone();
    let err = link_imported_modules(
        &mut client,
        &[dep(lib, "lib.bin"), dep(foreign, "spare.bin")],
        &wanted(),
    )
    .expect_err("a wrong artifact on the command line refuses");
    assert!(
        matches!(
            err,
            LinkError::Artifact { ref path, why: LinkRefusal::TargetMismatch } if path == "spare.bin"
        ),
        "{err:?}"
    );
    assert_eq!(client, before);
}

#[test]
fn source_instance_environment_preserves_inheritance_only_for_the_actual_field() {
    use clean_kernel::{Declaration, Environment, Level};
    let lib = library(Some(3));
    for operation in ["UInt32.add", "UInt32.sub"] {
        let mut env = Environment::with_prelude();
        let u = Expr::const_str("UInt32");
        env.add_decl(Declaration::Definition {
            name: KName::from_string("Client.namedDictionary"),
            level_params: vec![],
            type_: Expr::apps(
                Expr::const_(KName::from_string("HAdd"), vec![Level::zero(); 3]),
                [u.clone(), u.clone(), u.clone()],
            ),
            value: Expr::apps(
                Expr::const_(KName::from_string("HAdd.mk"), vec![Level::zero(); 3]),
                [u.clone(), u.clone(), u.clone(), Expr::const_str(operation)],
            ),
            is_reducible: true,
        })
        .unwrap();
        let source = Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::apps(
                Expr::const_(KName::from_string("HAdd.hAdd"), vec![Level::zero(); 3]),
                [
                    u.clone(),
                    u.clone(),
                    u.clone(),
                    Expr::const_str("Client.namedDictionary"),
                    Expr::bvar(0),
                    Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(3)),
                ],
            ),
        );
        env.add_decl(Declaration::Definition {
            name: KName::from_string("helper"),
            level_params: vec![],
            type_: Expr::arrow(u.clone(), u),
            value: source.clone(),
            is_reducible: true,
        })
        .expect("checked client source");
        let wanted = [WantedSymbol::with_source("helper", source)];
        let mut client = client_shell();
        let report = link_imported_modules_with_environment(
            &mut client,
            &[dep(lib.clone(), "lib.bin")],
            &wanted,
            Some(&env),
        )
        .unwrap();
        if operation == "UInt32.add" {
            assert_eq!(report.proved.len(), 1, "{report:?}");
            assert_eq!(restatement_rows(&client), 1);
            assert!(linked_verdict(&client, std::slice::from_ref(&lib)).is_empty());
        } else {
            assert!(report.proved.is_empty(), "{report:?}");
            assert_eq!(
                report.identity_only[0].1,
                LinkRefusal::FarComparandDisagreesWithClientSource
            );
            assert_eq!(restatement_rows(&client), 0);
            assert!(client.proof_certificates.is_empty());
        }
    }
}
