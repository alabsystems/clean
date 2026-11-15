// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! v41 CROSS-CRATE IDENTITY (gap G13).
//!
//! Before this batch a `Module` was flat and self-contained: no crate identity,
//! no dependency list, and no reference able to name an entity in another
//! module. `ProofEvidence::InheritedFromCallee` was two module-local `u32`s the
//! validator forced to resolve HERE, so cross-crate proof inheritance could not
//! be SPELLED, and `FunctionSummary.proved` was a bare bool with nothing naming
//! what established it.
//!
//! Every test below is written as a CONTRAST or a REFUSAL, because each of the
//! failure modes this batch guards against compiles cleanly.

use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::proof::{ProofCertificate, ProofDigest, ProofEvidence};
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer};

fn import(name: &str, byte: u8) -> ModuleImport {
    ModuleImport::new(name, ProofDigest::sha256([byte; 32]))
}

/// A module carrying every new carrier at once: an interned import table, a
/// summary whose `proved` bit is authenticated across the boundary, and a
/// certificate inheriting a proof from another crate.
fn cross_crate_module() -> Module {
    let mut m = Module::new("importer");
    let dep = m
        .intern_import(import("core_shim", 0xA1).with_producer(Producer::Clean))
        .expect("Module::intern_import: test fixture");

    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let summary = FunctionSummary::new()
        .proved()
        .backed_by(ExternRef::new(dep, "_ZN9core_shim11checked_addE").relying_on(ProofId::new(7)));
    // A bodyless external DECLARATION: this module's own handle on the
    // separately compiled callee. `name` is the LINK-TIME SYMBOL v41 ratified
    // it to be — a def-path spelling here would emit an unlinkable symbol, and
    // `ExternRef::symbol` has to match what the linker will resolve.
    m.try_add_function(Function::declaration(
        FuncId::new(0),
        "_ZN9core_shim11checked_addE",
        ft,
        summary,
    ))
    .expect("Module::try_add_function: test fixture");

    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(0),
            external: Some(
                ExternRef::new(dep, "_ZN9core_shim11checked_addE").relying_on(ProofId::new(7)),
            ),
        },
        assurance: None,
    });
    m
}

#[test]
fn cross_crate_identity_round_trips_all_four_formats() {
    let m = cross_crate_module();

    let back = deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture"))
        .expect("binary");
    assert_eq!(back, m, "binary");
    assert_eq!(back.imports.len(), 1);
    assert_eq!(back.imports[0].producer, Some(Producer::Clean));
    assert_eq!(
        back.functions[0]
            .summary
            .as_ref()
            .and_then(|s| s.backed_by.as_ref())
            .and_then(|r| r.obligation),
        Some(ProofId::new(7)),
        "the reference authenticating `proved` must survive binary"
    );

    // Text carries `Function.summary` since roadmap WS4.4 (F-064): the
    // `proved` claim and its `backed_by` citation travel as a `; #summary:`
    // / `; #backed-by:` block. (Between WS4.2 and WS4.4 text REFUSED such a
    // module rather than dropping them; before WS4.2 it dropped them.)
    assert_eq!(trust_ir::format::text_losses(&m), vec![]);
    let text = trust_ir::format::canonical_checked(&m).expect("loss-free since WS4.4");
    let re = trust_ir::parser::parse_module(&text).expect("text parses");
    assert_eq!(re, trust_ir::format::canonicalize(&m));
    assert_eq!(
        re.functions[0]
            .summary
            .as_ref()
            .and_then(|s| s.backed_by.as_ref())
            .and_then(|r| r.obligation),
        Some(ProofId::new(7)),
        "the reference authenticating `proved` must survive text"
    );
    assert_eq!(
        re.imports, m.imports,
        "the import table is the referent every ExternRef resolves against — \
         dropping it in text would leave every reference dangling"
    );
    // The EVIDENCE is carried, and must be.
    match &re.proof_certificates[0].evidence {
        ProofEvidence::InheritedFromCallee {
            external: Some(reference),
            ..
        } => {
            assert_eq!(reference.module, ImportId::new(0));
            assert_eq!(reference.symbol, "_ZN9core_shim11checked_addE");
            assert_eq!(reference.obligation, Some(ProofId::new(7)));
        }
        other => panic!("text round trip lost the cross-crate authority: {other:?}"),
    }

    let j = serde_json::to_string(&m).unwrap();
    assert_eq!(serde_json::from_str::<Module>(&j).unwrap(), m, "json");
    let mp = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&mp).unwrap(), m, "msgpack");
}

/// The POSITIONAL-MESSAGEPACK trap, stated as a test.
///
/// `rmp_serde::to_vec` encodes structs positionally and may only skip a
/// TRAILING field. `imports` was appended after `global_asm`, so `global_asm`
/// had to lose its `skip_serializing_if` in the same change; leaving it would
/// shift the import table into the `global_asm` slot on decode.
#[test]
fn appending_imports_flipped_global_asm_to_always_emitted() {
    let mut m = Module::new("positional");
    // `global_asm` empty, `imports` non-empty: the exact shape that misdecodes
    // if the skipped field is not the trailing one.
    m.intern_import(import("dep", 0x5A))
        .expect("Module::intern_import: test fixture");
    assert!(m.global_asm.is_empty());

    let mp = rmp_serde::to_vec(&m).unwrap();
    let back: Module = rmp_serde::from_slice(&mp).unwrap();
    assert_eq!(back, m);
    assert_eq!(back.imports.len(), 1, "the import table must not shift");
    assert!(back.global_asm.is_empty());

    let json = serde_json::to_string(&m).unwrap();
    assert!(
        json.contains("\"global_asm\""),
        "`global_asm` must be ALWAYS emitted now that `imports` follows it: {json}"
    );
}

/// The local form must be BYTE-IDENTICAL to what it was before `external`
/// existed. That is what makes this widening additive rather than a v38 break.
#[test]
fn a_local_inheritance_still_writes_wire_tag_6() {
    let mut local = Module::new("m");
    local.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "p".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(1),
            obligation: ProofId::new(2),
            external: None,
        },
        assurance: None,
    });

    let mut external = local.clone();
    let dep = external
        .intern_import(import("dep", 0x11))
        .expect("Module::intern_import: test fixture");
    external.proof_certificates[0].evidence = ProofEvidence::InheritedFromCallee {
        callee: FuncId::new(1),
        obligation: ProofId::new(2),
        external: Some(ExternRef::new(dep, "sym")),
    };

    let local_bytes = serialize_module(&local).expect("serialize_module: test fixture");
    let external_bytes = serialize_module(&external).expect("serialize_module: test fixture");
    assert!(
        find_subsequence(&local_bytes, &[6u8, 1, 2]).is_some(),
        "the local form must still write tag 6 followed by its two varints"
    );
    assert!(
        find_subsequence(&external_bytes, &[8u8, 1, 2]).is_some(),
        "the cross-crate form must write its OWN tag 8 — a v38 reader has to be \
         able to refuse it, and an unknown tag is the only refusal it has"
    );
    assert_ne!(local_bytes, external_bytes);
}

/// A v38-LABELLED blob carrying tag 8 must be REFUSED, not taken as
/// well-formed. The version gate is the whole point: an unknown tag fails
/// closed on its own, but tag 8 is not unknown to this reader.
#[test]
fn a_v38_labelled_blob_refuses_the_cross_crate_tag() {
    // Deliberately function-free and global-free: the only version-gated read
    // between the header and the certificate is the evidence tag itself, so the
    // refusal below cannot be some other desync wearing a disguise.
    let mut m = Module::new("relabelled");
    let dep = m
        .intern_import(import("dep", 0x22))
        .expect("Module::intern_import: test fixture");
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "p".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(0),
            external: Some(ExternRef::new(dep, "sym")),
        },
        assurance: None,
    });

    let mut bytes = serialize_module(&m).expect("serialize_module: test fixture");
    assert!(
        deserialize_module(&bytes).is_ok(),
        "the v41 blob itself must decode — otherwise the relabelling below \
         proves nothing"
    );
    bytes[8..12].copy_from_slice(&38u32.to_le_bytes());
    let err = deserialize_module(&bytes)
        .expect_err("a v38-labelled blob must not decode a v41 cross-crate inheritance");
    assert!(
        format!("{err:?}").contains("InvalidTag"),
        "expected a tag refusal, got {err:?}"
    );
}

/// A content digest may never hash two meanings equal. "Discharged in this
/// module" and "discharged in crate X" are different claims.
#[test]
fn the_module_digest_separates_local_from_cross_crate_inheritance() {
    let mut local = Module::new("m");
    local.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "p".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(3),
            external: None,
        },
        assurance: None,
    });

    let mut external = local.clone();
    let dep = external
        .intern_import(import("dep", 0x33))
        .expect("Module::intern_import: test fixture");
    external.proof_certificates[0].evidence = ProofEvidence::InheritedFromCallee {
        callee: FuncId::new(0),
        obligation: ProofId::new(3),
        external: Some(ExternRef::new(dep, "sym").relying_on(ProofId::new(3))),
    };

    assert_ne!(local.stable_digest(), external.stable_digest());

    // And two imports that differ ONLY in digest are different dependencies.
    let mut other = external.clone();
    other.imports[0].digest = ProofDigest::sha256([0x44; 32]);
    assert_ne!(
        external.stable_digest(),
        other.stable_digest(),
        "the digest is the identity of the import — changing it must change the \
         module's identity, or the pin is decorative"
    );
}

/// `imports` is content-interned in the manner of `universes`/`predicates`:
/// identity is the whole `(name, digest, producer)` triple.
#[test]
fn imports_are_content_interned_on_the_whole_triple() {
    let mut m = Module::new("interning");
    let a = m
        .intern_import(import("dep", 0x01))
        .expect("Module::intern_import: test fixture");
    let again = m
        .intern_import(import("dep", 0x01))
        .expect("Module::intern_import: test fixture");
    assert_eq!(a, again, "the same artifact must intern to one id");
    assert_eq!(m.imports.len(), 1);

    // A different digest is a different DEPENDENCY, not the same one restated.
    let rebuilt = m
        .intern_import(import("dep", 0x02))
        .expect("Module::intern_import: test fixture");
    assert_ne!(a, rebuilt);

    // An UNRECORDED producer is not the same claim as a recorded one.
    let recorded = m
        .intern_import(import("dep", 0x01).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    assert_ne!(a, recorded);
    assert_eq!(m.imports.len(), 3);

    assert_eq!(m.import(a).map(|i| i.name.as_str()), Some("dep"));
    assert!(
        m.import(ImportId::new(99)).is_none(),
        "a dangling import id must resolve to nothing — a consumer that cannot \
         resolve the referent cannot authenticate the edge"
    );
}

fn find_subsequence(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}
