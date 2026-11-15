// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adversarial coverage for `Module::executable_content_digest_v1`.
//!
//! The identity deliberately closes over codegen-facing IR (including on-IR
//! proof annotations and the v41 ABI/linkage residue) while remaining
//! independent of the three module-level proof sidecars and of the codegen
//! license (`Function.body_gate` / `Function.display_path`), which is a
//! verdict ABOUT the image and must not move it. These tests keep every half
//! of that boundary explicit.

use trust_ir::proof::ProofContext;
use trust_ir::{
    BinOp, Block, BlockId, BodyGate, CallingConv, Constant, Endianness, FuncAttrs, FuncId, FuncTy,
    Function, FunctionSummary, Global, Inst, InstrNode, Linkage, Module, ModuleImport,
    ObligationDiagnostic, ObligationKind, ParamAttrs, Pred, PredId, Producer, ProofAnnotation,
    ProofCertificate, ProofDigest, ProofEvidence, ProofFormula, ProofId, ProofObligation,
    ProofStatus, ScopeData, SourceProvenance, SourceSpan, SpecModule, StructPassingPolicy,
    TargetInfo, TupleLayoutDescriptor, Ty, TyId, ValueId, Visibility,
};
use trust_ir::{
    inst::{BindingFrameDef, BindingSlot},
    value::BindingFrameId,
};

const BACKING_PROOF: u32 = 7;

fn value(base: u32, offset: u32) -> ValueId {
    ValueId::new(base + offset)
}

fn formula(payload: &str) -> ProofFormula {
    ProofFormula {
        schema: "smtlib2".into(),
        payload: payload.into(),
        smtlib: Some(payload.into()),
        sort: Some("Bool".into()),
        bindings: Vec::new(),
    }
}

/// A non-trivial module with an import, canonicalizable sparse SSA, debug and
/// source provenance, refinement facts, codegen hints, and populated proof
/// sidecars. `value_base` and `reverse_blocks` alter only incidental body
/// representation and therefore canonicalize to the same executable image.
fn fixture(value_base: u32, reverse_blocks: bool) -> Module {
    let mut module = Module::new("executable-content-fixture");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.files.push("src/fixture.rs".into());

    let main_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let import_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.types.push(Ty::I64);
    module.predicates.push(Pred::NonZero);
    module.types.push(Ty::Refine(TyId::new(0), PredId::new(0)));
    module.globals.push(Global {
        name: "EXECUTABLE_GLOBAL".into(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(41)),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });

    let entry_param = value(value_base, 1);
    let continuation_param = value(value_base, 2);
    let constant_result = value(value_base, 3);
    let add_result = value(value_base, 4);
    let call_result = value(value_base, 5);

    let mut entry = Block::new(BlockId::new(0)).with_param(entry_param, Ty::I64);
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(constant_result)
        .with_span(SourceSpan {
            file: 0,
            line: 10,
            col: 5,
        })
        .with_scope(0),
    );
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: entry_param,
            rhs: constant_result,
        })
        .with_result(add_result)
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::ValueRange { lo: 1, hi: 100 })
        .with_proof(ProofAnnotation::ProofRef(ProofId::new(BACKING_PROOF))),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![add_result],
    }));

    let mut continuation = Block::new(BlockId::new(1)).with_param(continuation_param, Ty::I64);
    continuation.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![continuation_param],
        })
        .with_result(call_result)
        .with_proof_context(ProofContext {
            assumes: vec![ProofId::new(BACKING_PROOF)],
            establishes: vec![ProofId::new(BACKING_PROOF)],
        }),
    );
    continuation.body.push(InstrNode::new(Inst::Return {
        values: vec![call_result],
    }));

    let mut main = Function::new(FuncId::new(0), "entry", main_ty, BlockId::new(0));
    if reverse_blocks {
        main.blocks.extend([continuation, entry]);
    } else {
        main.blocks.extend([entry, continuation]);
    }
    main.calling_conv = CallingConv::Rust;
    main.linkage = Linkage::External;
    main.attrs = FuncAttrs {
        inlinehint: true,
        params: vec![ParamAttrs {
            align: Some(8),
            ..ParamAttrs::default()
        }],
        ..FuncAttrs::default()
    };
    main.proofs.extend([
        ProofAnnotation::Pure,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Deterministic,
        ProofAnnotation::ParallelMap,
        ProofAnnotation::BoundedLoop(64),
    ]);
    main.value_names = Some(vec![
        (entry_param, "argument".into()),
        (add_result, "sum".into()),
        (continuation_param, "continued".into()),
    ]);
    main.scopes = Some(vec![ScopeData {
        parent: None,
        span: Some(SourceSpan {
            file: 0,
            line: 9,
            col: 1,
        }),
        inlined_at: None,
    }]);
    main.producer = Some(Producer::Other("fixture-producer".into()));
    main.source_provenance = Some(SourceProvenance {
        schema: 1,
        compiler_source_digest: ProofDigest::sha256([0x11; 32]),
        semantic_body_digest: ProofDigest::sha256([0x22; 32]),
        binding_digest: ProofDigest::sha256([0x33; 32]),
        loops: vec![],
    });

    let mut import = Function::new(FuncId::new(1), "runtime_import", import_ty, BlockId::new(0));
    import.calling_conv = CallingConv::C;
    import.linkage = Linkage::External;
    import.attrs.cold = true;
    import.summary = Some(FunctionSummary {
        requires: vec![formula("(>= x 0)")],
        ensures: vec![formula("(>= result x)")],
        params: vec!["x".into()],
        proved: false,
        decreases: Vec::new(),
        backed_by: None,
        effects: None,
    });

    module.functions.extend([main, import]);
    let obligation = ProofObligation::new(
        ProofId::new(BACKING_PROOF),
        ObligationKind::ArithmeticSafety,
        ProofStatus::Pending,
        "the addition does not overflow",
    )
    .with_function(FuncId::new(0))
    .with_formula(formula("(bvadd_no_overflow x 1)"));
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(BACKING_PROOF),
        prover: "fixture-prover".into(),
        evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),
        assurance: None,
    });
    module.obligation_diagnostics.push(
        ObligationDiagnostic::error(ProofId::new(BACKING_PROOF), "pending proof")
            .with_location(SourceSpan {
                file: 0,
                line: 11,
                col: 9,
            })
            .with_detail("model: x = max_i64"),
    );
    let mut spec = SpecModule::new("RetainedSpec");
    spec.actions.push("Step".into());
    module.spec_modules.push(spec);
    module
}

/// A frame lifecycle whose SSA ids can be dense or arbitrarily sparse. Frame
/// handles are ordinary `ValueId` operands, including on `CloseFrame` even
/// though that instruction itself is void.
fn binding_frame_fixture(value_base: u32) -> Module {
    let mut module = Module::new("binding-frame-executable-content");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let argument = value(value_base, 0);
    let opened_frame = value(value_base, 1);
    let bound_frame = value(value_base, 2);
    let loaded_value = value(value_base, 3);
    let mut block = Block::new(BlockId::new(0)).with_param(argument, Ty::I64);
    block.body.push(
        InstrNode::new(Inst::OpenFrame {
            def: BindingFrameDef::new(
                BindingFrameId::new(0),
                "argument-frame",
                vec![BindingSlot::new("argument", Ty::I64)],
            ),
        })
        .with_result(opened_frame),
    );
    block.body.push(
        InstrNode::new(Inst::BindSlot {
            frame: opened_frame,
            slot: 0,
            value: argument,
        })
        .with_result(bound_frame),
    );
    block.body.push(
        InstrNode::new(Inst::LoadSlot {
            frame: bound_frame,
            slot: 0,
            ty: Ty::I64,
        })
        .with_result(loaded_value),
    );
    block
        .body
        .push(InstrNode::new(Inst::CloseFrame { frame: bound_frame }));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![loaded_value],
    }));
    let mut function = Function::new(FuncId::new(0), "frame", signature, BlockId::new(0));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn assert_digest_changes(base: &Module, label: &str, mutate: impl FnOnce(&mut Module)) {
    let expected = base.executable_content_digest_v1();
    let mut changed = base.clone();
    mutate(&mut changed);
    assert_ne!(
        changed.executable_content_digest_v1(),
        expected,
        "{label} must change executable-content identity"
    );
}

/// The mutation is invisible to the executable identity, and the exact
/// structural identity witnesses that the module really did change.
fn assert_digest_unchanged(base: &Module, label: &str, mutate: impl FnOnce(&mut Module)) {
    let expected = base.executable_content_digest_v1();
    let mut changed = base.clone();
    mutate(&mut changed);
    assert_eq!(
        changed.executable_content_digest_v1(),
        expected,
        "{label} must not change executable-content identity"
    );
    assert_ne!(
        changed.stable_digest(),
        base.stable_digest(),
        "{label}: the adversary must really have changed the module"
    );
}

fn gated() -> BodyGate {
    BodyGate::Gated {
        authority: "trust-verifier".into(),
        evidence: None,
    }
}

fn proof_carrier(module: &mut Module) -> &mut InstrNode {
    module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find(|node| {
            node.proofs
                .iter()
                .any(|proof| matches!(proof, ProofAnnotation::ProofRef(_)))
        })
        .expect("fixture has one on-node ProofRef carrier")
}

#[test]
fn executable_content_digest_is_canonical_and_deterministic() {
    let stored = fixture(10, false);
    let mut sparse_and_reordered = fixture(1_000, true);
    sparse_and_reordered.functions[0]
        .attrs
        .params
        .push(ParamAttrs::default());

    let expected = stored.executable_content_digest_v1();
    assert_eq!(expected, stored.executable_content_digest_v1());
    assert_eq!(
        expected,
        sparse_and_reordered.executable_content_digest_v1(),
        "block storage order and SSA numbering are canonicalized"
    );
    assert_ne!(
        stored.stable_digest(),
        sparse_and_reordered.stable_digest(),
        "the full structural digest intentionally observes incidental storage"
    );
}

#[test]
fn binding_frame_operands_are_canonicalized_in_executable_identity() {
    let dense = binding_frame_fixture(0);
    let sparse = binding_frame_fixture(10_000);

    assert_eq!(
        dense.executable_content_digest_v1(),
        sparse.executable_content_digest_v1(),
        "BindSlot, LoadSlot, and CloseFrame frame operands must use the canonical ValueId map",
    );
    assert_ne!(
        dense.stable_digest(),
        sparse.stable_digest(),
        "the raw structural identity must prove that the fixture really changed SSA ids",
    );
}

#[test]
fn every_module_proof_sidecar_mutation_is_ignored() {
    let base = fixture(10, false);
    let expected = base.executable_content_digest_v1();

    let mut certified = base.clone();
    let obligation = &mut certified.proof_obligations[0];
    obligation.id = ProofId::new(999);
    obligation.kind = ObligationKind::PanicFreedom;
    obligation.status = ProofStatus::Certified;
    obligation.description = "a completely different proof claim".into();
    obligation.formula = Some(formula("false"));
    obligation.function = Some(FuncId::new(1));
    certified.proof_certificates[0] = ProofCertificate {
        obligation: ProofId::new(999),
        prover: "different-prover".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![0xaa; 64],
            context: vec![0xbb; 32],
            lineage: ProofDigest::sha256([0xcc; 32]),
            kernel_recheck: None,
        },
        assurance: None,
    };
    certified.obligation_diagnostics[0] =
        ObligationDiagnostic::note(ProofId::new(999), "certified with a different diagnostic")
            .with_detail("proof-only detail");

    assert_eq!(expected, certified.executable_content_digest_v1());
    assert_ne!(
        base.stable_digest(),
        certified.stable_digest(),
        "the adversary really changed the ordinary full-module identity"
    );

    let mut stripped = base.clone();
    stripped.proof_obligations.clear();
    stripped.proof_certificates.clear();
    stripped.obligation_diagnostics.clear();
    assert_eq!(
        expected,
        stripped.executable_content_digest_v1(),
        "the executable identity must not require its ProofRef sidecar to be present"
    );
}

#[test]
fn proof_ref_position_presence_and_id_remain_identity_bearing() {
    let mut base = fixture(10, false);
    base.proof_obligations.clear();
    base.proof_certificates.clear();
    base.obligation_diagnostics.clear();
    let expected = base.executable_content_digest_v1();

    let mut changed_id = base.clone();
    let proof = proof_carrier(&mut changed_id)
        .proofs
        .iter_mut()
        .find(|proof| matches!(proof, ProofAnnotation::ProofRef(_)))
        .expect("carrier contains ProofRef");
    *proof = ProofAnnotation::ProofRef(ProofId::new(BACKING_PROOF + 1));
    assert_ne!(expected, changed_id.executable_content_digest_v1());

    let mut removed = base.clone();
    proof_carrier(&mut removed)
        .proofs
        .retain(|proof| !matches!(proof, ProofAnnotation::ProofRef(_)));
    assert_ne!(expected, removed.executable_content_digest_v1());

    let mut moved = base.clone();
    proof_carrier(&mut moved)
        .proofs
        .retain(|proof| !matches!(proof, ProofAnnotation::ProofRef(_)));
    moved.functions[0]
        .proofs
        .push(ProofAnnotation::ProofRef(ProofId::new(BACKING_PROOF)));
    assert_ne!(
        expected,
        moved.executable_content_digest_v1(),
        "the same ProofRef at a different IR site must not alias"
    );
}

#[test]
fn executable_and_codegen_relevant_mutations_change_identity() {
    let base = fixture(10, false);

    assert_digest_changes(&base, "target layout", |module| {
        module.target_info.as_mut().unwrap().pointer_size = 4;
    });
    assert_digest_changes(&base, "type table", |module| {
        module.types[0] = Ty::I32;
    });
    assert_digest_changes(&base, "refinement predicate", |module| {
        module.predicates[0] = Pred::Top;
    });
    assert_digest_changes(&base, "global name", |module| {
        module.globals[0].name.push_str("_renamed");
    });
    assert_digest_changes(&base, "global initializer", |module| {
        module.globals[0].initializer = Some(Constant::Int(42));
    });
    assert_digest_changes(&base, "global align", |module| {
        module.globals[0].align = Some(64);
    });
    assert_digest_changes(&base, "function name", |module| {
        module.functions[0].name.push_str("_renamed");
    });
    assert_digest_changes(&base, "function signature", |module| {
        module.func_types[0].returns[0] = Ty::I32;
    });
    assert_digest_changes(&base, "function body", |module| {
        let node = &mut module.functions[0].blocks[0].body[1];
        let Inst::BinOp { op, .. } = &mut node.inst else {
            panic!("fixture body changed")
        };
        *op = BinOp::Sub;
    });
    assert_digest_changes(&base, "function attributes", |module| {
        module.functions[0].attrs.inlinehint = false;
    });
    assert_digest_changes(&base, "calling convention", |module| {
        module.functions[0].calling_conv = CallingConv::Fast;
    });
    assert_digest_changes(&base, "import declaration", |module| {
        module.functions[1].attrs.cold = false;
    });
    assert_digest_changes(&base, "instruction codegen annotation", |module| {
        let proofs = &mut module.functions[0].blocks[0].body[1].proofs;
        proofs[0] = ProofAnnotation::Wrapping;
    });
    assert_digest_changes(&base, "function codegen annotation payload", |module| {
        let proof = module.functions[0]
            .proofs
            .iter_mut()
            .find(|proof| matches!(proof, ProofAnnotation::BoundedLoop(_)))
            .unwrap();
        *proof = ProofAnnotation::BoundedLoop(65);
    });

    // v41 ABI/linkage residue: everything a linker or code generator acts on
    // stays identity-bearing, even though it shares the v41 header with the
    // (non-identity-bearing) codegen license.
    for linkage in [
        Linkage::AvailableExternally,
        Linkage::ExternalWeak,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        assert_digest_changes(&base, "function linkage", |module| {
            module.functions[0].linkage = linkage;
        });
    }
    assert_digest_changes(&base, "naked function attribute", |module| {
        module.functions[0].attrs.naked = true;
    });
    assert_digest_changes(&base, "target features", |module| {
        module.functions[0]
            .attrs
            .target_features
            .push("neon".into());
    });
    assert_digest_changes(&base, "global section", |module| {
        module.globals[0].section = Some(".rodata.x".into());
    });
    assert_digest_changes(&base, "global visibility", |module| {
        module.globals[0].visibility = Visibility::Hidden;
    });
    assert_digest_changes(&base, "global retention", |module| {
        module.globals[0].retained = true;
    });
    assert_digest_changes(&base, "global linkage", |module| {
        module.globals[0].linkage = Linkage::ExternalWeak;
    });
    assert_digest_changes(&base, "module-level global_asm", |module| {
        module.global_asm.push(".globl foo".into());
    });
    assert_digest_changes(&base, "module import table", |module| {
        module.imports.push(ModuleImport {
            name: "dependency".into(),
            digest: ProofDigest::sha256([0x55; 32]),
            producer: None,
            scheme: trust_ir::IdentityScheme::V2,
        });
    });
}

#[test]
fn codegen_license_and_display_path_are_not_identity_bearing() {
    let base = fixture(10, false);

    // On the defined entry function and on the body-less import alike.
    for index in [0usize, 1] {
        assert_digest_unchanged(&base, "ungated body", |module| {
            module.functions[index].body_gate = Some(BodyGate::Ungated);
        });
        assert_digest_unchanged(&base, "gated body", |module| {
            module.functions[index].body_gate = Some(gated());
        });
        assert_digest_unchanged(&base, "display path", |module| {
            module.functions[index].display_path = Some("crate::entry".into());
        });
        assert_digest_unchanged(&base, "gated body with display path", |module| {
            module.functions[index].body_gate = Some(gated());
            module.functions[index].display_path = Some("crate::entry".into());
        });
    }
    assert_digest_unchanged(&base, "every license shape at once", |module| {
        module.functions[0].body_gate = Some(BodyGate::Ungated);
        module.functions[0].display_path = Some("crate::entry".into());
        module.functions[1].body_gate = Some(gated());
        module.functions[1].display_path = Some("runtime::import".into());
    });
}

#[test]
fn license_strip_composes_with_other_v41_features() {
    let base = fixture(10, false);
    let mut naked = base.clone();
    naked.functions[0].attrs.naked = true;

    // `naked` forces a v41 projection; the license must still be invisible
    // inside it.
    assert_digest_unchanged(&naked, "license on a v41 image", |module| {
        module.functions[0].body_gate = Some(gated());
        module.functions[0].display_path = Some("crate::entry".into());
    });
    assert_ne!(
        naked.executable_content_digest_v1(),
        base.executable_content_digest_v1(),
        "the v41 header is identity-bearing when ABI content earns it"
    );
}

#[test]
fn conservative_non_sidecar_surfaces_remain_identity_bearing() {
    let base = fixture(10, false);

    assert_digest_changes(&base, "debug file table", |module| {
        module.files[0] = "src/other.rs".into();
    });
    assert_digest_changes(&base, "node debug span", |module| {
        module.functions[0].blocks[0].body[0]
            .span
            .as_mut()
            .unwrap()
            .line += 1;
    });
    assert_digest_changes(&base, "function summary", |module| {
        module.functions[1].summary.as_mut().unwrap().proved = true;
    });
    assert_digest_changes(&base, "function summary termination measure", |module| {
        module.functions[1]
            .summary
            .as_mut()
            .unwrap()
            .decreases
            .push(formula("(- n 1)"));
    });
    assert_digest_changes(&base, "spec module", |module| {
        module.spec_modules[0].name.push_str("Changed");
    });
    assert_digest_changes(&base, "producer provenance", |module| {
        module.functions[0].producer = Some(Producer::TrustIr);
    });
    assert_digest_changes(&base, "source provenance", |module| {
        module.functions[0]
            .source_provenance
            .as_mut()
            .unwrap()
            .compiler_source_digest = ProofDigest::sha256([0x44; 32]);
    });
    assert_digest_changes(&base, "proof context", |module| {
        let call = module.functions[0]
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.body)
            .find(|node| matches!(node.inst, Inst::Call { .. }))
            .unwrap();
        call.proof_context
            .as_mut()
            .unwrap()
            .assumes
            .push(ProofId::new(8));
    });

    // The two newest wire features, neither of which had a case here. They are
    // the ones whose omission would matter most: both raise the header past
    // v41, so both share a projection path with the codegen license — which
    // this same digest deliberately DOES strip. "Also v41+" must not become
    // "also stripped".
    //
    // v42 declared tuple layouts are concrete layout facts a consumer lays
    // bytes out from, so they are executable content.
    assert_digest_changes(&base, "v42 declared tuple layout", |module| {
        let tuple = module
            .add_type(Ty::Tuple(vec![Ty::I64, Ty::I64]))
            .expect("Module::add_type: test fixture");
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: tuple,
            size: 16,
            align: 8,
            field_offsets: vec![0, 8],
        });
    });
    // The descriptor's CONTENTS, not merely its presence: each field compared
    // against a module that already carries a descriptor for the same tuple,
    // so "the table is non-empty" cannot be what moves the digest.
    let with_tuple_layout = {
        let mut module = fixture(10, false);
        let tuple = module
            .add_type(Ty::Tuple(vec![Ty::I64, Ty::I64]))
            .expect("Module::add_type: test fixture");
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: tuple,
            size: 16,
            align: 8,
            field_offsets: vec![0, 8],
        });
        module
    };
    assert_digest_changes(&with_tuple_layout, "v42 tuple field offsets", |module| {
        module.tuple_layouts[0].field_offsets = vec![8, 0];
    });
    assert_digest_changes(&with_tuple_layout, "v42 tuple size", |module| {
        module.tuple_layouts[0].size = 24;
    });
    assert_digest_changes(&with_tuple_layout, "v42 tuple align", |module| {
        module.tuple_layouts[0].align = 16;
    });

    // v43 handles: the nominal `(name, runtime)` identity is what distinguishes
    // a handle from a same-width thin pointer, so all three of "a handle
    // appeared", "its name changed" and "its runtime changed" must move the
    // digest.
    assert_digest_changes(&base, "v43 handle in the type table", |module| {
        module
            .add_type(Ty::handle("Nat", "trust_bignum::Nat"))
            .expect("Module::add_type: test fixture");
    });
    let with_handle = {
        let mut module = fixture(10, false);
        module
            .add_type(Ty::handle("Nat", "trust_bignum::Nat"))
            .expect("Module::add_type: test fixture");
        module
    };
    let last = with_handle.types.len() - 1;
    assert_digest_changes(&with_handle, "v43 handle name", |module| {
        module.types[last] = Ty::handle("Int", "trust_bignum::Nat");
    });
    assert_digest_changes(&with_handle, "v43 handle runtime", |module| {
        module.types[last] = Ty::handle("Nat", "other_runtime::Nat");
    });
    assert_digest_changes(&with_handle, "v43 handle vs thin pointer", |module| {
        module.types[last] = Ty::Ptr;
    });
}
