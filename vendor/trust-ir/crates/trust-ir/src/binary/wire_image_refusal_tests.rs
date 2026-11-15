// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! D1a: the writer's refusal rule, stated once (`docs/SPEC_RATIFICATIONS.md`,
//! "A construct or count with no wire image is refused by the writer's own
//! arm, at every trust-ir entry point").
//!
//! A construct with no wire image is refused by the writer's own arm, through
//! `BinarySink::refuse`; a count past the format's `u32` through
//! `BinarySink::note_over_limit`. The one pre-check every entry point runs,
//! `Module::wire_image_refusal`, is that writer over a counting check sink,
//! so it cannot omit a construct the writer refuses — the drift that left
//! `Ty::Error` out of all four hand-written pre-checks this replaced. Test
//! rung: evidence on these inputs, never proof.

use super::*;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// A module whose only content is one immutable global initialized with
/// `len` zero bytes.
fn module_with_bytes(len: usize) -> Module {
    let mut module = Module::new("count-limit");
    module.globals.push(Global {
        name: "blob".into(),
        ty: Ty::U8,
        mutable: false,
        initializer: Some(Constant::Bytes {
            data: vec![0; len],
            utf8: false,
        }),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: crate::Visibility::Default,
        retained: false,
    });
    module
}

/// A module whose type table spells the producer-internal `Ty::Error` — the
/// one-line JSON edit (`"types": ["Error"]`) a decoder of JSON or MessagePack
/// admits and the binary format has no spelling for.
fn module_with_producer_internal_type() -> Module {
    let mut module = Module::new("producer-internal");
    module.types.push(Ty::Error);
    module
}

/// T-A4a (kind i). The IDENTITY walk is total over counts: a byte payload one
/// past `u32::MAX` is counted, never refused by a panic, and the count is the
/// exact `write_v64` spelling (injective past the format's limit). Only the
/// LENGTH of the payload is read; its pages are never touched, so the
/// 4 GiB `calloc` stays lazily zero-filled (peak RSS measured once and
/// recorded in the D1a commit).
#[test]
fn encoded_len_is_total_over_counts() {
    let empty = module_with_bytes(0);
    let empty_len = ModuleBinaryPlan::new(&empty).encoded_len();
    let n = u32::MAX as usize + 1;
    let big = module_with_bytes(n);
    let counted = catch_unwind(AssertUnwindSafe(|| {
        ModuleBinaryPlan::new(&big).encoded_len()
    }))
    .expect("the identity walk is total over counts");
    assert_eq!(
        counted,
        empty_len + n + encode_varint(n as u64).len() - encode_varint(0).len(),
        "the count is spelled as the v64 varint of the exact length"
    );
}

/// T-A6 (kind i, the `try_new` half). `ProjectedModuleBinaryPlan::try_new`
/// refuses a module the writer cannot encode BEFORE any byte is observable.
/// Its old hand-written pre-check omitted `Ty::Error` and returned `Ok`, so
/// the first `encoded_len` / `to_vec` on the plan panicked.
#[test]
fn try_new_refuses_a_producer_internal_type() {
    let module = module_with_producer_internal_type();
    let refusal = ProjectedModuleBinaryPlan::try_new(
        &module,
        ModuleBinaryOptions {
            body: ModuleBinaryBody::Raw,
            ..ModuleBinaryOptions::default()
        },
    )
    .err()
    .expect("a projection of a Ty::Error module is refused at construction");
    assert!(refusal.to_string().contains("Ty::Error"), "{refusal}");
}

/// T-A4b (kind ii; its failing half is T-A4a). The same over-limit count is
/// refused BY NAME by the one pre-check. (`serialize_module`'s own refusal
/// of it, without materializing 4 GiB, is T9 below.)
#[test]
fn a_count_past_the_format_is_refused_by_name() {
    let n = u32::MAX as usize + 1;
    let big = module_with_bytes(n);
    assert_eq!(
        big.wire_image_refusal(),
        Some(BinaryProjectionError::CountExceedsFormat {
            what: "Constant::Bytes data",
            count: n as u64,
        })
    );
    assert!(
        ProjectedModuleBinaryPlan::try_new(&big, ModuleBinaryOptions::default()).is_err(),
        "a projection of an over-limit module is refused at construction"
    );
    // The last count the format can carry is not a refusal.
    assert_eq!(module_with_bytes(0).wire_image_refusal(), None);
}

/// A sink that records everything, for the sink-contract tests.
#[derive(Default)]
struct RecordingSink {
    bytes: Vec<u8>,
    refusals: Vec<WireRefusal>,
    notes: Vec<(&'static str, u64)>,
}

impl BinarySink for RecordingSink {
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        self.refusals.push(refusal);
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        self.notes.push((what, count));
    }
}

/// T-A5 (kind iii, parity). `write_count` is byte-identical to the historical
/// `write_v32` spelling for every count the format carries, and past it is
/// the injective `write_v64` spelling plus a note. Mutation check: a
/// truncating `n as u32` aliases `2^32` onto `0` and the decode assertion goes
/// red; dropping the note leaves `notes` empty.
#[test]
fn write_count_is_the_v32_spelling_and_injective_past_it() {
    for n in [0_u32, 1, 127, 128, 16_383, 16_384, u32::MAX] {
        let mut counted = RecordingSink::default();
        write_count(&mut counted, "n", n as usize);
        let mut historical = RecordingSink::default();
        write_v32(&mut historical, n);
        assert_eq!(counted.bytes, historical.bytes, "{n}");
        assert_eq!(counted.bytes, encode_varint(u64::from(n)), "{n}");
        assert!(counted.notes.is_empty(), "{n}: within the format");
    }
    let past = u64::from(u32::MAX) + 1;
    let mut counted = RecordingSink::default();
    write_count(&mut counted, "n", past as usize);
    assert_eq!(counted.bytes, encode_varint(past));
    assert_eq!(
        decode_varint(&counted.bytes),
        Ok((past, counted.bytes.len()))
    );
    assert_eq!(counted.notes, vec![("n", past)]);
    assert!(counted.refusals.is_empty());
}

/// T-A5b (kind iii). The forwarding sinks forward BOTH hooks: a forwarder
/// that inherited a no-op default would silently drop a refusal (the hooks
/// have no default body, so a forwarder that omits one does not compile).
#[test]
fn a_buffered_blob_sink_forwards_the_refusal() {
    let mut inner = RecordingSink::default();
    {
        let mut buffered = BufferedBinarySink::<_, BINARY_STREAM_BUFFER_BYTES>::new(&mut inner);
        buffered.refuse(WireRefusal::ProducerInternalType);
        buffered.note_over_limit("table", u64::from(u32::MAX) + 1);
        buffered.finish();
    }
    assert_eq!(inner.refusals, vec![WireRefusal::ProducerInternalType]);
    assert_eq!(inner.notes, vec![("table", u64::from(u32::MAX) + 1)]);
}

fn function_with_inlined_scope(id: u32) -> Function {
    let mut function = Function::new(
        FuncId::new(id),
        "inlined",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    function.scopes = Some(vec![
        ScopeData::new(None, None),
        ScopeData {
            parent: Some(0),
            span: None,
            inlined_at: Some(crate::value::InlinedAt {
                span: crate::value::SourceSpan {
                    file: 0,
                    line: 1,
                    col: 1,
                },
                callee: "callee".into(),
            }),
        },
    ]);
    function
}

fn bound_certificate(obligation: u32) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(obligation),
        prover: "fixture".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage: ProofDigest::sha256([1; 32]),
            kernel_recheck: Some(crate::CleanCicKernelRecheck {
                module: "M".into(),
                theorems: vec![],
                anchor: "a".into(),
                allowed_axioms: vec![],
                binding: Some(Box::new(crate::CertificateBinding::new(
                    ProofDigest::sha256([2; 32]),
                    ProofDigest::sha256([3; 32]),
                ))),
            }),
        },
        assurance: None,
    }
}

/// T-A6 (kind ii; its failing half is `try_new_refuses_a_producer_internal_type`
/// and the bundle and CLI kind-(i) tests). Per carrier, the one pre-check
/// names it, `try_new` refuses with the SAME refusal, and every identity
/// entry still panics on it (R1). A module carrying every carrier reports
/// them in the pinned precedence — scope chain, completeness, `Ty::Error` —
/// the order trust's `native_request_metadata_tests` and ty's wire-identity
/// tests pin. A certificate binding is no longer a carrier of a refusal: wire
/// v61 writes it (`CERTIFICATE_BINDING_FORMAT_VERSION`), so a bound module
/// has no refusal and its image selects v61. Mutation check: removing an
/// arm's `refuse` call (or reordering the ranks) turns the matching
/// assertion red; refusing the binding again turns the binding control red.
#[test]
fn wire_image_refusal_is_the_writer_in_check_mode() {
    let chain = {
        let mut module = Module::new("chain");
        module.functions.push(function_with_inlined_scope(4));
        module
    };
    let claim = {
        let mut module = Module::new("claim");
        module.completeness = Some(crate::ModuleCompleteness::Complete);
        module
    };
    let binding = {
        let mut module = Module::new("binding");
        module.proof_certificates.push(bound_certificate(1));
        module.proof_certificates.push(bound_certificate(73));
        module
    };
    let carriers = [
        (
            &chain,
            BinaryProjectionError::InlinedScopeChainUnencodable {
                function: 4,
                scope: 1,
            },
        ),
        (&claim, BinaryProjectionError::CompletenessClaimUnencodable),
        (
            &module_with_producer_internal_type(),
            BinaryProjectionError::ProducerInternalType,
        ),
    ];
    for (module, expected) in carriers {
        assert_eq!(
            module.wire_image_refusal(),
            Some(expected.clone()),
            "{expected}"
        );
        assert_eq!(
            module.wire_image_refusals(),
            vec![expected.clone()],
            "{expected}"
        );
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(module, ModuleBinaryOptions::default()).err(),
            Some(expected.clone()),
            "try_new is the same check: {expected}"
        );
        let identity = catch_unwind(AssertUnwindSafe(|| module.stable_digest()));
        assert!(
            identity.is_err(),
            "identity still refuses a construct: {expected}"
        );
    }

    // Every carrier at once: the precedence is today's.
    let mut all = module_with_producer_internal_type();
    all.functions.push(function_with_inlined_scope(9));
    all.completeness = Some(crate::ModuleCompleteness::Complete);
    all.proof_certificates.push(bound_certificate(5));
    assert_eq!(
        all.wire_image_refusals(),
        vec![
            BinaryProjectionError::InlinedScopeChainUnencodable {
                function: 9,
                scope: 1,
            },
            BinaryProjectionError::CompletenessClaimUnencodable,
            BinaryProjectionError::ProducerInternalType,
        ]
    );
    assert_eq!(
        all.wire_image_refusal(),
        Some(BinaryProjectionError::InlinedScopeChainUnencodable {
            function: 9,
            scope: 1,
        })
    );

    // Control: an encodable module has no refusal.
    assert_eq!(Module::new("plain").wire_image_refusal(), None);

    // Control (wire v61): a bound certificate has a carrier. The pre-check
    // finds nothing, `try_new` admits it, and the image selects v61.
    assert_eq!(binding.wire_image_refusal(), None);
    assert!(binding.wire_image_refusals().is_empty());
    let raw = ModuleBinaryOptions {
        body: ModuleBinaryBody::Raw,
        ..ModuleBinaryOptions::default()
    };
    assert!(
        ProjectedModuleBinaryPlan::try_new(&binding, raw).is_ok(),
        "a bound certificate is encodable at v61"
    );
    // The default projection is the v38 spelling, which has no carrier for
    // it: refused by name, never narrowed.
    assert_eq!(
        ProjectedModuleBinaryPlan::try_new(&binding, ModuleBinaryOptions::default()).err(),
        Some(BinaryProjectionError::CertificateBindingRequiresV61)
    );
    let image = serialize_module(&binding).expect("a bound certificate is encodable");
    assert_eq!(
        image[MAGIC.len()..MAGIC.len() + 4],
        CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes(),
        "a bound certificate selects the version that carries it"
    );
}

/// The identity sinks panic on a construct with the text each arm panicked
/// with before D1a, so a consumer reading a panic payload sees no change.
#[test]
fn identity_panics_keep_their_text() {
    let payload = catch_unwind(AssertUnwindSafe(|| {
        module_with_producer_internal_type().stable_digest()
    }))
    .expect_err("an identity of a Ty::Error module panics");
    let message = payload
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_default();
    assert_eq!(message, PRODUCER_INTERNAL_TYPE_UNENCODABLE_MESSAGE);
}

/// T9 (kind ii; before D1b `serialize_module` panicked on every carrier
/// below). Every blob entry returns the refusal the one pre-check names, per
/// carrier and for the over-limit count, and never panics: `serialize_module`,
/// `ModuleBinaryPlan::{to_vec, write_to}` and `ProjectedModuleBinaryPlan::
/// {to_vec, write_to}` (`write_to` as `InvalidData` carrying it, after its one
/// streaming pass). The count module's 4 GiB payload is never materialized by
/// the materializing entries: their check walk reads its length only.
/// Mutation check: skipping the pre-walk makes the count case allocate
/// 4 GiB, and a dropped record (in either sink) turns the `Err` assertions
/// red.
#[test]
fn serialize_refuses_every_construct_the_writer_cannot_encode() {
    let chain = {
        let mut module = Module::new("chain");
        module.functions.push(function_with_inlined_scope(4));
        module
    };
    let claim = {
        let mut module = Module::new("claim");
        module.completeness = Some(crate::ModuleCompleteness::Complete);
        module
    };
    let count = module_with_bytes(u32::MAX as usize + 1);
    for module in [
        &chain,
        &claim,
        &module_with_producer_internal_type(),
        &count,
    ] {
        let expected = module
            .wire_image_refusal()
            .expect("every carrier here has no wire image");
        let serialized = catch_unwind(AssertUnwindSafe(|| serialize_module(module)))
            .expect("serialize_module never panics");
        assert_eq!(serialized.err(), Some(expected.clone()), "{expected}");
        assert_eq!(
            ModuleBinaryPlan::new(module).to_vec().err(),
            Some(expected.clone()),
            "{expected}"
        );
        // `write_to` streams in one pass; the 4 GiB payload would be copied
        // into the writer, so the count module is checked through the other
        // entries only.
        if module.globals.is_empty() {
            let mut sink = Vec::new();
            let streamed = ModuleBinaryPlan::new(module)
                .write_to(&mut sink)
                .expect_err("write_to refuses too");
            assert_eq!(streamed.kind(), io::ErrorKind::InvalidData, "{expected}");
            assert_eq!(
                streamed
                    .get_ref()
                    .and_then(|inner| inner.downcast_ref::<BinaryProjectionError>()),
                Some(&expected),
                "write_to carries the refusal"
            );
        }
    }

    // The projected plan states the same rule over its projected image: a
    // plan that exists has an image (`try_new` refused the source), and its
    // blob entries return it.
    let plain = Module::new("plain");
    let mut projected = ProjectedModuleBinaryPlan::try_new(&plain, ModuleBinaryOptions::default())
        .expect("an encodable module projects");
    let bytes = projected.to_vec().expect("an encodable projection writes");
    let mut streamed = Vec::new();
    projected
        .write_to(&mut streamed)
        .expect("an encodable projection streams");
    assert_eq!(bytes, streamed);

    // Control: an encodable module serializes, and every spelling agrees. A
    // bound certificate is encodable since wire v61 (it was a refusing
    // carrier here before), so it is a control too.
    let binding = {
        let mut module = Module::new("binding");
        module.proof_certificates.push(bound_certificate(1));
        module
    };
    for module in [&plain, &binding] {
        let bytes = serialize_module(module).expect("an encodable module serializes");
        assert_eq!(ModuleBinaryPlan::new(module).to_vec(), Ok(bytes.clone()));
        assert_eq!(ModuleBinaryPlan::new(module).encoded_len(), bytes.len());
        assert_eq!(
            &deserialize_module(&bytes).expect("round trip"),
            module,
            "the bytes are the module's"
        );
    }
}
