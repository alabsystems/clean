// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Content-addressed weight blobs (PKG-U13e, SPEC_RATIFICATIONS §27):
//! `Constant::TensorBlob` (Constant tag 18) and the module blob table, a
//! trailing section after the v58 closure layouts, both read-gated on
//! `TENSOR_BLOB_FORMAT_VERSION`. The codec spells exactly what it is given
//! and refuses only a table out of its canonical order; whether a row's bytes
//! hash to its digest, whether a constant's digest names a row and whether
//! its extents fit the bytes are the validator's questions, so some fixtures
//! below are deliberately ill-formed.

use super::*;
use crate::blob::{Blob, BlobDigest};
use crate::interpret::{
    ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
};
use crate::{Block, Function, InstrNode};

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn relabel(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut forged = bytes.to_vec();
    forged[8..12].copy_from_slice(&version.to_le_bytes());
    forged
}

/// `f() -> ty` returning `const ty value`, in `module`.
fn push_const_function(module: &mut Module, ty: Ty, value: Constant) {
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![ty.clone()],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut f = Function::new(id, format!("weights{}", id.index()), sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    let out = ValueId::new(0);
    entry
        .body
        .push(InstrNode::new(Inst::Const { ty, value }).with_results(vec![out]));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![out] }));
    f.blocks.push(entry);
    module.functions.push(f);
}

/// Four little-endian `i32`s: the 2x2 matrix `[[1, 2], [3, -1]]`.
fn matrix_bytes() -> Vec<u8> {
    [1i32, 2, 3, -1]
        .iter()
        .flat_map(|x| x.to_le_bytes())
        .collect()
}

/// A well-formed weight: `const tensor<i32, 2> tensor_blob<..>[2, 2]` and its
/// one table row.
fn weight_module() -> Module {
    let mut module = Module::new("tensor_blob_codec");
    let digest = module.intern_blob(matrix_bytes());
    push_const_function(
        &mut module,
        tensor(Ty::I32, 2),
        Constant::TensorBlob {
            digest,
            dims: vec![2, 2],
        },
    );
    module
}

/// Two rows (one unreferenced) and a rank-0 constant over a four-byte row.
fn two_row_module() -> Module {
    let mut module = weight_module();
    let scalar = module.intern_blob(7i32.to_le_bytes().to_vec());
    push_const_function(
        &mut module,
        tensor(Ty::I32, 0),
        Constant::TensorBlob {
            digest: scalar,
            dims: vec![],
        },
    );
    module.intern_blob(vec![0xAA; 3]);
    module
}

/// A constant whose digest names no row (the validator's `MissingBlob`), and
/// nothing else at v70: only Constant tag 18 is read-gated in its bytes.
fn constant_only_module() -> Module {
    let mut module = Module::new("tensor_blob_codec");
    push_const_function(
        &mut module,
        Ty::I32,
        Constant::TensorBlob {
            digest: BlobDigest::of(b"elsewhere"),
            dims: vec![0, 3],
        },
    );
    module
}

/// A table with no constant (an unreferenced row is admitted), and nothing
/// else at v70: only the trailing section is read-gated.
fn table_only_module() -> Module {
    let mut module = Module::new("tensor_blob_codec");
    module.intern_blob(vec![]);
    module
}

fn fixtures() -> Vec<(&'static str, Module)> {
    vec![
        ("weight", weight_module()),
        ("two-row", two_row_module()),
        ("constant-only", constant_only_module()),
        ("table-only", table_only_module()),
    ]
}

fn spell(value: &Constant) -> Vec<u8> {
    SealedStringPool::by_replay(|pool, bytes| {
        write_constant(bytes, pool, value);
    })
}

#[test]
fn modules_round_trip_at_exactly_the_blob_version() {
    for (name, module) in fixtures() {
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), TENSOR_BLOB_FORMAT_VERSION, "{name}");
        let (decoded, version) =
            deserialize_module_with_wire_version(&bytes).expect("lossless module");
        assert_eq!(version.get(), TENSOR_BLOB_FORMAT_VERSION, "{name}");
        assert_eq!(decoded, module, "{name}");
        assert_eq!(decoded.stable_digest(), module.stable_digest(), "{name}");
        assert_eq!(
            serialize_module(&decoded).expect("serialize_module: decoded fixture"),
            bytes,
            "{name}: re-encoding is byte-identical"
        );
    }
}

/// The tag-18 spelling and the table section, pinned byte for byte: the 32
/// digest bytes, then the counted extents as fixed-width little-endian
/// `u64`s; the section is the counted rows, each the 32 digest bytes and the
/// counted data.
#[test]
fn wire_spellings_are_pinned() {
    let digest = BlobDigest::of(&matrix_bytes());
    let mut expected = vec![18];
    expected.extend_from_slice(&digest.0);
    expected.push(2);
    expected.extend_from_slice(&2u64.to_le_bytes());
    expected.extend_from_slice(&2u64.to_le_bytes());
    assert_eq!(
        spell(&Constant::TensorBlob {
            digest,
            dims: vec![2, 2],
        }),
        expected
    );
    let mut rank_zero = vec![18];
    rank_zero.extend_from_slice(&digest.0);
    rank_zero.push(0);
    assert_eq!(
        spell(&Constant::TensorBlob {
            digest,
            dims: vec![],
        }),
        rank_zero
    );

    // The table is the module's last section.
    let module = weight_module();
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    let mut section = vec![1];
    section.extend_from_slice(&digest.0);
    section.push(16);
    section.extend_from_slice(&matrix_bytes());
    assert!(
        bytes.ends_with(&section),
        "the blob table closes the module image"
    );
}

/// A truncated constant is refused, never read with a defaulted field.
#[test]
fn truncated_constants_are_refused() {
    let bytes = spell(&Constant::TensorBlob {
        digest: BlobDigest::of(&matrix_bytes()),
        dims: vec![2, 2],
    });
    for cut in 1..bytes.len() {
        let mut reader = Reader::new(&bytes[..cut]);
        reader.version = TENSOR_BLOB_FORMAT_VERSION;
        assert!(
            read_constant::<crate::NoExt>(&mut reader).is_err(),
            "{cut} of {} bytes read as a constant",
            bytes.len()
        );
    }
    // A truncated table is refused too.
    let module = two_row_module();
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    let table_start = bytes.len()
        - module
            .blobs
            .iter()
            .map(|row| 32 + 1 + row.data.len())
            .sum::<usize>()
        - 1;
    for cut in table_start..bytes.len() {
        assert!(
            deserialize_module(&bytes[..cut]).is_err(),
            "{cut} of {} bytes read as a module",
            bytes.len()
        );
    }
}

/// Below v70 the constant's tag is unread (`InvalidTag(18)`,
/// `refuse/blob_tensor_blob_below_its_version`) and the table's bytes are
/// trailing bytes.
#[test]
fn bytes_below_their_version_are_refused() {
    let bytes = serialize_module(&constant_only_module()).expect("serialize_module: fixture");
    assert_eq!(
        deserialize_module(&relabel(&bytes, TENSOR_BLOB_FORMAT_VERSION - 1)),
        Err(BinaryError::InvalidTag(CONSTANT_TENSOR_BLOB_TAG)),
    );
    // A v69 header still has the v69 layout up to the constant; earlier
    // labels stop at an earlier field. Every older label is refused.
    for version in MIN_READ_VERSION..TENSOR_BLOB_FORMAT_VERSION {
        assert!(
            deserialize_module(&relabel(&bytes, version)).is_err(),
            "a v{version} label carrying Constant tag 18 is refused"
        );
    }
    let table = serialize_module(&table_only_module()).expect("serialize_module: fixture");
    assert_eq!(
        deserialize_module(&relabel(&table, TENSOR_BLOB_FORMAT_VERSION - 1)),
        Err(BinaryError::InvalidData(
            "trailing bytes after canonical module payload".to_string()
        )),
    );
}

/// The table's canonical order is strictly ascending digest
/// (`refuse/blob_tensor_blob_table_not_canonical`): the reader refuses rows
/// out of order and a digest listed twice, which is what holds identical
/// bytes once on the wire.
#[test]
fn a_table_out_of_canonical_order_is_refused() {
    let canonical = two_row_module();
    assert!(crate::blob::blob_table_order_refusal(&canonical.blobs).is_none());

    let mut reversed = canonical.clone();
    reversed.blobs.reverse();
    let bytes = serialize_module(&reversed).expect("the writer spells any order");
    match deserialize_module(&bytes) {
        Err(BinaryError::InvalidData(reason)) => {
            assert!(reason.contains("out of canonical order"), "{reason}")
        }
        other => panic!("a reversed table was read: {other:?}"),
    }

    let mut twice = canonical.clone();
    let row = twice.blobs[0].clone();
    twice.blobs.insert(1, row);
    let bytes = serialize_module(&twice).expect("the writer spells any order");
    match deserialize_module(&bytes) {
        Err(BinaryError::InvalidData(reason)) => {
            assert!(reason.contains("twice"), "{reason}")
        }
        other => panic!("a digest listed twice was read: {other:?}"),
    }

    // A row whose bytes do not hash to its digest is the validator's
    // question (`BlobDigestMismatch`): the codec carries it.
    let mut tampered = canonical;
    tampered.blobs[0].data.push(0);
    let bytes = serialize_module(&tampered).expect("serialize_module: fixture");
    assert_eq!(deserialize_module(&bytes), Ok(tampered));
}

/// Interning holds identical bytes once and keeps the canonical order.
#[test]
fn interning_stores_identical_bytes_once() {
    let mut module = Module::new("intern");
    let first = module.intern_blob(matrix_bytes());
    let other = module.intern_blob(vec![1, 2, 3]);
    let again = module.intern_blob(matrix_bytes());
    assert_eq!(first, again);
    assert_ne!(first, other);
    assert_eq!(module.blobs.len(), 2);
    assert!(crate::blob::blob_table_order_refusal(&module.blobs).is_none());
    assert_eq!(
        module.blob(&first).map(|row| &row.data),
        Some(&matrix_bytes())
    );
    assert!(module.blob(&BlobDigest::of(b"absent")).is_none());
}

#[test]
fn v38_projections_refuse_blobs_by_name() {
    for (name, module) in fixtures() {
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                Some(BinaryProjectionError::TensorBlobRequiresV70),
                "{name}"
            );
        }
    }
    assert!(
        BinaryProjectionError::TensorBlobRequiresV70
            .to_string()
            .contains(&format!("v{TENSOR_BLOB_FORMAT_VERSION} binary projection"))
    );
}

/// No field of the constant or the table is erased by the module digest; the
/// body digest reads the constant's digest and extents, never the table.
#[test]
fn every_field_moves_the_module_digest_and_only_the_constant_moves_the_body() {
    let base = weight_module();
    let body = |m: &Module| m.function_body_digest(FuncId::new(0)).expect("body digest");
    let original = base.stable_digest();
    let original_body = body(&base);

    type Mutant = (&'static str, fn(&mut Module), bool);
    let mutants: [Mutant; 6] = [
        (
            "constant digest",
            |m| {
                if let Inst::Const {
                    value: Constant::TensorBlob { digest, .. },
                    ..
                } = &mut m.functions[0].blocks[0].body[0].inst
                {
                    *digest = BlobDigest::of(b"other");
                }
            },
            true,
        ),
        (
            "constant extents",
            |m| {
                if let Inst::Const {
                    value: Constant::TensorBlob { dims, .. },
                    ..
                } = &mut m.functions[0].blocks[0].body[0].inst
                {
                    *dims = vec![1, 4];
                }
            },
            true,
        ),
        (
            "constant rank",
            |m| {
                if let Inst::Const {
                    value: Constant::TensorBlob { dims, .. },
                    ..
                } = &mut m.functions[0].blocks[0].body[0].inst
                {
                    dims.push(1);
                }
            },
            true,
        ),
        ("row bytes", |m| m.blobs[0].data[0] ^= 1, false),
        (
            "row digest",
            |m| m.blobs[0].digest = BlobDigest::of(b"other"),
            false,
        ),
        (
            "an extra row",
            |m| {
                m.intern_blob(vec![5; 9]);
            },
            false,
        ),
    ];
    for (name, mutate, moves_body) in mutants {
        let mut module = base.clone();
        mutate(&mut module);
        assert_ne!(module, base, "{name}: the mutant changes nothing");
        assert_ne!(module.stable_digest(), original, "{name}");
        assert_eq!(
            body(&module) != original_body,
            moves_body,
            "{name}: the body digest moves exactly when the body changes"
        );
    }
}

struct Admit;

impl ExecutionObserver for Admit {
    type Refusal = ();

    fn admit(&mut self, _progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        Ok(())
    }
}

/// The observed identity walk (its own collector and writer) states the same
/// module and body identities as the canonical writer, header included.
#[test]
fn observed_identity_matches_the_canonical_writer() {
    for (name, module) in fixtures() {
        let mut observer = Admit;
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let site = ExecutionSite::Entry(FuncId::new(0));
        assert_eq!(
            module
                .stable_digest_observed(&mut session, site)
                .expect("observed identity: test fixture"),
            module.stable_digest(),
            "{name}"
        );
        assert_eq!(
            module
                .checked_stable_digest_observed(&mut session, site)
                .expect("checked observed identity: test fixture"),
            module.stable_digest(),
            "{name}"
        );
        for f in &module.functions {
            assert_eq!(
                module
                    .function_body_digest_observed(f.id, &mut session, site)
                    .expect("observed body identity: test fixture"),
                module.function_body_digest(f.id),
                "{name}: body of {}",
                f.id.index()
            );
        }
    }
}

/// The blob row type round-trips the canonical digest constructor.
#[test]
fn rows_built_by_new_match_their_digest() {
    let row = Blob::new(matrix_bytes());
    assert!(row.digest_matches());
    assert_eq!(row.digest, BlobDigest::of(&matrix_bytes()));
}
