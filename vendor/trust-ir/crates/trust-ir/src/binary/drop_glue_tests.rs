// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Amendment D, Part 1 (`docs/SPEC_RATIFICATIONS.md` §20): the module
//! drop-glue table (a trailing section) and `Inst::DropInvoke` (Inst tag 68),
//! both read-gated on `DROP_GLUE_FORMAT_VERSION`.

use super::*;
use crate::ty::{FieldDef, StructDef, StructRepr};
use crate::value::StructId;
use crate::{Block, DropGlueEntry, Function, InstrNode};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().unwrap())
}

fn relabel(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut forged = bytes.to_vec();
    forged[8..12].copy_from_slice(&version.to_le_bytes());
    forged
}

fn struct_ty(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// Two structs, a glue function per struct (`(ptr) -> ()`), and a caller
/// `f(%0: ptr)` that drops a `S0` and then (when `invoke`) drops a `S1`
/// through a `DropInvoke` into a cleanup pad that resumes. `table` decides
/// whether the drop-glue rows are stated.
fn drop_module(table: bool, invoke: bool) -> Module {
    let mut module = Module::new("drop_glue_codec");
    for id in 0..2 {
        module.add_struct(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![FieldDef {
                name: "p".into(),
                ty: Ty::Ptr,
                offset: None,
            }],
            size: None,
            align: None,
            repr: StructRepr::default(),
            origin: None,
        });
    }
    let ptr_to_unit = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, name) in [(0, "drop_s0"), (1, "drop_s1")] {
        let mut glue = Function::new(FuncId::new(id), name, ptr_to_unit, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        glue.blocks.push(block);
        module
            .try_add_function(glue)
            .expect("Module::try_add_function: test fixture");
    }
    let mut f = Function::new(FuncId::new(2), "f", ptr_to_unit, b(0));
    let mut entry = Block::new(b(0));
    entry.params.push((v(0), Ty::Ptr));
    entry.body.push(InstrNode::new(Inst::Drop {
        ty: struct_ty(0),
        ptr: v(0),
    }));
    if invoke {
        entry.body.push(InstrNode::new(Inst::DropInvoke {
            ty: struct_ty(1),
            ptr: v(0),
            normal_dest: b(1),
            normal_args: vec![v(0)],
            unwind_dest: b(2),
        }));
        f.blocks.push(entry);
        let mut normal = Block::new(b(1));
        normal.params.push((v(1), Ty::Ptr));
        normal
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(normal);
        let mut pad = Block::new(b(2));
        pad.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results(vec![v(2), v(3)]),
        );
        pad.body.push(InstrNode::new(Inst::Resume { exn: v(2) }));
        f.blocks.push(pad);
    } else {
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
    }
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    if table {
        module.set_drop_glue(struct_ty(1), FuncId::new(1)).unwrap();
        module.set_drop_glue(struct_ty(0), FuncId::new(0)).unwrap();
    }
    module
}

#[test]
fn drop_glue_table_and_drop_invoke_round_trip_at_their_version() {
    for (table, invoke) in [(true, false), (false, true), (true, true)] {
        let module = drop_module(table, invoke);
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            header_version(&bytes),
            DROP_GLUE_FORMAT_VERSION,
            "a table row or a DropInvoke selects the drop-glue version (table={table}, \
             invoke={invoke})"
        );
        let back = deserialize_module(&bytes).expect("decodes");
        assert_eq!(back, module, "table={table}, invoke={invoke}");
    }
    // `set_drop_glue` inserted the rows in their one canonical order
    // (ascending glue), whatever order they were stated in.
    let module = drop_module(true, true);
    assert_eq!(
        module.drop_glue,
        vec![
            DropGlueEntry {
                glue: FuncId::new(0),
                ty: struct_ty(0),
            },
            DropGlueEntry {
                glue: FuncId::new(1),
                ty: struct_ty(1),
            },
        ]
    );
    // The DropInvoke spelling: `Drop`'s payload, then `Invoke`'s successors.
    let inst = &module.functions[2].blocks[0].body[1].inst;
    let encoded = SealedStringPool::by_replay(|pool, bytes| {
        write_inst(bytes, pool, None, inst);
    });
    let mut expected = vec![68];
    expected.extend(SealedStringPool::by_replay(|pool, bytes| {
        write_ty(bytes, pool, &struct_ty(1));
    }));
    expected.extend([0, 1, 1, 0, 2]);
    assert_eq!(encoded, expected);
}

#[test]
fn a_module_without_drop_glue_or_drop_invoke_keeps_its_bytes_and_digest() {
    // A v47 module whose drops are unresolved keeps tag 57 and v47 exactly.
    let module = drop_module(false, false);
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), DROP_INST_FORMAT_VERSION);
    assert!(module.drop_glue.is_empty());
    // And its digests are the digests of those exact bytes: re-encoding a
    // decoded copy reproduces both.
    let back = deserialize_module(&bytes).unwrap();
    assert_eq!(
        serialize_module(&back).expect("serialize_module: test fixture"),
        bytes
    );
    assert_eq!(back.stable_digest(), module.stable_digest());
    assert_eq!(
        back.executable_content_digest_v1(),
        module.executable_content_digest_v1()
    );
    // A module with no drop at all keeps the base version.
    let mut plain = module;
    plain.functions[2].blocks[0].body.remove(0);
    assert_eq!(
        header_version(&serialize_module(&plain).expect("serialize_module: test fixture")),
        BASE_FORMAT_VERSION
    );
}

#[test]
fn drop_invoke_tag_is_refused_below_its_version() {
    let bytes =
        serialize_module(&drop_module(false, true)).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), DROP_GLUE_FORMAT_VERSION);
    for older in [DROP_GLUE_FORMAT_VERSION - 1, DROP_INST_FORMAT_VERSION] {
        assert_eq!(
            deserialize_module(&relabel(&bytes, older)),
            Err(BinaryError::InvalidTag(68)),
            "a v{older}-labelled blob carrying Inst tag 68 must fail closed"
        );
    }
}

#[test]
fn the_drop_glue_section_is_read_gated_on_its_version() {
    // Table only (no DropInvoke): below the version the reader does not
    // read the section, so its bytes are TRAILING and refused — never read
    // as some other section, never dropped.
    let bytes =
        serialize_module(&drop_module(true, false)).expect("serialize_module: test fixture");
    assert_eq!(header_version(&bytes), DROP_GLUE_FORMAT_VERSION);
    match deserialize_module(&relabel(&bytes, DROP_GLUE_FORMAT_VERSION - 1)) {
        Err(BinaryError::InvalidData(message)) => {
            assert!(message.contains("trailing bytes"), "{message}");
        }
        other => panic!("a v54-labelled blob with a drop-glue section decoded: {other:?}"),
    }
}

#[test]
fn a_drop_glue_table_out_of_canonical_order_is_refused_on_read() {
    let canonical = drop_module(true, false);
    let rows = canonical.drop_glue.clone();
    // Descending glue.
    let mut descending = canonical.clone();
    descending.drop_glue = vec![rows[1].clone(), rows[0].clone()];
    // Equal glue (one glue naming two types).
    let mut equal = canonical.clone();
    equal.drop_glue = vec![
        rows[0].clone(),
        DropGlueEntry {
            glue: rows[0].glue,
            ty: rows[1].ty.clone(),
        },
    ];
    // A duplicate key under ascending glue.
    let mut duplicate = canonical.clone();
    duplicate.drop_glue = vec![
        rows[0].clone(),
        DropGlueEntry {
            glue: rows[1].glue,
            ty: rows[0].ty.clone(),
        },
    ];
    for (what, module, needle) in [
        ("descending glue", descending, "canonical order"),
        ("equal glue", equal, "canonical order"),
        ("duplicate key", duplicate, "two rows for type"),
    ] {
        // The writer writes what it is given; the READER holds the order.
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        match deserialize_module(&bytes) {
            Err(BinaryError::InvalidData(message)) => {
                assert!(message.contains(needle), "{what}: {message}");
            }
            other => panic!("{what}: a non-canonical drop-glue table decoded: {other:?}"),
        }
    }
    // The canonical table decodes.
    assert!(
        deserialize_module(&serialize_module(&canonical).expect("serialize_module: test fixture"))
            .is_ok()
    );
}

#[test]
fn a_sparse_glue_func_id_is_not_refused_on_read() {
    // Function ids are sparse KEYS, not positions: whether a glue id names a
    // function is the validator's question (InvalidDropGlue), never the
    // reader's.
    let mut module = drop_module(false, false);
    module
        .set_drop_glue(struct_ty(0), FuncId::new(1000))
        .unwrap();
    let back =
        deserialize_module(&serialize_module(&module).expect("serialize_module: test fixture"))
            .expect("decodes");
    assert_eq!(back.drop_glue, module.drop_glue);
}

#[test]
fn the_digests_separate_drop_glue_tables() {
    let without = drop_module(false, false);
    let with = drop_module(true, false);
    let mut other_glue = drop_module(false, false);
    other_glue
        .set_drop_glue(struct_ty(0), FuncId::new(1))
        .unwrap();
    other_glue
        .set_drop_glue(struct_ty(1), FuncId::new(0))
        .unwrap();
    let stable = [
        without.stable_digest(),
        with.stable_digest(),
        other_glue.stable_digest(),
    ];
    let executable = [
        without.executable_content_digest_v1(),
        with.executable_content_digest_v1(),
        other_glue.executable_content_digest_v1(),
    ];
    for i in 0..3 {
        for j in (i + 1)..3 {
            assert_ne!(stable[i], stable[j], "stable_digest {i} vs {j}");
            // The table changes what a `Drop` executes, so the executable
            // identity moves with it.
            assert_ne!(
                executable[i], executable[j],
                "executable content {i} vs {j}"
            );
        }
    }
}

#[test]
fn v38_projections_refuse_drop_glue_and_drop_invoke() {
    for (table, invoke) in [(true, false), (false, true)] {
        let module = drop_module(table, invoke);
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                Some(BinaryProjectionError::DropGlueRequiresV55),
                "table={table}, invoke={invoke}"
            );
        }
    }
}

#[test]
fn a_pre_drop_glue_blob_decodes_with_an_empty_table() {
    // Every v47..=v54 drop decodes UNRESOLVED: there is no table to carry.
    let bytes =
        serialize_module(&drop_module(false, false)).expect("serialize_module: test fixture");
    for version in DROP_INST_FORMAT_VERSION..DROP_GLUE_FORMAT_VERSION {
        if !(MIN_READ_VERSION..=VERSION).contains(&version) {
            continue;
        }
        let back = deserialize_module(&relabel(&bytes, version))
            .unwrap_or_else(|e| panic!("v{version}: {e:?}"));
        assert!(back.drop_glue.is_empty(), "v{version}");
        assert!(matches!(
            back.functions[2].blocks[0].body[0].inst,
            Inst::Drop { .. }
        ));
    }
}
