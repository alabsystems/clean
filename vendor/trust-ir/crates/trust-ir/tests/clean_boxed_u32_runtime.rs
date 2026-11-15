// Copyright 2026 Andrew Yates | Apache-2.0
use std::collections::BTreeMap;
use trust_ir::clean_boxed_u32::*;

fn sources() -> RuntimeSources<'static> {
    RuntimeSources {
        object_model: include_bytes!("fixtures/clean_uint32_runtime/object_model.rs.txt"),
        ctor_scalar: include_bytes!("fixtures/clean_uint32_runtime/ctor_scalar.rs.txt"),
        rc_core: include_bytes!("fixtures/clean_uint32_runtime/rc_core.rs.txt"),
        refcount: include_bytes!("fixtures/clean_uint32_runtime/refcount.rs.txt"),
        public_api: include_bytes!("fixtures/clean_uint32_runtime/public_api.rs.txt"),
    }
}
fn image(address: u64, value: u32, rc: u32) -> Allocation {
    let mut bytes = rc.to_le_bytes().to_vec();
    bytes.extend([0, 0, 0, 4]);
    bytes.extend(value.to_le_bytes());
    Allocation {
        address,
        alignment: 8,
        bytes: bytes.into_iter().map(Some).collect(),
        live: true,
    }
}
fn heap(images: Vec<Allocation>, credits: &[(u64, u64)]) -> UInt32Heap {
    UInt32Heap::new(
        sources().bind().unwrap(),
        images,
        credits.iter().copied().collect(),
    )
    .unwrap()
}
#[test]
fn every_runtime_source_is_bound_and_mutations_are_refused() {
    assert!(sources().bind().is_ok());
    for i in 0..5 {
        let s = sources();
        let mut data = [
            s.object_model,
            s.ctor_scalar,
            s.rc_core,
            s.refcount,
            s.public_api,
        ]
        .map(<[u8]>::to_vec);
        data[i][0] ^= 1;
        let mutant = RuntimeSources {
            object_model: &data[0],
            ctor_scalar: &data[1],
            rc_core: &data[2],
            refcount: &data[3],
            public_api: &data[4],
        };
        assert_eq!(mutant.bind(), Err(Fault::RuntimeSourceMismatch(i)));
    }
}
#[test]
fn encoder_roundtrip_has_full_u32_range_without_heap_allocation() {
    let mut h = heap(vec![], &[]);
    let mut seed = 0x438fd09au32;
    for value in (0..4096)
        .chain([0x7fff_ffff, 0x8000_0000, u32::MAX])
        .chain((0..4096).map(|_| {
            seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
            seed
        }))
    {
        let output = encode(value);
        // Independent bit-word oracle, including the UInt32 high bit.
        assert_eq!(output.word(), u64::from(value) * 2 + 1);
        assert_eq!(h.decode(output.word()), Ok(value));
        let f = h.begin(&[output.word(), output.word()]).unwrap();
        assert_eq!(h.release(f, 1), Ok(ReleaseEffect::Tagged));
        assert_eq!(h.release(f, 0), Ok(ReleaseEffect::Tagged));
        assert_eq!(h.finish(f, value).unwrap(), output);
        assert!(h.allocations().is_empty());
    }
}
#[test]
fn aliased_occurrences_require_two_references_and_decode_before_free() {
    let untouched = image(0x2000, 0x12345678, 5);
    let mut h = heap(
        vec![image(0x1000, u32::MAX, 1), untouched.clone()],
        &[(0x1000, 2)],
    );
    let f = h.begin(&[0x1000, 0x1000]).unwrap();
    assert_eq!(h.decode_input(f, 0), Ok(u32::MAX));
    assert_eq!(h.decode_input(f, 1), Ok(u32::MAX));
    assert_eq!(h.finish(f, 1), Err(Fault::UnreleasedInputs));
    assert_eq!(
        h.release(f, 0),
        Ok(ReleaseEffect::Decremented {
            address: 0x1000,
            before: 1,
            after: 0
        })
    );
    assert_eq!(h.decode_input(f, 0), Err(Fault::ReleasedInput));
    assert_eq!(h.release(f, 0), Err(Fault::ReleasedInput));
    assert_eq!(h.decode_input(f, 1), Ok(u32::MAX));
    assert_eq!(
        h.release(f, 1),
        Ok(ReleaseEffect::Freed {
            address: 0x1000,
            size: 12,
            alignment: 8
        })
    );
    assert_eq!(h.decode(0x1000), Err(Fault::DeadAllocation));
    assert_eq!(&h.allocations()[&0x2000], &untouched);
    // MAX * MAX mod 2^32 = 1; ownership is separate from the scalar proof.
    assert_eq!(
        h.finish(f, u32::MAX.wrapping_mul(u32::MAX)).unwrap().word(),
        3
    );
    assert!(h.is_retired(f));
    assert_eq!(h.release(f, 1), Err(Fault::RetiredFrame));
}
#[test]
fn insufficient_alias_ownership_is_rejected_without_any_state_change() {
    let mut h = heap(vec![image(0x1000, 7, 0)], &[(0x1000, 1)]);
    let before = h.clone();
    assert_eq!(
        h.begin(&[0x1000, 0x1000]),
        Err(Fault::MissingOwnedReferences {
            address: 0x1000,
            need: 2,
            have: 1
        })
    );
    assert_eq!(h, before);
    assert_eq!(
        UInt32Heap::new(
            sources().bind().unwrap(),
            vec![image(0x1000, 7, 0)],
            BTreeMap::from([(0x1000, 2)])
        ),
        Err(Fault::MissingOwnedReferences {
            address: 0x1000,
            need: 2,
            have: 1
        })
    );
}
#[test]
fn shared_frames_consume_only_transferred_credits_and_preserve_external_owner() {
    let mut h = heap(vec![image(0x1000, 123, 2)], &[(0x1000, 2)]);
    let a = h.begin(&[0x1000]).unwrap();
    let b = h.begin(&[0x1000]).unwrap();
    let before = h.clone();
    assert!(matches!(
        h.begin(&[0x1000]),
        Err(Fault::MissingOwnedReferences { have: 0, .. })
    ));
    assert_eq!(h, before);
    h.release(b, 0).unwrap();
    h.finish(b, 0).unwrap();
    assert_eq!(h.decode_input(a, 0), Ok(123));
    h.release(a, 0).unwrap();
    h.finish(a, 0).unwrap();
    // Three references existed; only two were transferred and consumed.
    assert!(h.allocations()[&0x1000].live);
    assert_eq!(&h.allocations()[&0x1000].bytes[..4], &[Some(0); 4]);
    assert_eq!(h.decode(0x1000), Ok(123));
}
#[test]
fn all_small_alias_multiplicities_and_release_orders_obey_conservation() {
    for refs in 1..=32u32 {
        for transferred in 1..=refs {
            let frame_cell = image(0x3000, 19, 7);
            let mut h = heap(
                vec![
                    image(0x1000, refs.wrapping_mul(17), refs - 1),
                    frame_cell.clone(),
                ],
                &[(0x1000, u64::from(transferred))],
            );
            let words = vec![0x1000; transferred as usize];
            let f = h.begin(&words).unwrap();
            // Reverse slot order makes aliased occurrence identity observable.
            for (dropped, slot) in (0..transferred as usize).rev().enumerate() {
                assert_eq!(h.decode_input(f, slot), Ok(refs * 17));
                h.release(f, slot).unwrap();
                let remaining = refs as usize - dropped - 1;
                let c = &h.allocations()[&0x1000];
                assert_eq!(c.live, remaining != 0);
                if c.live {
                    let rc: Vec<_> = c.bytes[..4].iter().map(|x| x.unwrap()).collect();
                    assert_eq!(
                        u32::from_le_bytes(rc.try_into().unwrap()) as usize + 1,
                        remaining
                    );
                }
                assert_eq!(&h.allocations()[&0x3000], &frame_cell);
            }
            assert!(h.finish(f, 0).is_ok());
        }
    }
}
#[test]
fn sticky_counts_consume_ghost_slots_without_freeing_or_changing_memory() {
    for rc in [
        RC_STICKY_DROP,
        RC_STICKY_DROP + 1,
        0xf000_0000,
        0xf000_ffff,
        u32::MAX - 1,
    ] {
        let original = image(0x1000, 11, rc);
        let mut h = heap(vec![original.clone()], &[(0x1000, 3)]);
        let f = h.begin(&[0x1000; 3]).unwrap();
        for slot in 0..3 {
            assert_eq!(
                h.release(f, slot),
                Ok(ReleaseEffect::Frozen {
                    address: 0x1000,
                    count: rc
                })
            );
        }
        assert!(h.finish(f, 11).is_ok());
        assert_eq!(&h.allocations()[&0x1000], &original);
        assert!(matches!(
            h.begin(&[0x1000]),
            Err(Fault::MissingOwnedReferences { have: 0, .. })
        ));
    }
    let mut h = heap(vec![image(0x1000, 11, RC_STICKY_DROP - 1)], &[(0x1000, 1)]);
    let f = h.begin(&[0x1000]).unwrap();
    assert_eq!(
        h.release(f, 0),
        Ok(ReleaseEffect::Decremented {
            address: 0x1000,
            before: RC_STICKY_DROP - 1,
            after: RC_STICKY_DROP - 2
        })
    );
}
#[test]
fn null_out_of_range_interior_wrong_kind_and_uninitialized_inputs_refuse() {
    let h = heap(vec![image(0x1000, 0, 0)], &[]);
    for (word, error) in [
        (0, Fault::Null),
        (2, Fault::Misaligned),
        (0x1002, Fault::Misaligned),
        (0x1008, Fault::UnknownAllocation),
        (0x2000, Fault::UnknownAllocation),
        ((1u64 << 33) | 1, Fault::TaggedOutOfRange),
    ] {
        assert_eq!(h.decode(word), Err(error));
    }
    for i in 0..12 {
        let mut c = image(0x1000, 9, 0);
        c.bytes[i] = None;
        assert_eq!(
            heap(vec![c], &[]).decode(0x1000),
            Err(Fault::Uninitialized(i))
        );
    }
    for kind in 1..=7 {
        let mut c = image(0x1000, 0, 0);
        c.bytes[5] = Some(kind);
        assert_eq!(heap(vec![c], &[]).decode(0x1000), Err(Fault::WrongKind));
    }
    for (index, value) in [(4, 1), (6, 1), (7, 8)] {
        let mut c = image(0x1000, 0, 0);
        c.bytes[index] = Some(value);
        assert_eq!(heap(vec![c], &[]).decode(0x1000), Err(Fault::WrongLayout));
    }
    assert_eq!(
        heap(vec![image(0x1000, 7, u32::MAX)], &[]).decode(0x1000),
        Err(Fault::InvalidRefcount)
    );
    let mut c = image(0x1000, 9, 0);
    c.live = false;
    assert_eq!(
        heap(vec![c], &[]).decode(0x1000),
        Err(Fault::DeadAllocation)
    );
}
#[test]
fn invalid_later_operand_and_omitted_release_preserve_exact_error_state() {
    let mut h = heap(vec![image(0x1000, 8, 0)], &[(0x1000, 1)]);
    let before = h.clone();
    assert_eq!(h.begin(&[0x1000, 0]), Err(Fault::Null));
    assert_eq!(h, before);
    let f = h.begin(&[0x1000, encode(31).word()]).unwrap();
    h.release(f, 0).unwrap();
    let before = h.clone();
    assert_eq!(h.finish(f, 99), Err(Fault::UnreleasedInputs));
    assert_eq!(h, before);
    assert_eq!(h.release(f, 2), Err(Fault::InvalidSlot));
    assert_eq!(h, before);
    h.release(f, 1).unwrap();
    h.finish(f, 99).unwrap();
}
#[test]
fn malformed_or_overlapping_bounded_memory_is_never_admitted() {
    for alignment in [1, 2, 4, 16, 32] {
        let mut c = image(0x1000, 99, 0);
        c.alignment = alignment;
        assert_eq!(heap(vec![c], &[]).decode(0x1000), Err(Fault::WrongLayout));
    }
    let binding = sources().bind().unwrap();
    let mut a = image(0x1000, 1, 0);
    a.alignment = 3;
    assert_eq!(
        UInt32Heap::new(binding, vec![a], BTreeMap::new()),
        Err(Fault::InvalidAllocation)
    );
    assert_eq!(
        UInt32Heap::new(
            binding,
            vec![image(0x1000, 1, 0), image(0x1008, 2, 0)],
            BTreeMap::new()
        ),
        Err(Fault::OverlappingAllocations)
    );
    assert_eq!(
        UInt32Heap::new(binding, vec![image(u64::MAX - 7, 1, 0)], BTreeMap::new()),
        Err(Fault::InvalidAllocation)
    );
    let mut a = image(0x1000, 1, 0);
    a.bytes.pop();
    assert_eq!(heap(vec![a], &[]).decode(0x1000), Err(Fault::WrongLayout));
}

#[test]
fn every_u32_edge_has_identical_tagged_and_initialized_heap_values() {
    for value in [0, 1, (1 << 31) - 1, 1 << 31, u32::MAX] {
        for rc in [0, 1, RC_STICKY_DROP - 1, RC_STICKY_DROP] {
            let mut h = heap(vec![image(0x1000, value, rc)], &[(0x1000, 1)]);
            let word = encode(value).word();
            let f = h.begin(&[word, 0x1000]).unwrap();
            assert_eq!(h.decode_input(f, 0), h.decode_input(f, 1));
            h.release(f, 1).unwrap();
            h.release(f, 0).unwrap();
            assert_eq!(h.finish(f, value).unwrap().word(), word);
        }
    }
}
