// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent byte vectors and real original producer carriers; no authority.
use super::*;
use crate::level::LeanLevelProfile;
use crate::tc::TypeChecker;
use crate::{Expr, Level, Name};
use sha2::{Digest, Sha256};
use std::io::Read;

#[path = "tests_enums.rs"]
mod tests_enums;

const C4_48: &[u8] = include_bytes!("../../../tests/fixtures/environment_dag_wire/c4-lean48.dag");
const C4_430: &[u8] = include_bytes!("../../../tests/fixtures/environment_dag_wire/c4-lean430.dag");
const C4_JSON_48: &str =
    include_str!("../../../tests/fixtures/environment_dag_wire/c4-lean48.json");
const C4_JSON_430: &str =
    include_str!("../../../tests/fixtures/environment_dag_wire/c4-lean430.json");
const ORIGINAL3FA: &[u8] =
    include_bytes!("../../../tests/fixtures/environment_dag_wire/original-3fa.dag.zst");

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn exact_legacy_grammar(bytes: &[u8], epoch: LegacyEnvironmentDagEpoch) -> Option<[usize; 5]> {
    // Used ONLY on authenticated minimal outputs of original writers. The
    // decoder also accepts old nonminimal integers, whose semantic value is
    // retained but whose original width is deliberately not a DTO field.
    let Envelope {
        environment,
        nodes,
        mut budget,
    } = envelope(bytes, Encoding::Legacy).unwrap();
    for PayloadNode { kind, .. } in nodes {
        let mut decoder = Decoder::with_budget(&kind, Encoding::Legacy, budget).unwrap();
        let wire = WExprKind::read(&mut decoder).unwrap();
        budget = decoder.finish().unwrap();
        let mut encoder = Encoder::new(Encoding::Legacy);
        wire.write(&mut encoder).unwrap();
        assert_eq!(
            encoder.finish(),
            kind,
            "a nested legacy field changed shape"
        );
    }
    let mut decoder = Decoder::with_budget(&environment, Encoding::Legacy, budget).unwrap();
    let mut encoder = Encoder::new(Encoding::Legacy);
    let counts = match epoch {
        LegacyEnvironmentDagEpoch::Clean3fa => {
            let wire = Legacy3faEnvironment::read(&mut decoder).unwrap();
            let counts = wire.declaration_counts();
            wire.write(&mut encoder).unwrap();
            Some(counts)
        }
        LegacyEnvironmentDagEpoch::CleanC4 => {
            LegacyC4Environment::read(&mut decoder)
                .unwrap()
                .write(&mut encoder)
                .unwrap();
            None
        }
    };
    decoder.finish().unwrap();
    assert_eq!(
        encoder.finish(),
        environment,
        "full legacy Environment DTO changed bytes"
    );
    counts
}

fn ordered_fixture_json(text: &str) -> serde_json::Value {
    let mut value: serde_json::Value = serde_json::from_str(text).unwrap();
    value["constants"]
        .as_array_mut()
        .unwrap()
        .sort_by_key(|row| serde_json::to_string(&row["name"]).unwrap());
    value
}

#[test]
fn genuine_c4_g1_profiles_preserve_all_bytes_and_authored_fixture_fields() {
    for (bytes, json, profile, hash) in [
        (
            C4_48,
            C4_JSON_48,
            LeanLevelProfile::Lean48,
            "5792f52f37830826ac2b01d11b622d426dd775fdb70b8db5b35a618a17dcf421",
        ),
        (
            C4_430,
            C4_JSON_430,
            LeanLevelProfile::Lean430,
            "0833fdb82e927c2a9da8982bdb4adf31d8b575fa2dbdcdcae29d0caee99030c6",
        ),
    ] {
        assert_eq!(sha(bytes), hash);
        exact_legacy_grammar(bytes, LegacyEnvironmentDagEpoch::CleanC4);
        let env = Environment::from_legacy_dag_bincode(bytes, LegacyEnvironmentDagEpoch::CleanC4)
            .unwrap();
        assert_eq!(env.lean_level_profile(), profile);
        assert_eq!(env.num_constants(), 2);
        // JSON is an independent old-writer fixture observation for THESE
        // fields, not an assertion about every persisted Environment table.
        assert_eq!(
            ordered_fixture_json(&env.to_json().unwrap()),
            ordered_fixture_json(json)
        );
        let raw = Level::IMax(
            Level::Succ(Level::Zero.into()).into(),
            Level::Param(Name::from_string("u")).into(),
        );
        let mut checker = TypeChecker::new(&env);
        checker.set_kernel_theory(crate::env::KernelTheory::Lean);
        assert_eq!(
            checker.is_def_eq(
                &Expr::sort(raw),
                &Expr::sort(Level::Param(Name::from_string("u")))
            ),
            profile == LeanLevelProfile::Lean430
        );
        let v2 = env.to_dag_bincode().unwrap();
        let restored = Environment::from_dag_bincode(&v2).unwrap();
        assert_eq!(restored.lean_level_profile(), profile);
        assert_eq!(restored.to_dag_bincode().unwrap(), v2);
        assert!(restored.declaration_verification.is_empty());
    }
}

#[test]
fn original_3fa_full_carrier_keeps_every_declaration_table_and_fixed_profile() {
    assert_eq!(
        sha(ORIGINAL3FA),
        "0eb639b891320cd64730eb7ce233620481647a3dd3c4889d1eec8f748a5647b3"
    );
    let decoder = zstd::stream::read::Decoder::new(ORIGINAL3FA).unwrap();
    let mut raw = Vec::new();
    decoder
        .take((MAX_BYTES + 1) as u64)
        .read_to_end(&mut raw)
        .unwrap();
    assert_eq!(raw.len(), 4_540_257);
    assert_eq!(
        sha(&raw),
        "dbf8b3e669d2ca33602ae54c6402126ddb99b464ff8b178a66fce734d1584e65"
    );
    let expected = exact_legacy_grammar(&raw, LegacyEnvironmentDagEpoch::Clean3fa).unwrap();
    let env =
        Environment::from_legacy_dag_bincode(&raw, LegacyEnvironmentDagEpoch::Clean3fa).unwrap();
    assert_eq!(env.lean_level_profile(), LeanLevelProfile::Lean430);
    assert_eq!(env.num_constants(), 3010);
    assert_eq!(
        [
            env.constants.len(),
            env.inductives.len(),
            env.constructors.len(),
            env.recursors.len(),
            env.quotients.len()
        ],
        expected
    );
    assert!(env.declaration_verification.is_empty());
    assert!(env.native_reducers.is_empty());
    for root in ["original_unsigned", "original_signed", "original_constant"] {
        let name = Name::from_string(&format!("Trust.Cert.CheckedMulI128Raw.{root}"));
        let info = env.get_const(&name).expect("original root record was lost");
        assert!(info.value.is_some());
        assert!(info.level_params.is_empty());
    }
    let v2 = env.to_dag_bincode().unwrap();
    let restored = Environment::from_dag_bincode(&v2).unwrap();
    assert_eq!(restored.to_dag_bincode().unwrap(), v2);
    assert_eq!(
        [
            restored.constants.len(),
            restored.inductives.len(),
            restored.constructors.len(),
            restored.recursors.len(),
            restored.quotients.len()
        ],
        expected
    );
    // Restored records have no replay authority. Production CG's exact
    // original admission predicates, not this codec control, decide proofs.
}

#[test]
fn default_reader_never_guesses_g1_schema_and_explicit_epochs_do_not_read_v2() {
    for bytes in [C4_48, C4_430] {
        assert!(Environment::from_dag_bincode(bytes)
            .expect_err("default guessed G1")
            .to_string()
            .contains("explicit source epoch"));
        assert!(
            Environment::from_legacy_dag_bincode(bytes, LegacyEnvironmentDagEpoch::Clean3fa)
                .is_err()
        );
    }
    let v2 = Environment::default().to_dag_bincode().unwrap();
    for epoch in [
        LegacyEnvironmentDagEpoch::Clean3fa,
        LegacyEnvironmentDagEpoch::CleanC4,
    ] {
        assert!(Environment::from_legacy_dag_bincode(&v2, epoch).is_err());
    }
    // These actual golden wrong-epoch refusals are not a claim that every G1
    // string is disjoint across the two globally ambiguous grammars.
}

#[test]
fn owned_primitive_width_tags_lengths_and_trailing_bytes_are_checked() {
    for (value, bytes) in [
        (0, vec![0]),
        (250, vec![250]),
        (251, vec![251, 251, 0]),
        (65536, vec![252, 0, 0, 1, 0]),
        (u64::MAX, vec![253, 255, 255, 255, 255, 255, 255, 255, 255]),
    ] {
        let mut r = Decoder::new(&bytes, Encoding::Legacy).unwrap();
        assert_eq!(r.u64().unwrap(), value);
        r.finish().unwrap();
        let mut w = Encoder::new(Encoding::Legacy);
        w.u64(value).unwrap();
        assert_eq!(w.finish(), bytes);
    }
    let bytes = [0x44, 0x33, 0x22, 0x11];
    let mut r = Decoder::new(&bytes, Encoding::V2).unwrap();
    assert_eq!(r.u32().unwrap(), 0x11223344);
    r.finish().unwrap();
    let nonminimal = [251, 0, 0];
    let mut r = Decoder::new(&nonminimal, Encoding::Legacy).unwrap();
    let zero = r.u64().unwrap();
    r.finish().unwrap();
    assert_eq!(zero, 0);
    let mut w = Encoder::new(Encoding::Legacy);
    w.u64(zero).unwrap();
    assert_eq!(
        w.finish(),
        [0],
        "semantic roundtrip must not pretend to retain nonminimal width"
    );
    for bytes in [vec![253, 0, 0, 0, 0, 0, 0, 0, 0], vec![254], vec![255]] {
        assert!(Decoder::new(&bytes, Encoding::Legacy)
            .unwrap()
            .u32()
            .is_err());
    }
    assert!(Decoder::new(&[2], Encoding::V2).unwrap().boolean().is_err());
    assert!(<Option<u32> as Wire>::read(&mut Decoder::new(&[2], Encoding::V2).unwrap()).is_err());
    let huge = u64::MAX.to_le_bytes();
    let mut r = Decoder::new(&huge, Encoding::V2).unwrap();
    assert!(r.bytes().is_err());
    assert_eq!(
        r.budget.remaining(),
        MAX_BYTES,
        "limit was checked after allocation"
    );
    let mut r = Decoder::new(&[1, 0], Encoding::Legacy).unwrap();
    assert_eq!(r.u8().unwrap(), 1);
    assert!(r.finish().is_err());
}

#[test]
fn legacy_key_identity_rejects_nonminimal_duplicates_but_metadata_sequences_retain_them() {
    use super::containers::{Map, Set};
    use super::syntax::WName;
    use super::types::WMDataValue;
    use crate::expr::MDataValue;
    // Same Name::Num(Anon,0), once minimal and once using the accepted
    // nonminimal u16 varint for zero. Raw-slice comparison would miss this.
    let map = [2, 2, 0, 0, 10, 2, 0, 251, 0, 0, 11];
    let result = Map::<WName, u64>::read(&mut Decoder::new(&map, Encoding::Legacy).unwrap());
    assert!(result
        .expect_err("duplicate decoded Name was overwritten")
        .to_string()
        .contains("duplicate"));
    let set = [2, 2, 0, 0, 2, 0, 251, 0, 0];
    assert!(
        Set::<WName>::read(&mut Decoder::new(&set, Encoding::Legacy).unwrap())
            .expect_err("duplicate decoded Name was accepted in a set")
            .to_string()
            .contains("duplicate")
    );
    // The same two keys are legal in MDataMap because it is a sequence.
    let sequence = [2, 2, 0, 0, 0, 1, 2, 0, 251, 0, 0, 1, 17];
    let mut decoder = Decoder::new(&sequence, Encoding::Legacy).unwrap();
    let wire = Vec::<(WName, WMDataValue)>::read(&mut decoder).unwrap();
    decoder.finish().unwrap();
    let values =
        Vec::<(Name, MDataValue)>::from_wire(wire, &mut Restoration::new(0).unwrap()).unwrap();
    assert_eq!(values.len(), 2);
    assert_eq!(values[0].0, values[1].0);
    assert_eq!(values[0].1, MDataValue::Bool(true));
    assert_eq!(values[1].1, MDataValue::Nat(17));
}

#[test]
fn impossible_announced_sequences_do_not_reserve_before_complete_elements_exist() {
    use super::containers::{Map, Set};
    use super::syntax::{Unit, WName};
    use super::types::WBigNat;
    // 240MiB-ish announced storage, but not even the first u64 is present.
    let announced = 30_000_000u64.to_le_bytes();
    let mut r = Decoder::new(&announced, Encoding::V2).unwrap();
    assert!(Vec::<u64>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    // Tiny truncations distinguish evidence-based growth from an announced
    // count reserve without relying on rejection by the overall byte limit.
    let tiny = 2u64.to_le_bytes();
    let mut r = Decoder::new(&tiny, Encoding::V2).unwrap();
    assert!(Vec::<u64>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    let one = 1u64.to_le_bytes();
    let mut r = Decoder::new(&one, Encoding::V2).unwrap();
    assert!(Map::<WName, u64>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    let mut r = Decoder::new(&one, Encoding::V2).unwrap();
    assert!(Set::<WName>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    // A full node needs id + payload length + payload; an incomplete first
    // record must not reserve any PayloadNode capacity.
    for available in 0..12 {
        let mut partial = one.to_vec();
        partial.resize(8 + available, 0);
        let mut r = Decoder::new(&partial, Encoding::V2).unwrap();
        assert!(read_nodes(&mut r).is_err());
        assert_eq!(r.budget.remaining(), MAX_BYTES);
    }
    let mut big = 1u32.to_le_bytes().to_vec();
    big.extend(announced);
    let mut r = Decoder::new(&big, Encoding::V2).unwrap();
    assert!(WBigNat::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    let mut legacy = Decoder::new(&[2, 0, 0], Encoding::Legacy).unwrap();
    assert_eq!(Vec::<u64>::read(&mut legacy).unwrap(), [0, 0]);
    legacy.finish().unwrap();
    let count = 1_000_000u64.to_le_bytes();
    let mut r = Decoder::new(&count, Encoding::V2).unwrap();
    assert!(Map::<WName, u64>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    let mut r = Decoder::new(&count, Encoding::V2).unwrap();
    assert!(Set::<WName>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    let mut r = Decoder::new(&count, Encoding::V2).unwrap();
    assert!(read_nodes(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    let mut r = Decoder::new(&[], Encoding::V2).unwrap();
    assert!(Box::<WName>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
    // Do not use len<=remaining: legitimate zero-wire unit values exist.
    let zero_wire = 3u64.to_le_bytes();
    let mut r = Decoder::new(&zero_wire, Encoding::V2).unwrap();
    assert_eq!(Vec::<Unit>::read(&mut r).unwrap().len(), 3);
    r.finish().unwrap();
    let excessive = (MAX_BYTES as u64 + 1).to_le_bytes();
    let mut r = Decoder::new(&excessive, Encoding::V2).unwrap();
    assert!(Vec::<Unit>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES);
}

#[test]
fn decoded_sequence_capacity_growth_is_incremental_bounded_and_accounted() {
    // No custom allocator is needed to expose over-allocation: a prior
    // four-slot request may have produced six physical slots. A twelve-slot
    // target then requires eight additional charged slots, never six.
    let (target, delta) = primitive::collection_growth(4, 6, 6, 20).unwrap().unwrap();
    assert_eq!((target, delta), (12, 8));
    let mut budget = Budget::default();
    budget.allocate(4, size_of::<u64>()).unwrap();
    budget.allocate(delta, size_of::<u64>()).unwrap();
    assert_eq!(budget.remaining(), MAX_BYTES - 12 * size_of::<u64>());
    assert_eq!(
        primitive::collection_growth(4, 6, 4, 20).unwrap(),
        Some((12, 8)),
        "incidental slots must be charged before use, not only after they fill"
    );
    let mut bytes = 5u64.to_le_bytes().to_vec();
    for value in [1u64, 2, 3, 4, 5] {
        bytes.extend(value.to_le_bytes());
    }
    let mut r = Decoder::new(&bytes, Encoding::V2).unwrap();
    assert_eq!(Vec::<u64>::read(&mut r).unwrap(), [1, 2, 3, 4, 5]);
    assert_eq!(r.budget.remaining(), MAX_BYTES - 5 * size_of::<u64>());
    r.finish().unwrap();
    let mut partial = 30_000_000u64.to_le_bytes().to_vec();
    partial.extend(17u64.to_le_bytes());
    let mut r = Decoder::new(&partial, Encoding::V2).unwrap();
    assert!(Vec::<u64>::read(&mut r).is_err());
    assert_eq!(
        r.budget.remaining(),
        MAX_BYTES - 4 * size_of::<u64>(),
        "first parsed value may reserve only the initial bounded geometric chunk"
    );

    // The declared bound is ten, so the fifth complete value crosses from a
    // four-slot request to an eight-slot request, even though the sixth value
    // is absent. Accounting must charge capacity, not just five values.
    let mut crossing = 10u64.to_le_bytes().to_vec();
    for value in [1u64, 2, 3, 4, 5] {
        crossing.extend(value.to_le_bytes());
    }
    let mut r = Decoder::new(&crossing, Encoding::V2).unwrap();
    assert!(Vec::<u64>::read(&mut r).is_err());
    assert_eq!(r.budget.remaining(), MAX_BYTES - size_of::<[u64; 8]>());

    // Nested slices share the same aggregate accounting rather than resetting
    // their allowance each time an envelope payload becomes a new decoder.
    let bytes = [1u64.to_le_bytes(), 17u64.to_le_bytes()].concat();
    let mut first = Decoder::new(&bytes, Encoding::V2).unwrap();
    assert_eq!(Vec::<u64>::read(&mut first).unwrap(), [17]);
    let mut budget = first.finish().unwrap();
    assert_eq!(budget.remaining(), MAX_BYTES - size_of::<u64>());
    budget.allocate(MAX_BYTES - size_of::<u64>(), 1).unwrap();
    let mut second = Decoder::with_budget(&bytes, Encoding::V2, budget).unwrap();
    assert!(Vec::<u64>::read(&mut second).is_err());
    assert_eq!(
        second.budget.remaining(),
        0,
        "successive slice reset the aggregate budget"
    );
}
