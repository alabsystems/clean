// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::library::MathverseLibrary;
use crate::shard::ShardReader;
use crate::trust::policy::TrustPolicy;
use crate::verify::incremental::{
    verify_corpus_incremental_with_env_policy, IncrementalVerifyReport, InductiveReplayPolicy,
};

fn reader(writer: ShardWriter) -> ShardReader {
    let mut bytes = Vec::new();
    writer.write(&mut bytes).expect("serialize candidate shard");
    ShardReader::from_bytes(&bytes).expect("read candidate shard")
}

fn assert_unverified(reader: &ShardReader, count: usize) {
    assert_eq!(reader.constants.len(), count);
    for header in &reader.constants {
        let name = &reader.strings[header.name_idx as usize];
        assert_eq!(
            header.import_confidence,
            ImportConfidence::Unverified as u8,
            "raw family member {name} has not passed checked replay"
        );
        assert!(!header.has_value(), "family metadata remains value-less");
        assert!(
            !TrustPolicy::default().is_visible(header),
            "unverified family {name} is not default trusted search material"
        );
    }
}

fn replay(reader: &ShardReader) -> IncrementalVerifyReport {
    // Replay must examine candidates even when ordinary trusted search hides them.
    let mut library = MathverseLibrary::new(TrustPolicy::default());
    library.load_shard(reader).expect("load candidate shard");
    let mut env = clean_kernel::Environment::try_with_prelude().expect("kernel prelude");
    env.set_cumulative(true);
    verify_corpus_incremental_with_env_policy(&library, env, InductiveReplayPolicy::Generate).1
}

fn assert_replayed(reader: &ShardReader) {
    let report = replay(reader);
    assert_eq!(report.total, reader.constants.len());
    for header in &reader.constants {
        let name = &reader.strings[header.name_idx as usize];
        assert!(
            report.kernel_verified_names.contains(name),
            "checked replay must independently earn {name}: {:?}",
            report.failures
        );
    }
}

#[test]
fn serapi_family_is_unverified_until_checked_replay() {
    let mut writer = ShardWriter::new();
    CoqImporter
        .import_sexp(
            "(CoqInductive P7.nat 0 (Sort Set) \
             (Ctor O (Ind P7.nat 0)) \
             (Ctor S (Prod n (Ind P7.nat 0) (Ind P7.nat 0))))",
            &mut writer,
        )
        .expect("parse family candidate");
    let reader = reader(writer);
    assert_unverified(&reader, 3);
    assert_replayed(&reader);
}

#[test]
fn template_product_is_unverified_until_checked_replay() {
    let mut writer = ShardWriter::new();
    assert_eq!(emit_template_poly_prod(&mut writer), 2);
    let reader = reader(writer);
    assert_unverified(&reader, 2);
    assert_replayed(&reader);
}

#[test]
fn malformed_constructor_is_not_preverified_or_replayed() {
    let mut writer = ShardWriter::new();
    CoqImporter
        .import_sexp(
            "(CoqInductive P7.bad 0 (Sort Set) (Ctor bogus (Sort Prop)))",
            &mut writer,
        )
        .expect("syntax permits this invalid family candidate");
    let reader = reader(writer);
    assert_unverified(&reader, 2);
    let report = replay(&reader);
    assert_eq!(report.total, 2);
    // The root's arity is independently valid as an empty type. The bad
    // constructor itself, whose result is Prop rather than that type, is not.
    let constructor = reader.strings[reader.constants[1].name_idx as usize].clone();
    assert!(!report.kernel_verified_names.contains(&constructor));
    assert!(report.failures.iter().any(|(name, _)| name == &constructor));
}

#[test]
fn ill_typed_family_root_never_receives_kernel_verified() {
    let mut writer = ShardWriter::new();
    CoqImporter
        .import_sexp(
            "(CoqInductive P7.badRoot 0 (App (Sort Prop) (Sort Prop)) \
             (Ctor bogus (Ind P7.badRoot 0)))",
            &mut writer,
        )
        .expect("syntax permits an ill-typed arity candidate");
    let reader = reader(writer);
    assert_unverified(&reader, 2);
    let report = replay(&reader);
    assert_eq!(report.total, 2);
    assert_eq!(
        report.kernel_verified, 0,
        "{:?}",
        report.kernel_verified_names
    );
    assert!(report.kernel_verified_names.is_empty());
    assert!(report.failed + report.axiom_fallback + report.reconstruct_failed > 0);
}
