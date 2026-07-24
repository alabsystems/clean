// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #3522: the `coq_alpha` shard writers (SerAPI
//! constant/axiom importer, mutual-inductive importer, and mutual-fixpoint
//! importer) must populate `MathverseConstantHeader::decl_kind` from the source
//! declaration shape rather than hardcoding the 0 byte.
//!
//! A hardcoded 0 byte is read as `DeclKind::Theorem`, silently mislabelling
//! every imported Coq constructor, inductive type, and axiom as a theorem
//! in downstream queries.
//!
//! Kept as an integration test (outside `src/coq_alpha.rs`) so the 1.5K-line
//! production file does not grow past its 500-line size budget.

use clean_mathverse::coq::alpha::{
    import_mutual_fixpoint, import_mutual_inductive, parse_sexp, sexp_to_mutual_inductive,
    CicFixBody, CicSort, CicTerm, CoqImporter,
};
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::types::DeclKind;

#[test]
fn test_coq_alpha_decl_kind_round_trip() {
    // (1) CoqConstant + CoqAxiom via import_sexp.
    let mut w = ShardWriter::new();
    let sexp = "(CoqConstant id (Prod A (Sort (Type 0)) (Prod _ (Rel 0) (Rel 1))) \
                 (Lambda A (Sort (Type 0)) (Lambda x (Rel 0) (Rel 0)))) \
                (CoqAxiom classic (Sort Prop))";
    let stats = CoqImporter.import_sexp(sexp, &mut w).expect("import");
    assert_eq!(stats.translated, 1);
    assert_eq!(stats.axiomatized, 1);

    let mut buf = Vec::new();
    w.write(&mut buf).expect("shard write");
    let reader = ShardReader::from_bytes(&buf).expect("shard read");

    let (_, hdr_def) = reader.lookup_name("id").expect("id present");
    assert_eq!(hdr_def.decl_kind, DeclKind::Definition as u8);
    let (_, hdr_ax) = reader.lookup_name("classic").expect("classic present");
    assert_eq!(hdr_ax.decl_kind, DeclKind::Axiom as u8);

    // (2) Mutual inductive: nat + its two constructors.
    let ind_input = r#"(MutualInductive (Params)
        (Body nat (Sort (Type 0)) (Ctor O (Sort (Type 0)))
            (Ctor S (Prod n (Ind nat 0) (Sort (Type 0))))))"#;
    let mind = sexp_to_mutual_inductive(&parse_sexp(ind_input).expect("parse")).expect("mind");
    let mut w2 = ShardWriter::new();
    import_mutual_inductive(&mind, "Coq.Init.Datatypes", &mut w2).expect("import mind");
    let mut buf2 = Vec::new();
    w2.write(&mut buf2).expect("shard write");
    let reader2 = ShardReader::from_bytes(&buf2).expect("shard read");

    let (_, hdr_ind) = reader2.lookup_name("nat").expect("nat present");
    assert_eq!(hdr_ind.decl_kind, DeclKind::Inductive as u8);
    let (_, hdr_o) = reader2.lookup_name("nat.O").expect("nat.O present");
    assert_eq!(hdr_o.decl_kind, DeclKind::Constructor as u8);
    let (_, hdr_s) = reader2.lookup_name("nat.S").expect("nat.S present");
    assert_eq!(hdr_s.decl_kind, DeclKind::Constructor as u8);

    // (3) Mutual fixpoint: focused body is a Definition, others Axiom.
    let bodies = vec![
        CicFixBody {
            name: "even_fix".into(),
            type_: CicTerm::Sort(CicSort::type_at(0)),
            body: CicTerm::Rel(0),
            recursive_arg_idx: 0,
        },
        CicFixBody {
            name: "odd_fix".into(),
            type_: CicTerm::Sort(CicSort::type_at(0)),
            body: CicTerm::Rel(0),
            recursive_arg_idx: 0,
        },
    ];
    let mut w3 = ShardWriter::new();
    import_mutual_fixpoint(&bodies, 0, "Coq.Init.Nat", &mut w3).expect("import fix");
    let mut buf3 = Vec::new();
    w3.write(&mut buf3).expect("shard write");
    let reader3 = ShardReader::from_bytes(&buf3).expect("shard read");

    let (_, hdr_focus) = reader3.lookup_name("even_fix").expect("even_fix present");
    assert_eq!(hdr_focus.decl_kind, DeclKind::Definition as u8);
    let (_, hdr_other) = reader3.lookup_name("odd_fix").expect("odd_fix present");
    assert_eq!(hdr_other.decl_kind, DeclKind::Axiom as u8);

    // Guard against silent revert: no written header should have the
    // legacy 0 default for a non-theorem constant in this test.
    assert_ne!(hdr_def.decl_kind, DeclKind::Theorem as u8);
    assert_ne!(hdr_ind.decl_kind, DeclKind::Theorem as u8);
    assert_ne!(hdr_o.decl_kind, DeclKind::Theorem as u8);
    assert_ne!(hdr_focus.decl_kind, DeclKind::Theorem as u8);
}
