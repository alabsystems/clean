// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CIC declaration extraction.

use super::*;
use crate::coq::extended::sexp_parser::parse_sexp;

#[test]
fn test_extract_definition() {
    let sexp = parse_sexp("(Definition mydef (Prop) (Rel 0))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name, "mydef");
    assert_eq!(decls[0].kind, CicDeclKind::Definition);
    assert!(decls[0].type_sexp.is_some());
    assert!(decls[0].body_sexp.is_some());
}

#[test]
fn test_extract_theorem() {
    let sexp = parse_sexp("(Theorem add_comm (Prod n Nat Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name, "add_comm");
    assert_eq!(decls[0].kind, CicDeclKind::Theorem);
}

#[test]
fn test_extract_lemma() {
    let sexp = parse_sexp("(Lemma foo_bar (Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::Lemma);
}

#[test]
fn test_extract_axiom_has_profile() {
    let sexp = parse_sexp("(Axiom func_ext (Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::Axiom);
    assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_extract_coinductive_has_profile() {
    let sexp = parse_sexp("(CoInductive stream (Prod A Set Set))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::CoInductive);
    assert!(decls[0].axiom_profile.has(AxiomProfile::COQ_COINDUCTIVE));
}

#[test]
fn test_extract_inductive() {
    let sexp = parse_sexp("(Inductive (nat (Sort Type)))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::Inductive);
    assert_eq!(decls[0].name, "nat");
}

#[test]
fn test_extract_record() {
    let sexp = parse_sexp("(Record point (Prod x R (Prod y R Set)))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::Record);
}

#[test]
fn test_extract_class() {
    let sexp = parse_sexp("(Class Eq (Prod A Type Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::Class);
}

#[test]
fn test_extract_instance() {
    let sexp = parse_sexp("(Instance nat_eq (App Eq nat) (Rel 0))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::Instance);
}

#[test]
fn test_extract_canonical_structure() {
    let sexp = parse_sexp("(Canonical nat_eqType (nat_eqMixin))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].kind, CicDeclKind::CanonicalStructure);
}

#[test]
fn test_extract_module_with_nested_decls() {
    let sexp = parse_sexp("(Module Foo (Definition bar (Prop)) (Theorem baz (Prop)))").unwrap();
    let decls = extract_declarations(&sexp);
    // Module itself + bar + baz
    assert_eq!(decls.len(), 3);
    assert_eq!(decls[0].kind, CicDeclKind::Module);
    assert_eq!(decls[0].name, "Foo");
    assert_eq!(decls[1].name, "Foo.bar");
    assert_eq!(decls[2].name, "Foo.baz");
}

#[test]
fn test_extract_module_functor() {
    let sexp = parse_sexp("(Module F (ModuleParams (A Type)) (Definition id (Rel 0)))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls[0].kind, CicDeclKind::ModuleFunctor);
    assert!(decls[0].axiom_profile.has(AxiomProfile::COQ_MODULE_FUNCTOR));
}

#[test]
fn test_flocq_profile_detection() {
    let sexp = parse_sexp("(Definition Flocq.Core.Float_prop.round_correct (Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert!(decls[0].axiom_profile.has(AxiomProfile::FLOAT_APPROX));
}

#[test]
fn test_mathcomp_profile_detection() {
    let sexp = parse_sexp("(Theorem mathcomp.algebra.ring.addrC (Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert!(decls[0].axiom_profile.has(AxiomProfile::CLASSICAL));
}

#[test]
fn test_compcert_profile_detection() {
    let sexp = parse_sexp("(Axiom compcert.common.Memory.load_valid (Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_sprop_profile_detection() {
    let sexp = parse_sexp("(Definition use_SProp_elim (Prop))").unwrap();
    let decls = extract_declarations(&sexp);
    assert_eq!(decls.len(), 1);
    assert!(decls[0].axiom_profile.has(AxiomProfile::COQ_SPROP));
}

#[test]
fn test_extract_from_stream() {
    let sexps = crate::coq::extended::sexp_parser::parse_sexp_stream(
        "(Theorem t1 (Prop)) (Definition d1 (Prop) (Rel 0)) (Axiom a1 (Prop))",
    )
    .unwrap();
    let decls = extract_declarations_from_stream(&sexps);
    assert_eq!(decls.len(), 3);
}

#[test]
fn test_extract_unknown_tag_skipped() {
    let sexp = parse_sexp("(UnknownForm x y z)").unwrap();
    let decls = extract_declarations(&sexp);
    assert!(decls.is_empty());
}
