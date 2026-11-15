// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual Clean registration of the numeric request model, not Rust admission.

use super::{
    declarations, DeclarationInput, DATA_NAMES, INDUCTIVE_NAMES, NEGATIVE_CONTROLS, PROOF_ROOTS,
    PROP_PROOF_ROOTS, TYPE_PROOF_ROOTS,
};
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::{parse_check, run_with_stack, shared_spec};
use clean_kernel::{ConstantKind, Level, Name, TypeChecker};
use clean_parser::{parse_decl, SurfaceDecl};
use std::collections::HashSet;

const EXPECTED_PROOFS: &[&str] = &[
    "dia_entries_sound",
    "dia_stored_constant_admission",
    "dia_stored_constant_prior_sound",
    "dia_stored_family_prior_sound",
    "dia_input_admitted",
    "dia_input_to_old_chain",
    "dia_old_chain_trans",
    "dia_chain_to_old_chain",
    "dia_input_preserves_sound",
    "dia_chain_admitted",
    "dia_chain_sound",
    "dia_fresh_family",
    "dia_fresh_constant",
    "dia_reuse_family",
    "dia_reuse_constant",
    "dia_mixed_chain",
    "dia_mixed_admissions",
    "dia_mixed_preservation",
    "dia_reused_family_admitted",
    "dia_reused_constant_admitted",
];

const ADMITTED_TYPE: &str = r"forall (env : KEnv) (input : KernelDeclInput) (out : KEnv),
 KernelDeclInputAccepts env input out -> EnvSound env -> KernelDeclInputAdmission input";

const CHAIN_SOUND_TYPE: &str = r"forall (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv) (ctx : KernelLocalCtx),
 KernelDeclInputChain env inputs out -> KernelStateMatchesSpec (KernelState.mk env ctx) -> EnvSound env ->
 ProdType (KernelStateMatchesSpec (KernelState.mk out ctx))
  (ProdType (EnvSound out) (dia_requests_admitted inputs))";

struct CarrierContract {
    name: &'static str,
    ty: &'static str,
    params: u32,
    indices: u32,
    constructors: &'static [(&'static str, u32)],
}

const CARRIERS: &[CarrierContract] = &[
    CarrierContract {
        name: "KernelDeclInput",
        ty: "Type",
        params: 0,
        indices: 0,
        constructors: &[("const_", 4), ("inductive_", 4)],
    },
    CarrierContract {
        name: "KernelDeclInputAdmission",
        ty: "KernelDeclInput -> Type",
        params: 1,
        indices: 0,
        constructors: &[("mk", 3)],
    },
    CarrierContract {
        name: "KernelDeclInputAccepts",
        ty: "KEnv -> KernelDeclInput -> KEnv -> Type",
        params: 1,
        indices: 2,
        constructors: &[
            ("const_fresh", 5),
            ("inductive_fresh", 5),
            ("const_reuse", 7),
            ("inductive_reuse", 7),
        ],
    },
    CarrierContract {
        name: "KernelDeclInputChain",
        ty: "KEnv -> ListType KernelDeclInput -> KEnv -> Type",
        params: 0,
        indices: 3,
        constructors: &[("nil", 1), ("cons", 7)],
    },
];

mod callers;
mod checks;
mod refusals;

use checks::{assert_sort, elaborate, empty_closures, record, tuple_ast};

#[test]
fn declaration_input_admission_exact_partitions_parse() {
    assert_eq!(PROOF_ROOTS, EXPECTED_PROOFS);
    assert_eq!(TYPE_PROOF_ROOTS, EXPECTED_PROOFS);
    assert!(PROP_PROOF_ROOTS.is_empty());
    assert_eq!(
        DATA_NAMES,
        &[
            "dia_admission_at",
            "dia_requests_admitted",
            "dia_family_request",
            "dia_constant_request",
            "dia_mixed_requests"
        ]
    );
    assert_eq!(
        INDUCTIVE_NAMES,
        CARRIERS.iter().map(|c| c.name).collect::<Vec<_>>()
    );
    let (mut proofs, mut data, mut carriers) = (Vec::new(), Vec::new(), Vec::new());
    let mut names = HashSet::new();
    for declaration in declarations() {
        match declaration {
            DeclarationInput::Inductive(source) => {
                parse_check(source).expect("carrier source parses");
                let SurfaceDecl::Inductive { name, ctors, .. } =
                    parse_decl(source).expect("carrier AST")
                else {
                    panic!("real carrier declaration")
                };
                let contract = CARRIERS
                    .iter()
                    .find(|c| clean_parser::parse_name(c.name).expect("name") == name)
                    .expect("reviewed carrier");
                assert_eq!(
                    ctors.iter().map(|c| c.name.clone()).collect::<Vec<_>>(),
                    contract
                        .constructors
                        .iter()
                        .map(|(n, _)| clean_parser::parse_name(n).expect("constructor name"))
                        .collect::<Vec<_>>()
                );
                assert!(names.insert(contract.name));
                carriers.push(contract.name);
            }
            DeclarationInput::Proof(name, ty, body) => {
                tuple_ast(name, ty, body);
                assert!(names.insert(name));
                proofs.push(*name);
            }
            DeclarationInput::Data(name, ty, body) => {
                tuple_ast(name, ty, body);
                assert!(names.insert(name));
                data.push(*name);
            }
        }
    }
    assert_eq!(proofs, EXPECTED_PROOFS);
    assert_eq!(data, DATA_NAMES);
    assert_eq!(carriers, INDUCTIVE_NAMES);
    assert_eq!(names.len(), 29);
    for &(name, ty, body) in NEGATIVE_CONTROLS {
        assert!(names.insert(name), "fresh negative name");
        tuple_ast(name, ty, body);
    }
    assert_eq!(NEGATIVE_CONTROLS.len(), 9);
    assert_eq!(names.len(), 38);
}

#[test]
fn declaration_input_admission_actual_records_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut proofs, mut data) = (0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => {
                    record(spec, name, ty, body, true);
                    proofs += 1;
                }
                DeclarationInput::Data(name, ty, body) => {
                    record(spec, name, ty, body, false);
                    data += 1;
                }
                DeclarationInput::Inductive(_) => {}
            }
        }
        assert_eq!((proofs, data), (20, 5));
    });
}

#[test]
fn declaration_input_admission_real_carrier_contracts() {
    run_with_stack(|| {
        let spec = shared_spec();
        for contract in CARRIERS {
            let root = Name::from_string(contract.name);
            let metadata = spec.env().get_inductive(&root).expect("real carrier");
            let constant = spec.env().get_const(&root).expect("type former");
            let record = spec
                .definitions()
                .get(contract.name)
                .expect("carrier record");
            assert!(!record.is_axiom);
            assert_eq!(record.category, AxiomCategory::FoundationalRule);
            assert_eq!(record.proof_status, ProofStatus::DerivedPending);
            assert!(record.value_src.is_none() && record.elaborated_value.is_none());
            assert!(constant.value.is_none());
            assert_ne!(constant.kind, ConstantKind::Axiom);
            assert_eq!(record.elaborated_type.as_ref(), Some(&constant.type_));
            assert_eq!(metadata.type_, constant.type_);
            assert_eq!(
                (metadata.num_params, metadata.num_indices),
                (contract.params, contract.indices)
            );
            assert!(metadata.level_params.is_empty());
            let expected = elaborate(spec, contract.ty);
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            assert!(
                checker.is_def_eq(&constant.type_, &expected),
                "{}: exact former",
                contract.name
            );
            assert_sort(
                spec,
                &constant.type_,
                Level::succ(Level::succ(Level::zero())),
            );
            assert_eq!(
                metadata.constructor_names,
                contract
                    .constructors
                    .iter()
                    .map(|(n, _)| Name::from_string(&format!("{}.{n}", contract.name)))
                    .collect::<Vec<_>>()
            );
            empty_closures(spec, contract.name);
            for (index, (suffix, fields)) in contract.constructors.iter().enumerate() {
                let name = format!("{}.{suffix}", contract.name);
                let ctor_root = Name::from_string(&name);
                let ctor = spec
                    .env()
                    .get_constructor(&ctor_root)
                    .expect("real constructor");
                let constant = spec
                    .env()
                    .get_const(&ctor_root)
                    .expect("constructor constant");
                assert_eq!(ctor.inductive_name, root);
                assert_eq!(ctor.constructor_idx as usize, index);
                assert_eq!(ctor.num_params, contract.params);
                assert_eq!(ctor.num_fields, *fields);
                assert_eq!(ctor.type_, constant.type_);
                assert_ne!(constant.kind, ConstantKind::Axiom);
                assert!(constant.value.is_none());
                assert_sort(spec, &constant.type_, Level::succ(Level::zero()));
                empty_closures(spec, &name);
            }
            let recursor = format!("{}.rec", contract.name);
            assert!(spec
                .env()
                .get_const(&Name::from_string(&recursor))
                .is_some());
            empty_closures(spec, &recursor);
        }
    });
}
