// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The W4 sources parse; the W4b device registers, re-derives `ir_lzd_ctr` and proves
//! `is_zfc_set_equiv` safe under its callee's contract, with an empty axiom closure.

use super::*;
use crate::axiom_ratchet::live_env_axioms;
use crate::test_utils::{build_eval_ir_spec_with_stack, build_spec_with_stack, run_with_stack};
use clean_kernel::{ConstantKind, Environment, Name};
use std::collections::BTreeSet;

/// Every axiom reachable from `root` through types, values and recursor rules.
fn axioms_reachable(env: &Environment, root: &str) -> BTreeSet<Name> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![Name::from_string(root)];
    let mut axioms = BTreeSet::new();
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.kind == ConstantKind::Axiom {
            axioms.insert(name.clone());
        }
        let mut next = info.type_.collect_constants();
        if let Some(v) = &info.value {
            v.collect_constants_into(&mut next);
        }
        if let Some(rec) = env.get_recursor(&name) {
            for rule in &rec.rules {
                rule.rhs.collect_constants_into(&mut next);
            }
        }
        stack.extend(next);
    }
    axioms
}

fn report(label: &str, times: &[(String, f64)]) {
    let total: f64 = times.iter().map(|(_, s)| s).sum();
    for (name, secs) in times {
        eprintln!("W4 {label} {secs:9.4}s {name}");
    }
    eprintln!(
        "W4 {label} total {total:.3}s over {} declarations",
        times.len()
    );
}

#[test]
fn test_vcg_sources_parse_ascii_unique_and_certified_by_refl() {
    assert!(
        VCG_DEVICE.is_ascii() && VCG_LZD.is_ascii(),
        "spec sources stay ASCII"
    );
    assert!(VCG_LZD
        .starts_with("-- MINTED by reports/crystal-lane/2026-09-30-link4-m0/w4/gen_vcg_lzd.py"));
    let device = vcg_decls(VCG_DEVICE, None);
    let lzd = vcg_decls(VCG_LZD, Some(VCG_TABLE_MARKER));
    let table = vcg_lzd_table();
    assert!(!device.is_empty() && !lzd.is_empty());
    let names: Vec<&str> = table.iter().map(|d| d.name.as_str()).collect();
    assert_eq!(
        names,
        [
            "ir_vcg_lzd_local",
            "ir_vcg_lzd_ctr",
            "ir_vcg_lzd_ctr_gives_landed",
            "ir_vcg_lzd_landed_gives_ctr"
        ]
    );
    let mut seen = BTreeSet::new();
    for d in device.iter().chain(&lzd).chain(&table) {
        assert!(
            seen.insert(d.name.clone()),
            "duplicate declaration {}",
            d.name
        );
        assert_eq!(
            d.source.matches('(').count(),
            d.source.matches(')').count(),
            "{}",
            d.name
        );
        assert!(!d.source.contains("sorry"), "{}", d.name);
    }
    // The body's behaviour is decided ONLY by the per-segment certificates, each one Eq.refl.
    let certificates: Vec<&VcgDecl> = lzd.iter().filter(|d| d.name.ends_with("_chk")).collect();
    assert!(!certificates.is_empty());
    for d in &certificates {
        assert!(
            d.source
                .contains(":= Eq.refl (IRList IRConfig) (ir_vcg_obl_"),
            "{} is not an Eq.refl certificate",
            d.name
        );
    }
    // ... and the contract is the group-soundness theorem over the regenerated local obligation.
    assert!(table[1]
        .source
        .contains("ir_ctr_group_sound ir_lzd_module IRLzdIn"));
    assert!(table[1].source.contains("ir_vcg_lzd_local n"));
}

/// `ir_lzd`'s node count (all five functions; the deref chain is stepped, not contracted).
const LZD_NODES: f64 = 76.0;
/// `is_zfc_set_equiv`'s node count (its callee is contracted, so only the body counts).
const ZSE_NODES: f64 = 307.0;

fn total(times: &[(String, f64)]) -> f64 {
    times.iter().map(|(_, s)| s).sum()
}

/// The certificate shape every W4b segment takes: ONE abstract-environment `Eq.refl`.
const W4B_CERT_BODY: &str = ":= (fun env mem d r => (Eq.refl _ _))";

/// The landed ByteV1 trie now provides the scratch device's helper names.
/// Give the scratch FUNCTION definitions their own names and recheck every
/// one, retaining the shared inductive types and every original proof body.
/// The generated source files remain the standalone W4b record's inputs.
fn isolated_w4b_decls(mut decls: Vec<VcgDecl>) -> Vec<VcgDecl> {
    fn identifier(c: char) -> bool {
        c.is_ascii_alphanumeric() || matches!(c, '_' | '\'' | '.')
    }
    fn rename(name: &str) -> String {
        if matches!(
            name,
            "ir_bm_bcase"
                | "ir_bt_bget"
                | "ir_bt_bset"
                | "ir_bt_bget_bset_same"
                | "ir_bt_bget_bset_other"
                | "ir_bt_get"
                | "ir_bt_set"
                | "ir_bt_get_leaf"
                | "ir_bt_get_set_same"
                | "ir_bt_get_set_other"
                | "ir_bt_get_set"
        ) {
            format!("w4b_scratch_{name}")
        } else {
            name.to_owned()
        }
    }
    assert!(decls
        .iter()
        .all(|decl| !decl.name.starts_with("w4b_scratch_")));
    for decl in &mut decls {
        // This fixture fragment contains identifiers/numerals, not strings;
        // refuse a future string-bearing source instead of rewriting data.
        assert!(!decl.source.contains('"'));
        decl.source = decl
            .source
            .split_inclusive(|c| !identifier(c))
            .map(|part| {
                let name = part.trim_end_matches(|c| !identifier(c));
                rename(name) + &part[name.len()..]
            })
            .collect();
        decl.name = rename(&decl.name);
    }
    decls
}

#[test]
fn test_w4b_sources_parse_ascii_unique_and_certified_by_refl() {
    for (name, text) in [
        ("w4b_device", W4B_DEVICE),
        ("w4b_lzd", W4B_LZD),
        ("w4b_zse_module", W4B_ZSE_MODULE),
        ("w4b_zse", W4B_ZSE),
    ] {
        assert!(text.is_ascii(), "{name}: spec sources stay ASCII");
    }
    assert!(W4B_LZD
        .starts_with("-- MINTED by reports/crystal-lane/2026-10-07-link4-m0/w4b/gen/gen_lzd5.py"));
    assert!(W4B_ZSE
        .starts_with("-- MINTED by reports/crystal-lane/2026-10-07-link4-m0/w4b/gen/gen_zse.py"));
    let device = vcg_decls(W4B_DEVICE, None);
    let lzd = vcg_decls(W4B_LZD, Some(VCG_TABLE_MARKER));
    let table = vcg_table(W4B_LZD);
    let module = vcg_decls(W4B_ZSE_MODULE, None);
    let zse = vcg_decls(W4B_ZSE, None);
    let names: Vec<&str> = table.iter().map(|d| d.name.as_str()).collect();
    assert_eq!(
        names,
        [
            "vz_local",
            "vz_ctr",
            "vz_ctr_gives_landed",
            "vz_landed_gives_ctr"
        ]
    );
    let mut seen = BTreeSet::new();
    for d in device
        .iter()
        .chain(&lzd)
        .chain(&table)
        .chain(&module)
        .chain(&zse)
    {
        assert!(
            seen.insert(d.name.clone()),
            "duplicate declaration {}",
            d.name
        );
        assert_eq!(
            d.source.matches('(').count(),
            d.source.matches(')').count(),
            "{}",
            d.name
        );
        assert!(!d.source.contains("sorry"), "{}", d.name);
    }
    // Each body's behaviour is decided ONLY by its per-segment certificates, each one Eq.refl over
    // an abstract environment; the glue never runs the machine itself.
    for (body, glue, expect) in [("ir_lzd", &lzd, 13usize), ("is_zfc_set_equiv", &zse, 101)] {
        let certs: Vec<&VcgDecl> = glue
            .iter()
            .filter(|d| d.source.contains(" : ir_vcg_cert "))
            .collect();
        assert_eq!(certs.len(), expect, "{body}: one certificate per segment");
        for d in &certs {
            assert!(
                d.source.ends_with(W4B_CERT_BODY),
                "{} is not an Eq.refl certificate",
                d.name
            );
        }
        for d in glue.iter() {
            assert!(
                !d.source.contains("ir_step ") && !d.source.contains("ir_steps "),
                "{}: the glue never steps the machine; only the device's lemmas do",
                d.name
            );
        }
    }
    assert!(table[1]
        .source
        .contains("ir_ctr_group_sound ir_lzd_module IRLzdIn"));
    assert!(table[1].source.contains("vz_local n"));
}

/// The W4b device and both bodies' per-function glue register on the EvalIR bundle (T3's
/// registration figure, per node, comes from this test's report in a release build).
#[test]
fn test_w4b_device_and_both_bodies_register_on_eval_ir_bundle() {
    run_with_stack(|| {
        let mut spec = build_eval_ir_spec_with_stack();
        let device = spec
            .add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_decls(W4B_DEVICE, None)))
            .expect("the W4b device registers");
        let lzd = spec
            .add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_decls(
                W4B_LZD,
                Some(VCG_TABLE_MARKER),
            )))
            .expect("ir_lzd's per-case glue registers");
        let module = spec
            .add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_decls(W4B_ZSE_MODULE, None)))
            .expect("the second body's module registers");
        let zse = spec
            .add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_decls(W4B_ZSE, None)))
            .expect("is_zfc_set_equiv's glue registers");
        report("w4b-device", &device);
        report("w4b-lzd", &lzd);
        report("w4b-zse-module", &module);
        report("w4b-zse", &zse);
        eprintln!(
            "W4B per-node registration: ir_lzd (cases) {:.2} ms/node, is_zfc_set_equiv {:.2} ms/node",
            total(&lzd) * 1000.0 / LZD_NODES,
            total(&zse) * 1000.0 / ZSE_NODES
        );
        for root in [
            "ir_vcg_run_sound",
            "ir_vcg_step_ft",
            "ir_vcg_callo",
            "ir_vcg_postfs_sound",
            "ir_vcg_xretT",
            "vz_deref",
            "zs_ctr",
        ] {
            assert!(
                spec.env().get_const(&Name::from_string(root)).is_some(),
                "{root} registered"
            );
            assert_eq!(
                axioms_reachable(spec.env(), root),
                BTreeSet::new(),
                "{root} reaches an axiom"
            );
        }
    });
}

/// The contract table on the full spec: `vz_ctr` has the landed `ir_lzd_ctr`'s statement, both
/// `ir_ctr_weaken` directions check, nothing reaches an axiom, and the census is unchanged.
#[test]
fn test_w4b_lzd_ctr_rederived_on_full_spec() {
    #[derive(serde::Deserialize)]
    struct GoldenAxiom {
        name: String,
    }
    #[derive(serde::Deserialize)]
    struct Golden {
        count: usize,
        axioms: Vec<GoldenAxiom>,
    }
    let golden: Golden = serde_json::from_str(include_str!(
        "../../../../../data/clean_verify_axiom_ratchet.json"
    ))
    .expect("the axiom ratchet parses");
    run_with_stack(move || {
        let mut spec = build_spec_with_stack();
        spec.add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_decls(W4B_DEVICE, None)))
            .expect("the W4b device registers");
        let lzd = spec
            .add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_decls(
                W4B_LZD,
                Some(VCG_TABLE_MARKER),
            )))
            .expect("per-case glue registers");
        let table = spec
            .add_eval_ir_vcg_decls(&isolated_w4b_decls(vcg_table(W4B_LZD)))
            .expect("the contract table registers");
        report("w4b-lzd-full", &lzd);
        report("w4b-table", &table);
        eprintln!(
            "W4B per-node registration (full spec): ir_lzd glue + table {:.2} ms/node",
            (total(&lzd) + total(&table)) * 1000.0 / LZD_NODES
        );
        let env = spec.env();
        let ours = env.get_const(&Name::from_string("vz_ctr")).expect("vz_ctr");
        let landed = env
            .get_const(&Name::from_string("ir_lzd_ctr"))
            .expect("ir_lzd_ctr");
        assert_eq!(
            ours.type_, landed.type_,
            "the re-derived contract states exactly the landed one"
        );
        for root in ["vz_ctr", "vz_ctr_gives_landed", "vz_landed_gives_ctr"] {
            assert_eq!(
                axioms_reachable(env, root),
                BTreeSet::new(),
                "{root} reaches an axiom"
            );
        }
        let live: BTreeSet<String> = live_env_axioms(&spec).into_iter().map(|a| a.name).collect();
        let pinned: BTreeSet<String> = golden.axioms.into_iter().map(|a| a.name).collect();
        assert_eq!(golden.count, 11, "the census the plan holds fixed");
        assert_eq!(
            live, pinned,
            "registering W4b changes the kernel axiom census"
        );
    });
}
