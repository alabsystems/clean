// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! F3's live inventory through the production environment constructor.
//! This supplements the kernel's CLI mirror through the actual production
//! constructor. Both must stay at zero non-foundational value-less constants.

use super::{module_elaboration_lock, module_environment, EnvironmentSetup};
use clean_kernel::env::is_canonical_foundational_constant;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, Name, QuotKind};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::path::PathBuf;

fn ratchet() -> Value {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/prelude_axiom_ratchet.json");
    serde_json::from_str(&std::fs::read_to_string(path).expect("read prelude ratchet"))
        .expect("parse prelude ratchet")
}

fn non_foundational(env: &Environment) -> BTreeSet<String> {
    env.constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .filter(|c| !is_canonical_foundational_constant(c))
        .filter(|c| {
            !env.get_quot(&c.name)
                .is_some_and(|q| q.kind != QuotKind::Sound)
        })
        .map(|c| c.name.to_string())
        .collect()
}

fn ratchet_problems(env: &Environment, pin: &Value) -> Vec<String> {
    let live = non_foundational(env);
    let mut allowed = BTreeSet::new();
    for bucket in [
        "debt_signature",
        "debt_proposition",
        "debt_inhabitation",
        "unknown_sort",
        "trust_markers",
        "admitted_domain",
    ] {
        for name in pin[bucket].as_array().expect("ratchet name bucket") {
            allowed.insert(name.as_str().expect("ratchet name").to_owned());
        }
    }
    let mut problems: Vec<_> = live
        .difference(&allowed)
        .map(|name| format!("unpinned non-foundational axiom: {name}"))
        .collect();
    let ceiling = pin["baseline_non_foundational"]
        .as_u64()
        .expect("ratchet ceiling");
    if live.len() as u64 > ceiling {
        problems.push(format!(
            "non-foundational count {} exceeds baseline {ceiling}",
            live.len()
        ));
    }
    let floor = pin["floor_total_declarations"]
        .as_u64()
        .expect("ratchet declaration floor");
    if (env.constants().count() as u64) < floor {
        problems.push(format!(
            "production environment is below declaration floor {floor}"
        ));
    }
    problems
}

#[test]
fn test_self_proof_f3_production_prelude_census() -> Result<(), Box<dyn std::error::Error>> {
    let _lock = module_elaboration_lock();
    let mut env = module_environment(EnvironmentSetup::default()).expect("production environment");
    let pin = ratchet();
    let problems = ratchet_problems(&env, &pin);
    assert!(
        problems.is_empty(),
        "production prelude ratchet: {problems:#?}"
    );

    let names = non_foundational(&env);
    assert_eq!(pin["baseline_non_foundational"], json!(0));
    assert!(
        names.is_empty(),
        "F3 default constructor must remain at zero"
    );
    let report = json!({
        "schema": "clean-self-proof-f3-production-census-v1",
        "constructor": "clean_elab::module_driver::module_environment(EnvironmentSetup::default())",
        "total_declarations": env.constants().count(),
        "non_foundational_axioms": names,
        "observed_non_foundational": names.len(),
        "pinned_ceiling": pin["baseline_non_foundational"],
        "f3_zero_census_holds": names.is_empty(),
        "scope": "Axiom-kind constants excluding canonical foundations and registered quotient primitives; no proof or parity claim",
    });
    eprintln!("F3 production census: {report}");
    // Explicit artifact minting only; a normal test run never edits the tree.
    if let Some(path) = std::env::var_os("CLEAN_SELF_PROOF_F3_CENSUS_OUT") {
        std::fs::write(
            path,
            format!("{}\n", serde_json::to_string_pretty(&report)?),
        )?;
    }

    // The production constructor now satisfies the zero baseline. Exercise
    // that positive case before requiring the planted-axiom refusal below.
    let mut zero = pin.clone();
    zero["baseline_non_foundational"] = json!(0);
    assert!(ratchet_problems(&env, &zero).is_empty());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("SelfProofF3.planted"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .expect("well-typed planted axiom");
    let planted = ratchet_problems(&env, &pin);
    assert!(planted
        .iter()
        .any(|p| p == "unpinned non-foundational axiom: SelfProofF3.planted"));
    assert!(ratchet_problems(&env, &zero)
        .iter()
        .any(|p| p.contains("exceeds baseline 0")));
    eprintln!("F3 negative control refused planted axiom: {planted:?}");
    Ok(())
}

fn register_source(
    env: &mut Environment,
    source: &str,
) -> Result<crate::ElabResult, crate::ElabError> {
    let decl = clean_parser::parse_decl_exact(source).expect("F3 fixture parses exactly");
    crate::elaborate_decl_and_register(env, &decl)
}

#[test]
fn test_self_proof_f3_source_requests_preserve_zero_and_refusals() {
    let _lock = module_elaboration_lock();
    let mut env = module_environment(EnvironmentSetup::default()).expect("production environment");
    for source in [
        "def f3Text : String := \"IO.println sorryAx tryFinally\"",
        "theorem f3Pure : True := True.intro",
    ] {
        register_source(&mut env, source).expect("pure source");
        assert!(
            non_foundational(&env).is_empty(),
            "text is not a kernel dependency"
        );
    }
    for source in [
        "def f3Wrong : IO Unit := IO.println (0 : Nat)",
        "def f3Unknown : IO Unit := IO.forged \"F3\"",
        "theorem f3False : False := Nat.zero",
    ] {
        let error = register_source(&mut env, source).expect_err("invalid source must fail");
        eprintln!("F3 source negative control: {error}");
        assert!(
            non_foundational(&env).is_empty(),
            "failed source must not install stubs"
        );
    }
    register_source(&mut env, "def f3IO : IO Unit := IO.println \"F3\"")
        .expect("ordinary IO source retains its bootstrap vocabulary");
    assert_eq!(non_foundational(&env).len(), 14);
    assert!(env.get_const(&Name::from_string("sorryAx")).is_none());
    assert!(env.get_const(&Name::from_string("tryFinally")).is_none());
    let info = env
        .get_const(&Name::from_string("f3IO"))
        .expect("registered IO");
    let ty = info.type_.clone();
    let kernel = clean_kernel::ReferenceKernel::new(env).expect("reference entry");
    let result = kernel.check_closed_term(&ty, &Expr::const_(Name::from_string("f3IO"), vec![]));
    assert!(
        matches!(
            result,
            Err(clean_kernel::ReferenceRefusal::OutsideAx0 { .. })
        ),
        "IO runtime support is never an Ax0 proof: {result:?}"
    );
}

#[test]
fn test_self_proof_f3_failed_registration_does_not_leave_fragments() {
    let _lock = module_elaboration_lock();
    let mut env = module_environment(EnvironmentSetup::default()).expect("production environment");
    // Mutate a valid emitted term so registration itself sees a real IO
    // reference but must reject a mismatched declared type transactionally.
    let source = "def f3IO : IO Unit := IO.println \"F3\"";
    let surface = clean_parser::parse_decl_exact(source).expect("parse source");
    let advice = env.bootstrap_stub_advice().expect("advice");
    let mut result = crate::elaborate_decl(&advice, &surface).expect("elaborate source");
    if let crate::ElabResult::Definition { ty, .. } = &mut result {
        *ty = Expr::const_(Name::from_string("False"), vec![]);
    } else {
        panic!("expected definition");
    }
    let error =
        crate::register::register_elab_result(&mut env, &result).expect_err("kernel type mismatch");
    eprintln!("F3 malformed registration refused: {error}");
    assert!(non_foundational(&env).is_empty());
    assert!(env.get_const(&Name::from_string("f3IO")).is_none());
}

#[test]
fn test_self_proof_f3_read_only_source_apis_preserve_vocabulary() {
    let _lock = module_elaboration_lock();
    let env = module_environment(EnvironmentSetup::default()).expect("production environment");
    let source = "def f3ReadOnly : IO Unit := IO.println \"F3\"";
    let decl = clean_parser::parse_decl_exact(source).expect("parse IO declaration");
    crate::elaborate_decl(&env, &decl).expect("read-only declaration source API");
    let (captured, _) = crate::elaborate_decl_capturing_holes(&env, &decl);
    captured.expect("IDE source API");
    let expr = clean_parser::parse_expr("IO.println").expect("parse IO expression");
    let value = crate::elaborate(&env, &expr).expect("read-only expression source API");
    let mut refs = std::collections::HashSet::new();
    value.used_constants_dag(clean_kernel::expr::UsedConstants::ConstantsOnly, &mut refs);
    assert!(refs.contains(&Name::from_string("IO.println")));
    let bad = clean_parser::parse_decl_exact("def f3ReadOnlyBad : IO Unit := IO.println (0 : Nat)")
        .expect("parse wrong IO argument");
    let error =
        crate::elaborate_decl(&env, &bad).expect_err("read-only source still rejects wrong types");
    assert!(error.to_string().contains("Type mismatch"), "{error}");
    assert!(
        non_foundational(&env).is_empty(),
        "read-only advice never extends the checked context"
    );
}

fn diagnosed(result: crate::ElabResult) -> crate::ElabResult {
    crate::ElabResult::Diagnosed {
        result: Box::new(result),
        diagnostics: Vec::new(),
    }
}

#[test]
fn test_self_proof_f3_diagnosed_composite_requests_stubs() {
    let _lock = module_elaboration_lock();
    let mut env = module_environment(EnvironmentSetup::default()).expect("production environment");
    let decl = clean_parser::parse_decl_exact("def f3DiagnosedIO : IO Unit := IO.println \"F3\"")
        .expect("parse IO declaration");
    let result = crate::elaborate_decl(&env, &decl).expect("untrusted source advice");
    let result = diagnosed(crate::ElabResult::Multiple(vec![diagnosed(result)]));
    crate::register::register_elab_result(&mut env, &result)
        .expect("diagnosed composite must request IO stubs before checking");
    assert!(env.get_const(&Name::from_string("f3DiagnosedIO")).is_some());
    assert_eq!(non_foundational(&env).len(), 14);
    assert!(env.get_const(&Name::from_string("sorryAx")).is_none());
}

#[test]
fn test_self_proof_f3_diagnosed_composite_rolls_back_prefix() {
    let _lock = module_elaboration_lock();
    let mut env = module_environment(EnvironmentSetup::default()).expect("production environment");
    let before = env.constants().count();
    let first = clean_parser::parse_decl_exact("def f3DiagnosedPrefix : Nat := 0")
        .expect("parse valid prefix");
    let first = crate::elaborate_decl(&env, &first).expect("elaborate valid prefix");
    let bad = clean_parser::parse_decl_exact("def f3DiagnosedBad : Nat := 1")
        .expect("parse declaration to mutate");
    let mut bad = crate::elaborate_decl(&env, &bad).expect("elaborate valid declaration");
    if let crate::ElabResult::Definition { ty, .. } = &mut bad {
        *ty = Expr::const_(Name::from_string("False"), Vec::new());
    } else {
        panic!("expected definition");
    }
    let result = diagnosed(crate::ElabResult::Multiple(vec![first, diagnosed(bad)]));
    let error = crate::register::register_elab_result(&mut env, &result)
        .expect_err("late kernel type mismatch");
    assert!(
        error.to_string().to_lowercase().contains("mismatch"),
        "{error}"
    );
    assert!(
        env.get_const(&Name::from_string("f3DiagnosedPrefix"))
            .is_none(),
        "diagnosed composite leaked a registered prefix"
    );
    assert!(env
        .get_const(&Name::from_string("f3DiagnosedBad"))
        .is_none());
    assert_eq!(env.constants().count(), before);
    assert!(non_foundational(&env).is_empty());
}
