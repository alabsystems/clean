// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attack battery for the dependency-closed re-check.
//!
//! Every test here builds an environment the way the `.olean` import lane does
//! — inductive families through the kernel, ordinary constants through the
//! STRUCTURAL tier (`extend_constants_structural`: no free vars / no
//! metavariables / level scope, and nothing else) — and then asks three
//! questions of the same environment:
//!
//! 1. what does the local assumed-environment check
//!    ([`crate::verify_batch_full::typecheck_constants_full`]) say?
//! 2. what does the strict per-declaration check
//!    ([`clean_kernel::env::Environment::check_decl_readonly_strict`], the
//!    per-node work of `audit_certification`) say?
//! 3. what does [`super::recheck_closed`] say?
//!
//! The battery is only interesting where those answers differ.

use super::{recheck_closed, ClosedRecheckOptions, ClosedRecheckRefusal, RecheckLevel};
use crate::verify_batch_full::typecheck_constants_full;
use clean_kernel::env::{
    ConstantInfo, ConstantKind, Declaration, Environment, Reducibility, TrustedEnvExt,
};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType, RecursorArgOrder};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use std::collections::BTreeSet;

const HEARTBEATS: u32 = 2_000_000;

fn n(s: &str) -> Name {
    Name::interned(s)
}

fn konst(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// `Type` (`Sort 1`).
fn type0() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// `Prop` (`Sort 0`).
fn prop() -> Expr {
    Expr::sort(Level::zero())
}

fn targets(names: &[&str]) -> BTreeSet<Name> {
    names.iter().map(|s| n(s)).collect()
}

/// The local check's display-string target set (its own API).
fn display_targets(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|s| (*s).to_owned()).collect()
}

/// Register a constant through the same STRUCTURAL tier the `.olean` import
/// uses, so nothing about it is kernel-checked on the way in.
fn import_structurally(env: &mut Environment, info: ConstantInfo) {
    let rejected = env.extend_constants_structural(std::iter::once(info));
    assert!(
        rejected.is_empty(),
        "structural tier rejected the fixture: {rejected:?}"
    );
}

fn definition(name: &str, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo {
        name: n(name),
        level_params: vec![],
        type_,
        value: Some(value),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    }
}

/// `RC.N : Type` with `RC.N.z` and `RC.N.s`, plus `RC.B : Type` with `RC.B.t`.
fn base_families(env: &mut Environment) {
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("RC.N"),
            type_: type0(),
            constructors: vec![
                Constructor {
                    name: n("RC.N.z"),
                    type_: konst("RC.N"),
                },
                Constructor {
                    name: n("RC.N.s"),
                    type_: Expr::pi(BinderInfo::Default, konst("RC.N"), konst("RC.N")),
                },
            ],
        }],
    })
    .expect("RC.N must be admissible");
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("RC.B"),
            type_: type0(),
            constructors: vec![Constructor {
                name: n("RC.B.t"),
                type_: konst("RC.B"),
            }],
        }],
    })
    .expect("RC.B must be admissible");
}

/// A four-deep definition chain ending in `RC.top`, optionally with the value
/// of `RC.g{depth}` replaced by a term of the WRONG type.
///
/// Each `RC.gk` is only ever REFERENCED by its successor, and a reference uses
/// the declared type — so corrupting a value anywhere in the chain leaves every
/// other declaration locally consistent.
fn chain_env(corrupt_depth: Option<usize>) -> Environment {
    let mut env = Environment::default();
    base_families(&mut env);
    for depth in 0..4usize {
        let value = if corrupt_depth == Some(depth) {
            // Type-correct as a term, but of type `RC.B`, not `RC.N`.
            konst("RC.B.t")
        } else if depth == 0 {
            konst("RC.N.z")
        } else {
            Expr::app(konst("RC.N.s"), konst(&format!("RC.g{}", depth - 1)))
        };
        import_structurally(
            &mut env,
            definition(&format!("RC.g{depth}"), konst("RC.N"), value),
        );
    }
    import_structurally(
        &mut env,
        definition(
            "RC.top",
            konst("RC.N"),
            Expr::app(konst("RC.N.s"), konst("RC.g3")),
        ),
    );
    env
}

#[test]
fn closed_replay_accepts_the_uncorrupted_chain() {
    let env = chain_env(None);
    let run = recheck_closed(
        &env,
        &targets(&["RC.top"]),
        &ClosedRecheckOptions {
            max_heartbeats: HEARTBEATS,
            ..ClosedRecheckOptions::default()
        },
    );
    assert!(
        run.report.passed(),
        "control corpus must replay cleanly, got {:?}",
        run.report.refusals
    );
    // The whole chain really was re-admitted, not skipped.
    for name in ["RC.g0", "RC.g1", "RC.g2", "RC.g3", "RC.top"] {
        assert!(
            run.replayed.get_const(&n(name)).is_some(),
            "{name} must be present in the replay environment"
        );
    }
    // Only `RC.N` is reachable from `RC.top`; `RC.B` is not in the cone, and a
    // closed re-check must replay the cone, not the environment.
    assert_eq!(run.report.families_replayed, 1);
    assert!(run.report.constants_admitted >= 5);
}

#[test]
fn corruption_at_every_depth_passes_the_local_check_and_is_caught_by_the_closed_replay() {
    for depth in 0..4usize {
        let env = chain_env(Some(depth));
        let corrupted = format!("RC.g{depth}");

        // (1) The local assumed-environment check, asked about the TARGET, is
        //     silent: `RC.top`'s own type and value are consistent, because the
        //     reference to `RC.g3` is believed at its declared type.
        let (pass, fail, errors) =
            typecheck_constants_full(&env, &display_targets(&["RC.top"]), HEARTBEATS);
        assert_eq!(
            (pass, fail),
            (1, 0),
            "depth {depth}: the local check must PASS the target (that is the defect), \
             errors={errors:?}"
        );

        // (2) The strict per-declaration check, asked about the TARGET, is also
        //     silent for the same reason.
        let top = env.get_const(&n("RC.top")).expect("target present");
        let top_decl = Declaration::Definition {
            name: top.name.clone(),
            level_params: top.level_params.clone(),
            type_: top.type_.clone(),
            value: top.value.clone().expect("target has a value"),
            is_reducible: top.is_reducible,
        };
        assert!(
            env.check_decl_readonly_strict(&top_decl).is_ok(),
            "depth {depth}: the strict per-declaration check must PASS the target"
        );

        // (3) The closed replay refuses: the corrupted constant fails its own
        //     `add_decl`, and everything above it in the chain is refused
        //     because a dependency was refused.
        let run = recheck_closed(
            &env,
            &targets(&["RC.top"]),
            &ClosedRecheckOptions {
                max_heartbeats: HEARTBEATS,
                ..ClosedRecheckOptions::default()
            },
        );
        assert!(
            !run.report.passed(),
            "depth {depth}: the closed replay must refuse the corrupted cone"
        );
        assert!(
            run.report.refusals.iter().any(|r| matches!(
                r,
                ClosedRecheckRefusal::DeclarationRefused { name, .. } if name == &corrupted
            )),
            "depth {depth}: expected a DeclarationRefused for {corrupted}, got {:?}",
            run.report.refusals
        );
        assert!(
            run.replayed.get_const(&n("RC.top")).is_none(),
            "depth {depth}: nothing downstream of a refusal may enter the replay environment"
        );
        for above in (depth + 1)..4 {
            let name = format!("RC.g{above}");
            assert!(
                run.replayed.get_const(&n(&name)).is_none(),
                "depth {depth}: {name} depends on the refused constant and must not be admitted"
            );
        }
    }
}

#[test]
fn a_constant_missing_from_the_environment_is_refused_not_ignored() {
    let mut env = Environment::default();
    base_families(&mut env);
    // `RC.dangling` names a constant nothing ever registered — exactly the
    // shape an import skip leaves behind.
    import_structurally(
        &mut env,
        definition(
            "RC.uses_missing",
            konst("RC.N"),
            Expr::app(konst("RC.N.s"), konst("RC.absent")),
        ),
    );
    let run = recheck_closed(
        &env,
        &targets(&["RC.uses_missing"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(!run.report.passed());
    assert!(
        run.report.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::AbsentFromEnvironment { name } if name == "RC.absent"
        )),
        "expected an AbsentFromEnvironment refusal, got {:?}",
        run.report.refusals
    );
    assert!(run.replayed.get_const(&n("RC.uses_missing")).is_none());
}

/// Replace the body under an expression's leading lambda prefix, keeping the
/// binders exactly as they were. Used to tamper with an ι-rule right-hand side
/// without having to know the recursor rule's binder convention.
fn replace_lambda_body(expr: &Expr, body: Expr) -> Expr {
    match expr.kind() {
        ExprKind::Lam(bd, ty, inner) => {
            Expr::lam(*bd, ty.as_ref().clone(), replace_lambda_body(inner, body))
        }
        _ => body,
    }
}

/// Build `RC.N.rec.{1} motive minor_z minor_s major`, honouring the recursor's
/// own argument order.
fn rec_app(env: &Environment, motive: Expr, minor_z: Expr, minor_s: Expr, major: Expr) -> Expr {
    let rec = env.get_recursor(&n("RC.N.rec")).expect("RC.N.rec exists");
    let levels: Vec<Level> = rec
        .level_params
        .iter()
        .map(|_| Level::succ(Level::zero()))
        .collect();
    let mut term = Expr::const_(rec.name.clone(), levels);
    term = Expr::app(term, motive);
    match rec.arg_order {
        RecursorArgOrder::MajorAfterMinors => {
            term = Expr::app(term, minor_z);
            term = Expr::app(term, minor_s);
            term = Expr::app(term, major);
        }
        RecursorArgOrder::MajorAfterMotive => {
            term = Expr::app(term, major);
            term = Expr::app(term, minor_z);
            term = Expr::app(term, minor_s);
        }
    }
    term
}

/// An environment where `RC.N.rec`'s ι-rule for `RC.N.z` has been replaced with
/// one that returns `RC.True` no matter what the minor premises are, and a
/// constant `RC.item` that type-checks ONLY under that tampered rule.
///
/// `RC.item`'s declared type reduces to `RC.False` under the real rule, so
/// `RC.item` is a proof of a false proposition.
fn tampered_rule_env(tamper: bool) -> Environment {
    tampered_rule_env_or_refusal(tamper).unwrap_or_else(|rejected| {
        panic!("the structural tier refused the fixture's recursors: {rejected:?}")
    })
}

/// [`tampered_rule_env`], or what the STRUCTURAL tier refused.
fn tampered_rule_env_or_refusal(
    tamper: bool,
) -> Result<Environment, Vec<(Name, clean_kernel::env::EnvError)>> {
    // (1) A kernel-built source environment, so the ι-rules start out correct.
    let mut source = Environment::default();
    base_families(&mut source);
    source
        .add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: n("RC.True"),
                type_: prop(),
                constructors: vec![Constructor {
                    name: n("RC.True.intro"),
                    type_: konst("RC.True"),
                }],
            }],
        })
        .expect("RC.True must be admissible");
    source
        .add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: n("RC.False"),
                type_: prop(),
                constructors: vec![],
            }],
        })
        .expect("RC.False must be admissible");

    // (2) An "imported" environment built the way the `.olean` lane builds one:
    //     every inductive, constructor and recursor enters through the
    //     STRUCTURAL tier, which validates a rule's right-hand side for free
    //     variables, metavariables and level scope — and nothing about what the
    //     rule computes.
    let mut env = Environment::default();
    let inductives: Vec<_> = source.inductives().cloned().collect();
    let constructors: Vec<_> = source.constructors().cloned().collect();
    let recursors: Vec<_> = source
        .recursors()
        .cloned()
        .map(|mut rec| {
            if tamper && rec.name == n("RC.N.rec") {
                let zero = n("RC.N.z");
                let rule = rec
                    .rules
                    .iter_mut()
                    .find(|r| r.constructor_name == zero)
                    .expect("RC.N.rec has a rule for RC.N.z");
                rule.rhs = replace_lambda_body(&rule.rhs, konst("RC.True"));
            }
            rec
        })
        .collect();
    assert!(env
        .extend_inductives_structural(inductives.into_iter())
        .is_empty());
    assert!(env
        .extend_constructors_structural(constructors.into_iter())
        .is_empty());
    let rejected = env.extend_recursors_structural(recursors.into_iter());
    if !rejected.is_empty() {
        return Err(rejected);
    }

    // (3) The claim, imported the same way.
    let motive = Expr::lam(BinderInfo::Default, konst("RC.N"), prop());
    let minor_s = Expr::lam(
        BinderInfo::Default,
        konst("RC.N"),
        Expr::lam(BinderInfo::Default, prop(), konst("RC.True")),
    );
    let claim = rec_app(&env, motive, konst("RC.False"), minor_s, konst("RC.N.z"));
    import_structurally(
        &mut env,
        ConstantInfo {
            name: n("RC.item"),
            level_params: vec![],
            type_: claim,
            value: Some(konst("RC.True.intro")),
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Theorem,
        },
    );
    Ok(env)
}

#[test]
fn control_the_untampered_rule_refuses_the_same_claim_everywhere() {
    let env = tampered_rule_env(false);
    // Without the tamper the claim reduces to `RC.False`, so even the weakest
    // level refuses it. This is what makes the tampered run below a finding
    // rather than an artefact of a badly built fixture.
    let (pass, fail, _errors) =
        typecheck_constants_full(&env, &display_targets(&["RC.item"]), HEARTBEATS);
    assert_eq!(
        (pass, fail),
        (0, 1),
        "the claim is FALSE under the real ι-rule and must be refused"
    );
    let run = recheck_closed(
        &env,
        &targets(&["RC.item"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(!run.report.passed());
}

#[test]
fn a_tampered_iota_rule_is_refused_by_the_structural_tier() {
    // Since clean main's recursor regeneration (the kernel regenerates each
    // imported recursor from its resident family), the STRUCTURAL tier itself
    // compares an imported ι-rule with the generated one and refuses the
    // tamper, naming it, so no weaker level (the local assumed-environment
    // check, the strict per-declaration check) can be handed a tampered rule
    // any more. The closed replay's own regeneration runs on the honest
    // environment in `control_the_untampered_rule_refuses_the_same_claim_everywhere`.
    let rejected = match tampered_rule_env_or_refusal(true) {
        Err(rejected) => rejected,
        Ok(_) => panic!("the structural tier must refuse the tampered ι-rule"),
    };
    assert!(
        rejected
            .iter()
            .any(|(name, error)| *name == n("RC.N.rec") && format!("{error:?}").contains("RC.N.z")),
        "the structural tier must name the tampered rule: {rejected:?}"
    );
}

#[test]
fn an_unsafe_declaration_in_the_cone_is_refused() {
    let mut env = Environment::default();
    base_families(&mut env);
    import_structurally(
        &mut env,
        definition("RC.shaky", konst("RC.N"), konst("RC.N.z")),
    );
    env.mark_unsafe(n("RC.shaky"));
    import_structurally(
        &mut env,
        definition(
            "RC.uses_shaky",
            konst("RC.N"),
            Expr::app(konst("RC.N.s"), konst("RC.shaky")),
        ),
    );
    let run = recheck_closed(
        &env,
        &targets(&["RC.uses_shaky"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(!run.report.passed());
    assert!(
        run.report.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::OutsideTrustedFragment { name, marker }
                if name == "RC.shaky" && *marker == "unsafe"
        )),
        "expected an OutsideTrustedFragment refusal, got {:?}",
        run.report.refusals
    );
}

#[test]
fn levels_state_what_they_prove_and_only_the_closed_replay_may_ground_certified() {
    assert!(!RecheckLevel::LocalAssumedEnv.may_ground_certified_class());
    assert!(!RecheckLevel::ClosureAssumedEnv.may_ground_certified_class());
    assert!(RecheckLevel::ClosedReplay.may_ground_certified_class());
    // The imported-cone gate trusts the consumer's base, and says so.
    assert!(!RecheckLevel::ImportedOverBase.may_ground_certified_class());
    assert!(RecheckLevel::ImportedOverBase
        .does_not_prove()
        .contains("consumer's own base"));

    // The weaker levels must SAY what they do not prove, in their own text.
    assert!(RecheckLevel::LocalAssumedEnv
        .does_not_prove()
        .contains("dependency cone"));
    assert!(RecheckLevel::ClosureAssumedEnv
        .does_not_prove()
        .contains("ι-rule"));
    // No level may call itself "full".
    for level in [
        RecheckLevel::LocalAssumedEnv,
        RecheckLevel::ClosureAssumedEnv,
        RecheckLevel::ClosedReplay,
        RecheckLevel::ImportedOverBase,
    ] {
        assert!(
            !level.token().contains("full"),
            "{} must not be spelled with `full`",
            level.token()
        );
        assert!(!level.proves().is_empty());
        assert!(!level.does_not_prove().is_empty());
    }
}

#[test]
fn a_passing_report_quotes_its_own_scope() {
    let env = chain_env(None);
    let run = recheck_closed(
        &env,
        &targets(&["RC.top"]),
        &ClosedRecheckOptions::default(),
    );
    let sentence = run.report.verdict_sentence();
    assert!(sentence.contains("dependency-closed-replay"));
    assert!(sentence.contains("PASS"));
    // A pass sentence must carry the level's own limitation clause.
    assert!(sentence.contains("does not authenticate the bytes it replayed"));
}

// ─────────────────────────────────────────────────────────────────────────────
// A NAME IS NOT ITS DISPLAY STRING (2026-09-24).
//
// The whole-closure replay of the Lean 4.8.0 + TSL closure refused four TRUE
// constants as `AbsentFromEnvironment`: `Lean.termMacro.trace[_]_`,
// `Lean.Parser.Tactic.Conv.conv·._` and their two `_aux_…_macroRules_…`
// companions. Each has a component that itself contains `.`
// (`termMacro.trace[_]_`, `conv·._`). `recheck_closed` took display strings and
// re-parsed them with `Name::interned`, which splits on every `.`, so it went
// looking for a different, nonexistent name. The same re-parse keyed the
// absent-cascade map, so a dependent of such a name was not reported as blocked
// by it.
// ─────────────────────────────────────────────────────────────────────────────

/// `RC.«macro.node[_]_»` — two components, the second containing a dot.
fn dotted_name() -> Name {
    Name::anon().str("RC").str("macro.node[_]_")
}

fn definition_named(name: Name, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo {
        name,
        level_params: vec![],
        type_,
        value: Some(value),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    }
}

#[test]
fn a_dotted_component_does_not_survive_the_display_string_round_trip() {
    // The premise of the defect, pinned: rendering then re-interning yields a
    // DIFFERENT name. If this ever stops holding, the tests below lose their
    // teeth and must be revisited, not deleted.
    let dotted = dotted_name();
    assert_eq!(dotted.to_string(), "RC.macro.node[_]_");
    assert_ne!(Name::interned(&dotted.to_string()), dotted);
}

#[test]
fn a_constant_whose_name_component_contains_a_dot_is_replayed_not_absent() {
    let dotted = dotted_name();
    let mut env = Environment::default();
    base_families(&mut env);
    import_structurally(
        &mut env,
        definition_named(dotted.clone(), konst("RC.N"), konst("RC.N.z")),
    );
    import_structurally(
        &mut env,
        definition(
            "RC.uses_dotted",
            konst("RC.N"),
            Expr::app(konst("RC.N.s"), Expr::const_(dotted.clone(), vec![])),
        ),
    );

    let asked: BTreeSet<Name> = [dotted.clone(), n("RC.uses_dotted")].into_iter().collect();
    let run = recheck_closed(&env, &asked, &ClosedRecheckOptions::default());
    assert!(
        run.report.passed(),
        "a true constant with a dotted component must replay: {:?}",
        run.report.refusals
    );
    assert!(run.replayed.get_const(&dotted).is_some());
    assert!(run.replayed.get_const(&n("RC.uses_dotted")).is_some());

    // The pre-fix path, reproduced exactly: the caller's display string,
    // re-interned, names nothing in the environment and is refused as absent.
    let reparsed: BTreeSet<Name> = [Name::interned(&dotted.to_string())].into_iter().collect();
    let old = recheck_closed(&env, &reparsed, &ClosedRecheckOptions::default());
    assert!(
        old.report.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::AbsentFromEnvironment { name } if name == "RC.macro.node[_]_"
        )),
        "the display-string round trip must reproduce the refusal: {:?}",
        old.report.refusals
    );
}

#[test]
fn a_dependent_of_an_absent_dotted_name_is_blocked_by_it_not_sent_to_add_decl() {
    let dotted = dotted_name();
    let mut env = Environment::default();
    base_families(&mut env);
    // `dotted` is never registered: the shape an import skip leaves behind.
    import_structurally(
        &mut env,
        definition(
            "RC.uses_missing_dotted",
            konst("RC.N"),
            Expr::app(konst("RC.N.s"), Expr::const_(dotted.clone(), vec![])),
        ),
    );
    let run = recheck_closed(
        &env,
        &targets(&["RC.uses_missing_dotted"]),
        &ClosedRecheckOptions::default(),
    );
    assert!(!run.report.passed());
    assert!(
        run.report.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::DependencyRefused { name, blocked_by }
                if name == "RC.uses_missing_dotted" && blocked_by == "RC.macro.node[_]_"
        )),
        "the dependent must be reported as blocked by the absent name: {:?}",
        run.report.refusals
    );
    assert!(
        !run.report.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::DeclarationRefused { name, .. } if name == "RC.uses_missing_dotted"
        )),
        "a dependent of an absent name must never reach add_decl: {:?}",
        run.report.refusals
    );
    assert!(run
        .replayed
        .get_const(&n("RC.uses_missing_dotted"))
        .is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// THE WEAKER LEVEL MAY NOT BE DESCRIBED AS A STRONGER ONE (2026-09-24).
//
// The round-22 verifier found four user-facing strings describing
// `typecheck_constants_full` (local-assumed-env) as `add_decl`-equivalent or as
// a kernel re-verify: the `olean import-reverify-metric` help summary and text,
// the `--full-validation` help, and the Init snapshot log line — whose wording
// is also SEALED into the snapshot's attestation receipt.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn no_source_in_this_crate_calls_the_local_check_add_decl_equivalent() {
    // Assembled at run time so this file does not match its own needles.
    let needles = [
        ["add_decl", "-equivalent"].concat(),
        ["full `add_decl`", " validation"].concat(),
        ["the kernel ", "re-verifies"].concat(),
        ["full re-", "verify (add_decl"].concat(),
    ];
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    // This crate's sources, plus the kernel file that documents the snapshot
    // attestation this crate seals (other kernel files use "re-verify" of a
    // real `add_decl`, which is not this claim).
    let mut stack = vec![root.join("src"), root.join("examples")];
    let mut hits = Vec::new();
    let snapshot = root.join("../clean-kernel/src/env/snapshot.rs");
    let text = std::fs::read_to_string(&snapshot).expect("kernel snapshot.rs must exist");
    for needle in &needles {
        if text.contains(needle.as_str()) {
            hits.push(format!("{}: {needle}", snapshot.display()));
        }
    }
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let text = std::fs::read_to_string(&path).unwrap_or_default();
                for needle in &needles {
                    if text.contains(needle.as_str()) {
                        hits.push(format!("{}: {needle}", path.display()));
                    }
                }
            }
        }
    }
    assert!(
        hits.is_empty(),
        "the local check is described as a stronger level: {hits:#?}"
    );
}
