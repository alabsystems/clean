// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! KR2 prerequisite: compile the partial CIC_L theory with pinned
//! Lean and re-admit its entire dependency cone through the reference entry.
//! These are structural typing and schema results, not checker or binary soundness.
//!
//! What a pass is evidence of is fixed by `cic_l_level/evidence.rs` (plan unit
//! E2): the targets are the declarations of the theory's own modules, private
//! ones included; the modules are `ORDER`'s; every theorem's statement is
//! pinned; and the axiom closure is the observed one.

#[path = "cic_l_level/evidence.rs"]
mod evidence;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{
    Expr, ExprKind, KernelEnvError, KernelTypeError, Level, Name, ReferenceKernel,
    ReferenceRefusal, TypeChecker,
};

const THEORY_ROOT: &str = "CICL.ListSupportCases";

#[path = "cic_l_level/negative_controls.rs"]
mod negative_controls;

#[path = "cic_l_level/tables.rs"]
mod tables;
use tables::{CORE_WITNESSES, THEOREMS};

#[path = "cic_l_level/control_cases.rs"]
mod control_cases;
use control_cases::{COMPUTATIONAL_CONTROLS, FORGED_ROWS, LEAN_CONTROL_PROGRAM};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// A level of [`COMPUTATIONAL_CONTROLS`] as a kernel term.
fn level_term(words: &str) -> Expr {
    let words: Vec<&str> = words.split(' ').collect();
    let (atom, successors) = words.split_last().expect("a level has an atom");
    let atom = match *atom {
        "p" => "CICL.LevelDecideCases.p",
        "q" => "CICL.LevelDecideCases.q",
        "zero" => "CICL.Level.zero",
        other => panic!("unknown level atom {other:?}"),
    };
    successors
        .iter()
        .rev()
        .fold(Expr::const_(name(atom), vec![]), |inner, word| {
            assert_eq!(*word, "succ", "only `succ` may precede the atom");
            Expr::app(Expr::const_(name("CICL.Level.succ"), vec![]), inner)
        })
}

/// One application of a soundness theorem in [`COMPUTATIONAL_CONTROLS`].
struct Control {
    sound: &'static str,
    relation: &'static str,
    /// `positive` at the accepted pair, `forged` at the rejected one.
    kind: &'static str,
    u: &'static str,
    v: &'static str,
}

/// Each computational control in table order, positive before forged.
fn computational_controls() -> Vec<Control> {
    COMPUTATIONAL_CONTROLS
        .iter()
        .flat_map(|&(sound, relation, [pu, pv], [ru, rv])| {
            [("positive", pu, pv), ("forged", ru, rv)].map(|(kind, u, v)| Control {
                sound,
                relation,
                kind,
                u,
                v,
            })
        })
        .collect()
}

/// The verdict line [`LEAN_CONTROL_PROGRAM`] must print for a control.
fn expected_lean_verdict(sound: &str, kind: &str) -> String {
    let verdict = if kind == "positive" {
        "accepted"
    } else {
        "refused, application type mismatch"
    };
    format!("C1 pinned Lean kernel {sound} {kind}: {verdict}")
}

/// Run [`LEAN_CONTROL_PROGRAM`] with pinned Lean over the compiled theory and
/// return its standard output, one verdict line per control.
fn pinned_lean_control_output() -> String {
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let lib = clean_olean::require_pinned_lean_lib_path()
        .expect("install the repository-pinned Lean toolchain");
    let compiled = clean_olean::test_support::compiled_fixture_dir("cic_l_level");
    let program = Path::new(env!("CARGO_MANIFEST_DIR")).join(LEAN_CONTROL_PROGRAM);
    let output = Command::new(&lean)
        .arg("--run")
        .arg(&program)
        .args(
            computational_controls()
                .iter()
                .map(|c| format!("{}|{}|{}|{}|{}", c.sound, c.relation, c.kind, c.u, c.v)),
        )
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .output()
        .expect("run pinned Lean on the computational controls");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        output.status.success(),
        "pinned Lean could not run {}: {}\n{stdout}\n{}",
        program.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

/// What the forged-statement rows miss.
#[derive(Debug, Default, PartialEq, Eq)]
struct ForgedRowGaps {
    /// A `wrong*` proposition the theory declares that no row offers.
    unforged: Vec<String>,
    /// A row whose proposition is no `wrong*` proposition of the theory.
    stray: Vec<String>,
}

/// The theory's `wrong*` propositions, read from what each module declares:
/// every definition whose type is `Prop` and whose last name component starts
/// with `wrong`. A `wrong*` definition of another type (the private terms the
/// binder cases build a proposition from) is no proposition to forge.
fn wrong_propositions(
    loaded: &Environment,
    modules: &BTreeMap<String, Vec<Name>>,
) -> BTreeSet<String> {
    modules
        .values()
        .flatten()
        .filter(|n| {
            n.last_component()
                .is_some_and(|last| last.starts_with("wrong"))
        })
        .filter(|n| {
            loaded.get_const(n).is_some_and(|c| {
                c.kind == clean_kernel::ConstantKind::Definition && c.type_.is_prop()
            })
        })
        .map(ToString::to_string)
        .collect()
}

/// Compare the declared `wrong*` propositions with the propositions `rows`
/// offer as forged statements.
fn forged_row_gaps(wrong: &BTreeSet<String>, rows: &[(&str, &str, &str)]) -> ForgedRowGaps {
    let forged: BTreeSet<String> = rows
        .iter()
        .map(|(module, _, proposition)| format!("CICL.{module}.{proposition}"))
        .collect();
    ForgedRowGaps {
        unforged: wrong.difference(&forged).cloned().collect(),
        stray: forged.difference(wrong).cloned().collect(),
    }
}

/// The rule witnesses and the forged-statement controls over the hand tables
/// in this file. `evidence::level_theory_rechecks_with_false_computation_controls`
/// is the test: it compiles, loads and replays the theory, runs the E2 checks,
/// and then calls this with the kernel it built.
fn rule_witnesses_and_forged_controls(
    loaded: &Environment,
    mut kernel: ReferenceKernel,
    inventory: &BTreeMap<String, String>,
    pins: &BTreeMap<String, String>,
) {
    // C1: unlike the whole-theory convenience table, these two module rows
    // must be exhaustive. Read module-of-origin names, including private and
    // generated theorems, rather than a namespace prefix or source-text scan.
    let modules = evidence::import_closure(
        &clean_olean::test_support::compiled_fixture_dir("cic_l_level"),
        THEORY_ROOT,
    );
    for module in ["CICL.LevelDecide", "CICL.LevelDecideCases"] {
        let declared: BTreeSet<String> = modules[module]
            .iter()
            .filter(|n| {
                loaded
                    .get_const(n)
                    .is_some_and(|c| c.kind == clean_kernel::ConstantKind::Theorem)
            })
            .map(ToString::to_string)
            .collect();
        let module_names: BTreeSet<String> =
            modules[module].iter().map(ToString::to_string).collect();
        let table: BTreeSet<String> = THEOREMS
            .iter()
            .filter(|n| module_names.contains(**n))
            .map(|n| (*n).to_owned())
            .collect();
        assert_eq!(
            declared, table,
            "C1 theorem table must equal module {module}'s theorem constants"
        );
        eprintln!(
            "C1 module theorem table: {module} {} theorems, exact",
            declared.len()
        );
    }
    // C1: each `wrong*` proposition is offered as a forged statement. The set
    // is read from what every module declares, not from FORGED_ROWS, so a
    // deleted row, or a proposition added without one, refuses here. The
    // planted gaps show the comparison can refuse in both directions.
    let wrong = wrong_propositions(loaded, &modules);
    assert_eq!(
        forged_row_gaps(&wrong, FORGED_ROWS),
        ForgedRowGaps::default(),
        "each wrong* proposition needs a forged-statement row, and each row one"
    );
    let dropped = (
        "LevelDecideCases",
        "constructor_bound_variable_rejected",
        "wrongConstructorBoundAccepted",
    );
    let without: Vec<(&str, &str, &str)> = FORGED_ROWS
        .iter()
        .copied()
        .filter(|row| *row != dropped)
        .collect();
    assert_eq!(without.len() + 1, FORGED_ROWS.len(), "one row is dropped");
    assert_eq!(
        forged_row_gaps(&wrong, &without),
        ForgedRowGaps {
            unforged: vec!["CICL.LevelDecideCases.wrongConstructorBoundAccepted".to_owned()],
            stray: vec![],
        },
        "a dropped row must be named unforged"
    );
    let mut with_stray = FORGED_ROWS.to_vec();
    with_stray.push((
        "LevelDecideCases",
        "constructor_bound_order",
        "wrongNotDeclared",
    ));
    assert_eq!(
        forged_row_gaps(&wrong, &with_stray),
        ForgedRowGaps {
            unforged: vec![],
            stray: vec!["CICL.LevelDecideCases.wrongNotDeclared".to_owned()],
        },
        "a row offering an undeclared proposition must be named stray"
    );
    eprintln!(
        "C1 forged rows: {} wrong* propositions in {} modules, each offered by a row; \
         planted dropped and stray rows refused",
        wrong.len(),
        modules.len()
    );
    let env = kernel.environment();
    let actual: BTreeSet<Name> = env
        .get_inductive(&name("CICL.CoreJudgmentIn"))
        .expect("core judgment was re-admitted")
        .constructor_names
        .iter()
        .cloned()
        .collect();
    let witnessed: BTreeSet<Name> = CORE_WITNESSES
        .iter()
        .map(|(constructor, _)| name(&format!("CICL.CoreJudgmentIn.{constructor}")))
        .collect();
    assert_eq!(actual, witnessed, "each core rule needs a checked witness");
    let checker = TypeChecker::new(env);
    for (constructor, witness) in CORE_WITNESSES {
        let c = env
            .get_const(&name(&format!("CICL.CoreTypingCases.{witness}")))
            .expect("rule witness was re-admitted");
        let statement = checker.whnf(&c.type_);
        assert!(
            matches!(statement.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name("CICL.CoreJudgmentIn")),
            "{witness} must state a ground core judgment, got {statement}"
        );
        let value = checker.whnf(c.value.as_ref().expect("rule witness has a proof"));
        assert!(
            matches!(value.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(&format!("CICL.CoreJudgmentIn.{constructor}"))),
            "{witness} must apply {constructor} at its root, got {value}"
        );
    }
    for (relation, witnesses) in [
        (
            "CICL.CoreHeadStep",
            vec![
                ("beta", "CICL.HeaderTraceCases.beta_step"),
                ("zeta", "CICL.HeaderTraceCases.zeta_step"),
                ("delta", "CICL.HeaderTraceCases.delta_step"),
                (
                    "localDefinition",
                    "CICL.HeaderTraceCases.local_definition_step",
                ),
                ("metadata", "CICL.HeaderTraceCases.metadata_step"),
                ("application", "CICL.HeaderTraceCases.application_step"),
            ],
        ),
        (
            "CICL.CoreHeadReduction",
            vec![
                ("refl", "CICL.HeaderTraceCases.reflexive_reduction"),
                ("step", "CICL.HeaderTraceCases.alias_header_reduction"),
            ],
        ),
        (
            "CICL.HeaderTelescope",
            vec![
                ("sort", "CICL.HeaderTraceCases.alias_header_view"),
                ("pi", "CICL.MutualHeaderCases.indexed_header_telescope"),
            ],
        ),
        (
            "CICL.ParameterAgreement",
            vec![
                ("zero", "CICL.MutualHeaderCases.parameter_agreement_zero"),
                ("succ", "CICL.MutualHeaderCases.shared_parameter_agreement"),
            ],
        ),
        (
            "CICL.SchemaExtension",
            vec![
                ("base", "CICL.MutualHeaderCases.empty_auxiliary_extension"),
                ("insert", "CICL.MutualHeaderCases.one_header_extended"),
            ],
        ),
    ] {
        let actual: BTreeSet<Name> = env
            .get_inductive(&name(relation))
            .expect("auxiliary rules were re-admitted")
            .constructor_names
            .iter()
            .cloned()
            .collect();
        let witnessed: BTreeSet<Name> = witnesses
            .iter()
            .map(|(constructor, _)| name(&format!("{relation}.{constructor}")))
            .collect();
        assert_eq!(
            actual, witnessed,
            "each {relation} rule needs a checked witness"
        );
        for (constructor, witness) in witnesses {
            let c = env
                .get_const(&name(witness))
                .expect("rule witness was re-admitted");
            let statement = checker.whnf(&c.type_);
            assert!(
                matches!(statement.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(relation)),
                "{witness} must state a ground {relation} judgment"
            );
            let value = checker.whnf(c.value.as_ref().expect("rule witness has a proof"));
            assert!(
                matches!(value.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(&format!("{relation}.{constructor}"))),
                "{witness} must apply {constructor} at its root"
            );
        }
    }
    for (relation, witnesses) in [
        (
            "CICL.PositiveField",
            vec![
                ("free", "CICL.ConstructorChecksCases.free_field_positive"),
                ("pi", "CICL.ConstructorChecksCases.function_field_positive"),
                (
                    "family",
                    "CICL.ConstructorChecksCases.mutual_field_positive",
                ),
            ],
        ),
        (
            "CICL.ConstructorFields",
            vec![
                ("result", "CICL.ConstructorChecksCases.f_result_shape"),
                ("field", "CICL.ConstructorChecksCases.f_fields"),
            ],
        ),
        (
            "CICL.ConstructorParameters",
            vec![
                ("done", "CICL.ConstructorChecksCases.parameters_done"),
                (
                    "parameter",
                    "CICL.ConstructorChecksCases.shared_parameter_checked",
                ),
            ],
        ),
    ] {
        let actual: BTreeSet<Name> = env
            .get_inductive(&name(relation))
            .expect("constructor rules were re-admitted")
            .constructor_names
            .iter()
            .cloned()
            .collect();
        let witnessed: BTreeSet<Name> = witnesses
            .iter()
            .map(|(constructor, _)| name(&format!("{relation}.{constructor}")))
            .collect();
        assert_eq!(
            actual, witnessed,
            "each {relation} rule needs a checked witness"
        );
        for (constructor, witness) in witnesses {
            let c = env
                .get_const(&name(witness))
                .expect("constructor witness was re-admitted");
            let statement = checker.whnf(&c.type_);
            assert!(
                matches!(statement.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(relation)),
                "{witness} must state a ground {relation} judgment"
            );
            let value = checker.whnf(c.value.as_ref().expect("constructor witness has a proof"));
            assert!(
                matches!(value.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(&format!("{relation}.{constructor}"))),
                "{witness} must apply {constructor} at its root"
            );
        }
    }
    let signature_witnesses = [("empty", "empty_signature"), ("insert", "two_declarations")];
    let actual: BTreeSet<Name> = env
        .get_inductive(&name("CICL.WfSignature"))
        .expect("signature admission was re-admitted")
        .constructor_names
        .iter()
        .cloned()
        .collect();
    let witnessed: BTreeSet<Name> = signature_witnesses
        .iter()
        .map(|(constructor, _)| name(&format!("CICL.WfSignature.{constructor}")))
        .collect();
    assert_eq!(
        actual, witnessed,
        "each signature rule needs a checked witness"
    );
    for (constructor, witness) in signature_witnesses {
        let c = env
            .get_const(&name(&format!("CICL.SignatureCases.{witness}")))
            .expect("signature witness was re-admitted");
        let statement = checker.whnf(&c.type_);
        assert!(
            matches!(statement.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name("CICL.WfSignature")),
            "{witness} must state signature well-formedness"
        );
        let value = checker.whnf(c.value.as_ref().expect("signature witness has a proof"));
        assert!(
            matches!(value.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(&format!("CICL.WfSignature.{constructor}"))),
            "{witness} must apply {constructor} at its root"
        );
    }
    for (witness, constructor) in [
        ("definition_is_enacted", "refl"),
        ("definition_is_retained", "zetaLocal"),
        ("beta_result_from_body", "beta"),
        ("let_result_from_body", "zeta"),
    ] {
        let c = env
            .get_const(&name(&format!("CICL.TypedSubstitutionCases.{witness}")))
            .expect("substitution witness was re-admitted");
        let value = checker.whnf(c.value.as_ref().expect("substitution witness has a proof"));
        assert!(
            matches!(value.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(&format!("CICL.CoreJudgmentIn.{constructor}"))),
            "{witness} must exercise {constructor}"
        );
    }
    // Plan unit E6: a negative control per core rule (or the inventory's
    // reason for none) and the WfContext census, with their planted failures.
    negative_controls::run(env, &checker);
    drop(checker);

    for subject in THEOREMS {
        let closure = evidence::axiom_closure(kernel.environment(), &name(subject))
            .expect("the theorem was admitted");
        eprintln!("{subject}: reference-admitted, axiom closure {closure:?}");
    }

    // Positive re-entry and its negative share the very same proof and level
    // parameters. Only the statement changes. A malformed or missing proof
    // cannot explain a negative result because the positive must first pass.
    for (module, proof, wrong) in FORGED_ROWS {
        let source = name(&format!("CICL.{module}.{proof}"));
        let c = loaded.get_const(&source).expect("control theorem exists");
        let value = c.value.clone().expect("control has a real proof");
        // The same forgery against the statement pin: this theorem restated
        // as the wrong proposition is refused as a changed statement.
        evidence::forged_statement_refused(
            inventory,
            pins,
            &source,
            &c.level_params,
            &Expr::const_(name(&format!("CICL.{module}.{wrong}")), vec![]),
        );
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("CICL.Controls.{module}_{proof}_{wrong}_positive")),
                level_params: c.level_params.clone(),
                type_: c.type_.clone(),
                value: value.clone(),
            })
            .expect("positive re-entry must pass");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("CICL.Controls.{module}_{proof}_{wrong}_forged")),
            level_params: c.level_params.clone(),
            type_: Expr::const_(name(&format!("CICL.{module}.{wrong}")), vec![]),
            value,
        });
        assert!(
            matches!(
                &bad,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "{wrong} must fail with a type mismatch, got {bad:?}"
        );
    }

    // C1: apply the actual soundness theorem to Eq.refl true. The positive
    // uses an accepted pair; the negative changes only the levels to a rejected
    // pair. The proposition is the theorem's own conclusion in both cases. Each
    // goes to both kernels: pinned Lean's, through LEAN_CONTROL_PROGRAM, and the
    // fenced reference entry here; each must give the expected verdict.
    let lean_output = pinned_lean_control_output();
    eprint!("{lean_output}");
    let controls = computational_controls();
    let expected: Vec<String> = controls
        .iter()
        .map(|c| expected_lean_verdict(c.sound, c.kind))
        .collect();
    assert_eq!(
        lean_output.lines().collect::<Vec<_>>(),
        expected,
        "pinned Lean's kernel must accept each positive control and refuse each forged one \
         with an application type mismatch"
    );
    let bool_true = Expr::const_(name("Bool.true"), vec![]);
    let true_refl = Expr::app(
        Expr::app(
            Expr::const_(name("Eq.refl"), vec![Level::succ(Level::zero())]),
            Expr::const_(name("Bool"), vec![]),
        ),
        bool_true,
    );
    for Control {
        sound,
        relation,
        kind,
        u,
        v,
    } in controls
    {
        let (u, v) = (level_term(u), level_term(v));
        let conclusion = Expr::app(
            Expr::app(
                Expr::const_(name(&format!("CICL.Level.{relation}")), vec![]),
                u.clone(),
            ),
            v.clone(),
        );
        let value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(name(&format!("CICL.Level.{sound}")), vec![]),
                    u,
                ),
                v,
            ),
            true_refl.clone(),
        );
        let result = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("CICL.Controls.{sound}_computational_{kind}")),
            level_params: vec![],
            type_: conclusion,
            value,
        });
        if kind == "positive" {
            result.expect("soundness applied to a computed acceptance must pass");
        } else {
            assert!(
                matches!(
                    &result,
                    Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                        source: KernelTypeError::TypeMismatch { .. },
                        ..
                    }))
                ),
                "{sound} must refuse the forged computed acceptance: {result:?}"
            );
        }
        eprintln!(
            "C1 computational control {sound} {kind}: expected verdict confirmed by pinned Lean \
             and fenced Clean"
        );
    }

    // Plan unit S0: `beta` carries the argument's typing. The mutation is
    // `beta_rule`'s own proof with that premise dropped, the constructor
    // applied to the two endpoint typings only. Its inferred type still asks
    // for the argument's typing, so it is admitted at `betaRule` and refused
    // at the rule as it stood before S0: the refusal is that premise and
    // nothing else, since the statements differ in it alone.
    let beta_rule = loaded
        .get_const(&name("CICL.CoreTypingCases.beta_rule"))
        .expect("beta_rule exists");
    let mutated = drop_last_argument(beta_rule.value.as_ref().expect("beta_rule has a proof"));
    kernel
        .add_checked(Declaration::Theorem {
            name: name("CICL.Controls.beta_without_argument_positive"),
            level_params: beta_rule.level_params.clone(),
            type_: Expr::const_(name("CICL.CoreTypingCases.betaRule"), vec![]),
            value: mutated.clone(),
        })
        .expect("beta without its argument still proves the rule that asks for it");
    let bad = kernel.add_checked(Declaration::Theorem {
        name: name("CICL.Controls.beta_without_argument_forged"),
        level_params: beta_rule.level_params.clone(),
        type_: Expr::const_(
            name("CICL.CoreTypingCases.wrongBetaWithoutArgument"),
            vec![],
        ),
        value: mutated,
    });
    assert!(
        matches!(
            &bad,
            Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                source: KernelTypeError::TypeMismatch { .. },
                ..
            }))
        ),
        "beta without the argument's typing must fail with a type mismatch, got {bad:?}"
    );
}

/// `fun xs y => f xs y` to `fun xs => f xs`: drop the innermost binder of a
/// lambda chain whose body applies its head to that binder last. Panics on any
/// other shape, so a change to `beta_rule`'s proof cannot pass unexamined.
fn drop_last_argument(value: &Expr) -> Expr {
    let ExprKind::Lam(binder, domain, body) = value.kind() else {
        panic!("beta_rule's proof is not a lambda: {value}");
    };
    match body.kind() {
        ExprKind::Lam(..) => Expr::lam(*binder, (**domain).clone(), drop_last_argument(body)),
        ExprKind::App(function, argument) => {
            assert!(
                matches!(argument.kind(), ExprKind::BVar(0)),
                "beta_rule's proof does not end in its last binder: {body}"
            );
            // The head does not mention the dropped binder; instantiating it
            // lowers every outer index by one, whatever is substituted.
            let lowered = function.instantiate(&Expr::prop());
            assert_eq!(
                lowered,
                function.instantiate(&Expr::sort(Level::succ(Level::zero()))),
                "beta_rule's head mentions the argument it drops"
            );
            lowered
        }
        _ => panic!("beta_rule's proof has an unexpected body: {body}"),
    }
}

/// The pinned terms of `CICL.BaseFamilies` are pinned Lean's own (plan unit M4).
/// `cic_l_level/compare_pinned_terms.lean` translates each pinned `CICL.Expr` to a
/// `Lean.Expr`, compares it with `Expr.equal` (binder names and annotations
/// included) and each descriptor field by field, and must detect its forged
/// controls. A statement pin binds a theorem's type, not the terms it names; this
/// binds the terms.
#[test]
fn base_family_terms_equal_pinned_lean() {
    let lib = clean_olean::require_pinned_lean_lib_path()
        .expect("install the repository-pinned Lean toolchain");
    let compiled = clean_olean::test_support::compiled_fixture_dir("cic_l_level");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin directory");
    let script =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cic_l_level/compare_pinned_terms.lean");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let run = Command::new(&lean)
        .arg(&script)
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([compiled.as_path(), lib.as_path()]).expect("Lean path"),
        )
        .env("PATH", std::env::join_paths(paths).expect("binary path"))
        .output()
        .expect("run pinned Lean on the comparison");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "pinned-term comparison failed: {stdout}\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    // Each line is a message, bare or after a `<file>:<line>:<column>: info: ` prefix.
    let labels = |marker: &str| -> BTreeSet<String> {
        stdout
            .lines()
            .map(|line| {
                line.split_once("info: ")
                    .map_or(line, |(_, message)| message)
            })
            .filter_map(|message| {
                message
                    .strip_prefix(marker)
                    .map(|label| label.trim().to_owned())
            })
            .collect()
    };
    let expected = |names: &[&str]| -> BTreeSet<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    };
    assert_eq!(
        labels("MATCH "),
        expected(&[
            "Eq name",
            "Eq universe parameter count",
            "Eq type",
            "Eq descriptor",
            "Eq.refl universe parameter count",
            "Eq.refl type",
            "Eq.refl descriptor",
            "Eq.rec universe parameter count",
            "Eq.rec type",
            "Eq.rec descriptor",
            "Eq.rec rule",
            "PUnit name",
            "PUnit universe parameter count",
            "PUnit type",
            "PUnit descriptor",
            "PUnit.unit name",
            "PUnit.unit universe parameter count",
            "PUnit.unit type",
            "PUnit.unit descriptor",
            "PUnit.rec name",
            "PUnit.rec universe parameter count",
            "PUnit.rec type",
            "PUnit.rec descriptor",
            "PUnit.rec rule PUnit.unit",
            "Nat name",
            "Nat universe parameter count",
            "Nat type",
            "Nat descriptor",
            "Nat.zero name",
            "Nat.zero universe parameter count",
            "Nat.zero type",
            "Nat.zero descriptor",
            "Nat.succ name",
            "Nat.succ universe parameter count",
            "Nat.succ type",
            "Nat.succ descriptor",
            "Nat.rec name",
            "Nat.rec universe parameter count",
            "Nat.rec type",
            "Nat.rec descriptor",
            "Nat.rec rule Nat.zero",
            "Nat.rec rule Nat.succ",
        ]),
        "every pinned term and descriptor is compared: {stdout}"
    );
    assert_eq!(
        labels("CONTROL DETECTED "),
        expected(&[
            "Eq type with its first binder made explicit",
            "Eq.rec type with its universe parameters swapped",
            "PUnit.rec type with its universe parameters swapped",
            "Nat.succ descriptor with no field",
            "Nat.rec successor rule replaced by zero rule",
        ]),
        "all forged controls are detected: {stdout}"
    );
}
