// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PKG-U6: decision procedures for trust-cg's e-graph rule statements,
//! kernel-checked by Clean THROUGH the reference entry, every closure ⊆ Ax0.
//!
//! The fixture family `tests/fixtures/lean/v4.30.0-rc2/eqsat_decide/` (its
//! README) holds what a rule found by search is proved with: no lemma per
//! rule, but a procedure the kernel evaluates on the rule's literal. The
//! vocabulary (`EqsatRule`) and the proof helpers (`EqsatBasics`) are the
//! `eqsat_rules` family's (`from eqsat_rules`); this family changes neither.
//! Here:
//!
//! * the family is compiled by the pinned `lean -o`, and every kernel
//!   declaration of its modules and of the two it takes from `eqsat_rules` is
//!   admitted from EMPTY through `ReferenceKernel` (`reference_base_closed`),
//!   is neither an axiom nor opaque, and has a closure ⊆ Ax0 that reaches no
//!   native-evaluation or sorry constant;
//! * the closure digest of `EqsatRule.Sound` on that environment is the one
//!   the `eqsat_rules` gate pins (read from `eqsat_rules.rs`, so there is one
//!   pin): this family does not change what a rule statement means;
//! * the replay and every check below run under the budget of U6-BUDGET
//!   ([`BUDGET`] kernel heartbeats: the entry has one `maxHeartbeats` for
//!   both);
//! * every theorem of `EqsatResidue`, `EqsatExhaust` and
//!   `EqsatDecideControls` is required by name in the replayed environment
//!   and its statement is the pinned one (the family's `STATEMENTS` file,
//!   [`statement_digest`]). The row of `EqsatDecide.exhaust8_sound` pins what
//!   the soundness theorem states, with the closure digest of `exhaust8`, of
//!   `EqsatRule.Sound` and of every other constant its statement names;
//! * the residue evaluator is evaluated by the kernel: closed outcomes of
//!   `Pat.evalR` and `checkR` are accepted by `Eq.refl`, and beside each a
//!   forged outcome is refused: a wrong residue, `true` for a false rule at
//!   its counterexample, a value for an undefined left side, an `equiv` rule
//!   whose left side is undefined, and a right side that is not a term beside
//!   an undefined left side; and one outcome of each operator the rule
//!   grammar and SemR's enumerations have, beside the outcome a neighbouring
//!   operator, the other signedness or the unreduced result would give
//!   (`eqsat_decide/operators.rs`);
//! * the procedure proves rules by the term a discharge record carries,
//!   `EqsatDecide.exhaust8_sound <literal> <type> EqsatDecide.rflTrue`
//!   (`eqsat_decide/procedure.rs`): for sixteen rule and type pairs at `u8`,
//!   `i8` and `bool` the entry accepts it for `EqsatRule.Sound <literal>
//!   <type>` on a literal built here, and the gate prints the time of each
//!   check and the smallest heartbeat limit it passes under;
//! * the same term is refused, for the claim (a `TypeMismatch`, never a
//!   refusal for lack of budget, depth or memory), for a false rule
//!   (trust-cg's wrong rules restated), for a true 8-bit rule at each of the
//!   ten other integer types (and the `u8` term offered there), for a
//!   refines-only rule offered as `equiv`, for a rule over 1,024 assignments,
//!   for a rule whose side is not a term, for a rule whose side conditions no
//!   assignment satisfies and for a `refines` rule whose left side is
//!   undefined behaviour on every assignment; the last two are `Sound` (a
//!   proof of each is accepted beside the refusal);
//! * the counts of the three groups of controls are asserted
//!   ([`CLOSED_OUTCOME_PAIRS`], [`RULES_PROVED`], [`TERMS_REFUSED`]): a
//!   control removed is an edit of a number;
//! * the budget is in force: the enumeration of a true rule with two 8-bit
//!   variables, asked for without the size limit, is refused with
//!   `HeartbeatExceeded` at [`BUDGET`];
//! * two replays from EMPTY in one process give one environment digest.
//!
//! The environment digest is not pinned: it chains every admitted
//! declaration, so it moves with each lemma added to the family.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{Level, ReferenceKernel, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_modules_with_deps, parse_module, reference_base_closed, DefinitionSafety};

#[path = "support/lean_tripwire.rs"]
mod lean_tripwire;
use lean_tripwire::{banned_words, lean_code_only};

// The `eqsat_rules` gate's term builders and statement digest, shared so the
// two gates build one literal and hash one statement the same way. Each gate
// uses a part of them.
#[allow(dead_code)]
#[path = "eqsat_rules/terms.rs"]
mod terms;
use terms::{accepted, app, bin, boolean, c, conds, lit, n, nat, un, var};

#[path = "eqsat_decide/procedure.rs"]
mod procedure;
use procedure::refused_for_the_claim as refused;

#[path = "eqsat_decide/operators.rs"]
mod operators;

#[allow(dead_code)]
#[path = "eqsat_rules/statements.rs"]
mod statements;
use statements::{check_statement_pins, required_statements, statement_digest, statement_pins};

const PINNED: &str = "v4.30.0-rc2";
const FAMILY: &str = "eqsat_decide";

/// The modules this family takes from `eqsat_rules`, in `ORDER`.
const FROM_EQSAT_RULES: [&str; 2] = ["EqsatRule", "EqsatBasics"];

/// The family's own modules, in `ORDER`.
const MODULES: [&str; 3] = ["EqsatResidue", "EqsatExhaust", "EqsatDecideControls"];

/// The modules whose every theorem is pinned by name and statement, each with
/// the namespace its theorems are declared in (`statements.rs` reads these).
const PINNED_MODULES: [(&str, &str); 3] = [
    ("EqsatResidue", "EqsatDecide"),
    ("EqsatExhaust", "EqsatDecide"),
    ("EqsatDecideControls", "EqsatDecideControls"),
];

/// U6-BUDGET (`docs/DECISIONS.md`): the kernel heartbeats one check gets. The
/// entry has one `maxHeartbeats` for the replay of the family and for each
/// closed-term check, so the replay runs under it too.
const BUDGET: u32 = 200_000;

/// The closed outcomes of the residue evaluator the gate has the entry accept,
/// each beside a forged outcome it refuses: 16 of `kernel_controls` and the
/// table of `operators.rs`.
const CLOSED_OUTCOME_PAIRS: usize = 16 + operators::CASES;

/// The rule and type pairs the record term proves under the budget.
const RULES_PROVED: usize = 16;

/// The terms the procedure controls have the entry refuse for the claim.
const TERMS_REFUSED: usize = 72;

/// `statements.rs` also requires the `eqsat_rules` satisfiability lemmas;
/// this family has none.
const SAT_LEMMAS: [&str; 0] = [];

/// The pinned statements: one `name digest` row per theorem of
/// [`PINNED_MODULES`] (the family's README, "Compiling").
const STATEMENTS: &str = include_str!("fixtures/lean/v4.30.0-rc2/eqsat_decide/STATEMENTS");

const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
/// The quotient formers: part of the theory, not axioms (Ax0's definition).
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

/// The closure digest of `EqsatRule.Sound` the `eqsat_rules` gate pins, read
/// from that gate's source so the two gates cannot hold two pins.
fn sound_closure_pin() -> String {
    let source = include_str!("eqsat_rules.rs");
    let declared = "const SOUND_CLOSURE_DIGEST: &str =";
    let at = source
        .find(declared)
        .expect("eqsat_rules.rs declares SOUND_CLOSURE_DIGEST");
    assert!(
        !source[at + declared.len()..].contains(declared),
        "eqsat_rules.rs declares SOUND_CLOSURE_DIGEST once"
    );
    let rest = &source[at + declared.len()..];
    let open = rest.find('"').expect("the pin is a string literal");
    let close = rest[open + 1..]
        .find('"')
        .expect("the pin's literal is closed");
    let pin = &rest[open + 1..open + 1 + close];
    assert!(
        pin.len() == 64 && pin.bytes().all(|b| b.is_ascii_hexdigit()),
        "the pin is a SHA-256 in hex: {pin}"
    );
    pin.to_owned()
}

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by {PINNED}; the workspace pin moved"
    );
    clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (PKG-U6 reads lean-{PINNED})"))
}

/// Every constant `root` reaches through types, values, inductive families,
/// constructors and recursors, by name.
fn reach(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(x) = stack.pop() {
        if !seen.insert(x.clone()) {
            continue;
        }
        let mut used = HashSet::new();
        let walk = |e: &Expr, used: &mut HashSet<Name>| {
            e.used_constants_dag(UsedConstants::WithProjectionStructures, used);
        };
        if let Some(c) = env.get_const(&x) {
            walk(&c.type_, &mut used);
            if let Some(v) = &c.value {
                walk(v, &mut used);
            }
        }
        if let Some(i) = env.get_inductive(&x) {
            walk(&i.type_, &mut used);
            used.extend(i.constructor_names.iter().cloned());
            used.extend(i.all_names.iter().cloned());
        }
        if let Some(c) = env.get_constructor(&x) {
            walk(&c.type_, &mut used);
            used.insert(c.inductive_name.clone());
        }
        if let Some(r) = env.get_recursor(&x) {
            walk(&r.type_, &mut used);
            used.insert(r.inductive_name.clone());
        }
        stack.extend(used.into_iter().filter(|u| !seen.contains(u)));
    }
    seen
}

/// The axioms `root` reaches, the quotient formers excluded.
fn axioms_of(env: &Environment, root: &Name) -> BTreeSet<String> {
    reach(env, root)
        .into_iter()
        .filter(|x| {
            env.get_const(x)
                .is_some_and(|c| c.kind == ConstantKind::Axiom && c.value.is_none())
        })
        .map(|x| x.to_string())
        .filter(|x| !QUOT_FORMERS.contains(&x.as_str()))
        .collect()
}

/// The kernel declarations a compiled module makes, read off its own `.olean`,
/// each with its declared safety. A module split into parts is refused: its
/// private part would go unread.
fn module_constants(family_dir: &Path, module: &str) -> Vec<(Name, Option<DefinitionSafety>)> {
    let path = family_dir.join(format!("{module}.olean"));
    for part in ["olean.private", "olean.server"] {
        let sibling = family_dir.join(format!("{module}.{part}"));
        assert!(
            !sibling.exists(),
            "{} exists: a split module",
            sibling.display()
        );
    }
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_module(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let listed: BTreeSet<&str> = parsed.const_names.iter().map(String::as_str).collect();
    let carried: BTreeSet<&str> = parsed.constants.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(listed, carried, "{module}: constNames and constants agree");
    parsed
        .constants
        .iter()
        .map(|c| (n(&c.name), c.definition_safety))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn family_source_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(PINNED)
        .join(FAMILY)
}

/// The modules whose declarations are audited: the two taken from
/// `eqsat_rules`, then the family's own.
fn audited_modules() -> Vec<&'static str> {
    FROM_EQSAT_RULES.into_iter().chain(MODULES).collect()
}

/// What one replay from EMPTY measured.
struct Replay {
    kernel: ReferenceKernel,
    declared: usize,
    admitted: usize,
    unsafe_twins: usize,
    load_ms: u128,
    replay_ms: u128,
    env_digest: String,
    sound_closure: String,
}

/// Load the family beside the pinned `Init`, admit every declaration of the
/// audited modules from EMPTY through the entry and audit each.
fn replay() -> Replay {
    let lib = pinned_lib();
    let dir = compiled_fixture_dir(FAMILY);
    let started = Instant::now();
    let mut env = Environment::for_lean_replay();
    let modules: Vec<String> = audited_modules().iter().map(|m| (*m).to_owned()).collect();
    let summaries = load_modules_with_deps(&mut env, &modules, &[dir.clone(), lib])
        .unwrap_or_else(|e| panic!("load the eqsat_decide family: {e}"));
    let loaded: BTreeSet<_> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_deref())
        .collect();
    for module in audited_modules() {
        assert!(loaded.contains(module), "module was not loaded: {module}");
    }
    let load_ms = started.elapsed().as_millis();

    let mut declared: BTreeSet<Name> = BTreeSet::new();
    let mut violations: Vec<String> = Vec::new();
    let mut unsafe_twins = 0usize;
    for module in audited_modules() {
        for (name, safety) in module_constants(&dir, module) {
            match safety {
                Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial) => {
                    if name.to_string().ends_with("._unsafe_rec") {
                        unsafe_twins += 1;
                    } else {
                        violations.push(format!(
                            "{name}: is a {safety:?} declaration that is not a compiler twin"
                        ));
                    }
                }
                _ => {
                    declared.insert(name);
                }
            }
        }
    }
    assert!(!declared.is_empty(), "the modules declare constants");

    let started = Instant::now();
    let mut options = ClosedRecheckOptions::default();
    options.max_heartbeats = BUDGET;
    let built = reference_base_closed(&env, &declared, &options).expect("start");
    let replay_ms = started.elapsed().as_millis();
    if !built.report.passed() {
        violations.push(format!("replay: {}", built.report.verdict_sentence()));
        for refusal in &built.report.refusals {
            violations.push(format!("replay refusal: {refusal:?}"));
        }
    }
    for (unit, refusal) in &built.entry_refusals {
        violations.push(format!("{unit}: refused by the entry: {refusal:?}"));
    }
    let ax0: BTreeSet<String> = AX0.iter().map(|s| (*s).to_string()).collect();
    {
        let k = built.kernel().environment();
        for name in &declared {
            let present = k.get_const(name).is_some()
                || k.get_inductive(name).is_some()
                || k.get_constructor(name).is_some()
                || k.get_recursor(name).is_some();
            if !present {
                violations.push(format!("{name}: not admitted through the entry"));
                continue;
            }
            // A second reading, on the kernel's own environment, of what the
            // entry already refused above: a declaration that reaches an
            // axiom outside Ax0 is not admitted (`OutsideAx0`) and stops at
            // the `continue`, so no fixture of this family reaches the three
            // checks below. They stay as a reading that does not go through
            // the entry's own classification.
            if let Some(c) = k.get_const(name) {
                if matches!(c.kind, ConstantKind::Axiom | ConstantKind::Opaque) {
                    violations.push(format!("{name}: is an {:?} constant", c.kind));
                }
            }
            let closure = axioms_of(k, name);
            if !closure.is_subset(&ax0) {
                violations.push(format!("{name}: closure {closure:?} is not ⊆ Ax0"));
            }
            let cone = reach(k, name);
            for bad in [
                "sorryAx",
                "Lean.ofReduceBool",
                "Lean.ofReduceNat",
                "Lean.trustCompiler",
            ] {
                if cone.contains(&n(bad)) {
                    violations.push(format!("{name}: reaches {bad}"));
                }
            }
        }
    }
    assert!(
        violations.is_empty(),
        "{} audit violation(s):\n  {}",
        violations.len(),
        violations.join("\n  ")
    );
    let admitted = built.admitted.len();
    let kernel = built.into_kernel().expect("a passing, pinned replay");
    assert_eq!(kernel.theory_id(), TheoryId::LeanReferenceV1);
    let sound_closure = kernel
        .environment()
        .closure_digest(&n("EqsatRule.Sound"))
        .expect("the closure of EqsatRule.Sound is enumerable");
    Replay {
        declared: declared.len(),
        admitted,
        unsafe_twins,
        load_ms,
        replay_ms,
        env_digest: hex(&kernel.env_digest().0),
        sound_closure: hex(&sound_closure),
        kernel,
    }
}

// ── Kernel terms of the residue evaluator ──

fn level_one() -> Level {
    Level::succ(Level::zero())
}

/// `@Eq.{1} ty lhs rhs`, for `ty : Type`.
fn eq(ty: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(n("Eq"), vec![level_one()]), [c(ty), lhs, rhs])
}

/// `@Eq.refl.{1} ty value`.
fn refl(ty: &str, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(n("Eq.refl"), vec![level_one()]),
        [c(ty), value],
    )
}

fn res(r: u64) -> Expr {
    app("EqsatDecide.RV.res", [nat(r)])
}

fn ok_res(r: u64) -> Expr {
    app("EqsatDecide.RR.ok", [res(r)])
}

/// An assignment: a `List RV` literal.
fn assignment(values: Vec<Expr>) -> Expr {
    let rv = || c("EqsatDecide.RV");
    values.into_iter().rev().fold(
        Expr::apps(Expr::const_(n("List.nil"), vec![Level::zero()]), [rv()]),
        |rest, value| {
            Expr::apps(
                Expr::const_(n("List.cons"), vec![Level::zero()]),
                [rv(), value, rest],
            )
        },
    )
}

/// `Pat.evalR int 8 256 env pat`.
fn eval_r(int: bool, env: Vec<Expr>, pat: Expr) -> Expr {
    app(
        "EqsatRule.Pat.evalR",
        [boolean(int), nat(8), nat(256), assignment(env), pat],
    )
}

/// A rule as the fields `checkR` takes: direction, left side, right side,
/// side conditions.
#[derive(Clone)]
struct Fields {
    dir: &'static str,
    lhs: Expr,
    rhs: Expr,
    conds: Expr,
}

/// `checkR dir lhs rhs conds int 8 256 env`.
fn check_r(rule: &Fields, int: bool, env: Vec<Expr>) -> Expr {
    app(
        "EqsatDecide.checkR",
        [
            c(&format!("EqsatRule.Dir.{}", rule.dir)),
            rule.lhs.clone(),
            rule.rhs.clone(),
            rule.conds.clone(),
            boolean(int),
            nat(8),
            nat(256),
            assignment(env),
        ],
    )
}

/// The kernel evaluates the residue evaluator: each closed outcome is accepted
/// by `Eq.refl`, and the forged outcome beside it is refused on the same entry.
fn kernel_controls(k: &ReferenceKernel) -> usize {
    let none = || conds(vec![]);
    let mut pairs = 0usize;
    let mut pair = |goal: Expr, forged: Expr, proof: Expr, what: &str| {
        accepted(k, &goal, &proof, what);
        refused(k, &forged, &proof, &format!("{what}, forged"));
        pairs += 1;
    };

    // 200 + 100 at 8 bits is 44, never 300.
    let sum = || eval_r(true, vec![res(200), res(100)], bin("add", var(0), var(1)));
    pair(
        eq("EqsatDecide.RR", sum(), ok_res(44)),
        eq("EqsatDecide.RR", sum(), ok_res(300)),
        refl("EqsatDecide.RR", ok_res(44)),
        "the outcome of (add ?x ?y) on 200, 100",
    );

    // An undefined operator is `ub`, never a value.
    let quotient = || eval_r(true, vec![res(5), res(0)], bin("udiv", var(0), var(1)));
    pair(
        eq("EqsatDecide.RR", quotient(), c("EqsatDecide.RR.ub")),
        eq("EqsatDecide.RR", quotient(), ok_res(0)),
        refl("EqsatDecide.RR", c("EqsatDecide.RR.ub")),
        "the outcome of (udiv ?x ?y) on 5, 0",
    );
    let forged_ub = refl("EqsatDecide.RR", ok_res(0));
    refused(
        k,
        &eq("EqsatDecide.RR", quotient(), c("EqsatDecide.RR.ub")),
        &forged_ub,
        "a value offered as the proof of an undefined outcome",
    );

    // `(const INT)` is not a term at `bool`, and an unbound variable is not
    // a term: `bad`, never a value.
    let literal_at_bool = || eval_r(false, vec![], lit(false, 0));
    pair(
        eq("EqsatDecide.RR", literal_at_bool(), c("EqsatDecide.RR.bad")),
        eq("EqsatDecide.RR", literal_at_bool(), ok_res(0)),
        refl("EqsatDecide.RR", c("EqsatDecide.RR.bad")),
        "the outcome of (const 0) at bool",
    );
    let unbound = || eval_r(true, vec![res(1)], var(1));
    pair(
        eq("EqsatDecide.RR", unbound(), c("EqsatDecide.RR.bad")),
        eq("EqsatDecide.RR", unbound(), ok_res(1)),
        refl("EqsatDecide.RR", c("EqsatDecide.RR.bad")),
        "the outcome of an unbound variable",
    );

    // One assignment of a true rule, `(and ?x (not ?x)) = (const 0)`.
    let and_not = Fields {
        dir: "equiv",
        lhs: bin("and", var(0), un("not", var(0))),
        rhs: lit(false, 0),
        conds: none(),
    };
    let check = |rule: &Fields, env: Vec<Expr>, value: bool| {
        eq("Bool", check_r(rule, true, env), boolean(value))
    };
    pair(
        check(&and_not, vec![res(0xa5)], true),
        check(&and_not, vec![res(0xa5)], false),
        refl("Bool", boolean(true)),
        "checkR of (and ?x (not ?x)) = 0 at 0xa5",
    );

    // A false rule, `(and ?x (const 254)) = ?x`: `false` at its
    // counterexample 1, where `rfl` on `true` is refused; `true` at 2.
    let and_254 = Fields {
        dir: "equiv",
        lhs: bin("and", var(0), lit(false, 254)),
        rhs: var(0),
        conds: none(),
    };
    pair(
        check(&and_254, vec![res(1)], false),
        check(&and_254, vec![res(1)], true),
        refl("Bool", boolean(false)),
        "checkR of (and ?x (const 254)) = ?x at 1",
    );
    pair(
        check(&and_254, vec![res(2)], true),
        check(&and_254, vec![res(1)], true),
        refl("Bool", boolean(true)),
        "rfl on true for (and ?x (const 254)) = ?x, at 2 against its counterexample 1",
    );

    // The direction, as `Sound` reads it: `(udiv ?x ?x) -> 1` at 0 has an
    // undefined left side, so the `refines` rule stands there and the
    // `equiv` rule does not.
    let udiv_self = |dir: &'static str| Fields {
        dir,
        lhs: bin("udiv", var(0), var(0)),
        rhs: lit(false, 1),
        conds: none(),
    };
    pair(
        check(&udiv_self("refines"), vec![res(0)], true),
        check(&udiv_self("equiv"), vec![res(0)], true),
        refl("Bool", boolean(true)),
        "checkR of (udiv ?x ?x) -> 1 at 0, refines against equiv",
    );
    // Undefined behaviour on the right side stands under neither direction.
    for dir in ["equiv", "refines"] {
        let one_to_udiv = Fields {
            dir,
            lhs: lit(false, 1),
            rhs: bin("udiv", var(0), var(0)),
            conds: none(),
        };
        pair(
            check(&one_to_udiv, vec![res(0)], false),
            check(&one_to_udiv, vec![res(0)], true),
            refl("Bool", boolean(false)),
            &format!("checkR of 1 -> (udiv ?x ?x) at 0, {dir}"),
        );
    }
    // A side that is not a term stands under neither direction: `?y` is
    // unbound in a one-variable assignment.
    for dir in ["equiv", "refines"] {
        let unbound_side = Fields {
            dir,
            lhs: var(1),
            rhs: var(1),
            conds: none(),
        };
        pair(
            check(&unbound_side, vec![res(0)], false),
            check(&unbound_side, vec![res(0)], true),
            refl("Bool", boolean(false)),
            &format!("checkR of ?y -> ?y with ?y unbound, {dir}"),
        );
    }

    // A right side that is not a term stands nowhere, not even beside an
    // undefined left side, where `Sound` asks nothing of it: `(udiv ?x 0)`
    // refines to 7 at 5, and does not refine to an unbound `?y`.
    let udiv_zero = |rhs: Expr| Fields {
        dir: "refines",
        lhs: bin("udiv", var(0), lit(false, 0)),
        rhs,
        conds: none(),
    };
    pair(
        check(&udiv_zero(lit(false, 7)), vec![res(5)], true),
        check(&udiv_zero(var(1)), vec![res(5)], true),
        refl("Bool", boolean(true)),
        "checkR of (udiv ?x 0) refines to 7 at 5, against an unbound right side",
    );

    // `pow2` holds at the top power of two: `?c = 0 where (pow2 ?c)` fails
    // at 128, and passes at 129 only by failing its condition.
    let pow2_zero = Fields {
        dir: "equiv",
        lhs: terms::cvar(0),
        rhs: lit(false, 0),
        conds: conds(vec![app("EqsatRule.Cond.pow2", [nat(0)])]),
    };
    pair(
        check(&pow2_zero, vec![res(129)], true),
        check(&pow2_zero, vec![res(128)], true),
        refl("Bool", boolean(true)),
        "checkR of ?c = 0 where (pow2 ?c), at 129 against 128",
    );

    // A side condition that fails skips the assignment: `(rotl ?x (const
    // ?n)) = ?x where ?n == 0 mod width` is tested at ?n = 8, and at ?n = 3,
    // where its sides differ, it stands only with its condition.
    let rotl_full = |with_condition: bool| Fields {
        dir: "equiv",
        lhs: bin("rotl", var(1), terms::cvar(0)),
        rhs: var(1),
        conds: conds(if with_condition {
            vec![app("EqsatRule.Cond.zeroModWidth", [nat(0)])]
        } else {
            vec![]
        }),
    };
    pair(
        check(&rotl_full(true), vec![res(8), res(0x81)], true),
        check(&rotl_full(true), vec![res(8), res(0x81)], false),
        refl("Bool", boolean(true)),
        "checkR of rotl_full at ?n = 8",
    );
    pair(
        check(&rotl_full(true), vec![res(3), res(0x81)], true),
        check(&rotl_full(false), vec![res(3), res(0x81)], true),
        refl("Bool", boolean(true)),
        "checkR of rotl_full at ?n = 3, with its condition against without",
    );
    pairs + operators::operator_controls(k)
}

/// The unoptimized replay of `Init`'s cone is far slower, so a debug run skips
/// it unless `--ignored` asks. `--profile authority` keeps debug assertions
/// on and so needs `-- --include-ignored`; `--release` runs it unasked.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "unoptimized replay of the cone takes many minutes; run with --profile authority -- --include-ignored, or --release"
)]
fn eqsat_decide_replay_from_empty_with_closures_in_ax0_and_kernel_controls() {
    let first = replay();
    eprintln!("eqsat_decide: budget {BUDGET} kernel heartbeats, for the replay and for each check");
    eprintln!(
        "eqsat_decide: declared {} (set aside {} unsafe compiler twins), admitted {} through the \
         entry; load {} ms, replay from EMPTY {} ms",
        first.declared, first.unsafe_twins, first.admitted, first.load_ms, first.replay_ms
    );
    eprintln!("eqsat_decide: env_digest {}", first.env_digest);
    eprintln!(
        "eqsat_decide: closure_digest(EqsatRule.Sound) {}",
        first.sound_closure
    );
    assert_eq!(
        first.sound_closure,
        sound_closure_pin(),
        "the closure digest of EqsatRule.Sound is not the one the eqsat_rules gate pins: this \
         family changed what a rule statement means"
    );
    let k = &first.kernel;

    // ── Every theorem of the pinned modules is in the replayed environment
    //    as a theorem, and states what its pinned row says. ──
    let pins = statement_pins(STATEMENTS);
    let mut closures: HashMap<Name, [u8; 32]> = HashMap::new();
    let mut observed: BTreeMap<String, String> = BTreeMap::new();
    let mut absent: Vec<String> = Vec::new();
    for name in required_statements() {
        match statement_digest(k.environment(), &n(&name), &mut closures) {
            Ok(digest) => {
                observed.insert(name, digest);
            }
            Err(why) => absent.push(why),
        }
    }
    assert!(
        absent.is_empty(),
        "required theorems the replayed environment does not hold:\n  {}",
        absent.join("\n  ")
    );
    if let Err(why) = check_statement_pins(&observed, &pins) {
        let table: Vec<String> = observed
            .iter()
            .map(|(name, digest)| format!("{name} {digest}"))
            .collect();
        panic!(
            "{why}\nthe statements this replay computed (re-pin a row only with the reason in \
             the commit message):\n{}",
            table.join("\n")
        );
    }
    eprintln!(
        "eqsat_decide: {} statements required by name and equal to their pins",
        observed.len()
    );
    eprintln!(
        "eqsat_decide: statement(EqsatDecide.exhaust8_sound) {}",
        observed["EqsatDecide.exhaust8_sound"]
    );
    // The comparison refuses a moved statement and a missing row, on the real
    // table, and a definition has no statement digest.
    {
        let (some, digest) = observed.iter().next().expect("statements are pinned");
        let mut moved = pins.clone();
        let flipped = if digest.starts_with('0') { '1' } else { '0' };
        moved.insert(some.clone(), format!("{flipped}{}", &digest[1..]));
        assert!(check_statement_pins(&observed, &moved)
            .is_err_and(|why| why.contains("not the pinned one")));
        let mut missing = pins.clone();
        missing.remove(some);
        assert!(check_statement_pins(&observed, &missing)
            .is_err_and(|why| why.contains("no pinned statement")));
        assert!(
            statement_digest(k.environment(), &n("EqsatDecide.checkR"), &mut closures).is_err(),
            "a definition has no statement digest"
        );
    }

    let pairs = kernel_controls(k);
    assert_eq!(
        pairs, CLOSED_OUTCOME_PAIRS,
        "the closed outcomes of the residue evaluator the gate checks"
    );
    eprintln!(
        "eqsat_decide: {pairs} closed outcomes of the residue evaluator accepted by Eq.refl, each \
         beside a forged outcome the entry refused"
    );

    let procedure = procedure::procedure_controls(k);
    assert_eq!(
        procedure.proved, RULES_PROVED,
        "the rule and type pairs the record term proves"
    );
    assert_eq!(
        procedure.refused, TERMS_REFUSED,
        "the terms the procedure controls have the entry refuse"
    );
    eprintln!(
        "eqsat_decide: {} rule and type pairs proved by `exhaust8_sound <literal> <type> \
         rflTrue` under {BUDGET} heartbeats: the dearest {}, all of them {}; {} terms refused \
         for the claim",
        procedure.proved, procedure.dearest, procedure.total, procedure.refused
    );

    // ── Identity: a second replay from EMPTY in this process. ──
    let second = replay();
    assert_eq!(
        first.env_digest, second.env_digest,
        "the environment digest differs between two replays"
    );
    assert_eq!(
        first.sound_closure, second.sound_closure,
        "the closure digest of EqsatRule.Sound differs between two replays"
    );
    assert_eq!(first.admitted, second.admitted);
    eprintln!(
        "eqsat_decide: second replay from EMPTY {} ms; env_digest and closure digest equal",
        second.replay_ms
    );
}

/// The source tripwire, for what the kernel cannot see (`implemented_by`,
/// `extern`) and as a second reading of what it can: no module of the family
/// has a banned word in its code (strings, characters and comments lexed
/// out) or a string literal, and the family takes SemR, the vocabulary and
/// the helpers from their own families and holds no copy.
#[test]
fn eqsat_decide_sources_carry_no_escape() {
    let dir = family_source_dir();
    for module in MODULES {
        let path = dir.join(format!("{module}.lean"));
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        assert_eq!(
            banned_words(&text),
            Vec::<&str>::new(),
            "{module}.lean has a banned word in its code"
        );
        let code = lean_code_only(&text);
        for word in ["bv_decide", "ofReduceBool", "ofReduceNat", "trustCompiler"] {
            assert!(
                !code.contains(word),
                "{module}.lean names `{word}` in its code"
            );
        }
        assert!(
            !code.contains('"'),
            "{module}.lean has a string literal in its code: the procedures are string-free"
        );
    }
    let order = std::fs::read_to_string(dir.join("ORDER")).expect("ORDER");
    let lines: Vec<&str> = order
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect();
    let mut expected = vec!["from semr SemR".to_owned()];
    expected.extend(
        FROM_EQSAT_RULES
            .iter()
            .map(|module| format!("from eqsat_rules {module}")),
    );
    expected.extend(MODULES.iter().map(|module| (*module).to_owned()));
    assert_eq!(
        lines, expected,
        "ORDER is SemR, the two eqsat_rules modules, then exactly the audited modules"
    );
    for copied in ["SemR", "EqsatRule", "EqsatBasics"] {
        assert!(
            !dir.join(format!("{copied}.lean")).exists(),
            "the family holds no copy of {copied}.lean"
        );
    }
}

/// The pinned statements are the theorems the sources declare: every theorem
/// of the pinned modules has a row in `STATEMENTS` and every row names one.
/// This runs without Lean, so a theorem added, renamed or deleted fails here
/// first; the replay test compares each row's digest with the statement the
/// kernel holds.
#[test]
fn eqsat_decide_statement_pins_name_the_sources_theorems() {
    let pins = statement_pins(STATEMENTS);
    let required = required_statements();
    let pinned: BTreeSet<String> = pins.keys().cloned().collect();
    let unpinned: Vec<&String> = required.difference(&pinned).collect();
    let stale: Vec<&String> = pinned.difference(&required).collect();
    assert!(
        unpinned.is_empty() && stale.is_empty(),
        "STATEMENTS and the sources disagree.\n  theorems with no row: {unpinned:?}\n  rows \
         with no theorem: {stale:?}"
    );
    // The theorems a consumer of the module is pointed to are among them (a
    // rename of one is a change to the documents too).
    for theorem in [
        "EqsatDecide.evalR_agrees",
        "EqsatDecide.holdsR_sound",
        "EqsatDecide.condsR_of_condsHold",
        "EqsatDecide.checkR_sound",
        "EqsatDecide.rflTrue",
        "EqsatDecide.sweep_sound",
        "EqsatDecide.live_satisfiable",
        "EqsatDecide.exhaust8_run",
        "EqsatDecide.holdsR_bad_left",
        "EqsatDecide.holdsR_bad_right",
        "EqsatDecide.live_defined",
        "EqsatDecide.exhaust8_sound",
        "EqsatDecide.exhaust8_defined",
        "EqsatDecide.exhaust8_satisfiable",
    ] {
        assert!(pinned.contains(theorem), "{theorem} is a pinned statement");
    }
    // The module of every pinned set is a module of the family.
    for (module, _) in PINNED_MODULES {
        assert!(MODULES.contains(&module), "{module} is a module of ORDER");
    }
    assert!(SAT_LEMMAS.is_empty());
}
