// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PKG-U2, PKG-U4c: the statements of trust-cg's e-graph rewrite rules over
//! SemR, kernel-checked by Clean THROUGH the reference entry, every closure ⊆
//! Ax0.
//!
//! The fixture family `tests/fixtures/lean/v4.30.0-rc2/eqsat_rules/` (its
//! README) holds the rule vocabulary (`EqsatRule`), the statements that pin it
//! (`EqsatAnchors`), the rule literals generated from trust-cg's rule files,
//! the lemmas of the integer rule set and of the saturation tier's rule set,
//! and the refutations of trust-cg's wrong rules. SemR is the `semr` family's
//! one copy (`from semr SemR`). Here:
//!
//! * the family is compiled by the pinned `lean -o`, and every kernel
//!   declaration its fourteen modules make is admitted from EMPTY through
//!   `ReferenceKernel` (`reference_base_closed`), is neither an axiom nor
//!   opaque, and has a closure ⊆ Ax0 that reaches no native-evaluation or sorry
//!   constant;
//! * every lemma the family's `LEMMAS` table names (one per rule of the two
//!   rule files and scope of the rule's domain; the `fold_*` rules get none)
//!   is a theorem whose type is the row's statement term for term, on the
//!   literal generated from the rule's file (`Defs` for the integer rule
//!   set, `TierSDefs` for a rule only the saturation tier has), and the entry
//!   accepts its record term for `Sound <literal> <type>` at every type of
//!   the scope; a `Sound` theorem of the lemma modules that no row names is
//!   refused, and a lemma that is not proved is listed in
//!   [`lemmas::TIMED_OUT`], never dropped (`eqsat_rules/lemmas.rs`);
//! * the files `gen_rule_defs.py` generates (the three modules of literals
//!   and `LEMMAS`) equal their pinned bytes ([`lemmas::GENERATED_FILES`]), so
//!   a literal edited by hand needs a visible re-pin;
//! * the two rule names both rule files have (`add_zero`, `mul_one`) are one
//!   row each: the two generated literals are one term, and the entry accepts
//!   the row's lemma for the saturation tier's statement at every type too;
//! * a rule statement built here as a raw kernel term, the way trust-cg's
//!   generator will build it (constructors and `Nat` literals only), is
//!   accepted with the family's lemma as its proof term;
//! * negative controls on the same entry, each beside an accepted control: an
//!   edited literal, a dropped side condition, another rule's lemma, another
//!   type's instance, and the refines proof of `(udiv ?x ?x) -> 1` offered for
//!   the equiv statement of the same sides;
//! * the statement does not carry the rule's domain: a bool-only rule's lemma
//!   is accepted for its statement at an integer type, so the domain test
//!   stays trust-cg's;
//! * each wrong-rule refutation is the statement `¬ Sound <wrong rule> <type>`
//!   it is named for, at its named type and (the `_all` forms) at each of the
//!   twelve integer types; the pointer-width controls are refuted at `usize`
//!   and hold at the fixed width that makes them true;
//! * a rule with a `where` clause has a satisfiability lemma
//!   (`EqsatInt.<rule>_sat`) that the entry accepts for
//!   `Satisfiable <literal> <type>` at every integer type, and a rule whose
//!   conditions contradict each other is `Sound` and refused as `Satisfiable`;
//! * what the kernel does NOT refuse is asserted as measured: a one-way rule
//!   of the grammar stated as `equiv`, and a lemma offered for a different
//!   literal with the same proposition (`const` flags, `var` against `cvar`,
//!   one residue);
//! * every theorem of `EqsatAnchors`, `EqsatIntControls` and
//!   `EqsatTierSControls` and every
//!   satisfiability lemma is required by name in the replayed environment and
//!   its statement is the pinned one (the family's `STATEMENTS` file,
//!   [`statement_digest`]);
//! * the closure digests of `EqsatRule.Sound` and `EqsatRule.Satisfiable` are
//!   the pinned ones ([`SOUND_CLOSURE_DIGEST`],
//!   [`SATISFIABLE_CLOSURE_DIGEST`]), and two replays from EMPTY in one
//!   process give one environment digest and one closure digest; both are
//!   printed so runs can be compared across processes.
//!
//! The environment digest is not pinned: it chains every admitted
//! declaration, so it moves with each lemma added to the family. It is
//! pinned where trust-cg cuts its bundle from a finished lemma set.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{ReferenceKernel, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_modules_with_deps, parse_module, reference_base_closed, DefinitionSafety};

#[path = "support/lean_tripwire.rs"]
mod lean_tripwire;
use lean_tripwire::{banned_words, lean_code_only};

#[path = "eqsat_rules/terms.rs"]
mod terms;
use terms::n;

#[path = "eqsat_rules/statements.rs"]
mod statements;
use statements::{check_statement_pins, required_statements, statement_digest, statement_pins};

#[path = "eqsat_rules/lemmas.rs"]
mod lemmas;
use lemmas::{
    check_generated_bytes, check_generated_files, check_rows_against_declared,
    check_rows_against_kernel, check_rows_against_sources, check_shared_rules, conditioned_rules,
    declared_lemmas, generated_rules, lemma_rows, lemma_table_controls, rule_file_digest,
    shared_rule_controls, tier_s_kernel_controls, GENERATED_FILES, INTEGER_SET, LEMMAS, RULE_SETS,
    SHARED_RULES, TIER_S_SET,
};

#[path = "eqsat_rules/controls.rs"]
mod controls;

const PINNED: &str = "v4.30.0-rc2";
const FAMILY: &str = "eqsat_rules";

/// The family's own modules, in `ORDER` (SemR comes `from semr`).
const MODULES: [&str; 14] = [
    "EqsatRule",
    "EqsatBasics",
    "EqsatAnchors",
    "EqsatIntRuleDefs",
    "EqsatIntWrongRuleDefs",
    "EqsatIntSample",
    "EqsatIntArith",
    "EqsatIntCmpSelBool",
    "EqsatIntBitwise",
    "EqsatIntNegRot",
    "EqsatIntControls",
    "EqsatTierSRuleDefs",
    "EqsatTierSInt",
    "EqsatTierSControls",
];

/// The closure digest of `EqsatRule.Sound` on the replayed kernel environment
/// (`Environment::closure_digest`): what the statement of a rule means, byte
/// for byte, with everything of SemR and `Init` it reaches. trust-cg's rule
/// registry is to compare the same digest with its own compiled-in pin, so a
/// change to the vocabulary, to SemR's scalar operators or to the kernel's
/// record encoding moves this constant here first. The test prints the digest
/// it computed; re-pin only with the reason in the commit message.
///
/// Measured equal across three processes on one host, and with trust-ir's
/// `SemR.lean` at both `0ea0e29f…` (this family's `from semr`) and `91eba057…`
/// (trust-ir e1976aa7d, the revision trust-cg locks). Not measured on a
/// second host.
///
/// Re-pinned once, with PKG-U4c, from
/// `85e64655ac2b2ef551c3fb170dd78d3e77b99dca8b409e373d4b98a201e6d4e1`: the
/// vocabulary did not change, the kernel's records did. Since e3b7ac3d1b the
/// replay keeps the reducibility hint Lean wrote for a definition, where it
/// had kept only `is_reducible` and let `add_decl` compute a height of its
/// own. Of the 860 members, 31 definitions have another `Regular` height in
/// their record and no member differs in anything else: with the 31 earlier
/// heights put back, the digest computed over this environment is the earlier
/// pin again, and each of the 31 new heights is the one pinned Lean reports
/// for the definition (`docs/DECISIONS.md`, PKG-U4c). A kernel built from a
/// Clean revision before e3b7ac3d1b computes the earlier digest for the same
/// sources.
const SOUND_CLOSURE_DIGEST: &str =
    "10e1b56561cdee4eb35e7a1950d37e855b52b9426fd258c1187c35e1d90a4c20";

/// The closure digest of `EqsatRule.Satisfiable`: what the second statement
/// of a rule with a `where` clause means. Its closure is `Admits`, `CondsHold`
/// and `PbOk` with what they reach; it does not contain `Pat.eval`.
/// Re-pinned with [`SOUND_CLOSURE_DIGEST`], for the same reason, from
/// `670e47201a75ad03603661deb1001a6ef5eff51a5e1b320c53a974114a3c5c91`.
const SATISFIABLE_CLOSURE_DIGEST: &str =
    "cfc8b07a4901cb40c3b7ddbd739fbf3d8bfd7e057239e9d53be18eb7d48206c2";

/// The pinned statements: one `name digest` row per theorem of
/// [`PINNED_MODULES`] and per lemma of [`SAT_LEMMAS`] (the family's README,
/// "Compiling").
const STATEMENTS: &str = include_str!("fixtures/lean/v4.30.0-rc2/eqsat_rules/STATEMENTS");

/// The modules whose every theorem is pinned by name and statement, each with
/// the namespace its theorems are declared in.
const PINNED_MODULES: [(&str, &str); 3] = [
    ("EqsatAnchors", "EqsatRule"),
    ("EqsatIntControls", "EqsatIntControls"),
    ("EqsatTierSControls", "EqsatTierSControls"),
];

/// The satisfiability lemmas: one per rule of the integer rule set that has a
/// `where` clause and is not a `fold_*` rule. The source test derives the
/// same list from `EqsatIntRuleDefs.lean`, and requires that no rule of the
/// saturation tier's rule file has a `where` clause.
const SAT_LEMMAS: [&str; 3] = ["rotl_full", "rotr_full", "sub_const_to_add"];

const INT_TYPES: [&str; 12] = [
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
];

const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
/// The quotient formers: part of the theory, not axioms (Ax0's definition).
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by {PINNED}; the workspace pin moved"
    );
    clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (PKG-U2 reads lean-{PINNED})"))
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

/// What one replay from EMPTY measured.
struct Replay {
    kernel: ReferenceKernel,
    /// The cache directory the family was compiled in (its `.olean`s).
    family_dir: PathBuf,
    declared: usize,
    admitted: usize,
    unsafe_twins: usize,
    load_ms: u128,
    replay_ms: u128,
    env_digest: String,
    sound_closure: String,
    sound_closure_members: usize,
    satisfiable_closure: String,
}

/// Load the family beside the pinned `Init`, admit every declaration of its
/// modules from EMPTY through the entry and audit each.
fn replay() -> Replay {
    let lib = pinned_lib();
    let dir = compiled_fixture_dir(FAMILY);
    let started = Instant::now();
    let mut env = Environment::for_lean_replay();
    let modules: Vec<String> = MODULES.iter().map(|m| (*m).to_owned()).collect();
    let summaries = load_modules_with_deps(&mut env, &modules, &[dir.clone(), lib])
        .unwrap_or_else(|e| panic!("load the eqsat_rules family: {e}"));
    let loaded: BTreeSet<_> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_deref())
        .collect();
    for module in MODULES {
        assert!(loaded.contains(module), "module was not loaded: {module}");
    }
    let load_ms = started.elapsed().as_millis();

    let mut declared: BTreeSet<Name> = BTreeSet::new();
    let mut violations: Vec<String> = Vec::new();
    let mut unsafe_twins = 0usize;
    for module in MODULES {
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
    let built =
        reference_base_closed(&env, &declared, &ClosedRecheckOptions::default()).expect("start");
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
    let sound = n("EqsatRule.Sound");
    let sound_closure = kernel
        .environment()
        .closure_digest(&sound)
        .expect("the closure of EqsatRule.Sound is enumerable");
    let sound_closure_members = kernel
        .environment()
        .dependency_closure(&sound)
        .expect("the closure of EqsatRule.Sound is enumerable")
        .len();
    let satisfiable_closure = kernel
        .environment()
        .closure_digest(&n("EqsatRule.Satisfiable"))
        .expect("the closure of EqsatRule.Satisfiable is enumerable");
    Replay {
        satisfiable_closure: hex(&satisfiable_closure),
        declared: declared.len(),
        admitted,
        unsafe_twins,
        load_ms,
        replay_ms,
        env_digest: hex(&kernel.env_digest().0),
        sound_closure: hex(&sound_closure),
        sound_closure_members,
        kernel,
        family_dir: dir,
    }
}

/// The unoptimized replay of `Init`'s cone is far slower, so a debug run skips
/// it unless `--ignored` asks. `--profile authority` keeps debug assertions
/// on and so needs `-- --include-ignored`; `--release` runs it unasked.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "unoptimized replay of the cone takes many minutes; run with --profile authority -- --include-ignored, or --release"
)]
fn eqsat_rules_replay_from_empty_with_closures_in_ax0_and_kernel_controls() {
    let first = replay();
    eprintln!(
        "eqsat_rules: declared {} (set aside {} unsafe compiler twins), admitted {} through the \
         entry; load {} ms, replay from EMPTY {} ms",
        first.declared, first.unsafe_twins, first.admitted, first.load_ms, first.replay_ms
    );
    eprintln!("eqsat_rules: env_digest {}", first.env_digest);
    eprintln!(
        "eqsat_rules: closure_digest(EqsatRule.Sound) {} over {} members",
        first.sound_closure, first.sound_closure_members
    );
    assert_eq!(
        first.sound_closure, SOUND_CLOSURE_DIGEST,
        "the closure digest of EqsatRule.Sound moved: the meaning of every rule statement changed"
    );
    eprintln!(
        "eqsat_rules: closure_digest(EqsatRule.Satisfiable) {}",
        first.satisfiable_closure
    );
    assert_eq!(
        first.satisfiable_closure, SATISFIABLE_CLOSURE_DIGEST,
        "the closure digest of EqsatRule.Satisfiable moved: the meaning of every satisfiability \
         statement changed"
    );
    let k = &first.kernel;

    // ── Every anchor, control and satisfiability lemma is in the replayed
    //    environment as a theorem, and states what its pinned row says. ──
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
        "eqsat_rules: {} statements required by name and equal to their pins ({} closure digests)",
        observed.len(),
        closures.len()
    );
    // The comparison refuses a moved statement, a missing row and a row for
    // an absent theorem, on the real table.
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
        let mut extra = pins.clone();
        extra.insert("EqsatRule.no_such_anchor".to_owned(), digest.clone());
        assert!(check_statement_pins(&observed, &extra)
            .is_err_and(|why| why.contains("not a theorem of the family")));
        // A definition is not a statement, and neither is an absent name.
        assert!(
            statement_digest(k.environment(), &n("EqsatRule.Sound"), &mut closures).is_err(),
            "a definition has no statement digest"
        );
        assert!(
            statement_digest(
                k.environment(),
                &n("EqsatRule.no_such_anchor"),
                &mut closures
            )
            .is_err(),
            "an absent name has no statement digest"
        );
        // Two theorems with different statements have different digests.
        assert_ne!(
            observed["EqsatRule.sound_equiv_iff"], observed["EqsatRule.sound_refines_iff"],
            "two different statements, one digest"
        );
    }

    // ── Every lemma `LEMMAS` names is the theorem its row says, and no
    //    `Sound` theorem of the lemma modules is outside the table. ──
    let rows = lemma_rows(LEMMAS);
    let census = check_rows_against_sources(&rows).unwrap_or_else(|why| panic!("LEMMAS: {why}"));
    let acceptances = check_rows_against_kernel(k, &first.family_dir, &rows)
        .unwrap_or_else(|why| panic!("LEMMAS: {why}"));
    eprintln!(
        "eqsat_rules: {} of {} rules have lemmas: {} Sound lemmas required by name, each stating \
         its rule at its scope ({} at every integer type, {} at one type, {} bool instances, {} \
         bool-only; {} with the premise checker-ground-eval), {} timed-out; {} fold rules with no \
         lemma; {} statements accepted by the entry, one per rule file, rule and instance type",
        census.rules - census.fold_rules,
        census.rules,
        census.proved,
        census.all_int,
        census.one_type,
        census.bool_instances,
        census.bool_only,
        census.with_ground_eval,
        census.timed_out,
        census.fold_rules,
        acceptances.values().sum::<usize>()
    );
    for set in RULE_SETS {
        eprintln!(
            "eqsat_rules: {}: {} rules, {} statements accepted by the entry on its literals \
             (EqsatRule.{})",
            set.rule_file,
            set.rules,
            acceptances.get(set.defs_namespace).copied().unwrap_or(0),
            set.defs_namespace
        );
    }
    // Every rule of the saturation tier's file is proved at each of the
    // twelve integer types: 120 statements on its own literals, 24 of them
    // (the two rule names both files have) by the integer rule set's lemmas.
    assert_eq!(
        acceptances.get(TIER_S_SET.defs_namespace).copied(),
        Some(TIER_S_SET.rules * INT_TYPES.len()),
        "every rule of {} is accepted at every integer type",
        TIER_S_SET.rule_file
    );
    lemma_table_controls(k, &first.family_dir, &rows);
    shared_rule_controls(k);
    tier_s_kernel_controls(k);
    eprintln!(
        "eqsat_rules: {} rule names in both rule files ({}): one literal and one row each",
        SHARED_RULES.len(),
        SHARED_RULES.join(", ")
    );

    controls::kernel_controls(k);

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
    assert_eq!(
        first.satisfiable_closure, second.satisfiable_closure,
        "the closure digest of EqsatRule.Satisfiable differs between two replays"
    );
    let mut second_closures: HashMap<Name, [u8; 32]> = HashMap::new();
    for (name, digest) in &observed {
        assert_eq!(
            statement_digest(second.kernel.environment(), &n(name), &mut second_closures).as_ref(),
            Ok(digest),
            "the statement digest of {name} differs between two replays"
        );
    }
    assert_eq!(first.admitted, second.admitted);
    eprintln!(
        "eqsat_rules: second replay from EMPTY {} ms; env_digest and closure digest equal",
        second.replay_ms
    );
}

/// The source tripwire, for what the kernel cannot see (`implemented_by`,
/// `extern`) and as a second reading of what it can: no module of the family
/// has a banned word in its code (strings, characters and comments lexed
/// out), the vocabulary has no string literal, and the family takes SemR
/// from the `semr` family and holds no copy of its own.
#[test]
fn eqsat_rules_sources_carry_no_escape() {
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
        for word in ["bv_decide", "ofReduceBool", "ofReduceNat", "trustCompiler"] {
            assert!(
                !lean_code_only(&text).contains(word),
                "{module}.lean names `{word}` in its code"
            );
        }
    }
    let vocabulary = std::fs::read_to_string(dir.join("EqsatRule.lean")).expect("EqsatRule.lean");
    assert!(
        !vocabulary.contains('"'),
        "EqsatRule.lean has a double quote: the vocabulary has no string literal"
    );
    let order = std::fs::read_to_string(dir.join("ORDER")).expect("ORDER");
    assert!(
        order.lines().any(|line| line.trim() == "from semr SemR"),
        "the family takes SemR from the semr family"
    );
    assert!(
        !dir.join("SemR.lean").exists(),
        "the family holds no second SemR copy"
    );
    let stems: Vec<&str> = order
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#') && !line.starts_with("from "))
        .collect();
    assert_eq!(stems, MODULES, "ORDER lists exactly the audited modules");
}

/// The pinned statements are the theorems the sources declare: every theorem
/// of `EqsatAnchors`, `EqsatIntControls` and `EqsatTierSControls` has a row in
/// `STATEMENTS`, every row names one, and every rule with a `where` clause has
/// its satisfiability lemma in the pinned set. This runs without Lean, so an anchor added,
/// renamed or deleted fails here first; the replay test compares each row's
/// digest with the statement the kernel holds.
#[test]
fn eqsat_rules_statement_pins_name_the_sources_theorems() {
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
    // The anchors a reader is pointed to are among them (a rename of one is
    // a change to the documents too).
    for anchor in [
        "EqsatRule.admits_one_iff",
        "EqsatRule.admits_inhabited",
        "EqsatRule.pbOk_iff",
        "EqsatRule.sound_equiv_iff",
        "EqsatRule.sound_refines_iff",
        "EqsatRule.equiv_gives_refines",
        "EqsatRule.refines_gives_equiv_of_total",
        "EqsatRule.equiv_stop_never",
        "EqsatRule.refines_stop_left",
        "EqsatRule.refines_value_left",
        "EqsatRule.bin_eval",
        "EqsatRule.un_eval",
        "EqsatRule.cmp_eval",
        "EqsatRule.sel_eval",
        "EqsatRule.bin_reads",
        "EqsatRule.un_reads",
        "EqsatRule.cmp_reads",
        "EqsatRule.sel_reads",
        "EqsatRule.stop_order",
        "EqsatRule.const_flag_is_data",
        "EqsatRule.var_cvar_one_statement",
        "EqsatRule.sound_of_unsatisfiable",
        "EqsatRule.satisfiable_of_no_conds",
        "EqsatRule.satisfiable_bool",
        "EqsatIntControls.refines_does_not_give_equiv",
        "EqsatIntControls.band_false_as_equiv_is_true",
        "EqsatIntControls.refines_ub_left_any_rhs",
        "EqsatIntControls.contradictory_is_sound",
        "EqsatIntControls.contradictory_not_satisfiable",
        "EqsatIntControls.same_residue_one_statement",
        "EqsatIntControls.eval_free_twin_holds",
    ] {
        assert!(pinned.contains(anchor), "{anchor} is a pinned statement");
    }
    // Each rule name both rule files have has its pinned identity of
    // literals, and `EqsatTierSControls` pins nothing else.
    let identities: BTreeSet<String> = SHARED_RULES
        .iter()
        .map(|rule| format!("EqsatTierSControls.{rule}_is_the_integer_rule"))
        .collect();
    let tier_s_controls: BTreeSet<String> = pinned
        .iter()
        .filter(|name| name.starts_with("EqsatTierSControls."))
        .cloned()
        .collect();
    assert_eq!(
        tier_s_controls, identities,
        "EqsatTierSControls states one identity of literals per shared rule name"
    );
    // Every rule with a `where` clause has a satisfiability lemma, and no
    // lemma is listed for a rule without one.
    let conditioned = conditioned_rules(&INTEGER_SET);
    let listed: BTreeSet<String> = SAT_LEMMAS.iter().map(|rule| (*rule).to_owned()).collect();
    assert_eq!(
        conditioned, listed,
        "the rules with a `where` clause are the rules with a satisfiability lemma"
    );
    // No rule of the saturation tier's file has a `where` clause, so none
    // needs a satisfiability lemma; one that gains a clause fails here until
    // its lemma is written and pinned.
    assert_eq!(
        conditioned_rules(&TIER_S_SET),
        BTreeSet::new(),
        "a rule of {} has a `where` clause and no satisfiability lemma",
        TIER_S_SET.rule_file
    );
    for rule_name in SAT_LEMMAS {
        let lemma = format!("theorem {rule_name}_sat ");
        let declared = ["EqsatIntSample", "EqsatIntNegRot"].iter().any(|module| {
            let text = std::fs::read_to_string(family_source_dir().join(format!("{module}.lean")))
                .expect("a lemma module");
            lean_code_only(&text)
                .lines()
                .any(|line| line.starts_with(&lemma))
        });
        assert!(
            declared,
            "EqsatInt.{rule_name}_sat is declared by a lemma module"
        );
    }
}

/// The lemma table is the sources' lemmas, without Lean: `LEMMAS` names the
/// rules the two generated modules define (`EqsatIntRuleDefs.lean`, then the
/// rules only `EqsatTierSRuleDefs.lean` has), a `fold_*` rule has no lemma,
/// and every other row's lemma is declared by exactly one lemma module (or
/// the row is listed as timed out and no module declares it). So a lemma deleted
/// or renamed in the sources fails here first; the replay test compares each
/// one's statement with its row and looks for `Sound` theorems outside the
/// table. The generated files (the table and the three modules of literals)
/// equal their pinned bytes, so a literal edited by hand fails here even where
/// the kernel accepts the same proofs for it.
#[test]
fn eqsat_rules_lemma_rows_name_the_sources_theorems() {
    let rows = lemma_rows(LEMMAS);
    let census = check_rows_against_sources(&rows).unwrap_or_else(|why| panic!("LEMMAS: {why}"));
    assert_eq!(
        census.proved + census.timed_out,
        census.lemma_rows,
        "a lemma row is proved or timed out"
    );
    // The comparison refuses a row with no theorem, a renamed lemma, a lemma
    // for a fold rule and a table that lost a rule, on the real table.
    let position = |rule: &str| {
        rows.iter()
            .position(|row| row.rule == rule)
            .unwrap_or_else(|| panic!("LEMMAS has {rule}"))
    };
    let mut absent = rows.clone();
    absent[position("add_zero")].lemma = Some("EqsatInt.no_such_lemma".to_owned());
    assert!(
        check_rows_against_sources(&absent).is_err_and(|why| why.contains("not EqsatInt.add_zero"))
    );
    let mut fold = rows.clone();
    fold[position("fold_add")].lemma = Some("EqsatInt.fold_add".to_owned());
    assert!(check_rows_against_sources(&fold).is_err_and(|why| why.contains("are one thing")));
    let mut short = rows.clone();
    short.remove(position("mul_one"));
    assert!(check_rows_against_sources(&short).is_err_and(|why| why.contains("different rules")));
    // A lemma dropped from the sources is refused, and so is a theorem
    // declared for a fold rule.
    let declared = declared_lemmas().expect("the lemma modules' theorems");
    assert!(check_rows_against_declared(&rows, &declared).is_ok());
    let mut dropped = declared.clone();
    assert!(dropped.remove("EqsatInt.rotr_full").is_some());
    assert!(check_rows_against_declared(&rows, &dropped)
        .is_err_and(|why| why.contains("no lemma module declares it")));
    let mut folded = declared.clone();
    folded.insert("EqsatInt.fold_add".to_owned(), "EqsatIntArith");
    assert!(check_rows_against_declared(&rows, &folded)
        .is_err_and(|why| why.contains("a fold rule gets no lemma")));
    // Every lemma module of the table is a module of the family.
    for module in lemmas::LEMMA_MODULES {
        assert!(MODULES.contains(&module), "{module} is a module of ORDER");
    }

    // ── The saturation tier's rule file (PKG-U4c). ──
    // The table and each generated module were read from one rule text.
    for set in RULE_SETS {
        assert!(
            MODULES.contains(&set.defs_module),
            "{} is a module of ORDER",
            set.defs_module
        );
        let digest = rule_file_digest(set).unwrap_or_else(|why| panic!("{why}"));
        eprintln!(
            "eqsat_rules: LEMMAS and {}.lean were generated from {} {digest}",
            set.defs_module, set.rule_file
        );
    }
    // The generated files are the reviewed ones, byte for byte: a literal
    // or a row edited by hand is refused here, whether or not the kernel
    // would see it.
    check_generated_files().unwrap_or_else(|why| panic!("{why}"));
    eprintln!(
        "eqsat_rules: {} generated files equal their pinned bytes ({})",
        GENERATED_FILES.len(),
        GENERATED_FILES.map(|(file, _)| file).join(", ")
    );
    // Controls on the pins, on the saturation tier's literals: two edits the
    // kernel does not see (they keep every proposition, so the family
    // compiles and the same proofs are accepted), one it does, and a comment.
    let tier_s_module = format!("{}.lean", TIER_S_SET.defs_module);
    let tier_s_text = std::fs::read_to_string(family_source_dir().join(&tier_s_module))
        .unwrap_or_else(|e| panic!("read {tier_s_module}: {e}"));
    assert!(check_generated_bytes(&tier_s_module, tier_s_text.as_bytes()).is_ok());
    for (what, from, to) in [
        ("a `const` flag", "Srt.t false", "Srt.t true"),
        (
            "`cvar` for `var`",
            "(Pat.var (nat_lit 1))",
            "(Pat.cvar (nat_lit 1))",
        ),
        (
            "another operator",
            "(Pat.bin BinOp.mul (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))",
            "(Pat.bin BinOp.add (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))",
        ),
        (
            "a comment",
            "Variables: x = 0 (t), y = 1 (t).",
            "Variables: none.",
        ),
    ] {
        let edited = tier_s_text.replacen(from, to, 1);
        assert_ne!(edited, tier_s_text, "{tier_s_module} has `{from}`");
        assert!(
            check_generated_bytes(&tier_s_module, edited.as_bytes())
                .is_err_and(|why| why.contains("the gate pins")),
            "{tier_s_module} with {what} edited must be refused"
        );
    }
    // A table row edited by hand, the table's bytes under a module's name,
    // and a file that is not generated.
    assert!(check_generated_bytes("LEMMAS", LEMMAS.as_bytes()).is_ok());
    let edited = LEMMAS.replacen("add_comm int plain", "add_comm u8 plain", 1);
    assert_ne!(edited, LEMMAS);
    assert!(check_generated_bytes("LEMMAS", edited.as_bytes())
        .is_err_and(|why| why.contains("the gate pins")));
    assert!(check_generated_bytes(&tier_s_module, LEMMAS.as_bytes())
        .is_err_and(|why| why.contains("the gate pins")));
    assert!(
        check_generated_bytes("EqsatTierSInt.lean", tier_s_text.as_bytes())
            .is_err_and(|why| why.contains("not a file of GENERATED_FILES"))
    );
    // The rule names both files have are the listed ones, on one literal.
    check_shared_rules().unwrap_or_else(|why| panic!("{why}"));
    // Every rule of the file has a lemma row at every integer type: its own
    // (stated on its own literal) or, for a shared name, the integer rule
    // set's. No rule of the file is without a lemma, and none is timed out.
    let tier_s_rules = generated_rules(&TIER_S_SET);
    assert_eq!(tier_s_rules.len(), TIER_S_SET.rules);
    for rule in &tier_s_rules {
        let row = &rows[position(rule)];
        let shared = SHARED_RULES.contains(&rule.as_str());
        assert_eq!(
            (row.scope.as_str(), row.kind.as_str(), row.lemma.as_deref()),
            ("int", "plain", Some(format!("EqsatInt.{rule}").as_str())),
            "{rule}: one lemma at every integer type"
        );
        let both = vec![INTEGER_SET.defs_namespace, TIER_S_SET.defs_namespace];
        let own = vec![TIER_S_SET.defs_namespace];
        assert_eq!(
            row.defs,
            if shared { both } else { own },
            "{rule}: the rule files that have it"
        );
        assert!(
            !lemmas::TIMED_OUT.contains(&(rule.as_str(), "int")),
            "{rule}: proved, not timed out"
        );
        // Its lemma dropped from the sources is refused; so is its row
        // dropped from the table.
        let mut dropped = declared.clone();
        assert!(dropped.remove(&format!("EqsatInt.{rule}")).is_some());
        assert!(
            check_rows_against_declared(&rows, &dropped)
                .is_err_and(|why| why.contains("no lemma module declares it")),
            "{rule}: its lemma dropped from the sources must be refused"
        );
        let mut short = rows.clone();
        short.remove(position(rule));
        assert!(
            check_rows_against_sources(&short).is_err_and(|why| why.contains("different rules")),
            "{rule}: its row dropped from the table must be refused"
        );
    }
    // The eight rules only this file has are declared by its lemma module.
    let own: BTreeSet<String> = tier_s_rules
        .iter()
        .filter(|rule| !SHARED_RULES.contains(&rule.as_str()))
        .map(|rule| format!("EqsatInt.{rule}"))
        .collect();
    let in_module: BTreeSet<String> = declared
        .iter()
        .filter(|(name, module)| **module == "EqsatTierSInt" && own.contains(*name))
        .map(|(name, _)| name.clone())
        .collect();
    assert_eq!(own.len(), 8);
    assert_eq!(in_module, own, "EqsatTierSInt declares the eight lemmas");
}
