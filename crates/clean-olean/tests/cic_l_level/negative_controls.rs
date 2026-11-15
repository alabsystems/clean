// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit E6 on the re-admitted kernel environment: one negative control
//! per constructor of `CICL.CoreJudgmentIn` (or the inventory's reason for
//! none), and the `WfContext` witness census.
//!
//! The rule inventory (`data/cic_l_rule_inventory.json`) names each
//! constructor's control; this module holds it to the admitted constants. A
//! control is a theorem `Refutes .c policy sig Γ s`, and the check reads what
//! `Refutes` means off the admitted definitions rather than trusting their
//! names: `Closed c` is constructor `c` with the judgment abstracted,
//! `Mutation c` is `Closed c` with exactly one non-dependent premise deleted,
//! `MutatedDerives` quantifies over relations closed under the other rules
//! and the mutation, and `Refutes` conjoins that with the judgment's refusal.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};

const CARRIER: &str = "CICL.CoreJudgmentIn";
const MODULE: &str = "CICL.NegativeControls";
const INVENTORY: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../data/cic_l_rule_inventory.json"
);

/// What the rule inventory records for one constructor of the carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Control {
    /// The control theorem, by qualified name.
    Theorem(String),
    /// No control, and the recorded reason.
    Owed(String),
}

/// The `WfContext` census: constructor, witness, and the level of the sort
/// the new entry's type lives in (none for the empty context).
const WF_CENSUS: &[(&str, &str, Option<u32>)] = &[
    ("nil", "wf_empty", None),
    ("assumption", "wf_assumption_sort_zero", Some(0)),
    ("assumption", "wf_assumption_sort_one", Some(1)),
    ("assumption", "wf_assumption_sort_two", Some(2)),
    ("definition", "wf_definition_sort_zero", Some(0)),
    ("definition", "wf_definition_sort_one", Some(1)),
    ("definition", "wf_definition_sort_two", Some(2)),
];

/// The levels of a height-2 tower, which every binder form must cover.
const WF_LEVELS: &[u32] = &[0, 1, 2];

/// Contexts with an ill-formed entry that `WfContext` refuses.
const WF_REFUSALS: &[&str] = &[
    "wf_refuses_open_assumption",
    "wf_refuses_open_definition",
    "wf_refuses_open_tail",
];

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn short(n: &Name) -> String {
    let full = n.to_string();
    full.rsplit('.').next().unwrap_or(&full).to_owned()
}

fn apply(head: Expr, args: &[Expr]) -> Expr {
    args.iter().fold(head, |f, a| Expr::app(f, a.clone()))
}

fn zero_levels(env: &Environment, n: &str) -> Result<Vec<Level>, String> {
    let c = env
        .get_const(&name(n))
        .ok_or_else(|| format!("{n} was not admitted"))?;
    Ok(vec![Level::zero(); c.level_params.len()])
}

fn constant(env: &Environment, n: &str) -> Result<Expr, String> {
    Ok(Expr::const_(name(n), zero_levels(env, n)?))
}

/// A constant no environment declares: the checks below only reduce and
/// compare, so a stand-in for each parameter keeps the terms closed.
fn stand_in(s: &str) -> Expr {
    Expr::const_(name(&format!("CICL.Controls.E6.{s}")), vec![])
}

fn head_is(e: &Expr, n: &str) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(c, _) if c == &name(n))
}

/// Structural equality up to binder annotations, which carry no meaning.
fn same(a: &Expr, b: &Expr) -> bool {
    match (a.kind(), b.kind()) {
        (ExprKind::Pi(_, d1, b1), ExprKind::Pi(_, d2, b2))
        | (ExprKind::Lam(_, d1, b1), ExprKind::Lam(_, d2, b2)) => same(d1, d2) && same(b1, b2),
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => same(f1, f2) && same(a1, a2),
        _ => a == b,
    }
}

/// The inventory's control for each carrier constructor, by short name.
pub(crate) fn inventory_controls() -> Result<BTreeMap<String, Control>, String> {
    let text = std::fs::read_to_string(INVENTORY).map_err(|e| format!("{INVENTORY}: {e}"))?;
    let doc: serde_json::Value =
        serde_json::from_str(&text).map_err(|e| format!("{INVENTORY}: {e}"))?;
    let rows = doc["rows"]
        .as_array()
        .ok_or_else(|| format!("{INVENTORY} has no rows"))?;
    let mut table = BTreeMap::new();
    for item in rows
        .iter()
        .filter_map(|row| row["cic_l"].as_array())
        .flatten()
    {
        let Some(ctor) = item["item"]
            .as_str()
            .and_then(|i| i.strip_prefix(&format!("{CARRIER}.")))
        else {
            continue;
        };
        let control = &item["control"];
        let entry = match (control["theorem"].as_str(), control["none"].as_str()) {
            (Some(t), None) => Control::Theorem(t.to_owned()),
            (None, Some(reason)) if !reason.trim().is_empty() => Control::Owed(reason.to_owned()),
            _ => continue,
        };
        if let Some(previous) = table.insert(ctor.to_owned(), entry.clone()) {
            if previous != entry {
                return Err(format!(
                    "{ctor} is given two controls: {previous:?}, {entry:?}"
                ));
            }
        }
    }
    Ok(table)
}

/// The carrier's constructors, by short name, in declaration order.
fn carrier_constructors(env: &Environment) -> Result<Vec<String>, String> {
    Ok(env
        .get_inductive(&name(CARRIER))
        .ok_or_else(|| format!("{CARRIER} was not admitted"))?
        .constructor_names
        .iter()
        .map(short)
        .collect())
}

/// Each admitted theorem stating `Refutes .c ...`, grouped by `c`.
fn refutation_census(env: &Environment) -> BTreeMap<String, BTreeSet<String>> {
    let mut census: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for c in env.constants() {
        if c.value.is_none() || !head_is(&c.type_, &format!("{MODULE}.Refutes")) {
            continue;
        }
        let rule = match c.type_.get_app_args().get(1).map(|r| r.kind().clone()) {
            Some(ExprKind::Const(r, _)) => short(&r),
            _ => format!("<unreadable rule in {}>", c.name),
        };
        census.entry(rule).or_default().insert(c.name.to_string());
    }
    census
}

/// `Closed c` and `Mutation c` at stand-in parameters and judgment `J`,
/// reduced to their telescopes.
struct RuleForms {
    constructor: Expr,
    closed: Expr,
    mutation: Expr,
}

fn rule_forms(
    env: &Environment,
    checker: &TypeChecker<'_>,
    ctor: &str,
) -> Result<RuleForms, String> {
    let params = [stand_in("Metadata"), stand_in("policy"), stand_in("sig")];
    let judgment = stand_in("J");
    let carrier = apply(constant(env, CARRIER)?, &params);
    let info = env
        .get_const(&name(&format!("{CARRIER}.{ctor}")))
        .ok_or_else(|| format!("{CARRIER}.{ctor} was not admitted"))?;
    let levels: Vec<(Name, Level)> = info
        .level_params
        .iter()
        .map(|p| (p.clone(), Level::zero()))
        .collect();
    let mut constructor = info.type_.instantiate_level_params(&levels);
    for param in &params {
        let ExprKind::Pi(_, _, body) = constructor.kind() else {
            return Err(format!("{CARRIER}.{ctor} has fewer than three parameters"));
        };
        constructor = body.instantiate(param);
    }
    let constructor = abstract_judgment(&constructor, &carrier, &judgment)?;
    let rule = constant(env, &format!("{MODULE}.Rule.{ctor}"))?;
    let at = |def: &str| -> Result<Expr, String> {
        let mut args = params.to_vec();
        args.extend([judgment.clone(), rule.clone()]);
        Ok(checker.whnf(&apply(constant(env, &format!("{MODULE}.{def}"))?, &args)))
    };
    Ok(RuleForms {
        constructor,
        closed: at("Closed")?,
        mutation: at("Mutation")?,
    })
}

/// Replace every occurrence of the applied carrier by the stand-in judgment;
/// any other mention of the carrier is refused.
fn abstract_judgment(e: &Expr, carrier: &Expr, judgment: &Expr) -> Result<Expr, String> {
    if e == carrier {
        return Ok(judgment.clone());
    }
    Ok(match e.kind() {
        ExprKind::App(f, a) => Expr::app(
            abstract_judgment(f, carrier, judgment)?,
            abstract_judgment(a, carrier, judgment)?,
        ),
        ExprKind::Pi(bd, d, b) => Expr::pi(
            *bd,
            abstract_judgment(d, carrier, judgment)?,
            abstract_judgment(b, carrier, judgment)?,
        ),
        ExprKind::Lam(bd, d, b) => Expr::lam(
            *bd,
            abstract_judgment(d, carrier, judgment)?,
            abstract_judgment(b, carrier, judgment)?,
        ),
        _ if e.collect_constants().contains(&name(CARRIER)) => {
            return Err(format!(
                "the carrier occurs other than applied to its parameters in {e}"
            ))
        }
        _ => e.clone(),
    })
}

fn pi_count(e: &Expr) -> usize {
    match e.kind() {
        ExprKind::Pi(_, _, b) => 1 + pi_count(b),
        _ => 0,
    }
}

/// The telescope with its `k`-th binder removed, if nothing after it uses it.
fn delete_binder(e: &Expr, k: usize) -> Option<Expr> {
    let ExprKind::Pi(bd, d, b) = e.kind() else {
        return None;
    };
    if k == 0 {
        return (!b.has_loose_bvar(0)).then(|| b.instantiate(&Expr::prop()));
    }
    Some(Expr::pi(*bd, (**d).clone(), delete_binder(b, k - 1)?))
}

/// The position of the one non-dependent premise of `full` that `mutated`
/// deletes, keeping every other binder and the conclusion.
pub(crate) fn premise_deleted(full: &Expr, mutated: &Expr) -> Result<usize, String> {
    (0..pi_count(full))
        .find(|&k| delete_binder(full, k).is_some_and(|d| same(&d, mutated)))
        .ok_or_else(|| {
            format!("{mutated}\nis not\n{full}\nwith exactly one non-dependent premise deleted")
        })
}

/// What `Refutes` and `MutatedDerives` unfold to, at stand-in arguments.
fn check_definitions(env: &Environment, checker: &TypeChecker<'_>) -> Result<(), String> {
    let [m, p, s, r, g, x] =
        ["Metadata", "policy", "sig", "rule", "context", "statement"].map(stand_in);
    let refutes = checker.whnf(&apply(
        constant(env, &format!("{MODULE}.Refutes"))?,
        &[
            m.clone(),
            r.clone(),
            p.clone(),
            s.clone(),
            g.clone(),
            x.clone(),
        ],
    ));
    let derives = apply(
        constant(env, &format!("{MODULE}.MutatedDerives"))?,
        &[
            m.clone(),
            p.clone(),
            s.clone(),
            r.clone(),
            g.clone(),
            x.clone(),
        ],
    );
    let judged = apply(
        constant(env, CARRIER)?,
        &[m.clone(), p.clone(), s.clone(), g.clone(), x.clone()],
    );
    let expected = apply(
        Expr::const_(name("And"), vec![]),
        &[
            derives.clone(),
            Expr::app(Expr::const_(name("Not"), vec![]), judged),
        ],
    );
    if !same(&refutes, &expected) {
        return Err(format!("Refutes unfolds to {refutes}, not {expected}"));
    }
    // ∀ J, (∀ r', r' ≠ r → Closed J r') → Mutation J r → J Γ s
    let relation = Expr::pi(
        BinderInfo::Default,
        Expr::app(constant(env, "CICL.Context")?, m.clone()),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(constant(env, "CICL.Statement")?, m.clone()),
            Expr::prop(),
        ),
    );
    let rule_type = Expr::const_(name(&format!("{MODULE}.Rule")), vec![]);
    let others = Expr::pi(
        BinderInfo::Default,
        rule_type.clone(),
        Expr::pi(
            BinderInfo::Default,
            apply(
                Expr::const_(name("Ne"), vec![Level::succ(Level::zero())]),
                &[rule_type, Expr::bvar(0), r.clone()],
            ),
            apply(
                constant(env, &format!("{MODULE}.Closed"))?,
                &[
                    m.clone(),
                    p.clone(),
                    s.clone(),
                    Expr::bvar(2),
                    Expr::bvar(1),
                ],
            ),
        ),
    );
    let mutation = apply(
        constant(env, &format!("{MODULE}.Mutation"))?,
        &[m, p, s, Expr::bvar(1), r],
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        relation,
        Expr::pi(
            BinderInfo::Default,
            others,
            Expr::pi(BinderInfo::Default, mutation, apply(Expr::bvar(2), &[g, x])),
        ),
    );
    let derives = checker.whnf(&derives);
    if !same(&derives, &expected) {
        return Err(format!(
            "MutatedDerives unfolds to {derives}, not {expected}"
        ));
    }
    Ok(())
}

/// One rule: `Closed` is its constructor, `Mutation` deletes one premise, and
/// the theorems refuting it are exactly the inventory's control, or none.
fn check_rule(
    env: &Environment,
    checker: &TypeChecker<'_>,
    ctor: &str,
    control: &Control,
    stated: &BTreeSet<String>,
) -> Result<String, String> {
    let forms = rule_forms(env, checker, ctor)?;
    if !same(&forms.closed, &forms.constructor) {
        return Err(format!(
            "Closed .{ctor} is {}, not the constructor with the judgment abstracted: {}",
            forms.closed, forms.constructor
        ));
    }
    let deleted = premise_deleted(&forms.closed, &forms.mutation)
        .map_err(|e| format!("Mutation .{ctor}: {e}"))?;
    match control {
        Control::Theorem(theorem) => {
            if stated != &BTreeSet::from([theorem.clone()]) {
                return Err(format!(
                    "{ctor}'s control is {theorem}, and the theorems refuting .{ctor} are {stated:?}"
                ));
            }
            if theorem != &format!("{MODULE}.{ctor}_control") {
                return Err(format!(
                    "{ctor}'s control {theorem} is not named {ctor}_control"
                ));
            }
            Ok(format!(
                "{ctor}: {theorem} refutes the rule with binder {deleted} deleted"
            ))
        }
        Control::Owed(reason) => {
            if !stated.is_empty() {
                return Err(format!(
                    "{ctor} records no control ({reason}), and {stated:?} refute it"
                ));
            }
            Ok(format!(
                "{ctor}: no control, binder {deleted} deleted: {reason}"
            ))
        }
    }
}

/// Every constructor has a control or a recorded reason, every control
/// refutes its own rule's mutation, and the definitions mean what they say.
pub(crate) fn check_controls(
    env: &Environment,
    checker: &TypeChecker<'_>,
    table: &BTreeMap<String, Control>,
) -> Result<Vec<String>, String> {
    let ctors = carrier_constructors(env)?;
    for ctor in &ctors {
        if !table.contains_key(ctor) {
            return Err(format!(
                "constructor {CARRIER}.{ctor} names no negative control in the rule inventory"
            ));
        }
    }
    for ctor in table.keys() {
        if !ctors.contains(ctor) {
            return Err(format!(
                "the inventory gives a control to {ctor}, which {CARRIER} lacks"
            ));
        }
    }
    let rules: Vec<String> = env
        .get_inductive(&name(&format!("{MODULE}.Rule")))
        .ok_or_else(|| format!("{MODULE}.Rule was not admitted"))?
        .constructor_names
        .iter()
        .map(short)
        .collect();
    if rules != ctors {
        return Err(format!(
            "{MODULE}.Rule is {rules:?}, not {CARRIER}'s constructors {ctors:?}"
        ));
    }
    check_definitions(env, checker)?;
    let census = refutation_census(env);
    let mut lines = Vec::new();
    let mut problems = Vec::new();
    for ctor in &ctors {
        let stated = census.get(ctor).cloned().unwrap_or_default();
        match check_rule(env, checker, ctor, &table[ctor], &stated) {
            Ok(line) => lines.push(line),
            Err(problem) => problems.push(problem),
        }
    }
    if !problems.is_empty() {
        return Err(problems.join("\n"));
    }
    for rule in census.keys() {
        if !ctors.contains(rule) {
            return Err(format!(
                "{:?} refute {rule}, which is no rule",
                census[rule]
            ));
        }
    }
    Ok(lines)
}

fn level_height(checker: &TypeChecker<'_>, e: &Expr) -> Option<u32> {
    let e = checker.whnf(e);
    let args = e.get_app_args();
    if head_is(&e, "CICL.Level.zero") && args.is_empty() {
        Some(0)
    } else if head_is(&e, "CICL.Level.succ") && args.len() == 1 {
        level_height(checker, args[0]).map(|h| h + 1)
    } else {
        None
    }
}

/// `WfContext` is inhabited at each constructor, at each level of the tower
/// for each binder form, and refuses the ill-formed contexts.
pub(crate) fn check_wf_census(
    env: &Environment,
    checker: &TypeChecker<'_>,
    census: &[(&str, &str, Option<u32>)],
) -> Result<(), String> {
    let ctors: BTreeSet<String> = env
        .get_inductive(&name("CICL.WfContext"))
        .ok_or("CICL.WfContext was not admitted")?
        .constructor_names
        .iter()
        .map(short)
        .collect();
    let witnessed: BTreeSet<String> = census.iter().map(|(c, _, _)| (*c).to_owned()).collect();
    if ctors != witnessed {
        return Err(format!(
            "WfContext has {ctors:?}, and the census witnesses {witnessed:?}"
        ));
    }
    for (ctor, witness, level) in census {
        let c = env
            .get_const(&name(&format!("{MODULE}.{witness}")))
            .ok_or_else(|| format!("{witness} was not admitted"))?;
        if !head_is(&c.type_, "CICL.WfContext") {
            return Err(format!("{witness} does not state WfContext"));
        }
        let value = checker.whnf(
            c.value
                .as_ref()
                .ok_or_else(|| format!("{witness} has no proof"))?,
        );
        if !head_is(&value, &format!("CICL.WfContext.{ctor}")) {
            return Err(format!(
                "{witness} does not apply WfContext.{ctor} at its root: {value}"
            ));
        }
        // The entry's sort level is argument 4 of `assumption` (Metadata sig
        // Γ A u) and 5 of `definition` (Metadata sig Γ A v u).
        let at = match *ctor {
            "assumption" => Some(4),
            "definition" => Some(5),
            _ => None,
        };
        let found = at.and_then(|i| {
            value
                .get_app_args()
                .get(i)
                .and_then(|u| level_height(checker, u))
        });
        if found != *level {
            return Err(format!(
                "{witness} has its entry at level {found:?}, not {level:?}"
            ));
        }
    }
    for form in ["assumption", "definition"] {
        let levels: BTreeSet<u32> = census
            .iter()
            .filter(|(c, _, _)| *c == form)
            .filter_map(|(_, _, l)| *l)
            .collect();
        if levels != WF_LEVELS.iter().copied().collect() {
            return Err(format!(
                "the {form} witnesses cover levels {levels:?}, not {WF_LEVELS:?}"
            ));
        }
    }
    for refusal in WF_REFUSALS {
        let c = env
            .get_const(&name(&format!("{MODULE}.{refusal}")))
            .ok_or_else(|| format!("{refusal} was not admitted"))?;
        let refused = c.type_.get_app_args().first().map(|r| (*r).clone());
        if !head_is(&c.type_, "Not") || !refused.is_some_and(|r| head_is(&r, "CICL.WfContext")) {
            return Err(format!("{refusal} does not refuse a WfContext"));
        }
    }
    Ok(())
}

/// The E6 check and its planted failures: a constructor whose control row is
/// gone, a row naming a theorem that refutes another rule or none, a mutation
/// that deletes nothing, and a census missing a level.
pub(crate) fn run(env: &Environment, checker: &TypeChecker<'_>) {
    let table = inventory_controls().expect("read the rule inventory's controls");
    for line in check_controls(env, checker, &table).expect("E6 negative controls") {
        eprintln!("E6 {line}");
    }
    check_wf_census(env, checker, WF_CENSUS).expect("E6 WfContext census");

    // Planted failures, each refused for its own reason.
    let planted = |change: &dyn Fn(&mut BTreeMap<String, Control>)| {
        let mut table = table.clone();
        change(&mut table);
        check_controls(env, checker, &table)
    };
    let sort = rule_forms(env, checker, "sort").expect("sort's forms");
    let bvar = rule_forms(env, checker, "bvar").expect("bvar's forms");
    let short_census: Vec<_> = WF_CENSUS
        .iter()
        .copied()
        .filter(|(_, w, _)| *w != "wf_definition_sort_two")
        .collect();
    let arms: [(&str, Result<Vec<String>, String>, &str); 6] = [
        (
            "a constructor whose control row is gone",
            planted(&|t| {
                t.remove("sort");
            }),
            "CoreJudgmentIn.sort names no negative control",
        ),
        (
            "a row naming a control that refutes another rule",
            planted(&|t| {
                t.insert(
                    "sort".to_owned(),
                    Control::Theorem(format!("{MODULE}.bvar_control")),
                );
            }),
            "the theorems refuting .sort are",
        ),
        (
            "a row naming a theorem that refutes nothing",
            planted(&|t| {
                t.insert(
                    "sort".to_owned(),
                    Control::Theorem("CICL.CoreTypingCases.sort_ground".to_owned()),
                );
            }),
            "the theorems refuting .sort are",
        ),
        (
            "a rule recorded as having no control while one refutes it",
            planted(&|t| {
                t.insert("sort".to_owned(), Control::Owed("planted".to_owned()));
            }),
            "records no control (planted)",
        ),
        (
            "a mutation that deletes nothing",
            premise_deleted(&sort.closed, &sort.closed).map(|k| vec![k.to_string()]),
            "with exactly one non-dependent premise deleted",
        ),
        (
            "another rule's mutation",
            premise_deleted(&sort.closed, &bvar.mutation).map(|k| vec![k.to_string()]),
            "with exactly one non-dependent premise deleted",
        ),
    ];
    for (label, outcome, reason) in arms {
        let err = outcome.expect_err(&format!("self-test: {label} must fail"));
        assert!(
            err.contains(reason),
            "self-test: {label} failed otherwise: {err}"
        );
        eprintln!("E6 SELFTEST refused {label}: {reason}");
    }
    let err = check_wf_census(env, checker, &short_census)
        .expect_err("self-test: a census missing a level must fail");
    assert!(
        err.contains("the definition witnesses cover levels"),
        "{err}"
    );
    eprintln!("E6 SELFTEST refused a WfContext census missing a level: {err}");
}
