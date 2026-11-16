// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lemma table of the `eqsat_rules` gate: the family's `LEMMAS` file names,
//! for every rule of the integer rule set and every scope of its domain, the
//! lemma that scope needs. The gate requires each as a theorem of the replayed
//! environment whose statement is the row's, term for term, and accepted by
//! the entry at every type of the scope; and it refuses a `Sound` theorem of
//! the lemma modules that no row names. So a lemma that is dropped, renamed,
//! restated or added without its row fails here.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_kernel::env::ConstantKind;
use clean_kernel::expr::Expr;
use clean_kernel::{BinderInfo, ExprKind, ReferenceKernel};

use super::statements::source_theorems;
use super::terms::{accepted, app, c, int_ty, n, sound};
use super::{family_source_dir, lean_tripwire::lean_code_only, module_constants, INT_TYPES};

/// The family's lemma table (`gen_rule_defs.py --lemmas` writes it from
/// trust-cg's rule text).
pub(super) const LEMMAS: &str = include_str!("../fixtures/lean/v4.30.0-rc2/eqsat_rules/LEMMAS");

/// The modules that declare the rule lemmas, all in namespace `EqsatInt`.
pub(super) const LEMMA_MODULES: [&str; 5] = [
    "EqsatIntSample",
    "EqsatIntArith",
    "EqsatIntCmpSelBool",
    "EqsatIntBitwise",
    "EqsatIntNegRot",
];

/// The rows of `LEMMAS` whose lemma is not proved, as `(rule, scope)`; the
/// family's README says what was tried for each. Such a lemma must be absent
/// from the sources and from the replayed environment, so a row is either
/// proved or listed here and never both. Empty: every lemma the integer rule
/// set needs is proved.
pub(super) const TIMED_OUT: [(&str, &str); 0] = [];

/// The rule set as counted: rules, `fold_*` rules (no lemma) and lemma rows.
/// `LEMMAS` is the list; these make a regenerated table that adds or drops a
/// rule a change to this file too.
const RULES: usize = 76;
const FOLD_RULES: usize = 28;
const LEMMA_ROWS: usize = 56;

/// One row of `LEMMAS`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LemmaRow {
    pub(super) rule: String,
    /// `int` (all twelve integer types), one integer type, or `bool`.
    pub(super) scope: String,
    /// `plain`, `eval` (premise `checker-ground-eval`) or `fold` (no lemma).
    pub(super) kind: String,
    /// The lemma's full name; `None` for a `fold` row.
    pub(super) lemma: Option<String>,
}

impl LemmaRow {
    fn timed_out(&self) -> bool {
        TIMED_OUT.contains(&(self.rule.as_str(), self.scope.as_str()))
    }

    fn rule_def(&self) -> Expr {
        c(&format!("EqsatRule.Defs.{}", self.rule))
    }

    /// What the lemma's type must be, term for term:
    /// `∀ t : SemR.IntTy, Sound Defs.<rule> (STy.int t)` for scope `int`, else
    /// `Sound Defs.<rule> <type>`.
    fn statement(&self) -> Expr {
        match self.scope.as_str() {
            "int" => Expr::pi(
                BinderInfo::Default,
                c("SemR.IntTy"),
                sound(self.rule_def(), app("EqsatRule.STy.int", [Expr::bvar(0)])),
            ),
            "bool" => sound(self.rule_def(), c("EqsatRule.STy.bool")),
            t => sound(self.rule_def(), int_ty(t)),
        }
    }

    /// Each instance type of the scope with the statement trust-cg builds
    /// there and the record term that proves it.
    fn instances(&self, lemma: &str) -> Vec<(String, Expr, Expr)> {
        match self.scope.as_str() {
            "int" => INT_TYPES
                .iter()
                .map(|t| {
                    (
                        (*t).to_owned(),
                        sound(self.rule_def(), int_ty(t)),
                        app(lemma, [c(&format!("SemR.IntTy.{t}"))]),
                    )
                })
                .collect(),
            _ => vec![(self.scope.clone(), self.statement(), c(lemma))],
        }
    }
}

/// The rows of a `LEMMAS` text: `rule scope kind lemma`, one per line; `#`
/// starts a comment line. A malformed row, a repeated `(rule, scope)` and a
/// lemma two rows name are panics, never skipped rows.
pub(super) fn lemma_rows(text: &str) -> Vec<LemmaRow> {
    let mut rows: Vec<LemmaRow> = Vec::new();
    let mut scopes: BTreeSet<(String, String)> = BTreeSet::new();
    let mut lemmas: BTreeSet<String> = BTreeSet::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split_whitespace();
        let (Some(rule), Some(scope), Some(kind), Some(lemma), None) = (
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
        ) else {
            panic!("LEMMAS: not a `rule scope kind lemma` row: {line}");
        };
        assert!(
            scope == "int" || scope == "bool" || INT_TYPES.contains(&scope),
            "LEMMAS: {rule}: `{scope}` is not a scope"
        );
        assert!(
            matches!(kind, "plain" | "eval" | "fold"),
            "LEMMAS: {rule}: `{kind}` is not a kind"
        );
        assert!(
            scopes.insert((rule.to_owned(), scope.to_owned())),
            "LEMMAS: {rule} at {scope} has two rows"
        );
        let lemma = (lemma != "-").then(|| lemma.to_owned());
        if let Some(lemma) = &lemma {
            assert!(
                lemma.starts_with("EqsatInt."),
                "LEMMAS: {lemma} is not in namespace EqsatInt"
            );
            assert!(
                lemmas.insert(lemma.clone()),
                "LEMMAS: two rows name {lemma}"
            );
        }
        rows.push(LemmaRow {
            rule: rule.to_owned(),
            scope: scope.to_owned(),
            kind: kind.to_owned(),
            lemma,
        });
    }
    rows
}

/// The name the README gives the lemma of `rule` at `scope`, given every
/// scope the rule has ("Lemma names and the record term").
fn lemma_name(rule: &str, scope: &str, scopes: &BTreeSet<&str>) -> String {
    match scope {
        "int" => format!("EqsatInt.{rule}"),
        "bool" if scopes.len() == 1 => format!("EqsatInt.{rule}"),
        _ => format!("EqsatInt.{rule}_{scope}"),
    }
}

/// The rules `EqsatIntRuleDefs.lean` defines, in its order.
fn generated_rules() -> Vec<String> {
    let path = family_source_dir().join("EqsatIntRuleDefs.lean");
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    lean_code_only(&text)
        .lines()
        .filter_map(|line| line.strip_prefix("def "))
        .map(|rest| {
            rest.strip_suffix(" : Rule :=")
                .unwrap_or_else(|| {
                    panic!("EqsatIntRuleDefs.lean: not a generated definition: {rest}")
                })
                .to_owned()
        })
        .collect()
}

/// What the table holds, for the gate's printed line.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct LemmaCensus {
    pub(super) rules: usize,
    pub(super) fold_rules: usize,
    pub(super) lemma_rows: usize,
    pub(super) proved: usize,
    pub(super) timed_out: usize,
    pub(super) all_int: usize,
    pub(super) one_type: usize,
    pub(super) bool_instances: usize,
    pub(super) bool_only: usize,
    pub(super) with_ground_eval: usize,
}

/// `rows` against the sources, without Lean: the table's rules are the
/// generated definitions in their order; a row is a `fold` row exactly when
/// its rule is a `fold_*` rule and then names no lemma; every other row names
/// the lemma the README's naming gives it; and that lemma is declared by
/// exactly one lemma module, unless the row is timed out, in which case no
/// module declares it.
pub(super) fn check_rows_against_sources(rows: &[LemmaRow]) -> Result<LemmaCensus, String> {
    check_rows_against_declared(rows, &declared_lemmas()?)
}

/// The theorems the lemma modules' sources declare, each with its module. A
/// name two modules declare is refused: the gate loads them into one
/// environment.
pub(super) fn declared_lemmas() -> Result<BTreeMap<String, &'static str>, String> {
    let mut declared: BTreeMap<String, &'static str> = BTreeMap::new();
    for module in LEMMA_MODULES {
        for theorem in source_theorems(module, "EqsatInt") {
            if let Some(first) = declared.insert(theorem.clone(), module) {
                return Err(format!("{theorem}: declared by {first} and by {module}"));
            }
        }
    }
    Ok(declared)
}

/// [`check_rows_against_sources`] over a given set of declared theorems.
pub(super) fn check_rows_against_declared(
    rows: &[LemmaRow],
    declared: &BTreeMap<String, &'static str>,
) -> Result<LemmaCensus, String> {
    let mut order: Vec<&str> = Vec::new();
    let mut scopes: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for row in rows {
        if order.last() != Some(&row.rule.as_str()) {
            if scopes.contains_key(row.rule.as_str()) {
                return Err(format!("{}: its rows are not together", row.rule));
            }
            order.push(&row.rule);
        }
        scopes.entry(&row.rule).or_default().insert(&row.scope);
    }
    let generated = generated_rules();
    if order != generated {
        return Err(format!(
            "LEMMAS and EqsatIntRuleDefs.lean name different rules, or in a different order \
             ({} rows' rules, {} definitions): regenerate both from one rule text",
            order.len(),
            generated.len()
        ));
    }
    if let Some(fold) = declared
        .keys()
        .find(|name| name.starts_with("EqsatInt.fold_"))
    {
        return Err(format!("{fold}: a fold rule gets no lemma"));
    }
    for (rule, scope) in TIMED_OUT {
        if !rows
            .iter()
            .any(|row| row.rule == rule && row.scope == scope && row.lemma.is_some())
        {
            return Err(format!("TIMED_OUT: {rule} at {scope} is not a lemma row"));
        }
    }
    let mut census = LemmaCensus {
        rules: order.len(),
        fold_rules: 0,
        lemma_rows: 0,
        proved: 0,
        timed_out: 0,
        all_int: 0,
        one_type: 0,
        bool_instances: 0,
        bool_only: 0,
        with_ground_eval: 0,
    };
    let mut fold_rules: BTreeSet<&str> = BTreeSet::new();
    for row in rows {
        let rule_scopes = &scopes[row.rule.as_str()];
        if rule_scopes.contains("int") && rule_scopes.iter().any(|s| INT_TYPES.contains(s)) {
            return Err(format!("{}: scope `int` beside one integer type", row.rule));
        }
        let is_fold = row.rule.starts_with("fold_");
        if is_fold != (row.kind == "fold") || is_fold != row.lemma.is_none() {
            return Err(format!(
                "{} at {}: a `fold_*` rule, a `fold` kind and a row with no lemma are one thing",
                row.rule, row.scope
            ));
        }
        let Some(lemma) = &row.lemma else {
            fold_rules.insert(&row.rule);
            continue;
        };
        let expected = lemma_name(&row.rule, &row.scope, rule_scopes);
        if *lemma != expected {
            return Err(format!(
                "{} at {}: the lemma is named {lemma}, not {expected}",
                row.rule, row.scope
            ));
        }
        census.lemma_rows += 1;
        match (row.timed_out(), declared.contains_key(lemma)) {
            (true, true) => return Err(format!("{lemma}: listed in TIMED_OUT and declared")),
            (true, false) => {
                census.timed_out += 1;
                continue;
            }
            (false, false) => {
                return Err(format!(
                    "{lemma}: no lemma module declares it ({} at {} would be unproved; a lemma \
                     that cannot be proved is listed in TIMED_OUT, never dropped)",
                    row.rule, row.scope
                ))
            }
            (false, true) => census.proved += 1,
        }
        match row.scope.as_str() {
            "int" => census.all_int += 1,
            "bool" if rule_scopes.len() == 1 => census.bool_only += 1,
            "bool" => census.bool_instances += 1,
            _ => census.one_type += 1,
        }
        if row.kind == "eval" {
            census.with_ground_eval += 1;
        }
    }
    census.fold_rules = fold_rules.len();
    if (census.rules, census.fold_rules, census.lemma_rows) != (RULES, FOLD_RULES, LEMMA_ROWS) {
        return Err(format!(
            "the rule set is {RULES} rules, {FOLD_RULES} of them fold rules, with {LEMMA_ROWS} \
             lemma rows; LEMMAS has {}, {} and {}",
            census.rules, census.fold_rules, census.lemma_rows
        ));
    }
    Ok(census)
}

/// The constant at the head of a statement's conclusion, its binders
/// stripped.
fn conclusion_head(statement: &Expr) -> Option<String> {
    let mut body = statement.strip_mdata();
    while let ExprKind::Pi(_, _, inner) = body.kind() {
        body = inner.strip_mdata();
    }
    match body.get_app_fn().strip_mdata().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// `rows` against the replayed environment. Every proved row's lemma is a
/// theorem whose type is the row's statement term for term, and the entry
/// accepts its record term for the statement at every type of the row's
/// scope; a timed-out row's lemma is absent; and every theorem the lemma
/// modules declare that concludes `EqsatRule.Sound` is a proved row's lemma.
/// Returns the number of acceptances.
pub(super) fn check_rows_against_kernel(
    k: &ReferenceKernel,
    family_dir: &Path,
    rows: &[LemmaRow],
) -> Result<usize, String> {
    let env = k.environment();
    let mut proved: BTreeSet<&str> = BTreeSet::new();
    let mut acceptances = 0usize;
    for row in rows {
        let Some(lemma) = &row.lemma else {
            continue;
        };
        let constant = env.get_const(&n(lemma));
        if row.timed_out() {
            if constant.is_some() {
                return Err(format!(
                    "{lemma}: listed in TIMED_OUT and in the environment"
                ));
            }
            continue;
        }
        let constant = constant
            .ok_or_else(|| format!("{lemma}: not a constant of the replayed environment"))?;
        if constant.kind != ConstantKind::Theorem || constant.value.is_none() {
            return Err(format!("{lemma}: is a {:?}, not a theorem", constant.kind));
        }
        if !constant.level_params.is_empty() {
            return Err(format!("{lemma}: has universe parameters"));
        }
        let statement = row.statement();
        if *constant.type_.strip_mdata() != statement {
            return Err(format!(
                "{lemma}: does not state its rule at its scope.\n  states   {}\n  required {}",
                constant.type_, statement
            ));
        }
        for (ty, instance, term) in row.instances(lemma) {
            accepted(
                k,
                &instance,
                &term,
                &format!("{} at {ty} by {lemma}", row.rule),
            );
            acceptances += 1;
        }
        proved.insert(lemma);
    }
    let mut sound_theorems = 0usize;
    for module in LEMMA_MODULES {
        for (name, _) in module_constants(family_dir, module) {
            let Some(constant) = env.get_const(&name) else {
                continue;
            };
            if constant.kind != ConstantKind::Theorem
                || conclusion_head(&constant.type_).as_deref() != Some("EqsatRule.Sound")
            {
                continue;
            }
            let name = name.to_string();
            if !proved.contains(name.as_str()) {
                return Err(format!(
                    "{name}: a Sound theorem of {module} that no row of LEMMAS names"
                ));
            }
            sound_theorems += 1;
        }
    }
    if sound_theorems != proved.len() {
        return Err(format!(
            "{} proved rows, {sound_theorems} Sound theorems in the lemma modules",
            proved.len()
        ));
    }
    Ok(acceptances)
}

/// The table's own refusals, on the real rows and the replayed environment:
/// a lemma taken out of its module's constants is not there to check, and
/// the comparisons refuse a row moved to another rule, a row moved to another
/// scope, a row with no theorem and a theorem with no row.
pub(super) fn lemma_table_controls(k: &ReferenceKernel, family_dir: &Path, rows: &[LemmaRow]) {
    let position = |rule: &str, scope: &str| {
        rows.iter()
            .position(|row| row.rule == rule && row.scope == scope)
            .unwrap_or_else(|| panic!("LEMMAS has {rule} at {scope}"))
    };
    let refused = |what: &str, edited: &[LemmaRow], needle: &str| {
        let why = check_rows_against_kernel(k, family_dir, edited)
            .expect_err(&format!("{what} must be refused"));
        assert!(
            why.contains(needle),
            "{what}: refused for another reason: {why}"
        );
    };
    // Another rule's lemma under this row's name: `sub_zero`'s row naming
    // `add_zero`'s lemma. Both statements are true; they are different terms.
    let mut swapped = rows.to_vec();
    swapped[position("sub_zero", "int")].lemma = Some("EqsatInt.add_zero".to_owned());
    refused("another rule's lemma", &swapped, "does not state its rule");
    // A bool-only lemma for its rule at an integer type: the entry accepts it
    // (the statement does not carry the domain), the table does not.
    let mut widened = rows.to_vec();
    widened[position("band_true", "bool")].scope = "u64".to_owned();
    refused(
        "a lemma at another scope",
        &widened,
        "does not state its rule",
    );
    // A row whose lemma no module declares.
    let mut absent = rows.to_vec();
    absent[position("add_zero", "int")].lemma = Some("EqsatInt.no_such_lemma".to_owned());
    refused("a row with no theorem", &absent, "not a constant");
    // A lemma whose row is gone.
    let mut dropped = rows.to_vec();
    dropped.remove(position("add_zero", "int"));
    refused("a theorem with no row", &dropped, "no row of LEMMAS names");
    // A satisfiability lemma is not a Sound lemma.
    let mut sat = rows.to_vec();
    sat[position("rotl_full", "int")].lemma = Some("EqsatInt.rotl_full_sat".to_owned());
    refused(
        "a Satisfiable lemma for a Sound row",
        &sat,
        "does not state its rule",
    );
}
