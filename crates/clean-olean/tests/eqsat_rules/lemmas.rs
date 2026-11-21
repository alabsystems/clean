// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lemma table of the `eqsat_rules` gate: the family's `LEMMAS` file names,
//! for every rule of trust-cg's two rule files ([`RULE_SETS`]: the integer
//! rule set and the saturation tier's) and every scope of its domain, the
//! lemma that scope needs. The gate requires each as a theorem of the replayed
//! environment whose statement is the row's, term for term, on the literal
//! generated from the rule's file, and accepted by the entry at every type of
//! the scope; and it refuses a `Sound` theorem of the lemma modules that no
//! row names. So a lemma that is dropped, renamed, restated or added without
//! its row fails here.
//!
//! The table is keyed by rule name. A name both rule files have
//! ([`SHARED_RULES`]) is one row: the two files give it one literal, its
//! lemma is stated on the first file's, and the entry must accept that lemma
//! for the second file's statement too.
//!
//! The table and the modules of literals are generated files, and the gate
//! pins the bytes of each ([`GENERATED_FILES`]): the kernel binds a lemma to
//! a proposition, not to a literal, so an edit of a literal that keeps the
//! proposition (or changes it together with the proof) is seen here and not
//! there.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_kernel::env::ConstantKind;
use clean_kernel::expr::Expr;
use clean_kernel::{BinderInfo, ExprKind, ReferenceKernel};
use sha2::{Digest, Sha256};

use super::statements::source_theorems;
use super::terms::{accepted, app, c, comm_literal, int_ty, n, refused, sound};
use super::{family_source_dir, hex, lean_tripwire::lean_code_only, module_constants, INT_TYPES};

/// The family's lemma table (`gen_rule_defs.py --lemmas` writes it from
/// trust-cg's rule text).
pub(super) const LEMMAS: &str = include_str!("../fixtures/lean/v4.30.0-rc2/eqsat_rules/LEMMAS");

/// The modules that declare the rule lemmas, all in namespace `EqsatInt`.
pub(super) const LEMMA_MODULES: [&str; 6] = [
    "EqsatIntSample",
    "EqsatIntArith",
    "EqsatIntCmpSelBool",
    "EqsatIntBitwise",
    "EqsatIntNegRot",
    "EqsatTierSInt",
];

/// One rule file of trust-cg `crates/trust-cg-eqsat/rules/` and the module
/// `gen_rule_defs.py` generates from it.
pub(super) struct RuleSet {
    /// The rule file's name; `LEMMAS` and the generated module record its
    /// SHA-256 under this name in their headers.
    pub(super) rule_file: &'static str,
    /// The generated module of the file's literals.
    pub(super) defs_module: &'static str,
    /// The namespace of those literals under `EqsatRule`.
    pub(super) defs_namespace: &'static str,
    /// The rules the file has. The generated module is the list; this makes a
    /// regenerated module that adds or drops a rule a change to this file
    /// too.
    pub(super) rules: usize,
}

/// trust-cg's integer rule set, `integer_identities.rules` (PKG-U2).
pub(super) const INTEGER_SET: RuleSet = RuleSet {
    rule_file: "integer_identities.rules",
    defs_module: "EqsatIntRuleDefs",
    defs_namespace: "Defs",
    rules: 76,
};

/// The rule set of trust-cg's saturation tier, `tier_s_integer.rules`
/// (PKG-U4c).
pub(super) const TIER_S_SET: RuleSet = RuleSet {
    rule_file: "tier_s_integer.rules",
    defs_module: "EqsatTierSRuleDefs",
    defs_namespace: "TierSDefs",
    rules: 10,
};

/// The rule files of the table, in its order: the rows of the first, then
/// the rows of the rules only a later file has.
pub(super) const RULE_SETS: [&RuleSet; 2] = [&INTEGER_SET, &TIER_S_SET];

/// The rule names both rule files have. Each file writes these rules with the
/// same text, so the two generated literals of a name are one term
/// (`EqsatTierSControls.<rule>_is_the_integer_rule`; [`check_shared_rules`]
/// on the sources and [`shared_rule_controls`] on the kernel's own terms).
/// Such a name has one row, and its lemma is stated on the first file's
/// literal.
pub(super) const SHARED_RULES: [&str; 2] = ["add_zero", "mul_one"];

/// The rows of `LEMMAS` whose lemma is not proved, as `(rule, scope)`; the
/// family's README says what was tried for each. Such a lemma must be absent
/// from the sources and from the replayed environment, so a row is either
/// proved or listed here and never both. Empty: every lemma the two rule
/// files need is proved.
pub(super) const TIMED_OUT: [(&str, &str); 0] = [];

/// The files `gen_rule_defs.py` writes from trust-cg's rule text, each with
/// the SHA-256 of its bytes: the three modules of literals and the lemma
/// table. Nothing else in Clean holds a generated literal: the kernel requires
/// a lemma's type by the literal's NAME, the environment digest is not pinned,
/// and the rule text lives in trust-cg, so `gen_rule_defs.py --check` is no
/// lane of this repository. Without these pins a literal edited by hand goes
/// through the gate whenever the family still compiles: with a `const` flag
/// or `var` against `cvar` changed (one proposition, the same proof), or with
/// its proof edited beside it. With them such an edit fails
/// [`check_generated_files`] until the row is re-pinned.
///
/// A pin says the file is the one that was reviewed, not that it is what the
/// rule text generates: that comparison is `gen_rule_defs.py --check` with
/// the rule file at hand, and trust-cg's own, which builds each literal from
/// its parsed rule. Re-pin a row only after regenerating the file, with the
/// rule file's revision in the commit message.
pub(super) const GENERATED_FILES: [(&str, &str); 4] = [
    (
        "EqsatIntRuleDefs.lean",
        "87fa7bfb397908c2d5fe00f8d99d28466910d39787e04e4f7e6a7c3f485bdb8a",
    ),
    (
        "EqsatIntWrongRuleDefs.lean",
        "a81eb8f7ee8de7c4771c33c7beb83d1f87983761e93b4584936d69d78b450cb3",
    ),
    (
        "EqsatTierSRuleDefs.lean",
        "f27f43cee07144aaf4a2dc0aae7c89ee9c68476492a587bea6f2a4c730c476c1",
    ),
    (
        "LEMMAS",
        "2305635f5cd4fb2b3034f83fc69d8cff830b9fd0893f3edeca3112bd9cfd5b47",
    ),
];

/// How the header of every file the generator writes begins to say so: a
/// module's reads ``GENERATED by `gen_rule_defs.py` in this directory`` and
/// the table's ``GENERATED by `gen_rule_defs.py --lemmas` in this directory``.
const GENERATED_MARK: &str = "GENERATED by `gen_rule_defs.py";

/// A generated file's header says so within its first three lines (the
/// generator and the README name the mark further down, and are not
/// generated).
fn says_generated(bytes: &[u8]) -> bool {
    String::from_utf8_lossy(bytes)
        .lines()
        .take(3)
        .any(|line| line.contains(GENERATED_MARK))
}

/// `bytes` are the pinned bytes of the generated file `file`: returns their
/// SHA-256, or why not.
pub(super) fn check_generated_bytes(file: &str, bytes: &[u8]) -> Result<String, String> {
    let pin = GENERATED_FILES
        .iter()
        .find_map(|(name, pin)| (*name == file).then_some(*pin))
        .ok_or_else(|| format!("{file}: not a file of GENERATED_FILES"))?;
    if !says_generated(bytes) {
        return Err(format!(
            "{file}: its first three lines do not carry the generator's mark ({GENERATED_MARK} ...`)"
        ));
    }
    let digest = hex(&Sha256::digest(bytes));
    if digest != pin {
        return Err(format!(
            "{file}: its bytes are {digest}; the gate pins {pin}. A generated file is not \
             edited by hand: regenerate it from trust-cg's rule text (`gen_rule_defs.py`; its \
             `--check` compares a file with the text) and re-pin it in GENERATED_FILES with the \
             rule file's revision in the commit message"
        ));
    }
    Ok(digest)
}

/// Every file of [`GENERATED_FILES`] has its pinned bytes; the table and the
/// generated module of every rule set are among them; and no other file of
/// the family says it is generated, so a further generated module cannot be
/// added without its pin.
pub(super) fn check_generated_files() -> Result<(), String> {
    let dir = family_source_dir();
    let pinned: BTreeSet<&str> = GENERATED_FILES.iter().map(|(file, _)| *file).collect();
    if pinned.len() != GENERATED_FILES.len() {
        return Err("GENERATED_FILES names a file twice".to_owned());
    }
    for (file, _) in GENERATED_FILES {
        let path = dir.join(file);
        let bytes = std::fs::read(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        check_generated_bytes(file, &bytes)?;
    }
    let mut required = vec!["LEMMAS".to_owned()];
    required.extend(
        RULE_SETS
            .iter()
            .map(|set| format!("{}.lean", set.defs_module)),
    );
    for file in required {
        if !pinned.contains(file.as_str()) {
            return Err(format!("{file}: generated, and not in GENERATED_FILES"));
        }
    }
    let entries = std::fs::read_dir(&dir).map_err(|e| format!("read {}: {e}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("read {}: {e}", dir.display()))?;
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if !path.is_file() || pinned.contains(name.as_str()) {
            continue;
        }
        let bytes = std::fs::read(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        if says_generated(&bytes) {
            return Err(format!(
                "{name}: carries the generator's mark ({GENERATED_MARK} ...`) and is not in \
                 GENERATED_FILES"
            ));
        }
    }
    Ok(())
}

/// The table as counted: rule names (76 of the integer rule set and the 8
/// only the saturation tier's has), `fold_*` rules (no lemma) and lemma rows.
/// `LEMMAS` is the list; these make a regenerated table that adds or drops a
/// rule a change to this file too.
const RULES: usize = 84;
const FOLD_RULES: usize = 28;
const LEMMA_ROWS: usize = 64;

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
    /// The namespaces (under `EqsatRule`) of the rule files that have the
    /// rule, in [`RULE_SETS`] order: read from the generated modules, not
    /// from the table. Empty for a rule no generated module defines.
    pub(super) defs: Vec<&'static str>,
}

impl LemmaRow {
    fn timed_out(&self) -> bool {
        TIMED_OUT.contains(&(self.rule.as_str(), self.scope.as_str()))
    }

    /// The rule's literal as generated from one rule file.
    fn rule_def(&self, defs: &str) -> Expr {
        c(&format!("EqsatRule.{defs}.{}", self.rule))
    }

    /// What the lemma's type must be, term for term, with `Defs` the
    /// namespace of the first rule file that has the rule:
    /// `∀ t : SemR.IntTy, Sound Defs.<rule> (STy.int t)` for scope `int`, else
    /// `Sound Defs.<rule> <type>`. `None` for a rule no generated module
    /// defines.
    fn statement(&self) -> Option<Expr> {
        let defs = self.defs.first()?;
        Some(self.statement_on(defs))
    }

    fn statement_on(&self, defs: &str) -> Expr {
        match self.scope.as_str() {
            "int" => Expr::pi(
                BinderInfo::Default,
                c("SemR.IntTy"),
                sound(
                    self.rule_def(defs),
                    app("EqsatRule.STy.int", [Expr::bvar(0)]),
                ),
            ),
            "bool" => sound(self.rule_def(defs), c("EqsatRule.STy.bool")),
            t => sound(self.rule_def(defs), int_ty(t)),
        }
    }

    /// Each rule file that has the rule and each instance type of the scope,
    /// with the statement trust-cg builds there (on that file's literal) and
    /// the record term that proves it: `(namespace, type, statement, term)`.
    fn instances(&self, lemma: &str) -> Vec<(&'static str, String, Expr, Expr)> {
        let mut out = Vec::new();
        for defs in &self.defs {
            match self.scope.as_str() {
                "int" => out.extend(INT_TYPES.iter().map(|t| {
                    (
                        *defs,
                        (*t).to_owned(),
                        sound(self.rule_def(defs), int_ty(t)),
                        app(lemma, [c(&format!("SemR.IntTy.{t}"))]),
                    )
                })),
                _ => out.push((*defs, self.scope.clone(), self.statement_on(defs), c(lemma))),
            }
        }
        out
    }
}

/// The rows of a `LEMMAS` text: `rule scope kind lemma`, one per line; `#`
/// starts a comment line. A malformed row, a repeated `(rule, scope)` and a
/// lemma two rows name are panics, never skipped rows.
pub(super) fn lemma_rows(text: &str) -> Vec<LemmaRow> {
    let mut owners: BTreeMap<String, Vec<&'static str>> = BTreeMap::new();
    for set in RULE_SETS {
        for rule in generated_rules(set) {
            owners.entry(rule).or_default().push(set.defs_namespace);
        }
    }
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
            defs: owners.get(rule).cloned().unwrap_or_default(),
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

fn family_text(file: &str) -> String {
    let path = family_source_dir().join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// The definitions a rule file's generated module makes, in its order: each
/// rule's name and the five lines of its literal (`Rule.mk` with its
/// direction, then the variables, the two sides and the side conditions).
pub(super) fn generated_definitions(set: &RuleSet) -> Vec<(String, Vec<String>)> {
    let module = set.defs_module;
    let text = family_text(&format!("{module}.lean"));
    let code = lean_code_only(&text);
    assert!(
        code.lines()
            .any(|line| line.trim() == format!("namespace EqsatRule.{}", set.defs_namespace)),
        "{module}.lean defines its literals in namespace EqsatRule.{}",
        set.defs_namespace
    );
    let mut definitions = Vec::new();
    let mut lines = code.lines().peekable();
    while let Some(line) = lines.next() {
        let Some(rest) = line.strip_prefix("def ") else {
            continue;
        };
        let name = rest
            .strip_suffix(" : Rule :=")
            .unwrap_or_else(|| panic!("{module}.lean: not a generated definition: {line}"));
        let mut literal = Vec::new();
        while let Some(next) = lines.peek() {
            if next.trim().is_empty() {
                break;
            }
            literal.push(lines.next().expect("peeked").trim().to_owned());
        }
        assert_eq!(
            literal.len(),
            5,
            "{module}.lean: {name}: `Rule.mk` and four fields"
        );
        definitions.push((name.to_owned(), literal));
    }
    definitions
}

/// The rules of a rule file's generated module that have a `where` clause
/// and are not `fold_*` rules: the last line of a generated definition is its
/// `Conds`.
pub(super) fn conditioned_rules(set: &RuleSet) -> BTreeSet<String> {
    let definitions = generated_definitions(set);
    assert_eq!(
        definitions.len(),
        set.rules,
        "{}.lean defines the {} rules of {}",
        set.defs_module,
        set.rules,
        set.rule_file
    );
    let mut rules = BTreeSet::new();
    for (name, literal) in definitions {
        let conds = literal[4].as_str();
        assert!(
            conds == "Conds.nil" || conds.starts_with("(Conds.cons "),
            "{name}: the last field is its Conds: {conds}"
        );
        if conds != "Conds.nil" && !name.starts_with("fold_") {
            rules.insert(name);
        }
    }
    rules
}

/// The rules a rule file's generated module defines, in its order.
pub(super) fn generated_rules(set: &RuleSet) -> Vec<String> {
    generated_definitions(set)
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}

/// The table's rules, in its order: every rule of the first rule file, then
/// the rules only a later file has.
fn table_rules() -> Vec<String> {
    let mut rules: Vec<String> = Vec::new();
    for set in RULE_SETS {
        for rule in generated_rules(set) {
            if !rules.contains(&rule) {
                rules.push(rule);
            }
        }
    }
    rules
}

/// The SHA-256 a generated file's header records for a rule file: the one
/// header line `<rule file>  <64 hex digits>`.
fn recorded_digest(file: &str, rule_file: &str) -> Result<String, String> {
    let text = family_text(file);
    let mut digests = text.lines().filter_map(|line| {
        let line = line.trim().trim_start_matches('#').trim();
        let digest = line.strip_prefix(rule_file)?.trim();
        (digest.len() == 64 && digest.bytes().all(|b| b.is_ascii_hexdigit()))
            .then(|| digest.to_owned())
    });
    match (digests.next(), digests.next()) {
        (Some(digest), None) => Ok(digest),
        (None, _) => Err(format!(
            "{file}: its header records no SHA-256 of {rule_file}"
        )),
        (Some(_), Some(_)) => Err(format!("{file}: its header records {rule_file} twice")),
    }
}

/// `LEMMAS` and a rule file's generated module were read from one rule text:
/// both headers record the rule file's SHA-256, and it is one digest.
/// Returns it.
pub(super) fn rule_file_digest(set: &RuleSet) -> Result<String, String> {
    let module = format!("{}.lean", set.defs_module);
    let table = recorded_digest("LEMMAS", set.rule_file)?;
    let generated = recorded_digest(&module, set.rule_file)?;
    if table != generated {
        return Err(format!(
            "LEMMAS was generated from {} at {table} and {module} at {generated}: regenerate \
             both from one rule text",
            set.rule_file
        ));
    }
    Ok(table)
}

/// The rule names both rule files have are [`SHARED_RULES`], and both files
/// give each one literal, without Lean: a name in both generated modules that
/// is not listed, a listed name one module lacks, and a shared name with two
/// literals are refused. So a rule added to one file under a name the other
/// has, or edited on one side only, cannot go by unseen under the other's
/// row.
pub(super) fn check_shared_rules() -> Result<(), String> {
    let integer: BTreeMap<String, Vec<String>> =
        generated_definitions(&INTEGER_SET).into_iter().collect();
    let tier_s: BTreeMap<String, Vec<String>> =
        generated_definitions(&TIER_S_SET).into_iter().collect();
    let shared: BTreeSet<&str> = integer
        .keys()
        .filter(|rule| tier_s.contains_key(*rule))
        .map(String::as_str)
        .collect();
    let listed: BTreeSet<&str> = SHARED_RULES.into_iter().collect();
    if shared != listed {
        return Err(format!(
            "the rule names {} and {} both have are {shared:?}; SHARED_RULES lists {listed:?}",
            INTEGER_SET.rule_file, TIER_S_SET.rule_file
        ));
    }
    for rule in SHARED_RULES {
        if integer[rule] != tier_s[rule] {
            return Err(format!(
                "{rule}: {} and {} give it two literals; one row cannot state both",
                INTEGER_SET.rule_file, TIER_S_SET.rule_file
            ));
        }
    }
    Ok(())
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
    for set in RULE_SETS {
        let defined = generated_rules(set).len();
        if defined != set.rules {
            return Err(format!(
                "{} has {} rules; {}.lean defines {defined}",
                set.rule_file, set.rules, set.defs_module
            ));
        }
    }
    let generated = table_rules();
    if order != generated {
        return Err(format!(
            "LEMMAS and the generated modules name different rules, or in a different order \
             ({} rows' rules, {} definitions): regenerate them from one rule text",
            order.len(),
            generated.len()
        ));
    }
    check_shared_rules()?;
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
            "the rule files have {RULES} rule names, {FOLD_RULES} of them fold rules, with \
             {LEMMA_ROWS} lemma rows; LEMMAS has {}, {} and {}",
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

/// The statements the entry accepted, counted by the namespace of the rule
/// file whose literal each is about.
pub(super) type Acceptances = BTreeMap<&'static str, usize>;

/// `rows` against the replayed environment. Every proved row's lemma is a
/// theorem whose type is the row's statement term for term, and the entry
/// accepts its record term for the statement at every type of the row's
/// scope, on the literal of every rule file that has the rule; a timed-out
/// row's lemma is absent; and every theorem the lemma modules declare that
/// concludes `EqsatRule.Sound` is a proved row's lemma. Returns the
/// acceptances.
pub(super) fn check_rows_against_kernel(
    k: &ReferenceKernel,
    family_dir: &Path,
    rows: &[LemmaRow],
) -> Result<Acceptances, String> {
    let env = k.environment();
    let mut proved: BTreeSet<&str> = BTreeSet::new();
    let mut acceptances = Acceptances::new();
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
        let statement = row
            .statement()
            .ok_or_else(|| format!("{}: no generated module defines it", row.rule))?;
        if *constant.type_.strip_mdata() != statement {
            return Err(format!(
                "{lemma}: does not state its rule at its scope.\n  states   {}\n  required {}",
                constant.type_, statement
            ));
        }
        for (defs, ty, instance, term) in row.instances(lemma) {
            accepted(
                k,
                &instance,
                &term,
                &format!("{defs}.{} at {ty} by {lemma}", row.rule),
            );
            *acceptances.entry(defs).or_default() += 1;
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
    let mut dropped = rows.to_vec();
    dropped.remove(position("mul_comm", "int"));
    refused(
        "a theorem of the saturation tier with no row",
        &dropped,
        "no row of LEMMAS names",
    );
    // The saturation tier's rules come in pairs that are easy to confuse and
    // all true: the lemma of the same rule with its sides exchanged, and of
    // the same law for the other operator, under this row's name.
    for (rule, other) in [
        ("add_assoc_right", "add_assoc_left"),
        ("mul_assoc_left", "mul_assoc_right"),
        ("distribute", "factor"),
        ("add_comm", "mul_comm"),
        ("add_assoc_right", "mul_assoc_right"),
    ] {
        let mut swapped = rows.to_vec();
        swapped[position(rule, "int")].lemma = Some(format!("EqsatInt.{other}"));
        refused(
            &format!("{other}'s lemma under the row of {rule}"),
            &swapped,
            "does not state its rule",
        );
    }
    // A row read against the other rule file's literals: a rule only the
    // saturation tier's file has is not a literal of the integer rule set,
    // and a rule both have is stated on the first file's literal, not the
    // second's.
    let mut other_file = rows.to_vec();
    other_file[position("add_comm", "int")].defs = vec![INTEGER_SET.defs_namespace];
    refused(
        "a rule of one rule file as a literal of the other",
        &other_file,
        "does not state its rule",
    );
    let mut second_file = rows.to_vec();
    second_file[position("add_zero", "int")].defs = vec![TIER_S_SET.defs_namespace];
    refused(
        "a shared rule's lemma as stated on the second file's literal",
        &second_file,
        "does not state its rule",
    );
    let mut undefined = rows.to_vec();
    undefined[position("factor", "int")].defs = Vec::new();
    refused(
        "a rule no generated module defines",
        &undefined,
        "no generated module defines it",
    );
    // A satisfiability lemma is not a Sound lemma.
    let mut sat = rows.to_vec();
    sat[position("rotl_full", "int")].lemma = Some("EqsatInt.rotl_full_sat".to_owned());
    refused(
        "a Satisfiable lemma for a Sound row",
        &sat,
        "does not state its rule",
    );
}

/// What the entry itself refuses and accepts for the saturation tier's
/// rules: a lemma offered for the statement of the same rule with its sides
/// exchanged, or of the same law for the other operator, is refused beside
/// the accepted control (the statements are true, and different
/// propositions); and the commutativity lemmas are accepted for the literals
/// built here and refused for the commutativity of `sub`, which is false.
pub(super) fn tier_s_kernel_controls(k: &ReferenceKernel) {
    let u64_ = int_ty("u64");
    let at_u64 = |rule: &str| app(&format!("EqsatInt.{rule}"), [c("SemR.IntTy.u64")]);
    let literal = |rule: &str| c(&format!("EqsatRule.{}.{rule}", TIER_S_SET.defs_namespace));
    for (rule, other) in [
        ("add_assoc_right", "add_assoc_left"),
        ("mul_assoc_left", "mul_assoc_right"),
        ("distribute", "factor"),
        ("factor", "distribute"),
        ("add_comm", "mul_comm"),
    ] {
        let statement = sound(literal(rule), u64_.clone());
        accepted(
            k,
            &statement,
            &at_u64(rule),
            &format!("control: {rule} at u64"),
        );
        refused(
            k,
            &statement,
            &at_u64(other),
            &format!("{other}'s lemma for the statement of {rule}"),
        );
    }
    for (op, lemma) in [("add", "add_comm"), ("mul", "mul_comm")] {
        accepted(
            k,
            &sound(comm_literal(op), u64_.clone()),
            &at_u64(lemma),
            &format!("{lemma} at u64 against the literal built here"),
        );
        refused(
            k,
            &sound(comm_literal("sub"), u64_.clone()),
            &at_u64(lemma),
            &format!("{lemma} for the commutativity of sub"),
        );
    }
}

/// A rule name both rule files have, on the replayed environment: the two
/// generated literals are one term (the two definitions have the same value,
/// term for term, not merely the same normal form). So the two statements
/// are one proposition and the one row's lemma proves both, which
/// [`check_rows_against_kernel`] requires of the entry at every type. Which
/// rule file a derivation's rule came from is therefore not a kernel fact;
/// it is the rule digest's and the registry's, in trust-cg.
pub(super) fn shared_rule_controls(k: &ReferenceKernel) {
    let env = k.environment();
    for rule in SHARED_RULES {
        let value = |set: &RuleSet| {
            let name = format!("EqsatRule.{}.{rule}", set.defs_namespace);
            env.get_const(&n(&name))
                .and_then(|constant| constant.value.clone())
                .unwrap_or_else(|| panic!("{name}: a definition of the replayed environment"))
        };
        assert!(
            value(&INTEGER_SET) == value(&TIER_S_SET),
            "{rule}: the two rule files' literals are one term"
        );
    }
    // A control on the comparison: two rules of one file are two terms.
    let value = |rule: &str| {
        env.get_const(&n(&format!("EqsatRule.TierSDefs.{rule}")))
            .and_then(|constant| constant.value.clone())
            .unwrap_or_else(|| panic!("TierSDefs.{rule}: a definition"))
    };
    assert!(
        value("add_assoc_right") != value("add_assoc_left"),
        "a rule and the same rule with its sides exchanged are two terms"
    );
}
