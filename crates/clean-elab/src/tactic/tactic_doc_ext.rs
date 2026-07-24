// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tactic documentation: syntax docs, dependency tracking, goal-pattern
//! suggestions, multi-format rendering, version tracking, and statistics.

use std::cell::Cell;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ExtTacticCategory {
    Basic,
    Advanced,
    Arithmetic,
    Rewriting,
    Automation,
    Logic,
    Search,
    Combinator,
    Closing,
    Custom,
}

impl ExtTacticCategory {
    #[must_use]
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Basic => "Basic",
            Self::Advanced => "Advanced",
            Self::Arithmetic => "Arithmetic",
            Self::Rewriting => "Rewriting",
            Self::Automation => "Automation",
            Self::Logic => "Logic",
            Self::Search => "Search",
            Self::Combinator => "Combinator",
            Self::Closing => "Closing",
            Self::Custom => "Custom",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DocFormat {
    Markdown,
    PlainText,
    Structured,
}

#[derive(Debug, Clone)]
pub(crate) struct TacticExample {
    pub(crate) description: String,
    pub(crate) code: String,
}

#[derive(Debug, Clone)]
pub(crate) struct TacticSyntaxDoc {
    pub(crate) pattern: String,
    pub(crate) accepts_with_clause: bool,
    pub(crate) accepts_at: bool,
    pub(crate) modifiers: Vec<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct ExtTacticDoc {
    pub(crate) name: String,
    pub(crate) category: ExtTacticCategory,
    pub(crate) description: String,
    pub(crate) syntax: TacticSyntaxDoc,
    pub(crate) examples: Vec<TacticExample>,
    pub(crate) see_also: Vec<String>,
    pub(crate) dependencies: Vec<String>,
    pub(crate) since_version: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum GoalPattern {
    Equality,
    False,
    Conjunction,
    Disjunction,
    Forall,
    Exists,
    NumericRelation,
    NatOrInt,
    Negation,
    Other,
}

impl GoalPattern {
    #[must_use]
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Equality => "Equality",
            Self::False => "False",
            Self::Conjunction => "Conjunction",
            Self::Disjunction => "Disjunction",
            Self::Forall => "Forall",
            Self::Exists => "Exists",
            Self::NumericRelation => "NumericRelation",
            Self::NatOrInt => "NatOrInt",
            Self::Negation => "Negation",
            Self::Other => "Other",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DocStats {
    pub(crate) total_tactics: usize,
    pub(crate) category_counts: HashMap<ExtTacticCategory, usize>,
    pub(crate) total_examples: usize,
    pub(crate) total_searches: usize,
}

pub(crate) struct ExtTacticDocRegistry {
    docs: HashMap<String, ExtTacticDoc>,
    goal_suggestions: HashMap<GoalPattern, Vec<String>>,
    search_count: Cell<usize>,
}

impl ExtTacticDocRegistry {
    #[must_use]
    pub(crate) fn new() -> Self {
        let mut docs = HashMap::new();
        for doc in build_all_docs() {
            docs.insert(doc.name.clone(), doc);
        }
        Self {
            docs,
            goal_suggestions: build_goal_suggestions(),
            search_count: Cell::new(0),
        }
    }

    #[must_use]
    pub(crate) fn get(&self, name: &str) -> Option<&ExtTacticDoc> {
        self.docs.get(name)
    }

    #[must_use]
    pub(crate) fn by_category(&self, cat: ExtTacticCategory) -> Vec<&ExtTacticDoc> {
        self.docs.values().filter(|d| d.category == cat).collect()
    }

    /// Search by keyword across name, description, and example code (case-insensitive).
    #[must_use]
    pub(crate) fn search_keyword(&self, keyword: &str) -> Vec<&ExtTacticDoc> {
        self.search_count.set(self.search_count.get() + 1);
        let kw = keyword.to_lowercase();
        self.docs
            .values()
            .filter(|d| {
                d.name.to_lowercase().contains(&kw)
                    || d.description.to_lowercase().contains(&kw)
                    || d.examples
                        .iter()
                        .any(|e| e.code.to_lowercase().contains(&kw))
            })
            .collect()
    }

    /// Suggest tactics for a given goal pattern.
    #[must_use]
    pub(crate) fn suggest_for_goal(&self, pattern: GoalPattern) -> Vec<&ExtTacticDoc> {
        self.search_count.set(self.search_count.get() + 1);
        self.goal_suggestions
            .get(&pattern)
            .map(|names| {
                names
                    .iter()
                    .filter_map(|n| self.docs.get(n.as_str()))
                    .collect()
            })
            .unwrap_or_default()
    }

    #[must_use]
    pub(crate) fn dependencies(&self, name: &str) -> Option<&[String]> {
        self.docs.get(name).map(|d| d.dependencies.as_slice())
    }

    #[must_use]
    pub(crate) fn reverse_dependencies(&self, name: &str) -> Vec<&str> {
        self.docs
            .values()
            .filter(|d| d.dependencies.iter().any(|dep| dep == name))
            .map(|d| d.name.as_str())
            .collect()
    }

    #[must_use]
    pub(crate) fn all_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.docs.keys().map(|s| s.as_str()).collect();
        names.sort_unstable();
        names
    }

    #[must_use]
    pub(crate) fn format_doc(&self, name: &str, fmt: DocFormat) -> Option<String> {
        let doc = self.docs.get(name)?;
        Some(match fmt {
            DocFormat::Markdown => fmt_markdown(doc),
            DocFormat::PlainText => fmt_plain(doc),
            DocFormat::Structured => fmt_structured(doc),
        })
    }

    #[must_use]
    pub(crate) fn stats(&self) -> DocStats {
        let mut category_counts: HashMap<ExtTacticCategory, usize> = HashMap::new();
        let mut total_examples = 0usize;
        for doc in self.docs.values() {
            *category_counts.entry(doc.category).or_insert(0) += 1;
            total_examples += doc.examples.len();
        }
        DocStats {
            total_tactics: self.docs.len(),
            category_counts,
            total_examples,
            total_searches: self.search_count.get(),
        }
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.docs.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.docs.is_empty()
    }
}

// -- Formatting helpers ------------------------------------------------------

fn fmt_markdown(d: &ExtTacticDoc) -> String {
    let mut o = format!(
        "## {}\n\n**Category:** {}  \n**Since:** v{}  \n**Syntax:** `{}`\n\n{}\n",
        d.name,
        d.category.label(),
        d.since_version,
        d.syntax.pattern,
        d.description
    );
    if !d.syntax.modifiers.is_empty() {
        o.push_str(&format!(
            "\n**Modifiers:** {}\n",
            d.syntax.modifiers.join(", ")
        ));
    }
    if !d.examples.is_empty() {
        o.push_str("\n### Examples\n\n");
        for ex in &d.examples {
            o.push_str(&format!(
                "*{}*\n```lean\n{}\n```\n\n",
                ex.description, ex.code
            ));
        }
    }
    if !d.dependencies.is_empty() {
        o.push_str(&format!(
            "**Uses internally:** {}\n",
            d.dependencies.join(", ")
        ));
    }
    if !d.see_also.is_empty() {
        o.push_str(&format!("\n**See also:** {}\n", d.see_also.join(", ")));
    }
    o
}

fn fmt_plain(d: &ExtTacticDoc) -> String {
    let mut o = format!(
        "{}\n  Category: {}\n  Since: v{}\n  Syntax: {}\n  {}\n",
        d.name,
        d.category.label(),
        d.since_version,
        d.syntax.pattern,
        d.description
    );
    for ex in &d.examples {
        o.push_str(&format!("  Example: {}: {}\n", ex.description, ex.code));
    }
    if !d.dependencies.is_empty() {
        o.push_str(&format!("  Uses: {}\n", d.dependencies.join(", ")));
    }
    if !d.see_also.is_empty() {
        o.push_str(&format!("  See also: {}\n", d.see_also.join(", ")));
    }
    o
}

fn fmt_structured(d: &ExtTacticDoc) -> String {
    let esc = |s: &str| s.replace('"', "\\\"");
    let exs: Vec<String> = d
        .examples
        .iter()
        .map(|e| {
            format!(
                "{{\"description\":\"{}\",\"code\":\"{}\"}}",
                esc(&e.description),
                esc(&e.code)
            )
        })
        .collect();
    let strs = |v: &[String]| {
        v.iter()
            .map(|s| format!("\"{}\"", s))
            .collect::<Vec<_>>()
            .join(",")
    };
    format!(
        "{{\"name\":\"{}\",\"category\":\"{}\",\"since\":\"{}\",\"syntax\":\"{}\",\
        \"description\":\"{}\",\"examples\":[{}],\"dependencies\":[{}],\"see_also\":[{}]}}",
        d.name,
        d.category.label(),
        d.since_version,
        esc(&d.syntax.pattern),
        esc(&d.description),
        exs.join(","),
        strs(&d.dependencies),
        strs(&d.see_also)
    )
}

// -- Data construction helpers -----------------------------------------------

fn mk(
    name: &str,
    cat: ExtTacticCategory,
    desc: &str,
    pat: &str,
    with_cl: bool,
    at: bool,
    mods: &[&str],
    exs: &[(&str, &str)],
    see: &[&str],
    deps: &[&str],
    ver: &str,
) -> ExtTacticDoc {
    ExtTacticDoc {
        name: name.into(),
        category: cat,
        description: desc.into(),
        syntax: TacticSyntaxDoc {
            pattern: pat.into(),
            accepts_with_clause: with_cl,
            accepts_at: at,
            modifiers: mods.iter().map(|s| (*s).into()).collect(),
        },
        examples: exs
            .iter()
            .map(|(d, c)| TacticExample {
                description: (*d).into(),
                code: (*c).into(),
            })
            .collect(),
        see_also: see.iter().map(|s| (*s).into()).collect(),
        dependencies: deps.iter().map(|s| (*s).into()).collect(),
        since_version: ver.into(),
    }
}

fn build_all_docs() -> Vec<ExtTacticDoc> {
    let mut docs = Vec::with_capacity(48);
    docs.extend(docs_basic());
    docs.extend(docs_rewriting());
    docs.extend(docs_logic());
    docs.extend(docs_arithmetic());
    docs.extend(docs_search());
    docs.extend(docs_combinator());
    docs.extend(docs_closing());
    docs.extend(docs_advanced());
    docs.extend(docs_automation());
    docs
}

fn docs_basic() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Basic;
    vec![
        mk(
            "intro",
            Basic,
            "Introduce a binder from the goal.",
            "intro (name : Name)",
            false,
            false,
            &[],
            &[("Introduce one", "intro h"), ("Multiple", "intro x y z")],
            &["intros", "apply"],
            &[],
            "0.1.0",
        ),
        mk(
            "intros",
            Basic,
            "Introduce all leading binders.",
            "intros (names : Name*)",
            false,
            false,
            &[],
            &[("All", "intros"), ("Named", "intros a b c")],
            &["intro"],
            &["intro"],
            "0.1.0",
        ),
        mk(
            "exact",
            Basic,
            "Close the goal with an exact proof term.",
            "exact (e : term)",
            false,
            false,
            &[],
            &[
                ("Hypothesis", "exact h"),
                ("Lemma", "exact Nat.zero_lt_succ n"),
            ],
            &["apply", "assumption"],
            &[],
            "0.1.0",
        ),
        mk(
            "apply",
            Basic,
            "Apply a function or lemma to the goal.",
            "apply (e : term)",
            false,
            false,
            &[],
            &[
                ("Lemma", "apply Nat.succ_lt_succ"),
                ("Ctor", "apply And.intro"),
            ],
            &["exact", "constructor"],
            &[],
            "0.1.0",
        ),
        mk(
            "assumption",
            Basic,
            "Close goal using a matching hypothesis.",
            "assumption",
            false,
            false,
            &[],
            &[("Basic", "assumption")],
            &["exact", "trivial"],
            &[],
            "0.1.0",
        ),
        mk(
            "constructor",
            Basic,
            "Apply the first applicable constructor.",
            "constructor",
            false,
            false,
            &[],
            &[("Basic", "constructor")],
            &["apply", "left", "right", "split"],
            &[],
            "0.1.0",
        ),
    ]
}

fn docs_rewriting() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Rewriting;
    vec![
        mk(
            "rw",
            Rewriting,
            "Rewrite the goal using equalities.",
            "rw [rules : term*]",
            false,
            true,
            &[],
            &[("Single", "rw [h]"), ("Bidirectional", "rw [<- h1, h2]")],
            &["simp", "unfold", "conv"],
            &[],
            "0.1.0",
        ),
        mk(
            "simp",
            Rewriting,
            "Simplify using the simp lemma set.",
            "simp [lemmas : term*]",
            false,
            true,
            &["only"],
            &[("Default", "simp"), ("Only", "simp only [Nat.add_zero]")],
            &["simp_all", "dsimp", "norm_num"],
            &["rw"],
            "0.1.0",
        ),
        mk(
            "unfold",
            Rewriting,
            "Unfold named constants in the goal.",
            "unfold (names : Name*)",
            false,
            true,
            &[],
            &[("Unfold", "unfold List.length")],
            &["delta", "simp", "dsimp"],
            &[],
            "0.1.0",
        ),
        mk(
            "dsimp",
            Rewriting,
            "Definitional simplification.",
            "dsimp [lemmas : term*]",
            false,
            true,
            &["only"],
            &[("Default", "dsimp"), ("Only", "dsimp only [List.map]")],
            &["simp", "unfold"],
            &[],
            "0.1.0",
        ),
    ]
}

fn docs_logic() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Logic;
    vec![
        mk(
            "cases",
            Logic,
            "Case analysis on an inductive type.",
            "cases (e : term)",
            true,
            false,
            &[],
            &[
                ("Simple", "cases h"),
                ("Patterns", "cases n with | zero => ..."),
            ],
            &["rcases", "induction", "by_cases"],
            &[],
            "0.1.0",
        ),
        mk(
            "contradiction",
            Logic,
            "Close goal via contradictory hypotheses.",
            "contradiction",
            false,
            false,
            &[],
            &[("Basic", "contradiction")],
            &["exfalso", "absurd", "by_contra"],
            &[],
            "0.1.0",
        ),
        mk(
            "by_contra",
            Logic,
            "Prove by contradiction.",
            "by_contra (h : Name?)",
            false,
            false,
            &[],
            &[("Named", "by_contra h"), ("Anon", "by_contra")],
            &["contradiction", "exfalso"],
            &[],
            "0.1.0",
        ),
        mk(
            "split",
            Logic,
            "Split a conjunction into two subgoals.",
            "split",
            false,
            false,
            &[],
            &[("Basic", "split")],
            &["constructor", "left", "right"],
            &["constructor"],
            "0.1.0",
        ),
        mk(
            "left",
            Logic,
            "Prove left disjunction alternative.",
            "left",
            false,
            false,
            &[],
            &[("Basic", "left")],
            &["right", "split"],
            &["constructor"],
            "0.1.0",
        ),
        mk(
            "right",
            Logic,
            "Prove right disjunction alternative.",
            "right",
            false,
            false,
            &[],
            &[("Basic", "right")],
            &["left", "split"],
            &["constructor"],
            "0.1.0",
        ),
        mk(
            "exfalso",
            Logic,
            "Change the goal to False.",
            "exfalso",
            false,
            false,
            &[],
            &[("Basic", "exfalso")],
            &["contradiction", "absurd", "by_contra"],
            &[],
            "0.1.0",
        ),
        mk(
            "tauto",
            Logic,
            "Prove propositional tautologies.",
            "tauto",
            false,
            false,
            &[],
            &[("Basic", "tauto")],
            &["decide", "itauto"],
            &["intro", "cases", "constructor", "assumption"],
            "0.1.0",
        ),
    ]
}

fn docs_arithmetic() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Arithmetic;
    vec![
        mk(
            "omega",
            Arithmetic,
            "Solve linear arithmetic over Nat/Int.",
            "omega",
            false,
            false,
            &[],
            &[("Basic", "omega")],
            &["linarith", "norm_num", "ring"],
            &[],
            "0.1.0",
        ),
        mk(
            "cert_mathverse",
            Arithmetic,
            "Normalize project certificate arithmetic, coerce supported Nat goals, then call omega.",
            "cert_mathverse",
            false,
            false,
            &[],
            &[("Basic", "cert_mathverse")],
            &["cert_simp", "omega", "linarith", "norm_num"],
            &["cert_simp", "omega"],
            "0.2.0",
        ),
        mk(
            "cert_simp",
            Arithmetic,
            "Simplify certificate/list/SAT/PB/NN verification arithmetic wrappers.",
            "cert_simp",
            false,
            false,
            &[],
            &[("Basic", "cert_simp")],
            &["cert_mathverse", "simp", "simp_all"],
            &["simp", "simp_all"],
            "0.2.0",
        ),
        mk(
            "norm_num",
            Arithmetic,
            "Normalize numeric expressions.",
            "norm_num [ext : term*]",
            false,
            true,
            &[],
            &[
                ("Basic", "norm_num"),
                ("Ext", "norm_num [Nat.prime_def_lt_prime]"),
            ],
            &["omega", "ring", "simp"],
            &["simp"],
            "0.1.0",
        ),
        mk(
            "ring",
            Arithmetic,
            "Prove ring equalities by normalization.",
            "ring",
            false,
            false,
            &[],
            &[("Basic", "ring")],
            &["ring_nf", "linarith", "norm_num"],
            &[],
            "0.1.0",
        ),
        mk(
            "linarith",
            Arithmetic,
            "Prove linear arithmetic inequalities.",
            "linarith [extra : term*]",
            false,
            false,
            &["only"],
            &[("Basic", "linarith"), ("Extra", "linarith [h1, h2]")],
            &["omega", "nlinarith", "norm_num"],
            &[],
            "0.1.0",
        ),
        mk(
            "nlinarith",
            Arithmetic,
            "Prove nonlinear arithmetic goals.",
            "nlinarith [extra : term*]",
            false,
            false,
            &[],
            &[
                ("Basic", "nlinarith"),
                ("Witness", "nlinarith [sq_nonneg x]"),
            ],
            &["linarith", "polyrith", "positivity"],
            &["linarith"],
            "0.2.0",
        ),
        mk(
            "field_simp",
            Arithmetic,
            "Clear denominators in field expressions.",
            "field_simp [l : term*]",
            false,
            true,
            &[],
            &[("Basic", "field_simp")],
            &["ring", "norm_num", "simp"],
            &["simp"],
            "0.2.0",
        ),
    ]
}

fn docs_search() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Search;
    vec![
        mk(
            "aesop",
            Search,
            "Automated proof search using rule sets.",
            "aesop",
            false,
            false,
            &[],
            &[("Basic", "aesop")],
            &["decide", "library_search", "tauto"],
            &["simp", "intro", "apply", "assumption", "constructor"],
            "0.2.0",
        ),
        mk(
            "decide",
            Search,
            "Solve decidable propositions by kernel reduction.",
            "decide",
            false,
            false,
            &[],
            &[("Basic", "decide")],
            &["native_decide", "omega", "tauto"],
            &[],
            "0.1.0",
        ),
        mk(
            "library_search",
            Search,
            "Search the environment for a closing lemma.",
            "library_search",
            false,
            false,
            &[],
            &[("Basic", "library_search")],
            &["aesop", "exact?", "apply?"],
            &["exact", "apply"],
            "0.2.0",
        ),
    ]
}

fn docs_combinator() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Combinator;
    vec![
        mk(
            "repeat",
            Combinator,
            "Repeatedly apply a tactic until it fails.",
            "repeat (tac : tactic)",
            false,
            false,
            &[],
            &[("Intro", "repeat intro _")],
            &["try", "all_goals", "any_goals"],
            &[],
            "0.1.0",
        ),
        mk(
            "try",
            Combinator,
            "Try a tactic; succeed even if it fails.",
            "try (tac : tactic)",
            false,
            false,
            &[],
            &[("Basic", "try assumption")],
            &["repeat", "first", "all_goals"],
            &[],
            "0.1.0",
        ),
        mk(
            "all_goals",
            Combinator,
            "Apply tactic to every open goal.",
            "all_goals (tac : tactic)",
            false,
            false,
            &[],
            &[("Simp all", "all_goals simp")],
            &["any_goals", "focus", "try"],
            &[],
            "0.1.0",
        ),
        mk(
            "focus",
            Combinator,
            "Apply tactic to the first goal only.",
            "focus (tac : tactic)",
            false,
            false,
            &[],
            &[("Focus", "focus (intro h; exact h)")],
            &["all_goals", "swap", "rotate"],
            &[],
            "0.1.0",
        ),
    ]
}

fn docs_closing() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Closing;
    vec![
        mk(
            "rfl",
            Closing,
            "Close the goal by reflexivity.",
            "rfl",
            false,
            false,
            &[],
            &[("Basic", "rfl")],
            &["exact rfl", "symm"],
            &[],
            "0.1.0",
        ),
        mk(
            "trivial",
            Closing,
            "Close simple goals.",
            "trivial",
            false,
            false,
            &[],
            &[("Basic", "trivial")],
            &["assumption", "rfl", "decide"],
            &["rfl", "assumption", "contradiction", "constructor"],
            "0.1.0",
        ),
        mk(
            "sorry",
            Closing,
            "Admit the goal without proof (unsound).",
            "sorry",
            false,
            false,
            &[],
            &[("Basic", "sorry")],
            &["admit"],
            &[],
            "0.1.0",
        ),
    ]
}

fn docs_advanced() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Advanced;
    vec![
        mk(
            "conv",
            Advanced,
            "Enter conversion mode for targeted rewriting.",
            "conv => (conv_tactics)",
            false,
            false,
            &["in"],
            &[("Rewrite", "conv => rw [h]")],
            &["rw", "simp", "change"],
            &["rw"],
            "0.1.0",
        ),
        mk(
            "calc",
            Advanced,
            "Structured proof by transitive chain.",
            "calc a R b := ... _ R c := ...",
            false,
            false,
            &[],
            &[("Chain", "calc x = y := by rfl\n  _ < z := by linarith")],
            &["trans", "conv"],
            &[],
            "0.1.0",
        ),
        mk(
            "induction",
            Advanced,
            "Structural induction on a variable.",
            "induction (e : term)",
            true,
            false,
            &[],
            &[("Basic", "induction n with | zero => ... | succ n ih => ...")],
            &["cases", "rcases"],
            &[],
            "0.1.0",
        ),
        mk(
            "have",
            Advanced,
            "Introduce an intermediate assertion.",
            "have (h : Name) : type := proof",
            false,
            false,
            &[],
            &[("Basic", "have h : n > 0 := by omega")],
            &["let", "suffices", "show"],
            &[],
            "0.1.0",
        ),
        mk(
            "revert",
            Advanced,
            "Move hypotheses back into the goal.",
            "revert (names : Name*)",
            false,
            false,
            &[],
            &[("Basic", "revert h")],
            &["intro", "generalize", "clear"],
            &[],
            "0.1.0",
        ),
    ]
}

fn docs_automation() -> Vec<ExtTacticDoc> {
    use ExtTacticCategory::Automation;
    vec![
        mk(
            "blast",
            Automation,
            "Aggressive automated proof search.",
            "blast",
            false,
            false,
            &[],
            &[("Basic", "blast")],
            &["aesop", "tauto", "simp"],
            &["simp", "intro", "apply", "cases", "contradiction", "omega"],
            "0.3.0",
        ),
        mk(
            "grind",
            Automation,
            "Extended automation with configurable strategies.",
            "grind",
            false,
            false,
            &[],
            &[("Basic", "grind")],
            &["blast", "aesop", "decide"],
            &["simp", "omega", "norm_num", "ring", "linarith"],
            "0.3.0",
        ),
        mk(
            "itauto",
            Automation,
            "Intuitionistic tautology prover.",
            "itauto",
            false,
            false,
            &[],
            &[("Basic", "itauto")],
            &["tauto", "decide"],
            &["intro", "cases", "constructor", "assumption"],
            "0.2.0",
        ),
    ]
}

fn build_goal_suggestions() -> HashMap<GoalPattern, Vec<String>> {
    use GoalPattern::*;
    let mut m = HashMap::new();
    let v = |s: &[&str]| s.iter().map(|x| (*x).into()).collect();
    m.insert(
        Equality,
        v(&[
            "rfl",
            "rw",
            "simp",
            "ring",
            "cert_mathverse",
            "omega",
            "calc",
        ]),
    );
    m.insert(
        False,
        v(&[
            "contradiction",
            "exfalso",
            "tauto",
            "cert_mathverse",
            "omega",
        ]),
    );
    m.insert(Conjunction, v(&["split", "constructor", "tauto"]));
    m.insert(Disjunction, v(&["left", "right", "tauto"]));
    m.insert(Forall, v(&["intro", "intros", "induction"]));
    m.insert(
        Exists,
        v(&["exact", "constructor", "cert_mathverse", "omega"]),
    );
    m.insert(
        NumericRelation,
        v(&[
            "cert_mathverse",
            "omega",
            "linarith",
            "norm_num",
            "nlinarith",
            "ring",
        ]),
    );
    m.insert(
        NatOrInt,
        v(&["cert_mathverse", "omega", "norm_num", "ring", "induction"]),
    );
    m.insert(Negation, v(&["by_contra", "intro", "tauto"]));
    m.insert(Other, v(&["simp", "aesop", "trivial", "blast"]));
    m
}
