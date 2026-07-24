// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean auto premise` — top-k premise shortlist for a goal type string.
//!
//! Purpose: agents searching for premises to use in proofs currently grep the
//! codebase blindly (`git grep "Nat.zero_le"`). For our whitelist of ~175
//! declarations (42 Theorems + ~130 axioms registered by
//! `Environment::with_prelude()`), this CLI ranks candidate premises by a
//! cheap hybrid of head-symbol match + token Jaccard overlap — no kernel
//! `Expr` construction required from the caller.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md` (CLI surface)
//! and issue #3600 (this verb).
//!
//! Sibling of `clean auto prove` under the same `auto` aggregator so future
//! automation verbs (`auto smt`, `auto atp`) can drop in without reshaping
//! the top-level clap tree. Part of Epic #3436.

use std::time::Instant;

use clap::{Args, ValueEnum};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_kernel::{
    env::gamma_crown_verify::{init_conjecture, CONJECTURE_IDS},
    ConstantKind, Environment, ProofQuality,
};

// -- Arguments ----------------------------------------------------------------

/// Classification filter for `--classification`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum PremiseClassification {
    /// Return every premise regardless of axiom dependencies.
    #[default]
    All,
    /// Only return Theorems with zero domain-specific axiom dependencies
    /// (`ProofQuality::Constructive`).
    Constructive,
}

/// Environment indexed by `clean auto premise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum PremiseEnvironment {
    /// Default kernel prelude.
    #[default]
    Prelude,
    /// Gamma-Crown / NNVerify conjecture environments.
    #[value(name = "gamma-crown", alias = "nn-verify")]
    GammaCrown,
}

impl PremiseEnvironment {
    fn as_str(self) -> &'static str {
        match self {
            Self::Prelude => "prelude",
            Self::GammaCrown => "gamma-crown",
        }
    }
}

/// Arguments for `clean auto premise`.
///
/// The goal is supplied as a free-text string — no Lean parser runs. The
/// string is tokenized lexically on whitespace + Lean delimiters and compared
/// against the pretty-printed types of every kernel-registered declaration.
#[derive(Debug, Clone, Args)]
pub struct PremiseArgs {
    /// Goal type as a free-text string
    /// (e.g. `"Eq Nat 0 0"` or `"∀ n : Nat, 0 ≤ n"`).
    #[arg(long, value_name = "STRING")]
    pub goal: String,
    /// Maximum number of premises to return (default 10).
    #[arg(long, value_name = "N", default_value_t = 10)]
    pub limit: usize,
    /// Classification filter (default `All`).
    #[arg(long, value_enum, default_value_t = PremiseClassification::All)]
    pub classification: PremiseClassification,
    /// Kernel environment to index.
    #[arg(long, value_enum, default_value_t = PremiseEnvironment::Prelude)]
    pub environment: PremiseEnvironment,
    /// Emit machine-readable JSON instead of the human table.
    #[arg(long)]
    pub json: bool,
    /// Print per-candidate scoring detail (head-symbol / jaccard breakdown).
    #[arg(short, long)]
    pub verbose: bool,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean auto premise` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PremiseCliError {
    /// `--goal` was empty or whitespace-only.
    #[error("`--goal` must be a non-empty string")]
    EmptyGoal,
    /// Requested environment could not be initialized.
    #[error("failed to initialize premise environment `{environment}`")]
    EnvironmentInit {
        /// Environment label.
        environment: &'static str,
    },
}

// -- Tokenization & fingerprinting -------------------------------------------

/// Lean-ish delimiters we split on in addition to whitespace. Conservative
/// set that covers the common goal-string shapes (`∀ a : T, P a`, `T → U`,
/// `Eq Nat 0 0`, `a + b = b + a`, `a ≤ b`) without trying to be a parser.
const DELIMITERS: &[char] = &[
    ' ', '\t', '\n', '\r', '(', ')', '{', '}', '[', ']', ',', ':', ';', '→', '∀', '∃', '¬', '∧',
    '∨', '⇒', '⇔', '≠', '\\', '|', '?',
];

/// Stopword tokens that carry no signal. Intentionally short — we want to
/// keep type-level keywords (`Nat`, `Rat`, `Eq`, `HAdd`) since those are the
/// strongest ranking features.
const STOPWORDS: &[&str] = &[
    "", "a", "b", "c", "n", "m", "k", "x", "y", "z", "p", "q", "h", "the", "is", "of", "for",
    "all", "any", "some",
];

/// A fingerprint for ranking: a tokenized body plus an explicit "heads"
/// subset (capitalized identifiers and recognized operator symbols).
#[derive(Clone, Debug, Default)]
pub(crate) struct Fingerprint {
    /// All non-stopword tokens (lowercased bag for Jaccard).
    pub(crate) tokens: Vec<String>,
    /// Head symbols: capitalized identifiers (`Nat`, `Eq`, `HAdd`) plus
    /// operator tokens (`+`, `=`, `≤`, `<`, `*`). These are the strongest
    /// ranking signal — they almost always survive whatever alpha-renaming
    /// a pretty-printer applies.
    pub(crate) heads: Vec<String>,
}

impl Fingerprint {
    /// Tokenize `text` into a fingerprint.
    ///
    /// Rules:
    ///
    /// 1. Split on whitespace and the `DELIMITERS` set (keeps operator
    ///    characters `+ - * / = < > ≤ ≥` as their own one-character tokens
    ///    when they appear between identifiers).
    /// 2. Strip stopwords from the bag.
    /// 3. Classify a token as a "head" when it starts with an ASCII uppercase
    ///    letter (`Nat`, `Rat`, `Eq`, `HAdd`, `LE`) OR when it is one of the
    ///    recognized operator symbols.
    pub(crate) fn from_text(text: &str) -> Self {
        Self::from_text_with_operator_aliases(text, true)
    }

    /// Fingerprint a declaration name and pretty-printed kernel type.
    ///
    /// Unlike goal text, declaration text must not expand a raw `+` into all
    /// arithmetic addition heads. Kernel types use `+` in universe levels
    /// (`Sort (u + 1)`), and treating that syntax as `Rat.add` made nearly
    /// every universe-polymorphic `List` theorem outrank actual Rat lemmas.
    fn from_declaration_text(text: &str) -> Self {
        Self::from_text_with_operator_aliases(text, false)
    }

    fn from_text_with_operator_aliases(text: &str, expand_operator_aliases: bool) -> Self {
        // First pass: break on DELIMITERS, then segment each chunk to pull
        // operator characters out as their own tokens so `a+b` tokenizes as
        // `a`, `+`, `b`.
        let mut tokens: Vec<String> = Vec::new();
        for chunk in text.split(|c: char| DELIMITERS.contains(&c)) {
            push_chunk_tokens(chunk, &mut tokens);
        }

        let mut heads: Vec<String> = Vec::new();
        let mut body: Vec<String> = Vec::new();
        for tok in tokens {
            let lower = tok.to_lowercase();
            if STOPWORDS.contains(&lower.as_str()) {
                continue;
            }
            if is_head_token(&tok) {
                // Expand operator tokens through `operator_aliases` so a
                // goal written with `+` matches declarations whose types
                // pretty-print as `HAdd.hAdd` / `Rat.add` / `Add.add`.
                // Always push the raw token too so symbol-for-symbol matches
                // (e.g. `+` in a goal vs `+` in a declaration doc) still
                // count.
                let aliases = operator_aliases(&tok);
                if aliases.is_empty() || !expand_operator_aliases {
                    heads.push(tok.clone());
                } else {
                    for alias in aliases {
                        heads.push((*alias).to_string());
                    }
                }
            }
            body.push(lower);
            // When a declaration name contains dots (e.g. `Rat.add`), the
            // leading segment (`Rat`) is ALSO a head — include it so goals
            // that mention the carrier match the segmented type names.
            if let Some((lead, rest)) = tok.split_once('.') {
                if is_head_token(lead) {
                    heads.push(lead.to_string());
                }
                // The tail segments (`add`, `hAdd`, `le`) become body tokens
                // so the Jaccard picks them up as keyword hits from a goal
                // like "add comm".
                for part in rest.split('.') {
                    let low = part.to_lowercase();
                    if !STOPWORDS.contains(&low.as_str()) {
                        body.push(low);
                    }
                }
            }
        }

        // De-duplicate to keep Jaccard well-behaved, but preserve order for
        // stable test output.
        dedup_stable(&mut body);
        dedup_stable(&mut heads);

        Self {
            tokens: body,
            heads,
        }
    }

    /// Classical Jaccard similarity on the body-token sets.
    pub(crate) fn jaccard(&self, other: &Fingerprint) -> f64 {
        if self.tokens.is_empty() || other.tokens.is_empty() {
            return 0.0;
        }
        let (small, large) = if self.tokens.len() <= other.tokens.len() {
            (&self.tokens, &other.tokens)
        } else {
            (&other.tokens, &self.tokens)
        };
        let intersection = small.iter().filter(|t| large.contains(t)).count();
        let union = self.tokens.len() + other.tokens.len() - intersection;
        if union == 0 {
            0.0
        } else {
            intersection as f64 / union as f64
        }
    }

    /// Fraction of this fingerprint's head symbols that appear in `other`.
    pub(crate) fn head_overlap(&self, other: &Fingerprint) -> f64 {
        if self.heads.is_empty() {
            return 0.0;
        }
        let matched = self
            .heads
            .iter()
            .filter(|h| other.heads.contains(h))
            .count();
        matched as f64 / self.heads.len() as f64
    }
}

fn push_chunk_tokens(chunk: &str, out: &mut Vec<String>) {
    const OPS: &[char] = &['+', '-', '*', '/', '=', '<', '>', '≤', '≥'];
    let mut buf = String::new();
    for ch in chunk.chars() {
        if OPS.contains(&ch) {
            if !buf.is_empty() {
                out.push(buf.clone());
                buf.clear();
            }
            out.push(ch.to_string());
        } else {
            buf.push(ch);
        }
    }
    if !buf.is_empty() {
        out.push(buf);
    }
}

fn is_head_token(tok: &str) -> bool {
    let Some(first) = tok.chars().next() else {
        return false;
    };
    if first.is_ascii_uppercase() {
        return true;
    }
    matches!(tok, "+" | "-" | "*" | "/" | "=" | "<" | ">" | "≤" | "≥")
}

fn operator_aliases(tok: &str) -> &'static [&'static str] {
    match tok {
        "+" => &[
            "+",
            "HAdd",
            "HAdd.hAdd",
            "Add",
            "Add.add",
            "Rat.add",
            "Nat.add",
        ],
        "-" => &[
            "-",
            "HSub",
            "HSub.hSub",
            "Sub",
            "Sub.sub",
            "Rat.sub",
            "Nat.sub",
        ],
        "*" => &[
            "*",
            "HMul",
            "HMul.hMul",
            "Mul",
            "Mul.mul",
            "Rat.mul",
            "Nat.mul",
        ],
        "/" => &["/", "HDiv", "HDiv.hDiv", "Div", "Div.div", "Rat.div"],
        "=" => &["=", "Eq"],
        "<" => &["<", "LT", "LT.lt"],
        ">" => &[">"],
        "≤" => &["≤", "LE", "LE.le"],
        "≥" => &["≥"],
        _ => &[],
    }
}

fn dedup_stable(v: &mut Vec<String>) {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    v.retain(|s| seen.insert(s.clone()));
}

// -- Index & ranking ---------------------------------------------------------

/// A single ranked candidate.
#[derive(Clone, Debug)]
pub struct RankedPremise {
    /// Declaration name (e.g. `Rat.add_comm`).
    pub name: String,
    /// Pretty-printed type string.
    pub type_str: String,
    /// Declaration classification tag (Theorem / Axiom / Definition / Opaque).
    pub kind: String,
    /// Proof-quality label (Constructive / AxiomDependent{n} / NotATheorem /
    /// Unchecked).
    pub quality: String,
    /// Combined score.
    pub score: f64,
    /// Head-symbol subscore (fraction of goal heads matched).
    pub head_score: f64,
    /// Jaccard subscore over body tokens.
    pub jaccard: f64,
}

/// Build an in-memory ranked list of candidates for `goal_fp` against the
/// given environment.
///
/// The index is built on every invocation because `Environment::with_prelude`
/// is <175 declarations and walking it takes a few milliseconds. If this ever
/// grows, cache the fingerprints on `ConstantInfo` via an extension.
pub(crate) fn rank_premises(
    env: &Environment,
    goal_fp: &Fingerprint,
    filter: PremiseClassification,
    limit: usize,
) -> Vec<RankedPremise> {
    let mut scored: Vec<RankedPremise> = Vec::new();

    // Snapshot names+kinds first so we can call `proof_quality` without
    // holding an iterator borrow on `env.constants()`.
    let snapshot: Vec<(String, ConstantKind, String)> = env
        .constants()
        .map(|info| {
            let type_str = format!("{}", info.type_);
            (info.name.to_string(), info.kind, type_str)
        })
        .collect();

    for (name, kind, type_str) in snapshot {
        let cand_fp = Fingerprint::from_declaration_text(&format!("{name} {type_str}"));
        let head_score = goal_fp.head_overlap(&cand_fp);
        let jaccard = goal_fp.jaccard(&cand_fp);
        // Primary weighting: head-symbol match dominates. A goal that
        // mentions `HAdd` + `Eq` should drive the ranking even if the
        // premise uses different bound-variable names.
        let score = head_score + 0.5 * jaccard;

        if score == 0.0 {
            continue;
        }

        // Classification filter.
        let name_id = clean_kernel::Name::from_string(&name);
        let quality = match env.proof_quality(&name_id) {
            Some(ProofQuality::Constructive) => "Constructive".to_string(),
            Some(ProofQuality::AxiomDependent { axiom_count, .. }) => {
                format!("AxiomDependent({axiom_count})")
            }
            Some(ProofQuality::NotATheorem) => "NotATheorem".to_string(),
            Some(ProofQuality::Unchecked) => "Unchecked".to_string(),
            // `ProofQuality` is `#[non_exhaustive]`; future variants fall
            // back to a human-readable placeholder so the CLI keeps working.
            Some(_) => "Other".to_string(),
            None => "Unknown".to_string(),
        };
        if matches!(filter, PremiseClassification::Constructive) && quality != "Constructive" {
            continue;
        }

        scored.push(RankedPremise {
            name,
            type_str,
            kind: format!("{:?}", kind),
            quality,
            score,
            head_score,
            jaccard,
        });
    }

    // Sort by (score desc, name-length asc, name asc) for stable, readable
    // output. Shorter names tend to be more-fundamental lemmas.
    scored.sort_by(|a, b| {
        premise_kind_priority(b)
            .cmp(&premise_kind_priority(a))
            .then_with(|| {
                b.score
                    .partial_cmp(&a.score)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .then_with(|| a.name.len().cmp(&b.name.len()))
            .then_with(|| a.name.cmp(&b.name))
    });
    scored.truncate(limit);
    scored
}

fn premise_kind_priority(premise: &RankedPremise) -> u8 {
    match premise.kind.as_str() {
        "Theorem" => 3,
        "Axiom" => 2,
        "Opaque" => 1,
        _ => 0,
    }
}

fn merge_ranked_premises(mut ranked: Vec<RankedPremise>) -> Vec<RankedPremise> {
    ranked.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.name.len().cmp(&b.name.len()))
            .then_with(|| a.name.cmp(&b.name))
    });

    let mut deduped: Vec<RankedPremise> = Vec::new();
    for candidate in ranked {
        if deduped
            .iter()
            .any(|existing| existing.name == candidate.name)
        {
            continue;
        }
        deduped.push(candidate);
    }
    deduped
}

fn rank_in_environment(
    environment: PremiseEnvironment,
    goal_fp: &Fingerprint,
    filter: PremiseClassification,
    limit: usize,
) -> Result<Vec<RankedPremise>, PremiseCliError> {
    match environment {
        PremiseEnvironment::Prelude => {
            let env = Environment::with_prelude();
            Ok(rank_premises(&env, goal_fp, filter, limit))
        }
        PremiseEnvironment::GammaCrown => {
            let per_env_limit = limit.max(50);
            let mut ranked = Vec::new();
            let mut initialized = 0usize;
            for id in CONJECTURE_IDS {
                let Ok(env) = init_conjecture(id) else {
                    continue;
                };
                initialized += 1;
                ranked.extend(rank_premises(&env, goal_fp, filter, per_env_limit));
            }
            if initialized == 0 {
                return Err(PremiseCliError::EnvironmentInit {
                    environment: environment.as_str(),
                });
            }
            let mut merged = merge_ranked_premises(ranked);
            merged.truncate(limit);
            Ok(merged)
        }
    }
}

/// Rank premises for a goal string in the selected environment.
///
/// This is the non-printing API used by research benches. It keeps the CLI
/// output and factory benchmark on the same ranking implementation.
pub fn rank_goal(
    goal: &str,
    environment: PremiseEnvironment,
    filter: PremiseClassification,
    limit: usize,
) -> Result<Vec<RankedPremise>, PremiseCliError> {
    let goal_trim = goal.trim();
    if goal_trim.is_empty() {
        return Err(PremiseCliError::EmptyGoal);
    }
    let goal_fp = Fingerprint::from_text(goal_trim);
    rank_in_environment(environment, &goal_fp, filter, limit)
}

// -- Entry point --------------------------------------------------------------

/// Dispatch entry point for `clean auto premise`. Called from
/// `clean-cli::cmd_auto::handle_auto_premise_command`.
pub fn run(args: PremiseArgs) -> Result<(), PremiseCliError> {
    let goal_trim = args.goal.trim();
    if goal_trim.is_empty() {
        return Err(PremiseCliError::EmptyGoal);
    }

    let start = Instant::now();
    let ranked = rank_goal(goal_trim, args.environment, args.classification, args.limit)?;
    let elapsed = start.elapsed();

    if args.json {
        emit_json(&args.goal, args.environment, &ranked, elapsed.as_micros());
    } else {
        emit_table(
            &args.goal,
            args.environment,
            &ranked,
            args.verbose,
            elapsed.as_millis(),
        );
    }
    Ok(())
}

fn emit_table(
    goal: &str,
    environment: PremiseEnvironment,
    ranked: &[RankedPremise],
    verbose: bool,
    elapsed_ms: u128,
) {
    println!(
        "clean auto premise — environment: {} — goal: {goal}",
        environment.as_str()
    );
    if ranked.is_empty() {
        println!("  (no candidates scored above 0)");
        return;
    }
    // Column widths: name up to 40, kind 11, quality 20, score 6.
    println!(
        "  {:<4} {:<40} {:<11} {:<22} {:>6}",
        "rank", "name", "kind", "quality", "score"
    );
    for (i, r) in ranked.iter().enumerate() {
        let name = truncate(&r.name, 40);
        let kind = truncate(&r.kind, 11);
        let qual = truncate(&r.quality, 22);
        println!(
            "  {:<4} {:<40} {:<11} {:<22} {:>6.3}",
            i + 1,
            name,
            kind,
            qual,
            r.score
        );
        if verbose {
            println!(
                "       head={:.3}  jaccard={:.3}  type={}",
                r.head_score,
                r.jaccard,
                truncate(&r.type_str, 80),
            );
        }
    }
    println!("  ({} candidates in {} ms)", ranked.len(), elapsed_ms);
}

fn emit_json(
    goal: &str,
    environment: PremiseEnvironment,
    ranked: &[RankedPremise],
    elapsed_us: u128,
) {
    println!("{}", render_json(goal, environment, ranked, elapsed_us));
}

fn render_json(
    goal: &str,
    environment: PremiseEnvironment,
    ranked: &[RankedPremise],
    elapsed_us: u128,
) -> String {
    // Tiny hand-rolled JSON so we don't pull serde_json into the default
    // dep graph. Structure is stable and documented in the issue.
    let mut out = String::new();
    out.push_str("{\"goal\":");
    push_json_string(&mut out, goal);
    out.push_str(",\"environment\":");
    push_json_string(&mut out, environment.as_str());
    out.push_str(&format!(
        ",\"elapsed_us\":{elapsed_us},\"count\":{},",
        ranked.len()
    ));
    out.push_str("\"results\":[");
    for (i, r) in ranked.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&format!("{{\"rank\":{},\"name\":", i + 1));
        push_json_string(&mut out, &r.name);
        out.push_str(",\"kind\":");
        push_json_string(&mut out, &r.kind);
        out.push_str(",\"quality\":");
        push_json_string(&mut out, &r.quality);
        out.push_str(",\"type\":");
        push_json_string(&mut out, &r.type_str);
        out.push_str(&format!(
            ",\"score\":{:.6},\"head_score\":{:.6},\"jaccard\":{:.6}}}",
            r.score, r.head_score, r.jaccard
        ));
    }
    out.push_str("]}");
    out
}

fn push_json_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
        out.push('…');
        out
    }
}

// -- Feature descriptor -------------------------------------------------------

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ISSUE_3600: Reference = Reference {
    kind: RefKind::Issue,
    label: "Premise selection CLI",
    target: "#3600",
};

const ISSUE_3386: Reference = Reference {
    kind: RefKind::Issue,
    label: "AI proof search with kernel verification loop",
    target: "#3386",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-auto",
    target: "clean-auto",
};

/// Feature descriptor for `clean auto premise`. Exposed at crate root for
/// registration via `clean-cli/src/registry.rs`.
pub const PREMISE_FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["auto", "premise"],
    domain_root: Some("auto"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "Top-k premise shortlist for a goal type string (Experimental)",
    description: "\
Rank kernel-registered declarations (Theorems + Axioms + Definitions) against \
a goal-type string and print the top-k best candidates — intended as a \
10-100× speedup over blind `grep` when an agent is looking for premises to \
pass to `search_proof` or a downstream SMT tactic. The goal is a free-text \
string — no Lean parser runs. The ranker combines a head-symbol match score \
(capitalized identifiers + recognized operator symbols) with a Jaccard overlap \
over the remaining body tokens; score = head_overlap + 0.5 × jaccard. \
The default CLI indexes `Environment::with_prelude()` only; richer algebraic \
surfaces are available through `--environment gamma-crown`, which initializes \
the clean Gamma-Crown / NNVerify conjecture environments and ranks over their \
registered declarations. \
`--classification constructive` restricts the output to Theorems with zero \
domain-specific axiom dependencies. `--json` emits a stable JSON shape for \
downstream tooling. Marked `Stability::Experimental` because the ranking \
formula and filter set will evolve alongside #3386 (AI proof search loop). \
Part of Epic #3436 (#3600).",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean auto premise --goal \"Eq Nat 0 0\"",
            what: "shortlist candidate premises for a Nat reflexivity goal in the default prelude",
        },
        Example {
            cmd: "clean auto premise --environment gamma-crown --goal \"C007 Farkas certificate composition\" --limit 5",
            what: "shortlist Gamma-Crown / NNVerify premises for a proof packet",
        },
        Example {
            cmd: "clean auto premise --goal \"∀ n : Nat, 0 ≤ n\" --limit 5",
            what: "shortlist the top 5 candidates for a Nat nonnegativity goal",
        },
        Example {
            cmd: "clean auto premise --goal \"Eq Nat 0 0\" --classification constructive --json",
            what: "emit JSON of constructive-only candidates for a reflexivity goal",
        },
    ],
    see_also: &["auto prove", "check", "eval"],
    references: &[DESIGN_REF, ISSUE_3600, ISSUE_3386, ISSUE_3436, CRATE_REF],
}];

const _: () = {
    assert!(
        !PREMISE_FEATURES.is_empty(),
        "PREMISE_FEATURES must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = PREMISE_FEATURES;
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fingerprint_splits_on_delimiters() {
        let fp = Fingerprint::from_text("∀ a b : Rat, a + b = b + a");
        // Heads should include Rat and the operator tokens.
        assert!(fp.heads.iter().any(|h| h == "Rat"), "heads={:?}", fp.heads);
        assert!(fp.heads.iter().any(|h| h == "+"), "heads={:?}", fp.heads);
        assert!(fp.heads.iter().any(|h| h == "="), "heads={:?}", fp.heads);
        // Body tokens should include lowercased `rat` (from the Jaccard bag)
        // but NOT the single-char stopwords.
        assert!(fp.tokens.iter().any(|t| t == "rat"));
        assert!(!fp.tokens.iter().any(|t| t == "a"));
    }

    #[test]
    fn fingerprint_jaccard_is_symmetric_and_bounded() {
        let a = Fingerprint::from_text("Nat zero le");
        let b = Fingerprint::from_text("Nat zero le refl");
        let jab = a.jaccard(&b);
        let jba = b.jaccard(&a);
        assert!((jab - jba).abs() < 1e-9);
        assert!(jab > 0.0 && jab <= 1.0);
    }

    #[test]
    fn fingerprint_head_overlap_counts_operator_aliases() {
        let goal = Fingerprint::from_text("Nat Rat + =");
        let cand = Fingerprint::from_text("Nat + x");
        let h = goal.head_overlap(&cand);
        // `+` expands to its arithmetic aliases, so cand matches Nat plus the
        // shared addition aliases but not Rat or Eq.
        assert!(
            (h - (8.0 / 11.0)).abs() < 1e-9,
            "head_overlap={} heads={:?}",
            h,
            goal.heads
        );
    }

    #[test]
    fn declaration_fingerprint_does_not_treat_universe_plus_as_rat_add() {
        let declaration = Fingerprint::from_declaration_text(
            "List.append_nil (alpha : Sort (u + 1)) : Eq (List alpha)",
        );
        assert!(declaration.heads.iter().any(|head| head == "+"));
        assert!(
            !declaration.heads.iter().any(|head| head == "Rat.add"),
            "a universe-level `+` must not fabricate arithmetic heads: {:?}",
            declaration.heads
        );
    }

    #[test]
    fn rank_rat_add_comm_appears_for_add_comm_goal() {
        // Build a richer environment that registers the Rat Field instance
        // (which pulls in `Rat.add_comm` via `register_rat_add_comm_proof`).
        let mut env = Environment::with_prelude();
        env.init_rat_field_inst()
            .expect("init_rat_field_inst should succeed in a fresh prelude");
        let goal = Fingerprint::from_text("∀ a b : Rat, a + b = b + a");
        let ranked = rank_premises(&env, &goal, PremiseClassification::All, 10);
        // `Rat.add_comm` MUST be registered once the Rat Field instance is
        // initialized — tripwire for a future regression.
        let top3: Vec<&str> = ranked.iter().take(3).map(|r| r.name.as_str()).collect();
        assert!(
            ranked.iter().any(|r| r.name == "Rat.add_comm"),
            "Rat.add_comm missing from ranked={:?}",
            ranked.iter().map(|r| &r.name).collect::<Vec<_>>()
        );
        assert!(
            top3.contains(&"Rat.add_comm"),
            "Rat.add_comm not in top 3; top3={:?}",
            top3
        );
    }

    #[test]
    fn rank_le_refl_appears_for_nonneg_nat_goal() {
        // `Nat.le_refl` is a foundational axiom registered by the standard
        // prelude chain (`init_nat_preorder` → ... → `Nat.le_refl`). The
        // goal "∀ n : Nat, 0 ≤ n" shares the `Nat` head and the `≤`
        // operator, so we expect it in the top 5.
        let env = Environment::with_prelude();
        let goal = Fingerprint::from_text("∀ n : Nat, 0 ≤ n");
        let ranked = rank_premises(&env, &goal, PremiseClassification::All, 10);
        let top5: Vec<&str> = ranked.iter().take(5).map(|r| r.name.as_str()).collect();
        assert!(
            top5.iter()
                .any(|n| *n == "Nat.zero_le" || *n == "Nat.le_refl"),
            "Neither Nat.zero_le nor Nat.le_refl in top5={:?}",
            top5
        );
    }

    #[test]
    fn empty_goal_rejected() {
        let args = PremiseArgs {
            goal: "   ".to_string(),
            limit: 10,
            classification: PremiseClassification::All,
            environment: PremiseEnvironment::Prelude,
            json: false,
            verbose: false,
        };
        let err = run(args).unwrap_err();
        assert!(matches!(err, PremiseCliError::EmptyGoal));
    }

    #[test]
    fn classification_filter_removes_axioms() {
        let env = Environment::with_prelude();
        let goal = Fingerprint::from_text("∀ a b : Rat, a + b = b + a");
        let all = rank_premises(&env, &goal, PremiseClassification::All, 50);
        let constructive = rank_premises(&env, &goal, PremiseClassification::Constructive, 50);
        // Every constructive result must have quality == "Constructive".
        assert!(
            constructive.iter().all(|r| r.quality == "Constructive"),
            "non-constructive leak: {:?}",
            constructive
                .iter()
                .map(|r| (&r.name, &r.quality))
                .collect::<Vec<_>>()
        );
        // Filter cannot grow the result set.
        assert!(constructive.len() <= all.len());
    }

    #[test]
    fn render_json_contract_for_eq_nat_goal() {
        let goal = "Eq Nat 0 0";
        let env = Environment::with_prelude();
        let goal_fp = Fingerprint::from_text(goal);
        let ranked = rank_premises(&env, &goal_fp, PremiseClassification::All, 3);
        assert!(
            !ranked.is_empty(),
            "expected the default prelude to yield candidates for {goal}"
        );

        let json = render_json(goal, PremiseEnvironment::Prelude, &ranked, 42);
        assert_eq!(
            json,
            format!(
                "{{\"goal\":\"Eq Nat 0 0\",\"environment\":\"prelude\",\"elapsed_us\":42,\"count\":{},\"results\":[{}]}}",
                ranked.len(),
                ranked
                    .iter()
                    .enumerate()
                    .map(|(i, r)| format!(
                        "{{\"rank\":{},\"name\":\"{}\",\"kind\":\"{}\",\"quality\":\"{}\",\"type\":\"{}\",\"score\":{:.6},\"head_score\":{:.6},\"jaccard\":{:.6}}}",
                        i + 1,
                        r.name,
                        r.kind,
                        r.quality,
                        r.type_str,
                        r.score,
                        r.head_score,
                        r.jaccard
                    ))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        );
    }
}
