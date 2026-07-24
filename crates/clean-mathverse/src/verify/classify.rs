// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MATH vs GENERATED classification of a module's OWN constants (Lane-A yield).
//!
//! The aggregate per-module kernel-verify rate (75–85%) mixes two very different
//! populations: the named results a mathematician actually writes (the
//! corpus-worthy rows we want to graduate) and the compiler-emitted internals
//! Lean's elaborator synthesizes per declaration (equation lemmas, recursors,
//! `match`/`brecOn` auxiliaries, structure projections, `sizeOf` specs, etc.).
//! Lane A's REAL yield is the kernel-verify rate on the MATH population alone;
//! the GENERATED population is boilerplate we would lower-tier, not graduate.
//!
//! This module is the AUDITABLE classifier. It is intentionally conservative:
//! a constant is [`ConstKind::Generated`] only when a `.`-separated segment is a
//! KNOWN Lean auto-generated tag, or when a segment is a numeric/`_<digits>`
//! suffix that Lean uses for hygienic/auto-named declarations. Anything else —
//! including every ordinary `Mathlib.Foo.bar_baz` theorem/definition — is
//! [`ConstKind::Math`]. The rule and a sample of each bucket are printed by the
//! worker so a human can confirm no real theorem was mislabeled to inflate the
//! math rate.
//!
//! # Why segment-based, not substring-based
//!
//! Lean's internal names are dot-structured: the auto-generated tag is always a
//! whole NAME SEGMENT (`Foo.eq_1`, `Foo.match_2`, `Foo.proof_3`, `Foo._sizeOf_1`,
//! `instFoo._cstage1`). Substring matching would mislabel honest math like
//! `Nat.rec_aux_lemma` or a user lemma literally named `..._below_...`. We only
//! ever inspect whole segments, with one narrow exception (`_cstage` suffix,
//! which Lean appends to the FINAL segment of compiled specializations).

/// Whether an OWN constant is human-authored MATH or a compiler-emitted
/// GENERATED artifact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstKind {
    /// A human-authored named result (Theorem / Definition / Inductive / Axiom /
    /// structure) — the corpus-worthy row Lane A wants to graduate.
    Math,
    /// A compiler-emitted internal (equation lemma, recursor, `match`/`brecOn`
    /// auxiliary, projection, `sizeOf` spec, `_cstage` specialization, hygienic
    /// `_<n>` name, …) — boilerplate to lower-tier, not graduate.
    Generated,
}

impl ConstKind {
    /// Stable lowercase label for sidecar/report serialization.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Math => "math",
            Self::Generated => "generated",
        }
    }
}

/// Known Lean auto-generated name SEGMENTS (exact, case-sensitive).
///
/// Each is a whole `.`-separated segment Lean emits per declaration. Sourced
/// from Lean 4's `Lean.Meta`/`Lean.Elab` auto-generated naming conventions
/// (equation compiler, structural/well-founded recursion, structures,
/// `deriving`). Kept explicit and conservative.
const GENERATED_EXACT_SEGMENTS: &[&str] = &[
    // Recursors / eliminators / cases.
    "rec",
    "recAux",
    "recOn",
    "casesOn",
    "binductionOn",
    "brecOn",
    "brecOnTable",
    "below",
    "ibelow",
    "noConfusion",
    "noConfusionType",
    "elim",
    // Structure / constructor auto-fields.
    "mk",
    "sizeOf",
    "fold",
    "ofNat",
    "ofScientific",
    "toCtorIdx",
    // Decidability / equality boilerplate.
    "decEq",
    "ofNatNat",
    // Compiler-IR / LCNF artifacts (specialization, boxing, closure lambdas,
    // reduced-arg wrappers, flattened constructors, inherited defaults). These
    // are emitted by Lean's compiler/elaborator, never written by a human.
    "_boxed",
    "_flat_ctor",
    "_inherited_default",
    "_default",
    "_unsafe_rec",
    "_impl",
];

/// Known auto-generated PREFIX tags on a segment: a segment beginning with one
/// of these (followed by `_<digits>` or another internal marker) is generated.
/// These match Lean's hygienic counter naming (`eq_1`, `match_2`, `proof_3`,
/// `_sizeOf_1`, `_simp_1`, `_proof_4`, `_eq_5`, `_unary`, …).
const GENERATED_SEGMENT_PREFIXES: &[&str] = &[
    "eq_",
    "_eq_",
    "match_",
    "_match_",
    "proof_",
    "_proof_",
    "_simp_",
    "simp_",
    "_sizeOf_",
    "sizeOf_",
    "_cstage",
    "_unary",
    "_mutual",
    "_elambda",
    "_elam",
    "_lam",
    "_redArg",
    "eq_def",
    "eq_unfold",
    "induct",
    "fwd",
    "brec",
    "_spec_",
];

/// Returns `true` if `segment` is a Lean auto-generated name segment.
///
/// A segment is generated when it is one of [`GENERATED_EXACT_SEGMENTS`], OR it
/// is a HYGIENIC name (a bare `_<digits>` segment, or one of the known prefixes
/// followed by digits / end-of-segment, e.g. `eq_1`, `match_3`, `_sizeOf_1`,
/// `_cstage2`, `proof_4`), OR it is the special `eq_def` / `eq_unfold` tag.
fn is_generated_segment(segment: &str) -> bool {
    if GENERATED_EXACT_SEGMENTS.contains(&segment) {
        return true;
    }
    // Bare hygienic counter segment: `_123`. Lean uses `_<digits>` for
    // auto-named anonymous declarations and macro scopes.
    if let Some(rest) = segment.strip_prefix('_') {
        if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
            return true;
        }
    }
    // Known generated prefixes. For the counter-style prefixes (ending in `_`),
    // require that what follows is a digit run or empty — so we match `eq_1`,
    // `match_12`, `_sizeOf_3`, `_proof_2` but NEVER an honest `eq_comm`,
    // `match_pattern`, or `proof_irrel` lemma a human wrote.
    for &p in GENERATED_SEGMENT_PREFIXES {
        if let Some(rest) = segment.strip_prefix(p) {
            if p.ends_with('_') {
                // counter form: prefix already ends with '_', tail must be digits
                if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
                    return true;
                }
            } else if p == "eq_def" || p == "eq_unfold" {
                // exact tags (with optional `_<digits>` disambiguator)
                if rest.is_empty()
                    || (rest.starts_with('_') && rest[1..].bytes().all(|b| b.is_ascii_digit()))
                {
                    return true;
                }
            } else {
                // `_cstage`, `_unary`, `_mutual`, `_redArg`, `brec`, `induct`,
                // `fwd`, `_spec_`, `_elambda`, `_elam`: these are Lean compiler
                // tags. Accept the bare tag or a `<tag><digits>`/`<tag>_<n>`
                // form; reject when followed by a letter (would be honest math
                // like `inductive_...`? — Lean never emits `induct` as a math
                // segment, but stay safe: require non-alpha tail).
                if rest.is_empty()
                    || rest
                        .bytes()
                        .next()
                        .is_some_and(|b| !b.is_ascii_alphabetic())
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Classify a fully qualified Lean constant name as MATH or GENERATED.
///
/// GENERATED iff ANY `.`-separated segment is a Lean auto-generated tag
/// (see [`is_generated_segment`]). Otherwise MATH. This is the documented
/// rule the worker prints for audit.
#[must_use]
pub fn classify_const(name: &str) -> ConstKind {
    if name.split('.').any(is_generated_segment) {
        ConstKind::Generated
    } else {
        ConstKind::Math
    }
}

/// The human-readable classification rule, printed by the worker so the split
/// is auditable.
#[must_use]
pub fn classification_rule() -> String {
    format!(
        "GENERATED iff any `.`-separated name segment is a Lean auto-generated tag: \
         exact={{ {exact} }}; prefix-counter (tag+digits)={{ {pref} }}; \
         bare hygienic `_<digits>`. Else MATH (human-authored Theorem/Def/Inductive/Axiom). \
         Matching is whole-segment (one narrow tail-form exception per prefix), never substring.",
        exact = GENERATED_EXACT_SEGMENTS.join(", "),
        pref = GENERATED_SEGMENT_PREFIXES.join(", "),
    )
}

#[cfg(test)]
#[path = "classify_tests.rs"]
mod tests;
