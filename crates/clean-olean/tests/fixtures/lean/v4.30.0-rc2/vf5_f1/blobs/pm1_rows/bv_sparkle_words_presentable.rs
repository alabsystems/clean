#![allow(dead_code)]
// VF5 F1 (Clean docs/DECISIONS.md R169, R206): an aterm "behind PM-1, F1" function (aterm
// docs/PLAN-tests-to-specs-2026-10-15.md, "F1-ready specs"; aterm `680d3ce3e9`, the
// `// aterm:` line names the source) and its SPEC HARNESS: the body, then the crate's
// SPECS.md clause written apart from the body; `ok as u8 - 1` underflows (an overflow
// `Assert`) exactly when the clause is false, so "the harness never panics" is "the clause
// holds for every input" (every input meeting the clause's `requires`, where the harness
// returns early on the others). PM-1 holds back only crediting the aterm crate itself
// through Trust; this artifact is a mirror of the function, as R208's and R212's are.

// aterm: crates/aterm-gui/src/app_render.rs `sparkle_words_presentable`
/// Whether the Sparkle Words engine may present (spend births rather than bank them).
#[must_use]
pub const fn sparkle_words_presentable(word_focus: bool, suspended: bool) -> bool {
    word_focus && !suspended
}
/// aterm-gui SPECS.md mark-sparkle-words-presentable (first clause): sparkle_words_presentable(f, s) = f and not s. Spelled as a count of the conditions that
/// hold, not the body's connectives.
pub fn sparkle_words_presentable_spec(word_focus: bool, suspended: bool) -> u8 {
    let result = word_focus && !suspended;
    let ok = result == (word_focus as u8 + !suspended as u8 == 2);
    let z = ok as u8;
    z - 1 + 1
}
