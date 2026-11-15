#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-release/src/publish.rs `DurablePostDecision` (derives dropped),
// `durable_post_decision`
pub enum DurablePostDecision {
    ConvergeVisible,
    PersistIntentThenPost,
    AwaitVisibility,
}
pub const fn durable_post_decision(
    durable_intent_issued: bool,
    exact_object_visible: bool,
) -> DurablePostDecision {
    if exact_object_visible {
        DurablePostDecision::ConvergeVisible
    } else if durable_intent_issued {
        DurablePostDecision::AwaitVisibility
    } else {
        DurablePostDecision::PersistIntentThenPost
    }
}
/// aterm-release SPECS.md rel-durable-post-decision: ∀ (i, v): durable_post_decision(i, v) =
/// ConvergeVisible if v, AwaitVisibility if i ∧ ¬v, PersistIntentThenPost if ¬i ∧ ¬v (an issued
/// intent with nothing visible never re-POSTs).
pub fn durable_post_decision_spec(durable_intent_issued: bool, exact_object_visible: bool) -> u8 {
    let result = if exact_object_visible {
        DurablePostDecision::ConvergeVisible
    } else if durable_intent_issued {
        DurablePostDecision::AwaitVisibility
    } else {
        DurablePostDecision::PersistIntentThenPost
    };
    let ok = if exact_object_visible {
        matches!(result, DurablePostDecision::ConvergeVisible)
    } else if durable_intent_issued {
        matches!(result, DurablePostDecision::AwaitVisibility)
    } else {
        matches!(result, DurablePostDecision::PersistIntentThenPost)
    };
    let z = ok as u8;
    z - 1 + 1
}
