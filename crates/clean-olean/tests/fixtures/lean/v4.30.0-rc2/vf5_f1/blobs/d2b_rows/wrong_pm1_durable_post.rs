#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_durable_post.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum DurablePostDecision {
    ConvergeVisible,
    PersistIntentThenPost,
    AwaitVisibility,
}
/// The clause re-POSTing an issued intent: false at (true, false).
pub fn durable_post_decision_wrong(durable_intent_issued: bool, exact_object_visible: bool) -> u8 {
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
        matches!(result, DurablePostDecision::PersistIntentThenPost)
    } else {
        matches!(result, DurablePostDecision::PersistIntentThenPost)
    };
    let z = ok as u8;
    z - 1 + 1
}
