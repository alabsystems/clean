// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nonvacuity consumers of the checked call rules. This ordinary Core fixture
//! has a five-result caller and identity callee. Values, caller locals, stack
//! suffix, memory and host state remain quantified. It is not a TLA translation
//! proof, and call/return rules alone do not establish whole-world validity.

use crate::spec::Specification;
use clean_kernel::Name;

fn list(ty: &str, items: impl IntoIterator<Item = impl AsRef<str>>) -> String {
    let items: Vec<_> = items.into_iter().collect();
    items
        .iter()
        .rev()
        .fold(format!("IRList.nil {ty}"), |tail, item| {
            format!("IRList.cons {ty} ({}) ({tail})", item.as_ref())
        })
}

const WORDS: [&str; 5] = ["a", "b", "c", "d", "e"];
const WORD_PARAMS: &str = "(a : Nat) (b : Nat) (c : Nat) (d : Nat) (e : Nat)";
const WORLD_PARAMS: &str = "(W : Type) (memory : IRByteMemoryV1) (host : W) (owners : IRList Nat) (next : Nat) (tail : IRList IRFrame) (locals : IRList IRBinding) (cursor : Nat)";
const PARENT: &str = "(byte_call_test_parent a b c d e locals)";
const VALUES: &str = "(byte_call_test_words a b c d e)";

fn checked(spec: &mut Specification, source: &str) {
    let name = source.split_whitespace().nth(1).unwrap();
    spec.add_recursive_def(
        source,
        "Quantified five-lane consumer of actual Core call/return rules",
    )
    .unwrap_or_else(|error| panic!("{name}: {error}"));
    let definition = spec.get_definition(name).unwrap();
    assert!(!definition.is_axiom);
    assert!(definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn range_params() -> String {
    WORDS
        .iter()
        .map(|word| format!("(h{word} : Eq Bool (ir_nat_ltb {word} (ir_nat_pow2 64)) Bool.true)"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn prepare(spec: &mut Specification) {
    let args = list("Nat", (0..5).map(|n| n.to_string()));
    let dests = list("Nat", (10..15).map(|n| n.to_string()));
    let types = list("IRTy", ["IRTy.uint_ 64"; 5]);
    let values = list(
        "IRScalar",
        WORDS.map(|word| format!("IRScalar.int_ {word}")),
    );
    let locals = WORDS
        .iter()
        .enumerate()
        .rev()
        .fold("locals".to_owned(), |tail, (id, word)| {
            format!("IRList.cons IRBinding (IRBinding.mk {id} (IRScalar.int_ {word})) ({tail})")
        });
    let ret_args = "IRNode.mk (IRInst.ret byte_call_test_args) (IRList.nil Nat)".to_string();
    let callee_nodes = list("IRNode", [ret_args]);
    let callee_blocks = list(
        "IRBlock",
        [format!("IRBlock.mk 0 (IRList.nil Nat) ({callee_nodes})")],
    );
    let parent_nodes = list(
        "IRNode",
        [
            "IRNode.mk (IRInst.call 7 byte_call_test_args) byte_call_test_dests",
            "IRNode.mk (IRInst.ret byte_call_test_dests) (IRList.nil Nat)",
        ],
    );
    let parent_blocks = list(
        "IRBlock",
        [format!("IRBlock.mk 0 (IRList.nil Nat) ({parent_nodes})")],
    );
    let functions = list(
        "IRFunc",
        [
            "byte_call_test_callee".to_owned(),
            format!("IRFunc.mk 9 byte_call_test_args 0 ({parent_blocks})"),
        ],
    );
    let bindings = list(
        "IRByteFunctionV1",
        [
            "byte_call_test_binding",
            "IRByteFunctionV1.mk 9 3 4160 1 Bool.false",
        ],
    );
    let signatures = list("IRByteSignatureV1", ["byte_call_test_signature"]);
    let sites = list(
        "IRByteSiteV1",
        [
            "byte_call_test_site",
            "IRByteSiteV1.mk 9 0 1 0 1 (IRList.nil IRTy)",
            "IRByteSiteV1.mk 7 0 0 0 1 (IRList.nil IRTy)",
        ],
    );
    for source in [
        format!("def byte_call_test_args : IRList Nat := {args}"),
        format!("def byte_call_test_dests : IRList Nat := {dests}"),
        format!("def byte_call_test_types : IRList IRTy := {types}"),
        format!("def byte_call_test_words {WORD_PARAMS} : IRList IRScalar := {values}"),
        format!("def byte_call_test_parent {WORD_PARAMS} (locals : IRList IRBinding) : IRFrame := IRFrame.mk 9 0 0 ({locals}) (IRList.nil Nat)"),
        format!("def byte_call_test_callee : IRFunc := IRFunc.mk 7 byte_call_test_args 0 ({callee_blocks})"),
        "def byte_call_test_binding : IRByteFunctionV1 := IRByteFunctionV1.mk 7 3 4096 1 Bool.false".to_owned(),
        "def byte_call_test_signature : IRByteSignatureV1 := IRByteSignatureV1.mk 3 byte_call_test_types byte_call_test_types Bool.false".to_owned(),
        "def byte_call_test_site : IRByteSiteV1 := IRByteSiteV1.mk 9 0 0 0 1 byte_call_test_types".to_owned(),
        format!("def byte_call_test_context : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk ({functions}) (IRList.nil IRGlobal)) (IRList.nil IRByteLayoutV1) ({signatures}) ({bindings}) ({sites})"),
    ] {
        checked(spec, &source);
    }

    let (_, fit_proof) = WORDS.iter().rev().fold(
        ("Bool.true".to_owned(), "Eq.refl Bool Bool.true".to_owned()),
        |(tail, proof), word| {
            let fit = format!("ir_byte_value_matches_v1 byte_call_test_context (IRTy.uint_ 64) (IRScalar.int_ {word})");
            let next_proof = format!("ir_byte_function_and_true_v1 ({fit}) ({tail}) (ir_byte_u64_value_fits_v1 byte_call_test_context {word} h{word}) ({proof})");
            (format!("Bool.and ({fit}) ({tail})"), next_proof)
        },
    );
    checked(spec, &format!(
        "def byte_call_test_fits {WORD_PARAMS} {} : Eq Bool (ir_byte_values_match_v1 byte_call_test_context byte_call_test_types {VALUES}) Bool.true := {fit_proof}",
        range_params()
    ));
    checked(
        spec,
        "def byte_call_test_ranges_inhabited : Eq Bool
      (ir_byte_values_match_v1 byte_call_test_context byte_call_test_types
        (byte_call_test_words 0 1 2 18446744073709551614 18446744073709551615)) Bool.true :=
      byte_call_test_fits 0 1 2 18446744073709551614 18446744073709551615
        (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)
        (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)",
    );
    checked(spec, "def byte_call_test_result_lanes (W : Type) (config : IRByteConfigV1 W) : IRList IRScalar :=
      match config with
      | IRByteConfigV1.running machine world => ir_resolve machine byte_call_test_dests
      | IRByteConfigV1.halted outcome world => IRList.nil IRScalar");
}

#[test]
fn five_symbolic_lanes_cross_actual_catalog_calls_and_return_to_current_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
        prepare(&mut spec);
        let world = "(IRByteWorldV1.mk W memory host owners next)";
        let machine = format!(
            "(IRMachine.mk (IRList.cons IRFrame {PARENT} tail) (IRList.nil IRMemSlot) cursor)"
        );
        let entered_frame = format!("(IRFrame.mk 7 0 0 (ir_bind_params byte_call_test_args {VALUES} (IRList.nil IRBinding)) byte_call_test_dests)");
        let entered_machine = format!("(IRMachine.mk (IRList.cons IRFrame {entered_frame} (IRList.cons IRFrame (ir_frame_advance {PARENT}) tail)) (IRList.nil IRMemSlot) cursor)");
        let entered_world =
            "(IRByteWorldV1.mk W memory host (IRList.cons Nat next owners) (Nat.succ next))";
        let entered = format!("(IRByteConfigV1.running W {entered_machine} {entered_world})");
        let direct = format!("(ir_byte_call_v1 W byte_call_test_context providers {machine} {world} byte_call_test_dests byte_call_test_site 7 byte_call_test_args)");
        let known = format!("(ir_byte_call_known_v1 W byte_call_test_context providers {machine} {world} byte_call_test_dests byte_call_test_site byte_call_test_binding byte_call_test_signature {VALUES})");
        let pushed = format!("(ir_byte_lift_v1 W (ir_byte_push_owner_v1 W {world}) (ir_push {machine} byte_call_test_dests byte_call_test_callee {VALUES}))");
        let lookup = "(Eq.refl (IROption IRByteFunctionV1) (IROption.some IRByteFunctionV1 byte_call_test_binding))";
        let signature = "(Eq.refl (IROption IRByteSignatureV1) (IROption.some IRByteSignatureV1 byte_call_test_signature))";
        let guard = "(byte_call_test_fits a b c d e ha hb hc hd he)";
        let call_proof = format!(
            "Eq.trans (IRByteConfigV1 W) {direct} {known} {entered}\n\
              (ir_byte_call_of_catalog_v1 W byte_call_test_context providers {machine} {world} byte_call_test_dests byte_call_test_site 7 byte_call_test_args byte_call_test_binding byte_call_test_signature {lookup} {signature})\n\
              (Eq.trans (IRByteConfigV1 W) {known} {pushed} {entered}\n\
                (ir_byte_internal_call_rule_v1 W byte_call_test_context providers {machine} {world} byte_call_test_dests byte_call_test_site byte_call_test_binding byte_call_test_signature {VALUES} byte_call_test_callee\n\
                  (Eq.refl Bool Bool.false) (Eq.refl (IROption IRFunc) (IROption.some IRFunc byte_call_test_callee)) (Eq.refl Bool Bool.true) {guard})\n\
                (ir_byte_push_frame_v1 W memory host owners next {PARENT} tail (IRList.nil IRMemSlot) cursor byte_call_test_dests byte_call_test_callee {VALUES}))"
        );
        checked(&mut spec, &format!(
            "def byte_call_test_enter {WORLD_PARAMS} (providers : IRByteProvidersV1 W) {WORD_PARAMS} {} : Eq (IRByteConfigV1 W) {direct} {entered} := {call_proof}", range_params()
        ));
        let indirect = format!("(ir_byte_call_indirect_v1 W byte_call_test_context providers {machine} {world} byte_call_test_dests byte_call_test_site (IRScalar.fnptr_ 7) 3 byte_call_test_args 1)");
        checked(&mut spec, &format!(
            "def byte_call_test_indirect {WORLD_PARAMS} (providers : IRByteProvidersV1 W) {WORD_PARAMS} {} : Eq (IRByteConfigV1 W) {indirect} {entered} :=\n\
              Eq.trans (IRByteConfigV1 W) {indirect} {direct} {entered}\n\
                (ir_byte_indirect_call_exact_v1 W byte_call_test_context providers {machine} {world} byte_call_test_dests byte_call_test_site 7 3 byte_call_test_args 1 byte_call_test_binding {lookup} (Eq.refl Bool Bool.true))\n\
                (byte_call_test_enter W memory host owners next tail locals cursor providers a b c d e ha hb hc hd he)", range_params()
        ));
        // Memory and host here are the current values at return, not saved
        // entry values. Retiring next must preserve host and bind every lane.
        let returned = format!("(IRByteConfigV1.running W (IRMachine.mk (IRList.cons IRFrame (ir_frame_set_many (ir_frame_advance {PARENT}) byte_call_test_dests {VALUES}) tail) (IRList.nil IRMemSlot) cursor) (IRByteWorldV1.mk W (ir_byte_retire_v1 next memory) host owners (Nat.succ next)))");
        let return_guard = format!("(ir_byte_function_and_true_v1 (ir_byte_values_match_v1 byte_call_test_context byte_call_test_types {VALUES}) Bool.true {guard} (Eq.refl Bool Bool.true))");
        checked(&mut spec, &format!(
            "def byte_call_test_return {WORLD_PARAMS} {WORD_PARAMS} {} : Eq (IRByteConfigV1 W)\n\
              (ir_byte_return_v1 W byte_call_test_context {entered_machine} {entered_world} byte_call_test_args) {returned} :=\n\
              ir_byte_return_to_caller_v1 W byte_call_test_context {entered_frame} (ir_frame_advance {PARENT}) tail (IRList.nil IRMemSlot) cursor memory host next owners (Nat.succ next) byte_call_test_args byte_call_test_binding byte_call_test_signature {lookup} {signature} {return_guard}", range_params()
        ));
        checked(&mut spec, &format!(
            "def byte_call_test_readback {WORLD_PARAMS} {WORD_PARAMS} {} : Eq (IRList IRScalar)\n\
              (byte_call_test_result_lanes W (ir_byte_return_v1 W byte_call_test_context {entered_machine} {entered_world} byte_call_test_args)) {VALUES} :=\n\
              ir_eq_cong (IRByteConfigV1 W) (IRList IRScalar) (byte_call_test_result_lanes W)\n\
                (ir_byte_return_v1 W byte_call_test_context {entered_machine} {entered_world} byte_call_test_args) {returned}\n\
                (byte_call_test_return W memory host owners next tail locals cursor a b c d e ha hb hc hd he)", range_params()
        ));
    });
}
