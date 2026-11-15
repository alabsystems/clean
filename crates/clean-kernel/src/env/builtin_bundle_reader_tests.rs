// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Corrupt source records must fail without publishing any checked prefix.

use super::*;
use serde_json::json;

const NAT: &[u8] = include_bytes!("builtin_data/nat-core-lean-4.35.0.json");

fn packet() -> Value {
    serde_json::from_slice(NAT).expect("source bundle JSON")
}
fn decl_index(packet: &Value, wanted: &str) -> usize {
    packet["declarations"]
        .as_array()
        .expect("declarations")
        .iter()
        .position(|decl| name(&decl["name"], 0).expect("name").to_string() == wanted)
        .expect("source declaration")
}
fn encoded(packet: &Value) -> Vec<u8> {
    serde_json::to_vec(packet).expect("encode mutation")
}
fn baseline() -> Environment {
    // Reader-only extraction: admit the genuine source into a fresh world;
    // the unchanged default Nat producer is outside this test's claim.
    let mut env = Environment::for_lean_replay();
    admit(
        &mut env,
        NAT,
        &[
            "Nat.casesOn",
            "Nat.recOn",
            "Nat.noConfusion",
            "Nat.below",
            "Nat.brecOn",
            "Nat.add",
        ],
    )
    .expect("genuine checked Nat packet");
    env.init_punit().expect("PUnit");
    env.init_pprod().expect("PProd");
    env
}
fn assert_refused_atomically(env: &mut Environment, packet: &Value, reason: &str) {
    let before = env.content_digest();
    let generation = env.generation;
    let error = admit(env, &encoded(packet), &["Nat.add"]).expect_err("corrupt record refused");
    assert!(error.to_string().contains(reason), "{error}");
    assert_eq!(env.content_digest(), before, "no checked prefix may escape");
    assert_eq!(env.generation, generation);
}

#[test]
fn exact_source_records_match_even_after_pprod_was_initialized() {
    let mut env = baseline();
    let before = env.content_digest();
    admit(
        &mut env,
        NAT,
        &[
            "Nat.casesOn",
            "Nat.recOn",
            "Nat.noConfusion",
            "Nat.below",
            "Nat.brecOn",
            "Nat.add",
        ],
    )
    .expect("all source records match existing checked declarations");
    assert_eq!(env.content_digest(), before);
    assert!(env
        .axiom_deps(&Name::from_string("Nat.add"))
        .expect("closure")
        .is_empty());
}

#[test]
fn new_axiom_is_refused_after_the_family_prefix_was_checked() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.add");
    packet["declarations"][decl]["kind"] = json!("axiom");
    packet["declarations"][decl]
        .as_object_mut()
        .expect("record")
        .remove("value");
    let mut env = Environment::for_lean_replay();
    assert_refused_atomically(&mut env, &packet, "new axiom");
    assert!(env.get_const(&Name::from_string("Nat")).is_none());
}

#[test]
fn wrong_value_type_is_refused_without_publishing_the_family() {
    let mut packet = packet();
    let zero = packet["expressions"]
        .as_array()
        .expect("nodes")
        .iter()
        .position(|node| {
            node[0] == "const" && name(&node[1], 0).is_ok_and(|n| n.to_string() == "Nat.zero")
        })
        .expect("zero expression");
    let decl = decl_index(&packet, "Nat.add");
    packet["declarations"][decl]["value"] = json!(zero);
    let mut env = Environment::for_lean_replay();
    assert_refused_atomically(&mut env, &packet, "Nat.add");
    assert!(env.get_const(&Name::from_string("Nat")).is_none());
}

#[test]
fn same_typed_existing_computation_must_match_the_source_body() {
    let mut packet = packet();
    let nat = packet["expressions"]
        .as_array()
        .expect("nodes")
        .iter()
        .position(|node| {
            node[0] == "const" && name(&node[1], 0).is_ok_and(|n| n.to_string() == "Nat")
        })
        .expect("Nat expression");
    let nodes = packet["expressions"].as_array_mut().expect("nodes");
    let first = nodes.len();
    nodes.push(json!(["bvar", 1]));
    nodes.push(json!(["lam", ["anon"], "default", nat, first]));
    nodes.push(json!(["lam", ["anon"], "default", nat, first + 1]));
    let decl = decl_index(&packet, "Nat.add");
    packet["declarations"][decl]["value"] = json!(first + 2);
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "existing computational body differs",
    );
}

#[test]
fn same_typed_family_cannot_reorder_its_constructors() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat");
    packet["declarations"][decl]["constructors"]
        .as_array_mut()
        .expect("constructors")
        .swap(0, 1);
    assert_refused_atomically(&mut baseline(), &packet, "constructor list differs");
}

#[test]
fn recursor_rhs_annotations_are_part_of_the_checked_packet() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.rec");
    let rhs = packet["declarations"][decl]["rules"][0]["rhs"]
        .as_u64()
        .expect("rhs") as usize;
    let mut mutated = packet["expressions"][rhs].clone();
    assert_eq!(mutated[0], "lam");
    let nodes = packet["expressions"].as_array_mut().expect("nodes");
    let prop = nodes.len();
    nodes.push(json!(["sort", ["zero"]]));
    mutated[3] = json!(prop);
    let value = nodes.len();
    nodes.push(mutated);
    packet["declarations"][decl]["rules"][0]["rhs"] = json!(value);
    assert_refused_atomically(&mut baseline(), &packet, "Nat.rec");
}

fn proof_packet() -> (Value, Name, Expr, Expr) {
    let mut packet = packet();
    let nodes = packet["expressions"].as_array_mut().expect("nodes");
    let nat = nodes
        .iter()
        .position(|e| e[0] == "const" && name(&e[1], 0).is_ok_and(|n| n.to_string() == "Nat"))
        .expect("Nat");
    let zero = nodes
        .iter()
        .position(|e| e[0] == "const" && name(&e[1], 0).is_ok_and(|n| n.to_string() == "Nat.zero"))
        .expect("zero");
    let eq = nodes.len();
    nodes.push(json!([
        "const",
        ["str", ["anon"], "Eq"],
        [["succ", ["zero"]]]
    ]));
    nodes.push(json!(["app", eq, nat]));
    nodes.push(json!(["app", eq + 1, zero]));
    nodes.push(json!(["app", eq + 2, zero]));
    let refl = nodes.len();
    nodes.push(json!([
        "const",
        ["str", ["str", ["anon"], "Eq"], "refl"],
        [["succ", ["zero"]]]
    ]));
    nodes.push(json!(["app", refl, nat]));
    nodes.push(json!(["app", refl + 1, zero]));
    packet["declarations"]
        .as_array_mut()
        .expect("declarations")
        .push(json!({
            "name": ["str", ["anon"], "BundleProof"], "kind": "theorem", "levels": [],
            "type": eq + 3, "value": refl + 2, "noncomputable": false
        }));
    packet["roots"]
        .as_array_mut()
        .expect("roots")
        .push(json!(["str", ["anon"], "BundleProof"]));
    let nodes = expressions(&packet["expressions"]).expect("proof nodes");
    (
        packet,
        Name::from_string("BundleProof"),
        nodes[eq + 3].clone(),
        nodes[refl + 2].clone(),
    )
}

#[test]
fn a_resident_theorem_kind_without_a_proof_cannot_satisfy_a_root() {
    let (packet, name, type_, value) = proof_packet();
    let mut env = baseline();
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
    })
    .expect("checked proof");
    // Adversarial malformed resident: even a stale FullKernelCheck stamp may
    // never excuse an absent proof payload.
    env.constants.get_mut(&name).expect("resident").value = None;
    let before = env.content_digest();
    let error = admit(&mut env, &encoded(&packet), &["BundleProof"]).expect_err("proof absent");
    assert!(error.to_string().contains("proof absent"), "{error}");
    assert_eq!(env.content_digest(), before);
}

#[test]
fn unverified_value_bearing_residents_cannot_be_reused() {
    use super::super::DeclarationVerification::{StructuralOnly, Unchecked};
    for provenance in [Some(Unchecked), Some(StructuralOnly), None] {
        let mut env = baseline();
        let name = Name::from_string("Nat.add");
        if let Some(provenance) = provenance {
            env.declaration_verification.insert(name, provenance);
        } else {
            env.declaration_verification.remove(&name);
        }
        assert_refused_atomically(&mut env, &packet(), "FullKernelCheck provenance");
    }
}

#[test]
fn alternate_checked_proofs_are_audited_through_their_actual_dependencies() {
    use super::super::DeclarationVerification::Unchecked;
    let (packet, name, type_, value) = proof_packet();
    let helper = Name::from_string("BundleProofHelper");
    let mut env = baseline();
    env.add_decl(Declaration::Definition {
        name: helper.clone(),
        level_params: vec![],
        type_: type_.clone(),
        value,
        is_reducible: false,
    })
    .expect("checked helper proof");
    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_,
        value: Expr::const_(helper.clone(), vec![]),
    })
    .expect("alternate checked proof");
    admit(&mut env, &encoded(&packet), &["BundleProof"]).expect("checked alternate proof is valid");
    env.declaration_verification.insert(helper, Unchecked);
    let before = env.content_digest();
    let error = admit(&mut env, &encoded(&packet), &["BundleProof"])
        .expect_err("unchecked alternate dependency");
    assert!(
        error
            .to_string()
            .contains("BundleProofHelper: resident lacks FullKernelCheck"),
        "{error}"
    );
    assert_eq!(env.content_digest(), before);
}

#[test]
fn computational_reuse_preserves_the_definition_reducibility_policy() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.add");
    packet["declarations"][decl]["reducible"] = json!(true);
    packet["declarations"][decl]["source_reducibility"] = json!("[reducible]");
    assert_refused_atomically(&mut baseline(), &packet, "reducibility policy differs");
}

#[test]
fn computational_reuse_preserves_borrowed_type_metadata() {
    let mut packet = packet();
    let annotation = packet["expressions"]
        .as_array()
        .expect("nodes")
        .iter()
        .position(|e| e[0] == "mdata")
        .expect("borrowed marker");
    packet["expressions"][annotation][1][0][1][1] = json!(false);
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "type binder/metadata policy differs",
    );
}

#[test]
fn computational_reuse_preserves_value_metadata_positions() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.add");
    let old = packet["declarations"][decl]["value"].clone();
    let nodes = packet["expressions"].as_array_mut().expect("nodes");
    let new = nodes.len();
    nodes.push(json!([
        "mdata",
        [[["str", ["anon"], "borrowed"], ["bool", true]]],
        old
    ]));
    packet["declarations"][decl]["value"] = json!(new);
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "computational binder/metadata policy differs",
    );
}

#[test]
fn a_request_outside_the_static_root_contract_is_refused() {
    let mut env = baseline();
    let before = env.content_digest();
    let error = admit(&mut env, NAT, &["Nat.mul"]).expect_err("undeclared root");
    assert!(error.to_string().contains("root contract"), "{error}");
    assert_eq!(env.content_digest(), before);
}

#[test]
fn unknown_or_unrecorded_metadata_normalization_is_refused() {
    let mut packet = packet();
    packet["normalizations"] = json!([]);
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "unrecorded metadata normalization",
    );
}

#[test]
fn unknown_source_reducibility_is_refused_without_publishing_a_prefix() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.add");
    packet["declarations"][decl]["source_reducibility"] = json!("[unknown_future_status]");
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "unsupported source reducibility status",
    );
}

#[test]
fn an_inconsistent_eager_projection_is_refused_without_publishing_a_prefix() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.add");
    packet["declarations"][decl]["reducible"] = json!(true);
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "inconsistent source reducibility projection",
    );
}

const LIST: &[u8] = include_bytes!("builtin_data/list-core-lean-4.35.0.json");

#[test]
fn source_headers_install_type_binder_kinds_and_constructor_names() {
    // Reader-only scope: genuine source admission, without default List migration.
    let mut env = Environment::for_lean_replay();
    admit(
        &mut env,
        LIST,
        &[
            "List.length",
            "List.concat",
            "List.append",
            "List.map",
            "List.foldl",
            "List.foldr",
        ],
    )
    .expect("checked source List");
    let h_add = Name::from_string("HAdd.hAdd");
    assert_eq!(
        env.get_param_binder_infos(&h_add)
            .expect("source type metadata"),
        &[
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            BinderInfo::InstImplicit,
            BinderInfo::Default,
            BinderInfo::Default,
        ]
    );
    // Generated projection VALUE lambdas intentionally differ from the TYPE's
    // implicit α/β binders. Named applications must use the public type.
    assert_eq!(
        env.get_typed_param_names(&Name::from_string("List.cons"))
            .expect("constructor header"),
        &[
            Name::from_string("α"),
            Name::from_string("head"),
            Name::from_string("tail"),
        ]
    );
}

#[test]
fn source_headers_preserve_numeric_identity_and_unfolded_forall_names() {
    let mut packet = packet();
    let nodes = packet["expressions"].as_array_mut().expect("nodes");
    let start = nodes.len();
    nodes.push(json!(["sort", ["zero"]]));
    nodes.push(json!(["bvar", 0]));
    nodes.push(json!(["bvar", 1]));
    nodes.push(json!([
        "pi",
        ["str", ["anon"], "hyp"],
        "default",
        start + 1,
        start + 2
    ]));
    nodes.push(json!([
        "lam",
        ["str", ["anon"], "p"],
        "default",
        start,
        start + 3
    ]));
    nodes.push(json!([
        "pi",
        ["num", ["str", ["anon"], "p"], 7],
        "default",
        start,
        start
    ]));
    packet["declarations"]
        .as_array_mut()
        .expect("declarations")
        .push(json!({
            "name": ["str", ["anon"], "HeaderPredicate"], "kind": "definition", "levels": [],
            "type": start + 5, "value": start + 4, "reducible": false,
            "hints": ["regular", 1], "source_reducibility": "[semireducible]", "noncomputable": false
        }));
    packet["roots"].as_array_mut().expect("roots").push(json!([
        "str",
        ["anon"],
        "HeaderPredicate"
    ]));
    let mut env = Environment::for_lean_replay();
    admit(&mut env, &encoded(&packet), &["HeaderPredicate"]).expect("checked predicate alias");
    let name = Name::from_string("HeaderPredicate");
    assert_eq!(
        env.get_typed_param_names(&name).expect("typed binder"),
        &[Name::from_string("p").num(7)]
    );
    let value = env
        .get_value_forall_binder_names(&name)
        .expect("unfolded forall metadata");
    assert_eq!(value.lambdas, 1);
    assert_eq!(value.names, vec![Name::from_string("hyp")]);
}

#[test]
fn malformed_source_binder_identity_is_refused_atomically() {
    let mut packet = packet();
    let decl = decl_index(&packet, "Nat.add");
    let type_id = packet["declarations"][decl]["type"].as_u64().expect("type") as usize;
    assert_eq!(packet["expressions"][type_id][0], "pi");
    packet["expressions"][type_id][1] = json!("invalid-name-node");
    assert_refused_atomically(&mut baseline(), &packet, "expected array");
}

#[test]
fn source_noncomputable_tags_are_installed_after_checked_admission() {
    let mut packet = packet();
    let add = decl_index(&packet, "Nat.add");
    packet["declarations"][add]["noncomputable"] = json!(true);
    let mut env = Environment::for_lean_replay();
    admit(&mut env, &encoded(&packet), &["Nat.add"]).expect("checked noncomputable definition");
    assert!(env.is_noncomputable(&Name::from_string("Nat.add")));
    assert!(env
        .axiom_deps(&Name::from_string("Nat.add"))
        .expect("checked closure")
        .is_empty());
}

#[test]
fn computational_reuse_preserves_noncomputable_policy() {
    let mut env = baseline();
    env.mark_noncomputable(Name::from_string("Nat.add"));
    assert_refused_atomically(&mut env, &packet(), "existing noncomputable policy differs");
}

#[test]
fn missing_or_malformed_noncomputable_tags_are_refused_atomically() {
    for value in [None, Some(json!("false"))] {
        let mut packet = packet();
        let add = decl_index(&packet, "Nat.add");
        let record = packet["declarations"][add].as_object_mut().expect("record");
        match value {
            Some(value) => {
                record.insert("noncomputable".into(), value);
            }
            None => {
                record.remove("noncomputable");
            }
        }
        assert_refused_atomically(&mut baseline(), &packet, "noncomputable");
    }
}

#[test]
fn checked_placeholder_upgrade_replaces_stale_noncomputable_tag() {
    let (packet, name, ty, _) = proof_packet();
    let mut env = baseline();
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: ty,
    })
    .expect("value-free placeholder");
    env.mark_noncomputable(name.clone());
    admit(&mut env, &encoded(&packet), &["BundleProof"]).expect("checked proof upgrade");
    assert!(!env.is_noncomputable(&name));
    assert_eq!(
        env.declaration_verification(&name),
        Some(crate::DeclarationVerification::FullKernelCheck)
    );
    assert!(env
        .axiom_deps(&name)
        .expect("actual proof closure")
        .is_empty());
}

#[test]
fn an_old_packet_without_compilation_tags_is_not_silently_replayed() {
    let mut packet = packet();
    packet["schema"] = json!("clean-checked-declaration-dag-2");
    assert_refused_atomically(&mut baseline(), &packet, "unsupported schema");
}

#[test]
fn actual_irreducible_policy_keeps_checked_value_and_kernel_reduction() {
    let mut packet = packet();
    let add = decl_index(&packet, "Nat.add");
    packet["declarations"][add]["source_reducibility"] = json!("[irreducible]");
    let mut env = Environment::for_lean_replay();
    admit(&mut env, &encoded(&packet), &["Nat.add"]).expect("checked irreducible definition");
    let name = Name::from_string("Nat.add");
    assert_eq!(
        env.get_reducibility(&name),
        Some(super::super::Reducibility::Irreducible)
    );
    assert!(env.get_const(&name).expect("definition").value.is_some());
    assert_eq!(
        env.declaration_verification(&name),
        Some(crate::DeclarationVerification::FullKernelCheck)
    );
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(TypeChecker::new(&env).is_def_eq(
        &Expr::apps(Expr::const_(name, vec![]), [zero.clone(), zero.clone()]),
        &zero,
    ));
    let before = env.content_digest();
    let generation = env.generation;
    admit(&mut env, &encoded(&packet), &["Nat.add"]).expect("idempotent policy reuse");
    assert_eq!(env.content_digest(), before);
    assert_eq!(env.generation, generation);
}

#[test]
fn existing_regular_definition_cannot_satisfy_irreducible_source_policy() {
    let mut packet = packet();
    let add = decl_index(&packet, "Nat.add");
    packet["declarations"][add]["source_reducibility"] = json!("[irreducible]");
    assert_refused_atomically(&mut baseline(), &packet, "reducibility policy differs");
}

#[test]
fn unsupported_irreducible_abbreviation_policy_is_refused() {
    let mut packet = packet();
    let add = decl_index(&packet, "Nat.add");
    packet["declarations"][add]["source_reducibility"] = json!("[irreducible]");
    packet["declarations"][add]["hints"] = json!(["abbrev"]);
    packet["declarations"][add]["reducible"] = json!(true);
    assert_refused_atomically(
        &mut baseline(),
        &packet,
        "unsupported irreducible abbreviation policy",
    );
}
