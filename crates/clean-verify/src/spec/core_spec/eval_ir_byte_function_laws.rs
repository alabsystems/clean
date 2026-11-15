// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked function-pointer representation laws over the actual byte profile.
//!
//! Catalog hypotheses name both actual lookups, not an assumed roundtrip or
//! an instruction result. They are local coherence premises, not a proof of
//! global catalog uniqueness, native address fidelity, or publication authority.
//! The existing value matcher only checks the forward catalog; encoding and
//! decoding additionally require the coherent reverse lookup.

use crate::spec::{SpecError, Specification};

const BINDING: &str = "IRByteFunctionV1.mk fid sig address cc imported";
const BASE_PARAMS: &str =
    "(ctx : IRByteContextV1) (fid : Nat) (sig : Nat) (address : Nat) (cc : Nat) (imported : Bool)";
const FORWARD: &str = "(forward : @Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx fid) (@IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk fid sig address cc imported)))";
const REVERSE: &str = "(reverse : @Eq (IROption IRByteFunctionV1) (ir_byte_function_address_v1 ctx address) (@IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk fid sig address cc imported)))";
const BOUNDS: &str = "(positive : Nat.lt 0 address) (bounded : Nat.lt address ir_byte_limit_v1)";
const ARGS: &str = "ctx fid sig address cc imported forward reverse positive bounded";

// Use the checked agreement with the paired walk, not definitional reduction
// of the optimized comparison's subtraction implementation. The latter is a
// valid local unfolding but is not stable across the independent Lean replay
// bridge's comparison representation. Only the reference walk is inducted on;
// the machine comparison is connected by its actual equality theorem.
const EQ_SELF: &str = r"def ir_byte_function_nat_eq_self_v1 (n : Nat) :
  @Eq Bool (ir_nat_eqb n n) Bool.true :=
@Eq.trans Bool (ir_nat_eqb n n) (ir_nat_eqb_walk n n) Bool.true
  (ir_nat_eqb_walk_eq n n)
  (@Nat.rec (fun (k : Nat) => @Eq Bool (ir_nat_eqb_walk k k) Bool.true)
    (@Eq.refl Bool Bool.true)
    (fun (k : Nat) (ih : @Eq Bool (ir_nat_eqb_walk k k) Bool.true) => ih)
    n)";

const AND_TRUE: &str = r"def ir_byte_function_and_true_v1 (a : Bool) (b : Bool)
  (left : @Eq Bool a Bool.true) (right : @Eq Bool b Bool.true) :
  @Eq Bool (Bool.and a b) Bool.true :=
@Eq.trans Bool (Bool.and a b) (Bool.and Bool.true b) Bool.true
  (ir_eq_cong Bool Bool (fun (x : Bool) => Bool.and x b) a Bool.true left) right";

fn eq(ty: &str, left: &str, right: &str) -> String {
    format!("@Eq ({ty}) ({left}) ({right})")
}

fn trans(ty: &str, left: &str, middle: &str, right: &str, first: &str, second: &str) -> String {
    format!("@Eq.trans ({ty}) ({left}) ({middle}) ({right}) ({first}) ({second})")
}

fn congr(input: &str, output: &str, map: &str, left: &str, right: &str, proof: &str) -> String {
    format!("ir_eq_cong ({input}) ({output}) ({map}) ({left}) ({right}) ({proof})")
}

// These proof-term maps expose the actual eliminators, so congruence can replace
// lookup results. Their endpoints are checked against the production definitions.
fn eliminate(input: &str, output: &str, success: &str, value: &str) -> String {
    let payload = output.strip_prefix("IROption ").expect("option result");
    format!(
        "@IROption.rec ({input}) (fun (_ : IROption ({input})) => {output}) (@IROption.none {payload}) ({success}) ({value})"
    )
}

fn bool_case(output: &str, success: &str, guard: &str) -> String {
    let payload = output.strip_prefix("IROption ").expect("option result");
    format!(
        "@Bool.rec (fun (_ : Bool) => {output}) (@IROption.none {payload}) ({success}) ({guard})"
    )
}

fn and(clauses: &[String]) -> String {
    let (first, rest) = clauses.split_first().expect("nonempty conjunction");
    if rest.is_empty() {
        first.clone()
    } else {
        format!("Bool.and ({first}) ({})", and(rest))
    }
}

fn and_proof(clauses: &[(String, String)]) -> String {
    let ((first, proof), rest) = clauses.split_first().expect("nonempty conjunction");
    if rest.is_empty() {
        proof.clone()
    } else {
        let tail = and(&rest
            .iter()
            .map(|(term, _)| term.clone())
            .collect::<Vec<_>>());
        format!(
            "ir_byte_function_and_true_v1 ({first}) ({tail}) ({proof}) ({})",
            and_proof(rest)
        )
    }
}

fn guard_law(name: &str, params: &str, equalities: &[&str]) -> (String, String) {
    let mut clauses: Vec<_> = equalities
        .iter()
        .map(|term| {
            (
                format!("ir_nat_eqb {term} {term}"),
                format!("ir_byte_function_nat_eq_self_v1 {term}"),
            )
        })
        .collect();
    clauses.push((
        "ir_nat_pos address".into(),
        "ir_byte_ltb_of_lt_v1 0 address positive".into(),
    ));
    clauses.push((
        "ir_nat_ltb address ir_byte_limit_v1".into(),
        "ir_byte_ltb_of_lt_v1 address ir_byte_limit_v1 bounded".into(),
    ));
    let guard = and(&clauses
        .iter()
        .map(|(term, _)| term.clone())
        .collect::<Vec<_>>());
    let source = format!(
        "def {name} {params} {BOUNDS} : {} := {}",
        eq("Bool", &guard, "Bool.true"),
        and_proof(&clauses)
    );
    (guard, source)
}

fn function_word_guard(actual: &str, back: &str) -> String {
    and(&[
        format!("ir_nat_eqb (ir_byte_binding_fid_v1 {actual}) fid"),
        format!("ir_nat_eqb (ir_byte_binding_fid_v1 {back}) fid"),
        format!("ir_nat_eqb (ir_byte_binding_sig_v1 {back}) (ir_byte_binding_sig_v1 {actual})"),
        format!(
            "ir_nat_eqb (ir_byte_binding_address_v1 {back}) (ir_byte_binding_address_v1 {actual})"
        ),
        format!("ir_nat_pos (ir_byte_binding_address_v1 {actual})"),
        format!("ir_nat_ltb (ir_byte_binding_address_v1 {actual}) ir_byte_limit_v1"),
    ])
}

fn word_inner(actual: &str, lookup: &str) -> String {
    let success = format!("@IROption.some Nat (ir_byte_binding_address_v1 {actual})");
    let body = bool_case(
        "IROption Nat",
        &success,
        &function_word_guard(actual, "back"),
    );
    eliminate(
        "IRByteFunctionV1",
        "IROption Nat",
        &format!("fun (back : IRByteFunctionV1) => {body}"),
        lookup,
    )
}

fn catalog_laws() -> Vec<(&'static str, String)> {
    let params = format!("{BASE_PARAMS} {FORWARD} {REVERSE} {BOUNDS}");
    let (fit_guard, fit_guard_source) = guard_law(
        "ir_byte_function_fit_guard_v1",
        "(sig : Nat) (address : Nat)",
        &["sig"],
    );
    let (word_guard, word_guard_source) = guard_law(
        "ir_byte_function_word_guard_v1",
        "(fid : Nat) (sig : Nat) (address : Nat)",
        &["fid", "fid", "sig", "address"],
    );
    let binding_some = format!("@IROption.some IRByteFunctionV1 ({BINDING})");
    let encoded = "@IROption.some Nat address";
    let decoded = "@IROption.some IRScalar (IRScalar.fnptr_ fid)";

    let outer_success = format!(
        "fun (actual : IRByteFunctionV1) => {}",
        word_inner(
            "actual",
            "ir_byte_function_address_v1 ctx (ir_byte_binding_address_v1 actual)"
        )
    );
    let from_forward = format!(
        "fun (lookup : IROption IRByteFunctionV1) => {}",
        eliminate("IRByteFunctionV1", "IROption Nat", &outer_success, "lookup")
    );
    let from_reverse = format!(
        "fun (lookup : IROption IRByteFunctionV1) => {}",
        word_inner(&format!("({BINDING})"), "lookup")
    );
    let forward_reduced = format!("({from_forward}) ({binding_some})");
    let reverse_reduced = format!("({from_reverse}) ({binding_some})");
    let guard_map = format!(
        "fun (guard : Bool) => {}",
        bool_case("IROption Nat", encoded, "guard")
    );
    let first = congr(
        "IROption IRByteFunctionV1",
        "IROption Nat",
        &from_forward,
        "ir_byte_function_v1 ctx fid",
        &binding_some,
        "forward",
    );
    let second = congr(
        "IROption IRByteFunctionV1",
        "IROption Nat",
        &from_reverse,
        "ir_byte_function_address_v1 ctx address",
        &binding_some,
        "reverse",
    );
    let third = congr(
        "Bool",
        "IROption Nat",
        &guard_map,
        &word_guard,
        "Bool.true",
        "ir_byte_function_word_guard_v1 fid sig address positive bounded",
    );
    let word = format!(
        "def ir_byte_function_word_of_catalog_v1 {params} : {} := {}",
        eq("IROption Nat", "ir_byte_function_word_v1 ctx fid", encoded),
        trans(
            "IROption Nat",
            "ir_byte_function_word_v1 ctx fid",
            &forward_reduced,
            encoded,
            &first,
            &trans(
                "IROption Nat",
                &forward_reduced,
                &reverse_reduced,
                encoded,
                &second,
                &third
            )
        )
    );

    let decode_guard = and(&[
        "ir_nat_eqb address address".into(),
        "ir_nat_eqb sig sig".into(),
    ]);
    let actual_guard = and(&[
        "ir_nat_eqb word address".into(),
        "ir_nat_eqb sig (ir_byte_binding_sig_v1 actual)".into(),
    ]);
    let decode_actual = bool_case(
        "IROption IRScalar",
        "@IROption.some IRScalar (IRScalar.fnptr_ (ir_byte_binding_fid_v1 actual))",
        &actual_guard,
    );
    let decode_inner = eliminate(
        "Nat",
        "IROption IRScalar",
        &format!("fun (word : Nat) => {decode_actual}"),
        "ir_byte_function_word_v1 ctx (ir_byte_binding_fid_v1 actual)",
    );
    let decode_outer = format!(
        "fun (lookup : IROption IRByteFunctionV1) => {}",
        eliminate(
            "IRByteFunctionV1",
            "IROption IRScalar",
            &format!("fun (actual : IRByteFunctionV1) => {decode_inner}"),
            "lookup"
        )
    );
    let guard_with_word = and(&[
        "ir_nat_eqb word address".into(),
        "ir_nat_eqb sig sig".into(),
    ]);
    let from_word = format!(
        "fun (lookup : IROption Nat) => {}",
        eliminate(
            "Nat",
            "IROption IRScalar",
            &format!(
                "fun (word : Nat) => {}",
                bool_case("IROption IRScalar", decoded, &guard_with_word)
            ),
            "lookup"
        )
    );
    let reverse_reduced = format!("({decode_outer}) ({binding_some})");
    let word_reduced = format!("({from_word}) ({encoded})");
    let first = congr(
        "IROption IRByteFunctionV1",
        "IROption IRScalar",
        &decode_outer,
        "ir_byte_function_address_v1 ctx address",
        &binding_some,
        "reverse",
    );
    let second = congr(
        "IROption Nat",
        "IROption IRScalar",
        &from_word,
        "ir_byte_function_word_v1 ctx fid",
        encoded,
        &format!("ir_byte_function_word_of_catalog_v1 {ARGS}"),
    );
    let guard_proof = and_proof(&[
        (
            "ir_nat_eqb address address".into(),
            "ir_byte_function_nat_eq_self_v1 address".into(),
        ),
        (
            "ir_nat_eqb sig sig".into(),
            "ir_byte_function_nat_eq_self_v1 sig".into(),
        ),
    ]);
    let third = congr(
        "Bool",
        "IROption IRScalar",
        &format!(
            "fun (guard : Bool) => {}",
            bool_case("IROption IRScalar", decoded, "guard")
        ),
        &decode_guard,
        "Bool.true",
        &guard_proof,
    );
    let decode = format!(
        "def ir_byte_function_decode_of_catalog_v1 {params} : {} := {}",
        eq(
            "IROption IRScalar",
            "ir_byte_decode_function_v1 ctx sig address",
            decoded
        ),
        trans(
            "IROption IRScalar",
            "ir_byte_decode_function_v1 ctx sig address",
            &reverse_reduced,
            decoded,
            &first,
            &trans(
                "IROption IRScalar",
                &reverse_reduced,
                &word_reduced,
                decoded,
                &second,
                &third
            )
        )
    );

    let fit_actual = and(&[
        "ir_nat_eqb sig (ir_byte_binding_sig_v1 actual)".into(),
        "ir_nat_pos (ir_byte_binding_address_v1 actual)".into(),
        "ir_nat_ltb (ir_byte_binding_address_v1 actual) (ir_nat_pow2 64)".into(),
    ]);
    let fit_map = format!(
        "fun (lookup : IROption IRByteFunctionV1) => @IROption.rec IRByteFunctionV1 (fun (_ : IROption IRByteFunctionV1) => Bool) Bool.false (fun (actual : IRByteFunctionV1) => {fit_actual}) lookup"
    );
    let fit_step = congr(
        "IROption IRByteFunctionV1",
        "Bool",
        &fit_map,
        "ir_byte_function_v1 ctx fid",
        &binding_some,
        "forward",
    );
    let fits = format!(
        "def ir_byte_function_fits_of_catalog_v1 {BASE_PARAMS} {FORWARD} {BOUNDS} : {} := {}",
        eq(
            "Bool",
            "ir_byte_function_fits_v1 ctx (IRTy.func_ sig) fid",
            "Bool.true"
        ),
        trans(
            "Bool",
            "ir_byte_function_fits_v1 ctx (IRTy.func_ sig) fid",
            &fit_guard,
            "Bool.true",
            &fit_step,
            "ir_byte_function_fit_guard_v1 sig address positive bounded"
        )
    );
    let scalar_word = format!(
        "def ir_byte_function_scalar_word_of_catalog_v1 {params} : {} := ir_byte_function_word_of_catalog_v1 {ARGS}",
        eq(
            "IROption Nat",
            "ir_byte_scalar_word_v1 ctx (IRScalar.fnptr_ fid)",
            encoded
        )
    );
    let decode_word = format!(
        "def ir_byte_function_decode_word_of_catalog_v1 {params} : {} := ir_byte_function_decode_of_catalog_v1 {ARGS}",
        eq(
            "IROption IRScalar",
            "ir_byte_decode_word_v1 ctx (IRTy.func_ sig) address",
            decoded
        )
    );
    let value_fits = format!(
        "def ir_byte_function_value_matches_of_catalog_v1 {BASE_PARAMS} {FORWARD} {BOUNDS} : {} := ir_byte_function_fits_of_catalog_v1 ctx fid sig address cc imported forward positive bounded",
        eq(
            "Bool",
            "ir_byte_value_matches_v1 ctx (IRTy.func_ sig) (IRScalar.fnptr_ fid)",
            "Bool.true"
        )
    );
    let roundtrip_map = format!(
        "fun (lookup : IROption Nat) => {}",
        eliminate(
            "Nat",
            "IROption IRScalar",
            "fun (word : Nat) => ir_byte_decode_function_v1 ctx sig word",
            "lookup"
        )
    );
    let roundtrip_start = format!("({roundtrip_map}) (ir_byte_function_word_v1 ctx fid)");
    let roundtrip_step = congr(
        "IROption Nat",
        "IROption IRScalar",
        &roundtrip_map,
        "ir_byte_function_word_v1 ctx fid",
        encoded,
        &format!("ir_byte_function_word_of_catalog_v1 {ARGS}"),
    );
    let roundtrip = format!(
        "def ir_byte_function_roundtrip_of_catalog_v1 {params} : {} := {}",
        eq("IROption IRScalar", &roundtrip_start, decoded),
        trans(
            "IROption IRScalar",
            &roundtrip_start,
            "ir_byte_decode_function_v1 ctx sig address",
            decoded,
            &roundtrip_step,
            &format!("ir_byte_function_decode_of_catalog_v1 {ARGS}")
        )
    );
    vec![
        ("ir_byte_function_nat_eq_self_v1", EQ_SELF.into()),
        ("ir_byte_function_and_true_v1", AND_TRUE.into()),
        ("ir_byte_function_fit_guard_v1", fit_guard_source),
        ("ir_byte_function_word_guard_v1", word_guard_source),
        ("ir_byte_function_word_of_catalog_v1", word),
        ("ir_byte_function_decode_of_catalog_v1", decode),
        ("ir_byte_function_fits_of_catalog_v1", fits),
        ("ir_byte_function_scalar_word_of_catalog_v1", scalar_word),
        ("ir_byte_function_decode_word_of_catalog_v1", decode_word),
        ("ir_byte_function_value_matches_of_catalog_v1", value_fits),
        ("ir_byte_function_roundtrip_of_catalog_v1", roundtrip),
    ]
}

impl Specification {
    pub(super) fn add_eval_ir_byte_function_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in catalog_laws() {
            self.add_recursive_def(&source, "Checked exact function catalog representation law; no roundtrip or native-fidelity axiom.")
                .map_err(|error| match error {
                    SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    SpecError::EnvError(detail) => SpecError::EnvError(format!("{name}: {detail}")),
                    other => other,
                })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn spec() -> Specification {
        Specification::new_eval_ir_byte_prelude_spec_v1()
            .expect("actual public checked byte-profile prelude")
    }

    fn assert_checked(spec: &Specification, name: &str) {
        let definition = spec.get_definition(name).expect("registered checked term");
        assert!(!definition.is_axiom);
        assert!(definition.elaborated_value.is_some());
        spec.verify_definition(name)
            .expect("independent rooted kernel replay");
        let name = Name::from_string(name);
        assert!(spec
            .env()
            .axiom_deps(&name)
            .expect("root exists")
            .is_empty());
        assert!(spec
            .env()
            .trust_marker_deps(&name)
            .expect("root exists")
            .is_empty());
    }

    fn witness(spec: &mut Specification, name: &str, source: &str) {
        spec.add_recursive_def(source, "Actual function-catalog theorem consumer")
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_checked(spec, name);
    }

    fn context(spec: &mut Specification, name: &str, entries: &[(u64, u64, u128)]) {
        let functions = entries.iter().rev().fold("@IRList.nil IRByteFunctionV1".to_owned(), |tail, &(fid, sig, address)| {
            format!("@IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk {fid} {sig} {address} 1 Bool.false) ({tail})")
        });
        witness(
            spec,
            name,
            &format!(
                "def {name} : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)) (@IRList.nil IRByteLayoutV1) (@IRList.nil IRByteSignatureV1) ({functions}) (@IRList.nil IRByteSiteV1)"
            ),
        );
    }

    fn observation(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
        witness(
            spec,
            name,
            &format!(
                "def {name} : {} := @Eq.refl ({ty}) ({expected})",
                eq(ty, actual, expected)
            ),
        );
    }

    fn reject_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Deliberately invalid function-catalog claim")
            .expect_err("wrong identity, signature, or address must not be certified");
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn quantified_function_laws_replay_without_axioms_or_trust_markers() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for (name, _) in catalog_laws() {
                assert_checked(&spec, name);
            }
        });
    }

    #[test]
    fn nat_self_equality_uses_checked_walk_agreement_and_rejects_wrong_answers() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_eval_ir_prelude_spec()
                .expect("actual comparison definitions and agreement laws");
            let root = "ir_byte_function_nat_eq_self_v1";
            witness(&mut spec, root, EQ_SELF);
            let dependencies = spec
                .get_definition(root)
                .expect("registered proof")
                .elaborated_value
                .as_ref()
                .expect("checked proof body")
                .collect_constants();
            assert!(
                dependencies.contains(&Name::from_string("ir_nat_eqb_walk_eq")),
                "replay must use the checked comparison agreement, not fragile unfolding"
            );
            witness(
                &mut spec,
                "byte_function_self_symbolic",
                "def byte_function_self_symbolic (n : Nat) : @Eq Bool (ir_nat_eqb n n) Bool.true := ir_byte_function_nat_eq_self_v1 n",
            );
            for (index, value) in [0_u64, 7, u64::MAX].into_iter().enumerate() {
                let name = format!("byte_function_self_concrete_{index}");
                witness(
                    &mut spec,
                    &name,
                    &format!(
                        "def {name} : @Eq Bool (ir_nat_eqb {value} {value}) Bool.true := ir_byte_function_nat_eq_self_v1 {value}"
                    ),
                );
            }
            for (name, source) in [
                (
                    "byte_function_self_wrong_bool",
                    "def byte_function_self_wrong_bool : @Eq Bool (ir_nat_eqb 42 42) Bool.false := ir_byte_function_nat_eq_self_v1 42",
                ),
                (
                    "byte_function_self_wrong_argument",
                    "def byte_function_self_wrong_argument : @Eq Bool (ir_nat_eqb 42 43) Bool.true := ir_byte_function_nat_eq_self_v1 42",
                ),
            ] {
                reject_type_mismatch(&mut spec, name, source);
            }
        });
    }

    #[test]
    fn generic_slot_consumer_preserves_exact_identity_and_signature() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            let params = format!("{BASE_PARAMS} {FORWARD} {REVERSE} {BOUNDS}");
            let actual = eliminate(
                "Nat",
                "IROption IRScalar",
                "fun (word : Nat) => ir_byte_decode_word_v1 ctx (IRTy.func_ sig) word",
                "ir_byte_scalar_word_v1 ctx (IRScalar.fnptr_ fid)",
            );
            witness(
                &mut spec,
                "byte_function_generic_slot",
                &format!(
                    "def byte_function_generic_slot {params} : {} := ir_byte_function_roundtrip_of_catalog_v1 {ARGS}",
                    eq(
                        "IROption IRScalar",
                        &actual,
                        "@IROption.some IRScalar (IRScalar.fnptr_ fid)"
                    )
                ),
            );
            witness(
                &mut spec,
                "byte_function_generic_match",
                &format!(
                    "def byte_function_generic_match {params} : {} := ir_byte_function_value_matches_of_catalog_v1 ctx fid sig address cc imported forward positive bounded",
                    eq(
                        "Bool",
                        "ir_byte_value_matches_v1 ctx (IRTy.func_ sig) (IRScalar.fnptr_ fid)",
                        "Bool.true"
                    )
                ),
            );
        });
    }

    #[test]
    fn catalogs_support_sparse_ids_and_full_width_nonzero_addresses() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            context(
                &mut spec,
                "byte_function_sparse",
                &[(41, 17, u64::MAX as u128), (7, 90, 4096)],
            );
            for (name, ty, actual, expected) in [
                (
                    "byte_function_max_word",
                    "IROption Nat",
                    "ir_byte_function_word_v1 byte_function_sparse 41",
                    "@IROption.some Nat 18446744073709551615",
                ),
                (
                    "byte_function_max_decode",
                    "IROption IRScalar",
                    "ir_byte_decode_function_v1 byte_function_sparse 17 18446744073709551615",
                    "@IROption.some IRScalar (IRScalar.fnptr_ 41)",
                ),
                (
                    "byte_function_sparse_decode",
                    "IROption IRScalar",
                    "ir_byte_decode_word_v1 byte_function_sparse (IRTy.func_ 90) 4096",
                    "@IROption.some IRScalar (IRScalar.fnptr_ 7)",
                ),
                (
                    "byte_function_max_match",
                    "Bool",
                    "ir_byte_value_matches_v1 byte_function_sparse (IRTy.func_ 17) (IRScalar.fnptr_ 41)",
                    "Bool.true",
                ),
            ] {
                observation(&mut spec, name, ty, actual, expected);
            }
        });
    }

    #[test]
    fn wrong_signature_reverse_alias_and_address_are_not_roundtrips() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            context(&mut spec, "byte_function_good", &[(5, 7, 4096)]);
            context(
                &mut spec,
                "byte_function_alias",
                &[(6, 7, 4096), (5, 7, 4096)],
            );
            context(&mut spec, "byte_function_zero", &[(5, 7, 0)]);
            context(&mut spec, "byte_function_overflow", &[(5, 7, 1_u128 << 64)]);
            // The operational catalog chooses its first match. In the malformed
            // alias context, 6 owns the reverse lookup: decoding must not invent
            // identity 5. Forward-only value typing intentionally still succeeds.
            for (name, ty, actual, expected) in [
                (
                    "byte_function_wrong_sig_none",
                    "IROption IRScalar",
                    "ir_byte_decode_function_v1 byte_function_good 8 4096",
                    "@IROption.none IRScalar",
                ),
                (
                    "byte_function_alias_word_none",
                    "IROption Nat",
                    "ir_byte_function_word_v1 byte_function_alias 5",
                    "@IROption.none Nat",
                ),
                (
                    "byte_function_alias_is_first",
                    "IROption IRScalar",
                    "ir_byte_decode_function_v1 byte_function_alias 7 4096",
                    "@IROption.some IRScalar (IRScalar.fnptr_ 6)",
                ),
                (
                    "byte_function_missing_none",
                    "IROption IRScalar",
                    "ir_byte_decode_function_v1 byte_function_good 7 4097",
                    "@IROption.none IRScalar",
                ),
                (
                    "byte_function_zero_none",
                    "IROption Nat",
                    "ir_byte_function_word_v1 byte_function_zero 5",
                    "@IROption.none Nat",
                ),
                (
                    "byte_function_overflow_none",
                    "IROption Nat",
                    "ir_byte_function_word_v1 byte_function_overflow 5",
                    "@IROption.none Nat",
                ),
                (
                    "byte_function_fit_is_not_encoding",
                    "Bool",
                    "ir_byte_value_matches_v1 byte_function_alias (IRTy.func_ 7) (IRScalar.fnptr_ 5)",
                    "Bool.true",
                ),
            ] {
                observation(&mut spec, name, ty, actual, expected);
            }
            for (name, actual) in [
                (
                    "byte_function_bad_signature",
                    "ir_byte_decode_function_v1 byte_function_good 8 4096",
                ),
                (
                    "byte_function_bad_alias",
                    "ir_byte_decode_function_v1 byte_function_alias 7 4096",
                ),
                (
                    "byte_function_bad_address",
                    "ir_byte_decode_function_v1 byte_function_good 7 4097",
                ),
            ] {
                reject_type_mismatch(
                    &mut spec,
                    name,
                    &format!(
                        "def {name} : {} := @Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.fnptr_ 5))",
                        eq(
                            "IROption IRScalar",
                            actual,
                            "@IROption.some IRScalar (IRScalar.fnptr_ 5)"
                        )
                    ),
                );
            }
        });
    }
}
