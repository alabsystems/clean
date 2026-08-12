// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick P1 — Lean-core class heads registered in the kernel prelude.
//!
//! End-to-end (parse → elaborate → kernel re-check) coverage for the heads
//! registered by Brick P1: `id`, `Functor` (map/mapConst/mapRev),
//! `Seq`/`SeqLeft`/`SeqRight`, `HAndThen`/`HOrElse`, the `Bind` combinators
//! (`=<<`/`>=>`/`<=<`), `Dvd`, `GetElem`/`GetElem?`, `Insert`/`Singleton`.
//!
//! Three assertion families:
//! 1. POSITIVE — shapes whose instances exist elaborate and kernel-check,
//!    with `rfl` value probes where the head computes. Includes the Brick 3
//!    parser RHS unit-thunk flips (`>> <|> <*> <* *>` end-to-end, audit rows
//!    a01/a04-a07) backed by `instHAndThenOption`/`instHOrElseOption`.
//! 2. LOUD-FAILURE — genuinely-wrong shapes must still be REJECTED. This
//!    includes the audit §5 silent-unsoundness tripwires: `xs[0]` with no
//!    bounds proof must never kernel-accept (Brick 4 landed the List
//!    instances + `get_elem_tactic` analog, so its failure mode is now the
//!    loud tactic-chain error; positive getElem coverage moved to
//!    tests/brick_4_getelem_e2e.rs).
//! 3. AXIOM HYGIENE — every new head has an EMPTY transitive axiom closure,
//!    except the documented `Bind.*` combinators, which rest on exactly the
//!    pre-existing `Bind.bind` stub axiom (no new axioms anywhere).
//!
//! Audit: docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md (rows a01–e09, §5).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed), and
/// return the failure text for shape assertions.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(ToString::to_string)
        .collect()
}

// =========================================================================
// 1. POSITIVE — registered heads with instances elaborate end-to-end
// =========================================================================

#[test]
fn test_id_application_elaborates_and_computes() {
    let env = elaborate_module(
        r"
def i5 : Nat := id 5
def iDollar : Nat := id $ 5
theorem id_val : id 5 = 5 := rfl
",
    )
    .expect("id 5 / id $ 5 should elaborate and kernel-check (audit rows e01-e03)");
    assert!(
        axiom_closure(&env, "id").is_empty(),
        "id must be a real definition with an empty axiom closure"
    );
}

#[test]
fn test_functor_map_option_and_list_elaborate_and_compute() {
    let env = elaborate_module(
        r"
def fmapOpt (o : Option Nat) : Option Nat := Nat.succ <$> o
def fmapList (xs : List Nat) : List Nat := Nat.succ <$> xs
def mapRevOpt (o : Option Nat) : Option Nat := o <&> Nat.succ
theorem fmap_opt_val : (Nat.succ <$> (some 1 : Option Nat)) = some 2 := rfl
",
    )
    .expect("<$> over Option/List and <&> over Option should elaborate (audit rows a03/a12)");
    for c in [
        "Functor.map",
        "Functor.mapConst",
        "Functor.mapRev",
        "instFunctorOption",
        "instFunctorList",
    ] {
        assert!(
            axiom_closure(&env, c).is_empty(),
            "{c} must have an empty axiom closure"
        );
    }
}

#[test]
fn test_seq_family_fully_thunked_explicit_calls_elaborate() {
    // The audit cross-check probe: even the FULLY-THUNKED explicit call
    // failed before P1. Brick 3 later added the parser-side thunk insertion
    // for `<*> <* *>` (operator tests above); these explicit forms remain
    // the P1 acceptance shape and must stay green alongside it (probe x3).
    let env = elaborate_module(
        r"
def seqOpt (f : Option (Nat -> Nat)) (o : Option Nat) : Option Nat :=
  Seq.seq f (fun _ : Unit => o)
def seqLeftOpt (a : Option Nat) (b : Option Nat) : Option Nat :=
  SeqLeft.seqLeft a (fun _ : Unit => b)
def seqRightOpt (a : Option Nat) (b : Option Nat) : Option Nat :=
  SeqRight.seqRight a (fun _ : Unit => b)
theorem seq_opt_val :
  Seq.seq (some Nat.succ) (fun _ : Unit => (some 1 : Option Nat)) = some 2 := rfl
theorem seq_right_none :
  SeqRight.seqRight (none : Option Nat) (fun _ : Unit => (some 1 : Option Nat)) = none := rfl
",
    )
    .expect("explicit thunked Seq/SeqLeft/SeqRight over Option should elaborate");
    for c in [
        "Seq.seq",
        "SeqLeft.seqLeft",
        "SeqRight.seqRight",
        "instSeqOption",
        "instSeqLeftOption",
        "instSeqRightOption",
    ] {
        assert!(
            axiom_closure(&env, c).is_empty(),
            "{c} must have an empty axiom closure"
        );
    }
}

#[test]
fn test_dvd_operator_and_head_elaborate() {
    let env = elaborate_module(
        r"
def dvdProp (a b : Nat) : Prop := a ∣ b
def dvdHead (a b : Nat) : Prop := Dvd.dvd a b
",
    )
    .expect("a ∣ b / Dvd.dvd a b over Nat should elaborate (audit row e05)");
    for c in ["Dvd.dvd", "instDvdNat"] {
        assert!(
            axiom_closure(&env, c).is_empty(),
            "{c} must have an empty axiom closure"
        );
    }
}

#[test]
fn test_collection_literal_list_elaborates_and_computes() {
    let env = elaborate_module(
        r"
def collLit : List Nat := {1, 2, 3}
theorem coll_val : ({1, 2} : List Nat) = List.cons 1 (List.cons 2 List.nil) := rfl
",
    )
    .expect("{1,2,3} : List Nat collection literal should elaborate (audit row e07)");
    for c in [
        "Insert.insert",
        "Singleton.singleton",
        "instInsertList",
        "instSingletonList",
    ] {
        assert!(
            axiom_closure(&env, c).is_empty(),
            "{c} must have an empty axiom closure"
        );
    }
}

#[test]
fn test_bind_combinators_elaborate_over_option() {
    let env = elaborate_module(
        r"
def bindLeftOpt (x : Option Nat) : Option Nat := (fun n => some n) =<< x
def kleisliR : Nat -> Option Nat := (fun n => some (Nat.succ n)) >=> (fun m => some m)
def kleisliL : Nat -> Option Nat := (fun m => some m) <=< (fun n => some (Nat.succ n))
",
    )
    .expect("=<< / >=> / <=< should elaborate (audit rows a09-a11)");
    // Documented deviation: the combinators are spelled against the
    // pre-existing Bind.bind stub axiom (no [Bind m] binder yet). Their
    // closure must be exactly that one PRE-EXISTING axiom — nothing new.
    for c in ["Bind.bindLeft", "Bind.kleisliRight", "Bind.kleisliLeft"] {
        assert_eq!(
            axiom_closure(&env, c),
            vec!["Bind.bind".to_string()],
            "{c} must rest on exactly the pre-existing Bind.bind stub axiom"
        );
    }
}

#[test]
fn test_getelem_class_heads_are_registered_with_empty_closure() {
    // The P1 class heads + projections must exist and be axiom-free (the
    // Brick 4 List instances have their own hygiene asserts in
    // tests/brick_4_getelem_e2e.rs).
    let env = Environment::with_prelude();
    for c in [
        "GetElem.getElem",
        "GetElem?.toGetElem",
        "GetElem?.getElem?",
        "GetElem?.getElem!",
        "HAndThen.hAndThen",
        "HOrElse.hOrElse",
    ] {
        assert!(
            env.get_const(&Name::from_string(c)).is_some(),
            "{c} must be registered in the prelude"
        );
        assert!(
            axiom_closure(&env, c).is_empty(),
            "{c} must have an empty axiom closure"
        );
    }
}

// =========================================================================
// 2. LOUD-FAILURE — staged heads and z-probe tripwires stay rejected
// =========================================================================

#[test]
fn test_getelem_no_proof_zprobe_stays_rejected() {
    // Audit §5 z-probe: unproved bounds must NEVER kernel-accept. Brick 4
    // registered the List instances and the `get_elem_tactic` analog, so the
    // failure is now the LOUD tactic-chain error (the obligation
    // `0 < List.length xs` is genuinely unprovable), never a leaked
    // metavariable and never `sorry`.
    let err = expect_rejected(
        "def g (xs : List Nat) : Nat := xs[0]\n",
        "xs[0] with no bounds proof in scope",
    );
    assert!(
        err.contains("failed to prove index is valid"),
        "failure must be the Brick 4 get_elem_tactic-analog rejection; got: {err}"
    );
}

#[test]
fn test_getelem_explicit_proof_elaborates() {
    // c02 `xs[i]'h` — FLIPPED by Brick 4: the List GetElem instance exists
    // and the deferred-instance pin lands before the proof slot, so the
    // explicit proof unifies against the concrete `valid xs i` obligation.
    // (Positive value/discharge coverage lives in tests/brick_4_getelem_e2e.rs.)
    elaborate_module("def g2 (xs : List Nat) (h : 0 < List.length xs) : Nat := xs[0]'h\n")
        .expect("xs[0]'h with an explicit bounds proof must elaborate (audit row c02)");
}

#[test]
fn test_getelem_optional_forms_elaborate() {
    // c03/c04 `xs[i]!` / `xs[i]?` — FLIPPED by Brick 4 via the
    // `List.instGetElem?NatLtLength` instance (+ `Inhabited Nat` for `!`).
    elaborate_module("def g3 (xs : List Nat) : Option Nat := xs[0]?\n")
        .expect("xs[0]? must elaborate via GetElem? (audit row c04)");
    elaborate_module("def g4 (xs : List Nat) : Nat := xs[0]!\n")
        .expect("xs[0]! must elaborate via GetElem? + Inhabited (audit row c03)");
}

#[test]
fn test_lazy_operators_thunked_by_parser_elaborate_and_compute() {
    // Brick 3 landed: the parser inserts the Lean-faithful RHS unit-thunk
    // (`fun _ : Unit => rhs`, exactly Lean's `<*>`-family macro_rules /
    // `binop_lazy%` expansion) for `>> <|> <*> <* *>`, and the kernel prelude
    // carries `instHAndThenOption` / `instHOrElseOption` (real `Option.bind` /
    // `Option.rec` bodies) alongside the P1 `instSeq*Option` instances — so
    // all five operators elaborate, kernel-check, and COMPUTE end-to-end
    // (audit rows a01/a04-a07).
    let env = elaborate_module(
        r"
def andThenOpt (a b : Option Nat) : Option Nat := a >> b
def orElseOpt (a b : Option Nat) : Option Nat := a <|> b
def seqOp (f : Option (Nat -> Nat)) (o : Option Nat) : Option Nat := f <*> o
def seqLeftOp (a b : Option Nat) : Option Nat := a <* b
def seqRightOp (a b : Option Nat) : Option Nat := a *> b
theorem andthen_val : ((some 1 : Option Nat) >> (some 2 : Option Nat)) = some 2 := rfl
theorem andthen_none : ((none : Option Nat) >> (some 2 : Option Nat)) = none := rfl
theorem orelse_first : ((some 1 : Option Nat) <|> (some 2 : Option Nat)) = some 1 := rfl
theorem orelse_none_lhs : ((none : Option Nat) <|> (some 3 : Option Nat)) = some 3 := rfl
theorem seq_val : (some Nat.succ <*> (some 1 : Option Nat)) = some 2 := rfl
theorem seq_left_val : ((some 1 : Option Nat) <* (some 2 : Option Nat)) = some 1 := rfl
theorem seq_right_none : ((none : Option Nat) *> (some 1 : Option Nat)) = none := rfl
",
    )
    .expect("parser-thunked `>> <|> <*> <* *>` over Option should elaborate and compute");
    for c in ["instHAndThenOption", "instHOrElseOption"] {
        assert!(
            axiom_closure(&env, c).is_empty(),
            "{c} must have an empty axiom closure"
        );
    }
}

#[test]
fn test_lazy_operator_wrong_shapes_stay_loud() {
    // Loud negatives: the RHS thunk must not have opened an over-acceptance
    // hole — genuinely-wrong operand types still fail instance resolution /
    // unification, never silently elaborate.
    expect_rejected(
        "def bad1 (a : Option Nat) (b : Nat) : Option Nat := a >> b\n",
        ">> with a bare-Nat RHS (no HAndThen (Option Nat) Nat _ instance)",
    );
    expect_rejected(
        "def bad2 (a b : Option Nat) : Option Nat := a <*> b\n",
        "<*> whose LHS is not an Option-wrapped function",
    );
}

#[test]
fn test_subst_cast_zprobe_now_elaborates() {
    // Audit §5 z-probe, originally must-reject ("the `▸` motive arm is
    // Brick 2; until it lands the Eq.rec shape must stay rejected"). Brick E2
    // landed the Lean-faithful elabSubst port (infer/elab_subst.rs), so this
    // proof-position cast now elaborates and kernel-checks. The silent-wrong
    // guards (orientation search, value-pinned computational casts, loud
    // negatives) live in tests/brick_e2_subst_e2e.rs.
    elaborate_module("theorem tz (a b : Nat) (h : a = b) : b = a := h ▸ rfl\n")
        .expect("`h ▸ rfl` must elaborate via the Brick E2 subst arm");
}
