// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `⟨…⟩`'s ENTRY contract: postponement on an open expected type, and Lean's
//! implicit lambda.
//!
//! `elabAnonymousCtor` (`Lean/Elab/BuiltinNotation.lean:43-54`) opens with
//! `tryPostponeIfNoneOrMVar expectedType?` (:46), whnfs (:53), and only THEN
//! throws `throwExpTypeUnknown` if `expectedType.getAppFn.isMVar` (:54).
//! Separately, `elabTermAux` wraps any non-blocked term — `⟨…⟩` included — in
//! implicit lambdas when the expected type's leading binder is implicit or
//! instance-implicit (`useImplicitLambda` / `elabImplicitLambda`,
//! `Lean/Elab/Term/TermElabM.lean:1711-1790`, wired at :1806-1808;
//! `blockImplicitLambda` at :1684-1688 does not list the anonymous
//! constructor).
//!
//! Clean had NEITHER at this entry: `elab_anonymous_ctor` read
//! `current_expected_type`, whnf'd once, and failed with
//! `AnonymousCtorNotInductive` unless the head was already a `Const`. The two
//! Mathlib rows are `Function.sometimes_eq` (`dif_pos ⟨a⟩`, whose `{c : Prop}`
//! is open when `⟨a⟩` is reached) and `forall_existsUnique_iff` (whose inner
//! `⟨…⟩` faces `∀ {a b}, r a b ↔ f a = b`).
//!
//! ACCEPTANCE BAR: the positives pin the produced VALUE with a `rfl` theorem,
//! so a term built at the wrong type or with the wrong constructor cannot pass.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// The `dif_pos` shape, prelude-only. `mydif_pos`'s `{c : Prop}` appears ONLY in
/// the result type, so when the `⟨h1, h2⟩` argument is reached the slot type is
/// the bare metavariable `?c` — exactly `Function.sometimes_eq`'s situation.
/// Pinned lean v4.30.0-rc2 accepts this file (measured).
const DIF: &str = "
structure MyAnd (p : Prop) (q : Prop) : Prop where
  intro :: (left : p) (right : q)

axiom MyDite : (c : Prop) -> Nat -> Nat -> Nat
axiom mydif_pos : {c : Prop} -> c -> (t : Nat) -> (e : Nat) -> MyDite c t e = t

axiom P : Prop
axiom Q : Prop
";

/// Lean's `Iff`, hand-rolled so the replica needs no import.
const IFF: &str = "
structure MyIff (p : Prop) (q : Prop) : Prop where
  intro :: (mp : p -> q) (mpr : q -> p)
";

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
                "declaration(s) failed to elaborate:\n{}",
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

#[test]
fn test_anonymous_ctor_in_slot_with_open_type_is_postponed() {
    // `⟨h1, h2⟩`'s slot type is the bare metavariable `?c`, pinned only by
    // unifying `mydif_pos`'s RESULT type with the declared statement. Without
    // postponement this was "Anonymous constructor ⟨⟩ expected inductive type,
    // got fvar#9223372036854775810" — a metavariable rendered as a bit-63 fvar.
    let src = format!(
        "{DIF}
theorem sometimesEq (h1 : P) (h2 : Q) : MyDite (MyAnd P Q) 1 2 = 1 :=
  mydif_pos ⟨h1, h2⟩ 1 2
"
    );
    elaborate_module(&src)
        .expect("an ⟨…⟩ in a slot whose type is still a metavariable must be postponed");
}

/// `Mathlib/Logic/Function/Basic.lean`'s `forall_existsUnique_iff` shape: the
/// ⟨…⟩ sits in an ARGUMENT SLOT whose type is `∀ {a b}, r a b ↔ f a = b`, so
/// `current_expected_type` really is the implicit Pi when the anonymous
/// constructor is reached. This is the position the entry-level insertion
/// exists for; a declaration VALUE may have had its binders introduced by the
/// declaration path before the value is elaborated at all.
const IMPLICIT_PI: &str = "
axiom r : Nat -> Nat -> Prop
axiom f : Nat -> Nat
axiom fwd : {a : Nat} -> {b : Nat} -> r a b -> f a = b
axiom bwd : {a : Nat} -> {b : Nat} -> f a = b -> r a b
";

#[test]
fn test_anonymous_ctor_in_an_implicit_pi_argument_slot_inserts_the_lambda() {
    let src = format!(
        "{IFF}{IMPLICIT_PI}
axiom consume : ({{a : Nat}} -> {{b : Nat}} -> MyIff (r a b) (f a = b)) -> True

theorem implicitLambda : True := consume ⟨fun h => fwd h, fun h => bwd h⟩
"
    );
    elaborate_module(&src)
        .expect("an ⟨…⟩ facing an implicit-binder Pi must be wrapped in implicit lambdas");
}

#[test]
fn test_anonymous_ctor_as_a_declaration_value_under_implicit_binders() {
    let src = format!(
        "{IFF}{IMPLICIT_PI}
theorem implicitLambdaDecl : {{a : Nat}} -> {{b : Nat}} -> MyIff (r a b) (f a = b) :=
  ⟨fun h => fwd h, fun h => bwd h⟩
"
    );
    elaborate_module(&src).expect("the same shape as a declaration value must elaborate as well");
}

#[test]
fn test_anonymous_ctor_against_instance_implicit_pi_inserts_the_lambda() {
    let src = format!(
        "{IFF}
class Tag (a : Type) where
  tag : Nat

axiom consumeInst : ([Tag Nat] -> MyIff True True) -> True

theorem instLambda : True := consumeInst ⟨fun h => h, fun h => h⟩
"
    );
    elaborate_module(&src).expect(
        "an instance-implicit leading binder inserts a lambda just as an implicit one does",
    );
}

#[test]
fn test_anonymous_ctor_with_no_expected_type_still_fails_loudly() {
    // Lean's `throwExpTypeUnknown`: postponement never turns an unknowable
    // type into a guess.
    let src = "
def unknowable := ⟨1, 2⟩
";
    elaborate_module(src)
        .expect_err("an ⟨…⟩ with no expected type at all must still be a loud failure");
}

/// CONTROL: the ordinary `⟨…⟩` path, where the slot type is already known, is
/// untouched — it must NOT be routed through the deferral (the `Prod.mk` tuple
/// encoding that closed class 15 depends on running against the real type).
#[test]
fn test_anonymous_ctor_with_known_slot_type_is_not_deferred() {
    let src = "
def pairOf (p : Nat × Nat) : Nat × Nat := p
def built : Nat × Nat := pairOf ⟨1, 2⟩
theorem built_pin : built = (1, 2) := rfl
";
    elaborate_module(src)
        .expect("an ⟨…⟩ whose slot type is already known must elaborate as before");
}

/// CONTROL: an ASCRIBED anonymous constructor pins its own type and is never
/// deferred (Lean keeps a type ascription on `blockImplicitLambda`, and
/// `deferrable_by_block` excludes an ascribed block for the same reason).
#[test]
fn test_ascribed_anonymous_ctor_still_elaborates() {
    let src = "
def ascribed : Nat × Nat := (⟨1, 2⟩ : Nat × Nat)
theorem ascribed_pin : ascribed = (1, 2) := rfl
";
    elaborate_module(src).expect("an ascribed ⟨…⟩ must keep elaborating against its ascription");
}

// ---------------------------------------------------------------------------
// ADVERSARIAL REVIEW ADDITIONS (W3E review pass)
//
// Each expectation was ground-truthed on the SAME shape against the pinned
// binary `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`, and the
// measured output is quoted in the doc comment.
// ---------------------------------------------------------------------------

/// MEASURED DIVERGENCE, REPAIRED IN THIS REVIEW: once Lean's implicit-lambda
/// loop is OPEN it peels every binder that is not EXPLICIT — strict implicits
/// included (`elabImplicitLambda`'s loop, `Lean/Elab/Term/TermElabM.lean:1780`:
/// `if c.isExplicit then … else` peel).
///
/// Measured at the pin:
///
/// ```lean
/// def g : ∀ {x : Nat} ⦃y : Nat⦄, Pair := ⟨1, 2⟩
/// #print g
/// -- def g : {x : Nat} → ⦃y : Nat⦄ → Pair :=
/// -- fun {x} ⦃y⦄ => { a := 1, b := 2 }
/// ```
///
/// The first landing peeled ONE binder per recursion and re-imposed the ENTRY
/// condition (`Implicit | InstImplicit`) on every one of them, so the strict
/// implicit stopped the loop and the `⟨…⟩` faced a `Pi` it could not read.
#[test]
fn test_anonymous_ctor_strict_implicit_after_an_implicit_is_peeled_too() {
    // The UNICODE spelling on purpose: Clean's `looks_like_binder_start`
    // (`crates/clean-parser/src/grammar/expr_app.rs`) reads the ASCII `{{` in a
    // TYPE as "nested braces, not a binder", so `⦃b : Nat⦄` is the spelling that
    // actually reaches the elaborator as a strict-implicit Pi. That ASCII gap is
    // pre-existing and is not this package's.
    let src = format!(
        "{IFF}
theorem strictAfterImplicit : {{a : Nat}} -> ⦃b : Nat⦄ -> MyIff True True :=
  ⟨fun h => h, fun h => h⟩
"
    );
    elaborate_module(&src).expect(
        "Lean's implicit-lambda loop peels a strict implicit once an implicit has opened it",
    );
}

/// CONTROL for the repair above, and the half that must NOT move: a LEADING
/// strict implicit does not OPEN the loop. `useImplicitLambda`
/// (TermElabM.lean:1719) refuses unless the leading binder is `{…}` or `[…]`,
/// and pinned lean rejects the file:
///
/// ```lean
/// def g3 : ∀ ⦃y : Nat⦄, Pair := ⟨1, 2⟩
/// -- error: Invalid `⟨...⟩` notation: The expected type `⦃y : Nat⦄ → Pair`
/// --        is not an inductive type
/// ```
#[test]
fn test_anonymous_ctor_leading_strict_implicit_does_not_open_the_lambda() {
    let src = format!(
        "{IFF}
theorem leadingStrict : ⦃b : Nat⦄ -> MyIff True True := ⟨fun h => h, fun h => h⟩
"
    );
    elaborate_module(&src).expect_err(
        "a LEADING strict implicit is not an implicit-lambda opener, exactly as in Lean",
    );
}

/// MEASURED DIVERGENCE, REPAIRED IN THIS REVIEW: `@`-explicit mode is a
/// property of the enclosing APPLICATION, not of the `⟨…⟩` argument's own
/// syntax, and Lean's `blockImplicitLambda` reads the term's own syntax
/// (`isExplicit stx`). Measured at the pin:
///
/// ```lean
/// def h {α : Type} (_ : α) (p : ∀ {x : Nat}, Pair) : Nat := (@p 0).a
/// #check @h Nat 0 ⟨1, 2⟩
/// -- h 0 fun {x} => { a := 1, b := 2 } : Nat
/// ```
///
/// The first landing gated the insertion on `!self.explicit_mode`, which is set
/// for the whole of `@f …` including its arguments, so Clean refused the term
/// Lean accepts.
#[test]
fn test_anonymous_ctor_under_an_explicit_application_still_inserts_the_lambda() {
    let src = format!(
        "{IFF}{IMPLICIT_PI}
axiom consume2 : (a : Type) -> ({{c : Nat}} -> MyIff (r 0 0) (f 0 = 0)) -> True

theorem explicitApp : True := @consume2 Nat ⟨fun h => fwd h, fun h => bwd h⟩
"
    );
    elaborate_module(&src).expect(
        "`@f` suppresses implicit ARGUMENT insertion, never the argument's own implicit lambda",
    );
}

/// The postponement is keyed on the expected type's HEAD being a metavariable
/// (Lean's `expectedType.getAppFn.isMVar`), not on the type mentioning one.
/// This is the near miss for `test_anonymous_ctor_in_slot_with_open_type_is_
/// postponed`: a slot typed `MyPair ?a Nat` has a rigid HEAD, so it must keep
/// elaborating eagerly and the fields must be what pin `?a`.
#[test]
fn test_anonymous_ctor_at_a_partially_open_but_rigid_headed_slot_is_eager() {
    let src = "
structure MyPair (a : Type) (b : Type) where
  fst : a
  snd : b

def usePair {a : Type} (p : MyPair a Nat) : Nat := p.snd
def eager : Nat := usePair ⟨true, 7⟩
theorem eager_pin : eager = 7 := rfl
";
    elaborate_module(src).expect(
        "a slot whose type mentions a metavariable but whose HEAD is rigid is not postponed",
    );
}

/// The deferral must not swallow a genuine failure: an `⟨…⟩` at a slot whose
/// type stays an open metavariable to the very end is still a LOUD error, not a
/// silently-dropped argument. This is the drain's refusal arm, which the
/// speculative result-type unification added beside it must never turn into a
/// success by assigning something arbitrary.
#[test]
fn test_anonymous_ctor_at_a_slot_that_stays_open_still_fails_loudly() {
    let src = "
axiom opaque2 : {c : Type} -> c -> Nat
def unresolved : Nat := opaque2 ⟨1, 2⟩
";
    elaborate_module(src)
        .expect_err("an ⟨…⟩ whose slot type is never pinned must fail, never be guessed");
}
