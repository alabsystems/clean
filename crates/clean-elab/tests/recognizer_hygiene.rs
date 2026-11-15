// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A recognizer of a well-known global head may fire only on a head that
//! RESOLVES to that global, never on a spelling a local binds. False theorems
//! measured 2026-09-26 against Lean 4.8.0, each accepted by e3f696689:
//!
//! * The elaborator rewrote a head by its SPELLING: `ite c t e` to `elab_if`,
//!   `not b`/`Not b` to `Bool.not`, `(flip g) a b` to `g b a`,
//!   `Function.comp`/`Function.const` (also read as a FIELD of a local
//!   `Function`) to their β-reducts, `And.elim`/`Iff.elim` to projections,
//!   `inferInstance` to instance synthesis, a do-block `pure` to the monad's
//!   `pure`, and `Eq`/`Ne` with a structure-literal operand to `@Eq T`. With
//!   the spelling bound by a parameter, `let`, `fun` or namespace member, the
//!   user's own function was replaced by the global's meaning: `def g (ite :
//!   Bool → Nat → Nat → Nat) : Nat := ite true 1 2` proved `g (fun _ _ c =>
//!   c) = 1` (Lean: `2`). Each recognizer now asks `head_denotes_global`,
//!   which runs the elaborator's own resolution (`resolve_ident_target`).
//! * `⟨a, b⟩` was `App(anonymousCtor, …)` recognized by TEXT, so a user's
//!   own `anonymousCtor` built a tuple. The parser's head is now marked
//!   generated and recognized by that mark.
//! * The builtin `if c then a else b` macro expanded to a plain generated
//!   `ite`, which a local `ite` captured in argument position; its template
//!   heads are now global references (`Syntax::global_ident`).
//! * Two of these had been cancelling a third: with `bif` captured by a local
//!   `cond` gone (a4e7697d0), the `Not`/`ite` hijack surfaced as NEW false
//!   theorems (`f1817`/`f1662` below).
//!
//! Every `T` statement is accepted by Lean 4.8.0 and every `F` statement is
//! refused by it (both measured); each `F` is the value e3f696689 computed.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

/// `(holds, decidable, statement)`: a statement that holds must register
/// axiom-free by `rfl`; one that does not must be refused by `rfl` and, when
/// it is a decidable equation of data, by `decide`, leaving nothing behind.
fn check(env: &mut Environment, prefix: &str, cases: &[(bool, bool, &str)]) {
    for (id, (holds, decidable, statement)) in cases.iter().enumerate() {
        if *holds {
            let name = format!("{prefix}_true_{id}");
            register(env, &format!("theorem {name} : {statement} := rfl"))
                .unwrap_or_else(|error| panic!("{statement} must hold: {error}"));
            let deps = env
                .axiom_deps(&Name::from_string(&name))
                .expect("registered theorem");
            assert!(deps.is_empty(), "{statement}: depends on axioms: {deps:?}");
            continue;
        }
        let proofs: &[(&str, &str)] = if *decidable {
            &[("rfl", "rfl"), ("decide", "by decide")]
        } else {
            &[("rfl", "rfl")]
        };
        for (kind, proof) in proofs {
            let name = format!("{prefix}_false_{id}_{kind}");
            let error = register(env, &format!("theorem {name} : {statement} := {proof}"))
                .expect_err(&format!("FALSE theorem accepted: {statement} := {proof}"));
            assert!(
                !error.contains("parse error"),
                "negative must parse: {error}"
            );
            assert!(
                env.get_const(&Name::from_string(&name)).is_none(),
                "false theorem registered: {statement}"
            );
        }
    }
}

/// A proposition the global meaning would prove and the user's own local
/// refutes: every listed proof must be refused.
fn refuted(env: &mut Environment, name: &str, statement: &str, proofs: &[&str]) {
    for (i, proof) in proofs.iter().enumerate() {
        let error = register(env, &format!("theorem {name}_{i} : {statement} := {proof}"))
            .expect_err(&format!("FALSE theorem accepted: {statement} := {proof}"));
        assert!(!error.contains("parse error"), "{error}");
    }
}

#[test]
fn value_recognizers_keep_a_locally_bound_head() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def r1 (ite : Bool → Nat → Nat → Nat) : Nat := ite true 1 2
def r2 : Nat := let ite : Prop → Nat → Nat → Nat := (fun _ _ c => c); ite True 1 2
def r3 : (Bool → Nat → Nat → Nat) → Nat := fun ite => (ite true 1 2) + 0
def r4 (not : Bool → Bool) : Bool := not true
def r5 (Not : Bool → Bool) : Nat := bif Not false then 1 else 2
def r6 (flip : (Nat → Nat → Nat) → Nat → Nat → Nat) : Nat := (flip Nat.sub) 5 3
def r7 : Nat := let flip : (Nat → Nat → Nat) → Nat → Nat → Nat := (fun g a b => g a b); flip Nat.sub 5 3
def r8 (inferInstance : Inhabited Nat) : Nat := (inferInstance : Inhabited Nat).default
def r9 (pure : Nat → Id Nat) : Nat := Id.run (do pure 3)
def r10 (pure : Nat → Id Nat) : Nat := Id.run (do let y ← pure 3; pure y)
def r11 (anonymousCtor : Nat → Nat → Nat × Nat) : Nat := (anonymousCtor 1 2).1
namespace NS
def ite : Bool → Nat → Nat → Nat := (fun _ _ c => c)
def r12 : Nat := ite true 1 2
def not : Bool → Bool := (fun b => b)
def r13 : Bool := not true
end NS
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "rev",
        &[
            (true, true, "r1 (fun _ _ c => c) = 2"),
            (false, true, "r1 (fun _ _ c => c) = 1"),
            (true, true, "r2 = 2"),
            (false, true, "r2 = 1"),
            (true, true, "r3 (fun _ _ c => c) = 2"),
            (false, true, "r3 (fun _ _ c => c) = 1"),
            (true, true, "r4 (fun b => b) = true"),
            (false, true, "r4 (fun b => b) = false"),
            (true, true, "r5 (fun b => b) = 2"),
            (false, true, "r5 (fun b => b) = 1"),
            (true, true, "r6 (fun g a b => g a b) = 2"),
            (false, true, "r6 (fun g a b => g a b) = 0"),
            (true, true, "r7 = 2"),
            (false, true, "r7 = 0"),
            (true, true, "r8 ⟨5⟩ = 5"),
            (false, true, "r8 ⟨5⟩ = 0"),
            (true, true, "r9 (fun x => x + 1) = 4"),
            (false, true, "r9 (fun x => x + 1) = 3"),
            (true, true, "r10 (fun x => x + 1) = 5"),
            (false, true, "r10 (fun x => x + 1) = 3"),
            (true, true, "r11 (fun a b => (b, a)) = 2"),
            (false, true, "r11 (fun a b => (b, a)) = 1"),
            (true, true, "NS.r12 = 2"),
            (false, true, "NS.r12 = 1"),
            (true, true, "NS.r13 = true"),
            (false, true, "NS.r13 = false"),
        ],
    );
}

#[test]
fn dotted_recognizers_read_a_local_prefix_as_a_field() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
structure FS where
  comp : (Nat → Nat) → (Nat → Nat) → Nat → Nat
  const : Type → Nat → Nat → Nat
structure LR where
  left : Nat
  right : Nat
structure FA where
  elim : (Nat → Nat → Nat) → LR → Nat
def d1 (Function : FS) : Nat := (Function.comp (· + 1) (· * 2)) 3
def d2 (Function : FS) : Nat := Function.comp (· + 1) (· * 2) 3
def d3 (Function : FS) : Nat := (Function.const Nat 5) 3
def d4 (And : FA) : Nat := And.elim (fun a b => a + 10 * b) (LR.mk 1 2)
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "dot",
        &[
            (true, true, "d1 ⟨fun _ _ _ => 0, fun _ _ _ => 0⟩ = 0"),
            (false, true, "d1 ⟨fun _ _ _ => 0, fun _ _ _ => 0⟩ = 7"),
            (true, true, "d2 ⟨fun _ _ _ => 0, fun _ _ _ => 0⟩ = 0"),
            (false, true, "d2 ⟨fun _ _ _ => 0, fun _ _ _ => 0⟩ = 7"),
            (true, true, "d3 ⟨fun _ _ _ => 0, fun _ _ _ => 0⟩ = 0"),
            (false, true, "d3 ⟨fun _ _ _ => 0, fun _ _ _ => 0⟩ = 5"),
            (true, true, "d4 ⟨fun _ _ => 0⟩ = 0"),
            (false, true, "d4 ⟨fun _ _ => 0⟩ = 21"),
        ],
    );
    // The global combinators are still recognized where nothing shadows them.
    register(
        &mut env,
        r#"
def g1 : Nat := (Function.comp (· + 1) (· * 2)) 3
def g2 : Nat := (flip Nat.sub) 3 5
def g3 : Nat := ite true 1 2
"#,
    )
    .expect("global combinators elaborate");
    check(
        &mut env,
        "glob",
        &[
            (true, true, "g1 = 7"),
            (true, true, "g2 = 2"),
            (true, true, "g3 = 1"),
        ],
    );
}

#[test]
fn prop_recognizers_keep_a_locally_bound_relation() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
structure P where
  x : Nat
def e1 (Eq : P → P → Prop) : Prop := Eq {x := 1} (P.mk 1)
def e2 (Eq : P → P → Prop) : Prop := Eq (P.mk 1) {x := 1}
def e3 (Ne : P → P → Prop) : Prop := Ne {x := 1} (P.mk 2)
"#,
    )
    .expect("definitions elaborate");
    // Lean: each is the user's `fun _ _ => False`, so none is provable.
    refuted(
        &mut env,
        "e1_holds",
        "e1 (fun _ _ => False)",
        &["by unfold e1; rfl", "by unfold e1; trivial"],
    );
    refuted(
        &mut env,
        "e2_holds",
        "e2 (fun _ _ => False)",
        &["by unfold e2; rfl", "by unfold e2; trivial"],
    );
    refuted(
        &mut env,
        "e3_holds",
        "e3 (fun _ _ => False)",
        &["by unfold e3; intro h; cases h", "by unfold e3; trivial"],
    );
}

#[test]
fn user_definitions_named_like_compiler_heads_are_ordinary() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def anonymousCtor (a b : Nat) : Nat × Nat := (b, a)
def w0 : Nat × Nat := anonymousCtor 1 2
def w1 : Nat × Nat := ⟨1, 2⟩
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "anon_ctor",
        &[
            (true, true, "w0 = (2, 1)"),
            (false, true, "w0 = (1, 2)"),
            (true, true, "w1 = (1, 2)"),
        ],
    );
}

#[test]
fn if_macro_head_is_not_captured_by_a_local_ite() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def y1 (ite : Bool → Nat → Nat → Nat) (n : Nat) : Nat := Nat.max (if (n == n) then 1 else 2) 0
def y2 (f : Nat → Nat) (ite : Bool → Nat → Nat → Nat) (b : Bool) : Nat := f (if b then 1 else 2)
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "ifmacro",
        &[
            (true, true, "y1 (fun _ a b => a + b) 0 = 1"),
            (false, true, "y1 (fun _ a b => a + b) 0 = 3"),
            (true, true, "y2 (fun a => a) (fun _ a b => a + b) true = 1"),
            (false, true, "y2 (fun a => a) (fun _ a b => a + b) true = 3"),
        ],
    );
}

/// The two false theorems a4e7697d0 introduced: fixing the capture of the
/// `bif` head by a local `cond` exposed the hijack of a local `Not`/`ite`
/// that it had been cancelling.
#[test]
fn unmasked_hijacks_stay_closed() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def f1817 (n : Nat) (a : Bool) (b : Bool) (decide : Prop → Bool) (cond : Bool → Nat → Nat → Nat) (m : Nat) : Nat :=
  (let Not : Bool → Bool := (fun _ => false); (bif (Not (decide (1 = 0))) then (cond (decide (m = n)) (Nat.max 4 m) (cond false m n)) else m))
def f1662 (ite : Bool → Nat → Nat → Nat) (xor : Bool → Bool → Bool) (cond : Bool → Nat → Nat → Nat) (b : Bool) (n : Nat) (a : Bool) (m : Nat) : Nat :=
  (cond (xor (xor false a) (xor b a)) ((ite a 2 m) + (bif false then m else n)) n)
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "unmasked",
        &[
            (
                true,
                true,
                "f1817 0 false false (fun _ => false) (fun c a b => if c then b else a) 3 = 3",
            ),
            (
                false,
                true,
                "f1817 0 false false (fun _ => false) (fun c a b => if c then b else a) 3 = 4",
            ),
            (
                true,
                true,
                "f1662 (fun _ a b => a + b) (fun a _ => a) (fun c a b => if c then b else a) true 0 false 2 = 4",
            ),
            (
                false,
                true,
                "f1662 (fun _ a b => a + b) (fun a _ => a) (fun c a b => if c then b else a) true 0 false 2 = 2",
            ),
        ],
    );
}

/// A notation's head is pre-resolved at the ROOT: a namespace member of the
/// same spelling does not capture it. Clean's root `cond`/`not` are
/// resolution fallbacks rather than constants, and a global reference used to
/// fall through to the namespace walk before reaching them, so `bif` inside
/// `namespace NQ` called `NQ.cond` (e3f696689: `NQ.q2 true = 2`).
#[test]
fn notation_heads_resolve_at_the_root() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
namespace NQ
def not : Bool → Bool := (fun b => b)
def q1 (a : Bool) : Bool := !a
def cond : Bool → Nat → Nat → Nat := (fun c a b => if c then b else a)
def q2 (b : Bool) : Nat := bif b then 1 else 2
end NQ
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "root_head",
        &[
            (true, true, "NQ.q1 true = false"),
            (false, true, "NQ.q1 true = true"),
            (true, true, "NQ.q2 true = 1"),
            (false, true, "NQ.q2 true = 2"),
        ],
    );
}
