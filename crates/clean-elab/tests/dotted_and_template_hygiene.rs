// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name resolution of dotted identifiers, of the `outParam`/`semiOutParam`
//! markers, and of user notation templates follows Lean 4.8.0. False
//! theorems measured 2026-09-26, each accepted by c565a700a (and the
//! dotted/`outParam`/template ones by e3f696689 and 3f45fb7c6 as well):
//!
//! * A `where`/`let rec` name is an AUXILIARY declaration in Lean: `Foo.x`
//!   with a `where`-bound `Foo` names the global `Foo.x` when one exists
//!   (`resolveLocalName`'s `skipAuxDecl`). Clean lowers such a binding to a
//!   plain `let`, and read `(Function.comp f g) a` as a field of the local:
//!   `w1 3 = 10` was accepted (Lean: `7`).
//! * A dotted identifier is ONE name to Lean (`resolveGlobalName` tries the
//!   full name first): `Foo.x` with a global value `Foo : S` and a global
//!   `Foo.x` is the latter, and inside `namespace N` with a member
//!   `N.Function`, `Function.comp` is the global. Clean projected the value.
//! * The parser turns `outParam e` into a marker by SPELLING, so a local
//!   named `outParam` was never called: `∀ (outParam : Nat → Nat), outParam 0
//!   = 0` was accepted.
//! * A notation's template identifiers carry the expansion's macro scope in
//!   Lean, so no binder at the use site captures them; Clean inlined the
//!   template and a parameter `gf` captured the template's global `gf`.
//!
//! Every `T` statement is accepted by Lean 4.8.0 and every `F` statement is
//! refused by it (both measured); each `F` is the value a build before this
//! change computed.

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
fn dotted_identifier_on_an_auxiliary_declaration_prefers_the_global() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
structure S where
  x : Nat
structure FS where
  comp : (Nat → Nat) → (Nat → Nat) → Nat → Nat
  const : Type → Nat → Nat → Nat
  uncurry : (Nat → Nat → Nat) → Nat × Nat → Nat
def Baz.x : Nat := 9
def d3 : Nat := Baz.x
where Baz : S := ⟨5⟩
def d4 : Nat := (Baz).x
where Baz : S := ⟨5⟩
def d5 : Nat := let Baz : S := ⟨5⟩; Baz.x
def d7 : Nat :=
  let rec Baz : S := ⟨5⟩
  Baz.x
def d8 : Nat := Qux.x
where Qux : S := ⟨5⟩
def w1 (a : Nat) : Nat := (Function.comp (· + 1) (· * 2)) a
where Function : FS := ⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩
def w2 (a : Nat) : Nat := Function.comp (· + 1) (· * 2) a
where Function : FS := ⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩
def w3 (a b : Nat) : Nat := Function.const Nat a b
where Function : FS := ⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩
def w4 (a b : Nat) : Nat := Function.uncurry Nat.add (a, b)
where Function : FS := ⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩
def w6 (Function : FS) (a : Nat) : Nat := Function.comp (· + 1) (· * 2) a
def w7 (a b : Nat) : Nat :=
  let rec Function : FS := ⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩
  (Function.const Nat a) b
"#,
    )
    .expect("definitions elaborate");
    let host = "⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩";
    let w6_true = format!("w6 {host} 3 = 10");
    let w6_false = format!("w6 {host} 3 = 7");
    check(
        &mut env,
        "aux",
        &[
            (true, true, "d3 = 9"),
            (false, true, "d3 = 5"),
            (true, true, "d4 = 5"),
            (false, true, "d4 = 9"),
            (true, true, "d5 = 5"),
            (false, true, "d5 = 9"),
            (true, true, "d7 = 9"),
            (false, true, "d7 = 5"),
            (true, true, "d8 = 5"),
            (false, true, "d8 = 9"),
            (true, true, "w1 3 = 7"),
            (false, true, "w1 3 = 10"),
            (true, true, "w2 3 = 7"),
            (false, true, "w2 3 = 10"),
            (true, true, "w3 1 2 = 1"),
            (false, true, "w3 1 2 = 8"),
            (true, true, "w4 1 2 = 9"),
            (false, true, "w4 1 2 = 3"),
            (true, true, &w6_true),
            (false, true, &w6_false),
            (true, true, "w7 1 2 = 1"),
            (false, true, "w7 1 2 = 8"),
        ],
    );
    refuted(
        &mut env,
        "aux_general",
        "∀ a b, w3 a b = a + 7",
        &["fun _ _ => rfl"],
    );
}

#[test]
fn dotted_identifier_prefers_a_global_of_the_full_name() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
structure S where
  x : Nat
structure FS where
  comp : (Nat → Nat) → (Nat → Nat) → Nat → Nat
  const : Type → Nat → Nat → Nat
  uncurry : (Nat → Nat → Nat) → Nat × Nat → Nat
def Foo : S := ⟨5⟩
def Foo.x : Nat := 9
def d1 : Nat := Foo.x
def d2 : Nat := (Foo).x
namespace N
def Function : FS := ⟨fun _ _ x => x + 7, fun _ a _ => a + 7, fun _ p => p.2 + 7⟩
def n1 (a : Nat) : Nat := Function.comp (· + 1) (· * 2) a
def n2 (a b : Nat) : Nat := Function.const Nat a b
def n3 (a b : Nat) : Nat := Function.uncurry Nat.add (a, b)
def n4 (a : Nat) : Nat := (Function.comp (· + 1) (· * 2)) a
end N
def Function.uncurry (f : Nat → Nat → Nat) (p : Nat × Nat) : Nat := f p.1 p.2 + 100
def u1 (a b : Nat) : Nat := Function.uncurry Nat.add (a, b)
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "full",
        &[
            (true, true, "d1 = 9"),
            (false, true, "d1 = 5"),
            (true, true, "d2 = 5"),
            (false, true, "d2 = 9"),
            (true, true, "N.n1 3 = 7"),
            (false, true, "N.n1 3 = 10"),
            (true, true, "N.n2 1 2 = 1"),
            (false, true, "N.n2 1 2 = 8"),
            (true, true, "N.n3 1 2 = 9"),
            (false, true, "N.n3 1 2 = 3"),
            (true, true, "N.n4 3 = 7"),
            (false, true, "N.n4 3 = 10"),
            (true, true, "u1 1 2 = 103"),
            (false, true, "u1 1 2 = 3"),
        ],
    );
}

#[test]
fn out_param_marker_needs_the_global_head() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def o1 (outParam : Nat → Nat) (a : Nat) : Nat := outParam a
def o2 (a : Nat) : Nat := let semiOutParam := fun (x : Nat) => x + 7; semiOutParam a
namespace NO
def outParam (x : Nat) : Nat := x + 7
def o4 (a : Nat) : Nat := outParam a
end NO
class Conv (α : Type) (β : outParam Type) where
  conv : α → β
instance : Conv Nat Bool where
  conv n := n == 0
def o6 (n : Nat) : Bool := Conv.conv n
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "outparam",
        &[
            (true, true, "o1 (fun x => x + 7) 1 = 8"),
            (false, true, "o1 (fun x => x + 7) 1 = 1"),
            (true, true, "o2 1 = 8"),
            (false, true, "o2 1 = 1"),
            (true, true, "NO.o4 1 = 8"),
            (false, true, "NO.o4 1 = 1"),
            (true, true, "o6 0 = true"),
            (false, true, "o6 0 = false"),
        ],
    );
    refuted(
        &mut env,
        "outparam_general",
        "∀ (outParam : Nat → Nat), outParam 0 = 0",
        &["fun _ => rfl"],
    );
}

#[test]
fn notation_template_is_not_captured_at_the_use_site() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def gf (n : Nat) : Nat := n + 100
notation "G " x => gf x
def m1 (gf : Nat → Nat) : Nat := G 1
def m5 : Nat := let gf : Nat → Nat := fun _ => 0; G 1
notation "LAM " x => (fun y => y + x)
def m8 (y : Nat) : Nat := (LAM y) 1
notation "MT " x => match x with | 0 => gf 0 | _ + 1 => 1
def m10 (gf : Nat → Nat) : Nat := MT 0
notation "MV " x => match x with | 0 => 0 | k + 1 => gf k
def m11 (gf : Nat → Nat) (k : Nat) : Nat := MV (k + 3)
notation "MK " x => match x with | 0 => x | k + 1 => k
def m13 (k : Nat) : Nat := MK (k + 3)
namespace Q
def qq (n : Nat) : Nat := n + 1000
notation "QN " x => qq x
end Q
def qq (n : Nat) : Nat := n + 5
def q2 : Nat := QN 1
def q3 (qq : Nat → Nat) : Nat := QN 1
section
variable (gf : Nat → Nat)
def a1 : Nat := G 3
end
section
variable (hh : Nat → Nat)
local notation "GD " x => hh x
def d0 : Nat := GD 3
def d1 (hh : Nat → Nat) : Nat := GD 3
end
"#,
    )
    .expect("definitions elaborate");
    check(
        &mut env,
        "template",
        &[
            (true, true, "m1 (fun _ => 0) = 101"),
            (false, true, "m1 (fun _ => 0) = 0"),
            (true, true, "m5 = 101"),
            (false, true, "m5 = 0"),
            (true, true, "m8 10 = 11"),
            (false, true, "m8 10 = 2"),
            (true, true, "m10 (fun _ => 0) = 100"),
            (false, true, "m10 (fun _ => 0) = 0"),
            (true, true, "m11 (fun _ => 0) 5 = 107"),
            (false, true, "m11 (fun _ => 0) 5 = 0"),
            (true, true, "m13 5 = 7"),
            (false, true, "m13 5 = 5"),
            (true, true, "q2 = 1001"),
            (false, true, "q2 = 6"),
            (true, true, "q3 (fun _ => 0) = 1001"),
            (false, true, "q3 (fun _ => 0) = 0"),
            (true, true, "a1 = 103"),
            (false, true, "a1 = 3"),
            (true, true, "d0 (fun x => x + 1) = 4"),
            (true, true, "d1 (fun x => x + 1) (fun x => x + 2) = 4"),
            (false, true, "d1 (fun x => x + 1) (fun x => x + 2) = 5"),
        ],
    );
}
