// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A notation is a macro: Lean 4.8.0 substitutes the operands into the
//! template's syntax, and the template's identifiers carry the expansion's
//! macro scope. Clean's template walks
//! (`clean_parser::mark_template_free_references`,
//! `clean_parser::instantiate_notation_template`) used to cover only a
//! fragment of the surface syntax; a template outside it (a `match`, a `do`
//! block, a `by` block, a `let rec`, an `if let`, …) was APPLIED to its
//! operands as a function instead, and was left unmarked. The operand was
//! then elaborated outside the template and a free name resolved with the
//! opens of the use site. The round-25 verifier of db37ea99b measured 112
//! false calls in `tp3` and 10 in `tp1` (2026-09-26).
//!
//! Every `T` statement is accepted by Lean 4.8.0 and every `F` statement is
//! refused by it (both measured, `probes/t_mirror.lean` of the round-25
//! notation-templates report); each `F` is the value db37ea99b computed. The
//! setup of every case is checked to elaborate on its own, so each refusal is
//! the statement's.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

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

/// Parse, elaborate, kernel-check and register `source` with ONE file
/// context (the `clean check` driver contract).
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(failures.join("\n"));
        }
    }
    Ok(env)
}

/// [`elaborate_module`] that goes on past a failing declaration, as the
/// `clean check` driver does: the environment and every failure.
fn elaborate_all(source: &str) -> (Environment, Vec<String>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("recovering parse");
    let mut failures = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => collect_failures(&result, &mut failures),
            Err(e) => failures.push(e.to_string()),
        }
    }
    (env, failures)
}

/// `(holds, statement)` over `setup`: a statement that holds is proved
/// axiom-free by `rfl`; one that does not is refused by `rfl` and `decide`.
fn check(setup: &str, cases: &[(bool, &str)]) {
    elaborate_module(setup).unwrap_or_else(|e| panic!("setup must elaborate: {e}\n{setup}"));
    for (id, (holds, statement)) in cases.iter().enumerate() {
        if *holds {
            let name = format!("case_true_{id}");
            let env = elaborate_module(&format!("{setup}\ntheorem {name} : {statement} := rfl\n"))
                .unwrap_or_else(|e| panic!("{statement} must hold: {e}"));
            let deps = env
                .axiom_deps(&Name::from_string(&name))
                .expect("registered theorem");
            assert!(deps.is_empty(), "{statement}: depends on axioms: {deps:?}");
            continue;
        }
        for proof in ["rfl", "by decide"] {
            let name = format!("case_false_{id}");
            let error = match elaborate_module(&format!(
                "{setup}\ntheorem {name} : {statement} := {proof}\n"
            )) {
                Ok(_) => panic!("FALSE theorem accepted: {statement} := {proof}"),
                Err(error) => error,
            };
            assert!(
                !error.contains("parse error"),
                "negative must parse: {error}"
            );
        }
    }
}

const PRELUDE: &str = "set_option quotPrecheck false\n\
namespace A\ndef kq : Nat := 1\nend A\n\
namespace B\ndef kq : Nat := 2\nend B\n\
def kz : Nat := 1000\n";

#[test]
fn operands_are_elaborated_inside_templates_of_every_form() {
    check(
        &format!(
            "{PRELUDE}\
notation \"Cm \" x => match (x : Int) with | n => (n + 10).toNat\n\
def m1 (a b : Nat) : Nat := (Cm (a - b)) + b\n\
notation \"Co \" x => Id.run (do let y : Int := x; return (y + 10).toNat)\n\
def m2 (a b : Nat) : Nat := (Co (a - b)) + b\n\
notation \"Cb \" x => (by exact ((x : Int) + 10).toNat : Nat)\n\
def m4 (a b : Nat) : Nat := (Cb (a - b)) + b\n\
notation \"Cr \" x => (let rec go (n : Int) : Nat := (n + 10).toNat; go x)\n\
def m5 (a b : Nat) : Nat := (Cr (a - b)) + b\n\
notation \"Ci \" x => (if let some n := some (x : Int) then (n + 10).toNat else 0)\n\
def m6 (a b : Nat) : Nat := (Ci (a - b)) + b\n"
        ),
        &[
            (true, "m1 0 2 = 10"),
            (false, "m1 0 2 = 12"),
            (true, "m2 0 2 = 10"),
            (false, "m2 0 2 = 12"),
            (true, "m4 0 2 = 10"),
            (false, "m4 0 2 = 12"),
            (true, "m5 0 2 = 10"),
            (false, "m5 0 2 = 12"),
            (true, "m6 0 2 = 10"),
            (false, "m6 0 2 = 12"),
        ],
    );
}

#[test]
fn free_names_of_every_template_form_resolve_where_it_is_declared() {
    check(
        &format!(
            "{PRELUDE}\
section\nopen A\n\
notation \"Todo \" x => Id.run (do let y := x; return y + kq)\n\
notation \"Tby \" x => (by exact x + kq : Nat)\n\
macro \"Mapp\" x:term : term => `(($x + kq))\n\
end\n\
open B in\ndef m3 (a b : Nat) : Nat := Todo (a * b)\n\
open B in\ndef m7 (a : Nat) : Nat := Tby a\n\
open B in\ndef g1 (a : Nat) : Nat := Mapp a\n"
        ),
        &[
            (true, "m3 7 5 = 36"),
            (false, "m3 7 5 = 37"),
            (true, "m7 7 = 8"),
            (false, "m7 7 = 9"),
            (true, "g1 5 = 6"),
            (false, "g1 5 = 7"),
        ],
    );
}

#[test]
fn template_binders_never_capture_operands_and_patterns_resolve_at_the_declaration() {
    check(
        &format!(
            "{PRELUDE}\
notation \"Pk \" x => match (5 : Nat) with | kz => x + kz\n\
notation \"Dk \" x => Id.run (do let kz := 5; return x + kz)\n\
notation \"Ik \" x => ((by intro kz; exact x + kz : Nat → Nat) 5)\n\
notation \"Hk \" x => (have : Nat := 5; this + x)\n\
def c1 : Nat := Pk kz\ndef c2 : Nat := Dk kz\ndef c3 : Nat := Ik kz\n\
def c4 (this : Nat) : Nat := Hk (this * 2)\n\
notation \"Mo \" x => match (x : Option Nat) with | none => 7 | some a => a\n\
def q2 (none : Nat) (o : Option Nat) : Nat := (Mo o) + none\n\
notation \"PM \" x => match (5 : Nat) with | kz => x + kz\n\
def e3 (a : Nat) : Nat := PM (PM (a + kz))\n"
        ),
        &[
            (true, "c1 = 1005"),
            (true, "c2 = 1005"),
            (true, "c3 = 1005"),
            (true, "c4 10 = 25"),
            (true, "q2 1 (some 3) = 4"),
            (false, "q2 1 (some 3) = 8"),
            (true, "q2 1 Option.none = 8"),
            (true, "e3 1 = 1011"),
        ],
    );
}

#[test]
fn a_section_dot_operand_belongs_to_the_parentheses_around_the_use() {
    check(
        &format!(
            "{PRELUDE}\
notation \"N \" x => (· + x)\n\
def q4 (a : Nat) : Nat → Nat := (N ·) a\n\
notation x \" ⊕⊕ \" y => (fun kz => x * 10 + y + kz) 0\n\
def e11 : Nat → Nat → Nat := (· ⊕⊕ ·)\n\
notation \"DUP \" x => x + x\n\
def e12 : Nat → Nat := (DUP ·)\n\
notation \"LB \" x => fun x => x + 1\n\
def e7 : Nat := (LB q) 4\n"
        ),
        &[
            (true, "q4 3 4 = 7"),
            (true, "e11 1 2 = 12"),
            (true, "e12 4 = 8"),
            (true, "e7 = 5"),
        ],
    );
}

/// `(fun kz b => …) a kz`: every argument of a β-redex is outside every
/// binder of its lambda — also when an infix notation's head is the lambda.
#[test]
fn a_lambda_applied_to_an_argument_naming_its_binder() {
    check(
        &format!(
            "{PRELUDE}\
def b1 (a : Nat) : Nat := (fun kz b => kz + b * 10) a kz\n\
infixl:65 \" +++ \" => fun kz b => kz + b * 10\n\
def e5 (a : Nat) : Nat := a +++ kz\n"
        ),
        &[
            (true, "b1 1 = 10001"),
            (false, "b1 1 = 11"),
            (true, "e5 1 = 10001"),
            (false, "e5 1 = 11"),
        ],
    );
}

/// A template form whose binding structure Clean does not model refuses the
/// DECLARATION, and every use of it — a use is never read as other syntax
/// (here, a call of the definition spelled like the notation's keyword).
#[test]
fn an_unmodelled_template_form_is_refused_never_applied() {
    let template = "(q(x) : Nat)";
    let declaration = format!("{PRELUDE}notation \"TM \" x => {template}\n");
    let error = elaborate_module(&declaration)
        .err()
        .unwrap_or_else(|| panic!("the declaration must be refused: {template}"));
    assert!(error.contains("refused"), "{template}: {error}");
    let use_site = format!(
        "{PRELUDE}def TM (n : Nat) : Nat := n + 7\n\
         notation \"TM \" x => {template}\n\
         def r (a : Nat) : Nat := TM a\n\
         theorem r_t : r 1 = 8 := rfl\n"
    );
    let (env, failures) = elaborate_all(&use_site);
    assert!(
        env.get_const(&Name::from_string("TM")).is_some(),
        "the definition itself stands"
    );
    assert!(
        env.get_const(&Name::from_string("r")).is_none()
            && env.get_const(&Name::from_string("r_t")).is_none(),
        "{template}: a use of the refused notation must be refused, not read as `TM a`: {failures:?}"
    );
}

const STRUCTS: &str = "structure SX where\n  x : Nat := 0\n  w : Nat := 0\n\
def fg (x w : Nat) : Nat := x * 10 + w\n\
def sx0 : SX := { x := 4, w := 9 }\n\
structure SI where\n  v : Nat := 0\n  x : Nat := 0\n\
structure SO where\n  x : SI := {}\n  w : SI := { v := 5 }\n\
def so0 : SO := { x := { v := 1, x := 2 }, w := { v := 3, x := 4 } }\n";

/// Lean's `notation` antiquotes EVERY identifier spelled like an operand
/// variable — a structure field, a `with` field, a field abbreviation, a
/// named-argument name, a projection field, a constructor alternative, a
/// leading-dot constructor — and a gap-free dotted run (`x.succ`, `(e).x.v`,
/// the field path `x.v := e`) is ONE identifier, never an operand variable.
/// ebcf3eb20 left the name positions as written and dropped the operand:
/// `si2 = 5`, `up2 = 0`, `sn1 = 30` were accepted (Lean 4.8.0: 505, 7, 3,
/// measured by the round-25 verifier, `rep_A_newly_false.lean`, `l24.lean`),
/// and so were `na1 7 = 12`, `pj1 7 = 4` on every build (Lean: 21, 9).
#[test]
fn every_identifier_spelled_like_an_operand_variable_is_that_operand() {
    check(
        &format!(
            "{PRELUDE}{STRUCTS}\
notation \"SI \" x => (({{ x := 5 }} : SX).x + ({{ x := 5 }} : SX).w * 100)\n\
def si2 : Nat := SI w\n\
notation \"UP \" x => ((fun (s : SX) => {{ s with x := 7 }}) {{}}).w\n\
def up2 : Nat := UP w\n\
notation \"NA \" x => fg (x := 1) 2\n\
def na1 (w : Nat) : Nat := NA w\n\
notation \"PJ \" x => (sx0).x\n\
def pj1 (w : Nat) : Nat := PJ w\n\
notation \"SN \" x => (fun (s : SX) => s.1 * 10 + s.2) {{ x := 3 }}\n\
def sn1 : Nat := SN w\n\
notation \"AB \" x => (({{ x }} : SX).w)\n\
def ab1 (w : Nat) : Nat := AB w\n\
notation \"SW \" x => (sx0.x + 0)\n\
def sw1 : Nat := SW w\n\
notation \"PC \" x => (so0).x.v\n\
def pc1 : Nat := PC w\n\
notation \"FP \" x => ({{ so0 with x.v := 9 }} : SO).w.v\n\
def fp1 : Nat := FP w\n\
notation \"IA \" x => (by cases (3 : Nat) with | zero => exact 1 | x n => exact n + 10 : Nat)\n\
def ia1 : Nat := IA succ\n\
notation \"RC \" x => ((.x : Option Nat).getD 7)\n\
def rc1 : Nat := RC none\n\
def x.succ : Nat := 77\n\
notation \"DT \" x => x.succ + 0\n\
def d2 (a : Nat) : Nat := DT a\n\
notation \"F1 \" y => (({{ y := 5 }} : SX).x)\n\
def cd1 : Nat := (F1 ·) 3\n\
notation \"F2 \" y => (fg (y := 1) 2)\n\
def cd2 : Nat := (F2 ·) 3\n"
        ),
        &[
            (true, "si2 = 505"),
            (false, "si2 = 5"),
            (true, "up2 = 7"),
            (false, "up2 = 0"),
            (true, "na1 7 = 21"),
            (false, "na1 7 = 12"),
            (true, "pj1 7 = 9"),
            (false, "pj1 7 = 4"),
            (true, "sn1 = 3"),
            (false, "sn1 = 30"),
            (true, "ab1 3 = 3"),
            (true, "sw1 = 4"),
            (true, "pc1 = 1"),
            (true, "fp1 = 3"),
            (true, "ia1 = 12"),
            (true, "rc1 = 7"),
            (true, "d2 1 = 77"),
            (false, "d2 1 = 2"),
            (true, "cd1 = 5"),
            (true, "cd2 = 12"),
        ],
    );
}

/// An operand that is no identifier cannot stand in a name position: Lean
/// refuses the use ("unexpected structure syntax", "invalid argument name");
/// ebcf3eb20 accepted it (the round-25 verifier's `f0526`, `f0540`).
#[test]
fn an_operand_in_a_name_position_must_be_an_identifier() {
    for (notation, template) in [
        ("SI", "(({ x := 5 } : SX).w)"),
        ("AB", "(({ x } : SX).w)"),
        ("NA", "fg (x := 1) 2"),
        ("PJ", "(sx0).x"),
    ] {
        let source = format!(
            "{PRELUDE}{STRUCTS}notation \"{notation} \" x => {template}\n\
             def r (a : Nat) : Nat := {notation} (a + 1)\n"
        );
        let (env, _) = elaborate_all(&source);
        assert!(
            env.get_const(&Name::from_string("r")).is_none(),
            "{template}: Lean refuses the use"
        );
    }
}

/// `obtain`/`rcases`/`rintro` and a tactic `match` in a template are expanded
/// with their pattern variables renamed apart from the operands, as Lean's
/// macro scope keeps them apart. ebcf3eb20 refused these templates, which
/// db37ea99b, e3f696689 and 3f45fb7c6 accepted with Lean's values
/// (`rep_newly_refused.lean`).
#[test]
fn tactic_pattern_binders_of_a_template_are_expanded_hygienically() {
    check(
        &format!(
            "{PRELUDE}\
notation \"OB \" x => (by obtain ⟨a, b⟩ := ((x, 1) : Nat × Nat); exact a * 10 + b : Nat)\n\
def ob1 (n : Nat) : Nat := OB n\n\
notation \"RC \" x => (by rcases ((x, 2) : Nat × Nat) with ⟨a, b⟩; exact a * 10 + b : Nat)\n\
def rc1 (n : Nat) : Nat := RC n\n\
notation \"RI \" x => ((by rintro ⟨a, b⟩; exact a * 10 + b + x : Nat × Nat → Nat) (3, 4))\n\
def ri1 (n : Nat) : Nat := RI n\n\
notation \"TM \" x => (by match x with | 0 => exact 5 | n + 1 => exact n : Nat)\n\
def tm1 (n : Nat) : Nat := TM n\n\
notation \"OBk \" x => (by obtain ⟨kz, b⟩ := ((5, 1) : Nat × Nat); exact kz * 10 + b + x : Nat)\n\
def o1 : Nat := OBk kz\n\
notation \"RCk \" x => (by rcases ((5, 1) : Nat × Nat) with ⟨kz, b⟩; exact kz * 10 + b + x : Nat)\n\
def o2 (kz : Nat) : Nat := RCk kz\n\
notation \"TMk \" x => (by match (5 : Nat) with | 0 => exact 0 | kz + 1 => exact kz + x : Nat)\n\
def o4 (kz : Nat) : Nat := TMk kz\n"
        ),
        &[
            (true, "ob1 4 = 41"),
            (true, "rc1 4 = 42"),
            (true, "ri1 4 = 38"),
            (true, "tm1 4 = 3"),
            (true, "o1 = 1051"),
            (false, "o1 = 51"),
            (true, "o2 7 = 58"),
            (false, "o2 7 = 102"),
            (true, "o4 7 = 11"),
            (false, "o4 7 = 8"),
        ],
    );
}

/// A template's free name in a hypothesis position (`clear`, `revert`,
/// `at`, `specialize`, a `cases` target) never names a hypothesis of the use
/// site: Lean's `kh✝` matches no user local, and a global it resolves to is
/// no hypothesis. Every build accepted `c1 0 = 1`, `c2 7 = 8`,
/// `c10 true = 1` (Lean: 2 each, `rep_open_classes.lean`).
#[test]
fn a_template_name_in_a_hypothesis_position_names_no_use_site_hypothesis() {
    check(
        &format!(
            "{PRELUDE}\
notation \"CK \" x => (by first | (clear kh; exact x) | exact 2 : Nat)\n\
def c1 (kh : Nat) : Nat := CK 1 + kh * 0\n\
notation \"RV \" x => (by first | (revert kh; exact fun k => k + x) | exact 2 : Nat)\n\
def c2 (kh : Nat) : Nat := RV 1 + kh * 0\n\
notation \"CA \" x => (by first | (cases kh <;> exact 1) | exact x : Nat)\n\
def c10 (kh : Bool) : Nat := CA 2\n\
notation \"RVz \" x => (by first | (revert kz; exact fun k => x + 2) | exact x + 1 : Nat)\n\
def g1 (a kz : Nat) : Nat := (RVz a) + kz * 0\n\
notation \"SAz \" x => (by first | (simp at kz; exact x) | exact x + 1 : Nat)\n\
def g2 (a b : Nat) : Nat := have kz : b + 0 = b := Nat.add_zero b; SAz a\n\
notation \"SPz \" x => (by first | (specialize kz 0; exact x) | exact x + 1 : Nat)\n\
def g3 (a b : Nat) : Nat := (fun (kz : Nat → Nat) => SPz a) (fun n => n + b)\n\
notation \"RWz \" x => (by first | (rw [Nat.add_zero] at kz; exact x) | exact x + 1 : Nat)\n\
def g4 (a b : Nat) : Nat := have kz : b + 0 = b := Nat.add_zero b; RWz a\n\
notation \"CAz \" x => (by first | (cases kz <;> exact x) | exact x + 1 : Nat)\n\
def g5 (a b : Nat) : Nat := (fun (kz : Bool) => CAz a) (b == 2)\n"
        ),
        &[
            (true, "c1 0 = 2"),
            (false, "c1 0 = 1"),
            (true, "c2 7 = 2"),
            (false, "c2 7 = 8"),
            (true, "c10 true = 2"),
            (false, "c10 true = 1"),
            (true, "g1 0 0 = 1"),
            (false, "g1 0 0 = 2"),
            (true, "g2 0 0 = 1"),
            (false, "g2 0 0 = 0"),
            (true, "g3 0 0 = 1"),
            (false, "g3 0 0 = 0"),
            (true, "g4 0 0 = 1"),
            (false, "g4 0 0 = 0"),
            (true, "g5 3 0 = 3"),
        ],
    );
}

/// Macros the quotation grammar cannot read (a typed antiquotation `$x:term`)
/// are read by the legacy quotation reader; their names resolve where the
/// macro is declared too. Every build accepted `m1 5 = 7` and
/// `m8 100 5 = 105` (Lean: 6, 6).
#[test]
fn a_legacy_read_macro_template_resolves_where_it_is_declared() {
    check(
        &format!(
            "{PRELUDE}\
section\nopen A\nmacro \"M1 \" x:term : term => `(Nat.add kq $x:term)\nend\n\
open B in def m1 (a : Nat) : Nat := M1 a\n\
def m8 (kq : Nat) (a : Nat) : Nat := M1 a + kq * 0\n"
        ),
        &[
            (true, "m1 5 = 6"),
            (false, "m1 5 = 7"),
            (true, "m8 100 5 = 6"),
            (false, "m8 100 5 = 105"),
        ],
    );
}

/// A tactic macro is a template too: its free names resolve where it is
/// declared. Every build accepted `t1 = 2`, `t3 50 = 50` (Lean: 1, 1).
#[test]
fn a_tactic_macro_template_resolves_where_it_is_declared() {
    check(
        &format!(
            "{PRELUDE}\
section\nopen A\nmacro \"mt1\" : tactic => `(tactic| exact kq)\n\
syntax \"mt2\" : tactic\nmacro_rules | `(tactic| mt2) => `(tactic| exact kq)\nend\n\
open B in def t1 : Nat := by mt1\n\
def t3 (kq : Nat) : Nat := (by mt1 : Nat) + kq * 0\n\
open B in def t4 : Nat := by mt2\n"
        ),
        &[
            (true, "t1 = 1"),
            (false, "t1 = 2"),
            (true, "t3 50 = 1"),
            (false, "t3 50 = 50"),
            (true, "t4 = 1"),
            (false, "t4 = 2"),
        ],
    );
}

/// `set_option hygiene false` makes a template the bare substitution: its
/// names resolve at the use and its binders capture (Lean 4.8.0,
/// `quoteSyntax`). new and db37ea99b accepted `h1 5 = 1001`, `h4 5 = 1001`
/// (Lean: 6, 6); every build computed the binder case `f1 0 0 = 1005`
/// (Lean: 10). The option is scoped: the next notation is hygienic.
#[test]
fn an_unhygienic_template_is_the_bare_substitution() {
    check(
        &format!(
            "{PRELUDE}\
set_option hygiene false in\nnotation \"HF \" x => x + kz\n\
def h1 (kz : Nat) : Nat := HF 1\n\
set_option hygiene false in\nmacro \"HM \" x:term : term => `($x + kz)\n\
def h4 (kz : Nat) : Nat := HM 1\n\
set_option hygiene false in\nmacro \"KW \" x:term : term => `((let kz := 5; $x + kz))\n\
def f1 (a b : Nat) : Nat := (KW kz) + a\n\
def f2 (kz : Nat) : Nat := KW kz\n\
set_option hygiene false in\nnotation \"KN \" x => (let kz := 5; x + kz)\n\
def f3 (a b : Nat) : Nat := (KN kz) + a\n\
notation \"HG \" x => x + kz\n\
def h9 (kz : Nat) : Nat := HG 1\n"
        ),
        &[
            (true, "h1 5 = 6"),
            (false, "h1 5 = 1001"),
            (true, "h4 5 = 6"),
            (false, "h4 5 = 1001"),
            (true, "f1 0 0 = 10"),
            (false, "f1 0 0 = 1005"),
            (true, "f2 7 = 10"),
            (false, "f2 7 = 12"),
            (true, "f3 0 0 = 10"),
            (true, "h9 5 = 1001"),
            (false, "h9 5 = 6"),
        ],
    );
}
