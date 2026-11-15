//! `variable … in <command>` through the elaborator. Lean's `cmd₁ in cmd₂` is
//! `section cmd₁ cmd₂ end`, so the variables scope over the one command.
//! Ground truth, pinned Lean v4.30.0-rc2: `variable (n : Nat) in def f : Nat
//! := n + 1` gives `f : Nat → Nat` with `f 2 = 3` by `rfl`; `variable {α :
//! Type} (a : α) in theorem t : a = a := rfl` gives `@t : ∀ {α : Type} (a : α),
//! a = a`; and a later `def g : Nat := n` is `Unknown identifier n`. Under
//! `variable (n : Nat)`, `include n in theorem t : True := True.intro` gives `t :
//! ∀ (n : Nat), True` while the next theorem stays `True`; after `include n`,
//! `omit n in` gives the next theorem `True` and the one after `∀ (n : Nat),
//! True` again. Breadth class (68) in docs/FRONTEND_CLASS_LEDGER.md.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Elaborate every declaration of `source`, continuing past a failed one,
/// and return the environment it leaves. One `FileContext` is threaded through
/// preprocessing AND elaboration, as `clean check` does (`cmd_core`): the
/// anonymous section elaborates its commands against that context, so an
/// `include n in` inside it sees the file's `variable (n : Nat)`.
fn elaborate_file(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source parses");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let _ = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx);
    }
    env
}

fn declared(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

#[test]
fn test_variable_in_def_takes_the_variable_as_its_argument() {
    let source = "variable (n : Nat) in\ndef vin_f : Nat := n + 1\n\
                  theorem vin_f_app : vin_f 2 = 3 := rfl\n";
    let env = elaborate_file(source);
    assert!(
        declared(&env, "vin_f"),
        "the scoped definition must register"
    );
    assert!(
        declared(&env, "vin_f_app"),
        "`vin_f` must take `n` as its one explicit argument (`vin_f 2 = 3` by rfl)"
    );
}

#[test]
fn test_variable_in_does_not_leak_past_its_command() {
    let source = "variable (n : Nat) in\ndef vin_f : Nat := n + 1\ndef vin_g : Nat := n\n";
    let env = elaborate_file(source);
    assert!(declared(&env, "vin_f"));
    assert!(
        !declared(&env, "vin_g"),
        "`n` must be out of scope after the command it was scoped to"
    );
}

#[test]
fn test_plain_variable_does_leak_control() {
    // The control for the test above: without `in`, the same later use of
    // `n` is in scope, so that test's refusal is the scoping and nothing else.
    let source = "variable (n : Nat)\ndef vin_f : Nat := n + 1\ndef vin_g : Nat := n\n";
    let env = elaborate_file(source);
    assert!(declared(&env, "vin_g"), "a plain `variable` stays in scope");
}

#[test]
fn test_variable_in_theorem_keeps_implicit_binders_implicit() {
    let source = "variable {α : Type} (a : α) in\ntheorem vin_t : a = a := rfl\n\
                  theorem vin_t_use : (5 : Nat) = 5 := vin_t 5\n";
    let env = elaborate_file(source);
    assert!(declared(&env, "vin_t"));
    assert!(
        declared(&env, "vin_t_use"),
        "`vin_t` must take `α` implicitly and `a` explicitly (`vin_t 5 : 5 = 5`)"
    );
}

#[test]
fn test_include_in_includes_the_variable_in_one_theorem_only() {
    let source = "variable (n : Nat)\ninclude n in\ntheorem vin_i : True := True.intro\n\
                  theorem vin_i2 : True := True.intro\n\
                  theorem vin_i_use : True := vin_i 5\n\
                  theorem vin_i2_use : True := vin_i2\n";
    let env = elaborate_file(source);
    assert!(declared(&env, "vin_i") && declared(&env, "vin_i2"));
    assert!(
        declared(&env, "vin_i_use"),
        "`include n in` must give `vin_i` the argument `n`"
    );
    assert!(
        declared(&env, "vin_i2_use"),
        "the include must not outlive its command: `vin_i2` takes no argument"
    );
}

#[test]
fn test_omit_in_omits_the_variable_from_one_theorem_only() {
    let source = "variable (n : Nat)\ninclude n\ntheorem vin_o : True := True.intro\n\
                  omit n in\ntheorem vin_o2 : True := True.intro\n\
                  theorem vin_o3 : True := True.intro\n\
                  theorem vin_o_use : True := vin_o 5\n\
                  theorem vin_o2_use : True := vin_o2\n\
                  theorem vin_o3_use : True := vin_o3 5\n";
    let env = elaborate_file(source);
    assert!(
        declared(&env, "vin_o_use"),
        "`include n` gives `vin_o` the argument `n`"
    );
    assert!(
        declared(&env, "vin_o2_use"),
        "`omit n in` must drop `n` from `vin_o2`"
    );
    assert!(
        declared(&env, "vin_o3_use"),
        "the omit must not outlive its command: `vin_o3` takes `n` again"
    );
}
