//! Checked adaptation into the remaining legacy dotted option-key protocol.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::FileContext;
use clean_kernel::{Environment, Name};

fn run(source: &str) -> (Environment, clean_elab::module_batch::ModuleOutcome) {
    let declarations = clean_parser::parse_file(source).unwrap();
    let mut env = Environment::new();
    let mut file = FileContext::new();
    let outcome = elaborate_module(
        &mut env,
        &mut file,
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    (env, outcome)
}

#[test]
fn ordinary_option_wrapper_preserves_checked_source_body() {
    let (env, outcome) = run("set_option pp.all false in\ndef identity (x : Type) : Type := x\n");
    assert!(
        outcome.is_clean() && outcome.committed,
        "{}",
        outcome.render_rejections()
    );
    assert!(env
        .get_const(&Name::anon().str("identity"))
        .unwrap()
        .value
        .is_some());
}

#[test]
fn quoted_dotted_option_is_retained_as_refusal_not_flattened() {
    let (env, outcome) = run("set_option «pp.all» false in\ndef identity (x : Type) : Type := x\n");
    assert!(!outcome.is_clean() && !outcome.committed);
    assert!(outcome.render_rejections().contains("option identity"));
    assert!(env.get_const(&Name::anon().str("identity")).is_none());
}
