use super::*;
use crate::macro_cmd_ext::{traced_expand_recursive, MacroDependencyGraph};
use clean_kernel::Name;

fn source(text: &str) -> SurfaceName {
    clean_parser::parse_name(text).unwrap()
}
fn definition(name: SurfaceName, expansion_template: SurfaceExpr) -> MacroDef {
    MacroDef {
        name,
        expansion_template,
        pattern: vec![],
        scoping: MacroScoping::Term,
    }
}
fn literal(value: u64) -> SurfaceExpr {
    SurfaceExpr::Lit(
        Span::new(0, 0),
        clean_parser::SurfaceLit::nat(clean_kernel::BigNat::Small(value)),
    )
}

#[test]
fn macro_registry_keeps_literal_dot_and_path_names_distinct() {
    let mut registry = MacroRegistry::empty();
    registry.register(definition(source("A.B"), literal(1)));
    registry.register(definition(source("«A.B»"), literal(2)));
    assert_eq!(registry.count(), 2);
    let first = expand_macro(&registry, &source("A.B"), &[]).unwrap();
    let second = expand_macro(&registry, &source("«A.B»"), &[]).unwrap();
    assert_ne!(format!("{first:?}"), format!("{second:?}"));
    assert!(registry
        .lookup(&source("A.B").with_relative_constructor())
        .is_none());
}

#[test]
fn recursive_macro_expansion_and_graph_keep_numeric_identity() {
    let numeric = SurfaceName::from_name(Name::anon().num(7));
    let decimal = source("«7»");
    let entry = source("«A.B»");
    let mut registry = MacroRegistry::empty();
    registry.register(definition(numeric.clone(), literal(7)));
    registry.register(definition(decimal.clone(), literal(9)));
    registry.register(definition(
        entry.clone(),
        SurfaceExpr::Ident(Span::new(0, 0), numeric.clone()),
    ));
    let trace = traced_expand_recursive(&registry, &entry, &[], 4).unwrap();
    assert_eq!(
        trace
            .steps
            .iter()
            .map(|step| step.macro_name.clone())
            .collect::<Vec<_>>(),
        vec![entry.clone(), numeric.clone()]
    );
    let dependencies = MacroDependencyGraph::build(&registry).dependencies_of(&entry);
    assert_eq!(dependencies.into_iter().collect::<Vec<_>>(), vec![numeric]);
    assert!(registry.lookup(&decimal).is_some());
}

#[test]
fn relative_selector_is_not_a_recursive_macro_reference() {
    let entry = source("entry");
    let callee = source("callee");
    let mut registry = MacroRegistry::empty();
    registry.register(definition(callee.clone(), literal(5)));
    registry.register(definition(
        entry.clone(),
        SurfaceExpr::Ident(Span::new(0, 0), callee.with_relative_constructor()),
    ));
    let trace = traced_expand_recursive(&registry, &entry, &[], 4).unwrap();
    assert_eq!(trace.steps.len(), 1);
    assert!(MacroDependencyGraph::build(&registry)
        .dependencies_of(&entry)
        .is_empty());
}
