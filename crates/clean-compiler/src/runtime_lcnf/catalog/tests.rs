use super::{references, MAX_REFERENCE_DEPTH};
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Name};
use std::collections::BTreeSet;
use std::sync::Arc;

fn names(expected: &[&str]) -> BTreeSet<Name> {
    expected
        .iter()
        .map(|name| Name::from_string(name))
        .collect()
}

fn wrappers(mut value: Arc<Expr>, count: usize) -> Arc<Expr> {
    for _ in 0..count {
        value = Arc::new(Expr::from_kind(ExprKind::MData(vec![], value)));
    }
    value
}

#[test]
fn shared_nodes_are_charged_once_across_all_roots() {
    let mut shared = Arc::new(Expr::const_str("Leaf"));
    for _ in 0..30 {
        shared = Arc::new(Expr::app_arc(shared.clone(), shared));
    }
    let roots = vec![
        Expr::proj_arc(Name::from_string("Record"), 0, shared.clone()),
        Expr::app_arc(shared.clone(), shared),
    ];
    assert_eq!(
        references(roots.clone(), 33).unwrap(),
        names(&["Leaf", "Record"])
    );
    assert_eq!(
        references(roots, 32).unwrap_err(),
        "environment expression reference node bound"
    );
}

#[test]
fn a_cached_suffix_preserves_the_longest_path() {
    let suffix = wrappers(Arc::new(Expr::const_str("Leaf")), 7);
    // The right child is explored first and caches the entire suffix at depth one.
    let term = |prefix| Expr::app_arc(wrappers(suffix.clone(), prefix), suffix.clone());
    assert_eq!(
        references(vec![term(MAX_REFERENCE_DEPTH - 8)], 300).unwrap(),
        names(&["Leaf"])
    );
    assert_eq!(
        references(vec![term(MAX_REFERENCE_DEPTH - 7)], 300).unwrap_err(),
        "environment expression reference depth bound"
    );
    let fresh_deep = wrappers(Arc::new(Expr::bvar(0)), MAX_REFERENCE_DEPTH + 1);
    assert_eq!(
        references(vec![(*fresh_deep).clone()], 300).unwrap_err(),
        "environment expression reference depth bound"
    );
}

#[test]
fn accepted_shapes_collect_only_constants_and_projection_owners() {
    let app = Expr::app(Expr::const_str("Head"), Expr::bvar(0));
    let lam = Expr::lam(BinderInfo::Default, Expr::const_str("Domain"), app);
    let pi = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::nat_lit(4));
    let body = Expr::proj_arc(
        Name::from_string("Struct"),
        2,
        Arc::new(Expr::const_str("Record")),
    );
    let term = Expr::let_named(
        Name::from_string("local"),
        pi,
        lam,
        Expr::mdata(vec![], body),
        false,
    );
    assert_eq!(
        references(vec![term], 16).unwrap(),
        names(&["Domain", "Head", "Record", "Struct"])
    );
    assert_eq!(references(vec![], 0).unwrap(), names(&[]));
    assert_eq!(
        references(vec![Expr::prop()], 0).unwrap_err(),
        "environment expression reference node bound"
    );
    assert_eq!(
        references(vec![Expr::prop(), Expr::prop()], 1).unwrap_err(),
        "environment expression reference node bound"
    );
}

#[test]
fn unsupported_nodes_still_refuse_the_entire_inventory() {
    for invalid in [
        Expr::fvar(FVarId::new(9)),
        Expr::from_kind(ExprKind::Squash(Arc::new(Expr::const_str("Hidden")))),
    ] {
        let invalid = Arc::new(invalid);
        let term = Expr::app_arc(invalid.clone(), invalid);
        assert_eq!(
            references(vec![Expr::const_str("Valid"), term], 10).unwrap_err(),
            "unsupported environment expression in dependency inventory"
        );
    }
}
