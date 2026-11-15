//! Distinct-node costs and adversarial identity/scope cases for shared terms.
use super::*;
use crate::term_dag::{DagScope, NodeKey};
use crate::{MinimalEnv, RawExpr, RawLevel};

fn diamond(depth: u32, leaf: Term) -> Term {
    (0..depth).fold(leaf, |t, _| Term::app(t.clone(), t))
}

fn built<T>(f: impl FnOnce() -> T) -> (T, u64) {
    let before = NODES_BUILT.with(std::cell::Cell::get);
    let out = f();
    (
        out,
        NODES_BUILT
            .with(std::cell::Cell::get)
            .saturating_sub(before),
    )
}

fn shared_edges(term: &Term) {
    let mut node = term;
    while let TermKind::App(left, right) = node.kind() {
        assert!(Arc::ptr_eq(&left.kind, &right.kind));
        node = left;
    }
}

#[test]
fn substitutions_build_each_shared_node_once_per_scope() {
    // The tree has 2^81 - 1 nodes; there are only 81 shared nodes.
    let source = diamond(80, Term::bvar(0));
    let (lifted, nodes) = built(|| source.lift(2));
    assert!(nodes <= 81, "lift built {nodes}");
    assert_eq!(lifted.loose, 3);
    shared_edges(&lifted);
    let (instantiated, nodes) = built(|| source.instantiate(&Term::bvar(3)));
    assert!(nodes <= 82, "instantiate built {nodes}");
    assert_eq!(instantiated.loose, 4);
    shared_edges(&instantiated);
    let vals = [Term::bvar(3), Term::bvar(4)];
    let (many, nodes) = built(|| source.instantiate_many(&vals));
    assert!(nodes <= 81, "instantiate_many built {nodes}");
    assert_eq!(many.loose, 5);
    shared_edges(&many);
    let source = diamond(80, Term::sort(Level::param(0)));
    let (levels, nodes) = built(|| source.instantiate_levels(&[Level::zero()]).unwrap());
    assert!(nodes <= 81, "instantiate_levels built {nodes}");
    shared_edges(&levels);
}

#[test]
fn structural_equality_visits_shared_pairs_instead_of_tree_paths() {
    let left = diamond(80, Term::bvar(0));
    let right = diamond(80, Term::bvar(0));
    assert!(!Arc::ptr_eq(&left.kind, &right.kind));
    let (equal, steps) = walk_steps(|| left == right);
    assert!(equal);
    assert!(steps <= 162, "equality visited {steps} pairs");
    let mut collision = Term::bvar(1);
    let zero = Term::bvar(0);
    collision.hash = zero.hash;
    assert_ne!(collision, zero, "a hash match grants no equality");
}

#[test]
fn hash_consing_is_exact_scoped_and_identity_keys_retain_their_nodes() {
    let first = {
        let _scope = DagScope::enter();
        let first = Term::bvar(0);
        let second = Term::bvar(0);
        assert!(Arc::ptr_eq(&first.kind, &second.kind));
        // Deliberately collide the interner's hash bucket; the shape differs.
        let x = crate::term_dag::intern(TermKind::BVar(0), 17);
        let y = crate::term_dag::intern(TermKind::BVar(1), 17);
        assert!(!Arc::ptr_eq(&x, &y));
        first
    };
    {
        let _scope = DagScope::enter();
        assert!(!Arc::ptr_eq(&first.kind, &Term::bvar(0).kind));
    }
    let weak = Arc::downgrade(&first.kind);
    let key = NodeKey(first);
    assert!(weak.upgrade().is_some());
    drop(key);
    assert!(weak.upgrade().is_none());
}

#[test]
fn shared_raw_validation_keeps_binder_depth_in_its_key() {
    let var = RawExpr::Shared(Arc::new(RawExpr::BVar(0)));
    let raw = RawExpr::App(
        Box::new(RawExpr::Lam(
            BinderInfo::Default,
            Box::new(RawExpr::Sort(RawLevel::Zero)),
            Box::new(var.clone()),
        )),
        Box::new(var),
    );
    assert!(matches!(
        Term::validate_closed(&MinimalEnv::new(), &raw),
        Err(crate::ValidateError::OpenVar { index: 0, depth: 0 }),
    ));
}

#[test]
fn shared_closed_raw_nodes_validate_once_across_binder_depths() {
    let mut raw = RawExpr::Shared(Arc::new(RawExpr::Sort(RawLevel::Zero)));
    for _ in 0..80 {
        raw = RawExpr::Shared(Arc::new(RawExpr::Pi(
            BinderInfo::Default,
            Box::new(raw.clone()),
            Box::new(raw),
        )));
    }
    let (term, nodes) = built(|| Term::validate_closed(&MinimalEnv::new(), &raw).unwrap());
    assert!(
        nodes <= 81,
        "validation rebuilt {nodes} nodes for an 81-node DAG"
    );
    assert!(!term.has_loose_bvars());
}
