use super::*;
use crate::tactic::library_search::{
    extract_typed_head_name, is_internal_search_name, library_search,
};
use crate::tactic::library_search_ext::{expr_contains_head, TypeFilterMode};
use crate::tactic::{LocalDecl, ProofState};
use clean_kernel::{Environment, Expr, FVarId, Level, Name};
use clean_parser::SurfaceName;

fn twins() -> [Name; 4] {
    [
        Name::anon().str("lemma.dot"),
        Name::anon().str("lemma").str("dot"),
        Name::anon().str("lemma").str("7"),
        Name::anon().str("lemma").num(7),
    ]
}

#[test]
fn local_search_results_preserve_all_typed_name_twins_and_actual_fvars() {
    let names = twins();
    let locals = names
        .iter()
        .enumerate()
        .map(|(index, name)| LocalDecl {
            binder_info: Default::default(),
            name: SurfaceName::from_name(name.clone()),
            fvar: FVarId::new(index as u64),
            ty: Expr::prop(),
            value: None,
        })
        .collect();
    let mut state = ProofState::with_context(Environment::default(), Expr::prop(), locals);
    let exact = exact_search(&mut state, 4).expect("local exact search");
    assert_eq!(exact.len(), 4);
    for (index, result) in exact.iter().enumerate() {
        assert_eq!(result.name, names[index]);
        assert_eq!(result.expr, Expr::fvar(FVarId::new(index as u64)));
    }
    let library = library_search(&mut state).expect("local library search");
    let locals: Vec<_> = library.iter().filter(|result| result.is_local).collect();
    assert_eq!(locals.len(), 4);
    for (index, result) in locals.iter().enumerate() {
        assert_eq!(result.name, names[index]);
        assert_eq!(result.expr, Expr::fvar(FVarId::new(index as u64)));
    }
}

#[test]
fn typed_search_head_filters_do_not_merge_display_twins() {
    let names = twins();
    for (index, name) in names.iter().enumerate() {
        let expr = Expr::const_(name.clone(), vec![]);
        assert_eq!(extract_typed_head_name(&expr), Some(name.clone()));
        let nested = Expr::app(
            Expr::const_(Name::anon().str("Wrapper"), vec![]),
            expr.clone(),
        );
        for (other_index, other) in names.iter().enumerate() {
            assert_eq!(
                TypeFilterMode::ExactHead.matches(&expr, other),
                index == other_index
            );
            assert_eq!(expr_contains_head(&nested, other), index == other_index);
        }
    }
}

#[test]
fn search_internal_spelling_heuristic_uses_real_components() {
    assert!(is_internal_search_name(
        &Name::anon().str("A").str("_private")
    ));
    assert!(!is_internal_search_name(&Name::anon().str("A._private")));
    assert!(!is_internal_search_name(&Name::anon().str("A").num(7)));
    assert_eq!(atomic_name(&Name::anon().str("rfl")), Some("rfl"));
    assert_eq!(atomic_name(&Name::anon().str("rfl").str("extra")), None);
    assert_eq!(atomic_name(&Name::anon().str("rfl").num(7)), None);
}

#[test]
fn forward_generated_names_preserve_rule_owner_and_avoid_exact_collisions() {
    let names = twins();
    let generated: Vec<_> = names
        .iter()
        .map(|name| aesop_builders::generate_forward_hyp_name(&[], name))
        .collect();
    for (index, name) in generated.iter().enumerate() {
        assert_eq!(
            name.name(),
            &names[index].clone().str("_aesop_forward").num(0)
        );
        for (other_index, other) in generated.iter().enumerate() {
            assert_eq!(name == other, index == other_index);
        }
        let occupied = LocalDecl {
            binder_info: Default::default(),
            name: name.clone(),
            fvar: FVarId::new(0),
            ty: Expr::prop(),
            value: None,
        };
        let fresh = aesop_builders::generate_forward_hyp_name(&[occupied], &names[index]);
        assert_eq!(
            fresh.name(),
            &names[index].clone().str("_aesop_forward").num(1)
        );
    }
}

#[test]
fn rewrite_search_applies_exact_quoted_local_not_its_hierarchical_twin() {
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let equality = |left, right| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat.clone(), Expr::nat_lit(left), Expr::nat_lit(right)],
        )
    };
    let good = SurfaceName::component("rewrite.dot", true);
    let bad = SurfaceName::generated_path("rewrite.dot");
    let mut locals = vec![LocalDecl {
        binder_info: Default::default(),
        name: bad,
        fvar: FVarId::new(0),
        ty: nat.clone(),
        value: None,
    }];
    // Eight actual local equations fill the bounded search without enumerating
    // unrelated environment lemmas. The first selected proof has the quoted name.
    for index in 0..8 {
        locals.push(LocalDecl {
            binder_info: Default::default(),
            name: if index == 0 {
                good.clone()
            } else {
                SurfaceName::from_name(Name::anon().str("other").num(index))
            },
            fvar: FVarId::new(index + 1),
            ty: equality(0, 1),
            value: None,
        });
    }
    let mut state = ProofState::with_context(env, equality(0, 0), locals);
    let results = rewrite_search(&mut state, 1).expect("quoted local is rewrite candidate");
    assert_eq!(results.len(), 1);
    assert_eq!(&results[0].name, good.name());
    assert_eq!(results[0].expr, Expr::fvar(FVarId::new(1)));
    rewrite_search_and_apply(&mut state).expect("typed rewrite selector");
    assert_eq!(state.current_goal().unwrap().target, equality(1, 1));
    crate::tactic::rfl(&mut state).expect("checked rewritten goal closes");
    assert!(state.is_complete());
}
