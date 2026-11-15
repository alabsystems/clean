use super::*;
use clean_kernel::BinderInfo;
use clean_parser::SurfaceName;

fn state() -> ProofState {
    let field = LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(0),
        name: SurfaceName::component("field_0", true),
        ty: Expr::prop(),
        value: None,
    };
    let target = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    );
    let mut state = ProofState::with_context(Environment::default(), target, vec![field]);
    let goal = state.goals.front_mut().unwrap();
    goal.case_binders = vec![FVarId::new(0)];
    goal.tag = Some(SurfaceName::component("C.dot", true));
    state
}

#[test]
fn introduction_retains_case_identity_across_successor_metavariables() {
    let mut state = state();
    let before = state.current_goal().unwrap().clone();
    crate::tactic::proof_term::intro(&mut state, &SurfaceName::component("new", false)).unwrap();
    let after = state.current_goal().unwrap();
    assert_ne!(after.meta_id, before.meta_id);
    assert_eq!(after.case_binders, before.case_binders);
    assert_eq!(after.tag, before.tag);
    assert_eq!(after.local_ctx[0].fvar, before.case_binders[0]);
}

#[test]
fn clearing_a_case_field_cannot_retarget_its_id_to_a_reused_spelling() {
    let mut state = state();
    let old_name = state.current_goal().unwrap().local_ctx[0].name.clone();
    crate::tactic::hypothesis::clear(&mut state, &old_name).unwrap();
    crate::tactic::proof_term::intro(&mut state, &old_name).unwrap();
    let after = state.current_goal().unwrap();
    let replacement = after
        .local_ctx
        .iter()
        .find(|decl| decl.name == old_name)
        .unwrap();
    assert_ne!(replacement.fvar, FVarId::new(0));
    assert!(!after.case_binders.contains(&replacement.fvar));
}

#[test]
fn have_and_let_continuations_keep_case_origin_but_new_obligations_do_not() {
    for is_let in [false, true] {
        for supplied in [false, true] {
            let mut state = state();
            let before = state.current_goal().unwrap().clone();
            let value = supplied.then(|| Expr::fvar(FVarId::new(0)));
            let name = SurfaceName::component("added.name", true);
            if is_let {
                crate::tactic::have_let::let_(&mut state, &name, Expr::prop(), value).unwrap();
            } else {
                crate::tactic::forward::have_(&mut state, &name, Expr::prop(), value).unwrap();
            }
            assert_eq!(state.goals.len(), if supplied { 1 } else { 2 });
            if !supplied {
                let obligation = state.current_goal().unwrap();
                assert!(obligation.case_binders.is_empty());
                assert!(obligation.tag.is_none());
            }
            let continuation = state.goals.back().unwrap();
            assert_eq!(continuation.case_binders, before.case_binders);
            assert_eq!(continuation.tag, before.tag);
            assert!(continuation
                .local_ctx
                .iter()
                .any(|decl| decl.name.same_syntax(&name)));
        }
    }
}

#[test]
fn a_value_replacement_maps_case_origin_to_the_new_visible_fvar() {
    let mut state = state();
    let prior = state.current_goal().unwrap().clone();
    let replacement = state
        .replace_local_decl_with_value(FVarId::new(0), Expr::prop(), Expr::fvar(FVarId::new(0)))
        .unwrap();
    assert_ne!(replacement, FVarId::new(0));
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.case_binders, vec![replacement]);
    assert_eq!(goal.tag, prior.tag);
    assert_eq!(
        goal.local_ctx
            .iter()
            .find(|decl| decl.fvar == replacement)
            .unwrap()
            .name,
        prior.local_ctx[0].name
    );
}
