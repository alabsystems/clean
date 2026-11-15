use super::*;
use clean_kernel::{FVarId, Name};

#[test]
fn quoted_script_names_keep_comments_and_command_separators() {
    let script = "intro «A;--/- B»; exact «A;--/- B» -- /- only a line comment\n";
    assert_eq!(
        parse_tactic_script(script),
        ["intro «A;--/- B»", "exact «A;--/- B»"]
    );
    assert_eq!(
        comment_strip::strip_block_comments("«/-x» /- real -/"),
        "«/-x»           "
    );
    assert_eq!(
        parse_tactic_script("exact \"a;--b\"; assumption"),
        ["exact \"a;--b\"", "assumption"]
    );
}

#[test]
fn exact_local_lookup_keeps_display_twins_and_shadowing() {
    let env = Environment::default();
    let quoted = script_name("«A.B»").unwrap();
    let qualified = script_name("A.B").unwrap();
    let state = elab_tactic::ProofState::with_context(
        env.clone(),
        Expr::prop(),
        vec![
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: qualified,
                ty: Expr::prop(),
                value: None,
            },
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: quoted.clone(),
                ty: Expr::prop(),
                value: None,
            },
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(2),
                name: quoted,
                ty: Expr::prop(),
                value: None,
            },
        ],
    );
    assert_eq!(
        resolve_expr_in_context(&state, "A.B", &env, "exact").unwrap(),
        Expr::fvar(FVarId::new(0))
    );
    assert_eq!(
        resolve_expr_in_context(&state, "«A.B»", &env, "exact").unwrap(),
        Expr::fvar(FVarId::new(2))
    );
    assert!(resolve_expr_in_context(&state, ".A.B", &env, "exact").is_err());
}

#[test]
fn script_name_bridge_retains_let_ids_and_real_receiver_priority() {
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::anon().str("Nat"), vec![]);
    let state = elab_tactic::ProofState::with_context(
        env.clone(),
        nat.clone(),
        vec![
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(41),
                name: script_name("A.B").unwrap(),
                ty: nat.clone(),
                value: None,
            },
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(42),
                name: script_name("«A.B»").unwrap(),
                ty: nat.clone(),
                value: Some(Expr::nat_lit(7)),
            },
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(43),
                name: script_name("A").unwrap(),
                ty: nat.clone(),
                value: None,
            },
            elab_tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(44),
                name: script_name("«.ctor»").unwrap(),
                ty: nat,
                value: None,
            },
        ],
    );
    assert_eq!(
        resolve_expr_in_context(&state, "«A.B»", &env, "exact").unwrap(),
        Expr::fvar(FVarId::new(42))
    );
    assert_eq!(
        resolve_expr_in_context(&state, "A", &env, "exact").unwrap(),
        Expr::fvar(FVarId::new(43))
    );
    assert_eq!(
        resolve_expr_in_context(&state, "«.ctor»", &env, "exact").unwrap(),
        Expr::fvar(FVarId::new(44))
    );
    // A real receiver must not be replaced by the unrelated qualified local.
    assert!(resolve_expr_in_context(&state, "A.B", &env, "exact").is_err());
    assert!(resolve_expr_in_context(&state, ".ctor", &env, "exact").is_err());
    assert!(resolve_expr_in_context(&state, "_root_.A.B", &env, "exact").is_err());
    let locals = &state.current_goal().unwrap().local_ctx;
    assert_eq!(
        locals.iter().map(|decl| decl.fvar).collect::<Vec<_>>(),
        [41, 42, 43, 44].map(FVarId::new)
    );
    assert_eq!(locals[1].value, Some(Expr::nat_lit(7)));
}

#[test]
fn target_name_protocol_preserves_escaped_keywords_and_refuses_missing_names() {
    let target = at_target(&["push_neg", "at", "«at»"]).unwrap().unwrap();
    assert_eq!(target.name(), &Name::anon().str("at"));
    assert!(!target.is_unescaped_component("at"));
    assert!(at_target(&["push_neg", "at"]).is_err());
    assert!(at_target(&["push_neg", "at", ".h"]).is_err());
    assert!(at_target(&["push_neg", "at", "h", "extra"]).is_err());
    assert!(at_target(&["unfold", "«at»"]).unwrap().is_none());
}
