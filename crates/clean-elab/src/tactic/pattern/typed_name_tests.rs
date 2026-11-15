use super::{names, rintro::RIntroPattern, util::generate_fresh_hyp_name};
use crate::tactic::{hypothesis, LocalDecl, ProofState};
use clean_kernel::{Environment, Expr, FVarId, Name};
use clean_parser::{parse_name, SurfaceName};

fn source(text: &str) -> SurfaceName {
    parse_name(text).unwrap()
}
fn local(name: SurfaceName, id: u64) -> LocalDecl {
    LocalDecl {
        binder_info: Default::default(),
        name,
        fvar: FVarId::new(id),
        ty: Expr::const_(Name::anon().str("Nat"), vec![]),
        value: None,
    }
}

#[test]
fn quoted_rintro_delimiters_and_keywords_are_identifiers() {
    for text in [
        "«a|b»",
        "«a,b»",
        "«(x)»",
        "«⟨x⟩»",
        "«_»",
        "«rfl»",
        "A.«b|c»",
        "«A.B»",
    ] {
        let RIntroPattern::Name(name) = RIntroPattern::parse(text).unwrap() else {
            panic!("not an identifier: {text}")
        };
        assert!(name.same_syntax(&source(text)));
    }
    assert!(matches!(
        RIntroPattern::parse("_"),
        Ok(RIntroPattern::Wildcard)
    ));
    assert!(matches!(
        RIntroPattern::parse("rfl"),
        Ok(RIntroPattern::Rfl)
    ));
}

#[test]
fn rintro_actual_nested_delimiters_ignore_comment_and_quoted_separators() {
    let RIntroPattern::Or(branches) =
        RIntroPattern::parse("⟨«a,b», <x, «y|z»>⟩ | (right)").unwrap()
    else {
        panic!("expected alternation")
    };
    assert_eq!(branches.len(), 2);
    let RIntroPattern::Tuple(fields) = &branches[0] else {
        panic!("expected tuple")
    };
    assert_eq!(fields.len(), 2);
    assert!(matches!(&fields[1], RIntroPattern::Tuple(inner) if inner.len() == 2));
    let RIntroPattern::Name(name) = RIntroPattern::parse("a /- |,<>() -/").unwrap() else {
        panic!("comment became syntax")
    };
    assert_eq!(name.name(), source("a").name());
    assert!(
        matches!(RIntroPattern::parse("<a,<b,c>>"), Ok(RIntroPattern::Tuple(fields)) if fields.len() == 2)
    );
}

#[test]
fn rintro_malformed_names_and_delimiters_refuse_without_recovery() {
    for text in [
        "«unterminated",
        "⟨a,b>",
        "<a,b",
        "a |",
        "| a",
        "<a,>",
        "<,a>",
        "a b",
        ".ctor",
        "\"a|b\"",
    ] {
        assert!(RIntroPattern::parse(text).is_err(), "accepted {text:?}");
    }
}

#[test]
fn generated_suffix_keeps_typed_component_boundaries() {
    let literal = source("«A.B»");
    let path = source("A.B");
    assert_ne!(
        names::generated_suffix(&literal, "1"),
        names::generated_suffix(&path, "1")
    );
    let numeric = SurfaceName::from_name(Name::anon().num(7));
    assert_ne!(
        names::generated_suffix(&numeric, "1"),
        names::generated_suffix(&source("«7»"), "1")
    );
    let ctx = vec![
        local(numeric.clone(), 1),
        local(names::generated_suffix(&numeric, "1"), 2),
    ];
    let fresh = generate_fresh_hyp_name(&ctx, &numeric);
    assert_eq!(fresh, names::generated_suffix(&numeric, "2"));
    assert!(ctx.iter().all(|d| d.name != fresh));
}

#[test]
fn hypothesis_lookup_respects_quoted_identity_and_latest_shadow() {
    let ctx = vec![
        local(source("A.B"), 1),
        local(source("«A.B»"), 2),
        local(source("«A.B»"), 3),
    ];
    let mut state = ProofState::with_context(
        Environment::new(),
        Expr::const_(Name::anon().str("True"), vec![]),
        ctx,
    );
    hypothesis::rename(&mut state, &source("«A.B»"), &source("renamed")).unwrap();
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx[0].name, source("A.B"));
    assert_eq!(goal.local_ctx[1].name, source("«A.B»"));
    assert_eq!(goal.local_ctx[2].name, source("renamed"));
    hypothesis::clear(&mut state, &source("«A.B»")).unwrap();
    assert_eq!(
        state
            .current_goal()
            .unwrap()
            .local_ctx
            .iter()
            .map(|d| d.fvar)
            .collect::<Vec<_>>(),
        vec![FVarId::new(1), FVarId::new(3)]
    );
}

#[test]
fn relative_name_cannot_select_a_local_or_mutate_case_ownership() {
    let name = source("x");
    let mut state = ProofState::with_context(
        Environment::new(),
        Expr::const_(Name::anon().str("True"), vec![]),
        vec![local(name.clone(), 9)],
    );
    state.current_goal_mut().unwrap().case_binders = vec![FVarId::new(9)];
    let relative = name.clone().with_relative_constructor();
    assert!(hypothesis::clear(&mut state, &relative).is_err());
    assert!(hypothesis::rename(&mut state, &name, &relative).is_err());
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 1);
    assert_eq!(goal.local_ctx[0].name, name);
    assert_eq!(goal.case_binders, vec![FVarId::new(9)]);
}

#[test]
fn case_labels_do_not_reassign_the_owned_field_population() {
    use crate::tactic::case_field_names::{generated_case_field_name, CaseFieldKind};
    let label = generated_case_field_name(&source("intro"), 0, CaseFieldKind::Field);
    let mut state = ProofState::with_context(
        Environment::new(),
        Expr::const_(Name::anon().str("True"), vec![]),
        vec![local(label.clone(), 1), local(source("actual"), 2)],
    );
    state.current_goal_mut().unwrap().case_binders = vec![FVarId::new(2)];
    hypothesis::rename(&mut state, &source("actual"), &label).unwrap();
    assert_eq!(
        state.current_goal().unwrap().case_binders,
        vec![FVarId::new(2)]
    );
    hypothesis::clear(&mut state, &label).unwrap();
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx[0].fvar, FVarId::new(1));
    assert_eq!(goal.case_binders, vec![FVarId::new(2)]); // Consumer intersects visible FVars.
}

#[test]
fn deferred_branch_identity_does_not_use_shared_field_ids_or_labels() {
    let target = Expr::const_(Name::anon().str("True"), vec![]);
    let mut state = ProofState::with_context(
        Environment::new(),
        target.clone(),
        vec![local(source("same"), 7)],
    );
    let first_meta = state.current_goal().unwrap().meta_id;
    let mut second = state.current_goal().unwrap().clone();
    second.meta_id = state.fresh_meta(target);
    let second_meta = second.meta_id;
    state.goals.push_back(second.clone());
    assert_eq!(
        super::rintro::pending_branch_position(&state, first_meta).unwrap(),
        0
    );
    assert_eq!(
        super::rintro::pending_branch_position(&state, second_meta).unwrap(),
        1
    );
    state.goals.remove(0);
    assert_eq!(
        super::rintro::pending_branch_position(&state, second_meta).unwrap(),
        0
    );
    assert!(super::rintro::pending_branch_position(&state, first_meta).is_err());
    state.goals.push_back(second);
    assert!(super::rintro::pending_branch_position(&state, second_meta).is_err());
}

#[test]
fn builtin_head_recognition_never_accepts_display_suffix_lookalikes() {
    for spelling in [
        Name::anon().str("Other").str("True"),
        Name::anon().str("Other.True"),
        Name::anon().num(7),
    ] {
        assert!(!super::util::is_true_prop(&Expr::const_(spelling, vec![])));
    }
    assert!(super::util::is_true_prop(&Expr::const_(
        source("«True»").into_name(),
        vec![]
    )));
    let class = Name::anon().str("A.B").num(7);
    assert_eq!(
        super::util::extract_class_name(&Expr::app(
            Expr::const_(class.clone(), vec![]),
            Expr::nat_lit(0)
        )),
        Some(class)
    );
    for name in [
        Name::anon().str("Other").str("Exists"),
        Name::anon().str("Other.Exists"),
    ] {
        let ty = Expr::app(
            Expr::app(Expr::const_(name, vec![]), Expr::nat_lit(0)),
            Expr::nat_lit(1),
        );
        assert!(super::util::try_extract_exists(&ty).is_none());
    }
}

#[test]
fn historical_prop_aliases_are_exact_paths_not_printed_suffixes() {
    for (label, recognize) in [
        ("True", super::util::is_true_prop as fn(&Expr) -> bool),
        ("False", super::util::is_false_prop as fn(&Expr) -> bool),
    ] {
        let path = Name::anon().str("Prop").str(label);
        let quoted = Name::anon().str(format!("Prop.{label}"));
        assert_eq!(path.to_string(), quoted.to_string());
        assert!(recognize(&Expr::const_(path, vec![])));
        assert!(!recognize(&Expr::const_(quoted, vec![])));
        assert!(!recognize(&Expr::const_(
            Name::anon().str("Other").str("Prop").str(label),
            vec![]
        )));
        assert!(!recognize(&Expr::app(
            Expr::const_(Name::anon().str("Prop").str(label), vec![]),
            Expr::nat_lit(0)
        )));
    }
}

#[test]
fn quoted_underscore_never_selects_an_anonymous_wildcard() {
    let plain = SurfaceName::component("_", false);
    let generated = SurfaceName::generated_path("_");
    let quoted = source("«_»");
    for wildcard in [&plain, &generated] {
        assert!(!names::local_name_matches(wildcard, &quoted));
        assert!(!names::local_name_matches(&quoted, wildcard));
    }
    assert!(names::local_name_matches(&quoted, &quoted));
}
