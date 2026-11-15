// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use crate::tactic::{builtins_compound, builtins_wave3, LocalDecl};
use crate::FileContext;
use clean_kernel::{Environment, FVarId, Level, Name};
use clean_parser::{parse_name, Span};

fn name(text: &str) -> SurfaceName {
    parse_name(text).unwrap()
}

#[test]
fn name_slots_and_local_fvars_preserve_quoted_control_tokens() {
    let mut ps = ProofState::new(Environment::new(), Expr::prop());
    for (index, spelling) in ["_", "«_»", "A.B", "«A.B»", "«7»", "«*»"]
        .iter()
        .enumerate()
    {
        let source = if *spelling == "_" {
            SurfaceName::component("_", false)
        } else {
            name(spelling)
        };
        let encoded = crate::tactic::registry::encode_name_argument(&source);
        assert!(expr_to_hyp_name(&ps, &encoded)
            .unwrap()
            .same_syntax(&source));
        let fvar = FVarId::new(index as u64);
        ps.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
            binder_info: Default::default(),
            fvar,
            name: source.clone(),
            ty: Expr::prop(),
            value: None,
        });
        assert!(expr_to_hyp_name(&ps, &Expr::fvar(fvar))
            .unwrap()
            .same_syntax(&source));
    }
    let numeric = Name::anon().num(7);
    assert_eq!(
        expr_to_hyp_name(&ps, &Expr::const_(numeric.clone(), vec![Level::zero()]))
            .unwrap()
            .name(),
        &numeric
    );
    assert_ne!(
        expr_to_hyp_name(&ps, &Expr::const_(numeric, vec![])).unwrap(),
        name("«7»")
    );
}

#[test]
fn malformed_name_slot_cannot_fall_back_to_its_inner_constant() {
    let ps = ProofState::new(Environment::new(), Expr::prop());
    let encoded = crate::tactic::registry::encode_name_argument(&name("«_»"));
    let ExprKind::MData(rows, _) = encoded.kind() else {
        panic!("expected typed wrapper")
    };
    let bad = Expr::mdata(
        rows.clone(),
        Expr::const_(Name::anon().str("different"), vec![]),
    );
    assert!(expr_to_hyp_name(&ps, &bad).is_err());
    assert!(expr_to_hyp_name(&ps, &Expr::prop()).is_err());
}

#[test]
fn relative_or_anonymous_name_slot_cannot_select_an_ordinary_local() {
    let ps = ProofState::new(Environment::new(), Expr::prop());
    for invalid in [
        name("h").with_relative_constructor(),
        SurfaceName::default(),
    ] {
        let encoded = crate::tactic::registry::encode_name_argument(&invalid);
        assert!(expr_to_hyp_name(&ps, &encoded).is_err());
    }
    for spelling in ["h", "«.h»"] {
        let source = name(spelling);
        let encoded = crate::tactic::registry::encode_name_argument(&source);
        assert!(expr_to_hyp_name(&ps, &encoded)
            .unwrap()
            .same_syntax(&source));
    }
}

#[test]
fn surface_name_extraction_is_structural_and_rejects_non_names() {
    let quoted = name("«A.B»");
    let field = name("«c.d»");
    let expr = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(SurfaceExpr::Ident(Span::dummy(), quoted.clone())),
        Projection::Named(field),
    );
    assert_eq!(
        surface_expr_to_name(&expr).unwrap().name(),
        &Name::anon().str("A.B").str("c.d")
    );
    assert_ne!(surface_expr_to_name(&expr).unwrap(), name("A.B.c.d"));
    assert!(surface_expr_to_name(&SurfaceExpr::Hole(Span::dummy())).is_err());
    assert!(surface_expr_to_name(&SurfaceExpr::Ident(
        Span::dummy(),
        name("C").with_relative_constructor()
    ))
    .is_err());
    assert!(
        surface_expr_to_name(&SurfaceExpr::Ident(Span::dummy(), SurfaceName::default())).is_err()
    );
}

#[test]
fn case_tag_prefixes_and_suffixes_use_components_not_quoted_dots() {
    let goal = name("Outer.«A.B».C");
    assert!(builtins_compound::name_suffix_match(
        &goal,
        &name("«A.B».C")
    ));
    assert!(builtins_compound::name_prefix_match(
        &goal,
        &name("Outer.«A.B»")
    ));
    assert!(!builtins_compound::name_suffix_match(&goal, &name("B.C")));
    assert!(!builtins_compound::name_prefix_match(
        &goal,
        &name("Outer.A")
    ));
    assert!(!builtins_compound::name_suffix_match(
        &goal,
        &SurfaceName::default()
    ));
}

#[test]
fn alternative_renaming_uses_stable_owned_fvars_not_labels_or_current_meta() {
    let mut ps = ProofState::new(Environment::new(), Expr::prop());
    let fresh_goal = ps.fresh_meta(Expr::prop());
    let goal = ps.current_goal_mut().unwrap();
    goal.tag = Some(name("mk"));
    for (index, spelling) in ["«mk_0»", "«ih_mk_0»", "older", "field", "ih"]
        .iter()
        .enumerate()
    {
        goal.local_ctx.push(LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(index as u64),
            name: name(spelling),
            ty: Expr::prop(),
            value: None,
        });
    }
    goal.case_binders = vec![FVarId::new(3), FVarId::new(4), FVarId::new(999)];
    goal.meta_id = fresh_goal; // ordinary successor changed meta, not case ownership
    builtins_compound::rename_alternative_binders(
        ps.current_goal_mut().unwrap(),
        &[name("value"), name("«_»")],
        true,
    );
    let goal = ps.current_goal().unwrap();
    assert!(goal.local_ctx[0].name.same_syntax(&name("«mk_0»")));
    assert!(goal.local_ctx[1].name.same_syntax(&name("«ih_mk_0»")));
    assert_eq!(goal.local_ctx[2].name, name("older"));
    assert_eq!(goal.local_ctx[3].name, name("value"));
    assert!(goal.local_ctx[4].name.same_syntax(&name("«_»")));
    builtins_compound::rename_alternative_binders(
        ps.current_goal_mut().unwrap(),
        &[SurfaceName::component("_", false), name("final")],
        true,
    );
    assert_eq!(ps.current_goal().unwrap().local_ctx[3].name, name("value"));
}

#[test]
fn inaccessible_name_detection_does_not_capture_authored_lookalikes() {
    for spelling in ["_hidden", "«_hidden»", "«7»", "«0.name»"] {
        assert!(
            !builtins_wave3::is_generated_inaccessible_name(&name(spelling)),
            "{spelling}"
        );
    }
    assert!(builtins_wave3::is_generated_inaccessible_name(
        &SurfaceName::generated_path("_hidden")
    ));
    assert!(builtins_wave3::is_generated_inaccessible_name(
        &SurfaceName::from_name(Name::anon().num(7))
    ));
}

fn accepted(source: &str) -> Environment {
    let decls = clean_parser::parse_file(source).expect("actual source parses");
    let mut env = Environment::new();
    let mut file = FileContext::new();
    let outcome = elaborate_module(
        &mut env,
        &mut file,
        &[SourceUnit {
            id: UnitId(0),
            decls: &decls,
        }],
        BatchOptions::islands(),
    );
    assert!(
        outcome.is_clean() && outcome.committed,
        "{}",
        outcome.render_rejections()
    );
    env
}

#[test]
fn source_tactic_match_dispatches_quoted_constructors_in_actual_hole_order() {
    let env = accepted("inductive Out where\n  | first : Out\n  | second : Out\ninductive «A.B» where\n  | «c.d» : «A.B»\n  | other : «A.B»\ndef pick (x : «A.B») : Out := by\n  match x with\n  | «A.B».other => exact Out.second\n  | «A.B».«c.d» => exact Out.first\n");
    let ctx = crate::infer::ElabCtx::new(&env);
    for (input, output) in [("c.d", "first"), ("other", "second")] {
        let call = Expr::app(
            Expr::const_(Name::anon().str("pick"), vec![]),
            Expr::const_(Name::anon().str("A.B").str(input), vec![]),
        );
        assert_eq!(
            ctx.whnf(&call),
            Expr::const_(Name::anon().str("Out").str(output), vec![])
        );
    }
}

#[test]
fn source_cases_cannot_rename_a_user_hypothesis_with_a_generated_looking_name() {
    let env = accepted("inductive Data where\n  | first : Data\n  | second : Data\ninductive Box where\n  | mk : Data → Box\ndef keep (x : Data) (b : Box) : Data := by\n  have «mk_0» : Data := x\n  cases b with\n  | mk value => exact «mk_0»\n");
    let ctx = crate::infer::ElabCtx::new(&env);
    let first = Expr::const_(Name::anon().str("Data").str("first"), vec![]);
    let second = Expr::const_(Name::anon().str("Data").str("second"), vec![]);
    let boxed = Expr::app(
        Expr::const_(Name::anon().str("Box").str("mk"), vec![]),
        second,
    );
    let call = Expr::app(
        Expr::app(
            Expr::const_(Name::anon().str("keep"), vec![]),
            first.clone(),
        ),
        boxed,
    );
    assert_eq!(
        ctx.whnf(&call),
        first,
        "source local must not be captured as a case field"
    );
}
