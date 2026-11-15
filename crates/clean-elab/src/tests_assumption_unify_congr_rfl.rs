// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `assumption` on a goal that still carries metavariables matches a
//! hypothesis by UNIFICATION, most recent first (Lean's
//! `findLocalDeclWithType?` with `isDefEq`): a `‹_›` deferred until the
//! enclosing application was elaborated and still facing `Nonempty ?α`
//! (`Function.surjective_comp_left_iff`, measured 2026-09-11 — that row also
//! needs the by-block bridge to hand the solution back to the elaborator,
//! which is separate work; the tactic-level half is pinned here). And `congr`
//! closes a reflexive goal before splitting it, comparing reduced heads
//! (`Unique.subtypeEq'`: `⟨y, ⋯⟩ = default` after `subst`).

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_assumption_unifies_an_open_goal_with_the_most_recent_matching_hypothesis() {
    use crate::tactic::{assumption, Goal, LocalDecl, ProofState};
    use crate::unify::MetaState;
    use clean_kernel::{Declaration, Expr, FVarId, Level, Name};
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("axiom A : Type");
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let nonempty = |t: Expr| {
        Expr::app(
            Expr::const_(
                Name::from_string("Nonempty"),
                vec![Level::succ(Level::zero())],
            ),
            t,
        )
    };
    // Context: `inst : Nonempty A`; goal: `Nonempty ?m` with `?m` open.
    let mut state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("inst"),
            ty: nonempty(a.clone()),
            value: None,
        }],
    );
    let m = state.metas.fresh(Expr::type_());
    let m_expr = Expr::fvar(MetaState::to_fvar(m));
    // Replace the placeholder goal by one whose target mentions `?m` (a goal
    // is minted against its target, so the target cannot be edited in place).
    let target = nonempty(m_expr.clone());
    let ctx = state.current_goal().expect("one goal").local_ctx.clone();
    let goal_meta = state.fresh_meta_in_context(target.clone(), &ctx);
    state.goals.clear();
    state.goals.push_front(Goal {
        meta_id: goal_meta,
        target,
        local_ctx: ctx,
        tag: None,
        case_binders: Vec::new(),
    });
    assumption(&mut state).expect("`assumption` must unify `Nonempty ?m` with the instance");
    assert_eq!(
        state.metas.instantiate(&m_expr),
        a,
        "the open metavariable must be solved from the matching hypothesis"
    );
    assert!(state.goals().is_empty(), "the goal must be closed");
}

#[test]
fn test_by_block_hands_back_the_solution_of_an_enclosing_metavariable() {
    let mut env = Environment::with_prelude();
    // `refine myElim ‹_› fun a => ?_` elaborates the application with `?α`
    // open; the deferred `‹_›` runs as a `by` block facing `Nonempty ?α`,
    // where `assumption` solves `?α := α` — and that solution must reach the
    // elaborator, or `fun a => ?_` keeps `a : ?α` and `exact k a` cannot fit.
    let src = "theorem myElim {α : Sort u} {p : Prop} (h : Nonempty α) (k : α → p) : p :=\n\
               \x20 @Nonempty.rec α (fun _ => p) k h\n\
               theorem viaRefine {α : Sort u} [Nonempty α] (q : Prop) (k : α → q) : q := by\n\
               \x20 refine myElim ‹_› fun a => ?_\n\
               \x20 exact k a\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the by-block bridge must hand `?α := α` back to the elaborator: {e}");
    }
}

#[test]
fn test_congr_closes_a_reflexive_goal_whose_heads_differ_syntactically() {
    let mut env = Environment::with_prelude();
    let src = "structure Box (α : Type) where\n\
               \x20 val : α\n\
               theorem boxDefault (n : Nat) (b : Box Nat) (h : b = ⟨n⟩) :\n\
               \x20   b = @Inhabited.default (Box Nat) ⟨⟨n⟩⟩ := by\n\
               \x20 subst h\n\
               \x20 congr\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr` must close `⟨n⟩ = default` by reflexivity: {e}");
    }
}
