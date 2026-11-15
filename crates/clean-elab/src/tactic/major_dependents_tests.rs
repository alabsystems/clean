// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The goals `cases` leaves on a nested inductive with a dependent
//! hypothesis, compared with pinned Lean 4.8.0's (class (80), brick B5):
//!
//! ```text
//! theorem n2 (q : Nat) (p : P) (h : p.isLeaf = true) (k : q = q) : False := by
//!   cases p
//!   trace_state
//! ```
//!
//! prints, for `case leaf`, `q : Nat`, `k : q = q`, `a✝ : Nat`,
//! `h : (P.leaf a✝).isLeaf = true`, and for `case conj` the same with
//! `a✝ : List P`: the hypothesis that mentions `p` is re-introduced after the
//! constructor's field, under its own name, about the constructor; `k` keeps
//! its place.

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, FVarId, Level};
use clean_parser::SurfaceName;

use super::core::{LocalDecl, ProofState};

const SRC: &str = "inductive P where
  | leaf : Nat → P
  | conj : List P → P

def P.isLeaf : P → Bool
  | .leaf _ => true
  | .conj _ => false
";

fn env_with_p() -> Environment {
    let mut env = Environment::with_prelude();
    let patterns = super::builtins::builtin_tactic_patterns();
    let decls = clean_parser::parse_file_with_tactics(SRC, &patterns).expect("parses");
    for decl in &decls {
        crate::elaborate_decl_and_register(&mut env, decl).expect("registers");
    }
    env
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn eq1(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(Expr::app(Expr::app(eq, ty), lhs), rhs)
}

fn local(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(id),
        name: SurfaceName::component(name, false),
        ty,
        value: None,
    }
}

fn names(state: &ProofState, goal: usize) -> Vec<String> {
    state.goals[goal]
        .local_ctx
        .iter()
        .map(|d| d.name.to_string())
        .collect()
}

#[test]
fn test_cases_nested_major_reintroduces_dependent_after_fields_like_lean() {
    let env = env_with_p();
    let q = Expr::fvar(FVarId::new(0));
    let p = Expr::fvar(FVarId::new(1));
    let is_leaf_p = Expr::app(c("P.isLeaf"), p);
    let ctx = vec![
        local(0, "q", c("Nat")),
        local(1, "p", c("P")),
        local(2, "h", eq1(c("Bool"), is_leaf_p, c("Bool.true"))),
        local(3, "k", eq1(c("Nat"), q.clone(), q)),
    ];
    let mut state = ProofState::with_elab_context(env, c("False"), ctx);
    super::proof_manipulation::cases(&mut state, &SurfaceName::component("p", false))
        .expect("cases on the nested `P`");
    assert_eq!(state.goals.len(), 2, "one goal per constructor of `P`");
    for (goal, ctor, field_ty) in [
        (0, "leaf", c("Nat")),
        (
            1,
            "conj",
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                c("P"),
            ),
        ),
    ] {
        let g = &state.goals[goal];
        assert_eq!(
            g.tag.as_ref().map(ToString::to_string).as_deref(),
            Some(ctor)
        );
        let ctx_names = names(&state, goal);
        assert_eq!(
            ctx_names.len(),
            4,
            "{ctor}: q, k, the field, h: {ctx_names:?}"
        );
        assert_eq!(&ctx_names[0], "q");
        assert_eq!(&ctx_names[1], "k");
        assert_eq!(&ctx_names[3], "h", "{ctor}: `h` comes back last, by name");
        let field = &g.local_ctx[2];
        assert!(
            g.case_binders.contains(&field.fvar),
            "{ctor}: the field is the case's binder"
        );
        let field_ty_seen = state.metas.instantiate(&field.ty);
        assert!(
            state.is_def_eq(g, &field_ty_seen, &field_ty),
            "{ctor}: field type {field_ty_seen}"
        );
        let ctor_app = Expr::app(c(&format!("P.{ctor}")), Expr::fvar(field.fvar));
        let want = eq1(
            c("Bool"),
            Expr::app(c("P.isLeaf"), ctor_app),
            c("Bool.true"),
        );
        let h_ty = state.metas.instantiate(&g.local_ctx[3].ty);
        assert_eq!(h_ty, want, "{ctor}: `h` is about the constructor");
        assert!(
            !super::hypothesis::collect_fvars(&h_ty).contains(&FVarId::new(1)),
            "{ctor}: no hypothesis names the eliminated `p`"
        );
    }
}
