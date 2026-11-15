// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Projection guards of Lean's kernel, ported to the ck0 re-checker
//! (decision R147, plan item `kernel-defensive-invariants-v4331`).
//!
//! Lean's `infer_proj` (`type_checker.cpp`) refuses a projection unless the
//! projected term's type is headed by the structure the projection names with
//! exactly that structure's parameters applied, and, when that type is a
//! proposition, unless the projected field and every earlier field it depends
//! on are proofs. `reduce_proj_core` (v4.33.1, leanprover/lean4#14632)
//! extracts a field only from a constructor of the named structure. Each test
//! pairs its subject with a control that the guard must keep accepting.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{infer, whnf, Budget, Env, InferError, MinimalEnv, Name, RawExpr, RawLevel, Term};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}
fn r_sort(level: u32) -> RawExpr {
    let mut l = RawLevel::Zero;
    for _ in 0..level {
        l = RawLevel::Succ(Box::new(l));
    }
    RawExpr::Sort(l)
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn r_proj(struct_name: &str, idx: u32, e: RawExpr) -> RawExpr {
    RawExpr::Proj(n(struct_name), idx, Box::new(e))
}
fn v(env: &dyn Env, raw: &RawExpr) -> Term {
    Term::validate_closed(env, raw).expect("term validates")
}

/// Declare `name : ty` (validated against the env built so far).
fn decl(env: MinimalEnv, name: &str, ty: &RawExpr) -> MinimalEnv {
    let ty = v(&env, ty);
    env.with_const_typed(n(name), 0, ty)
}

/// Declare a one-constructor, parameter-free structure `name : sort` whose
/// constructor `name.mk` has the type `ctor_ty` and `num_fields` fields.
fn structure(
    env: MinimalEnv,
    name: &str,
    sort: u32,
    ctor_ty: &RawExpr,
    num_fields: u32,
) -> MinimalEnv {
    let ctor = format!("{name}.mk");
    let env = decl(env, name, &r_sort(sort)).with_structure(n(name), n(&ctor), 0, num_fields);
    let ctor_ty = v(&env, ctor_ty);
    env.with_constructor(n(&ctor), 0, ctor_ty, 0, num_fields)
}

fn env() -> MinimalEnv {
    let env = decl(MinimalEnv::new(), "Bool", &r_sort(1));
    let env = decl(env, "Bool.true", &r_const("Bool"));
    let env = decl(env, "T", &r_sort(0));
    let env = decl(env, "G", &r_pi(r_const("Bool"), r_sort(0)));
    let env = decl(env, "H", &r_pi(r_const("T"), r_sort(0)));
    // structure PS : Prop where b : Bool              (a data field)
    let env = structure(env, "PS", 0, &r_pi(r_const("Bool"), r_const("PS")), 1);
    // structure PQ : Prop where t : T                 (a proof field)
    let env = structure(env, "PQ", 0, &r_pi(r_const("T"), r_const("PQ")), 1);
    // structure PD : Prop where b : Bool; g : G b     (proof field over data)
    let pd_mk = r_pi(
        r_const("Bool"),
        r_pi(r_app(r_const("G"), r_bvar(0)), r_const("PD")),
    );
    let env = structure(env, "PD", 0, &pd_mk, 2);
    // structure PE : Prop where t : T; h : H t        (proof field over proof)
    let pe_mk = r_pi(
        r_const("T"),
        r_pi(r_app(r_const("H"), r_bvar(0)), r_const("PE")),
    );
    let env = structure(env, "PE", 0, &pe_mk, 2);
    // structure SA : Type where b : Bool, and structure SB the same.
    let env = structure(env, "SA", 1, &r_pi(r_const("Bool"), r_const("SA")), 1);
    let env = structure(env, "SB", 1, &r_pi(r_const("Bool"), r_const("SB")), 1);
    let env = decl(env, "p", &r_const("PS"));
    let env = decl(env, "q", &r_const("PQ"));
    let env = decl(env, "d", &r_const("PD"));
    let env = decl(env, "e", &r_const("PE"));
    decl(env, "xb", &r_const("SB"))
}

fn infer_raw(env: &MinimalEnv, raw: &RawExpr) -> Result<Term, InferError> {
    infer(env, &v(env, raw), &mut Budget::default_budget())
}

/// #14807 class: a proof of a `Prop` structure must not yield data. Lean's
/// `infer_proj` refuses `p.0` for `p : PS` (`PS : Prop`, field `b : Bool`),
/// and refuses `d.1` for `d : PD` even though `g : G b` is a proof, because
/// its type would mention the data projection `d.0`. Before the port ck0 typed
/// both, so two proofs of `PS`, equal by proof irrelevance, could project to
/// different booleans.
#[test]
fn projection_of_a_data_field_out_of_a_proof_is_refused() {
    let env = env();
    // Controls: proof fields of a Prop structure, and a dependent proof field
    // whose dependency is itself a proof.
    assert_eq!(
        infer_raw(&env, &r_proj("PQ", 0, r_const("q"))).expect("control: q.0 : T"),
        v(&env, &r_const("T"))
    );
    assert_eq!(
        infer_raw(&env, &r_proj("PE", 1, r_const("e"))).expect("control: e.1 : H e.0"),
        v(&env, &r_app(r_const("H"), r_proj("PE", 0, r_const("e"))))
    );
    for (subject, raw) in [
        ("p.0 : Bool out of p : PS", r_proj("PS", 0, r_const("p"))),
        ("d.0 : Bool out of d : PD", r_proj("PD", 0, r_const("d"))),
        ("d.1 : G d.0 out of d : PD", r_proj("PD", 1, r_const("d"))),
    ] {
        let result = infer_raw(&env, &raw);
        assert!(
            matches!(result, Err(InferError::NotAStructure { .. })),
            "{subject} must be refused as an invalid projection, got {result:?}"
        );
    }
}

/// Lean's `infer_proj` refuses `I_name != proj_sname(e)`. Before the port ck0
/// typed `SA.0 xb` for `xb : SB` from `SB`'s field layout, ignoring the name.
#[test]
fn projection_naming_another_structure_is_refused() {
    let env = env();
    assert_eq!(
        infer_raw(&env, &r_proj("SB", 0, r_const("xb"))).expect("control: xb.0 : Bool"),
        v(&env, &r_const("Bool"))
    );
    let result = infer_raw(&env, &r_proj("SA", 0, r_const("xb")));
    assert!(
        matches!(result, Err(InferError::NotAStructure { .. })),
        "SA.0 of an SB must be refused, got {result:?}"
    );
}

/// leanprover/lean4#14632: `reduce_proj_core` extracts a field only from a
/// constructor of the projection's own structure.
#[test]
fn projection_of_a_foreign_constructor_stays_stuck() {
    let env = env();
    let tt = r_const("Bool.true");
    let own = v(&env, &r_proj("SB", 0, r_app(r_const("SB.mk"), tt.clone())));
    assert_eq!(
        whnf(&env, &own, &mut Budget::default_budget()).expect("budget"),
        v(&env, &tt),
        "control: SB.0 (SB.mk true) reduces"
    );
    let foreign = v(&env, &r_proj("SA", 0, r_app(r_const("SB.mk"), tt)));
    assert_eq!(
        whnf(&env, &foreign, &mut Budget::default_budget()).expect("budget"),
        foreign,
        "SA.0 (SB.mk true) must stay stuck"
    );
}
