// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The universe check's level comparison and a nested inductive's rewrite
//! are held to bounds on their work (`docs/DECISIONS.md` R172).
//!
//! * The universe check compares an inductive's sort with each field's
//!   (`Level::is_geq`: Lean's rules in Lean's order, R174). Against an `imax` spine the
//!   rules try both ways of splitting a `max`, and Lean's comparison
//!   remembers nothing, so its steps grow exponentially, whatever the answer:
//!   unremembered, a `max` of 20 parameters against a spine of 10 took 17 s
//!   in a debug build. ck0 remembers each answer, which makes the steps
//!   polynomial, and charges its work: past `MAX_LEVEL_GEQ_WORK` the
//!   inductive is refused.
//! * A nested inductive's auxiliary copies an occurrence's argument at every
//!   use of the container's parameter, and admission walks every copy. Each
//!   type the rewrite builds is charged an upper bound on its size before it
//!   is built, and past `MAX_AUX_SIZE` the block is refused.
//! * A block too wide for the depth bound is refused before its auxiliaries
//!   are built, and so is one of more than 1,024 distinct occurrences.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, add_inductive_nested, AdmitError, Constructor, InductiveDecl, MinimalEnv, Name,
    NestedError, RawExpr, RawLevel, Term, MAX_AUX_SIZE,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn r_const(s: &str) -> RawExpr {
    RawExpr::Const(n(s), vec![])
}

fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}

fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}

fn r_type() -> RawExpr {
    RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)))
}

/// `max` of the given parameters, right-nested.
fn raw_max(params: &[u32]) -> RawLevel {
    let mut iter = params.iter().rev();
    let mut l = iter.next().map_or(RawLevel::Zero, |&p| RawLevel::Param(p));
    for &p in iter {
        l = RawLevel::Max(Box::new(RawLevel::Param(p)), Box::new(l));
    }
    l
}

/// Run `f` on a thread with an 8 MiB stack, the size of the main thread's on
/// this platform, so the measurement does not depend on the caller's thread.
fn on_main_sized_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(f)
        .expect("thread spawns")
        .join()
        .expect("the decision returns rather than unwinding")
}

/// Where `s`, the universe of the field's codomain, sits in the inductive's
/// sort: absent, or first or last in canonical order (by parameter index).
#[derive(Clone, Copy)]
enum Codomain {
    Absent,
    First,
    Last,
}

/// `T (α_1 : Sort t_1) … (α_j : Sort t_j) (β : Sort s) : Sort top` with
/// `T.mk : (α_1 → … → α_j → β) → T α_1 … α_j β`. The field's sort is
/// `imax t_1 (… (imax t_j s))`, and `top` is the `max` of `extra` other
/// parameters, then the `t`s, with `s` where `at` says.
fn spine(extra: u32, j: u32, at: Codomain) -> InductiveDecl {
    let (s, first) = match at {
        Codomain::First => (0, 1),
        Codomain::Absent | Codomain::Last => (extra + j, 0),
    };
    let ts: Vec<u32> = (first + extra..first + extra + j).collect();
    let mut top: Vec<u32> = (first..first + extra).chain(ts.iter().copied()).collect();
    match at {
        Codomain::Absent => {}
        Codomain::First => top.insert(0, s),
        Codomain::Last => top.push(s),
    }
    let nlp = extra + j + 1;
    let over_params = |body: RawExpr| {
        let mut t = r_pi(RawExpr::Sort(RawLevel::Param(s)), body);
        for &tk in ts.iter().rev() {
            t = r_pi(RawExpr::Sort(RawLevel::Param(tk)), t);
        }
        t
    };
    // Under the params, `α_k` is BVar(j - k + 1) and `β` BVar(0); under `d`
    // of the field's binders, the next domain and the codomain are BVar(j).
    let mut field = RawExpr::BVar(j);
    for _ in 0..j {
        field = r_pi(RawExpr::BVar(j), field);
    }
    let mut ret = RawExpr::Const(n("T"), (0..nlp).map(RawLevel::Param).collect());
    for i in (1..=j + 1).rev() {
        ret = r_app(ret, RawExpr::BVar(i));
    }
    let env = MinimalEnv::new().with_const(n("T"), nlp);
    let valid = |raw: &RawExpr| Term::validate(&env, raw, 0, nlp).expect("the decl validates");
    InductiveDecl {
        name: n("T"),
        num_level_params: nlp,
        num_params: j + 1,
        type_: valid(&over_params(RawExpr::Sort(raw_max(&top)))),
        constructors: vec![Constructor {
            name: n("T.mk"),
            type_: valid(&over_params(r_pi(field, ret))),
        }],
    }
}

fn admit(decl: InductiveDecl) -> Result<(), AdmitError> {
    on_main_sized_stack(move || add_inductive(&mut MinimalEnv::new(), decl))
}

#[test]
fn test_universe_check_control_small_spines_keep_their_verdicts() {
    assert!(
        matches!(
            admit(spine(4, 4, Codomain::Absent)),
            Err(AdmitError::UniverseTooLarge { .. })
        ),
        "`s` is not below the sort"
    );
    admit(spine(4, 4, Codomain::First)).expect("every part of the spine is below the sort");
    admit(spine(4, 4, Codomain::Last)).expect("every part of the spine is below the sort");
}

/// With `s` last, the first tail of the `max` that holds no extra parameter
/// is at least the spine, and the comparison finds it in polynomial time.
#[test]
fn test_universe_check_control_wide_spine_found_early_admits() {
    admit(spine(20, 20, Codomain::Last)).expect("found without the exponential search");
}

/// Comparisons Lean decides only after trying every way of splitting the
/// `max` (unremembered, 20 against 10 took 17 s, and each step up about six
/// times as long): remembered, each pair of subterms is compared once.
#[test]
fn test_universe_check_comparison_exponential_in_lean_is_decided() {
    assert!(
        matches!(
            admit(spine(20, 20, Codomain::Absent)),
            Err(AdmitError::UniverseTooLarge { .. })
        ),
        "`s` is not below the sort"
    );
    admit(spine(20, 20, Codomain::First)).expect("found after the search");
}

/// 120 parameters against a spine of 60: past the work bound even
/// remembered. A false comparison is refused as Lean refuses it, after far
/// fewer steps.
#[test]
fn test_universe_check_comparison_past_the_work_bound_is_refused() {
    assert!(matches!(
        admit(spine(60, 60, Codomain::Absent)),
        Err(AdmitError::OutOfBudget { .. })
    ));
}

/// A true comparison past the work bound: Lean's comparison answers it after
/// exponentially many steps; ck0 refuses it, which is fail-closed.
#[test]
fn test_universe_check_true_comparison_past_the_work_bound_is_refused_where_lean_admits_it() {
    assert!(matches!(
        admit(spine(60, 60, Codomain::First)),
        Err(AdmitError::OutOfBudget { .. })
    ));
}

/// `S.{u,v} (α : Sort u) (β : Sort v) : Sort (top + 1)` with
/// `S.mk : (α → β) → S α β`, whose field is at `imax u v`.
fn arrow_field(top: RawLevel) -> InductiveDecl {
    let sort = |l: u32| RawExpr::Sort(RawLevel::Param(l));
    let over_params = |body: RawExpr| r_pi(sort(0), r_pi(sort(1), body));
    let s_of = |a: u32, b: u32| {
        let head = RawExpr::Const(n("S"), vec![RawLevel::Param(0), RawLevel::Param(1)]);
        r_app(r_app(head, RawExpr::BVar(a)), RawExpr::BVar(b))
    };
    // Under the params `α` is BVar(1) and `β` BVar(0); under the field, 2 and 1.
    let field = r_pi(RawExpr::BVar(1), RawExpr::BVar(1));
    let env = MinimalEnv::new().with_const(n("S"), 2);
    let valid = |raw: &RawExpr| Term::validate(&env, raw, 0, 2).expect("the decl validates");
    InductiveDecl {
        name: n("S"),
        num_level_params: 2,
        num_params: 2,
        type_: valid(&over_params(RawExpr::Sort(RawLevel::Succ(Box::new(top))))),
        constructors: vec![Constructor {
            name: n("S.mk"),
            type_: valid(&over_params(r_pi(field, s_of(2, 1)))),
        }],
    }
}

/// Lean refuses this inductive, in its elaborator ("Invalid universe level in
/// constructor `S.mk`") and in its kernel when it is handed over directly
/// ("(kernel) universe level of type_of(arg #3) of 'Sa.mk' is too big for
/// the corresponding inductive datatype"; Lean 4.30.0-rc2, measured
/// 2026-10-28, recorded in `fixtures/level_gap/`). Its `is_geq_core` takes the offsets of `succ (imax u v)` and
/// `imax u v`, whose bases differ. ck0 admitted it until R174 by a rule Lean
/// does not have.
#[test]
fn test_universe_check_offset_of_irreducible_imax_is_refused_as_lean_refuses_it() {
    let imax_uv = RawLevel::IMax(Box::new(RawLevel::Param(0)), Box::new(RawLevel::Param(1)));
    assert!(matches!(
        admit(arrow_field(imax_uv)),
        Err(AdmitError::UniverseTooLarge { .. })
    ));
}

/// The same inductive at `Sort (max u v + 1)`, which Lean admits.
#[test]
fn test_universe_check_control_offset_of_max_admits_as_lean_admits_it() {
    let max_uv = RawLevel::Max(Box::new(RawLevel::Param(0)), Box::new(RawLevel::Param(1)));
    admit(arrow_field(max_uv)).expect("`max u v + 1` is at least `u` and `v`");
}

/// `name (α : Type) : Type` with `count` constructors, each
/// `(α : Type) → α → … → α → name α` with `uses` fields of type `α`.
fn container(name: &str, count: usize, uses: u32) -> InductiveDecl {
    let env = MinimalEnv::new().with_const(n(name), 0);
    let mut ctor = r_app(r_const(name), RawExpr::BVar(uses));
    for k in (0..uses).rev() {
        ctor = r_pi(RawExpr::BVar(k), ctor);
    }
    let ctor = Term::validate_closed(&env, &r_pi(r_type(), ctor)).expect("the ctor validates");
    InductiveDecl {
        name: n(name),
        num_level_params: 0,
        num_params: 1,
        type_: Term::validate_closed(&env, &r_pi(r_type(), r_type())).expect("the type validates"),
        constructors: (0..count)
            .map(|i| Constructor {
                name: n(&format!("{name}.c{i}")),
                type_: ctor.clone(),
            })
            .collect(),
    }
}

/// `T : Type` with a constructor `T.c<i> : D_1 → … → T` per entry of
/// `ctors`, validated against `known`.
fn parent(known: &[String], ctors: Vec<Vec<RawExpr>>) -> InductiveDecl {
    let env = known
        .iter()
        .fold(MinimalEnv::new().with_const(n("T"), 0), |e, k| {
            e.with_const(n(k), 0)
        });
    let constructors = ctors
        .into_iter()
        .enumerate()
        .map(|(i, fields)| {
            let raw = fields
                .into_iter()
                .rev()
                .fold(r_const("T"), |t, d| r_pi(d, t));
            Constructor {
                name: n(&format!("T.c{i}")),
                type_: Term::validate_closed(&env, &raw).expect("the ctor validates"),
            }
        })
        .collect();
    InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 0,
        type_: Term::validate_closed(&env, &r_type()).expect("Type"),
        constructors,
    }
}

/// The detail of a nested refusal made while building the block, or the
/// outcome when there is none.
fn nested_detail(
    env: MinimalEnv,
    containers: Vec<InductiveDecl>,
    t: InductiveDecl,
) -> Result<String, String> {
    on_main_sized_stack(move || {
        let mut env = env;
        for c in containers {
            add_inductive(&mut env, c).expect("the container admits");
        }
        match add_inductive_nested(&mut env, t) {
            Err(NestedError::Aux {
                source: AdmitError::Derivation { detail, .. },
                ..
            }) => Ok(detail),
            other => Err(format!("{other:?}")),
        }
    })
}

/// `T` with a constructor `T.c<k> : P (A_k → T) → T` for each `k < count`:
/// `count` distinct occurrences of `P`.
fn occurrences(count: usize) -> Result<String, String> {
    let names: Vec<String> = (0..count).map(|k| format!("A{k}")).collect();
    let type_ty = Term::validate_closed(&MinimalEnv::new(), &r_type()).expect("Type");
    let env = names.iter().fold(MinimalEnv::new(), |e, k| {
        e.with_const_typed(n(k), 0, type_ty.clone())
    });
    let mut known = names.clone();
    known.push("P".to_string());
    let ctors = names
        .iter()
        .map(|a| vec![r_app(r_const("P"), r_pi(r_const(a), r_const("T")))])
        .collect();
    nested_detail(env, vec![container("P", 1, 1)], parent(&known, ctors))
}

#[test]
fn test_nested_occurrences_control_three_distinct_admit() {
    assert_eq!(occurrences(3), Err("Ok(())".to_string()));
}

/// Each distinct occurrence adds a motive, so 1,025 cannot fit: collection
/// stops at the 1,025th, before the auxiliaries are built.
#[test]
fn test_nested_occurrences_past_the_bound_are_refused_while_collected() {
    let detail = occurrences(1025).expect("refused as a derivation error");
    assert!(
        detail.contains("more than 1024 distinct nested occurrences"),
        "refused while collecting: {detail}"
    );
}

/// `T.c0 : C1 T → C2 T → T`, each container of `count` constructors: the
/// block's rules bind 3 motives and `2·count + 1` minors.
fn two_containers(count: usize) -> Result<String, String> {
    let known = ["C1".to_string(), "C2".to_string()];
    let ctors = vec![vec![
        r_app(r_const("C1"), r_const("T")),
        r_app(r_const("C2"), r_const("T")),
    ]];
    nested_detail(
        MinimalEnv::new(),
        vec![container("C1", count, 1), container("C2", count, 1)],
        parent(&known, ctors),
    )
}

#[test]
fn test_nested_block_width_control_two_containers_of_100_admit() {
    assert_eq!(two_containers(100), Err("Ok(())".to_string()));
}

#[test]
fn test_nested_block_too_wide_is_refused_before_its_auxiliaries_are_built() {
    let detail = two_containers(600).expect("refused as a derivation error");
    assert!(
        detail.contains(
            "before its auxiliaries are built, a constructor's ι rule binds 1204 variables"
        ),
        "refused from the counts: {detail}"
    );
}

/// A `Type` of `2^height` leaves `Prop`, joined by `G : Type → Type → Type`:
/// about `2^(height + 2)` nodes, and `2·height + 1` deep.
fn g_tree(height: u32) -> RawExpr {
    if height == 0 {
        RawExpr::Sort(RawLevel::Zero)
    } else {
        r_app(r_app(r_const("G"), g_tree(height - 1)), g_tree(height - 1))
    }
}

/// `W (α : Type) : Type` with `W.c0 : (α : Type) → α → … → W α` (`uses`
/// fields), and `T.c0 : W (D → T) → T`, `D` a `g_tree` of height 14: the
/// auxiliary's constructor holds `uses` copies of `D → T`, about 65,000
/// nodes each.
fn copies(uses: u32) -> Result<String, String> {
    let g_ty = Term::validate_closed(
        &MinimalEnv::new(),
        &r_pi(r_type(), r_pi(r_type(), r_type())),
    )
    .expect("G's type");
    let env = MinimalEnv::new().with_const_typed(n("G"), 0, g_ty);
    let known = ["G".to_string(), "W".to_string()];
    let ctors = vec![vec![r_app(r_const("W"), r_pi(g_tree(14), r_const("T")))]];
    nested_detail(env, vec![container("W", 1, uses)], parent(&known, ctors))
}

#[test]
fn test_nested_auxiliary_size_control_one_copy_admits() {
    assert_eq!(copies(1), Err("Ok(())".to_string()));
}

/// 300 copies of a 65,000-node argument: about 2·10^7 nodes as a tree, which
/// the rewrite rebuilds and admission walks one by one. Lean, whose terms
/// share their subterms, admits it.
#[test]
fn test_nested_auxiliary_past_the_size_bound_is_refused_where_lean_admits_it() {
    let detail = copies(300).expect("refused as a derivation error");
    assert!(
        detail.contains(&format!(
            "could build more than {MAX_AUX_SIZE} term nodes, past the budget at the auxiliary constructor copied from `W.c0`"
        )),
        "refused before the auxiliary is built: {detail}"
    );
}
