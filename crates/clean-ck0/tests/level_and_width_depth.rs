// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe levels and derived recursors are held to the depth bound
//! (`docs/DECISIONS.md` R166).
//!
//! A universe level counts toward the depth of the term it sits in: `validate`
//! and the level operations recurse over it natively, so a `Sort` whose level
//! is a `Succ` spine a million deep must be refused at the input, not abort the
//! process. δ-unfolding a universe-polymorphic constant instantiates its body's
//! levels, so a chain of definitions can grow a level a thousand nodes per step;
//! `whnf_core`'s reduct bound refuses that too.
//!
//! A level's canonical form can be far deeper than its raw tree: `max`
//! flattens into a chain of its distinct arguments, so a balanced raw `max` 21
//! deep over 2^20 parameters is a chain 2^20 long, and instantiating a
//! constant's level parameters with such chains multiplies their lengths.
//! Every level operation the checker runs is bounded node by node, so each is
//! refused, at the input and at instantiation, before anything walks it.
//!
//! A recursor's type has one binder per minor premise, so an inductive with
//! thousands of constructors derives a telescope far deeper than any input may
//! be, which `kernel_check_recursor` walks natively. It is refused before
//! derivation builds anything. Lean admits such an inductive: the refusal is
//! fail-closed, and pinned here.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, infer, AdmitError, Budget, BudgetError, Constructor, InductiveDecl, InferError,
    MinimalEnv, Name, RawExpr, RawLevel, Term, Transparency, ValidateError, MAX_VALIDATE_DEPTH,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

/// `base + count`, built in a loop.
fn succs(count: u32, base: RawLevel) -> RawLevel {
    let mut l = base;
    for _ in 0..count {
        l = RawLevel::Succ(Box::new(l));
    }
    l
}

/// Drop a level of any depth without native recursion: `RawLevel`'s own `Drop`
/// recurses, and the caller owns the untrusted value.
fn dismantle(level: RawLevel) {
    let mut stack = vec![level];
    while let Some(l) = stack.pop() {
        match l {
            RawLevel::Succ(inner) => stack.push(*inner),
            RawLevel::Max(a, b) | RawLevel::IMax(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            RawLevel::Zero | RawLevel::Param(_) => {}
        }
    }
}

/// `count` binders `Π (_ : Prop), …` over `body`.
fn pis(count: u32, body: RawExpr) -> RawExpr {
    let mut t = body;
    for _ in 0..count {
        t = RawExpr::Pi(
            BinderInfo::Default,
            Box::new(RawExpr::Sort(RawLevel::Zero)),
            Box::new(t),
        );
    }
    t
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

fn is_too_deep<T>(verdict: &Result<T, ValidateError>) -> bool {
    matches!(verdict, Err(ValidateError::MaxDepthExceeded { max }) if *max == MAX_VALIDATE_DEPTH)
}

#[test]
fn test_validate_universe_level_a_million_deep_is_refused_not_an_abort() {
    let refused = on_main_sized_stack(|| {
        let env = MinimalEnv::new();
        let raw = RawExpr::Sort(succs(1_000_000, RawLevel::Zero));
        let refused = is_too_deep(&Term::validate_closed(&env, &raw));
        if let RawExpr::Sort(level) = raw {
            dismantle(level);
        }
        refused
    });
    assert!(refused, "a level a million deep is MaxDepthExceeded");
}

/// A level counts toward the depth of the term it sits in, from where it sits:
/// one more per `Succ`, `Max` and `IMax` node.
#[test]
fn test_validate_universe_level_counts_toward_the_depth_bound() {
    let env = MinimalEnv::new();
    let at_bound = RawExpr::Sort(succs(MAX_VALIDATE_DEPTH - 1, RawLevel::Zero));
    Term::validate_closed(&env, &at_bound).expect("a Sort of height 1,024 is at the bound");
    let past = RawExpr::Sort(succs(MAX_VALIDATE_DEPTH, RawLevel::Zero));
    assert!(
        is_too_deep(&Term::validate_closed(&env, &past)),
        "a Sort of height 1,025 is past it"
    );
    let shallow = pis(400, RawExpr::Sort(succs(400, RawLevel::Zero)));
    Term::validate_closed(&env, &shallow).expect("400 binders over a level 400 deep fit");
    let deep = pis(400, RawExpr::Sort(succs(700, RawLevel::Zero)));
    assert!(
        is_too_deep(&Term::validate_closed(&env, &deep)),
        "400 binders over a level 700 deep do not"
    );
}

/// `c0.{u}` opaque, and `c(k+1).{u} := ck.{u + 1000}`: δ-unfolding `c(k+1)`
/// instantiates `u`, so each step adds 1,000 to the level.
fn level_tower_env(steps: u32) -> MinimalEnv {
    let mut env = MinimalEnv::new().with_const(n("c0"), 1);
    for k in 0..steps {
        let body = RawExpr::Const(n(&format!("c{k}")), vec![succs(1000, RawLevel::Param(0))]);
        let body = Term::validate(&env, &body, 0, 1).expect("the body is 1,001 high");
        let ty = Term::validate(&env, &RawExpr::Sort(RawLevel::Param(0)), 0, 1).expect("type");
        env = env.with_def(
            n(&format!("c{}", k + 1)),
            1,
            ty,
            body,
            Transparency::Transparent,
        );
    }
    env
}

#[test]
fn test_whnf_level_tower_control_one_step_unfolds() {
    let env = level_tower_env(1);
    let top = Term::validate_closed(&env, &RawExpr::Const(n("c1"), vec![RawLevel::Zero]))
        .expect("c1.{0}");
    let expected = Term::validate_closed(
        &env,
        &RawExpr::Const(n("c0"), vec![succs(1000, RawLevel::Zero)]),
    )
    .expect("c0.{1000}");
    let mut budget = Budget::default_budget();
    assert_eq!(clean_ck0::whnf(&env, &top, &mut budget), Ok(expected));
}

#[test]
fn test_whnf_level_grown_by_delta_is_refused_not_an_abort() {
    let fuel = Budget::default_budget().remaining();
    let (verdict, left) = on_main_sized_stack(|| {
        let env = level_tower_env(1000);
        let top = Term::validate_closed(&env, &RawExpr::Const(n("c1000"), vec![RawLevel::Zero]))
            .expect("c1000.{0}");
        let mut budget = Budget::default_budget();
        let verdict = clean_ck0::whnf(&env, &top, &mut budget).map(|_| ());
        (verdict, budget.remaining())
    });
    assert_eq!(verdict, Err(BudgetError::OutOfBudget));
    assert!(
        left > fuel / 2,
        "refused by the depth bound with fuel left, not by exhaustion ({left} of {fuel} left)"
    );
}

/// `E : Type` with `width` nullary constructors.
fn enum_decl(width: usize) -> InductiveDecl {
    let b = MinimalEnv::new().with_const(n("E"), 0);
    let e = Term::validate_closed(&b, &RawExpr::Const(n("E"), vec![])).expect("E");
    let ty = Term::validate_closed(&b, &RawExpr::Sort(succs(1, RawLevel::Zero))).expect("Type");
    InductiveDecl {
        name: n("E"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: (0..width)
            .map(|i| Constructor {
                name: n(&format!("E.c{i}")),
                type_: e.clone(),
            })
            .collect(),
    }
}

#[test]
fn test_wide_enum_control_1000_constructors_admits() {
    let outcome = on_main_sized_stack(|| {
        let mut env = MinimalEnv::new();
        add_inductive(&mut env, enum_decl(1_000))
            .map(|_| ())
            .map_err(|e| e.to_string())
    });
    assert_eq!(
        outcome,
        Ok(()),
        "a recursor of 1,002 binders fits the bound"
    );
}

/// Lean admits this enum; ck0 refuses it, fail-closed. When the gap closes this
/// test fails, and becomes a control that admits it.
#[test]
fn test_wide_enum_past_the_depth_bound_is_refused_where_lean_admits_it() {
    let detail = on_main_sized_stack(|| {
        let mut env = MinimalEnv::new();
        match add_inductive(&mut env, enum_decl(3_000)) {
            Err(AdmitError::Derivation { detail, .. }) => Some(detail),
            _ => None,
        }
    })
    .expect("refused as a derivation error");
    assert!(
        detail.contains("telescope has 3002 binders"),
        "refused before the recursor is built: {detail}"
    );
}

/// `max Param(lo) … Param(hi - 1)` as a balanced raw tree: about log2 of the
/// count deep raw, and canonically a chain one shorter than the count.
fn balanced_max(lo: u32, hi: u32) -> RawLevel {
    if hi - lo == 1 {
        return RawLevel::Param(lo);
    }
    let mid = lo + (hi - lo) / 2;
    RawLevel::Max(
        Box::new(balanced_max(lo, mid)),
        Box::new(balanced_max(mid, hi)),
    )
}

#[test]
fn test_validate_level_control_a_canonical_chain_of_1000_params_admits() {
    let env = MinimalEnv::new();
    let raw = RawExpr::Sort(balanced_max(0, 1000));
    Term::validate(&env, &raw, 0, 1000).expect("a canonical chain 999 deep fits");
}

/// 2,048 parameters: the raw tree is 12 deep, its canonical chain 2,047.
#[test]
fn test_validate_level_whose_canonical_form_passes_the_bound_is_refused() {
    let env = MinimalEnv::new();
    let raw = RawExpr::Sort(balanced_max(0, 2048));
    assert!(is_too_deep(&Term::validate(&env, &raw, 0, 2048)));
}

#[test]
fn test_validate_level_canonical_chain_a_million_long_is_refused_not_an_abort() {
    let refused = on_main_sized_stack(|| {
        let env = MinimalEnv::new();
        let raw = RawExpr::Sort(balanced_max(0, 1 << 20));
        is_too_deep(&Term::validate(&env, &raw, 0, 1 << 20))
    });
    assert!(
        refused,
        "a level whose canonical form is a million deep is refused"
    );
}

/// `Π (_ : Prop)^binders, Sort (max u_0 … u_999)`: the raw term is about
/// `binders + 11` deep and its level fits, but the canonical level is a chain
/// 999 deep, so the term as built is about `binders + 1,000` deep. Only the
/// built term's depth check refuses it.
#[test]
fn test_validate_term_whose_built_depth_passes_the_bound_is_refused() {
    let (fits, refused) = on_main_sized_stack(|| {
        let env = MinimalEnv::new();
        let built = |binders| {
            Term::validate(
                &env,
                &pis(binders, RawExpr::Sort(balanced_max(0, 1000))),
                0,
                1000,
            )
        };
        (
            built(20).map(drop).map_err(|e| format!("{e:?}")),
            is_too_deep(&built(1000)),
        )
    });
    fits.expect("1,020 deep as built fits");
    assert!(
        refused,
        "about 2,000 deep as built, from a raw term about 1,011 deep"
    );
}

/// `k.{u} : Π (_ : Prop)^600, Sort u`, opaque, instantiated at the `max` of
/// `width` parameters: every level fits, but the instantiated type is about
/// `600 + width` deep. Only `instantiate_levels`' result check refuses it.
fn instantiate_into_binders(width: u32) -> Result<Term, InferError> {
    let ty = Term::validate(
        &MinimalEnv::new(),
        &pis(600, RawExpr::Sort(RawLevel::Param(0))),
        0,
        1,
    )
    .expect("k's type is 602 deep");
    let env = MinimalEnv::new().with_const_typed(n("k"), 1, ty);
    let t = Term::validate(
        &env,
        &RawExpr::Const(n("k"), vec![balanced_max(0, width)]),
        0,
        width,
    )
    .expect("the level is a chain width - 1 deep");
    infer(&env, &t, &mut Budget::default_budget())
}

#[test]
fn test_infer_instantiated_type_whose_depth_passes_the_bound_is_refused() {
    let (fits, refused) = on_main_sized_stack(|| {
        (
            instantiate_into_binders(400)
                .map(drop)
                .map_err(|e| format!("{e:?}")),
            matches!(instantiate_into_binders(500), Err(InferError::OutOfBudget)),
        )
    });
    fits.expect("about 1,000 deep fits");
    assert!(refused, "about 1,100 deep, every level within the bound");
}

/// `c.{u_0 … u_(k-1)} : Sort (max u_0 … u_(k-1))`, opaque.
fn wide_const_env(k: u32) -> MinimalEnv {
    let ty = Term::validate(&MinimalEnv::new(), &RawExpr::Sort(balanced_max(0, k)), 0, k)
        .expect("c's type, a chain k - 1 deep");
    MinimalEnv::new().with_const_typed(n("c"), k, ty)
}

/// `c.{L_0 … L_(k-1)}`, each `L_i` the `max` of `m` parameters of its own.
/// Instantiating `c`'s type with them gives a chain `k·m` long.
fn wide_instance(env: &MinimalEnv, k: u32, m: u32) -> Term {
    let levels = (0..k).map(|i| balanced_max(i * m, (i + 1) * m)).collect();
    Term::validate(env, &RawExpr::Const(n("c"), levels), 0, k * m)
        .expect("each level is a chain m - 1 deep")
}

#[test]
fn test_infer_level_instantiation_control_within_the_bound() {
    let env = wide_const_env(20);
    let t = wide_instance(&env, 20, 20);
    let mut budget = Budget::default_budget();
    let ty = infer(&env, &t, &mut budget).expect("a chain of 400 fits");
    let expected = Term::validate(&env, &RawExpr::Sort(balanced_max(0, 400)), 0, 400)
        .expect("Sort (max of 400)");
    assert_eq!(ty, expected);
}

#[test]
fn test_infer_level_instantiation_past_the_bound_is_refused() {
    let env = wide_const_env(40);
    let t = wide_instance(&env, 40, 40);
    let mut budget = Budget::default_budget();
    assert!(
        matches!(infer(&env, &t, &mut budget), Err(InferError::OutOfBudget)),
        "c's type instantiated at 40 chains of 40 is a chain 1,600 long"
    );
}

#[test]
fn test_infer_level_instantiation_a_million_long_is_refused_not_an_abort() {
    let refused = on_main_sized_stack(|| {
        let env = wide_const_env(1000);
        let t = wide_instance(&env, 1000, 1000);
        let mut budget = Budget::default_budget();
        matches!(infer(&env, &t, &mut budget), Err(InferError::OutOfBudget))
    });
    assert!(refused, "a chain a million long is refused as it is built");
}

/// `d.{u_0 … u_39} := Sort (max u_0 … u_39)`, unfolded at 40 chains of 40.
#[test]
fn test_whnf_level_instantiation_past_the_bound_is_refused() {
    let (k, m) = (40, 40);
    let base = MinimalEnv::new();
    let body = Term::validate(&base, &RawExpr::Sort(balanced_max(0, k)), 0, k).expect("body");
    let ty = Term::validate(
        &base,
        &RawExpr::Sort(RawLevel::Succ(Box::new(balanced_max(0, k)))),
        0,
        k,
    )
    .expect("type");
    let env = MinimalEnv::new().with_def(n("d"), k, ty, body, Transparency::Transparent);
    let levels = (0..k).map(|i| balanced_max(i * m, (i + 1) * m)).collect();
    let t = Term::validate(&env, &RawExpr::Const(n("d"), levels), 0, k * m).expect("d.{…}");
    let fuel = Budget::default_budget().remaining();
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &t, &mut budget).map(|_| ()),
        Err(BudgetError::OutOfBudget)
    );
    assert!(
        budget.remaining() > fuel / 2,
        "refused by the depth bound, not by exhaustion"
    );
}

/// `imax u (imax u p)` with `u` replaced by `l`: the step of the chain below.
fn imax_twice(l: RawLevel) -> RawLevel {
    RawLevel::IMax(
        Box::new(l.clone()),
        Box::new(RawLevel::IMax(Box::new(l), Box::new(RawLevel::Param(1)))),
    )
}

/// `c0.{u, p}` opaque, and `c(k+1).{u, p} := ck.{imax u (imax u p), p}`: each
/// unfolding substitutes the level twice, so its tree, shared subterms counted
/// at each occurrence, doubles per step while its depth grows by two.
fn shared_level_chain(len: u32) -> MinimalEnv {
    let mut env = MinimalEnv::new().with_const(n("c0"), 2);
    for k in 0..len {
        let levels = vec![imax_twice(RawLevel::Param(0)), RawLevel::Param(1)];
        let body = Term::validate(&env, &RawExpr::Const(n(&format!("c{k}")), levels), 0, 2)
            .expect("the body");
        let ty = Term::validate(&env, &RawExpr::Sort(RawLevel::Zero), 0, 2).expect("Prop");
        env = env.with_def(
            n(&format!("c{}", k + 1)),
            2,
            ty,
            body,
            Transparency::Transparent,
        );
    }
    env
}

fn shared_level_top(env: &MinimalEnv, len: u32) -> Term {
    let levels = vec![RawLevel::Param(0), RawLevel::Param(1)];
    Term::validate(env, &RawExpr::Const(n(&format!("c{len}")), levels), 0, 2).expect("the top")
}

#[test]
fn test_whnf_shared_level_control_eight_steps_unfold() {
    let env = shared_level_chain(8);
    let mut level = RawLevel::Param(0);
    for _ in 0..8 {
        level = imax_twice(level);
    }
    let expected = Term::validate(
        &env,
        &RawExpr::Const(n("c0"), vec![level, RawLevel::Param(1)]),
        0,
        2,
    )
    .expect("c0 at the eight-step level");
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &shared_level_top(&env, 8), &mut budget),
        Ok(expected)
    );
}

/// On main, 22 steps took 8.6 s and the time doubled per step; 40 were killed
/// at 6.3 GB. After `k` steps the level has `2^(k+2) - 3` nodes, so the level
/// size bound refuses the 15th unfolding.
#[test]
fn test_whnf_shared_level_is_refused_not_exponential() {
    let env = shared_level_chain(40);
    let top = shared_level_top(&env, 40);
    let fuel = Budget::default_budget().remaining();
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &top, &mut budget).map(|_| ()),
        Err(BudgetError::OutOfBudget)
    );
    assert!(
        budget.remaining() > fuel / 2,
        "refused by the level size bound, not by exhaustion"
    );
}
