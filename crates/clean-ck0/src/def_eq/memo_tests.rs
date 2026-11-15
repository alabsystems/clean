//! The conversion cache (`crate::whnf`'s `DEFEQ_CACHE`) keeps a failing pair's
//! answer within a decision. Without it, `f^d a ≡ f^d b` (`f` an opaque
//! function, `a`, `b` distinct constants) re-decides the inner pair twice per
//! level, before and after reducing both sides, so it costs `2^d` steps.
use super::*;
use crate::level::Level;
use crate::term::ConstRef;
use crate::MinimalEnv;

fn constant(env: &MinimalEnv, name: &str) -> Term {
    Term::const_ref(ConstRef::mk(env, Name::from_dotted(name), vec![]).unwrap())
}

fn env() -> MinimalEnv {
    let ty = Term::sort(Level::succ(Level::zero()));
    let base = MinimalEnv::new().with_const_typed(Name::from_dotted("A"), 0, ty);
    let a_ty = constant(&base, "A");
    let f_ty = Term::pi(BinderInfo::Default, a_ty.clone(), a_ty.clone());
    base.with_const_typed(Name::from_dotted("a"), 0, a_ty.clone())
        .with_const_typed(Name::from_dotted("b"), 0, a_ty)
        .with_const_typed(Name::from_dotted("f"), 0, f_ty)
}

fn iterate(env: &MinimalEnv, depth: u32, x: &str) -> Term {
    let f = constant(env, "f");
    (0..depth).fold(constant(env, x), |t, _| Term::app(f.clone(), t))
}

#[test]
fn test_conversion_cache_failing_nest_answers_false_in_linear_fuel() {
    let env = env();
    let mut budget = Budget::default_budget();
    let start = budget.remaining();
    let equal = is_def_eq(
        &env,
        &iterate(&env, 64, "a"),
        &iterate(&env, 64, "b"),
        &mut budget,
    )
    .expect("2^64 steps without the cache; a few hundred with it");
    assert!(
        !equal,
        "distinct constants under the same head stay unequal"
    );
    let used = start.checked_sub(budget.remaining()).unwrap();
    assert!(used < 10_000, "{used} steps for a depth-64 failing nest");
}

#[test]
fn test_conversion_cache_equal_nest_still_answers_true() {
    let env = env();
    let mut budget = Budget::default_budget();
    let left = iterate(&env, 64, "a");
    let right = iterate(&env, 64, "a");
    assert!(is_def_eq(&env, &left, &right, &mut budget).unwrap());
    // The two nests are distinct allocations of the same term.
    let wrapped = Term::app(constant(&env, "f"), left);
    assert!(!is_def_eq(&env, &wrapped, &right, &mut budget).unwrap());
}

/// The very same open pair is equal by proof irrelevance in one context,
/// and unequal as data in another. Both calls must share one decision cache:
/// separate outer decisions would clear it and miss a context-free key.
#[test]
fn test_conversion_cache_distinguishes_open_term_contexts() {
    let env = env().with_const_typed(Name::from_dotted("P"), 0, Term::sort(Level::zero()));
    let p = constant(&env, "P");
    let a = constant(&env, "A");
    let left = Term::bvar(0);
    let right = Term::bvar(1);
    for proof_first in [true, false] {
        let _scope = crate::whnf::DecisionScope::enter();
        let mut budget = Budget::default_budget();
        for proofs in [proof_first, !proof_first] {
            let ty = if proofs { &p } else { &a };
            assert_eq!(
                is_def_eq_in_context(&env, &[ty.clone(), ty.clone()], &left, &right, &mut budget,)
                    .unwrap(),
                proofs,
                "same open terms, proofs={proofs}, proof_first={proof_first}",
            );
        }
    }
}

/// The last two bindings have identical types syntactically, but those types
/// refer to an outer type variable whose sort decides proof irrelevance.
#[test]
fn test_conversion_cache_keeps_outer_type_dependencies() {
    let env = env();
    let left = Term::bvar(0);
    let right = Term::bvar(1);
    let x_type = Term::bvar(0);
    let y_type = Term::bvar(1);
    for proof_first in [true, false] {
        let _scope = crate::whnf::DecisionScope::enter();
        let mut budget = Budget::default_budget();
        for proofs in [proof_first, !proof_first] {
            let sort = if proofs {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            };
            // X : Prop/Type; x : X; y : X (stored before each binder).
            let ctx = [Term::sort(sort), x_type.clone(), y_type.clone()];
            assert_eq!(
                is_def_eq_in_context(&env, &ctx, &left, &right, &mut budget).unwrap(),
                proofs
            );
        }
    }
}

/// An unused outer prefix cannot change either answer. Reusing this exact
/// decision avoids re-visiting an open DAG node once per irrelevant prefix.
#[test]
fn test_conversion_cache_reuses_an_open_pair_across_unused_prefixes() {
    let env = env().with_const_typed(Name::from_dotted("P"), 0, Term::sort(Level::zero()));
    let p = constant(&env, "P");
    let left = Term::bvar(0);
    let right = Term::bvar(1);
    let _scope = crate::whnf::DecisionScope::enter();
    let mut budget = Budget::default_budget();
    let first = [Term::sort(Level::zero()), p.clone(), p.clone()];
    let second = [Term::sort(Level::succ(Level::zero())), p.clone(), p];
    assert!(is_def_eq_in_context(&env, &first, &left, &right, &mut budget).unwrap());
    let before = budget.remaining();
    assert!(is_def_eq_in_context(&env, &second, &left, &right, &mut budget).unwrap());
    assert_eq!(
        before.saturating_sub(budget.remaining()),
        1,
        "the cached pair costs one entry step"
    );
}
