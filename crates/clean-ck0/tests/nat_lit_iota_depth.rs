// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reduction depth and native `Nat` cost are bounded (`docs/DECISIONS.md` R166).
//!
//! A `Nat` literal major premise of `Nat.rec` (R162's ι arm) builds its depth at
//! reduction time, not in the input: `Nat.rec m z (fun _ ih => Nat.succ ih) N` is
//! a term of depth 1 whose reduct is `Nat.succ (Nat.rec … (N - 1))`, and native
//! `succ` reduction whnf's that argument by native recursion, nesting frames per
//! unit of `N`. `MAX_VALIDATE_DEPTH` caps only the input. Three paths recurse that
//! way: native `succ` reduction, ι's own major premise, and conversion's
//! argument congruence. On each, a large `N` must end as a verdict (an `Err`),
//! never as a native-stack abort of the process, and a small `N` still reduces.
//! Head reduction is a loop, so it can also BUILD a term `N` deep from a term of
//! depth 1 (`spine`); such a reduct is refused, since dropping, comparing or
//! substituting into it recurses natively once per level.
//!
//! `Nat.pow` is computed only up to Lean's exponent bound, 2^24, and
//! `Nat.shiftLeft` without ck0's old 2^24 cap, which Lean never had. Native
//! arithmetic, a literal's predecessor in ι and in conversion included, pays one
//! budget step per word of its result, and at least its operands' size, before
//! building it; `/`, `%` and `gcd` pay for their quadratic work. Native
//! reduction fires only on Lean's own `Nat.<op>` constants, and reads the
//! constant `Nat.zero` as `0`, as Lean's `is_nat_lit_ext` does. The frame cap's
//! known gap, a non-tail native `succ` chain past about 255 levels, is pinned as
//! a refusal.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, BigNat, Budget, BudgetError, Constructor, InductiveDecl, MinimalEnv, Name,
    RawExpr, RawLevel, RawLit, Term, Transparency,
};

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
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter().fold(f, r_app)
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn lit(v: u64) -> RawExpr {
    RawExpr::Lit(RawLit::Nat(BigNat::from_u64(v)))
}
fn level_one() -> RawLevel {
    RawLevel::Succ(Box::new(RawLevel::Zero))
}

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &MinimalEnv, raw: &RawExpr) -> Term {
    Term::validate(env, raw, 0, 0).expect("term validates")
}

/// `Nat : Type` with `zero : Nat`, `succ : Nat → Nat`.
fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1)),
        constructors: vec![
            Constructor {
                name: n("Nat.zero"),
                type_: vlvl(&b, &r_const("Nat")),
            },
            Constructor {
                name: n("Nat.succ"),
                type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat"))),
            },
        ],
    }
}

/// `Tower : Type` with `base : Tower`, `up : Tower → Tower`: a constructor that
/// `Nat`'s native reduction does not fold, so conversion compares under it.
fn tower_decl() -> InductiveDecl {
    let b = boot(&[("Tower", 0), ("Tower.base", 0), ("Tower.up", 0)]);
    InductiveDecl {
        name: n("Tower"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1)),
        constructors: vec![
            Constructor {
                name: n("Tower.base"),
                type_: vlvl(&b, &r_const("Tower")),
            },
            Constructor {
                name: n("Tower.up"),
                type_: vlvl(&b, &r_pi(r_const("Tower"), r_const("Tower"))),
            },
        ],
    }
}

fn env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, tower_decl()).expect("Tower admits");
    env
}

/// `Nat.rec (motive := fun _ => R) z s N`.
fn nat_rec(result: &str, zero_case: RawExpr, succ_case: RawExpr, major: RawExpr) -> RawExpr {
    r_apps(
        RawExpr::Elim(n("Nat"), level_one(), vec![]),
        vec![
            r_lam(r_const("Nat"), r_const(result)),
            zero_case,
            succ_case,
            major,
        ],
    )
}

/// `fun (_ : Nat) (ih : R) => body`, with `ih` as `#0` in `body`.
fn succ_case(result: &str, body: RawExpr) -> RawExpr {
    r_lam(r_const("Nat"), r_lam(r_const(result), body))
}

/// Native `succ` path: `Nat.rec 0 (fun _ ih => Nat.succ ih) N`, which is `N`.
fn count_up(env: &MinimalEnv, value: u64) -> Term {
    let raw = nat_rec(
        "Nat",
        r_const("Nat.zero"),
        succ_case("Nat", r_app(r_const("Nat.succ"), r_bvar(0))),
        lit(value),
    );
    vlvl(env, &raw)
}

/// ι's major path: `Nat.rec 0 (fun _ ih => Nat.rec 0 (fun _ _ => 0) ih) N`. Each
/// step's reduct is an eliminator whose major is the next step, so ι whnf's its
/// major one frame deeper per unit of `N`. It is `Nat.zero` for every `N`.
fn nested_majors(env: &MinimalEnv, value: u64) -> Term {
    let inner = nat_rec(
        "Nat",
        r_const("Nat.zero"),
        succ_case("Nat", r_const("Nat.zero")),
        r_bvar(0),
    );
    let raw = nat_rec(
        "Nat",
        r_const("Nat.zero"),
        succ_case("Nat", inner),
        lit(value),
    );
    vlvl(env, &raw)
}

/// Conversion's congruence path: two towers of height `N`. `plain` steps with
/// `fun _ ih => up ih`; `cased` with `fun k ih => Nat.rec (up ih) (fun _ _ => up
/// ih) k`, which is no constructor while `k` is a variable, so the two step
/// functions are not convertible and conversion must unfold both sides and
/// compare under `up`, one frame deeper per level.
fn towers(env: &MinimalEnv, value: u64) -> (Term, Term) {
    let up_ih = |shift: u32| r_app(r_const("Tower.up"), r_bvar(shift));
    let plain = nat_rec(
        "Tower",
        r_const("Tower.base"),
        succ_case("Tower", up_ih(0)),
        lit(value),
    );
    // Under `k` (#1) and `ih` (#0); inside the inner minor's two binders `ih` is #2.
    let cased_body = nat_rec("Tower", up_ih(0), succ_case("Tower", up_ih(2)), r_bvar(1));
    let cased = nat_rec(
        "Tower",
        r_const("Tower.base"),
        succ_case("Tower", cased_body),
        lit(value),
    );
    (vlvl(env, &plain), vlvl(env, &cased))
}

/// `Nat.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun _ ih x => ih (g x))
/// N Nat.zero`, with `g` an opaque constant. Head reduction is a loop that ends at
/// `g (g (… Nat.zero))`, a reduct `N` deep built from a term of depth 1.
fn spine(env: &MinimalEnv, value: u64) -> Term {
    let nat_to_nat = || r_pi(r_const("Nat"), r_const("Nat"));
    let raw = r_apps(
        RawExpr::Elim(n("Nat"), level_one(), vec![]),
        vec![
            r_lam(r_const("Nat"), nat_to_nat()),
            r_lam(r_const("Nat"), r_bvar(0)),
            r_lam(
                r_const("Nat"),
                r_lam(
                    nat_to_nat(),
                    r_lam(
                        r_const("Nat"),
                        r_app(r_bvar(1), r_app(r_const("g"), r_bvar(0))),
                    ),
                ),
            ),
            lit(value),
            r_const("Nat.zero"),
        ],
    );
    vlvl(env, &raw)
}

/// `g` applied `count` times to `Nat.zero`.
fn g_iterated(env: &MinimalEnv, count: u32) -> Term {
    let mut raw = r_const("Nat.zero");
    for _ in 0..count {
        raw = r_app(r_const("g"), raw);
    }
    vlvl(env, &raw)
}

fn env_with_g() -> MinimalEnv {
    env().with_const(n("g"), 0)
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

/// A refusal by the frame cap or the reduct-depth bound, not exhaustion: both
/// are `OutOfBudget`, but these fire after a few thousand steps, while running
/// out of fuel leaves none.
fn assert_refused_with_fuel_left(outcome: (Result<(), BudgetError>, u64), fuel: u64) {
    let (verdict, left) = outcome;
    assert_eq!(verdict, Err(BudgetError::OutOfBudget));
    assert!(
        left > fuel / 2,
        "refused by a depth bound with fuel left, not by exhaustion ({left} of {fuel} left)"
    );
}

#[test]
fn test_reduction_depth_control_small_literal_counts_up() {
    let env = env();
    let mut budget = Budget::default_budget();
    let reduct = clean_ck0::whnf(&env, &count_up(&env, 200), &mut budget)
        .expect("200 levels fit the frame cap and the default budget");
    // The base case is the constant `Nat.zero`; native `succ` reads it as `0`.
    assert_eq!(
        reduct,
        vlvl(&env, &lit(200)),
        "Nat.rec … 200 counts back up to 200"
    );
}

/// A known gap, pinned as a refusal (R166): a native `succ` level holds two
/// reduction frames, so about 255 levels fit the frame cap, while pinned Lean,
/// which guards the same recursion by stack space, reduces this to `300`. When
/// the gap closes this test fails; it then becomes a control expecting `300`.
#[test]
fn test_reduction_depth_gap_count_up_300_is_refused_where_lean_reduces_it() {
    let env = env();
    let fuel = Budget::default_budget().remaining();
    let mut budget = Budget::default_budget();
    let verdict = clean_ck0::whnf(&env, &count_up(&env, 300), &mut budget).map(|_| ());
    assert_refused_with_fuel_left((verdict, budget.remaining()), fuel);
}

#[test]
fn test_reduction_depth_native_succ_path_is_a_verdict_not_an_abort() {
    let fuel = Budget::default_budget().remaining();
    let outcome = on_main_sized_stack(|| {
        let env = env();
        let mut budget = Budget::default_budget();
        let verdict = clean_ck0::whnf(&env, &count_up(&env, 200_000), &mut budget).map(|_| ());
        (verdict, budget.remaining())
    });
    assert_refused_with_fuel_left(outcome, fuel);
}

#[test]
fn test_reduction_depth_control_small_nested_majors_reduce() {
    let env = env();
    let mut budget = Budget::default_budget();
    let reduct = clean_ck0::whnf(&env, &nested_majors(&env, 50), &mut budget)
        .expect("50 nested majors fit the default budget");
    assert_eq!(reduct, vlvl(&env, &r_const("Nat.zero")));
}

#[test]
fn test_reduction_depth_iota_major_path_is_a_verdict_not_an_abort() {
    let fuel = Budget::default_budget().remaining();
    let outcome = on_main_sized_stack(|| {
        let env = env();
        let mut budget = Budget::default_budget();
        let verdict = clean_ck0::whnf(&env, &nested_majors(&env, 200_000), &mut budget).map(|_| ());
        (verdict, budget.remaining())
    });
    assert_refused_with_fuel_left(outcome, fuel);
}

#[test]
fn test_reduction_depth_control_small_towers_convert() {
    let env = env();
    let (plain, cased) = towers(&env, 50);
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::is_def_eq(&env, &plain, &cased, &mut budget),
        Ok(true),
        "two towers of height 50 are the same tower"
    );
}

#[test]
fn test_reduction_depth_conversion_path_is_a_verdict_not_an_abort() {
    // The fuel clean-kernel's `ck0_ingest_codegen` gate re-checks with: on the
    // default budget this path runs out of fuel before its depth matters.
    let fuel = 64_000_000;
    let outcome = on_main_sized_stack(move || {
        let env = env();
        let (plain, cased) = towers(&env, 200_000);
        let mut budget = Budget::new(fuel);
        let verdict = clean_ck0::is_def_eq(&env, &plain, &cased, &mut budget).map(|_| ());
        (verdict, budget.remaining())
    });
    assert_refused_with_fuel_left(outcome, fuel);
}

#[test]
fn test_reduction_depth_control_small_spine_is_built() {
    let env = env_with_g();
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &spine(&env, 50), &mut budget),
        Ok(g_iterated(&env, 50)),
        "the loop builds g applied 50 times"
    );
}

#[test]
fn test_reduction_depth_built_spine_is_a_verdict_not_an_abort() {
    let fuel = Budget::default_budget().remaining();
    let outcome = on_main_sized_stack(|| {
        let env = env_with_g();
        let mut budget = Budget::default_budget();
        let verdict = clean_ck0::whnf(&env, &spine(&env, 200_000), &mut budget).map(|_| ());
        (verdict, budget.remaining())
    });
    assert_refused_with_fuel_left(outcome, fuel);
}

fn pow(env: &MinimalEnv, base: u64, exponent: u64) -> Term {
    vlvl(
        env,
        &r_apps(r_const("Nat.pow"), vec![lit(base), lit(exponent)]),
    )
}

#[test]
fn test_native_pow_reduces_up_to_the_exponent_bound() {
    let env = boot(&[("Nat.pow", 0)]);
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &pow(&env, 2, 10), &mut budget),
        Ok(vlvl(&env, &lit(1024)))
    );
    let at_bound = clean_ck0::whnf(&env, &pow(&env, 1, 1 << 24), &mut budget)
        .expect("an exponent of 2^24 is within the bound");
    assert_eq!(at_bound, vlvl(&env, &lit(1)), "1^(2^24) is computed");
}

#[test]
fn test_native_pow_past_the_exponent_bound_stays_stuck() {
    let env = boot(&[("Nat.pow", 0)]);
    let past = pow(&env, 2, (1 << 24) + 1);
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &past, &mut budget),
        Ok(past.clone()),
        "Lean's kernel leaves Nat.pow 2 (2^24 + 1) unreduced"
    );
}

#[test]
fn test_native_succ_reads_nat_zero_as_zero() {
    let env = env();
    let mut budget = Budget::default_budget();
    let one = vlvl(&env, &r_app(r_const("Nat.succ"), r_const("Nat.zero")));
    assert_eq!(
        clean_ck0::whnf(&env, &one, &mut budget),
        Ok(vlvl(&env, &lit(1))),
        "Lean's kernel reduces Nat.succ Nat.zero to 1"
    );
}

#[test]
fn test_native_binary_op_reads_nat_zero_as_zero() {
    let env = boot(&[("Nat.add", 0), ("Nat.zero", 0)]);
    let mut budget = Budget::default_budget();
    let sum = vlvl(
        &env,
        &r_apps(r_const("Nat.add"), vec![r_const("Nat.zero"), lit(2)]),
    );
    assert_eq!(
        clean_ck0::whnf(&env, &sum, &mut budget),
        Ok(vlvl(&env, &lit(2)))
    );
}

#[test]
fn test_native_succ_of_nat_zero_is_not_two() {
    let env = env();
    let mut budget = Budget::default_budget();
    let one = vlvl(&env, &r_app(r_const("Nat.succ"), r_const("Nat.zero")));
    assert_eq!(
        clean_ck0::is_def_eq(&env, &one, &vlvl(&env, &lit(2)), &mut budget),
        Ok(false),
        "negative control: Nat.succ Nat.zero is 1, not 2"
    );
}

fn shift_left(value: RawExpr, shift: u64) -> RawExpr {
    r_apps(r_const("Nat.shiftLeft"), vec![value, lit(shift)])
}

/// `Nat.pow (Nat.shiftLeft 1 2^20) 4` is `2^(2^22)`: a result of 65,537 words.
fn big_power(env: &MinimalEnv) -> Term {
    let base = shift_left(lit(1), 1 << 20);
    vlvl(env, &r_apps(r_const("Nat.pow"), vec![base, lit(4)]))
}

#[test]
fn test_native_nat_work_control_big_power_is_computed() {
    let env = boot(&[("Nat.pow", 0), ("Nat.shiftLeft", 0)]);
    let mut budget = Budget::default_budget();
    let power =
        clean_ck0::whnf(&env, &big_power(&env), &mut budget).expect("fits the default budget");
    let mut budget = Budget::default_budget();
    let expected = vlvl(&env, &shift_left(lit(1), 1 << 22));
    let expected = clean_ck0::whnf(&env, &expected, &mut budget).expect("fits the default budget");
    assert_eq!(power, expected, "(2^(2^20))^4 = 2^(2^22)");
}

/// An operation whose charge does not fit is refused and exhausts the budget.
/// That the charge comes before the result is built is the order of
/// `try_native_nat`'s code, which no outcome here can observe.
#[test]
fn test_native_nat_work_over_the_budget_is_refused() {
    let env = boot(&[("Nat.pow", 0), ("Nat.shiftLeft", 0)]);
    // The base costs 16,385 words; the power's 65,537 do not fit what is left.
    let mut budget = Budget::new(50_000);
    assert_eq!(
        clean_ck0::whnf(&env, &big_power(&env), &mut budget),
        Err(BudgetError::OutOfBudget)
    );
    assert_eq!(
        budget.remaining(),
        0,
        "a refused charge exhausts the budget"
    );
}

/// `2^65536`, a literal of 1,025 words.
fn big_literal() -> BigNat {
    BigNat::from_u64(2).pow(&BigNat::from_u64(1 << 16))
}

fn big_lit(value: &BigNat) -> RawExpr {
    RawExpr::Lit(RawLit::Nat(value.clone()))
}

/// Only Lean's own level-free `Nat.<op>` constants reduce natively: pinned Lean
/// compares the head with each exact constant. A user's `Foo.Nat.add` is an
/// ordinary definition, unfolded by δ.
#[test]
fn test_native_nat_ops_are_leans_root_constants_only() {
    let base = env();
    let nat_to_nat_to_nat = r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat")));
    let ty = vlvl(&base, &nat_to_nat_to_nat);
    let first = vlvl(
        &base,
        &r_lam(r_const("Nat"), r_lam(r_const("Nat"), r_bvar(1))),
    );
    let env = base
        .with_def(n("Foo.Nat.add"), 0, ty, first, Transparency::Transparent)
        .with_const(n("Foo.Nat.succ"), 0);
    let mut budget = Budget::default_budget();
    let add = vlvl(&env, &r_apps(r_const("Foo.Nat.add"), vec![lit(2), lit(3)]));
    assert_eq!(
        clean_ck0::whnf(&env, &add, &mut budget),
        Ok(vlvl(&env, &lit(2))),
        "δ unfolds Foo.Nat.add 2 3 to its first argument"
    );
    assert_eq!(
        clean_ck0::is_def_eq(&env, &add, &vlvl(&env, &lit(5)), &mut budget),
        Ok(false),
        "Foo.Nat.add 2 3 is not 2 + 3"
    );
    let succ = vlvl(&env, &r_app(r_const("Foo.Nat.succ"), lit(1)));
    assert_eq!(
        clean_ck0::whnf(&env, &succ, &mut budget),
        Ok(succ.clone()),
        "an opaque Foo.Nat.succ stays stuck"
    );
}

/// `Nat.rec 0 (fun n _ => n) L` is `L - 1`: one ι step on a literal major. The
/// predecessor is native arithmetic, charged before it is built.
#[test]
fn test_iota_on_a_literal_major_pays_for_its_predecessor() {
    let env = env();
    let big = big_literal();
    let rec = vlvl(
        &env,
        &nat_rec(
            "Nat",
            r_const("Nat.zero"),
            succ_case("Nat", r_bvar(1)),
            big_lit(&big),
        ),
    );
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &rec, &mut budget),
        Ok(vlvl(&env, &big_lit(&big.sub(&BigNat::one())))),
        "control: it fits the default budget"
    );
    let mut budget = Budget::new(500);
    assert_eq!(
        clean_ck0::whnf(&env, &rec, &mut budget),
        Err(BudgetError::OutOfBudget),
        "the predecessor is charged 1,026 steps, more than 500"
    );
}

/// `L ≡ Nat.succ c` compares `L - 1` with `c`: the predecessor is charged before
/// it is built.
#[test]
fn test_conversion_of_a_literal_with_succ_pays_for_its_predecessor() {
    let env = env().with_const(n("c"), 0);
    let big = vlvl(&env, &big_lit(&big_literal()));
    let succ_c = vlvl(&env, &r_app(r_const("Nat.succ"), r_const("c")));
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::is_def_eq(&env, &big, &succ_c, &mut budget),
        Ok(false),
        "control: c is opaque"
    );
    let mut budget = Budget::new(500);
    assert_eq!(
        clean_ck0::is_def_eq(&env, &big, &succ_c, &mut budget),
        Err(BudgetError::OutOfBudget),
        "the predecessor is charged 1,026 steps, more than 500"
    );
}

/// `/`, `%` and `gcd` are charged the product of their operands' sizes, which
/// bounds their quadratic work: `gcd L L` is charged 1,025² = 1,050,625 steps,
/// and `L % 3` is charged 1,026.
#[test]
fn test_native_division_is_charged_by_its_work() {
    let env = boot(&[("Nat.gcd", 0), ("Nat.mod", 0)]);
    let big = big_lit(&big_literal());
    let gcd = vlvl(
        &env,
        &r_apps(r_const("Nat.gcd"), vec![big.clone(), big.clone()]),
    );
    let mut budget = Budget::new(2_000_000);
    assert_eq!(
        clean_ck0::whnf(&env, &gcd, &mut budget),
        Ok(vlvl(&env, &big)),
        "control: gcd L L = L within 2M steps"
    );
    let mut budget = Budget::new(1_000_000);
    assert_eq!(
        clean_ck0::whnf(&env, &gcd, &mut budget),
        Err(BudgetError::OutOfBudget),
        "a 1,050,625-step charge does not fit the explicit 1M allowance"
    );
    let modulo = vlvl(&env, &r_apps(r_const("Nat.mod"), vec![big, lit(3)]));
    let mut budget = Budget::new(5_000);
    assert_eq!(
        clean_ck0::whnf(&env, &modulo, &mut budget),
        Ok(vlvl(&env, &lit(1))),
        "2^65536 % 3 = 1, at a linear charge"
    );
}

/// Reading two literals copies them, so a comparison, whose result is one
/// `Bool`, and an application that stays stuck are charged the operands' size:
/// 1,026 steps for `L = 2^65536`. The stuck case is a shift past `u64`, which
/// main leaves stuck too, so main's run of this test stays bounded.
#[test]
fn test_native_nat_operands_are_charged_when_the_result_is_small() {
    let env = boot(&[("Nat.beq", 0), ("Nat.shiftLeft", 0), ("Bool.true", 0)]);
    let big = big_lit(&big_literal());
    let beq = vlvl(
        &env,
        &r_apps(r_const("Nat.beq"), vec![big.clone(), big.clone()]),
    );
    let past_u64 = big_lit(&BigNat::from_u64(2).pow(&BigNat::from_u64(64)));
    let stuck = vlvl(&env, &r_apps(r_const("Nat.shiftLeft"), vec![big, past_u64]));
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &beq, &mut budget),
        Ok(vlvl(&env, &r_const("Bool.true"))),
        "control: L == L"
    );
    assert_eq!(
        clean_ck0::whnf(&env, &stuck, &mut budget),
        Ok(stuck.clone()),
        "control: a shift past u64 stays stuck"
    );
    for (what, term) in [("L == L", &beq), ("L <<< 2^64", &stuck)] {
        let mut budget = Budget::new(500);
        assert_eq!(
            clean_ck0::whnf(&env, term, &mut budget),
            Err(BudgetError::OutOfBudget),
            "{what} is charged 1,026 steps, more than 500"
        );
    }
}

/// Pinned Lean bounds no `Nat.shiftLeft`; the work meter pays for the result.
#[test]
fn test_native_shift_left_past_two_to_the_24_reduces_as_in_lean() {
    let env = boot(&[("Nat.shiftLeft", 0), ("Nat.shiftRight", 0)]);
    let shift = (1 << 24) + 1;
    let mut budget = Budget::default_budget();
    assert_eq!(
        clean_ck0::whnf(&env, &vlvl(&env, &shift_left(lit(0), shift)), &mut budget),
        Ok(vlvl(&env, &lit(0))),
        "0 <<< k is 0"
    );
    let round_trip = vlvl(
        &env,
        &r_apps(
            r_const("Nat.shiftRight"),
            vec![shift_left(lit(1), shift), lit(shift)],
        ),
    );
    assert_eq!(
        clean_ck0::whnf(&env, &round_trip, &mut budget),
        Ok(vlvl(&env, &lit(1))),
        "(1 <<< k) >>> k = 1"
    );
}

/// Native binary folds, like pinned Lean's kernel, do not touch the second
/// operand after the first is known not to be a literal. The unchanged depth
/// guard still refuses that second operand when it is actually demanded.
#[test]
fn test_native_binary_fold_short_circuits_a_nonliteral_first_operand() {
    let env = env();
    let ty = vlvl(
        &env,
        &r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat"))),
    );
    let env = env.with_const_typed(n("Nat.add"), 0, ty);
    let rhs = nat_rec(
        "Nat",
        r_const("Nat.zero"),
        succ_case("Nat", r_app(r_const("Nat.succ"), r_bvar(0))),
        lit(300),
    );
    let raw = r_apps(r_const("Nat.add"), vec![r_bvar(0), rhs]);
    let term = Term::validate(&env, &raw, 1, 0).unwrap();
    let mut budget = Budget::default_budget();
    assert_eq!(clean_ck0::whnf(&env, &term, &mut budget).unwrap(), term);
    let mut demanded = Budget::default_budget();
    assert!(clean_ck0::whnf(&env, &count_up(&env, 300), &mut demanded).is_err());
}
