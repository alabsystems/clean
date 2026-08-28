// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **KERNEL PROBE — can the kernel already express a decreasing proof whose
//! goal carries TRUNCATED SUBTRACTION on both sides of the comparison?**
//!
//! The decreasing cascade in `clean-elab` closes a `Nat.lt` obligation with a
//! ladder of named prelude theorems (`Nat.sub_lt`, `Nat.mod_lt`, the
//! `Nat.add_lt_add_*` sum congruences). None of them can see through Nat's
//! *truncated* subtraction: `a - b` is `0` when `a ≤ b` and a genuine
//! difference otherwise, so any obligation whose truth depends on WHICH of the
//! two holds is outside every tier. The branch-free Euclid step
//! `gcdB a b = gcdB ((a-b)+(b-a)) (a-(a-b))` with `termination_by a + 2*b` is
//! exactly such an obligation, and it is refused today.
//!
//! Before widening the cascade, this file answers the prior question by hand:
//! is the refusal a KERNEL limit, or only a cascade limit? The claim under
//! test is that it is only a cascade limit, because the standard elimination
//! works with prelude pieces that already exist:
//!
//! ```text
//! Or.rec (Nat.le_total x y)                      -- case split on the order
//!   branch (h : x ≤ y):  d := y - x,  hd : x + d = y
//!                        rewrite y := x + d in the goal (congrArg + Eq.mp)
//!                        every `-` node now has a closed form:
//!                          x - (x + d) = 0        Nat.ulpRound.sub_eq_zero_of_le
//!                          (x + d) - x = d        Nat.ulpRound.add_sub_cancel_left
//!                          (x + d) - d = x        Nat.ulpRound.add_sub_self_right
//!                          t - 0       = t        Nat.sub_zero
//!                          0 + t       = t        Nat.zero_add
//!                        the residual goal `L < R` is subtraction-free and is
//!                        closed by `Nat.add_lt_add_left 0 S hS L : L < L + S`
//!                        transported along `L + S = R`.
//! ```
//!
//! NOTHING HERE IS ASSUMED. Every step is a real term over constructive,
//! axiom-free prelude theorems; the kernel re-checks each declaration at
//! `add_decl`; the axiom closure is audited empty; and the adversarial controls
//! at the bottom hand the kernel the SAME skeletons with one piece swapped for
//! a wrong-typed one, and with a FALSE sibling proposition, and require a
//! rejection in every case.
//!
//! The probe proposition is `min a b < a + b` spelled without `Nat.min`:
//!
//! ```text
//! probeSplit : ∀ (a b : Nat), 0 < b → (a - (a - b)) < a + b
//! ```
//!
//! It is the smallest proposition that needs the WHOLE machinery: `a - (a - b)`
//! is `b` in one branch and `a` in the other, so no single rewrite closes it,
//! and the residual `<` is not a congruence of the two sides.
//!
//! **What this fixture does and does not show.** It shows the kernel accepts
//! the case-split + substitution + normalize + residual skeleton, and it pins
//! the exact spelling of every prelude lemma the cascade tier will name. It
//! does NOT show that a search procedure can FIND these terms — that is the
//! cascade's job, exercised end-to-end in
//! `clean-elab/tests/wf_branch_free_gcd_e2e.rs`.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, Level};

/// Constants this hand-built probe names. Checked up front so a missing
/// prelude piece fails with its own name rather than as a kernel error deep
/// inside a term.
const REQUIRED: &[&str] = &[
    "Nat",
    "Nat.lt",
    "Nat.le",
    "Nat.add",
    "Nat.sub",
    "Nat.zero",
    "Nat.succ",
    "Nat.le_total",
    "Nat.le_trans",
    "Nat.le_add_right",
    "Nat.add_comm",
    "Nat.add_lt_add_left",
    "Nat.sub_zero",
    "Nat.zero_add",
    "Nat.ulpRound.sub_eq_zero_of_le",
    "Nat.ulpRound.sub_add_cancel",
    "Nat.ulpRound.add_sub_cancel_left",
    "Nat.ulpRound.add_sub_self_right",
    "Or.rec",
    "Eq",
    "Eq.mp",
    "Eq.mpr",
    "Eq.trans",
    "congrArg",
];

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat() -> Expr {
    cst("Nat")
}

fn add(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.add"), [x, y])
}

fn sub(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.sub"), [x, y])
}

fn lt(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.lt"), [x, y])
}

fn le(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.le"), [x, y])
}

fn zero() -> Expr {
    cst("Nat.zero")
}

/// `@Eq.{1} Nat lhs rhs`.
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), lhs, rhs],
    )
}

/// `@Eq.trans.{1} Nat a b c h1 h2 : a = c`.
fn eq_trans(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), a, b, c, h1, h2],
    )
}

/// `@congrArg.{1,1} Nat Prop a₁ a₂ f h : f a₁ = f a₂`, for `f : Nat → Prop`.
///
/// `f` is given as a body with `hole` abstracted out.
fn congr_arg_prop(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        [nat(), Expr::sort(Level::zero()), a1, a2, f, h],
    )
}

/// `@congrArg.{1,1} Nat Nat a₁ a₂ f h : f a₁ = f a₂`, for `f : Nat → Nat`.
fn congr_arg_nat(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        [nat(), nat(), a1, a2, f, h],
    )
}

/// `fun (t : Nat) => body[hole := t]`.
fn nat_lam(hole: FVarId, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), body.abstract_fvar(hole))
}

/// `@Eq.mp.{0} α β (h : α = β) (a : α) : β`.
fn eq_mp(alpha: Expr, beta: Expr, h: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
        [alpha, beta, h, a],
    )
}

/// `@Eq.mpr.{0} α β (h : α = β) (b : β) : α`.
fn eq_mpr(alpha: Expr, beta: Expr, h: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
        [alpha, beta, h, b],
    )
}

/// `@Or.rec ha hb (fun _ => motive) minor_left minor_right major`.
///
/// The motive is constant (the goal does not mention the disjunction proof),
/// which is what a case split on `Nat.le_total` needs.
fn or_rec(ha: Expr, hb: Expr, goal: Expr, left: Expr, right: Expr, major: Expr) -> Expr {
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::apps(cst("Or"), [ha.clone(), hb.clone()]),
        goal,
    );
    Expr::apps(cst("Or.rec"), [ha, hb, motive, left, right, major])
}

/// `0 < x + y` from `hx : 0 < x`, via `Nat.le_trans 1 x (x + y) hx (Nat.le_add_right x y)`.
///
/// `Nat.lt 0 t` is `Nat.le (Nat.succ 0) t` by δ, so `Nat.le_trans` at
/// `a := Nat.succ Nat.zero` IS the positivity statement.
fn pos_add_left(x: Expr, y: Expr, hx: Expr) -> Expr {
    Expr::apps(
        cst("Nat.le_trans"),
        [
            Expr::app(cst("Nat.succ"), zero()),
            x.clone(),
            add(x.clone(), y.clone()),
            hx,
            Expr::apps(cst("Nat.le_add_right"), [x, y]),
        ],
    )
}

/// `L < L + S` from `hs : 0 < S`, via `Nat.add_lt_add_left 0 S hs L`.
///
/// The lemma's conclusion is `Nat.lt (Nat.add L Nat.zero) (Nat.add L S)`, and
/// `Nat.add L Nat.zero` ι-reduces to `L`, so the term inhabits `L < L + S`
/// **without any transport**. That definitional identity is the load-bearing
/// assumption of the residual tier and is what `probe_1_*` pins.
fn lt_add_pos(l: Expr, s: Expr, hs: Expr) -> Expr {
    Expr::apps(cst("Nat.add_lt_add_left"), [zero(), s, hs, l])
}

fn env_with_prelude() -> Environment {
    let env = Environment::with_prelude();
    for name in REQUIRED {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "prelude must provide `{name}` for this probe to mean anything"
        );
    }
    env
}

/// Register a theorem and assert its axiom closure is foundational-only.
fn add_theorem(env: &mut Environment, name: &str, ty: Expr, value: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
    })
    .map_err(|e| format!("{e:?}"))?;
    let closure = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must have an axiom closure"));
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let offending: Vec<String> = closure
        .iter()
        .map(ToString::to_string)
        .filter(|ax| !foundational.contains(&ax.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "{name} must be axiom-free, got {offending:?}"
    );
    Ok(())
}

// ══════════════ probe 1: the strict-residual step ══════════════

/// `Nat.add_lt_add_left Nat.zero S hs L` inhabits `Nat.lt L (Nat.add L S)`.
///
/// This is the whole residual tier in one term: an obligation `L < R` where the
/// linear form of `R` exceeds that of `L` by a positive residual `S` reduces to
/// `0 < S`. It works only because `Nat.add L Nat.zero` is DEFINITIONALLY `L`.
#[test]
fn probe_1_strict_residual_needs_no_transport() {
    let mut env = env_with_prelude();
    let (l, s, hs) = (FVarId::new(7001), FVarId::new(7002), FVarId::new(7003));
    let body = lt_add_pos(Expr::fvar(l), Expr::fvar(s), Expr::fvar(hs));
    let goal = lt(Expr::fvar(l), add(Expr::fvar(l), Expr::fvar(s)));

    let ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                lt(zero(), Expr::fvar(s)),
                goal.abstract_fvar(hs),
            )
            .abstract_fvar(s),
        )
        .abstract_fvar(l),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(
                BinderInfo::Default,
                lt(zero(), Expr::fvar(s)),
                body.abstract_fvar(hs),
            )
            .abstract_fvar(s),
        )
        .abstract_fvar(l),
    );
    add_theorem(&mut env, "probeResidual", ty, value).expect("the residual step must kernel-check");
}

/// ADVERSARIAL CONTROL for probe 1: the same term at a residual that is NOT the
/// one the goal names must be REJECTED. Without this, probe 1 shows only that
/// *some* term type-checks.
#[test]
fn probe_1_control_a_mismatched_residual_is_rejected() {
    let mut env = env_with_prelude();
    let (l, s, hs) = (FVarId::new(7011), FVarId::new(7012), FVarId::new(7013));
    // The claim is `L < L + S`; the value proves `L < L + S` for the WRONG
    // summand order (`S + L`), which is not definitionally the same term.
    let body = Expr::apps(
        cst("Nat.add_lt_add_left"),
        [zero(), Expr::fvar(l), Expr::fvar(hs), Expr::fvar(s)],
    );
    let goal = lt(Expr::fvar(l), add(Expr::fvar(l), Expr::fvar(s)));
    let ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                lt(zero(), Expr::fvar(s)),
                goal.abstract_fvar(hs),
            )
            .abstract_fvar(s),
        )
        .abstract_fvar(l),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(
                BinderInfo::Default,
                lt(zero(), Expr::fvar(s)),
                body.abstract_fvar(hs),
            )
            .abstract_fvar(s),
        )
        .abstract_fvar(l),
    );
    assert!(
        add_theorem(&mut env, "probeResidualBad", ty, value).is_err(),
        "a residual proof about the wrong summand must be REJECTED"
    );
    assert!(
        env.get_const(&Name::from_string("probeResidualBad"))
            .is_none(),
        "a rejected theorem must register nothing"
    );
}

// ═══════ probe 2: the case split, substitution and normalization ═══════

/// The probe proposition `∀ (a b : Nat), 0 < b → (a - (a - b)) < a + b`,
/// as a type over the two parameter fvars.
fn probe_split_goal(a: FVarId, b: FVarId) -> Expr {
    lt(
        sub(Expr::fvar(a), sub(Expr::fvar(a), Expr::fvar(b))),
        add(Expr::fvar(a), Expr::fvar(b)),
    )
}

/// Build the whole `probeSplit` value. `wrong_residual` swaps the branch-2
/// residual for one the goal does not name (the adversarial control).
fn build_probe_split(a: FVarId, b: FVarId, h: FVarId, wrong_residual: bool) -> Expr {
    let (ea, eb, eh) = (Expr::fvar(a), Expr::fvar(b), Expr::fvar(h));
    let goal = probe_split_goal(a, b);

    // ── branch 1: `hab : a ≤ b`. Then `b = a + d` with `d := b - a`. ──
    let hab = FVarId::new(7101);
    let d1 = sub(eb.clone(), ea.clone());
    // hd : Nat.add a d = b
    //    = Eq.trans (Nat.add_comm a d) (Nat.ulpRound.sub_add_cancel b a hab)
    let hd1 = eq_trans(
        add(ea.clone(), d1.clone()),
        add(d1.clone(), ea.clone()),
        eb.clone(),
        Expr::apps(cst("Nat.add_comm"), [ea.clone(), d1.clone()]),
        Expr::apps(
            cst("Nat.ulpRound.sub_add_cancel"),
            [eb.clone(), ea.clone(), Expr::fvar(hab)],
        ),
    );
    // Substitute `b := a + d` in the goal and in the hypothesis `h : 0 < b`.
    let subst1 = add(ea.clone(), d1.clone());
    let goal1 = goal.clone().subst_fvar(b, &subst1);
    // hs : 0 < a + d, by transporting `h : 0 < b` backwards along hd.
    let pos_ty_open = lt(zero(), Expr::fvar(b));
    let hs1 = eq_mpr(
        lt(zero(), subst1.clone()),
        lt(zero(), eb.clone()),
        congr_arg_prop(
            subst1.clone(),
            eb.clone(),
            nat_lam(b, pos_ty_open.clone()),
            hd1.clone(),
        ),
        eh.clone(),
    );
    // Normalize `a - (a + d)` to `Nat.zero`, hence `a - (a - (a + d))` to `a`.
    let inner1 = sub(ea.clone(), subst1.clone());
    let pf_inner1 = Expr::apps(
        cst("Nat.ulpRound.sub_eq_zero_of_le"),
        [
            ea.clone(),
            subst1.clone(),
            Expr::apps(cst("Nat.le_add_right"), [ea.clone(), d1.clone()]),
        ],
    );
    let hole = FVarId::new(7199);
    let pf_lhs1 = eq_trans(
        sub(ea.clone(), inner1.clone()),
        sub(ea.clone(), zero()),
        ea.clone(),
        congr_arg_nat(
            inner1.clone(),
            zero(),
            nat_lam(hole, sub(ea.clone(), Expr::fvar(hole))),
            pf_inner1,
        ),
        Expr::app(cst("Nat.sub_zero"), ea.clone()),
    );
    // Residual: `a < a + (a + d)`, from `0 < a + d`.
    let r1 = add(ea.clone(), subst1.clone());
    let core1 = lt_add_pos(ea.clone(), subst1.clone(), hs1);
    // Transport `a < R` back to `(a - (a - (a+d))) < R` along pf_lhs1.
    let branch1_inner = eq_mpr(
        lt(sub(ea.clone(), inner1.clone()), r1.clone()),
        lt(ea.clone(), r1.clone()),
        congr_arg_prop(
            sub(ea.clone(), inner1.clone()),
            ea.clone(),
            nat_lam(hole, lt(Expr::fvar(hole), r1.clone())),
            pf_lhs1,
        ),
        core1,
    );
    // Transport the substitution away: goal1 = goal[b := a + d], and
    // `congrArg (fun t => goal[b := t]) hd1 : goal1 = goal`.
    let branch1 = Expr::lam(
        BinderInfo::Default,
        le(ea.clone(), eb.clone()),
        eq_mp(
            goal1.clone(),
            goal.clone(),
            congr_arg_prop(subst1, eb.clone(), nat_lam(b, goal.clone()), hd1),
            branch1_inner,
        )
        .abstract_fvar(hab),
    );

    // ── branch 2: `hba : b ≤ a`. Then `a = b + d` with `d := a - b`. ──
    let hba = FVarId::new(7102);
    let d2 = sub(ea.clone(), eb.clone());
    let hd2 = eq_trans(
        add(eb.clone(), d2.clone()),
        add(d2.clone(), eb.clone()),
        ea.clone(),
        Expr::apps(cst("Nat.add_comm"), [eb.clone(), d2.clone()]),
        Expr::apps(
            cst("Nat.ulpRound.sub_add_cancel"),
            [ea.clone(), eb.clone(), Expr::fvar(hba)],
        ),
    );
    let subst2 = add(eb.clone(), d2.clone());
    let goal2 = goal.clone().subst_fvar(a, &subst2);
    // Normalize: `(b + d) - b = d`, then `(b + d) - d = b`.
    let inner2 = sub(subst2.clone(), eb.clone());
    let pf_inner2 = Expr::apps(
        cst("Nat.ulpRound.add_sub_cancel_left"),
        [eb.clone(), d2.clone()],
    );
    let pf_lhs2 = eq_trans(
        sub(subst2.clone(), inner2.clone()),
        sub(subst2.clone(), d2.clone()),
        eb.clone(),
        congr_arg_nat(
            inner2.clone(),
            d2.clone(),
            nat_lam(hole, sub(subst2.clone(), Expr::fvar(hole))),
            pf_inner2,
        ),
        Expr::apps(
            cst("Nat.ulpRound.add_sub_self_right"),
            [eb.clone(), d2.clone()],
        ),
    );
    // Residual: the normalized goal is `b < (b + d) + b`, and the linear
    // residual of `(b + d) + b` over `b` is `b + d`, so the core term proves
    // `b < b + (b + d)` and is transported along `Nat.add_comm`.
    let r2 = add(subst2.clone(), eb.clone());
    let residual2 = if wrong_residual {
        // CONTROL: name `d` as the residual instead of `b + d`.
        d2.clone()
    } else {
        subst2.clone()
    };
    let hs2 = pos_add_left(eb.clone(), d2.clone(), eh.clone());
    let core2 = lt_add_pos(eb.clone(), residual2.clone(), hs2);
    let commuted = eq_mp(
        lt(eb.clone(), add(eb.clone(), residual2.clone())),
        lt(eb.clone(), r2.clone()),
        congr_arg_prop(
            add(eb.clone(), residual2.clone()),
            r2.clone(),
            nat_lam(hole, lt(eb.clone(), Expr::fvar(hole))),
            Expr::apps(cst("Nat.add_comm"), [eb.clone(), residual2]),
        ),
        core2,
    );
    let branch2_inner = eq_mpr(
        lt(sub(subst2.clone(), inner2.clone()), r2.clone()),
        lt(eb.clone(), r2.clone()),
        congr_arg_prop(
            sub(subst2.clone(), inner2.clone()),
            eb.clone(),
            nat_lam(hole, lt(Expr::fvar(hole), r2.clone())),
            pf_lhs2,
        ),
        commuted,
    );
    let branch2 = Expr::lam(
        BinderInfo::Default,
        le(eb.clone(), ea.clone()),
        eq_mp(
            goal2.clone(),
            goal.clone(),
            congr_arg_prop(subst2, ea.clone(), nat_lam(a, goal.clone()), hd2),
            branch2_inner,
        )
        .abstract_fvar(hba),
    );

    or_rec(
        le(ea.clone(), eb.clone()),
        le(eb.clone(), ea.clone()),
        goal,
        branch1,
        branch2,
        Expr::apps(cst("Nat.le_total"), [ea, eb]),
    )
}

/// Close `body` over `(a b : Nat) (h : 0 < b)`.
fn close_probe(a: FVarId, b: FVarId, h: FVarId, body: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(
                BinderInfo::Default,
                lt(zero(), Expr::fvar(b)),
                body.abstract_fvar(h),
            )
            .abstract_fvar(b),
        )
        .abstract_fvar(a),
    )
}

fn probe_ty(a: FVarId, b: FVarId, h: FVarId, goal: Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                lt(zero(), Expr::fvar(b)),
                goal.abstract_fvar(h),
            )
            .abstract_fvar(b),
        )
        .abstract_fvar(a),
    )
}

/// **THE PROBE.** `min a b < a + b`, spelled `(a - (a - b)) < a + b`, proved by
/// case split on `Nat.le_total`, substitution of the larger parameter,
/// truncation normalization, and the strict residual — every step a named,
/// axiom-free prelude theorem.
#[test]
fn probe_2_truncated_subtraction_case_split_kernel_checks() {
    let mut env = env_with_prelude();
    let (a, b, h) = (FVarId::new(7201), FVarId::new(7202), FVarId::new(7203));
    let goal = probe_split_goal(a, b);
    let value = close_probe(a, b, h, build_probe_split(a, b, h, false));
    add_theorem(&mut env, "probeSplit", probe_ty(a, b, h, goal), value)
        .expect("the case-split skeleton must kernel-check");
}

/// ADVERSARIAL CONTROL: the same skeleton with branch 2's residual replaced by
/// one the goal does not name must be REJECTED.
#[test]
fn probe_2_control_a_wrong_residual_is_rejected() {
    let mut env = env_with_prelude();
    let (a, b, h) = (FVarId::new(7211), FVarId::new(7212), FVarId::new(7213));
    let goal = probe_split_goal(a, b);
    let value = close_probe(a, b, h, build_probe_split(a, b, h, true));
    assert!(
        add_theorem(&mut env, "probeSplitBad", probe_ty(a, b, h, goal), value).is_err(),
        "a wrong residual must be REJECTED"
    );
    assert!(
        env.get_const(&Name::from_string("probeSplitBad")).is_none(),
        "a rejected theorem must register nothing"
    );
}

/// ADVERSARIAL CONTROL: the FALSE sibling `(a - (a - b)) < a` (false at `a = 0`)
/// must be REJECTED even though the skeleton is the same shape.
#[test]
fn probe_2_control_a_false_sibling_is_rejected() {
    let mut env = env_with_prelude();
    let (a, b, h) = (FVarId::new(7221), FVarId::new(7222), FVarId::new(7223));
    let false_goal = lt(
        sub(Expr::fvar(a), sub(Expr::fvar(a), Expr::fvar(b))),
        Expr::fvar(a),
    );
    let value = close_probe(a, b, h, build_probe_split(a, b, h, false));
    assert!(
        add_theorem(
            &mut env,
            "probeSplitFalse",
            probe_ty(a, b, h, false_goal),
            value
        )
        .is_err(),
        "the false sibling `min a b < a` must be REJECTED"
    );
    assert!(
        env.get_const(&Name::from_string("probeSplitFalse"))
            .is_none(),
        "a rejected theorem must register nothing"
    );
}

// ═══════ probe 3: the normalization lemmas, at their exact shapes ═══════

/// Every rewrite the tier will fire, applied at the shape it will see, checked
/// one by one so a signature drift names itself instead of failing deep inside
/// the composite term above.
#[test]
fn probe_3_each_truncation_rewrite_applies_at_its_shape() {
    let mut env = env_with_prelude();
    let (x, y) = (FVarId::new(7301), FVarId::new(7302));
    let (ex, ey) = (Expr::fvar(x), Expr::fvar(y));
    let bind2 = |goal: Expr, value: Expr| {
        (
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(BinderInfo::Default, nat(), goal.abstract_fvar(y)).abstract_fvar(x),
            ),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), value.abstract_fvar(y)).abstract_fvar(x),
            ),
        )
    };
    for (name, goal, value) in [
        (
            "probeAddSubCancelLeft",
            nat_eq(sub(add(ex.clone(), ey.clone()), ex.clone()), ey.clone()),
            Expr::apps(
                cst("Nat.ulpRound.add_sub_cancel_left"),
                [ex.clone(), ey.clone()],
            ),
        ),
        (
            "probeAddSubSelfRight",
            nat_eq(sub(add(ex.clone(), ey.clone()), ey.clone()), ex.clone()),
            Expr::apps(
                cst("Nat.ulpRound.add_sub_self_right"),
                [ex.clone(), ey.clone()],
            ),
        ),
        (
            "probeSubOfLeAdd",
            nat_eq(sub(ex.clone(), add(ex.clone(), ey.clone())), zero()),
            Expr::apps(
                cst("Nat.ulpRound.sub_eq_zero_of_le"),
                [
                    ex.clone(),
                    add(ex.clone(), ey.clone()),
                    Expr::apps(cst("Nat.le_add_right"), [ex.clone(), ey.clone()]),
                ],
            ),
        ),
        (
            "probeSubZero",
            nat_eq(sub(ex.clone(), zero()), ex.clone()),
            Expr::app(cst("Nat.sub_zero"), ex.clone()),
        ),
        (
            "probeZeroAdd",
            nat_eq(add(zero(), ey.clone()), ey.clone()),
            Expr::app(cst("Nat.zero_add"), ey.clone()),
        ),
    ] {
        let (ty, value) = bind2(goal, value);
        add_theorem(&mut env, name, ty, value)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e}"));
    }
}

/// The positivity route the residual tier uses for a SUM residual:
/// `0 < x` gives `0 < x + y` through `Nat.le_trans` and `Nat.le_add_right`.
#[test]
fn probe_3_positivity_of_a_sum_from_its_left_summand() {
    let mut env = env_with_prelude();
    let (x, y, hx) = (FVarId::new(7311), FVarId::new(7312), FVarId::new(7313));
    let (ex, ey) = (Expr::fvar(x), Expr::fvar(y));
    let goal = lt(zero(), add(ex.clone(), ey.clone()));
    let value = pos_add_left(ex.clone(), ey.clone(), Expr::fvar(hx));
    let ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                lt(zero(), ex.clone()),
                goal.abstract_fvar(hx),
            )
            .abstract_fvar(y),
        )
        .abstract_fvar(x),
    );
    let val = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(
                BinderInfo::Default,
                lt(zero(), ex.clone()),
                value.abstract_fvar(hx),
            )
            .abstract_fvar(y),
        )
        .abstract_fvar(x),
    );
    add_theorem(&mut env, "probePosAdd", ty, val).expect("sum positivity must kernel-check");
}
