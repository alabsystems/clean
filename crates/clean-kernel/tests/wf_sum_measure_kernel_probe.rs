// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **KERNEL PROBE — can the kernel already express a SUM termination measure?**
//!
//! The elaborator's well-founded lowering refuses a `termination_by` measure
//! that mentions more than one parameter ("lexicographic / packed"). Before
//! widening it, this file answers the prior question by hand: is the refusal a
//! KERNEL limit, or only an elaborator limit?
//!
//! The claim under test is that it is only an elaborator limit, because a
//! multi-parameter measure `m : (a b : Nat) → Nat` still induces a
//! **one-parameter** well-founded relation — on `Nat`, the measure's VALUE —
//! provided the parameters are carried in the MOTIVE and related to the
//! recursion variable by a hypothesis. That is the course-of-values encoding:
//!
//! ```text
//! α    := Nat                                     -- the measure's value
//! rel  := Nat.lt
//! hwf  := @WellFounded.intro Nat Nat.lt Nat.accNatLt
//! C    := fun (n : Nat) => (a b : Nat) → Nat.lt (a + b) n → Nat
//! F    := fun n rec a b (hm : Nat.lt (a + b) n) => …
//!             rec (a + b) hm a' b' (prf : Nat.lt (a' + b') (a + b)) …
//! f    := fun a b => @WellFounded.fix Nat C Nat.lt hwf F
//!             (Nat.succ (a + b)) a b (Nat.le.refl (Nat.succ (a + b)))
//! ```
//!
//! Two things make this work without `PSigma`, `Prod`, `invImage`, or any
//! `Eq`-rewriting:
//!
//! * `rec`'s major premise is `a + b` — the measure at the CURRENT parameters —
//!   and `hm` is exactly the proof `Nat.lt (a + b) n` it needs. So the
//!   per-call-site obligation that remains is `Nat.lt (m a' b') (m a b)`: the
//!   same shape the one-parameter lowering already discharges, with a
//!   multi-parameter `m`.
//! * The seed `Nat.lt (a + b) (Nat.succ (a + b))` is `Nat.le.refl` up to δ —
//!   the identity `measure_wf.rs` already relies on.
//!
//! NOTHING HERE IS ASSUMED. The decreasing proof is a real term built from the
//! constructive prelude theorems `Nat.sub_lt` and `Nat.add_lt_add_left`; the
//! kernel re-checks the whole definition at `add_decl`; and the adversarial
//! control below hands the kernel the SAME term with the decreasing proof
//! swapped for the wrong-typed hypothesis and requires a rejection.
//!
//! The probe function is
//!
//! ```text
//! probeSum a b = if 0 < b then Nat.succ (probeSum a (b-1)) else a   -- = a + b
//! ```
//!
//! **What this fixture does and does not show.** Its measure is `a + b`, which
//! mentions BOTH parameters — the class the elaborator refused — and the
//! decrease it owes is the genuine `Nat.lt (a + (b-1)) (a + b)`, discharged by
//! `Nat.add_lt_add_left` over `Nat.sub_lt`. It deliberately does NOT try to
//! be the hardest case: `a` is carried unchanged, so a hand-built decreasing
//! proof stays readable. The harder class — different branches shrinking
//! different parameters, which is subtractive Euclid — is exercised at the
//! elaborator level in `clean-elab/tests/wf_sum_measure_e2e.rs`, where the
//! discharge cascade builds the proofs instead of a human.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, Level};

/// Constants this hand-built encoding names. Checked up front so a missing
/// prelude piece fails with its own name rather than as a kernel error deep
/// inside a term.
const REQUIRED: &[&str] = &[
    "Nat",
    "Nat.lt",
    "Nat.le.refl",
    "Nat.succ",
    "Nat.zero",
    "Nat.add",
    "Nat.sub",
    "Nat.sub_lt",
    "Nat.zero_lt_succ",
    "Nat.add_lt_add_left",
    "Nat.accNatLt",
    "Nat.decLt",
    "Not",
    "dite",
    "WellFounded",
    "WellFounded.intro",
    "WellFounded.fix",
];

/// A monotone source of free variables. The kernel never allocates these for
/// us outside the elaborator, and `abstract_fvar` only needs them to be
/// distinct.
struct Fresh(u64);

impl Fresh {
    fn next(&mut self) -> FVarId {
        self.0 += 1;
        FVarId::new(self.0)
    }
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn c_at(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

fn nat() -> Expr {
    c("Nat")
}

fn add(x: Expr, y: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [x, y])
}

fn lt(x: Expr, y: Expr) -> Expr {
    Expr::apps(c("Nat.lt"), [x, y])
}

/// Whether the decreasing proof handed to `rec` is the real one or the
/// adversarial substitute. Both build the SAME term otherwise, so the control
/// isolates exactly the proof obligation.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Decrease {
    /// `Nat.add_lt_add_left (b-1) b (Nat.sub_lt b 1 h _) a`.
    Proved,
    /// `hm` — well-typed in the context, but a proof of the WRONG proposition
    /// (`Nat.lt (a+b) n`, not `Nat.lt (a + (b-1)) (a+b)`).
    Bogus,
}

/// Build `(type, value)` for `probeSum` in the course-of-values encoding.
fn build_probe_sum(decrease: Decrease) -> (Expr, Expr) {
    let mut f = Fresh(0);
    let l1 = Level::succ(Level::zero());
    let nat_lt = c("Nat.lt");
    let succ = c("Nat.succ");
    let zero = c("Nat.zero");
    let one = Expr::app(succ.clone(), zero.clone());

    // type: Nat → Nat → Nat
    let type_ = Expr::arrow(nat(), Expr::arrow(nat(), nat()));

    // C := fun (n : Nat) => (a b : Nat) → Nat.lt (Nat.add a b) n → Nat
    let (n_c, a_c, b_c) = (f.next(), f.next(), f.next());
    let motive = {
        let inner = Expr::arrow(
            lt(add(Expr::fvar(a_c), Expr::fvar(b_c)), Expr::fvar(n_c)),
            nat(),
        );
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(b_c));
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(a_c));
        Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(n_c))
    };

    // hwf := @WellFounded.intro.{1} Nat Nat.lt Nat.accNatLt
    let hwf = Expr::apps(
        c_at("WellFounded.intro", vec![l1.clone()]),
        [nat(), nat_lt.clone(), c("Nat.accNatLt")],
    );

    // F := fun (n : Nat) (rec : (k : Nat) → Nat.lt k n → C k)
    //          (a b : Nat) (hm : Nat.lt (Nat.add a b) n) =>
    //        dite (Nat.lt Nat.zero b) (Nat.decLt Nat.zero b)
    //          (fun h => rec (Nat.add a b) hm (Nat.succ a) (Nat.sub b 1) prf)
    //          (fun _ => a)
    let n = f.next();
    let rec_ty = {
        let k = f.next();
        let inner = Expr::arrow(
            lt(Expr::fvar(k), Expr::fvar(n)),
            Expr::app(motive.clone(), Expr::fvar(k)),
        );
        Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(k))
    };
    let rec = f.next();
    let (a, b, hm) = (f.next(), f.next(), f.next());
    let hm_ty = lt(add(Expr::fvar(a), Expr::fvar(b)), Expr::fvar(n));
    let cond = lt(zero.clone(), Expr::fvar(b));
    let b_minus_1 = Expr::apps(c("Nat.sub"), [Expr::fvar(b), one.clone()]);

    let h = f.next();
    // Nat.sub_lt b 1 h (Nat.zero_lt_succ Nat.zero) : Nat.lt (Nat.sub b 1) b
    let sub_lt = Expr::apps(
        c("Nat.sub_lt"),
        [
            Expr::fvar(b),
            one.clone(),
            Expr::fvar(h),
            Expr::app(c("Nat.zero_lt_succ"), zero.clone()),
        ],
    );
    // `Nat.add_lt_add_left : ∀ a b, Nat.lt a b → ∀ c, Nat.lt (c+a) (c+b)`
    // — a constructive, axiom-free prelude `Theorem` — instantiated at
    // `(b-1) b sub_lt a` gives exactly the obligation the call site owes:
    //
    //     Nat.lt (Nat.add a (Nat.sub b 1)) (Nat.add a b)
    //
    // i.e. the SUM decreases although neither summand is inspected by the
    // relation. This is the term the elaborator's cascade must reproduce.
    let proved = Expr::apps(
        c("Nat.add_lt_add_left"),
        [b_minus_1.clone(), Expr::fvar(b), sub_lt, Expr::fvar(a)],
    );
    let decrease_proof = match decrease {
        Decrease::Proved => proved,
        Decrease::Bogus => Expr::fvar(hm),
    };

    // rec (Nat.add a b) hm a (Nat.sub b 1) prf : Nat
    let call = Expr::apps(
        Expr::fvar(rec),
        [
            add(Expr::fvar(a), Expr::fvar(b)),
            Expr::fvar(hm),
            Expr::fvar(a),
            b_minus_1.clone(),
            decrease_proof,
        ],
    );
    // The function computes `a + b`: each step drops one from `b` and adds one
    // to the RESULT (not to `a`), which keeps the measure's left summand fixed
    // so the decrease is `Nat.add_lt_add_left` on the nose.
    let then_body = Expr::app(succ.clone(), call);
    let then_lam = Expr::lam(
        BinderInfo::Default,
        cond.clone(),
        then_body.abstract_fvar(h),
    );

    let h_neg = f.next();
    let else_lam = Expr::lam(
        BinderInfo::Default,
        Expr::app(c("Not"), cond.clone()),
        Expr::fvar(a).abstract_fvar(h_neg),
    );

    let dite_app = Expr::apps(
        c_at("dite", vec![l1.clone()]),
        [
            nat(),
            cond.clone(),
            Expr::apps(c("Nat.decLt"), [zero.clone(), Expr::fvar(b)]),
            then_lam,
            else_lam,
        ],
    );

    let fix_body = {
        let t = Expr::lam(BinderInfo::Default, hm_ty, dite_app.abstract_fvar(hm));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(b));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(a));
        let t = Expr::lam(BinderInfo::Default, rec_ty, t.abstract_fvar(rec));
        Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(n))
    };

    // value := fun a b => @WellFounded.fix.{1,1} Nat C Nat.lt hwf F
    //            (Nat.succ (a+b)) a b (Nat.le.refl (Nat.succ (a+b)))
    let (a_o, b_o) = (f.next(), f.next());
    let m_o = add(Expr::fvar(a_o), Expr::fvar(b_o));
    let succ_m = Expr::app(succ.clone(), m_o);
    let fix = Expr::apps(
        c_at("WellFounded.fix", vec![l1.clone(), l1]),
        [nat(), motive, nat_lt, hwf, fix_body, succ_m.clone()],
    );
    let applied = Expr::apps(
        fix,
        [
            Expr::fvar(a_o),
            Expr::fvar(b_o),
            Expr::app(c("Nat.le.refl"), succ_m),
        ],
    );
    let value = {
        let t = Expr::lam(BinderInfo::Default, nat(), applied.abstract_fvar(b_o));
        Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(a_o))
    };

    (type_, value)
}

fn env_with_required() -> Environment {
    let env = Environment::with_prelude();
    let missing: Vec<&str> = REQUIRED
        .iter()
        .copied()
        .filter(|name| env.get_const(&Name::from_string(name)).is_none())
        .collect();
    assert!(
        missing.is_empty(),
        "the builtin prelude must provide the course-of-values foundation; missing {missing:?}"
    );
    env
}

fn register_probe(env: &mut Environment, name: &str, decrease: Decrease) -> Result<(), String> {
    let (type_, value) = build_probe_sum(decrease);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .map_err(|e| format!("{e:?}"))
}

/// **THE PROBE.** A two-parameter SUM measure lowered through `WellFounded.fix`
/// is a term the kernel accepts.
#[test]
fn test_kernel_accepts_a_sum_measure_course_of_values_fix() {
    let mut env = env_with_required();
    register_probe(&mut env, "probeSum", Decrease::Proved)
        .expect("the kernel must accept the course-of-values encoding of a SUM measure");

    let value = env
        .get_const(&Name::from_string("probeSum"))
        .and_then(|k| k.value.clone())
        .expect("probeSum keeps its value");
    assert!(!value.has_sorry(), "probeSum must be sorry-free");
}

/// **THE CONTROL.** The same term with the decreasing proof replaced by a
/// well-typed proof of the WRONG proposition must be REJECTED. Without this,
/// the acceptance above would be evidence that the kernel checks nothing.
#[test]
fn test_kernel_rejects_the_same_shape_with_a_bogus_decrease() {
    let mut env = env_with_required();
    let err = register_probe(&mut env, "probeSumBogus", Decrease::Bogus)
        .expect_err("a wrong-typed decreasing proof must be refused by the kernel");
    assert!(
        env.get_const(&Name::from_string("probeSumBogus")).is_none(),
        "a refused declaration must register nothing (error was: {err})"
    );
}

/// **IT COMPUTES.** `probeSum a b = a + b`, so `probeSum 12 18` must reduce to
/// `30` — the `WellFounded.fix` application has to grind all the way through
/// `Acc.rec` and `Nat.accNatLt`, which is the claim a typing check alone does
/// not make.
#[test]
fn test_the_sum_measure_fix_actually_computes() {
    let mut env = env_with_required();
    register_probe(&mut env, "probeSum", Decrease::Proved).expect("probeSum registers");

    let l1 = Level::succ(Level::zero());
    let eq_at = |lhs: Expr, rhs: Expr| Expr::apps(c_at("Eq", vec![l1.clone()]), [nat(), lhs, rhs]);
    let probe = c("probeSum");
    let app = Expr::apps(probe, [Expr::nat_lit(12), Expr::nat_lit(18)]);

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("probeSum_12_18"),
        level_params: vec![],
        type_: eq_at(app.clone(), Expr::nat_lit(30)),
        value: Expr::apps(
            c_at("Eq.refl", vec![l1.clone()]),
            [nat(), Expr::nat_lit(30)],
        ),
    })
    .expect("probeSum 12 18 must COMPUTE to 30 by kernel reduction");

    // MUTATION CONTROL at the same layer: the computation is a decision.
    let wrong = env.add_decl(Declaration::Theorem {
        name: Name::from_string("probeSum_12_18_bad"),
        level_params: vec![],
        type_: eq_at(app, Expr::nat_lit(29)),
        value: Expr::apps(c_at("Eq.refl", vec![l1]), [nat(), Expr::nat_lit(29)]),
    });
    assert!(
        wrong.is_err(),
        "`probeSum 12 18 = 29` must be refused — otherwise the computation \
         evidence above is vacuous"
    );
}

/// The encoding admits no axioms of its own: the transitive closure is
/// foundational-only.
#[test]
fn test_the_sum_measure_encoding_has_a_foundational_only_axiom_closure() {
    let mut env = env_with_required();
    register_probe(&mut env, "probeSum", Decrease::Proved).expect("probeSum registers");

    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let closure = env
        .axiom_deps(&Name::from_string("probeSum"))
        .expect("probeSum has an axiom closure");
    let offending: Vec<String> = closure
        .iter()
        .map(ToString::to_string)
        .filter(|ax| !foundational.contains(&ax.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "the course-of-values sum-measure encoding must not admit an axiom, got {offending:?}"
    );
}
