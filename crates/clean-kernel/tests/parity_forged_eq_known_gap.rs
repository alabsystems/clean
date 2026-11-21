// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! F7 regression for the certified parity shortcut. All four checked entry
//! modes must fall back to ordinary reduction when the equality premise fails.
//! The positive control checks the result on the genuine definitions.
//! See reports/parity-arm-forged-foundation-2026-11-18/README.md.

#[path = "parity_forged_eq_known_gap/support.rs"]
mod support;

use std::collections::HashSet;

use clean_kernel::{
    BinderInfo, ConstantKind, Constructor, Declaration, Environment, Expr, ExprKind, InductiveDecl,
    InductiveType, Level, Name, TypeChecker,
};
use support::{copy_closure, kernels, reconstruction, Sink};

/// An odd literal far above the shortcut's 2^16 threshold. δ cannot decide
/// `Nat.div2Par` here over Clean's own definition, so the genuine control's
/// `1` can only come from the shortcut.
const BIG: u64 = u64::MAX;

/// The lemmas the shortcut's reconstruction cites (`reconstruction()` in
/// `src/tc/reduction/nat_parity.rs`, transcribed in `support.rs`).
const CITED: &[&str] = &[
    "Eq.symm",
    "Eq.trans",
    "congrArg",
    "Nat.add_comm",
    "Nat.add_sub_cancel",
    "Nat.div2_rejoin",
];

fn n(s: &str) -> Name {
    Name::from_string(s)
}
fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}
fn nat() -> Expr {
    c("Nat")
}
fn app(f: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(f), args)
}
fn one() -> Level {
    Level::succ(Level::zero())
}
fn eq_nat(head: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(n(head), vec![one()]), [nat(), a, b])
}
fn refl_nat(head: &str, a: Expr) -> Expr {
    Expr::apps(Expr::const_(n(head), vec![one()]), [nat(), a])
}
fn par(k: u64) -> Expr {
    app("Nat.div2Par", [Expr::nat_lit(k)])
}
fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_,
        value,
    }
}

// ---------------------------------------------------------------------------
// The forged world.
// ---------------------------------------------------------------------------

/// `λ binders… (p : Prop) (h : p), h`, following the Pi telescope of `ty`.
fn mirror_value(ty: &Expr) -> Expr {
    match ty.kind() {
        ExprKind::Pi(binder, dom, body) => Expr::lam(*binder, Expr::clone(dom), mirror_value(body)),
        _ => Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
    }
}

/// `{α : Sort u} → α → α → Prop`, the type of `Eq` and of `MyEq`.
fn relation_type(u: &Name) -> Expr {
    Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::param(u.clone())),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
        ),
    )
}

/// `def Eq.{u} : {α : Sort u} → α → α → Prop := fun _ _ _ => ∀ p : Prop, p → p`
fn forged_eq() -> Declaration {
    let u = n("u");
    let all_props = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let value = Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(Level::param(u.clone())),
        Expr::lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::lam(BinderInfo::Default, Expr::bvar(1), all_props),
        ),
    );
    Declaration::Definition {
        name: n("Eq"),
        level_params: vec![u.clone()],
        type_: relation_type(&u),
        value,
        is_reducible: false,
    }
}

/// `False`, `True` and `MyEq` (Lean's `Eq` under another name), all honest.
fn honest_inductives() -> Vec<InductiveDecl> {
    let u = n("u");
    let refl_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::param(u.clone())),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::apps(
                Expr::const_(n("MyEq"), vec![Level::param(u.clone())]),
                [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)],
            ),
        ),
    );
    let single = |name: &str, level_params, num_params, type_, constructors| InductiveDecl {
        level_params,
        num_params,
        types: vec![InductiveType {
            name: n(name),
            type_,
            constructors,
        }],
    };
    let ctor = |name: &str, type_| Constructor {
        name: n(name),
        type_,
    };
    vec![
        single("False", vec![], 0, Expr::prop(), vec![]),
        single(
            "True",
            vec![],
            0,
            Expr::prop(),
            vec![ctor("True.intro", c("True"))],
        ),
        single(
            "MyEq",
            vec![u.clone()],
            2,
            relation_type(&u),
            vec![ctor("MyEq.refl", refl_type)],
        ),
    ]
}

/// Genuine arithmetic, the forged `Eq`, a forged `Nat.div2Par`, every cited
/// lemma at Clean's own statement proved through the forged `Eq`, and the
/// honest inductives. Each step is admitted in every kernel today.
fn add_forged_world(src: &Environment, dst: &mut dyn Sink) {
    copy_closure(
        src,
        dst,
        &["Nat", "Nat.shiftRight", "Nat.add", "Nat.sub", "Nat.div2"],
    );
    let mut decls = vec![
        forged_eq(),
        Declaration::Definition {
            name: n("Nat.div2Par"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, nat(), nat()),
            value: Expr::lam(BinderInfo::Default, nat(), Expr::nat_lit(0)),
            is_reducible: false,
        },
    ];
    // Each cited lemma (and `Eq.refl`) keeps Clean's own statement, proved
    // through the forged `Eq`.
    for name in std::iter::once(&"Eq.refl").chain(CITED) {
        let info = src.get_const(&n(name)).expect("with_prelude has it");
        decls.push(Declaration::Theorem {
            name: n(name),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: mirror_value(&info.type_),
        });
    }
    for decl in decls {
        let name = match &decl {
            Declaration::Definition { name, .. }
            | Declaration::Axiom { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. } => name.clone(),
        };
        dst.add(decl)
            .unwrap_or_else(|e| panic!("the forged world's {name} was refused: {e}"));
    }
    for ind in honest_inductives() {
        let name = ind.types[0].name.clone();
        dst.add_ind(ind)
            .unwrap_or_else(|e| panic!("honest inductive {name} was refused: {e}"));
    }
}

/// What a kernel decides in the forged world.
#[derive(Debug, PartialEq, Eq)]
struct Verdicts {
    /// `whnf (Nat.div2Par BIG)`; δ over the forged definition gives `0`.
    whnf: Expr,
    /// `h1 : MyEq (Nat.div2Par BIG) 1 := MyEq.refl 1`, false by δ.
    h1: bool,
    /// `d0 : MyEq (Nat.div2Par BIG) 0 := MyEq.refl 0`, true by δ.
    d0: bool,
    /// `t : ∀ n, MyEq (Nat.div2Par n) 0 := fun n => MyEq.refl 0`, true by δ.
    t: bool,
    /// `bad : MyEq (1 : Nat) 0 := t BIG`.
    bad: bool,
    /// `boom : False := MyEq.rec (motive := fun k _ => Nat.rec False (fun _ _ => True) k) True.intro (t BIG)`,
    /// judged on its own rather than through `bad`.
    boom: bool,
    /// Axiom-kind constants reachable from the reconstruction's goal and proof
    /// and, when it was admitted, from `boom`.
    axioms: Vec<String>,
}

fn decide(dst: &mut dyn Sink) -> Verdicts {
    let lit = Expr::nat_lit;
    let whnf = TypeChecker::new(dst.env()).whnf(&par(BIG));
    let my_eq = |a, b| eq_nat("MyEq", a, b);
    let my_refl = |a| refl_nat("MyEq.refl", a);
    // MyEq.rec's levels: the motive's universe is 0, the inductive's `u` is 1.
    let rec = dst.env().get_recursor(&n("MyEq.rec")).expect("MyEq.rec");
    let rec_levels: Vec<Level> = rec
        .level_params
        .iter()
        .map(|p| if *p == n("u") { one() } else { Level::zero() })
        .collect();
    let nat_case = Expr::apps(
        Expr::const_(n("Nat.rec"), vec![one()]),
        [
            Expr::lam(BinderInfo::Default, nat(), Expr::prop()),
            c("False"),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, Expr::prop(), c("True")),
            ),
            Expr::bvar(1),
        ],
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, my_eq(lit(1), Expr::bvar(0)), nat_case),
    );
    let t_big = Expr::app(c("Probe.t"), lit(BIG));
    let boom = Expr::apps(
        Expr::const_(n("MyEq.rec"), rec_levels),
        [
            nat(),
            lit(1),
            motive,
            c("True.intro"),
            lit(0),
            t_big.clone(),
        ],
    );
    let t_type = Expr::pi(
        BinderInfo::Default,
        nat(),
        my_eq(app("Nat.div2Par", [Expr::bvar(0)]), lit(0)),
    );
    let t_value = Expr::lam(BinderInfo::Default, nat(), my_refl(lit(0)));
    let mut admit = |d| dst.add(d).is_ok();
    let h1 = admit(theorem(
        "Probe.h1",
        my_eq(par(BIG), lit(1)),
        my_refl(lit(1)),
    ));
    let d0 = admit(theorem(
        "Probe.d0",
        my_eq(par(BIG), lit(0)),
        my_refl(lit(0)),
    ));
    let t = admit(theorem("Probe.t", t_type, t_value));
    let bad = admit(theorem("Probe.bad", my_eq(lit(1), lit(0)), t_big));
    let boom = admit(theorem("Probe.boom", c("False"), boom));
    let (goal, proof) = reconstruction();
    let mut roots = goal.collect_constants();
    roots.extend(proof.collect_constants());
    roots.insert(n("Probe.boom"));
    let axioms = axioms_reachable(dst.env(), roots);
    Verdicts {
        whnf,
        h1,
        d0,
        t,
        bad,
        boom,
        axioms,
    }
}

/// Every axiom-kind constant reachable from `roots` through types and values;
/// a root the environment lacks contributes nothing.
fn axioms_reachable(env: &Environment, roots: HashSet<Name>) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut stack: Vec<Name> = roots.into_iter().collect();
    let mut axioms = Vec::new();
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.kind == ConstantKind::Axiom {
            axioms.push(name.to_string());
        }
        stack.extend(info.type_.collect_constants());
        if let Some(value) = &info.value {
            stack.extend(value.collect_constants());
        }
    }
    axioms.sort();
    axioms
}

/// Keep the fixture sensitive to equality provenance independently of the
/// reconstruction's ordinary axiom audit.
fn forgery_is_adequate(label: &str, env: &Environment) {
    let (goal, proof) = reconstruction();
    let audit = env.audit_certification(&goal, &proof);
    assert!(
        audit.is_certified() && audit.foundations.is_empty(),
        "{label}: the forged world no longer certifies the reconstruction; \
         re-forge what it cites (see `CITED`): {audit:?}"
    );
}

fn expected_fallback() -> Verdicts {
    Verdicts {
        whnf: Expr::nat_lit(0),
        h1: false,
        d0: true,
        t: true,
        bad: false,
        boom: false,
        axioms: Vec::new(),
    }
}

fn on_big_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(body)
        .expect("spawn")
        .join()
        .expect("test thread");
}

#[test]
fn test_parity_shortcut_requires_the_equality_premise_in_every_kernel() {
    on_big_stack(|| {
        let src = Environment::with_prelude();
        for (label, mut dst) in kernels() {
            add_forged_world(&src, dst.as_mut());
            forgery_is_adequate(&label, dst.env());
            assert_eq!(
                decide(dst.as_mut()),
                expected_fallback(),
                "{label}: the kernel must fall back to the admitted definition"
            );
        }
    });
}

/// Control: over Clean's own `Nat.div2Par` and `Eq`, the shortcut's answer is
/// the true one in every kernel, and the false one is refused.
#[test]
fn test_parity_shortcut_over_genuine_definitions_decides_truly_in_every_kernel() {
    on_big_stack(|| {
        let src = Environment::with_prelude();
        let mut roots = vec![
            "Nat",
            "Eq",
            "Nat.shiftRight",
            "Nat.add",
            "Nat.sub",
            "Nat.div2",
            "Nat.div2Par",
        ];
        roots.extend(CITED);
        for (label, mut dst) in kernels() {
            copy_closure(&src, dst.as_mut(), &roots);
            let whnf = TypeChecker::new(dst.env()).whnf(&par(BIG));
            assert_eq!(whnf, Expr::nat_lit(1), "{label}");
            let one_ok = dst.add(theorem(
                "Probe.par1",
                eq_nat("Eq", par(BIG), Expr::nat_lit(1)),
                refl_nat("Eq.refl", Expr::nat_lit(1)),
            ));
            one_ok.unwrap_or_else(|e| panic!("{label}: the true parity was refused: {e}"));
            let zero = dst.add(theorem(
                "Probe.par0",
                eq_nat("Eq", par(BIG), Expr::nat_lit(0)),
                refl_nat("Eq.refl", Expr::nat_lit(0)),
            ));
            assert!(zero.is_err(), "{label}: the false parity was admitted");
        }
    });
}
