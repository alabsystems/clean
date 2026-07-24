// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for kernel-level `Fin.sum` registration and linearity lemmas.
//!
//! Part of #3219.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_fin_sum().expect("init_fin_sum");
    env
}

#[test]
fn test_fin_sum_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum")).is_some());
}

#[test]
fn test_fin_sum_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum_zero")).is_some());
}

#[test]
fn test_fin_sum_succ_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum_succ")).is_some());
}

#[test]
fn test_fin_sum_le_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum_le")).is_some());
}

#[test]
fn test_fin_sum_add_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum_add")).is_some());
}

#[test]
fn test_fin_cast_succ_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.castSucc")).is_some());
}

#[test]
fn test_fin_last_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.last")).is_some());
}

#[test]
fn test_fin_sum_nonneg_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("Fin.sum_nonneg"))
        .is_some());
}

#[test]
fn test_fin_sum_smul_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum_smul")).is_some());
}

#[test]
fn test_fin_sum_type_checks() {
    let env = make_env();
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&fin_sum).expect("infer Fin.sum type");
    // Fin.sum : (n : Nat) -> (Fin n -> Rat) -> Rat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_le_type_checks() {
    let env = make_env();
    let fin_sum_le = Expr::const_(Name::from_string("Fin.sum_le"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&fin_sum_le).expect("infer Fin.sum_le type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_add_type_checks() {
    let env = make_env();
    let fin_sum_add = Expr::const_(Name::from_string("Fin.sum_add"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&fin_sum_add).expect("infer Fin.sum_add type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_nonneg_type_checks() {
    let env = make_env();
    let fin_sum_nonneg = Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fin_sum_nonneg)
        .expect("infer Fin.sum_nonneg type");
    // Fin.sum_nonneg : (n : Nat) -> (f : Fin n -> Rat) -> ... -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_smul_type_checks() {
    let env = make_env();
    let fin_sum_smul = Expr::const_(Name::from_string("Fin.sum_smul"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fin_sum_smul)
        .expect("infer Fin.sum_smul type");
    // Fin.sum_smul : (n : Nat) -> (c : Rat) -> (f : Fin n -> Rat) -> ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_sub_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Fin.sum_sub")).is_some());
}

#[test]
fn test_fin_sum_sub_type_checks() {
    let env = make_env();
    let fin_sum_sub = Expr::const_(Name::from_string("Fin.sum_sub"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&fin_sum_sub).expect("infer Fin.sum_sub type");
    // Fin.sum_sub : (n : Nat) -> (f : Fin n -> Rat) -> (g : Fin n -> Rat) -> ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_zero_fn_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("Fin.sum_zero_fn"))
        .is_some());
}

#[test]
fn test_fin_sum_zero_fn_type_checks() {
    let env = make_env();
    let fin_sum_zero_fn = Expr::const_(Name::from_string("Fin.sum_zero_fn"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fin_sum_zero_fn)
        .expect("infer Fin.sum_zero_fn type");
    // Fin.sum_zero_fn : (n : Nat) -> Eq ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_fin_sum_single_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("Fin.sum_single"))
        .is_some());
}

#[test]
fn test_fin_sum_single_type_checks() {
    let env = make_env();
    let fin_sum_single = Expr::const_(Name::from_string("Fin.sum_single"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fin_sum_single)
        .expect("infer Fin.sum_single type");
    // Fin.sum_single : (n : Nat) -> (i : Fin n) -> (x : Rat) -> ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_fin_sum().expect("first init");
    env.init_fin_sum().expect("second init");
}

/// **Faithful-carrier discriminator (base case):** `Fin.sum 0 f` whnf-reduces
/// to `Rat.zero` via one Nat.rec iota step on the zero branch.
///
/// Acceptance criterion #2 from `designs/2026-04-20-fin-sum-faithful-carrier.md`
/// (as adapted to the n=0 case): the reduction actually fires and is not a
/// placeholder collapse. Under the old `fun _ _ => Rat.zero` carrier, the
/// same whnf would also return `Rat.zero` — but for the wrong reason (beta
/// on a constant lambda). This test is specifically designed so that the
/// ι-step on `Nat.rec` at `Nat.zero` must fire.
///
/// Part of #3546.
#[test]
fn test_fin_sum_faithful_carrier_base_reduces_to_zero() {
    let env = make_env();
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);

    // Register a symbolic f : Fin 0 -> Rat so whnf has a real (not stuck) arg.
    // We cannot easily construct an inhabitant of Fin 0 -> Rat, but whnf
    // on `Fin.sum 0 f` should not need to evaluate f — the Nat.rec ι-step
    // picks the zero-case lambda and beta-reduces to Rat.zero.
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_zero = Expr::app(fin, nat_zero.clone());
    let f_type = Expr::pi(crate::expr::BinderInfo::Default, fin_zero, rat);
    let mut env_mut = env;
    let f_name = Name::from_string("__test_faithful_carrier_f0");
    env_mut
        .add_decl(crate::env::Declaration::Axiom {
            name: f_name.clone(),
            level_params: vec![],
            type_: f_type,
        })
        .expect("register test f");

    let tc = TypeChecker::with_mode(&env_mut, env_mut.mode());
    let f = Expr::const_(f_name, vec![]);
    let app = Expr::app(Expr::app(fin_sum, nat_zero), f);

    let result = tc.whnf(&app);

    // With the faithful Nat.rec.{1} carrier, whnf reduces `Fin.sum 0 f` to
    // `Rat.zero` (which may further unfold to `Rat.mk Int.zero 1` under full
    // reducible-definition unfolding). Either way, the reduction fired and
    // the result is definitionally equal to `Rat.zero`. The meaningful
    // discriminator is the step case (next test).
    assert!(
        tc.is_def_eq(&result, &rat_zero),
        "Fin.sum 0 f should be def-eq to Rat.zero. Got: {result:?}"
    );
}

/// **Faithful-carrier discriminator (step case):** `Fin.sum (Nat.succ 0) f`
/// whnf-reduces to a term that is **definitionally different from `Rat.zero`**,
/// proving the carrier is not the old `fun _ _ => Rat.zero` placeholder.
///
/// Under the old placeholder, `Fin.sum (succ 0) f` whnf-reduced to `Rat.zero`
/// (trivial beta). Under the faithful `Nat.rec` carrier it reduces to
/// `Rat.add (Fin.sum 0 (f ∘ Fin.castSucc 0)) (f (Fin.last 0))`, which is
/// `Rat.add (...) (f (Fin.last 0))` — a non-trivial term that mentions
/// `Rat.add`, `f`, and `Fin.last`.
///
/// This test is the definitive discriminator: a placeholder carrier fails it.
/// Part of #3546.
#[test]
fn test_fin_sum_faithful_carrier_succ_reduces_non_trivially() {
    let env = make_env();
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(nat_succ, nat_zero);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);

    // Register a symbolic f : Fin (succ 0) -> Rat
    let fin_succ_zero = Expr::app(fin, succ_zero.clone());
    let f_type = Expr::pi(crate::expr::BinderInfo::Default, fin_succ_zero, rat);
    let mut env_mut = env;
    let f_name = Name::from_string("__test_faithful_carrier_f1");
    env_mut
        .add_decl(crate::env::Declaration::Axiom {
            name: f_name.clone(),
            level_params: vec![],
            type_: f_type,
        })
        .expect("register test f");

    let tc = TypeChecker::with_mode(&env_mut, env_mut.mode());
    let f = Expr::const_(f_name, vec![]);
    let app = Expr::app(Expr::app(fin_sum, succ_zero), f);

    let result = tc.whnf(&app);

    // Core discriminator: the result must NOT be Rat.zero. If it is,
    // either the carrier is still a placeholder or the ι-step didn't fire.
    assert_ne!(
        result, rat_zero,
        "#3546 faithful-carrier discriminator FAILED: Fin.sum 1 f whnf'd to \
         Rat.zero, indicating the carrier is still the `fun _ _ => Rat.zero` \
         placeholder. Expected a Rat.add application that mentions f. \
         Got: {result:?}"
    );

    // Soft check: the result should be an `App` (the Rat.add at the top).
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "Fin.sum (succ 0) f whnf should produce an App (Rat.add application). \
         Got: {result:?}"
    );
}

/// **Proof quality discriminator (#integrity-audit):** `Fin.sum_zero` is
/// honestly `ProofQuality::AxiomDependent`, NOT `Constructive`.
///
/// `Fin.sum_zero`'s type names `Fin.sum`, whose carrier definition references
/// `Fin.castSucc` and `Fin.last`. Those two were historically whitelisted as
/// "foundational" so that this theorem's transitive closure looked empty and
/// the theorem was reported `Constructive`. The 2026-06 integrity audit
/// reclassified `Fin.castSucc` / `Fin.last` (and the Rat ordered-field /
/// lattice + Nat bitwise facts) as ADMITTED DOMAIN axioms — mathematically
/// true but unproved in THIS kernel — by adding them to
/// `ADMITTED_DOMAIN_AXIOMS` and excluding them from `is_foundational_axiom`.
///
/// The honest state: the transitive axiom closure is NON-EMPTY but contains
/// ONLY admitted domain axioms (no `sorry`, no rogue/unexpected axiom), so the
/// theorem is `AxiomDependent` on admitted domain assumptions. This is the
/// truthful classification; reporting it `Constructive` was the overstatement
/// the audit removed.
///
/// Part of #3546; reclassified by the 2026-06 integrity audit.
#[test]
fn test_fin_sum_zero_is_constructive_after_fin_axiom_elimination() {
    // #3470: `Fin.castSucc` / `Fin.last` were ELIMINATED to computable
    // `Declaration::Definition`s (no longer admitted axioms), so `Fin.sum_zero`'s
    // transitive axiom closure is now EMPTY — it is genuinely `Constructive`, not
    // `AxiomDependent`. Real progress: the elimination removed the admitted-axiom
    // dependency this test previously (honestly) pinned.
    let env = make_env();
    let name = Name::from_string("Fin.sum_zero");

    let deps = env
        .axiom_deps(&name)
        .expect("Fin.sum_zero not found in environment");
    assert!(
        deps.is_empty(),
        "Fin.sum_zero closure must be EMPTY after the Fin.castSucc/Fin.last \
         elimination (#3470); got {deps:?}"
    );
    assert!(
        matches!(
            env.proof_quality(&name),
            Some(crate::env::ProofQuality::Constructive)
        ),
        "Fin.sum_zero must be Constructive now that Fin.castSucc/Fin.last are \
         Definitions, got {:?}",
        env.proof_quality(&name)
    );
}

/// **Proof quality discriminator (#integrity-audit):** `Fin.sum_succ` is
/// honestly `ProofQuality::AxiomDependent`, NOT `Constructive`.
///
/// `Fin.sum_succ`'s type directly names `Fin.castSucc` and `Fin.last` (the
/// step-case equation `Fin.sum (n+1) f = Rat.add (Fin.sum n (f ∘ castSucc))
/// (f (Fin.last n))`). Those were reclassified from foundational to ADMITTED
/// DOMAIN axioms by the 2026-06 integrity audit, so this theorem's transitive
/// closure honestly reaches them and it is `AxiomDependent`, not `Constructive`.
///
/// The honest state: closure is NON-EMPTY but contains ONLY admitted domain
/// axioms (no `sorry`, no rogue/unexpected axiom). Part of #3546; reclassified
/// by the 2026-06 integrity audit.
#[test]
fn test_fin_sum_succ_is_constructive_after_fin_axiom_elimination() {
    // #3470: `Fin.sum_succ`'s step-case type names `Fin.castSucc` / `Fin.last`,
    // which were ELIMINATED to computable `Declaration::Definition`s. They no
    // longer appear in the transitive axiom closure (axiom_deps walks into a
    // Definition's value, which uses only Fin.mk/Fin.val/Fin.rec — no axioms),
    // so `Fin.sum_succ` is now genuinely `Constructive`, not `AxiomDependent`.
    let env = make_env();
    let name = Name::from_string("Fin.sum_succ");

    let deps = env
        .axiom_deps(&name)
        .expect("Fin.sum_succ not found in environment");
    assert!(
        deps.is_empty(),
        "Fin.sum_succ closure must be EMPTY after the Fin.castSucc/Fin.last \
         elimination (#3470); got {deps:?}"
    );
    assert!(
        matches!(
            env.proof_quality(&name),
            Some(crate::env::ProofQuality::Constructive)
        ),
        "Fin.sum_succ must be Constructive now that Fin.castSucc/Fin.last are \
         Definitions, got {:?}",
        env.proof_quality(&name)
    );
}

#[test]
fn zzz_probe_lemma_kinds() {
    let mut env = Environment::with_prelude();
    env.init_fin_sum().expect("init_fin_sum");
    env.init_nat_totality_proofs().expect("totality");
    env.register_nat_lt_irrefl_theorem().expect("lt_irrefl");
    for name in [
        "Nat.lt_or_eq_of_le",
        "Nat.le_of_succ_le_succ",
        "Nat.lt_irrefl",
        "Nat.lt_of_le_of_ne",
        "Nat.decEq",
        "Nat.lt",
        "Nat.le",
        "Nat.le.refl",
        "Nat.le.step",
        "Fin.eq_of_val_eq",
        "Fin.isLt",
        "Fin.val",
        "Fin.castSucc",
        "Fin.last",
        "Or",
        "Or.rec",
        "Or.inl",
        "Or.inr",
        "Eq.ndrec",
        "Eq.mpr",
        "absurd",
        "False.elim",
        "Nat.succ.injEq",
        "congrArg",
    ] {
        let n = Name::from_string(name);
        let info = env.get_const(&n);
        match info {
            None => println!("PROBE {name}: ABSENT"),
            Some(c) => {
                let deps = env.axiom_deps(&n).map(|d| {
                    let mut v: Vec<String> = d.iter().map(|x| x.to_string()).collect();
                    v.sort();
                    v
                });
                println!("PROBE {name}: kind={:?} deps={:?}", c.kind, deps);
            }
        }
    }
}

#[test]
fn zzz_probe_lemma_types() {
    let mut env = Environment::with_prelude();
    env.init_fin_sum().expect("init_fin_sum");
    env.init_nat_totality_proofs().expect("totality");
    for name in [
        "Nat.lt_or_eq_of_le",
        "Nat.le_of_succ_le_succ",
        "Or.rec",
        "absurd",
        "Nat.lt_irrefl",
        "Nat.lt",
        "Fin.last",
        "Fin.castSucc",
        "Eq.ndrec",
        "Eq.refl",
        "Eq.symm",
    ] {
        let n = Name::from_string(name);
        if let Some(c) = env.get_const(&n) {
            println!("TYPE {name}: {:?}", c.type_);
        } else {
            println!("TYPE {name}: ABSENT");
        }
    }
}

fn show(e: &Expr) -> String {
    use crate::expr::ExprKind;
    match e.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        ExprKind::App(f, a) => format!("({} {})", show(f), show(a)),
        ExprKind::Lam(_, t, b) => format!("(fun :{} => {})", show(t), show(b)),
        ExprKind::Pi(_, t, b) => format!("(({}) -> {})", show(t), show(b)),
        ExprKind::BVar(i) => format!("#{}", i),
        ExprKind::FVar(_) => "fv".into(),
        ExprKind::Sort(l) => format!("Sort({:?})", l),
        other => format!("{:?}", other),
    }
}

#[test]
fn zzz_probe_lemma_types2() {
    let mut env = Environment::with_prelude();
    env.init_fin_sum().expect("init_fin_sum");
    env.init_nat_totality_proofs().expect("totality");
    for name in [
        "Nat.lt_of_le_of_ne",
        "Nat.decEq",
        "Decidable.rec",
        "Decidable",
        "Eq.mpr",
        "Eq.mp",
        "Fin.isLt",
        "Fin.eq_of_val_eq",
        "Fin.mk",
        "Fin.val",
        "instLENat",
        "instLTNat",
        "LE.le",
        "LT.lt",
        "id",
    ] {
        let n = Name::from_string(name);
        if let Some(c) = env.get_const(&n) {
            println!("TY2 {name}: {}", show(&c.type_));
        } else {
            println!("TY2 {name}: ABSENT");
        }
    }
}

#[test]
fn zzz_probe_types3() {
    let mut env = Environment::with_prelude();
    env.init_fin_sum().expect("init_fin_sum");
    env.init_nat_totality_proofs().expect("totality");
    for name in [
        "Nat.lt_succ_iff",
        "Nat.succ_le_succ",
        "Nat.lt_succ_self",
        "instLENat",
        "instLTNat",
        "LE.mk",
        "LT.mk",
    ] {
        let n = Name::from_string(name);
        if let Some(c) = env.get_const(&n) {
            println!(
                "TY3 {name}: {} ||| VALUE: {}",
                show(&c.type_),
                c.value.as_ref().map(show).unwrap_or("<none>".into())
            );
        } else {
            println!("TY3 {name}: ABSENT");
        }
    }
}
