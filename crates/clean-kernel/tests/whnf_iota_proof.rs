// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use clean_kernel::env::Environment;
use clean_kernel::tc::whnf_proof::WhnfProofStep;
use clean_kernel::{BinderInfo, Expr, KernelTypeError, Level, Name, TypeChecker};
fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
fn rec(motive: Expr, zero: Expr, successor: Expr, n: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [motive, zero, successor, n],
    )
}
#[test]
fn fused_iota_step_still_produces_a_checked_equality() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let tc = TypeChecker::new(&env);
    let term = rec(
        lam(c("Nat"), c("Nat")),
        Expr::nat_lit(13),
        lam(c("Nat"), lam(c("Nat"), Expr::bvar(0))),
        Expr::nat_lit(0),
    );
    tc.check_type(&term, &c("Nat")).unwrap();
    let outcome = tc.whnf_with_proof(&term, &c("Nat"), Level::succ(Level::zero()));
    assert_eq!(outcome.result, Expr::nat_lit(13));
    assert!(outcome
        .steps
        .iter()
        .any(|step| matches!(step, WhnfProofStep::Iota)));
    let proof = outcome
        .proof
        .expect("the iota reduction must produce its equality witness");
    let eq = |rhs| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [c("Nat"), term.clone(), rhs],
        )
    };
    tc.check_type(&proof, &eq(Expr::nat_lit(13))).unwrap();
    assert!(matches!(
        tc.check_type(&proof, &eq(Expr::nat_lit(29))),
        Err(KernelTypeError::TypeMismatch { .. })
    ));
}
#[test]
fn fused_iota_preserves_the_symbolic_native_grind_guard() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200);
    let id = tc.push_binder_local(Name::from_string("symbolic"), c("Nat"), BinderInfo::Default);
    let motive = lam(c("Nat"), c("Nat"));
    let successor = lam(c("Nat"), lam(c("Nat"), Expr::bvar(0)));
    let inner = rec(
        motive.clone(),
        Expr::fvar(id),
        successor.clone(),
        Expr::nat_lit(1024),
    );
    let outer = rec(motive, inner.clone(), successor, Expr::nat_lit(0));
    tc.check_type(&outer, &c("Nat")).unwrap();
    #[cfg(feature = "inference-stats")]
    let _ = clean_kernel::work_meter::stats::take();
    let reduced = tc.whnf(&outer);
    assert!(
        reduced.get_app_fn().is_lam(),
        "the existing guard retains the RHS application"
    );
    assert_ne!(reduced, inner);
    assert!(!tc.heartbeat_spent());
    #[cfg(feature = "inference-stats")]
    eprintln!("guard-work {:?}", clean_kernel::work_meter::stats::take());
}
