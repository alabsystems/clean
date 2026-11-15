use super::{declarations as d, *};
use clean_kernel::{BinderInfo, Declaration, KernelTypeError, Level, Name};

fn f(id: u64) -> Expr {
    Expr::fvar(clean_kernel::expr::FVarId::new(id))
}
fn refl(ty: Expr, x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, x],
    )
}
fn reject(env: &Environment, proof: &Expr, goal: &Expr) {
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(goal, &Expr::sort(Level::zero()))
        .expect("negative proposition itself well typed");
    let e = tc
        .check_type(proof, goal)
        .expect_err("wrong quantified computation/world must refuse");
    assert!(matches!(e, KernelTypeError::TypeMismatch { .. }), "{e:?}");
    assert!(!tc.heartbeat_spent());
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}
#[test]
fn test_universal_source_addition_theorem_is_checked_without_axioms() {
    let env = source_environment().expect("actual source declarations and modulo theorem");
    let name = Name::from_string(d::ADEQUACY);
    let decl = env.get_const(&name).unwrap();
    let proof = d::c(d::ADEQUACY);
    let mut tc = TypeChecker::new(&env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(&proof, &decl.type_)
        .expect("forall body/environment/world, no sampled premise");
    let audit = env.audit_certification(&decl.type_, &proof);
    assert!(audit.is_certified(), "{audit:?}");
    for n in audit.dependencies {
        assert!(env.axiom_deps(&n).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&n).unwrap().is_empty());
        assert!(env.trust_marker_deps(&n).unwrap().is_empty());
    }
    assert!(!tc.heartbeat_spent());
}
/// When `var` names a directory, write `data()` there as `file` (pretty JSON).
/// Optional evidence output: it asserts nothing about the subject, `data` is
/// built only when requested, and a requested write that fails still fails
/// the test.
fn export_evidence_if_requested(var: &str, file: &str, data: impl FnOnce() -> serde_json::Value) {
    let Ok(directory) = std::env::var(var) else {
        return;
    };
    let directory = std::path::PathBuf::from(directory);
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(
        directory.join(file),
        serde_json::to_vec_pretty(&data()).unwrap(),
    )
    .unwrap();
}

#[test]
fn test_original_source_literals_and_serialized_proofs_replay() {
    for (i, literal, value) in [
        (0, "0", 0),
        (1, "1u64", 1),
        (2, "0xff", 255),
        (3, "0b1010_0101u64", 165),
        (4, "0o77", 63),
        (5, "18_446_744_073_709_551_615u64", u64::MAX),
    ] {
        let text =
            format!("pub fn add_word(original:u64)->u64 {{ original.wrapping_add({literal}) }}");
        let projected = project_word64_addition_source(&text).unwrap();
        assert_eq!(projected.literal(), value);
        assert_eq!(projected.function(), "add_word");
        assert_eq!(projected.parameter(), "original");
        assert_eq!(projected.body().parameter, 0);
        let proof = projected.proof_candidate();
        let bytes = serde_json::to_vec(&proof).unwrap();
        let restored: Expr = serde_json::from_slice(&bytes).unwrap();
        let checked = replay_word64_addition_source(&text, &restored).unwrap();
        assert_eq!(checked.source().original_text(), text);
        assert_eq!(checked.claim(), &projected.claim());
        export_evidence_if_requested(
            "TRUST_WORD64_ADDITION_OUT",
            &format!("addition-{i}.json"),
            || {
                serde_json::json!({
                "model":MODEL,"original_source":text,"literal":value,"claim":checked.claim(),"proof":checked.proof(),
                "scope":"forall source environments/all valid u64 inputs/arbitrary world, empty trace; source-model only, not IR/TCX/ABI/NoUB/admission"})
            },
        );
    }
}
#[test]
fn test_parser_refuses_shadowing_effects_wrong_types_and_unchecked_literals() {
    let invalid = [
        "use imported::u64; fn a(x:u64)->u64{x.wrapping_add(1)}",
        "type u64 = u32; fn a(x:u64)->u64{x.wrapping_add(1)}",
        "trait T{} fn a(x:u64)->u64{x.wrapping_add(1)}",
        "fn a<u64>(x:u64)->u64{x.wrapping_add(1)}",
        "fn a(x:u64)->u64{let u64=1; x.wrapping_add(u64)}",
        "fn a(x:u64)->u64{use imported::item; x.wrapping_add(1)}",
        "fn a(x:u64)->u64{hidden!();x.wrapping_add(1)}",
        "fn a(x:u64)->u64{x.wrapping_add(hidden!())}",
        "#[unknown] fn a(x:u64)->u64{x.wrapping_add(1)}",
        "fn a(#[unknown] x:u64)->u64{x.wrapping_add(1)}",
        "unsafe fn a(x:u64)->u64{x.wrapping_add(1)}",
        "const fn a(x:u64)->u64{x.wrapping_add(1)}",
        "async fn a(x:u64)->u64{x.wrapping_add(1)}",
        "extern \"C\" fn a(x:u64)->u64{x.wrapping_add(1)}",
        "fn a(mut x:u64)->u64{x.wrapping_add(1)}",
        "fn a(ref x:u64)->u64{x.wrapping_add(1)}",
        "fn a(x:u32)->u64{x.wrapping_add(1)}",
        "fn a(x:u64)->u32{x.wrapping_add(1)}",
        "fn a(x:&u64)->u64{x.wrapping_add(1)}",
        "fn a(x:u64,y:u64)->u64{x.wrapping_add(1)}",
        "fn a(x:u64)->u64{other.wrapping_add(1)}",
        "fn a(x:u64)->u64{x.checked_add(1)}",
        "fn a(x:u64)->u64{x.wrapping_add::<u64>(1)}",
        "fn a(x:u64)->u64{x.wrapping_add(1,2)}",
        "fn a(x:u64)->u64{x.wrapping_add(18446744073709551616)}",
        "fn a(x:u64)->u64{x.wrapping_add(0x1_0000_0000_0000_0000u64)}",
        "fn a(x:u64)->u64{x.wrapping_add(1u128)}",
        "fn a(x:u64)->u64{x.wrapping_add(1usize)}",
        "fn a(x:u64)->u64{x.wrapping_add(-1)}",
        "fn a(x:u64)->u64{x.wrapping_add(1.0)}",
        "fn a(x:u64)->u64{x.wrapping_add(1+1)}",
        "fn a(x:u64)->u64{x.wrapping_add(1 as u64)}",
        "fn a(x:u64)->u64{x.wrapping_add(1);}",
        "fn a(x:u64)->u64{x.wrapping_add(1); hidden!()}",
        "fn a(x:u64)->u64{let y=x.wrapping_add(1); y}",
    ];
    for source in invalid {
        assert!(
            project_word64_addition_source(source).is_err(),
            "accepted {source}"
        );
    }
}
#[test]
fn test_kernel_ground_wrapping_computation_matches_u128_arithmetic() {
    let env = source_environment().unwrap();
    for (x, k) in [
        (0, 0),
        (u64::MAX, 0),
        (u64::MAX, 1),
        (u64::MAX, u64::MAX),
        (1u64 << 63, 1u64 << 63),
        (1, u64::MAX),
        (u64::MAX - 1, 2),
        (17, 29),
    ] {
        let result = ((u128::from(x) + u128::from(k)) % (1u128 << 64)) as u64;
        let computation = d::app(d::WORD_ADD, [Expr::nat_lit(x), Expr::nat_lit(k)]);
        let goal = d::eq(d::c("Nat"), computation, Expr::nat_lit(result));
        let mut tc = TypeChecker::new(&env);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        tc.check_type(&refl(d::c("Nat"), Expr::nat_lit(result)), &goal)
            .expect("actual checked ground modulo computation");
        assert!(!tc.heartbeat_spent());
    }
}
#[test]
fn test_kernel_refuses_wrong_literal_index_modulus_result_world_and_trace() {
    let env = source_environment().unwrap();
    let source = project_word64_addition_source("fn a(x:u64)->u64{x.wrapping_add(1)}").unwrap();
    let rho = f(3);
    let w = f(10);
    let world = f(12);
    let other = f(13);
    let bs = [
        (3, Expr::arrow(d::c("Nat"), d::c("Nat"))),
        (10, Expr::type_()),
        (12, w.clone()),
        (13, w.clone()),
    ];
    let actual = d::app(
        d::RUN,
        [
            w.clone(),
            source.body().reflect(),
            rho.clone(),
            world.clone(),
        ],
    );
    let proof = d::close(
        &bs,
        Expr::apps(
            source.proof_candidate(),
            [rho.clone(), w.clone(), world.clone()],
        ),
        true,
    );
    let x = Expr::app(rho.clone(), Expr::nat_lit(0));
    let good = d::app(d::WORD_ADD, [x.clone(), Expr::nat_lit(1)]);
    for wrong in [
        d::app(d::WORD_ADD, [x.clone(), Expr::nat_lit(2)]),
        d::app(
            d::WORD_ADD,
            [Expr::app(rho, Expr::nat_lit(1)), Expr::nat_lit(1)],
        ),
        d::app("Nat.add", [x.clone(), Expr::nat_lit(1)]),
        d::app(
            "Nat.mod",
            [
                d::app("Nat.add", [x.clone(), Expr::nat_lit(1)]),
                Expr::nat_lit(1u64 << 63),
            ],
        ),
    ] {
        let goal = d::close(
            &bs,
            d::eq(
                d::exit_ty(w.clone()),
                actual.clone(),
                d::returned(w.clone(), wrong, world.clone()),
            ),
            false,
        );
        reject(&env, &proof, &goal);
    }
    let wrong_world = d::close(
        &bs,
        d::eq(
            d::exit_ty(w.clone()),
            actual.clone(),
            d::returned(w.clone(), good.clone(), other),
        ),
        false,
    );
    reject(&env, &proof, &wrong_world);
    let trace = Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [d::c("Nat"), Expr::nat_lit(7), d::trace_nil()],
    );
    let traced = d::app(d::EXIT_MK, [w.clone(), good, world, trace]);
    let goal = d::close(&bs, d::eq(d::exit_ty(w), actual, traced), false);
    reject(&env, &proof, &goal);
}
#[test]
fn test_replay_refuses_open_forged_context_and_preserves_identity_environment() {
    let text = "fn a(x:u64)->u64{x.wrapping_add(1)}";
    assert!(replay_word64_addition_source(text, &f(9)).is_err());
    assert!(replay_word64_addition_source(text, &Expr::bvar(0)).is_err());
    assert!(replay_word64_addition_source(text, &d::c("unknown_proof")).is_err());
    let env = source_environment().unwrap();
    let mut forged = env.clone();
    assert!(forged
        .add_decl(Declaration::Axiom {
            name: Name::from_string(d::ADEQUACY),
            level_params: vec![],
            type_: Expr::sort(Level::zero())
        })
        .is_err());
    let identity =
        super::super::source_identity_kernel::project_identity_source("fn identity(x:u64)->u64{x}")
            .unwrap();
    super::super::source_identity_kernel::replay_identity_source(
        identity.original_text(),
        &identity.proof_candidate().unwrap(),
    )
    .expect("unchanged identity API still independent");
    // An open binder is not accepted merely because a lambda wraps it.
    let open = Expr::lam(BinderInfo::Default, d::c("Nat"), Expr::bvar(1));
    assert!(replay_word64_addition_source(text, &open).is_err());
}

#[test]
fn test_vocabulary_installs_alongside_identity_and_refuses_duplicate_installation() {
    let mut env = super::super::source_identity_kernel::source_environment().unwrap();
    install_source_model(&mut env).expect("separate checked source namespaces coexist");
    let source = project_word64_addition_source("fn a(x:u64)->u64{x.wrapping_add(1)}").unwrap();
    let claim = source.claim();
    let proof = source.proof_candidate();
    let mut tc = TypeChecker::new(&env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(&proof, &claim).unwrap();
    assert!(!tc.heartbeat_spent());
    drop(tc);
    let audit = env.audit_certification(&claim, &proof);
    assert!(audit.is_certified(), "{audit:?}");
    for n in audit.dependencies {
        assert!(env.axiom_deps(&n).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&n).unwrap().is_empty());
        assert!(env.trust_marker_deps(&n).unwrap().is_empty());
    }
    assert!(install_source_model(&mut env).is_err());
}
