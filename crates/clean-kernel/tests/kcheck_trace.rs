// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use clean_kernel::expr::{BinderData, Expr};
use clean_kernel::kcheck_trace::term::{Label, Node, Term};
use clean_kernel::kcheck_trace::*;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

fn b(i: u32) -> Term {
    Term::new(Node::BVar(i))
}
fn sort() -> Term {
    Term::new(Node::Sort(Level::zero()))
}
fn app(f: Term, a: Term, d: Term) -> Term {
    Term::new(Node::App(f, a, Label::Checked(d)))
}
fn lam(d: Term, t: Term) -> Term {
    Term::new(Node::Lam(BinderData::default(), d, t))
}

#[test]
fn substitution_transports_domain_under_nested_binder() {
    // fun y : x => f y, where f's argument was checked against x.
    let t = lam(b(0), app(b(2), b(0), b(1)));
    let substituted = t.instantiate(&sort());
    let expected = lam(sort(), app(b(1), b(0), sort()));
    assert_eq!(substituted, expected);
    assert_eq!(substituted.erase(), t.erase().instantiate(&sort().erase()));
    let wrong = lam(sort(), app(b(1), b(0), b(1)));
    assert_ne!(
        substituted, wrong,
        "a side table that leaves the label behind must fail"
    );
}

#[test]
fn substituted_argument_is_lifted_inside_label() {
    let t = lam(sort(), app(b(1), b(0), b(1)));
    let actual = t.instantiate(&b(0));
    let expected = lam(sort(), app(b(1), b(0), b(1)));
    assert_eq!(actual, expected);
    assert_eq!(actual.erase(), t.erase().instantiate(&b(0).erase()));
}

#[test]
fn universe_instantiation_traverses_labels() {
    let u = Name::from_string("u");
    let d = Term::new(Node::Sort(Level::param(u.clone())));
    let t = app(b(0), b(1), d);
    let actual = t.instantiate_levels(&[u], &[Level::zero()]);
    assert_eq!(actual, app(b(0), b(1), sort()));
}

#[test]
fn opening_and_abstraction_roundtrip_labels() {
    let t = app(b(0), b(0), b(0));
    assert_eq!(t.open(7).abstract_local(7), t);
    assert_eq!(t.lift(2, 0), app(b(2), b(2), b(2)));
}

#[test]
fn failed_branch_rolls_back_nested_successes() {
    let mut j = Journal::default();
    j.push(Token::Stop);
    let result: Result<(), &str> = j.attempt(|j| {
        j.push(Token::App);
        j.attempt::<_, &str>(|j| {
            j.push(Token::Refl);
            Ok(())
        })?;
        Err("outer failure")
    });
    assert_eq!(result, Err("outer failure"));
    assert_eq!(j.tokens(), &[Token::Stop]);
}

#[test]
fn beta_compares_stored_domain_and_refuses_a_mutant() {
    let d = sort();
    let argument = Term::new(Node::Const(Name::from_string("p"), vec![]));
    let redex = app(lam(d.clone(), app(b(0), b(0), b(0))), argument.clone(), d);
    let mut j = Journal::default();
    let Some((class, Some(reduct))) = beta(&redex, &mut j, |_, _, _| Err("unexpected".into()))
    else {
        panic!("beta should contract");
    };
    assert_eq!(class, DomainClass::Identical);
    assert_eq!(reduct, app(argument.clone(), argument.clone(), argument));
    assert_eq!(j.tokens(), &[Token::Dom, Token::Refl]);
    let wrong = Term::new(Node::Sort(Level::succ(Level::zero())));
    let redex = app(lam(sort(), b(0)), b(0), wrong.clone());
    let Some((class, reduct)) = beta(&redex, &mut j, |label, domain, j| {
        assert_eq!(label, &wrong);
        assert_eq!(domain, &sort());
        j.push(Token::Sort);
        Err("sort domains differ".into())
    }) else {
        panic!("expected exposed redex");
    };
    assert_eq!(class, DomainClass::Failed("sort domains differ".into()));
    assert_eq!(reduct, None);
    assert_eq!(j.tokens(), &[Token::Dom, Token::Refl]);
}

#[test]
fn missing_domain_is_named_and_never_reinferred() {
    let t = Term::new(Node::App(
        lam(sort(), b(0)),
        b(0),
        Label::Missing("recursor_rhs".into()),
    ));
    let mut j = Journal::default();
    assert_eq!(
        beta(&t, &mut j, |_, _, _| panic!("must not hide a hole")),
        Some((DomainClass::Missing("recursor_rhs".into()), None))
    );
    assert!(j.tokens().is_empty());
}

#[test]
fn conversion_branch_retains_its_dom_certificate() {
    let t = app(
        lam(sort(), b(0)),
        b(0),
        Term::new(Node::Const(Name::from_string("Alias"), vec![])),
    );
    let mut j = Journal::default();
    let Some((class, Some(_))) = beta(&t, &mut j, |_, _, j| {
        j.push(Token::DeltaL);
        j.push(Token::Refl);
        Ok(2)
    }) else {
        panic!("should contract");
    };
    assert_eq!(class, DomainClass::Convertible { steps: 2 });
    assert_eq!(j.tokens(), &[Token::Dom, Token::DeltaL, Token::Refl]);
}

#[test]
fn erasure_does_not_encode_a_label_as_kernel_metadata() {
    let t = app(sort(), sort(), b(5));
    assert_eq!(
        t.erase(),
        Expr::app(Expr::sort(Level::zero()), Expr::sort(Level::zero()))
    );
    let differently_labelled = app(sort(), sort(), sort());
    assert_eq!(t.erase(), differently_labelled.erase());
    assert_ne!(t, differently_labelled);
    let mut active = std::collections::HashSet::new();
    active.insert(t);
    assert!(!active.contains(&differently_labelled));
    active.insert(differently_labelled);
    assert_eq!(active.len(), 2, "search keys must preserve distinct labels");
}

#[test]
fn ordinary_and_fenced_verdicts_and_reduction_counts_survive_local_tracing() {
    use clean_kernel::env::{Declaration, Environment};
    use clean_kernel::tc::{reduction_stats, TypeChecker};
    use clean_kernel::ReferenceKernel;
    fn ordinary() -> (Vec<bool>, String) {
        let env = Environment::for_lean_replay();
        let tc = TypeChecker::new(&env);
        let p = Expr::sort(Level::zero());
        let identity = Expr::lam(BinderData::default(), p.clone(), Expr::bvar(0));
        let reduced = Expr::app(identity, p.clone());
        reduction_stats::reduction_stats_reset();
        let verdicts = vec![
            tc.whnf(&reduced) == p,
            tc.is_def_eq(&reduced, &p),
            tc.is_def_eq(&p, &Expr::type_()),
        ];
        (verdicts, reduction_stats::reduction_stats_report(0))
    }
    fn fenced() -> Vec<bool> {
        let base = Environment::for_lean_replay();
        let mut k = ReferenceKernel::new(base).expect("honest replay base");
        let p = Expr::sort(Level::zero());
        let ty = Expr::pi(BinderData::default(), p.clone(), p.clone());
        let good = Declaration::Definition {
            name: Name::from_string("C4.identity"),
            level_params: vec![],
            type_: ty.clone(),
            value: Expr::lam(BinderData::default(), p.clone(), Expr::bvar(0)),
            is_reducible: true,
        };
        let bad = Declaration::Theorem {
            name: Name::from_string("C4.bad"),
            level_params: vec![],
            type_: ty,
            value: p,
        };
        vec![k.add_checked(good).is_ok(), k.add_checked(bad).is_ok()]
    }
    let before = ordinary();
    let fence_before = fenced();
    let mut j = Journal::default();
    let t = app(lam(sort(), b(0)), b(0), sort());
    assert!(beta(&t, &mut j, |_, _, _| Err("unused".into())).is_some());
    let env = Environment::for_lean_replay();
    let mut tracer = core::CoreTracer::new(&env, 10000);
    let raw = Expr::app(
        Expr::lam(BinderData::default(), Expr::type_(), Expr::bvar(0)),
        Expr::sort(Level::zero()),
    );
    let (annotated, _) = tracer.check(&raw).expect("isolated checker");
    assert_eq!(
        tracer.whnf(&annotated).expect("isolated beta").erase(),
        Expr::sort(Level::zero())
    );
    drop(tracer);
    // Exercise an enabled oracle profiler on the post-delta shape of the
    // convertible-domain fixture too. The argument is the closed proposition
    // forall P : Prop, P -> P, so its type converts with the stored domain.
    let type_one = Term::new(Node::Sort(Level::succ(Level::zero())));
    let label = app(lam(type_one.clone(), b(0)), sort(), type_one);
    let proposition = Term::new(Node::Pi(
        BinderData::default(),
        sort(),
        Term::new(Node::Pi(BinderData::default(), b(0), b(1))),
    ));
    let checker = TypeChecker::new(&env);
    assert!(checker.is_def_eq(
        &checker
            .infer_type(&proposition.erase())
            .expect("closed proposition"),
        &label.erase(),
    ));
    let redex = app(lam(sort(), b(0)), proposition, label);
    let mut profiled = core::CoreTracer::new(&env, 10000);
    profiled.whnf(&redex).expect("profiled domain guard");
    assert!(profiled
        .oracle_conversions
        .iter()
        .any(|call| call.source == "beta"
            && call.equal
            && !call.budget_exhausted
            && call.heartbeats > 0));
    drop(profiled);
    assert_eq!(before, ordinary());
    assert_eq!(fence_before, fenced());
    assert_eq!(before.0, vec![true, true, false]);
    assert_eq!(fence_before, vec![true, false]);
    assert!(
        !before.1.is_empty(),
        "compile this test with reduction-stats"
    );
}

#[test]
fn core_checker_records_the_domain_used_for_argument_checking() {
    use clean_kernel::env::Environment;
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let env = Environment::for_lean_replay();
    let p = Expr::sort(Level::zero());
    let ty = Expr::sort(Level::succ(Level::zero()));
    // (fun T : Type => T) Prop: the label is Type, not Prop.
    let raw = Expr::app(
        Expr::lam(BinderData::default(), ty.clone(), Expr::bvar(0)),
        p.clone(),
    );
    let mut tracer = CoreTracer::new(&env, 10000);
    let (labelled, inferred) = tracer.check(&raw).expect("core check");
    let Node::App(_, _, Label::Checked(domain)) = labelled.0.as_ref() else {
        panic!("checked application must have a label");
    };
    assert_eq!(domain.erase(), ty);
    assert_eq!(inferred.erase(), ty);
    assert_eq!(tracer.whnf(&labelled).expect("labelled beta").erase(), p);
    assert_eq!(tracer.beta_classes, vec![DomainClass::Identical]);
}

#[test]
fn core_checker_reports_coverage_and_budget_separately_from_domain_failure() {
    use clean_kernel::env::Environment;
    use clean_kernel::kcheck_trace::core::{CoreTracer, Refusal};
    let env = Environment::for_lean_replay();
    let mut tracer = CoreTracer::new(&env, 10);
    assert!(
        matches!(tracer.check(&Expr::nat_lit(0)),Err(Refusal::Coverage {source_name,..}) if source_name=="literal_type_absent")
    );
    assert!(tracer.beta_classes.is_empty());
    let mut tracer = CoreTracer::new(&env, 0);
    assert!(matches!(
        tracer.check(&Expr::sort(Level::zero())),
        Err(Refusal::Budget)
    ));
    assert!(tracer.beta_classes.is_empty());
}

#[test]
fn delta_exposes_a_lambda_with_a_convertible_but_different_domain() {
    use clean_kernel::env::{Declaration, Environment};
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let mut env = Environment::default();
    let p = Expr::sort(Level::zero());
    let ty = Expr::type_();
    let alias = Name::from_string("C4.Alias");
    let function = Name::from_string("C4.f");
    env.add_decl(Declaration::Definition {
        name: alias.clone(),
        level_params: vec![],
        type_: ty,
        value: p.clone(),
        is_reducible: true,
    })
    .expect("alias");
    let a = Expr::const_(alias, vec![]);
    env.add_decl(Declaration::Definition {
        name: function.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderData::default(), a.clone(), a),
        value: Expr::lam(BinderData::default(), p.clone(), Expr::bvar(0)),
        is_reducible: true,
    })
    .expect("convertible declared and actual domains");
    let raw = Expr::lam(
        BinderData::default(),
        p,
        Expr::app(Expr::const_(function, vec![]), Expr::bvar(0)),
    );
    let mut tracer = CoreTracer::new(&env, 10000);
    let (checked, _) = tracer.check(&raw).expect("checked application");
    let Node::Lam(_, _, body) = checked.0.as_ref() else {
        panic!("lambda");
    };
    let reduced = tracer.whnf(&body.open(0)).expect("beta after delta");
    assert!(matches!(reduced.0.as_ref(), Node::Local(0)));
    assert!(tracer
        .beta_classes
        .iter()
        .any(|c| matches!(c,DomainClass::Convertible {steps} if *steps>0)));
    let oracle = tracer
        .oracle_conversions
        .iter()
        .find(|call| call.source == "beta")
        .expect("actual kernel beta-label comparison");
    assert!(oracle.equal && !oracle.budget_exhausted);
    assert!(oracle.heartbeats > 0);
    assert_eq!(oracle.heartbeats, oracle.categories.values().sum::<u64>());
    assert!(oracle.categories.get("isDefEq").copied().unwrap_or(0) > 0);
    assert!(
        CoreTracer::new(&env, 10000).oracle_conversions.is_empty(),
        "a new declaration must not inherit an oracle profile"
    );
}

#[test]
fn eta_and_proof_irrelevance_use_labelled_inference() {
    use clean_kernel::env::{Declaration, Environment};
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let mut env = Environment::default();
    let truth = Expr::pi(
        BinderData::default(),
        Expr::sort(Level::zero()),
        Expr::pi(BinderData::default(), Expr::bvar(0), Expr::bvar(1)),
    );
    let function_type = Expr::pi(BinderData::default(), truth.clone(), truth.clone());
    let value = Expr::lam(BinderData::default(), truth.clone(), Expr::bvar(0));
    for name in ["C4.etaF", "C4.etaG"] {
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(name),
            level_params: vec![],
            type_: function_type.clone(),
            value: value.clone(),
        })
        .expect("opaque proof function");
    }
    let f = Expr::const_(Name::from_string("C4.etaF"), vec![]);
    let g = Expr::const_(Name::from_string("C4.etaG"), vec![]);
    let eta = Expr::lam(
        BinderData::default(),
        truth,
        Expr::app(f.clone(), Expr::bvar(0)),
    );
    let mut tracer = CoreTracer::new(&env, 100000);
    let (f, _) = tracer.check(&f).expect("opaque function");
    let (g, _) = tracer.check(&g).expect("opaque function");
    let (eta, _) = tracer.check(&eta).expect("eta body annotated");
    assert!(tracer.conv(&eta, &f).expect("eta conversion"));
    assert!(tracer.journal.tokens().contains(&Token::EtaR));
    assert!(tracer.conv(&f, &g).expect("proof irrelevance"));
    assert!(tracer.journal.tokens().contains(&Token::Irrel));
}

fn nat_environment() -> clean_kernel::env::Environment {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    let mut env = clean_kernel::env::Environment::default();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Nat"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::pi(BinderData::default(), nat.clone(), nat),
                },
            ],
        }],
    })
    .expect("Nat admission");
    env
}

#[test]
fn iota_records_the_major_application_label() {
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let env = nat_environment();
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let motive = Expr::lam(BinderData::default(), nat(), nat());
    let step = Expr::lam(
        BinderData::default(),
        nat(),
        Expr::lam(BinderData::default(), nat(), Expr::bvar(0)),
    );
    let raw = Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [motive, zero.clone(), step, Expr::nat_lit(2)],
    );
    let mut tracer = CoreTracer::new(&env, 100000);
    let (term, _) = tracer.check(&raw).expect("recursor application");
    let result = tracer.whnf(&term).expect("labelled iota");
    assert!(tracer
        .conv(
            &result,
            &Term::new(Node::Const(Name::from_string("Nat.zero"), vec![]))
        )
        .expect("result"));
    assert!(!tracer.iota_classes.is_empty());
    assert!(tracer.iota_classes.iter().all(|(_, c)| matches!(
        c,
        DomainClass::Identical | DomainClass::LevelInstantiated | DomainClass::Convertible { .. }
    )));
}

#[test]
fn iota_rule_spine_checks_old_labels_against_rhs_binders() {
    use clean_kernel::kcheck_trace::core::{CoreTracer, LabelledEnvironment, Refusal};
    let env = nat_environment();
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let zero_name = Name::from_string("Nat.zero");
    let zero = Expr::const_(zero_name.clone(), vec![]);
    let rec_name = Name::from_string("Nat.rec");
    let levels = vec![Level::succ(Level::zero())];
    let raw = Expr::apps(
        Expr::const_(rec_name.clone(), levels.clone()),
        [
            Expr::lam(BinderData::default(), nat(), nat()),
            zero.clone(),
            Expr::lam(
                BinderData::default(),
                nat(),
                Expr::lam(BinderData::default(), nat(), Expr::bvar(0)),
            ),
            zero.clone(),
        ],
    );
    let _subject_type = clean_kernel::tc::TypeChecker::new(&env)
        .infer_type_full(&raw)
        .expect("the unchanged ordinary checker accepts the subject");
    let mut producer = CoreTracer::new(&env, 100000);
    let (term, _) = producer.check(&raw).expect("checked source labels");
    let rec = env.get_recursor(&rec_name).expect("Nat recursor");
    let rule = rec
        .rules
        .iter()
        .find(|rule| rule.constructor_name == zero_name)
        .expect("zero computation rule");
    let raw_rhs = rule
        .rhs
        .instantiate_level_params_direct(&rec.level_params, &levels);
    let (rhs, _) = producer.check(&raw_rhs).expect("checked rule");
    let mut valid = LabelledEnvironment::default();
    valid.insert_rule(rec_name.clone(), zero_name.clone(), rhs.clone());
    let mut tracer = CoreTracer::with_labelled_environment(&env, &valid, 100000);
    assert_eq!(tracer.whnf(&term).expect("rule spine").erase(), zero);
    assert_eq!(
        tracer.beta_classes.len(),
        3,
        "motive and both minor applications must each perform DOM"
    );
    let Node::Lam(binder, _, body) = rhs.0.as_ref() else {
        panic!("rule starts with its motive binder");
    };
    let wrong_domain = sort();
    let forged = Term::new(Node::Lam(*binder, wrong_domain.clone(), body.clone()));
    let mut invalid = LabelledEnvironment::default();
    invalid.insert_rule(rec_name, zero_name, forged);
    let mut tracer = CoreTracer::with_labelled_environment(&env, &invalid, 100000);
    let error = tracer
        .whnf(&term)
        .expect_err("old labels cannot be replaced by the forged RHS binder type");
    assert!(!matches!(error, Refusal::Budget));
    let failure = tracer.domain_problems.first().expect("named DOM refusal");
    assert!(matches!(failure.class, DomainClass::Failed(_)));
    assert_eq!(failure.domain, wrong_domain.erase().to_string());
}

#[test]
fn deep_labels_transform_and_drop_without_native_stack_recursion() {
    let mut term = b(0);
    for _ in 0..2000 {
        term = app(term, b(0), b(0));
    }
    let instantiated = term.instantiate(&sort());
    assert!(!instantiated.erased_eq(&term));
    drop(instantiated);
    drop(term);
}

#[test]
fn k_records_the_major_label_and_uses_infer_ann() {
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let mut env = nat_environment();
    env.init_eq().expect("equality admission");
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = || Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Level::succ(Level::zero());
    let eq = |right: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            [nat(), zero(), right],
        )
    };
    let motive = Expr::lam(
        BinderData::default(),
        nat(),
        Expr::lam(BinderData::default(), eq(Expr::bvar(0)), nat()),
    );
    let call = Expr::apps(
        Expr::const_(Name::from_string("Eq.rec"), vec![one.clone(), one.clone()]),
        [nat(), zero(), motive, zero(), zero(), Expr::bvar(0)],
    );
    let raw = Expr::lam(BinderData::default(), eq(zero()), call);
    let expected = Expr::lam(BinderData::default(), eq(zero()), zero());
    let mut tracer = CoreTracer::new(&env, 1000000);
    let (raw, _) = tracer.check(&raw).expect("K application");
    let (expected, _) = tracer.check(&expected).expect("constant result");
    assert!(tracer.conv(&raw, &expected).expect("K conversion"));
    assert!(!tracer.k_classes.is_empty());
    assert!(tracer.k_classes.iter().all(|(_, c)| matches!(
        c,
        DomainClass::Identical | DomainClass::LevelInstantiated | DomainClass::Convertible { .. }
    )));
}

#[test]
fn projections_and_structure_eta_preserve_labels() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let mut env = nat_environment();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pair = Expr::const_(Name::from_string("TracePair"), vec![]);
    let mk = Expr::const_(Name::from_string("TracePair.mk"), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("TracePair"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("TracePair.mk"),
                type_: Expr::pi(
                    BinderData::default(),
                    nat.clone(),
                    Expr::pi(BinderData::default(), nat, pair.clone()),
                ),
            }],
        }],
    })
    .expect("pair admission");
    let proj = |i, e| Expr::proj(Name::from_string("TracePair"), i, e);
    let eta = Expr::lam(
        BinderData::default(),
        pair.clone(),
        Expr::apps(mk, [proj(0, Expr::bvar(0)), proj(1, Expr::bvar(0))]),
    );
    let identity = Expr::lam(BinderData::default(), pair, Expr::bvar(0));
    assert!(clean_kernel::tc::TypeChecker::new(&env).is_def_eq(&eta, &identity));
    let mut tracer = CoreTracer::new(&env, 1000000);
    let (eta, _) = tracer.check(&eta).expect("labelled projections");
    let (identity, _) = tracer.check(&identity).expect("identity");
    assert!(tracer
        .conv(&eta, &identity)
        .expect("labelled structure eta"));
}

#[test]
fn universe_only_identity_survives_term_substitution() {
    let u = Name::from_string("u");
    let original = Term::new(Node::Sort(Level::param(u.clone())));
    let label = original.instantiate_levels(&[u], &[Level::zero()]);
    let redex = app(lam(sort(), b(0)), sort(), label.clone());
    let mut journal = Journal::default();
    assert!(matches!(
        beta(&redex, &mut journal, |_, _, _| Err("unused".into())),
        Some((DomainClass::LevelInstantiated, Some(_)))
    ));
    let under = app(b(0), b(0), label).instantiate(&sort());
    let Node::App(_, _, Label::Checked(domain)) = under.0.as_ref() else {
        panic!("label");
    };
    assert_ne!(domain.before_levels(), &domain.erase());
}

#[test]
fn iota_walk_refuses_a_bad_minor_label_before_returning_the_minor() {
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let env = nat_environment();
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let raw = Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderData::default(), nat(), nat()),
            zero.clone(),
            Expr::lam(
                BinderData::default(),
                nat(),
                Expr::lam(BinderData::default(), nat(), Expr::bvar(0)),
            ),
            zero,
        ],
    );
    let mut producer = CoreTracer::new(&env, 100000);
    let (term, _) = producer.check(&raw).expect("valid recursor application");
    fn mutate(t: &Term, from_end: usize) -> Term {
        let Node::App(f, a, d) = t.0.as_ref() else {
            panic!("application spine");
        };
        if from_end == 0 {
            Term::new(Node::App(f.clone(), a.clone(), Label::Checked(sort())))
        } else {
            Term::new(Node::App(mutate(f, from_end - 1), a.clone(), d.clone()))
        }
    }
    // Major is position 3; mutate the zero-case minor at position 1.
    let mutant = mutate(&term, 2);
    let mut tracer = CoreTracer::new(&env, 100000);
    assert!(tracer.whnf(&mutant).is_err());
    let failure = tracer
        .spine_comparisons
        .iter()
        .find(|e| matches!(e.class, DomainClass::Failed(_)))
        .expect("named failed position");
    assert_eq!(
        (
            failure.target.as_str(),
            failure.position_kind.as_str(),
            failure.position
        ),
        ("recursor", "minor", 1)
    );
    assert_eq!(tracer.domain_problems.len(), 1);
}

#[test]
fn trace_depth_counts_walk_positions_and_finalizes_a_declaration_header() {
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let env = clean_kernel::env::Environment::default();
    let mut tracer = CoreTracer::new(&env, 10000);
    let raw = Expr::lam(BinderData::default(), Expr::type_(), Expr::bvar(0));
    tracer.check(&raw).expect("typed lambda");
    tracer.finish_journal();
    assert!(tracer.volume.max_call_depth > 1);
    assert!(tracer.volume.largest_term_height > 1);
    assert!(tracer.volume.depth_bound >= tracer.volume.max_call_depth);
    assert_eq!(
        tracer.journal.tokens().first(),
        Some(&Token::Depth(tracer.volume.depth_bound))
    );
}

#[test]
fn admitted_labelled_prefix_reuses_syntax_without_rechecking_earlier_entries() {
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let env = nat_environment();
    let names: Vec<_> = env.constants().map(|c| c.name.clone()).collect();
    let mut initial = CoreTracer::new(&env, 100000);
    let prefix = initial.annotate_group(&names).expect("annotated Nat block");
    let mut next = CoreTracer::with_labelled_environment(&env, &prefix, 100000);
    let raw = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(0),
    );
    next.check(&raw).expect("checked with labelled prefix");
    assert!(next.reannotated_dependencies.is_empty());
    assert!(!next.volume.inference_nodes.contains_key("environment"));
}

#[test]
fn construction_heads_and_minor_origins_survive_rebuilt_spines() {
    let rec = Name::from_string("Nat.rec");
    let direct = app(Term::new(Node::Const(rec.clone(), vec![])), sort(), sort());
    assert!(!direct.had_other_head(&rec));
    let indirect =
        app(b(0), sort(), sort()).instantiate(&Term::new(Node::Const(rec.clone(), vec![])));
    assert!(indirect.had_other_head(&rec));
    // A later outer node can be built with the actual recursor as head;
    // the inner application's earlier variable head must still be counted.
    let outer = app(indirect, sort(), sort());
    assert!(outer.had_other_head(&rec));
    let minor = app(Term::new(Node::Local(3)), b(0), sort()).mark_minor_heads(&rec, 3, 1);
    let closed = minor.abstract_local(3).instantiate(&lam(sort(), b(0)));
    assert_eq!(closed.minor_origin(), Some(&rec));
}

#[test]
fn iota_constructor_spine_is_charged_for_prop_and_data() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let mut env = nat_environment();
    let u = Name::from_string("trace_u");
    let family = Name::from_string("TraceUnit");
    let ctor = Name::from_string("TraceUnit.unit");
    let rec = Name::from_string("TraceUnit.rec");
    env.add_inductive_core(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 0,
        types: vec![InductiveType {
            name: family.clone(),
            type_: Expr::sort(Level::param(u.clone())),
            constructors: vec![Constructor {
                name: ctor.clone(),
                type_: Expr::const_(family.clone(), vec![Level::param(u.clone())]),
            }],
        }],
    })
    .expect("polymorphic unit family");
    for level in [Level::zero(), Level::succ(Level::zero())] {
        let unit_type = Expr::const_(family.clone(), vec![level.clone()]);
        let levels: Vec<_> = env
            .get_recursor(&rec)
            .expect("recursor")
            .level_params
            .iter()
            .map(|p| {
                if p == &u {
                    level.clone()
                } else {
                    Level::succ(Level::zero())
                }
            })
            .collect();
        let raw = Expr::apps(
            Expr::const_(rec.clone(), levels),
            [
                Expr::lam(
                    BinderData::default(),
                    unit_type,
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
                Expr::const_(ctor.clone(), vec![level]),
            ],
        );
        let mut tracer = CoreTracer::new(&env, 100000);
        let (term, _) = tracer.check(&raw).expect("unit elimination");
        tracer.whnf(&term).expect("unit iota");
        assert!(
            tracer.journal.tokens().contains(&Token::SpineRefl(0)),
            "Revision 4 IOTA charges its empty constructor walk for Prop and data"
        );
    }
}

#[test]
fn literal_expansion_refuses_a_name_only_nat_environment() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::kcheck_trace::core::{CoreTracer, Refusal};
    let mut env = clean_kernel::env::Environment::default();
    let nat = Name::from_string("Nat");
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Nat.alternate"),
                type_: Expr::const_(nat, vec![]),
            }],
        }],
    })
    .expect("noncanonical Nat namesake");
    let mut tracer = CoreTracer::new(&env, 10000);
    assert!(
        matches!(tracer.expand_literal(&clean_kernel::expr::Literal::Nat(clean_kernel::expr::BigNat::Small(1))),Err(Refusal::Coverage{source_name,..}) if source_name=="literal_Nat_extension_not_canonical")
    );
    assert!(tracer.literal_expansions.is_empty());
}

#[test]
fn unavailable_string_literal_construction_is_named_before_any_application_is_built() {
    use clean_kernel::kcheck_trace::core::{CoreTracer, Refusal};
    let env = nat_environment();
    let mut tracer = CoreTracer::new(&env, 10000);
    assert!(
        matches!(tracer.expand_literal(&clean_kernel::expr::Literal::String("a".into())),Err(Refusal::Coverage{source_name,..}) if source_name=="String_literal_ofList_missing_or_legacy_layout")
    );
    assert!(tracer.literal_expansions.is_empty());
    assert!(tracer.domain_problems.is_empty());
}

// These C4 elaboration controls share this integration target's environment helpers.
#[path = "kcheck_trace/c4_elaboration_controls.rs"]
mod c4_elaboration_controls;
#[test]
fn native_nat_extension_does_not_fold_a_forged_definition() {
    use clean_kernel::env::Declaration;
    use clean_kernel::kcheck_trace::core::CoreTracer;
    let mut env = nat_environment();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let name = Name::from_string("Nat.add");
    let forged_result = Expr::nat_lit(99);
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::pi(
            BinderData::default(),
            nat.clone(),
            Expr::pi(BinderData::default(), nat.clone(), nat.clone()),
        ),
        value: Expr::lam(
            BinderData::default(),
            nat.clone(),
            Expr::lam(BinderData::default(), nat, forged_result.clone()),
        ),
        is_reducible: true,
    })
    .expect("forged arithmetic definition is well typed");
    assert!(!env.native_fold_authorized(&name));
    let raw = Expr::apps(
        Expr::const_(name, vec![]),
        [Expr::nat_lit(1), Expr::nat_lit(2)],
    );
    let checker = clean_kernel::tc::TypeChecker::new(&env);
    assert!(checker.is_def_eq(&checker.whnf(&raw), &forged_result));
    let mut tracer = CoreTracer::new(&env, 10000);
    let (annotated, _) = tracer.check(&raw).expect("typed forged application");
    let reduced = tracer.whnf(&annotated).expect("ordinary delta fallback");
    assert!(checker.is_def_eq(&reduced.erase(), &forged_result));
    assert!(
        tracer.native_nat_steps.is_empty(),
        "a name never licenses primitive arithmetic"
    );
}

#[test]
fn independent_shared_label_dags_compare_without_unfolding_their_trees() {
    let mut left = app(b(0), b(1), sort());
    let mut equal = app(b(0), b(1), sort());
    let mut different = app(
        b(0),
        b(1),
        Term::new(Node::Sort(Level::succ(Level::zero()))),
    );
    // Only 49 application nodes per graph; recursive tree equality repeats
    // the child comparison three times at each level (3^48 paths).
    for _ in 0..48 {
        left = app(left.clone(), left.clone(), left);
        equal = app(equal.clone(), equal.clone(), equal);
        different = app(different.clone(), different.clone(), different);
    }
    assert!(left == equal);
    assert!(left.erased_eq(&different));
    assert!(
        left != different,
        "deep annotations remain part of equality"
    );
}

#[test]
fn transformations_preserve_shared_labels_context_and_diagnostics() {
    // Forty-nine nodes represent 3^48 paths. Every transformation must visit
    // the labelled DAG, including annotations, without expanding those paths.
    let u = Name::from_string("dag_u");
    let mut t = app(b(0), Term::new(Node::Sort(Level::param(u.clone()))), b(0));
    for _ in 0..48 {
        t = app(t.clone(), t.clone(), t);
    }
    let opened = t.open(7);
    assert_eq!(opened.abstract_local(7), t);
    assert_eq!(t.lift(1, 0).instantiate(&sort()), t);
    let instantiated = opened.instantiate_levels(&[u], &[Level::zero()]);
    assert_ne!(instantiated, opened);
    assert_eq!(instantiated.before_levels(), &opened.erase());
    assert_eq!(instantiated.abstract_local(7).open(7), instantiated);
    assert_eq!(instantiated.height(), t.height());
    let Node::App(f, a, Label::Checked(d)) = instantiated.0.as_ref() else {
        panic!("shared application");
    };
    assert!(std::sync::Arc::ptr_eq(&f.0, &a.0));
    assert!(std::sync::Arc::ptr_eq(&a.0, &d.0));
    // A shared input at two binder depths must use different work-table keys.
    let shared = app(b(0), b(1), b(0));
    let mixed = app(shared.clone(), lam(sort(), shared), sort()).instantiate(&sort());
    assert_eq!(
        mixed,
        app(
            app(sort(), b(0), sort()),
            lam(sort(), app(b(0), sort(), b(0))),
            sort()
        )
    );
}

#[test]
fn identity_transform_reuse_includes_hidden_labels_and_binder_depth() {
    use std::sync::Arc;
    let closed = lam(sort(), app(b(0), b(0), b(0)));
    assert!(Arc::ptr_eq(&closed.0, &closed.lift(0, 0).0));
    assert!(Arc::ptr_eq(&closed.0, &closed.lift(7, 0).0));
    assert!(Arc::ptr_eq(&closed.0, &closed.instantiate(&b(2)).0));
    // Separate variable nodes must all reuse the unchanged substitution value.
    let substituted = app(b(0), b(0), b(0)).instantiate(&closed);
    let Node::App(f, a, Label::Checked(d)) = substituted.0.as_ref() else {
        panic!("application");
    };
    for value in [f, a, d] {
        assert!(Arc::ptr_eq(&value.0, &closed.0));
    }
    // The erasure is closed, but the application label is open. Neither
    // substitution nor lifting may skip the hidden variable.
    let hidden = app(sort(), sort(), b(0));
    assert_eq!(hidden.instantiate(&sort()), app(sort(), sort(), sort()));
    assert_eq!(hidden.lift(2, 0), app(sort(), sort(), b(2)));
    let scoped = lam(sort(), app(sort(), sort(), b(1)));
    assert_eq!(
        scoped.instantiate(&sort()),
        lam(sort(), app(sort(), sort(), sort()))
    );
    assert_eq!(scoped.lift(2, 0), lam(sort(), app(sort(), sort(), b(3))));
    let u = Name::from_string("reuse_u");
    let actual =
        Term::new(Node::Sort(Level::param(u.clone()))).instantiate_levels(&[u], &[Level::zero()]);
    assert!(Arc::ptr_eq(&actual.0, &actual.lift(3, 0).0));
    assert_eq!(actual.before_levels(), actual.lift(3, 0).before_levels());
    assert_eq!(
        b(Expr::MAX_BVAR_INDEX).instantiate(&sort()),
        b(Expr::MAX_BVAR_INDEX - 1)
    );
}
