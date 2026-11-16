// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    decl_budget, declaration, identity, parse_decl_exact, trace, ConstantKind,
    DeclarationVerification, ElabError, Expr, ExprKind, Level, Name, Row, Specification,
    SurfaceDecl, TypeChecker,
};

fn strict_root(spec: &Specification, name: &Name) -> Result<(), String> {
    let env = spec.env();
    let info = env.get_const(name).ok_or("missing actual constant")?;
    require!(
        env.declaration_verification(name) == Some(DeclarationVerification::FullKernelCheck),
        "{name}: ordinary full-check provenance absent"
    );
    for deps in [
        env.axiom_deps(name),
        env.foundational_axiom_deps(name),
        env.trust_marker_deps(name),
    ] {
        require!(
            deps.ok_or("missing closure root")?.is_empty(),
            "{name}: nonempty axiom/trust closure"
        );
    }
    // A read-only Eq reflexivity query exposes the NAMED root and its complete
    // type/value/family closure to the EXISTING strict certification audit.
    // It never installs a witness and is never called first admission.
    let reference = Expr::const_(
        name.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let checker = TypeChecker::with_mode(env, env.mode());
    let ty = checker
        .infer_type(&reference)
        .map_err(|e| format!("{e:?}"))?;
    let universe = checker.infer_sort(&ty).map_err(|e| format!("{e:?}"))?;
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_str_levels("Eq", vec![universe.clone()]),
                ty.clone(),
            ),
            reference.clone(),
        ),
        reference.clone(),
    );
    let proof = Expr::app(
        Expr::app(Expr::const_str_levels("Eq.refl", vec![universe]), ty),
        reference,
    );
    let audit = env.audit_certification(&goal, &proof);
    require!(
        audit.is_certified(),
        "{name}: strict audit refused: {audit:?}"
    );
    require!(
        !clean_kernel::tc::declaration_budget_exhausted(),
        "{name}: incomplete replay budget"
    );
    if let Some(value) = &info.value {
        require!(
            info.kind != ConstantKind::Axiom,
            "{name}: value/axiom mismatch"
        );
        if let Some(record) = spec.get_definition(&name.to_string()) {
            require!(
                !record.is_axiom
                    && record.elaborated_type.as_ref() == Some(&info.type_)
                    && record.elaborated_value.as_ref() == Some(value),
                "{name}: actual kernel/record mismatch"
            );
            spec.verify_definition(&name.to_string())
                .map_err(|e| e.to_string())?;
        } else {
            // Generated casesOn/recOn have checked kernel values, not source
            // SpecDefinition records. Ordinary source defs still require their
            // exact source record in joined(), before reaching this helper.
            let recursor = env.get_recursor(name).ok_or_else(|| {
                format!("{name}: missing source record and actual generated recursor")
            })?;
            recursor.validate_metadata()?;
            require!(
                recursor.name == *name
                    && recursor.type_ == info.type_
                    && env.get_inductive(&recursor.inductive_name).is_some(),
                "{name}: generated recursor identity/type/family mismatch"
            );
        }
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(value, &info.type_)
            .map_err(|e| format!("{name}: actual kernel value replay failed: {e:?}"))?;
        if tc
            .infer_sort(&info.type_)
            .map_err(|e| format!("{e:?}"))?
            .is_zero()
        {
            let audit = env.audit_certification(&info.type_, value);
            require!(
                audit.is_certified(),
                "{name}: actual proof replay refused: {audit:?}"
            );
        }
    }
    Ok(())
}

pub(super) fn joined(spec: &Specification, row: &Row, event: &trace::Event) -> Result<(), String> {
    let (name, kind) = declaration(&row.source)?;
    require!(
        event.source == row.source && event.kind == kind && event.header == name,
        "{}: source/actual-call join mismatch",
        row.name
    );
    require!(
        event.absent_before
            && event.accepted
            && !event.exhausted
            && event.returned_name.as_deref() == Some(name.as_str())
            && event.elaborator_error.is_none(),
        "{name}: not an observed normal first admission: {event:?}"
    );
    let root = Name::from_string(&name);
    require!(
        event.kernel.as_ref() == spec.env().get_const(&root)
            && event.verification == Some(DeclarationVerification::FullKernelCheck),
        "{name}: actual checked declaration changed or provenance absent"
    );
    require!(
        event.family == trace::family(spec.env(), &root),
        "{name}: actual family metadata changed"
    );
    if kind == "def" {
        let record = spec.get_definition(&name).ok_or("missing actual record")?;
        require!(
            record.type_src == row.source
                && record.value_src.as_deref() == Some(row.source.as_str()),
            "{name}: cached expression or metadata does not authenticate source bytes"
        );
    } else {
        let family = spec
            .env()
            .get_inductive(&root)
            .ok_or("missing actual family")?;
        require!(
            !family.constructor_names.is_empty(),
            "{name}: missing actual constructors"
        );
        for constructor in &family.constructor_names {
            strict_root(spec, constructor)?;
        }
        let recursors: Vec<_> = spec
            .env()
            .recursors()
            .filter(|r| r.inductive_name == root)
            .collect();
        require!(
            recursors
                .iter()
                .any(|r| r.name == Name::from_string(&format!("{name}.rec"))),
            "missing actual recursor"
        );
        for recursor in recursors {
            recursor.validate_metadata()?;
            strict_root(spec, &recursor.name)?;
        }
    }
    strict_root(spec, &root)
}

fn spine(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprKind::App(function, argument) = head.kind() {
        args.push(argument.as_ref());
        head = function.as_ref();
    }
    args.reverse();
    (head, args)
}

pub(super) fn original_red(
    spec: &Specification,
    row: &Row,
    event: &trace::Event,
) -> Result<(), String> {
    require!(
        !event.accepted && !event.exhausted && event.absent_before,
        "RED did not finish as a refusal"
    );
    let SurfaceDecl::Def {
        name,
        binders,
        ty: Some(ty),
        val,
        ..
    } = parse_decl_exact(&row.source).map_err(|e| e.to_string())?
    else {
        return Err("RED is not original explicit def".into());
    };
    require!(
        binders.is_empty(),
        "RED must remain the original closed declaration"
    );
    let ts = ty.span();
    let vs = val.span();
    let goal = spec
        .elaborate_source(&row.source[ts.start..ts.end], "original RED goal")
        .map_err(|e| e.to_string())?;
    let proof = spec
        .elaborate_source(&row.source[vs.start..vs.end], "original RED reflexivity")
        .map_err(|e| e.to_string())?;
    let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    require!(
        tc.infer_sort(&goal)
            .map_err(|e| format!("{e:?}"))?
            .is_zero(),
        "RED goal is not a proposition"
    );
    let inferred = tc.infer_type(&proof).map_err(|e| format!("{e:?}"))?;
    let (eq, endpoints) = spine(&goal);
    let (refl, refl_args) = spine(&proof);
    require!(
        matches!(eq.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Eq"))
            && endpoints.len() == 3,
        "original goal is not exact homogeneous Eq"
    );
    require!(
        matches!(refl.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Eq.refl"))
            && refl_args.len() == 2,
        "original value is not exact reflexivity"
    );
    require!(
        tc.is_def_eq(endpoints[0], refl_args[0])
            && tc.is_def_eq(endpoints[2], refl_args[1])
            && !tc.is_def_eq(endpoints[1], endpoints[2]),
        "original endpoint/reflexivity cause changed"
    );
    let error = match tc.check_type(&proof, &goal) {
        Err(error) => error,
        Ok(()) => return Err("independent replay accepted original false reflexivity".into()),
    };
    let clean_kernel::tc::TypeError::TypeMismatch {
        expected,
        inferred: actual,
        ..
    } = &error
    else {
        return Err(format!("unrelated strict replay failure: {error:?}"));
    };
    require!(
        tc.is_def_eq(expected, &goal) && tc.is_def_eq(actual, &inferred),
        "wrong mismatch location/cause"
    );
    require!(
        !tc.heartbeat_spent() && !clean_kernel::tc::declaration_budget_exhausted(),
        "semantic diagnostic exhausted heartbeat or declaration budget"
    );
    require!(
        spec.env().get_const(name.name()).is_none()
            && spec.get_definition(&name.name().to_string()).is_none(),
        "original RED name became resident"
    );
    require!(
        error.location().is_none(),
        "independent mismatch is not at the unlabelled top level"
    );
    // Ordinary add_decl labels this same top-level error with the declaration.
    // Use public constructors; never widen checker configuration visibility.
    let error = error.with_location(Some(Box::new(
        clean_kernel::tc::ExprLocation::with_decl_name(name.name().clone()),
    )));
    // The normal API's observed error must bind to this exact top-level error.
    // No guessed or pre-filled receipt. A different current diagnostic remains
    // a qualification loss and is printed for an owner to investigate.
    match event.elaborator_error.as_ref() {
        Some(ElabError::KernelCheckFailed {
            name: failed,
            detail,
        }) if failed == name.name() && detail == &error.to_string() => Ok(()),
        _ => Err(format!(
            "UNQUALIFIED original RED diagnostic; actual={:?}; independently replayed={error:?}",
            event.elaborator_error
        )),
    }
}

pub(super) fn replay_budget(check: impl FnOnce() -> Result<(), String>) -> Result<(), String> {
    decl_budget::with_spec_declaration_budget(|| {
        decl_budget::begin_declaration();
        Ok(check())
    })
    .map_err(|e| e.to_string())?
}

pub(super) fn cost_coverage(costs: &[(&str, usize, String)]) -> Result<(), String> {
    require!(costs.len() == 83, "missing cost row");
    let expected: Vec<_> = [("F1", identity::F1), ("S1a", identity::S1A)]
        .into_iter()
        .flat_map(|(table, ids)| {
            ids.iter()
                .enumerate()
                .map(move |(index, (id, _))| (table, index, (*id).to_owned()))
        })
        .collect();
    require!(
        costs == expected,
        "wrong cost table/index/ID/order or duplicate cost row"
    );
    Ok(())
}

#[test]
fn direct_json_projection_matches_the_existing_shallow_projection() {
    let mut env = clean_kernel::Environment::new();
    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("snapshotShallow"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: true,
    })
    .expect("ordinary checked shallow definition");
    let before = (env.generation(), env.checker_settings());
    let text = env.to_json().expect("existing JSON projection");
    let parsed: serde_json::Value = serde_json::from_str(&text).expect("shallow JSON");
    let direct = env.json_observation();
    assert_eq!(
        serde_json::to_value(&direct).expect("shallow projection"),
        parsed
    );
    assert_eq!(direct, env.json_observation());
    let mut changed = direct.clone();
    let entry = changed
        .constants
        .iter_mut()
        .find(|entry| entry.name == Name::from_string("snapshotShallow"))
        .expect("the exact checked root");
    assert!(entry.value.take().is_some());
    assert_ne!(changed, direct, "the captured value cannot disappear");
    assert_eq!((env.generation(), env.checker_settings()), before);
}

#[test]
fn direct_json_projection_preserves_checked_deep_terms_without_parser_changes() {
    let mut env = clean_kernel::Environment::new();
    let name = Name::from_string("snapshotDeep");
    let original_constants = env.constants().count();
    let mut ty = Expr::type_();
    let mut value = Expr::prop();
    for _ in 0..160 {
        ty = Expr::pi(clean_kernel::BinderInfo::Default, Expr::type_(), ty);
        value = Expr::lam(clean_kernel::BinderInfo::Default, Expr::type_(), value);
    }
    env.add_decl(clean_kernel::Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: ty,
        value: value.clone(),
        is_reducible: true,
    })
    .expect("ordinary kernel checks the exact deep definition");
    assert_eq!(
        env.declaration_verification(&name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    let before = (env.generation(), env.checker_settings());
    let text = env.to_json().expect("existing deep serialization succeeds");
    let error = serde_json::from_str::<serde_json::Value>(&text)
        .expect_err("ordinary parser retains its default depth refusal");
    assert!(error.is_syntax());
    assert!(error.to_string().starts_with("recursion limit exceeded"));
    let direct = env.json_observation();
    assert_eq!(direct.constants.len(), original_constants + 1);
    let named: Vec<_> = direct
        .constants
        .iter()
        .filter(|entry| entry.name == name)
        .collect();
    assert_eq!(named.len(), 1);
    let projected = named[0].value.as_ref().expect("exact checked value");
    assert_eq!(projected, &value);
    let stored = env
        .get_const(&name)
        .and_then(|entry| entry.value.as_ref())
        .expect("actual checked root");
    match (projected.kind(), stored.kind()) {
        (ExprKind::Lam(_, a_ty, a_body), ExprKind::Lam(_, b_ty, b_body)) => {
            assert!(std::sync::Arc::ptr_eq(a_ty, b_ty));
            assert!(std::sync::Arc::ptr_eq(a_body, b_body));
        }
        _ => panic!("the exact deep lambda structure is retained"),
    }
    assert_eq!((env.generation(), env.checker_settings()), before);
}
