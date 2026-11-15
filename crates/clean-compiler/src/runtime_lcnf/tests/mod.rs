//! Split from a single 1448-line `tests.rs` on 2026-09-14. The file crossed
//! the 1000-line paragon threshold when the typed-runtime importer merge
//! landed; the helpers and the first half stay here, the rest is `part_two`.
//! Splitting a test module is API-neutral, which is why this file was chosen
//! over `clean-olean`'s `load_parse.rs` (production code, same crossing).
//! Synthetic typing controls and mandatory-input actual captured-body controls.
//! The test-only index constructor deliberately permits decoded-field mutation;
//! the public constructor always runs the raw capture API itself.

use super::*;
use crate::lcnf::{Arg, Code, DeclValue, LetValue};
use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, Level, Multiplicity, Name};
use clean_olean::import::runtime::*;
use clean_olean::module::{ConstantKind, DefinitionSafety};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

fn row(
    name: Name,
    kind: ConstantKind,
    ty: Expr,
    body: RuntimeBody,
    family: RuntimeFamily,
    dependencies: Vec<Name>,
) -> RuntimeDeclaration {
    RuntimeDeclaration {
        name: name.clone(),
        kind,
        level_params: vec![],
        declaration_safety: Some(DefinitionSafety::Safe),
        hints: None,
        mutual_declarations: Some(vec![name]),
        type_: Ok(ty),
        body,
        family,
        dependencies: dependencies.into_iter().collect(),
        represented_fields_complete: true,
        issues: vec![],
    }
}

fn modeled_context(names: &[Name]) -> RuntimeContext {
    let data = Name::from_string("Data");
    let zero = data.clone().str("zero");
    let mut declarations = vec![
        row(
            data.clone(),
            ConstantKind::Inductive,
            Expr::sort(Level::succ(Level::zero())),
            RuntimeBody::NoStoredValueForKind,
            RuntimeFamily::Inductive {
                all: vec![data.clone()],
                constructors: vec![zero.clone()],
                num_params: 0,
                num_indices: 0,
                num_nested: Some(0),
                is_nested: false,
                is_recursive: false,
                is_unsafe: false,
                is_reflexive: false,
            },
            vec![data.clone(), zero.clone()],
        ),
        row(
            zero,
            ConstantKind::Constructor,
            Expr::const_(data.clone(), vec![]),
            RuntimeBody::NoStoredValueForKind,
            RuntimeFamily::Constructor {
                inductive: data.clone(),
                index: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            },
            vec![data.clone()],
        ),
    ];
    for name in names {
        let ty = Expr::const_(data.clone(), vec![]);
        declarations.push(row(
            name.clone(),
            ConstantKind::Definition,
            Expr::pi(BinderInfo::Default, ty.clone(), ty.clone()),
            RuntimeBody::Stored(Ok(Expr::lam(BinderInfo::Default, ty, Expr::bvar(0)))),
            RuntimeFamily::None,
            vec![data.clone(), name.clone()],
        ));
    }
    RuntimeContext::index(vec![RuntimeModuleCapture {
        selected: RuntimeOleanPart::Private,
        parts: vec![RuntimePartExtraction {
            identity: RuntimePartIdentity {
                part: RuntimeOleanPart::Private,
                label: "synthetic-unit-control".into(),
                byte_count: 0,
                blake3: [0; 32],
            },
            captured: RuntimeOleanInput {
                label: "synthetic-unit-control".into(),
                bytes: Vec::new().into(),
            },
            borrowed_prefix: vec![],
            source_row_count: Some(declarations.len()),
            rows: declarations
                .into_iter()
                .enumerate()
                .map(|(index, declaration)| RuntimeDeclarationRow {
                    index,
                    declaration: Ok(declaration),
                })
                .collect(),
            error: None,
        }],
    }])
}

fn mutate(
    context: &RuntimeContext,
    name: &Name,
    action: impl FnOnce(&mut RuntimeDeclaration),
) -> RuntimeContext {
    let mut modules = context.modules.clone();
    let &(m, p, r) = context.names.get(name).unwrap().first().unwrap();
    action(modules[m].parts[p].rows[r].declaration.as_mut().unwrap());
    RuntimeContext::index(modules)
}

#[test]
fn identity_lowers_without_environment_or_placeholder() {
    let name = Name::from_string("run");
    let context = modeled_context(std::slice::from_ref(&name));
    let output = context
        .lower_definition(&name, RuntimeLimits::default())
        .unwrap();
    assert_eq!(output.declaration.name, name);
    assert_eq!(output.declaration.params.len(), 1);
    assert!(
        matches!(output.declaration.body,DeclValue::Code(ref code) if **code==Code::Return(output.declaration.params[0].fvar_id))
    );
    assert_eq!(output.dependencies.len(), 3);
}

#[test]
fn display_twins_resolve_independently_and_duplicates_refuse() {
    let names = [Name::from_string("Run.leaf"), Name::anon().str("Run.leaf")];
    let context = modeled_context(&names);
    for name in &names {
        assert_eq!(
            context
                .lower_definition(name, RuntimeLimits::default())
                .unwrap()
                .declaration
                .name,
            *name
        );
    }
    let duplicate =
        RuntimeContext::index(vec![context.modules[0].clone(), context.modules[0].clone()]);
    assert!(matches!(
        duplicate.lower_definition(&names[0], RuntimeLimits::default()),
        Err(RuntimeLowerError::Ambiguous(_))
    ));
}

#[test]
fn missing_header_and_selected_part_never_fall_back() {
    let name = Name::from_string("run");
    let mut context = modeled_context(std::slice::from_ref(&name));
    context.catalog.remove(&Name::from_string("Data"));
    assert!(matches!(
        context.lower_definition(&name, RuntimeLimits::default()),
        Err(RuntimeLowerError::Missing(_))
    ));
    let mut modules = modeled_context(std::slice::from_ref(&name)).modules;
    modules[0].selected = RuntimeOleanPart::Base;
    let missing = RuntimeContext::index(modules);
    assert!(matches!(
        missing.lower_definition(&name, RuntimeLimits::default()),
        Err(RuntimeLowerError::Capture(_))
    ));
}

#[test]
fn unknown_row_and_population_mismatch_remain_visible() {
    let name = Name::from_string("run");
    for mode in 0..3 {
        let mut modules = modeled_context(std::slice::from_ref(&name)).modules;
        let part = &mut modules[0].parts[0];
        match mode {
            0 => part.rows[0].declaration = Err("bad exact identity".into()),
            1 => part.rows[0].index = 9,
            _ => part.source_row_count = None,
        }
        let context = RuntimeContext::index(modules);
        assert_eq!(context.captures()[0].parts[0].rows.len(), 3);
        assert!(matches!(
            context.lower_definition(&name, RuntimeLimits::default()),
            Err(RuntimeLowerError::Capture(_))
        ));
    }
}

#[test]
fn wrong_binder_universe_and_body_refuse() {
    let name = Name::from_string("run");
    let original = modeled_context(std::slice::from_ref(&name));
    for body in [
        Expr::bvar(0),
        Expr::fvar(clean_kernel::FVarId::new(0)),
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        ),
        Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Data"), vec![Level::zero()]),
            Expr::bvar(0),
        ),
        Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Data"),
            Expr::sort(Level::param(Name::from_string("missing"))),
        ),
    ] {
        let changed = mutate(&original, &name, |row| {
            row.body = RuntimeBody::Stored(Ok(body))
        });
        assert!(changed
            .lower_definition(&name, RuntimeLimits::default())
            .is_err());
    }
}

#[test]
fn family_metadata_and_missing_body_are_not_favorable_labels() {
    let name = Name::from_string("run");
    let context = modeled_context(std::slice::from_ref(&name));
    let zero = Name::from_string("Data.zero");
    let bad = mutate(&context, &zero, |row| {
        if let RuntimeFamily::Constructor { num_fields, .. } = &mut row.family {
            *num_fields = 1
        }
    });
    assert!(matches!(
        bad.lower_definition(&name, RuntimeLimits::default()),
        Err(RuntimeLowerError::Family { .. })
    ));
    let stub = mutate(&context, &name, |row| {
        row.body = RuntimeBody::MissingRequiredValue
    });
    assert!(matches!(
        stub.lower_definition(&name, RuntimeLimits::default()),
        Err(RuntimeLowerError::MissingBody(_))
    ));
}

#[test]
fn every_resource_bound_is_an_explicit_error() {
    let name = Name::from_string("run");
    let context = modeled_context(std::slice::from_ref(&name));
    for limits in [
        RuntimeLimits {
            steps: 0,
            ..RuntimeLimits::default()
        },
        RuntimeLimits {
            depth: 0,
            ..RuntimeLimits::default()
        },
        RuntimeLimits {
            declarations: 0,
            ..RuntimeLimits::default()
        },
    ] {
        assert!(matches!(
            context.lower_definition(&name, limits),
            Err(RuntimeLowerError::Resource(_))
        ));
    }
}

#[test]
fn unrepresented_binder_multiplicities_refuse_even_when_header_and_body_agree() {
    let name = Name::from_string("run");
    let context = modeled_context(std::slice::from_ref(&name));
    for mult in [Multiplicity::Zero, Multiplicity::One, Multiplicity::Many] {
        for mode in 0..3 {
            let changed = mutate(&context, &name, |row| {
                let binder = BinderData::new(BinderInfo::Default, mult);
                if mode != 0 {
                    row.type_ = Ok(Expr::pi(
                        binder,
                        Expr::const_str("Data"),
                        Expr::const_str("Data"),
                    ));
                }
                if mode != 1 {
                    row.body = RuntimeBody::Stored(Ok(Expr::lam(
                        binder,
                        Expr::const_str("Data"),
                        Expr::bvar(0),
                    )));
                }
            });
            let result = changed.lower_definition(&name, RuntimeLimits::default());
            if mult == Multiplicity::Many {
                assert!(result.is_ok());
            } else {
                assert!(matches!(
                    result,
                    Err(RuntimeLowerError::Unsupported(
                        "runtime binder multiplicity"
                    ))
                ));
            }
        }
    }
}

#[test]
fn bare_and_partial_constructors_are_closures_not_incomplete_allocations() {
    let name = Name::from_string("make");
    let context = modeled_context(std::slice::from_ref(&name));
    let pair = Name::from_string("Data.pair");
    let data = Expr::const_str("Data");
    let pair_type = Expr::pi(
        BinderInfo::Default,
        data.clone(),
        Expr::pi(BinderInfo::Default, data.clone(), data.clone()),
    );
    let context = mutate(&context, &Name::from_string("Data"), |row| {
        if let RuntimeFamily::Inductive { constructors, .. } = &mut row.family {
            constructors.push(pair.clone());
        }
        row.dependencies.insert(pair.clone());
    });
    let mut modules = context.modules;
    let part = &mut modules[0].parts[0];
    part.rows.push(RuntimeDeclarationRow {
        index: part.rows.len(),
        declaration: Ok(row(
            pair.clone(),
            ConstantKind::Constructor,
            pair_type.clone(),
            RuntimeBody::NoStoredValueForKind,
            RuntimeFamily::Constructor {
                inductive: Name::from_string("Data"),
                index: 1,
                num_params: 0,
                num_fields: 2,
                is_unsafe: false,
            },
            vec![Name::from_string("Data")],
        )),
    });
    part.source_row_count = Some(part.rows.len());
    let context = RuntimeContext::index(modules);
    for supplied in 0..=2 {
        let mut body = Expr::const_(pair.clone(), vec![]);
        let mut ty = pair_type.clone();
        for _ in 0..supplied {
            body = Expr::app(body, Expr::const_str("Data.zero"));
            let ExprKind::Pi(_, _, result) = ty.kind() else {
                panic!()
            };
            ty = result.as_ref().clone();
        }
        let context = mutate(&context, &name, |row| {
            row.body = RuntimeBody::Stored(Ok(body));
            row.type_ = Ok(ty);
            row.dependencies.insert(pair.clone());
        });
        let output = context
            .lower_definition(&name, RuntimeLimits::default())
            .unwrap();
        let DeclValue::Code(code) = output.declaration.body else {
            panic!()
        };
        let mut code = code.as_ref();
        let mut supplied_ids = Vec::new();
        for _ in 0..supplied {
            let Code::Let(value, rest) = code else {
                panic!("supplied value must stay outside eta closure")
            };
            assert!(
                matches!(&value.value,LetValue::Ctor{name,args,..} if *name==Name::from_string("Data.zero") && args.is_empty())
            );
            supplied_ids.push(value.fvar_id);
            code = rest;
        }
        let mut expected = supplied_ids.into_iter().map(Arg::FVar).collect::<Vec<_>>();
        if supplied < 2 {
            let Code::Fun(fun, rest) = code else {
                panic!("constructor value needs a closure")
            };
            assert_eq!(fun.params.len(), 2 - supplied);
            assert_eq!(**rest, Code::Return(fun.fvar_id));
            expected.extend(fun.params.iter().map(|p| Arg::FVar(p.fvar_id)));
            code = &fun.body;
        }
        let Code::Let(value, rest) = code else {
            panic!()
        };
        assert!(
            matches!(&value.value,LetValue::Ctor{name,args,..} if *name==pair && *args==expected)
        );
        assert_eq!(**rest, Code::Return(value.fvar_id));
    }
}

#[test]
fn mutually_recursive_bodies_are_not_reported_as_acyclic() {
    let a = Name::from_string("Run.a");
    let b = Name::from_string("Run.b");
    let original = modeled_context(&[a.clone(), b.clone()]);
    let mut context = original.clone();
    for (name, callee) in [(&a, &b), (&b, &a)] {
        context = mutate(&context, name, |row| {
            row.body = RuntimeBody::Stored(Ok(Expr::lam(
                BinderInfo::Default,
                Expr::const_str("Data"),
                Expr::app(Expr::const_(callee.clone(), vec![]), Expr::bvar(0)),
            )));
            row.dependencies.insert(callee.clone());
            row.mutual_declarations = Some(vec![a.clone(), b.clone()]);
        });
    }
    for name in [&a, &b] {
        assert!(
            context
                .lower_definition(name, RuntimeLimits::default())
                .unwrap()
                .declaration
                .recursive
        );
    }
    let broken = mutate(&context, &b, |row| {
        row.body = original.declaration(&b).unwrap().body.clone();
    });
    for name in [&a, &b] {
        assert!(
            !broken
                .lower_definition(name, RuntimeLimits::default())
                .unwrap()
                .declaration
                .recursive
        );
    }
}

fn captured_input(path: &Path) -> RuntimeOleanInput {
    RuntimeOleanInput {
        label: path.to_string_lossy().into_owned(),
        bytes: std::fs::read(path).unwrap().into(),
    }
}
fn captured_module(base: &Path) -> RuntimeModuleInput {
    let server = base.with_extension("olean.server");
    let private = base.with_extension("olean.private");
    assert!(
        server.is_file() && private.is_file(),
        "all pinned modern fixture parts required"
    );
    RuntimeModuleInput {
        base: captured_input(base),
        server: Some(captured_input(&server)),
        private: Some(captured_input(&private)),
        selected: RuntimeOleanPart::Private,
    }
}
/// The two module inputs every `actual_*` test captures, resolved once per
/// test process: the base `.olean` of the `runtime_probe` fixture family
/// (`crates/clean-olean/tests/fixtures/lean/<pin>/runtime_probe/`, compiled by
/// the pinned Lean into clean-olean's content-addressed cache) and the pinned
/// toolchain's own `Init/Prelude.olean`; `captured_module` derives the
/// `.olean.server` / `.olean.private` companions of each.
///
/// Fail-closed by design: both resolvers PANIC when the repository-pinned
/// toolchain (`lean-toolchain`, v4.30.0-rc2) is not installed, so a box without
/// it FAILS these tests instead of passing over zero test lines. No environment
/// variable is consulted — the previous `CLEAN_RUNTIME_LCNF_FIXTURE` /
/// `CLEAN_RUNTIME_LCNF_PRELUDE` readers had no producer anywhere in the tree.
fn pinned_inputs() -> &'static (PathBuf, PathBuf) {
    static INPUTS: OnceLock<(PathBuf, PathBuf)> = OnceLock::new();
    INPUTS.get_or_init(|| {
        let probe = clean_olean::test_support::compiled_fixture_dir("runtime_probe")
            .join("RuntimeProbe.olean");
        let prelude = clean_olean::pinned_lean_lib_path()
            .expect(clean_olean::test_support::PINNED_LEAN_REQUIRED)
            .join("Init")
            .join("Prelude.olean");
        (probe, prelude)
    })
}
/// Capture `[RuntimeProbe, Init.Prelude]` through the public runtime reader.
/// `pub(super)` so `emission_tests` (a sibling under `runtime_lcnf`) shares the
/// same compiled fixture instead of carrying a second resolver.
pub(super) fn actual_context() -> RuntimeContext {
    let (probe, prelude) = pinned_inputs();
    RuntimeContext::capture(vec![captured_module(probe), captured_module(prelude)])
}
/// Per-part constant counts of the RuntimeProbe triple as the INDEPENDENT
/// upstream reader sees them (`tests/fixtures/lean/<pin>/oracle/DumpOlean.lean`
/// run by the pinned Lean, one `parts[i].constants` array per part in argument
/// order). This is the value Clean's runtime reader is held to below — derived
/// from the same bytes, never typed. Measured 2026-09-15 on the committed
/// family (`runtime_probe/README.md`, § Constant roster): 24 / 24 / 25, the
/// private part adding exactly the `count` matcher.
fn oracle_constant_counts() -> Vec<usize> {
    let (probe, _) = pinned_inputs();
    let parts = [
        probe.clone(),
        probe.with_extension("olean.server"),
        probe.with_extension("olean.private"),
    ];
    let args: Vec<&str> = parts
        .iter()
        .map(|part| part.to_str().expect("utf-8 fixture path"))
        .collect();
    let dump = clean_olean::test_support::run_oracle(&args);
    dump["parts"]
        .as_array()
        .expect("oracle `parts` array")
        .iter()
        .map(|part| {
            part["constants"]
                .as_array()
                .expect("oracle `constants` array")
                .len()
        })
        .collect()
}
/// The names of the rows a captured part decoded, for roster comparisons
/// between parts of one module.
fn row_names(part: &RuntimePartExtraction) -> BTreeSet<Name> {
    part.rows
        .iter()
        .filter_map(|row| row.declaration.as_ref().ok())
        .map(|declaration| declaration.name.clone())
        .collect()
}

fn calls(code: &Code, out: &mut BTreeSet<Name>) {
    match code {
        Code::Let(decl, rest) => {
            if let LetValue::Const { name, .. } | LetValue::Ctor { name, .. } = &decl.value {
                out.insert(name.clone());
            }
            calls(rest, out)
        }
        Code::Fun(decl, rest) => {
            calls(&decl.body, out);
            calls(rest, out)
        }
        _ => {}
    }
}

#[test]
fn actual_partial_helper_lowers_stored_body_and_keeps_exact_calls() {
    let context = actual_context();
    assert!(
        context.capture_errors().is_empty(),
        "{:?}",
        context.capture_errors()
    );
    let matcher = Name::anon()
        .str("_private")
        .str("RuntimeProbe")
        .num(0)
        .str("RuntimeProbe")
        .str("count")
        .str("match_1");
    // Row population per part, held to the independent upstream reader rather
    // than to a typed literal (the lost original's `[24, 24, 25]` is what the
    // oracle measures on the committed family; a fixture edit moves both).
    let probe_parts = &context.captures()[0].parts;
    assert_eq!(
        probe_parts.iter().map(|p| p.rows.len()).collect::<Vec<_>>(),
        oracle_constant_counts()
    );
    // Shape, number-free: the server part re-exports the base roster, and the
    // private part adds exactly one constant — the `match` compiler's matcher,
    // which the module system keeps out of the exported parts.
    let [base, server, private] = probe_parts.as_slice() else {
        panic!("RuntimeProbe must capture base, server and private parts")
    };
    let (base, server, private) = (row_names(base), row_names(server), row_names(private));
    assert_eq!(base, server);
    assert!(base.is_subset(&private));
    assert_eq!(
        private.difference(&base).cloned().collect::<Vec<_>>(),
        std::slice::from_ref(&matcher)
    );
    let name = Name::from_string("RuntimeProbe.count._unsafe_rec");
    assert_eq!(
        context.declaration(&name).unwrap().declaration_safety,
        Some(DefinitionSafety::Partial)
    );
    let output = context
        .lower_definition(&name, RuntimeLimits::default())
        .unwrap();
    assert!(output.declaration.recursive);
    let mut actual = BTreeSet::new();
    let DeclValue::Code(code) = &output.declaration.body else {
        panic!("no fabricated extern")
    };
    calls(code, &mut actual);
    assert!(actual.contains(&name) && actual.contains(&matcher));
    // Exact captured branch dataflow, not merely the presence of favorable
    // names: zero allocates zero; succ calls this root on its bound predecessor
    // and wraps that result; the exact matcher receives those two closures.
    assert_eq!(output.declaration.params.len(), 1);
    let Code::Fun(zero_branch, rest) = code.as_ref() else {
        panic!("zero branch closure")
    };
    assert_eq!(zero_branch.params.len(), 1);
    assert_eq!(zero_branch.params[0].ty, Expr::const_str("Unit"));
    let Code::Let(zero, zero_return) = zero_branch.body.as_ref() else {
        panic!()
    };
    assert!(
        matches!(&zero.value,LetValue::Ctor{name,args,levels} if *name==Name::from_string("Unary.zero") && args.is_empty() && levels.is_empty())
    );
    assert_eq!(**zero_return, Code::Return(zero.fvar_id));
    let Code::Fun(succ_branch, rest) = rest.as_ref() else {
        panic!("succ branch closure")
    };
    assert_eq!(succ_branch.params.len(), 1);
    assert_eq!(succ_branch.params[0].ty, Expr::const_str("Unary"));
    let Code::Let(recur, rest_succ) = succ_branch.body.as_ref() else {
        panic!()
    };
    assert!(
        matches!(&recur.value,LetValue::Const{name:callee,args,levels} if *callee==name && *args==vec![Arg::FVar(succ_branch.params[0].fvar_id)] && levels.is_empty())
    );
    let Code::Let(succ, succ_return) = rest_succ.as_ref() else {
        panic!()
    };
    assert!(
        matches!(&succ.value,LetValue::Ctor{name,args,levels} if *name==Name::from_string("Unary.succ") && *args==vec![Arg::FVar(recur.fvar_id)] && levels.is_empty())
    );
    assert_eq!(**succ_return, Code::Return(succ.fvar_id));
    let Code::Let(call, call_return) = rest.as_ref() else {
        panic!()
    };
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Unary"),
        Expr::const_str("Unary"),
    );
    assert!(
        matches!(&call.value,LetValue::Const{name,args,levels} if *name==matcher && *levels==vec![Level::succ(Level::zero())] && *args==vec![Arg::Type(motive),Arg::FVar(output.declaration.params[0].fvar_id),Arg::FVar(zero_branch.fvar_id),Arg::FVar(succ_branch.fvar_id)])
    );
    assert_eq!(**call_return, Code::Return(call.fvar_id));
    assert!(
        actual.contains(&Name::from_string("Unary.zero"))
            && actual.contains(&Name::from_string("Unary.succ"))
    );
    let required: BTreeSet<_> = output.dependencies.iter().map(|r| r.name.clone()).collect();
    for name in [
        "Unary",
        "Unary.rec",
        "Unary.casesOn",
        "Unit",
        "Unit.unit",
        "PUnit",
        "PUnit.unit",
    ] {
        assert!(required.contains(&Name::from_string(name)), "{name}");
    }
    // The root's body lives in the selected private part, whose provenance
    // records the ordered parts extracted before it — base then server. That
    // is a property of the capture order (`extract_olean_runtime_parts`), not
    // a claim that the private rows reach server-owned objects.
    assert!(
        matches!(output.origin.provenance, RuntimeProvenance::Captured { ref borrowed_prefix, ref part, .. }
            if part.part == RuntimeOleanPart::Private
                && borrowed_prefix.iter().map(|p| p.part).collect::<Vec<_>>()
                    == [RuntimeOleanPart::Base, RuntimeOleanPart::Server])
    );
}

#[test]
fn actual_quoted_twin_and_matcher_are_distinct_source_bodies() {
    let context = actual_context();
    let name = Name::anon().str("RuntimeProbe").str("count._unsafe_rec");
    let output = context
        .lower_definition(&name, RuntimeLimits::default())
        .unwrap();
    assert!(!output.declaration.recursive);
    let DeclValue::Code(code) = output.declaration.body else {
        panic!()
    };
    assert_eq!(*code, Code::Return(output.declaration.params[0].fvar_id));
    let matcher = Name::anon()
        .str("_private")
        .str("RuntimeProbe")
        .num(0)
        .str("RuntimeProbe")
        .str("count")
        .str("match_1");
    let result = context
        .lower_definition(&matcher, RuntimeLimits::default())
        .unwrap();
    let DeclValue::Code(code) = result.declaration.body else {
        panic!()
    };
    let mut targets = BTreeSet::new();
    calls(&code, &mut targets);
    assert!(targets.contains(&Name::from_string("Unary.casesOn")));
}

#[test]
fn actual_context_mutations_refuse_without_name_or_body_substitution() {
    let context = actual_context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let matcher = Name::anon()
        .str("_private")
        .str("RuntimeProbe")
        .num(0)
        .str("RuntimeProbe")
        .str("count")
        .str("match_1");
    let mut absent = context.clone();
    absent.catalog.remove(&matcher);
    assert!(matches!(
        absent.lower_definition(&root, RuntimeLimits::default()),
        Err(RuntimeLowerError::Missing(_))
    ));
    for name in [matcher, root.clone()] {
        for mode in 0..3 {
            let changed = mutate(&context, &name, |row| match mode {
                0 => row.body = RuntimeBody::Stored(Ok(Expr::bvar(0))),
                1 => row.level_params.push(Name::from_string("extraUniverse")),
                _ => row.type_ = Ok(Expr::sort(Level::zero())),
            });
            assert!(changed
                .lower_definition(&root, RuntimeLimits::default())
                .is_err());
        }
    }
    // A same-type changed body is actually lowered; partial safety or the
    // generated helper's spelling never selects a hard-coded recursive body.
    let changed = mutate(&context, &root, |row| {
        row.body = RuntimeBody::Stored(Ok(Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Unary"),
            Expr::bvar(0),
        )));
    });
    let output = changed
        .lower_definition(&root, RuntimeLimits::default())
        .unwrap();
    assert!(!output.declaration.recursive);
    let DeclValue::Code(code) = output.declaration.body else {
        panic!()
    };
    assert_eq!(*code, Code::Return(output.declaration.params[0].fvar_id));
}

#[test]
fn runtime_ir_identity_has_exact_layout_and_no_erasure_escape() {
    use crate::ir::{IRArg, IRBody, IRType, VarId};
    let name = Name::from_string("run");
    let context = modeled_context(std::slice::from_ref(&name));
    let output = context.lower_ir(&name, RuntimeLimits::default()).unwrap();
    assert_eq!(output.rows.len(), 3);
    let row = output.rows.iter().find(|r| r.origin.name == name).unwrap();
    let RuntimeIrStatus::Lowered(decls) = &row.status else {
        panic!("{:?}", row.status)
    };
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name, name);
    assert_eq!(decls[0].params, vec![(VarId(0), IRType::Object)]);
    assert_eq!(decls[0].return_type, IRType::Object);
    assert_eq!(decls[0].body, IRBody::Ret(IRArg::Var(VarId(0))));
    for mult in [Multiplicity::Zero, Multiplicity::One] {
        let changed = mutate(&context, &name, |r| {
            let b = BinderData::new(BinderInfo::Default, mult);
            r.type_ = Ok(Expr::pi(
                b,
                Expr::const_str("Data"),
                Expr::const_str("Data"),
            ));
            r.body = RuntimeBody::Stored(Ok(Expr::lam(b, Expr::const_str("Data"), Expr::bvar(0))));
        });
        let output = changed.lower_ir(&name, RuntimeLimits::default()).unwrap();
        assert!(matches!(
            &output
                .rows
                .iter()
                .find(|r| r.origin.name == name)
                .unwrap()
                .status,
            RuntimeIrStatus::Refused(RuntimeLowerError::Unsupported(
                "runtime binder multiplicity"
            ))
        ));
    }
}

mod part_two;
