//! The second half of `runtime_lcnf`'s test module — see `mod.rs` for why
//! it is split. Helpers (`row`, `modeled_context`, `mutate`) and the shared
//! imports come from the parent through the glob below.

use super::*;

#[test]
fn runtime_ir_never_defaults_unknown_or_proposition_layout_to_object() {
    let name = Name::from_string("run");
    let context = modeled_context(std::slice::from_ref(&name));
    let prop = mutate(&context, &Name::from_string("Data"), |r| {
        r.type_ = Ok(Expr::sort(Level::zero()))
    });
    let output = prop.lower_ir(&name, RuntimeLimits::default()).unwrap();
    assert!(matches!(
        &output
            .rows
            .iter()
            .find(|r| r.origin.name == name)
            .unwrap()
            .status,
        RuntimeIrStatus::Refused(_)
    ));
    let missing = mutate(&context, &name, |r| {
        r.type_ = Ok(Expr::const_str("Unknown"))
    });
    let output = missing.lower_ir(&name, RuntimeLimits::default()).unwrap();
    assert!(matches!(
        &output
            .rows
            .iter()
            .find(|r| r.origin.name == name)
            .unwrap()
            .status,
        RuntimeIrStatus::Refused(_)
    ));
}

#[test]
fn runtime_ir_alias_function_spines_keep_bare_and_partial_arity() {
    use crate::ir::{IRBody, IRExpr};
    let root = Name::from_string("returnFunction");
    let leaf = Name::from_string("leaf");
    let alias = Name::from_string("Alias");
    let context = modeled_context(&[root.clone(), leaf.clone()]);
    let data = Expr::const_str("Data");
    let mut modules = context.modules;
    let part = &mut modules[0].parts[0];
    part.rows.push(RuntimeDeclarationRow {
        index: part.rows.len(),
        declaration: Ok(row(
            alias.clone(),
            ConstantKind::Definition,
            Expr::sort(Level::succ(Level::zero())),
            RuntimeBody::Stored(Ok(Expr::pi(
                BinderInfo::Default,
                data.clone(),
                data.clone(),
            ))),
            RuntimeFamily::None,
            vec![Name::from_string("Data")],
        )),
    });
    part.source_row_count = Some(part.rows.len());
    let context = RuntimeContext::index(modules);
    for supplied in 0..=1 {
        let context = mutate(&context, &leaf, |r| {
            r.type_ = Ok(if supplied == 0 {
                Expr::const_(alias.clone(), vec![])
            } else {
                Expr::pi(
                    BinderInfo::Default,
                    data.clone(),
                    Expr::const_(alias.clone(), vec![]),
                )
            });
            let id = Expr::lam(BinderInfo::Default, data.clone(), Expr::bvar(0));
            r.body = RuntimeBody::Stored(Ok(if supplied == 0 {
                id
            } else {
                Expr::lam(BinderInfo::Default, data.clone(), id)
            }));
            r.dependencies.insert(alias.clone());
        });
        let context = mutate(&context, &root, |r| {
            r.type_ = Ok(Expr::const_(alias.clone(), vec![]));
            let f = Expr::const_(leaf.clone(), vec![]);
            r.body = RuntimeBody::Stored(Ok(if supplied == 0 {
                f
            } else {
                Expr::app(f, Expr::const_str("Data.zero"))
            }));
            r.dependencies.insert(alias.clone());
            r.dependencies.insert(leaf.clone());
        });
        let output = context.lower_ir(&root, RuntimeLimits::default()).unwrap();
        let row = output.rows.iter().find(|r| r.origin.name == root).unwrap();
        let RuntimeIrStatus::Lowered(decls) = &row.status else {
            panic!("{:?}", row.status)
        };
        let mut body = &decls[0].body;
        if supplied == 1 {
            let IRBody::VDecl { rest, .. } = body else {
                panic!()
            };
            body = rest;
        }
        let IRBody::VDecl { value, .. } = body else {
            panic!()
        };
        assert!(
            matches!(value,IRExpr::PartialApply{fn_id,arity,args} if fn_id.0==leaf && *arity==1+supplied && args.len()==supplied as usize)
        );
    }
}

#[test]
fn runtime_ir_function_returning_definition_needs_staged_call_not_header_arity() {
    let caller = Name::from_string("caller");
    let value = Name::from_string("functionValue");
    let leaf = Name::from_string("leaf");
    let context = modeled_context(&[caller.clone(), value.clone(), leaf.clone()]);
    let context = mutate(&context, &value, |r| {
        r.body = RuntimeBody::Stored(Ok(Expr::const_(leaf.clone(), vec![])));
        r.dependencies.insert(leaf.clone());
    });
    let context = mutate(&context, &caller, |r| {
        r.body = RuntimeBody::Stored(Ok(Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Data"),
            Expr::app(Expr::const_(value.clone(), vec![]), Expr::bvar(0)),
        )));
        r.dependencies.insert(value.clone());
    });
    context
        .lower_definition(&caller, RuntimeLimits::default())
        .unwrap();
    let result = context.lower_ir(&caller, RuntimeLimits::default()).unwrap();
    assert!(matches!(
        &result
            .rows
            .iter()
            .find(|r| r.origin.name == caller)
            .unwrap()
            .status,
        RuntimeIrStatus::Refused(RuntimeLowerError::Unsupported(
            "runtime function-value ABI needs staged application"
        ))
    ));
}

#[test]
fn actual_partial_runtime_ir_retains_calls_tags_and_unresolved_rows() {
    use crate::ir::{IRBody, IRExpr};
    fn expressions<'a>(body: &'a IRBody, out: &mut Vec<&'a IRExpr>) {
        if let IRBody::VDecl { value, rest, .. } = body {
            out.push(value);
            expressions(rest, out);
        }
    }
    let context = actual_context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let output = context.lower_ir(&root, RuntimeLimits::default()).unwrap();
    assert_eq!(
        output.rows.len(),
        context
            .dependency_closure(&root, RuntimeLimits::default())
            .unwrap()
            .len()
    );
    let row = output.rows.iter().find(|r| r.origin.name == root).unwrap();
    let RuntimeIrStatus::Lowered(decls) = &row.status else {
        panic!("{:?}", row.status)
    };
    assert_eq!(decls.len(), 4);
    assert_eq!(decls[0].name, root);
    let mut exprs = Vec::new();
    for decl in decls {
        expressions(&decl.body, &mut exprs);
    }
    let matcher = Name::anon()
        .str("_private")
        .str("RuntimeProbe")
        .num(0)
        .str("RuntimeProbe")
        .str("count")
        .str("match_1");
    assert_eq!(row.specializations.len(), 1);
    let spec = &row.specializations[0];
    assert_eq!(spec.source.name, matcher);
    assert_eq!(spec.wrapper.name, Name::from_string("Unary.casesOn"));
    assert_eq!(spec.recursor.name, Name::from_string("Unary.rec"));
    assert_eq!(spec.family.name, Name::from_string("Unary"));
    assert!(exprs.iter().any(
        |e| matches!(e,IRExpr::Apply{fn_id,args} if fn_id.0==spec.generated_name && args.len()==3)
    ));
    assert!(exprs
        .iter()
        .any(|e| matches!(e,IRExpr::Apply{fn_id,args} if fn_id.0==root && args.len()==1)));
    for (name, tag, fields) in [("Unary.zero", 0, 0), ("Unary.succ", 1, 1)] {
        assert!(exprs.iter().any(|e|matches!(e,IRExpr::Ctor{info,args} if info.name==Name::from_string(name) && info.tag==tag && info.num_objects==fields && info.num_scalars==0 && args.len()==fields as usize)));
    }
    assert!(matches!(
        &output
            .rows
            .iter()
            .find(|r| r.origin.name == matcher)
            .unwrap()
            .status,
        RuntimeIrStatus::Refused(_)
    ));
    assert!(matches!(
        &output
            .rows
            .iter()
            .find(|r| r.origin.name == Name::from_string("Unary.rec"))
            .unwrap()
            .status,
        RuntimeIrStatus::Refused(_)
    ));
    // A root body is real IR progress, not a whole-call-graph success signal.
    assert!(output
        .rows
        .iter()
        .any(|r| matches!(r.status, RuntimeIrStatus::Refused(_))));
}

#[test]
fn actual_runtime_ir_quoted_twin_never_borrows_recursive_body() {
    use crate::ir::{IRArg, IRBody, VarId};
    let context = actual_context();
    let quoted = Name::anon().str("RuntimeProbe").str("count._unsafe_rec");
    let output = context.lower_ir(&quoted, RuntimeLimits::default()).unwrap();
    let row = output
        .rows
        .iter()
        .find(|r| r.origin.name == quoted)
        .unwrap();
    let RuntimeIrStatus::Lowered(decls) = &row.status else {
        panic!("{:?}", row.status)
    };
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name, quoted);
    assert_eq!(decls[0].body, IRBody::Ret(IRArg::Var(VarId(0))));
}

// Deliberately small independent interpreter for this diagnostic IR fragment.
// It has no producer shortcuts keyed to names, and a finite fuel refusal; these
// are falsification controls, not a proof of RC/heap/native semantics.
#[derive(Clone, Debug, PartialEq)]
enum IrValue {
    Ctor(u32, Vec<IrValue>),
    Closure(Name, Vec<IrValue>),
}
struct IrEval {
    functions: std::collections::BTreeMap<Name, crate::ir::IRDecl>,
    fuel: usize,
}
impl IrEval {
    fn from_output(output: &RuntimeIrOutput) -> Self {
        let mut functions = std::collections::BTreeMap::new();
        for row in &output.rows {
            if let RuntimeIrStatus::Lowered(decls) = &row.status {
                for decl in decls {
                    crate::to_ir_ext::validate_ir_decl(decl).unwrap();
                    assert!(functions.insert(decl.name.clone(), decl.clone()).is_none());
                }
            }
        }
        Self {
            functions,
            fuel: 10000,
        }
    }
    fn call(&mut self, name: &Name, args: Vec<IrValue>) -> Result<IrValue, &'static str> {
        let decl = self.functions.get(name).cloned().ok_or("missing callee")?;
        if args.len() != decl.params.len() {
            return Err("arity");
        }
        let locals = decl.params.iter().map(|(id, _)| id.0).zip(args).collect();
        self.body(&decl.body, locals)
    }
    fn arg(
        arg: &crate::ir::IRArg,
        locals: &std::collections::BTreeMap<u32, IrValue>,
    ) -> Result<IrValue, &'static str> {
        match arg {
            crate::ir::IRArg::Var(id) => locals.get(&id.0).cloned().ok_or("unbound"),
            _ => Err("erased"),
        }
    }
    fn body(
        &mut self,
        body: &crate::ir::IRBody,
        mut locals: std::collections::BTreeMap<u32, IrValue>,
    ) -> Result<IrValue, &'static str> {
        use crate::ir::{IRBody, IRExpr};
        self.fuel = self.fuel.checked_sub(1).ok_or("fuel")?;
        match body {
            IRBody::Ret(arg) => Self::arg(arg, &locals),
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                let values = |args: &Vec<crate::ir::IRArg>| {
                    args.iter()
                        .map(|a| Self::arg(a, &locals))
                        .collect::<Result<Vec<_>, _>>()
                };
                let result = match value {
                    IRExpr::Ctor { info, args } => IrValue::Ctor(info.tag, values(args)?),
                    IRExpr::PartialApply { fn_id, args, .. } => {
                        IrValue::Closure(fn_id.0.clone(), values(args)?)
                    }
                    IRExpr::Apply { fn_id, args } => self.call(&fn_id.0, values(args)?)?,
                    IRExpr::ClosureApply { closure, args } => {
                        let IrValue::Closure(name, mut captured) = Self::arg(closure, &locals)?
                        else {
                            return Err("not closure");
                        };
                        captured.extend(values(args)?);
                        self.call(&name, captured)?
                    }
                    IRExpr::Proj { idx, arg, .. } => {
                        let IrValue::Ctor(_, fields) = Self::arg(arg, &locals)? else {
                            return Err("not constructor");
                        };
                        fields.get(*idx as usize).cloned().ok_or("field")?
                    }
                    _ => return Err("unsupported expression"),
                };
                if locals.insert(var.0, result).is_some() {
                    return Err("duplicate local");
                }
                self.body(rest, locals)
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                let Some(IrValue::Ctor(tag, _)) = locals.get(&scrutinee.0) else {
                    return Err("bad scrutinee");
                };
                if let Some(alt) = alts.iter().find(|a| a.ctor.tag == *tag) {
                    self.body(&alt.body, locals)
                } else if let Some(default) = default {
                    self.body(default, locals)
                } else {
                    Err("missing alternative")
                }
            }
            _ => Err("unsupported body"),
        }
    }
}

#[test]
fn actual_specialized_matcher_executes_both_cases_and_preserves_divergence() {
    use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
    let context = actual_context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let output = context.lower_ir(&root, RuntimeLimits::default()).unwrap();
    let row = output.rows.iter().find(|r| r.origin.name == root).unwrap();
    let spec = &row.specializations[0];
    let mut eval = IrEval::from_output(&output);
    let mut value = IrValue::Ctor(0, vec![]);
    for _ in 0..7 {
        eval.fuel = 10000;
        assert_eq!(eval.call(&root, vec![value.clone()]), Ok(value.clone()));
        value = IrValue::Ctor(1, vec![value]);
    }
    let zero_fun = eval
        .functions
        .values()
        .find(|d| {
            d.name != root
                && matches!(&d.body,
        IRBody::VDecl{value:IRExpr::Ctor{info,..},..} if info.name==Name::from_string("Unary.zero"))
        })
        .unwrap()
        .name
        .clone();
    let quoted = Name::anon().str("RuntimeProbe").str("count._unsafe_rec");
    let quoted_output = context.lower_ir(&quoted, RuntimeLimits::default()).unwrap();
    eval.functions
        .extend(IrEval::from_output(&quoted_output).functions);
    let looping = Name::anon().str("falsification-only-loop");
    eval.functions.insert(
        looping.clone(),
        IRDecl {
            name: looping.clone(),
            params: vec![(VarId(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(looping.clone()),
                    args: vec![IRArg::Var(VarId(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            },
        },
    );
    let zero = IrValue::Ctor(0, vec![]);
    let succ = IrValue::Ctor(1, vec![zero.clone()]);
    for (input, z, s, expected) in [
        (
            succ.clone(),
            looping.clone(),
            quoted.clone(),
            Ok(zero.clone()),
        ),
        (zero.clone(), looping.clone(), quoted, Err("fuel")),
        (zero.clone(), zero_fun.clone(), looping.clone(), Ok(zero)),
        (succ, zero_fun, looping, Err("fuel")),
    ] {
        eval.fuel = 100;
        assert_eq!(
            eval.call(
                &spec.generated_name,
                vec![
                    input,
                    IrValue::Closure(z, vec![]),
                    IrValue::Closure(s, vec![])
                ]
            ),
            expected
        );
    }
}

#[test]
fn actual_matcher_rule_handler_constructor_and_motive_twins_refuse_specialization() {
    let context = actual_context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let original = context.lower_ir(&root, RuntimeLimits::default()).unwrap();
    let spec = &original
        .rows
        .iter()
        .find(|r| r.origin.name == root)
        .unwrap()
        .specializations[0];
    fn change_handler(expr: &Expr, n: usize) -> Expr {
        if n > 0 {
            let ExprKind::Lam(b, d, body) = expr.kind() else {
                panic!()
            };
            return Expr::lam(*b, d.as_ref().clone(), change_handler(body, n - 1));
        }
        let ExprKind::App(f, handler) = expr.kind() else {
            panic!()
        };
        let ExprKind::Lam(b, d, body) = handler.kind() else {
            panic!()
        };
        let ExprKind::App(h, _) = body.kind() else {
            panic!()
        };
        Expr::app(
            f.as_ref().clone(),
            Expr::lam(
                *b,
                d.as_ref().clone(),
                Expr::app(h.as_ref().clone(), Expr::const_str("Unary.zero")),
            ),
        )
    }
    let mut mutations = Vec::new();
    fn inside(expr: &Expr, n: usize, edit: fn(&Expr) -> Expr) -> Expr {
        if n == 0 {
            return edit(expr);
        }
        let ExprKind::Lam(b, d, body) = expr.kind() else {
            panic!()
        };
        Expr::lam(*b, d.as_ref().clone(), inside(body, n - 1, edit))
    }
    fn swap_handlers(expr: &Expr, depth: u32) -> Expr {
        match expr.kind() {
            ExprKind::BVar(i) if *i >= depth && *i - depth < 2 => {
                Expr::bvar(depth + 1 - (*i - depth))
            }
            ExprKind::App(f, a) => Expr::app(swap_handlers(f, depth), swap_handlers(a, depth)),
            ExprKind::Lam(b, d, body) => {
                Expr::lam(*b, swap_handlers(d, depth), swap_handlers(body, depth + 1))
            }
            ExprKind::Pi(b, d, body) => {
                Expr::pi(*b, swap_handlers(d, depth), swap_handlers(body, depth + 1))
            }
            _ => expr.clone(),
        }
    }
    mutations.push(mutate(&context, &spec.source.name, |r| {
        let RuntimeBody::Stored(Ok(body)) = &r.body else {
            panic!()
        };
        r.body = RuntimeBody::Stored(Ok(inside(body, 4, |e| swap_handlers(e, 0))));
    }));
    mutations.push(mutate(&context, &root, |r| {
        let RuntimeBody::Stored(Ok(body)) = &r.body else {
            panic!()
        };
        r.body = RuntimeBody::Stored(Ok(inside(body, 1, |e| {
            let mut head = e;
            let mut args = Vec::new();
            while let ExprKind::App(f, a) = head.kind() {
                args.push(a.as_ref().clone());
                head = f;
            }
            args.reverse();
            assert_eq!(args.len(), 4);
            args[0] = Expr::lam(
                BinderInfo::Default,
                Expr::const_str("Unary"),
                Expr::const_str("Unit"),
            );
            args.into_iter().fold(head.clone(), Expr::app)
        })));
    }));
    mutations.push(mutate(&context, &spec.source.name, |r| {
        let RuntimeBody::Stored(Ok(body)) = &r.body else {
            panic!()
        };
        r.body = RuntimeBody::Stored(Ok(change_handler(body, 4)));
    }));
    mutations.push(mutate(&context, &spec.recursor.name, |r| {
        let RuntimeFamily::Recursor { rules, .. } = &mut r.family else {
            panic!()
        };
        rules.swap(0, 1);
    }));
    mutations.push(mutate(&context, &spec.recursor.name, |r| {
        fn replace(expr: &Expr) -> Expr {
            match expr.kind() {
                ExprKind::Lam(b, d, body) => Expr::lam(*b, d.as_ref().clone(), replace(body)),
                _ => Expr::const_str("Unary.zero"),
            }
        }
        let RuntimeFamily::Recursor { rules, .. } = &mut r.family else {
            panic!()
        };
        rules[0].rhs = Ok(replace(rules[0].rhs.as_ref().unwrap()));
    }));
    mutations.push(mutate(&context, &Name::from_string("Unary.succ"), |r| {
        let RuntimeFamily::Constructor { index, .. } = &mut r.family else {
            panic!()
        };
        *index = 0;
    }));
    mutations.push(mutate(&context, &spec.source.name, |r| {
        r.level_params.push(Name::from_string("extra"));
    }));
    for changed in mutations {
        if let Ok(output) = changed.lower_ir(&root, RuntimeLimits::default()) {
            assert!(output
                .rows
                .iter()
                .find(|r| r.origin.name == root)
                .unwrap()
                .specializations
                .is_empty());
        }
    }
    // Close IR projection mutation is rejected by the independent evaluator,
    // not hidden by symbolic-name matching.
    let mut eval = IrEval::from_output(&original);
    let decl = eval.functions.get_mut(&spec.generated_name).unwrap();
    let crate::ir::IRBody::Case { alts, .. } = &mut decl.body else {
        panic!()
    };
    let crate::ir::IRBody::VDecl {
        value: crate::ir::IRExpr::Proj { idx, .. },
        ..
    } = &mut *alts[1].body
    else {
        panic!()
    };
    *idx = 1;
    assert_eq!(
        eval.call(
            &root,
            vec![IrValue::Ctor(1, vec![IrValue::Ctor(0, vec![])])]
        ),
        Err("field")
    );
}

#[test]
fn actual_matcher_function_and_constructor_arguments_use_typed_value_lowering() {
    use crate::ir::{IRBody, IRExpr};
    fn map_spine(expr: &Expr, edit: impl FnOnce(&mut Vec<Expr>)) -> Expr {
        let mut head = expr;
        let mut args = Vec::new();
        while let ExprKind::App(f, a) = head.kind() {
            args.push(a.as_ref().clone());
            head = f;
        }
        args.reverse();
        assert_eq!(args.len(), 4);
        edit(&mut args);
        args.into_iter().fold(head.clone(), Expr::app)
    }
    fn header(expr: &Expr, n: usize, arg_ty: &Expr) -> Expr {
        let (b, d, body, lambda) = match expr.kind() {
            ExprKind::Lam(b, d, body) => (b, d, body, true),
            ExprKind::Pi(b, d, body) => (b, d, body, false),
            _ => panic!(),
        };
        let (domain, body) = if n == 0 {
            let ExprKind::Pi(ab, _, codomain) = d.kind() else {
                panic!()
            };
            (
                Expr::pi(*ab, arg_ty.clone(), codomain.as_ref().clone()),
                body.as_ref().clone(),
            )
        } else {
            (d.as_ref().clone(), header(body, n - 1, arg_ty))
        };
        if lambda {
            Expr::lam(*b, domain, body)
        } else {
            Expr::pi(*b, domain, body)
        }
    }
    fn value(expr: &Expr, n: usize, target: &Name) -> Expr {
        if n > 0 {
            let ExprKind::Lam(b, d, body) = expr.kind() else {
                panic!()
            };
            return Expr::lam(*b, d.as_ref().clone(), value(body, n - 1, target));
        }
        map_spine(expr, |args| {
            let ExprKind::App(handler, _) = args[2].kind() else {
                panic!()
            };
            args[2] = Expr::app(
                handler.as_ref().clone(),
                Expr::const_(target.clone(), vec![]),
            );
        })
    }
    let context = actual_context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let output = context.lower_ir(&root, RuntimeLimits::default()).unwrap();
    let matcher = output
        .rows
        .iter()
        .find(|r| r.origin.name == root)
        .unwrap()
        .specializations[0]
        .source
        .name
        .clone();
    let data = Expr::const_str("Unary");
    for (target, arg_ty, function) in [
        (
            Name::anon().str("RuntimeProbe").str("count._unsafe_rec"),
            Expr::pi(BinderInfo::Default, data.clone(), data.clone()),
            true,
        ),
        (Name::from_string("Unary.zero"), data, false),
    ] {
        let changed = mutate(&context, &matcher, |r| {
            r.type_ = Ok(header(r.type_.as_ref().unwrap(), 2, &arg_ty));
            let RuntimeBody::Stored(Ok(body)) = &r.body else {
                panic!()
            };
            r.body = RuntimeBody::Stored(Ok(value(&header(body, 2, &arg_ty), 4, &target)));
            r.dependencies.insert(target.clone());
        });
        let changed = mutate(&changed, &root, |r| {
            let RuntimeBody::Stored(Ok(body)) = &r.body else {
                panic!()
            };
            let ExprKind::Lam(b, d, body) = body.kind() else {
                panic!()
            };
            r.body = RuntimeBody::Stored(Ok(Expr::lam(
                *b,
                d.as_ref().clone(),
                map_spine(body, |args| {
                    let ExprKind::Lam(b, _, body) = args[2].kind() else {
                        panic!()
                    };
                    args[2] = Expr::lam(*b, arg_ty.clone(), body.as_ref().clone());
                }),
            )));
        });
        // These are source-type-correct close twins, not malformed-type errors
        // accidentally satisfying a negative test.
        changed
            .lower_definition(&root, RuntimeLimits::default())
            .unwrap();
        let output = changed.lower_ir(&root, RuntimeLimits::default()).unwrap();
        let row = output.rows.iter().find(|r| r.origin.name == root).unwrap();
        assert_eq!(row.specializations.len(), 1, "{:?}", row.status);
        let RuntimeIrStatus::Lowered(decls) = &row.status else {
            panic!()
        };
        let spec = &row.specializations[0];
        let decl = decls
            .iter()
            .find(|d| d.name == spec.generated_name)
            .unwrap();
        let IRBody::Case { alts, .. } = &decl.body else {
            panic!()
        };
        let IRBody::VDecl { value, .. } = alts[0].body.as_ref() else {
            panic!()
        };
        if function {
            assert!(
                matches!(value,IRExpr::PartialApply{fn_id,arity:1,args} if fn_id.0==target && args.is_empty())
            );
        } else {
            assert!(
                matches!(value,IRExpr::Ctor{info,args} if info.name==target && info.tag==0 && args.is_empty())
            );
        }
        let mut eval = IrEval::from_output(&output);
        assert_eq!(
            eval.call(&root, vec![IrValue::Ctor(0, vec![])]),
            Ok(IrValue::Ctor(0, vec![]))
        );
    }
}
