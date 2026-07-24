// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]

use super::collect_app_args;
use crate::bridge::{BridgeError, BridgeResult};
use crate::smtlib_builder::{SmtLibCommand, SmtLibExpr, SmtLibSort};
use clean_kernel::{ConstructorVal, Environment, Expr, ExprKind, Name};
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InductiveDTSpec {
    pub(crate) sort_name: String,
    pub(crate) constructors: Vec<DTConstructor>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DTConstructor {
    pub(crate) name: String,
    pub(crate) recognizer: String,
    pub(crate) fields: Vec<DTField>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DTField {
    pub(crate) accessor: String,
    pub(crate) sort: SmtLibSort,
    pub(crate) recursive: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DTRecognizer {
    pub(crate) name: String,
    pub(crate) domain: SmtLibSort,
}
impl DTRecognizer {
    pub(crate) fn declaration(&self) -> SmtLibCommand {
        SmtLibCommand::DeclareFun {
            name: self.name.clone(),
            args: vec![self.domain.clone()],
            result: SmtLibSort::Bool,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DTAccessor {
    pub(crate) name: String,
    pub(crate) constructor: String,
    pub(crate) field_index: usize,
    pub(crate) domain: SmtLibSort,
    pub(crate) range: SmtLibSort,
    pub(crate) recursive: bool,
}
impl DTAccessor {
    pub(crate) fn declaration(&self) -> SmtLibCommand {
        SmtLibCommand::DeclareFun {
            name: self.name.clone(),
            args: vec![self.domain.clone()],
            result: self.range.clone(),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DTAcyclicitySpec {
    pub(crate) rank_function: String,
    pub(crate) rank_declaration: SmtLibCommand,
    pub(crate) axiom: SmtLibExpr,
}
pub(crate) fn translate_inductive_to_dt(
    env: &Environment,
    ty: &Expr,
) -> BridgeResult<InductiveDTSpec> {
    let ty = ty.strip_mdata().clone();
    let (ind, args) = resolve_inductive_application(env, &ty)?;
    let sort_name = mangle_type_name(env, &ty)?;
    let constructors = ind
        .constructor_names
        .iter()
        .map(|ctor_name| {
            let ctor =
                env.get_constructor(ctor_name)
                    .ok_or_else(|| BridgeError::TranslationFailed {
                        context: format!("missing constructor metadata for {ctor_name}"),
                    })?;
            translate_constructor(env, ctor, &args, &sort_name)
        })
        .collect::<BridgeResult<Vec<_>>>()?;
    Ok(InductiveDTSpec {
        sort_name,
        constructors,
    })
}
impl InductiveDTSpec {
    pub(crate) fn declaration_smtlib(&self) -> String {
        let ctors = self
            .constructors
            .iter()
            .map(|ctor| {
                if ctor.fields.is_empty() {
                    format!("({})", ctor.name)
                } else {
                    let fields = ctor
                        .fields
                        .iter()
                        .map(|field| format!("({} {})", field.accessor, field.sort.to_smtlib2()))
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("({} {fields})", ctor.name)
                }
            })
            .collect::<Vec<_>>()
            .join(" ");
        format!("(declare-datatype {} ({ctors}))", self.sort_name)
    }
    pub(crate) fn clash_axioms(&self) -> Vec<SmtLibExpr> {
        let mut axioms = Vec::new();
        for lhs_idx in 0..self.constructors.len() {
            for rhs_idx in (lhs_idx + 1)..self.constructors.len() {
                let lhs = &self.constructors[lhs_idx];
                let rhs = &self.constructors[rhs_idx];
                let lhs_vars = quantified_vars("x", &lhs.fields);
                let rhs_vars = quantified_vars("y", &rhs.fields);
                axioms.push(forall(
                    combine_vars(&lhs_vars, &rhs_vars),
                    not(eq(ctor_app(lhs, &lhs_vars), ctor_app(rhs, &rhs_vars))),
                ));
            }
        }
        axioms
    }
    pub(crate) fn dt_constructor_recognizers(&self) -> Vec<DTRecognizer> {
        let domain = self.sort();
        self.constructors
            .iter()
            .map(|ctor| DTRecognizer {
                name: ctor.recognizer.clone(),
                domain: domain.clone(),
            })
            .collect()
    }
    pub(crate) fn dt_accessor_functions(&self) -> Vec<DTAccessor> {
        let domain = self.sort();
        self.constructors
            .iter()
            .flat_map(|ctor| {
                ctor.fields
                    .iter()
                    .enumerate()
                    .map(|(field_index, field)| DTAccessor {
                        name: field.accessor.clone(),
                        constructor: ctor.name.clone(),
                        field_index,
                        domain: domain.clone(),
                        range: field.sort.clone(),
                        recursive: field.recursive,
                    })
            })
            .collect()
    }
    pub(crate) fn selector_axioms(&self) -> Vec<SmtLibExpr> {
        let mut axioms = Vec::new();
        for ctor in &self.constructors {
            if ctor.fields.is_empty() {
                continue;
            }
            let vars = quantified_vars("x", &ctor.fields);
            let ctor_term = ctor_app(ctor, &vars);
            for (idx, field) in ctor.fields.iter().enumerate() {
                axioms.push(forall(
                    vars.clone(),
                    eq(
                        apply(&field.accessor, vec![ctor_term.clone()]),
                        var(&vars[idx].0),
                    ),
                ));
            }
        }
        axioms
    }
    pub(crate) fn dt_acyclicity_axiom(&self) -> Option<DTAcyclicitySpec> {
        let rank_function = format!("{}_dt_rank", self.sort_name);
        let rank_declaration = SmtLibCommand::DeclareFun {
            name: rank_function.clone(),
            args: vec![self.sort()],
            result: SmtLibSort::Int,
        };
        let clauses = self
            .constructors
            .iter()
            .filter_map(|ctor| {
                let vars = quantified_vars("x", &ctor.fields);
                let ctor_term = ctor_app(ctor, &vars);
                let decreases = ctor
                    .fields
                    .iter()
                    .filter(|field| field.recursive)
                    .map(|field| {
                        lt(
                            rank(
                                &rank_function,
                                apply(&field.accessor, vec![ctor_term.clone()]),
                            ),
                            rank(&rank_function, ctor_term.clone()),
                        )
                    })
                    .collect::<Vec<_>>();
                (!decreases.is_empty()).then(|| forall(vars, conjunction(decreases)))
            })
            .collect::<Vec<_>>();
        (!clauses.is_empty()).then(|| DTAcyclicitySpec {
            rank_function,
            rank_declaration,
            axiom: conjunction(clauses),
        })
    }
    pub(crate) fn dt_injectivity_axioms(&self) -> Vec<SmtLibExpr> {
        self.constructors
            .iter()
            .filter(|ctor| !ctor.fields.is_empty())
            .map(|ctor| {
                let lhs_vars = quantified_vars("x", &ctor.fields);
                let rhs_vars = quantified_vars("y", &ctor.fields);
                let equalities = lhs_vars
                    .iter()
                    .zip(&rhs_vars)
                    .map(|((lhs_name, _), (rhs_name, _))| eq(var(lhs_name), var(rhs_name)))
                    .collect::<Vec<_>>();
                forall(
                    combine_vars(&lhs_vars, &rhs_vars),
                    implies(
                        eq(ctor_app(ctor, &lhs_vars), ctor_app(ctor, &rhs_vars)),
                        conjunction(equalities),
                    ),
                )
            })
            .collect()
    }
    fn sort(&self) -> SmtLibSort {
        SmtLibSort::Uninterpreted(self.sort_name.clone())
    }
}
fn translate_constructor(
    env: &Environment,
    ctor: &ConstructorVal,
    args: &[Expr],
    sort_name: &str,
) -> BridgeResult<DTConstructor> {
    let ctor_name = format!("{sort_name}_{}", short_name(&ctor.name));
    let recognizer = format!("is_{ctor_name}");
    let mut current = ctor.type_.clone();
    for arg in args {
        let ExprKind::Pi(_, _, body) = current.kind() else {
            return Err(BridgeError::TranslationFailed {
                context: format!("constructor {} missing parameter binder", ctor.name),
            });
        };
        current = body.instantiate(arg);
    }
    let mut fields = Vec::new();
    while let ExprKind::Pi(_, domain, body) = current.kind() {
        let field_ty = domain.strip_mdata().clone();
        if field_ty.has_loose_bvars() {
            return Err(BridgeError::UnsupportedExpr {
                context: format!(
                    "dependent constructor field in {} is not supported for SMT datatypes",
                    ctor.name
                ),
            });
        }
        let sort = lean_type_to_smt_sort(env, &field_ty, sort_name)?;
        fields.push(DTField {
            accessor: format!("{ctor_name}_field{}", fields.len()),
            recursive: sort == dt_sort(sort_name),
            sort,
        });
        current = (**body).clone();
    }
    if current.has_loose_bvars() || mangle_type_name(env, &current)? != sort_name {
        return Err(BridgeError::UnsupportedExpr {
            context: format!(
                "constructor {} does not return the fully applied inductive target",
                ctor.name
            ),
        });
    }
    if fields.len() != ctor.num_fields as usize {
        return Err(BridgeError::TranslationFailed {
            context: format!(
                "constructor {} field count mismatch: metadata={} extracted={}",
                ctor.name,
                ctor.num_fields,
                fields.len()
            ),
        });
    }

    Ok(DTConstructor {
        name: ctor_name,
        recognizer,
        fields,
    })
}

fn resolve_inductive_application<'a>(
    env: &'a Environment,
    ty: &Expr,
) -> BridgeResult<(&'a clean_kernel::InductiveVal, Vec<Expr>)> {
    let (head, args) = collect_app_args(ty);
    let ExprKind::Const(name, _) = head.kind() else {
        return Err(BridgeError::UnsupportedExpr {
            context: format!("datatype translation requires a constant-head type, got {ty:?}"),
        });
    };
    let ind = env
        .get_inductive(name)
        .ok_or_else(|| BridgeError::UnsupportedExpr {
            context: format!("{name} is not a registered inductive type"),
        })?;
    if ind.all_names.len() != 1 || ind.is_nested || ind.num_indices != 0 {
        return Err(BridgeError::UnsupportedExpr {
            context: format!(
                "inductive datatype translation currently supports only non-nested, non-indexed, non-mutual inductives: {}",
                ind.name
            ),
        });
    }
    if args.len() != ind.num_params as usize {
        return Err(BridgeError::UnsupportedExpr {
            context: format!(
                "inductive {} requires {} parameters, got {}",
                ind.name,
                ind.num_params,
                args.len()
            ),
        });
    }
    Ok((ind, args))
}
fn lean_type_to_smt_sort(
    env: &Environment,
    ty: &Expr,
    sort_name: &str,
) -> BridgeResult<SmtLibSort> {
    if mangle_type_name(env, ty)? == sort_name {
        return Ok(dt_sort(sort_name));
    }
    let ty = ty.strip_mdata();
    match ty.kind() {
        ExprKind::Const(name, _) => Ok(match name.to_string().as_str() {
            "Nat" | "Int" => SmtLibSort::Int,
            "Real" | "Rat" => SmtLibSort::Real,
            "Bool" => SmtLibSort::Bool,
            other => SmtLibSort::Uninterpreted(sanitize_symbol(other)),
        }),
        ExprKind::Sort(_) => Ok(SmtLibSort::Bool),
        ExprKind::App(_, _) => {
            let (head, args) = collect_app_args(ty);
            let ExprKind::Const(name, _) = head.kind() else {
                return Err(BridgeError::UnsupportedExpr {
                    context: format!("unsupported higher-order field type {ty:?}"),
                });
            };
            match name.to_string().as_str() {
                "Array" if args.len() == 2 => Ok(SmtLibSort::Array(
                    Box::new(lean_type_to_smt_sort(env, &args[0], sort_name)?),
                    Box::new(lean_type_to_smt_sort(env, &args[1], sort_name)?),
                )),
                "Nat" | "Int" => Ok(SmtLibSort::Int),
                "Real" | "Rat" => Ok(SmtLibSort::Real),
                "Bool" => Ok(SmtLibSort::Bool),
                _ => Ok(SmtLibSort::Uninterpreted(mangle_type_name(env, ty)?)),
            }
        }
        _ => Err(BridgeError::UnsupportedExpr {
            context: format!("unsupported SMT datatype field type {ty:?}"),
        }),
    }
}
fn mangle_type_name(env: &Environment, ty: &Expr) -> BridgeResult<String> {
    let ty = ty.strip_mdata();
    match ty.kind() {
        ExprKind::Const(name, _) => Ok(match name.to_string().as_str() {
            "Nat" | "Int" => "Int".to_string(),
            "Real" | "Rat" => "Real".to_string(),
            "Bool" => "Bool".to_string(),
            "String" => "String".to_string(),
            other => sanitize_symbol(other),
        }),
        ExprKind::Sort(_) => Ok("Bool".to_string()),
        ExprKind::App(_, _) => {
            let (head, args) = collect_app_args(ty);
            let ExprKind::Const(name, _) = head.kind() else {
                return Err(BridgeError::UnsupportedExpr {
                    context: format!("unsupported type application {ty:?}"),
                });
            };
            if name.to_string() == "Array" && args.len() == 2 {
                return Ok(format!(
                    "Array_{}_{}",
                    mangle_type_name(env, &args[0])?,
                    mangle_type_name(env, &args[1])?
                ));
            }
            let base = if env.get_inductive(name).is_some() {
                sanitize_symbol(&short_name(name))
            } else {
                sanitize_symbol(&name.to_string())
            };
            if args.is_empty() {
                Ok(base)
            } else {
                Ok(format!(
                    "{base}_{}",
                    args.iter()
                        .map(|arg| mangle_type_name(env, arg))
                        .collect::<BridgeResult<Vec<_>>>()?
                        .join("_")
                ))
            }
        }
        _ => Err(BridgeError::UnsupportedExpr {
            context: format!("unsupported type name encoding for {ty:?}"),
        }),
    }
}
fn quantified_vars(prefix: &str, fields: &[DTField]) -> Vec<(String, SmtLibSort)> {
    fields
        .iter()
        .enumerate()
        .map(|(idx, field)| (format!("{prefix}{idx}"), field.sort.clone()))
        .collect()
}
fn combine_vars(
    lhs: &[(String, SmtLibSort)],
    rhs: &[(String, SmtLibSort)],
) -> Vec<(String, SmtLibSort)> {
    lhs.iter().cloned().chain(rhs.iter().cloned()).collect()
}
fn dt_sort(sort_name: &str) -> SmtLibSort {
    SmtLibSort::Uninterpreted(sort_name.to_string())
}
fn ctor_app(ctor: &DTConstructor, vars: &[(String, SmtLibSort)]) -> SmtLibExpr {
    apply(&ctor.name, vars.iter().map(|(name, _)| var(name)).collect())
}
fn rank(name: &str, expr: SmtLibExpr) -> SmtLibExpr {
    apply(name, vec![expr])
}
fn var(name: &str) -> SmtLibExpr {
    SmtLibExpr::Var(name.to_string())
}
fn apply(name: &str, args: Vec<SmtLibExpr>) -> SmtLibExpr {
    SmtLibExpr::Apply(name.to_string(), args)
}
fn eq(lhs: SmtLibExpr, rhs: SmtLibExpr) -> SmtLibExpr {
    apply("=", vec![lhs, rhs])
}
fn not(expr: SmtLibExpr) -> SmtLibExpr {
    apply("not", vec![expr])
}
fn lt(lhs: SmtLibExpr, rhs: SmtLibExpr) -> SmtLibExpr {
    apply("<", vec![lhs, rhs])
}
fn implies(lhs: SmtLibExpr, rhs: SmtLibExpr) -> SmtLibExpr {
    apply("=>", vec![lhs, rhs])
}
fn conjunction(exprs: Vec<SmtLibExpr>) -> SmtLibExpr {
    match exprs.len() {
        0 => apply("true", vec![]),
        1 => exprs
            .into_iter()
            .next()
            .expect("invariant: len == 1 match arm guarantees one element"),
        _ => apply("and", exprs),
    }
}
fn forall(vars: Vec<(String, SmtLibSort)>, body: SmtLibExpr) -> SmtLibExpr {
    if vars.is_empty() {
        body
    } else {
        SmtLibExpr::Forall(vars, Box::new(body))
    }
}
fn short_name(name: &Name) -> String {
    name.to_string()
        .rsplit('.')
        .next()
        .unwrap_or_default()
        .to_string()
}
fn sanitize_symbol(name: &str) -> String {
    let mut out = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect::<String>();
    if out.is_empty() {
        out.push('T');
    }
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, 'T');
        out.insert(1, '_');
    }
    out
}
