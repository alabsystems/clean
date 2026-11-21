// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit declaration identities in Lean source parsed by the module driver.

use clean_elab::module_driver::parse_module;
use clean_parser::{Projection, SurfaceDecl, SurfaceExpr, SurfaceName};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fs, path::Path};

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub(super) enum Kind {
    Def,
    Inductive,
    Constructor,
    Structure,
    Field,
    Theorem,
}

pub(super) struct Item {
    pub(super) kind: Kind,
    pub(super) refutes: Option<SurfaceName>,
}

pub(super) fn load(path: &Path) -> Result<BTreeMap<SurfaceName, Item>, String> {
    let at_path = |reason| format!("{}: {reason}", path.display());
    let text = fs::read_to_string(path).map_err(|err| at_path(err.to_string()))?;
    let (_, parsed) = parse_module(path, &text);
    let report = parsed.map_err(|err| at_path(err.to_string()))?;
    if let Some(diag) = report.diagnostics.first() {
        return Err(at_path(format!(
            "parser recovery at line {}: {}",
            diag.recovery_start.line, diag.message
        )));
    }

    let mut items = BTreeMap::new();
    index(&report.decls, &SurfaceName::default(), &mut items, true).map_err(at_path)?;
    Ok(items)
}

fn index(
    declarations: &[SurfaceDecl],
    namespace: &SurfaceName,
    items: &mut BTreeMap<SurfaceName, Item>,
    persistent: bool,
) -> Result<(), String> {
    for declaration in declarations {
        match declaration {
            SurfaceDecl::Namespace { name, decls, .. } => {
                index(decls, &name.qualify_under(namespace), items, persistent)?;
            }
            SurfaceDecl::Section { decls, .. } | SurfaceDecl::Mutual { decls, .. } => {
                index(decls, namespace, items, persistent)?;
            }
            SurfaceDecl::Open {
                body: Some(body), ..
            }
            | SurfaceDecl::SetOption {
                body: Some(body), ..
            } => {
                index(
                    std::slice::from_ref(body.as_ref()),
                    namespace,
                    items,
                    persistent,
                )?;
            }
            SurfaceDecl::GuardMsgs { cmd, .. } => {
                index(std::slice::from_ref(cmd.as_ref()), namespace, items, false)?;
            }
            SurfaceDecl::RawDecl { span, .. } => {
                return Err(format!("unparsed declaration at byte {}", span.start));
            }
            _ if !persistent => {}
            SurfaceDecl::Def { name, .. }
            | SurfaceDecl::Opaque { name, .. }
            | SurfaceDecl::Instance {
                name: Some(name), ..
            } => {
                add(items, name.qualify_under(namespace), Kind::Def, None)?;
            }
            SurfaceDecl::Theorem {
                name,
                binders,
                universe_params,
                ty,
                ..
            } => {
                let refutes = if binders.is_empty() && universe_params.is_empty() {
                    refutes_rule(ty)
                } else {
                    None
                };
                add(items, name.qualify_under(namespace), Kind::Theorem, refutes)?;
            }
            SurfaceDecl::Inductive { name, ctors, .. } => {
                let name = name.qualify_under(namespace);
                for ctor in ctors {
                    add(
                        items,
                        ctor.name.qualify_under(&name),
                        Kind::Constructor,
                        None,
                    )?;
                }
                add(items, name, Kind::Inductive, None)?;
            }
            SurfaceDecl::Structure { name, fields, .. }
            | SurfaceDecl::Class { name, fields, .. } => {
                let name = name.qualify_under(namespace);
                for field in fields.iter().filter(|field| !field.is_default_override) {
                    add(items, field.name.qualify_under(&name), Kind::Field, None)?;
                }
                add(items, name, Kind::Structure, None)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn add(
    items: &mut BTreeMap<SurfaceName, Item>,
    name: SurfaceName,
    kind: Kind,
    refutes: Option<SurfaceName>,
) -> Result<(), String> {
    match items.entry(name) {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(Item { kind, refutes });
            Ok(())
        }
        std::collections::btree_map::Entry::Occupied(entry) => {
            Err(format!("duplicate source declaration {}", entry.key()))
        }
    }
}

/// Recognize the source spelling of the control statement's outer application.
fn refutes_rule(ty: &SurfaceExpr) -> Option<SurfaceName> {
    let SurfaceExpr::App(_, head, arguments) = ty else {
        return None;
    };
    let [argument, _, ..] = arguments.as_slice() else {
        return None;
    };
    let head = dotted_name(head)?;
    if head.is_relative_constructor()
        || (!head.is_unescaped_component("Refutes")
            && head != SurfaceName::generated_path("CICL.NegativeControls.Refutes"))
    {
        return None;
    }
    if argument.name.is_some() {
        return None;
    }
    let rule = dotted_name(&argument.expr)?;
    if rule.is_relative_constructor() {
        rule.component_text()?;
    } else if ![
        SurfaceName::generated_path("Rule"),
        SurfaceName::generated_path("CICL.NegativeControls.Rule"),
    ]
    .contains(&rule.parent())
    {
        return None;
    }
    Some(rule.last_component())
}

/// A qualified term identifier can parse as a chain of named projections.
fn dotted_name(expr: &SurfaceExpr) -> Option<SurfaceName> {
    let mut base = expr;
    let mut fields = Vec::new();
    while let SurfaceExpr::Proj(_, inner, Projection::Named(field)) = base {
        fields.push(field);
        base = inner;
    }
    let SurfaceExpr::Ident(_, name) = base else {
        return None;
    };
    if name.is_relative_constructor() && !fields.is_empty() {
        return None;
    }
    Some(
        fields
            .into_iter()
            .rev()
            .fold(name.clone(), |prefix, field| prefix.append(field)),
    )
}
