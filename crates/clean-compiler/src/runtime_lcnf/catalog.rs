//! The compiler's in-memory lowering view, not another serialized runtime format.
//!
//! Full imported and environment records remain in their original captures.
//! This view contains only fields consumed by the conditional runtime checker.

use clean_kernel::{Expr, Name};
use clean_olean::import::runtime::{RuntimeBody, RuntimeDeclaration, RuntimeFamily};
use clean_olean::module::{ConstantKind, DefinitionSafety};
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Debug)]
pub struct RuntimeCatalogDeclaration {
    pub name: Name,
    pub kind: ConstantKind,
    pub level_params: Vec<Name>,
    pub declaration_safety: Option<DefinitionSafety>,
    pub type_: Result<Expr, String>,
    pub body: RuntimeBody,
    pub family: RuntimeFamily,
    pub dependencies: BTreeSet<Name>,
    /// Completeness of this lowering view, never source/refinement authority.
    pub represented_fields_complete: bool,
    pub issues: Vec<String>,
}

impl From<&RuntimeDeclaration> for RuntimeCatalogDeclaration {
    fn from(row: &RuntimeDeclaration) -> Self {
        Self {
            name: row.name.clone(),
            kind: row.kind.clone(),
            level_params: row.level_params.clone(),
            declaration_safety: row.declaration_safety,
            type_: row.type_.clone(),
            body: row.body.clone(),
            family: row.family.clone(),
            dependencies: row.dependencies.clone(),
            represented_fields_complete: row.represented_fields_complete,
            issues: row.issues.clone(),
        }
    }
}

const MAX_REFERENCE_DEPTH: usize = 256;

enum Visit<'a> {
    Enter(&'a Expr),
    Finish(&'a Expr),
}

fn schedule_children<'a>(
    expr: &'a Expr,
    names: &mut BTreeSet<Name>,
    pending: &mut Vec<Visit<'a>>,
) -> Result<(), String> {
    use clean_kernel::ExprKind;
    match expr.kind() {
        ExprKind::Const(name, _) => {
            names.insert(name.clone());
        }
        ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
            pending.extend([Visit::Enter(f), Visit::Enter(a)]);
        }
        ExprKind::Let(_, ty, value, body, _) => {
            pending.extend([Visit::Enter(ty), Visit::Enter(value), Visit::Enter(body)]);
        }
        ExprKind::Proj(name, _, value) => {
            names.insert(name.clone());
            pending.push(Visit::Enter(value));
        }
        ExprKind::MData(_, value) => pending.push(Visit::Enter(value)),
        ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
        _ => return Err("unsupported environment expression in dependency inventory".into()),
    }
    Ok(())
}

pub(super) fn references(expressions: Vec<Expr>, limit: usize) -> Result<BTreeSet<Name>, String> {
    use std::ptr::from_ref;

    // All roots and their Arc children stay live while addresses are keys.
    // A completed node records the longest distance in edges to a leaf.
    let mut heights = HashMap::new();
    let mut open: Vec<usize> = Vec::new();
    let mut pending = Vec::new();
    let mut names = BTreeSet::new();
    for root in &expressions {
        pending.push(Visit::Enter(root));
        while let Some(visit) = pending.pop() {
            let height = match visit {
                Visit::Enter(expr) => {
                    let cached = heights.get(&from_ref(expr)).copied();
                    if open.len() + cached.unwrap_or(0) > MAX_REFERENCE_DEPTH {
                        return Err("environment expression reference depth bound".into());
                    }
                    let Some(height) = cached else {
                        // Charge on entry, including unfinished ancestors. Each
                        // distinct node schedules at most three children and one finish.
                        if heights.len() + open.len() >= limit {
                            return Err("environment expression reference node bound".into());
                        }
                        open.push(0);
                        pending.push(Visit::Finish(expr));
                        schedule_children(expr, &mut names, &mut pending)?;
                        continue;
                    };
                    height
                }
                Visit::Finish(expr) => {
                    let height = open.pop().expect("finish matches an entered expression");
                    heights.insert(from_ref(expr), height);
                    height
                }
            };
            if let Some(parent_height) = open.last_mut() {
                *parent_height = (*parent_height).max(height + 1);
            }
        }
    }
    Ok(names)
}

#[cfg(test)]
mod tests;
