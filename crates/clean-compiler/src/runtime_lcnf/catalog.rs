//! The compiler's in-memory lowering view, not another serialized runtime format.
//!
//! Full imported and environment records remain in their original captures.
//! This view contains only fields consumed by the conditional runtime checker.

use clean_kernel::{Expr, Name};
use clean_olean::import::runtime::{RuntimeBody, RuntimeDeclaration, RuntimeFamily};
use clean_olean::module::{ConstantKind, DefinitionSafety};
use std::collections::BTreeSet;

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

pub(super) fn references(
    expressions: impl IntoIterator<Item = Expr>,
    limit: usize,
) -> Result<BTreeSet<Name>, String> {
    use clean_kernel::ExprKind;
    let mut pending: Vec<_> = expressions.into_iter().map(|e| (e, 0usize)).collect();
    let mut names = BTreeSet::new();
    let mut steps = 0usize;
    while let Some((expr, depth)) = pending.pop() {
        steps += 1;
        if steps > limit || depth > 256 {
            return Err("environment expression reference bound".into());
        }
        match expr.kind() {
            ExprKind::Const(name, _) => {
                names.insert(name.clone());
            }
            ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
                pending.push((f.as_ref().clone(), depth + 1));
                pending.push((a.as_ref().clone(), depth + 1));
            }
            ExprKind::Let(_, ty, value, body, _) => {
                for child in [ty, value, body] {
                    pending.push((child.as_ref().clone(), depth + 1));
                }
            }
            ExprKind::Proj(name, _, value) => {
                names.insert(name.clone());
                pending.push((value.as_ref().clone(), depth + 1));
            }
            ExprKind::MData(_, value) => pending.push((value.as_ref().clone(), depth + 1)),
            ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            _ => return Err("unsupported environment expression in dependency inventory".into()),
        }
    }
    Ok(names)
}
