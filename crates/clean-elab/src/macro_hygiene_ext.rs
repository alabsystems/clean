// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::fmt;

use clean_kernel::{Expr, ExprKind, MDataMap, MDataValue, Name};

use crate::error::ElabError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ScopeId(u64);

impl ScopeId {
    pub(crate) fn root() -> Self {
        Self(0)
    }
    pub(crate) fn id(self) -> u64 {
        self.0
    }
    pub(crate) fn is_root(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ScopeId({})", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HygieneInfo {
    pub(crate) scope: ScopeId,
    pub(crate) definition_site: Option<(usize, usize)>,
    pub(crate) macro_name: Option<Name>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopeColor {
    pub(crate) name: Name,
    pub(crate) scope: ScopeId,
    pub(crate) is_captured: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ViolationKind {
    ScopeLeak,
    NameCapture,
    UnresolvedMacroVar,
}

impl fmt::Display for ViolationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ScopeLeak => f.write_str("ScopeLeak"),
            Self::NameCapture => f.write_str("NameCapture"),
            Self::UnresolvedMacroVar => f.write_str("UnresolvedMacroVar"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HygieneViolation {
    pub(crate) name: Name,
    pub(crate) expected_scope: ScopeId,
    pub(crate) actual_scope: ScopeId,
    pub(crate) kind: ViolationKind,
}

pub(crate) struct HygieneContext {
    next_scope: u64,
    scope_stack: Vec<ScopeId>,
    scope_info: HashMap<ScopeId, HygieneInfo>,
    name_bindings: HashMap<String, Vec<ScopeColor>>,
    gensym_counter: u64,
}

impl Default for HygieneContext {
    fn default() -> Self {
        Self::new()
    }
}

impl HygieneContext {
    pub(crate) fn new() -> Self {
        let root = ScopeId::root();
        let mut scope_info = HashMap::new();
        scope_info.insert(
            root,
            HygieneInfo {
                scope: root,
                definition_site: None,
                macro_name: None,
            },
        );
        Self {
            next_scope: 1,
            scope_stack: vec![root],
            scope_info,
            name_bindings: HashMap::new(),
            gensym_counter: 0,
        }
    }

    pub(crate) fn enter_macro_scope(&mut self, macro_name: &Name) -> ScopeId {
        self.enter_macro_scope_with_site_opt(macro_name, None)
    }

    pub(crate) fn enter_macro_scope_with_site(
        &mut self,
        macro_name: &Name,
        line: usize,
        col: usize,
    ) -> ScopeId {
        self.enter_macro_scope_with_site_opt(macro_name, Some((line, col)))
    }

    pub(crate) fn leave_macro_scope(&mut self) -> Option<ScopeId> {
        (self.scope_stack.len() > 1)
            .then(|| self.scope_stack.pop())
            .flatten()
    }

    pub(crate) fn current_scope(&self) -> ScopeId {
        self.scope_stack
            .last()
            .copied()
            .unwrap_or_else(ScopeId::root)
    }

    pub(crate) fn scope_depth(&self) -> usize {
        self.scope_stack.len()
    }

    pub(crate) fn fresh_name(&mut self, base: &str) -> Name {
        let fresh = Name::from_string(&format!("{base}_hyg_{}", self.gensym_counter));
        self.gensym_counter = self.gensym_counter.saturating_add(1);
        self.bind_name(&fresh, self.current_scope());
        fresh
    }

    pub(crate) fn is_accessible(&self, name: &Name, from_scope: ScopeId) -> bool {
        !self.visible_bindings(name, from_scope).is_empty()
    }

    pub(crate) fn bind_name(&mut self, name: &Name, scope: ScopeId) {
        let bindings = self.name_bindings.entry(name.to_string()).or_default();
        if bindings.iter().any(|b| b.name == *name && b.scope == scope) {
            return;
        }
        bindings.push(ScopeColor {
            name: name.clone(),
            scope,
            is_captured: false,
        });
    }

    pub(crate) fn mark_captured(&mut self, name: &Name, scope: ScopeId) {
        if let Some(bindings) = self.name_bindings.get_mut(&name.to_string()) {
            for binding in bindings.iter_mut().filter(|binding| binding.scope == scope) {
                binding.is_captured = true;
            }
        }
    }

    pub(crate) fn info_for_scope(&self, scope: ScopeId) -> Option<&HygieneInfo> {
        self.scope_info.get(&scope)
    }

    pub(crate) fn bindings_for(&self, name: &Name) -> &[ScopeColor] {
        self.name_bindings
            .get(&name.to_string())
            .map_or(&[], Vec::as_slice)
    }

    pub(crate) fn scope_stack(&self) -> &[ScopeId] {
        &self.scope_stack
    }

    fn enter_macro_scope_with_site_opt(
        &mut self,
        macro_name: &Name,
        definition_site: Option<(usize, usize)>,
    ) -> ScopeId {
        let scope = ScopeId(self.next_scope);
        self.next_scope = self.next_scope.saturating_add(1);
        self.scope_stack.push(scope);
        self.scope_info.insert(
            scope,
            HygieneInfo {
                scope,
                definition_site,
                macro_name: Some(macro_name.clone()),
            },
        );
        scope
    }

    fn is_scope_visible_from(&self, scope: ScopeId, from_scope: ScopeId) -> bool {
        if scope.is_root() {
            return true;
        }
        let Some(limit) = self.scope_stack.iter().position(|s| *s == from_scope) else {
            return false;
        };
        self.scope_stack[..=limit].contains(&scope)
    }

    fn visible_bindings<'a>(&'a self, name: &Name, from_scope: ScopeId) -> Vec<&'a ScopeColor> {
        self.bindings_for(name)
            .iter()
            .filter(|binding| self.is_scope_visible_from(binding.scope, from_scope))
            .collect()
    }

    fn innermost_visible_scope(&self, name: &Name, from_scope: ScopeId) -> Option<ScopeId> {
        self.visible_bindings(name, from_scope)
            .last()
            .map(|binding| binding.scope)
    }
}

pub(crate) fn colorize_expr(expr: &Expr, ctx: &HygieneContext) -> Expr {
    colorize(expr, ctx, ctx.current_scope())
}

pub(crate) fn resolve_hygienic(name: &Name, ctx: &HygieneContext) -> Result<Name, ElabError> {
    let visible = visible_bindings(name, ctx, ctx.current_scope())?;
    match visible.as_slice() {
        [binding] => Ok(binding.name.clone()),
        [] => Err(ElabError::UnknownIdent(name.to_string())),
        _ => Err(ElabError::MacroError(format!(
            "ambiguous hygienic name: {name}"
        ))),
    }
}

pub(crate) fn alpha_rename_avoiding(expr: Expr, avoid: &[Name], ctx: &mut HygieneContext) -> Expr {
    rename(expr, avoid, ctx)
}

pub(crate) fn check_hygiene_violation(expr: &Expr, ctx: &HygieneContext) -> Vec<HygieneViolation> {
    let mut violations = Vec::new();
    check(expr, ctx, None, &mut violations);
    violations
}

fn visible_bindings<'a>(
    name: &Name,
    ctx: &'a HygieneContext,
    from_scope: ScopeId,
) -> Result<Vec<&'a ScopeColor>, ElabError> {
    let _ = ctx
        .name_bindings
        .get(&name.to_string())
        .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
    Ok(ctx.visible_bindings(name, from_scope))
}

fn scope_key() -> Name {
    Name::from_string("hyg.scope")
}

fn binder_keys() -> [Name; 2] {
    [
        Name::from_string("hyg.binder_name"),
        Name::from_string("binder.name"),
    ]
}

fn canonical_fvar_name(id: clean_kernel::FVarId) -> Name {
    Name::from_string(&format!("fvar_{}", id.as_u64()))
}

fn binder_name_from_metadata(metadata: &MDataMap) -> Option<Name> {
    let keys = binder_keys();
    metadata.iter().find_map(|(key, value)| {
        ((*key == keys[0]) || (*key == keys[1])).then(|| match value {
            MDataValue::Name(name) => Some(name.clone()),
            MDataValue::String(text) => Some(Name::from_string(text)),
            _ => None,
        })?
    })
}

fn scope_from_metadata(metadata: &MDataMap) -> Option<ScopeId> {
    metadata.iter().find_map(|(key, value)| {
        (*key == scope_key()).then_some(match value {
            MDataValue::Nat(scope) => Some(ScopeId(*scope)),
            _ => None,
        })?
    })
}

fn annotate(scope: ScopeId, expr: Expr) -> Expr {
    Expr::mdata(vec![(scope_key(), MDataValue::Nat(scope.id()))], expr)
}

fn rename_metadata(metadata: &MDataMap, avoid: &[Name], ctx: &mut HygieneContext) -> MDataMap {
    let keys = binder_keys();
    metadata
        .iter()
        .map(|(key, value)| {
            if *key == keys[0] || *key == keys[1] {
                match value {
                    MDataValue::Name(name) if avoid.iter().any(|avoid_name| avoid_name == name) => {
                        return (
                            key.clone(),
                            MDataValue::Name(ctx.fresh_name(&name.to_string())),
                        );
                    }
                    MDataValue::String(text) => {
                        let name = Name::from_string(text);
                        if avoid.iter().any(|avoid_name| avoid_name == &name) {
                            return (
                                key.clone(),
                                MDataValue::String(std::sync::Arc::from(
                                    ctx.fresh_name(text).to_string(),
                                )),
                            );
                        }
                    }
                    _ => {}
                }
            }
            (key.clone(), value.clone())
        })
        .collect()
}

fn rename_name(name: &Name, avoid: &[Name], ctx: &mut HygieneContext) -> Name {
    if avoid.iter().any(|avoid_name| avoid_name == name) {
        ctx.fresh_name(&name.to_string())
    } else {
        name.clone()
    }
}

fn check_ref(
    name: &Name,
    ctx: &HygieneContext,
    actual_scope: ScopeId,
    violations: &mut Vec<HygieneViolation>,
) {
    let current = ctx.current_scope();
    let visible = ctx.visible_bindings(name, current);
    let expected = visible
        .last()
        .map(|binding| binding.scope)
        .unwrap_or_else(ScopeId::root);
    if !actual_scope.is_root() && !ctx.is_scope_visible_from(actual_scope, current) {
        violations.push(HygieneViolation {
            name: name.clone(),
            expected_scope: expected,
            actual_scope,
            kind: ViolationKind::ScopeLeak,
        });
        return;
    }
    if let Some(binding) = visible.iter().find(|binding| binding.is_captured) {
        violations.push(HygieneViolation {
            name: name.clone(),
            expected_scope: expected,
            actual_scope: binding.scope,
            kind: ViolationKind::NameCapture,
        });
        return;
    }
    if visible.len() > 1 || (!visible.is_empty() && actual_scope != expected) {
        violations.push(HygieneViolation {
            name: name.clone(),
            expected_scope: expected,
            actual_scope,
            kind: if ctx.is_scope_visible_from(actual_scope, current) {
                ViolationKind::NameCapture
            } else {
                ViolationKind::ScopeLeak
            },
        });
        return;
    }
    if visible.is_empty() && name.to_string().starts_with('$') {
        violations.push(HygieneViolation {
            name: name.clone(),
            expected_scope: ScopeId::root(),
            actual_scope,
            kind: ViolationKind::UnresolvedMacroVar,
        });
    }
}

fn check_binder(name: &Name, ctx: &HygieneContext, violations: &mut Vec<HygieneViolation>) {
    let current = ctx.current_scope();
    if let Some(scope) = ctx
        .innermost_visible_scope(name, current)
        .filter(|scope| *scope != current)
    {
        violations.push(HygieneViolation {
            name: name.clone(),
            expected_scope: current,
            actual_scope: scope,
            kind: ViolationKind::NameCapture,
        });
    }
}

fn colorize(expr: &Expr, ctx: &HygieneContext, from_scope: ScopeId) -> Expr {
    match expr.kind() {
        ExprKind::BVar(idx) => Expr::bvar(*idx),
        ExprKind::FVar(id) => ctx
            .innermost_visible_scope(&canonical_fvar_name(*id), from_scope)
            .map_or_else(|| Expr::fvar(*id), |scope| annotate(scope, Expr::fvar(*id))),
        ExprKind::Sort(level) => Expr::sort(level.clone()),
        ExprKind::Const(name, levels) => {
            let base = if levels.is_empty() {
                Expr::const_str(&name.to_string())
            } else {
                Expr::from_kind(ExprKind::Const(name.clone(), levels.clone()))
            };
            ctx.innermost_visible_scope(name, from_scope)
                .map_or(base.clone(), |scope| annotate(scope, base))
        }
        ExprKind::App(func, arg) => Expr::app(
            colorize(func, ctx, from_scope),
            colorize(arg, ctx, from_scope),
        ),
        ExprKind::Lam(binder, ty, body) => Expr::lam(
            *binder,
            colorize(ty, ctx, from_scope),
            colorize(body, ctx, from_scope),
        ),
        ExprKind::Pi(binder, ty, body) => Expr::pi(
            *binder,
            colorize(ty, ctx, from_scope),
            colorize(body, ctx, from_scope),
        ),
        ExprKind::Let(name, ty, value, body, non_dep) => Expr::let_named(
            name.clone(),
            colorize(ty, ctx, from_scope),
            colorize(value, ctx, from_scope),
            colorize(body, ctx, from_scope),
            *non_dep,
        ),
        ExprKind::MData(metadata, inner) => {
            Expr::mdata(metadata.clone(), colorize(inner, ctx, from_scope))
        }
        ExprKind::Proj(struct_name, idx, inner) => {
            Expr::proj(struct_name.clone(), *idx, colorize(inner, ctx, from_scope))
        }
        _ => expr.clone(),
    }
}

fn rename(expr: Expr, avoid: &[Name], ctx: &mut HygieneContext) -> Expr {
    match expr.kind() {
        ExprKind::BVar(idx) => Expr::bvar(*idx),
        ExprKind::FVar(id) => Expr::fvar(*id),
        ExprKind::Sort(level) => Expr::sort(level.clone()),
        ExprKind::Const(name, levels) => {
            let name = rename_name(name, avoid, ctx);
            if levels.is_empty() {
                Expr::const_str(&name.to_string())
            } else {
                Expr::from_kind(ExprKind::Const(name, levels.clone()))
            }
        }
        ExprKind::App(func, arg) => Expr::app(
            rename((**func).clone(), avoid, ctx),
            rename((**arg).clone(), avoid, ctx),
        ),
        ExprKind::Lam(binder, ty, body) => Expr::lam(
            *binder,
            rename((**ty).clone(), avoid, ctx),
            rename((**body).clone(), avoid, ctx),
        ),
        ExprKind::Pi(binder, ty, body) => Expr::pi(
            *binder,
            rename((**ty).clone(), avoid, ctx),
            rename((**body).clone(), avoid, ctx),
        ),
        ExprKind::Let(name, ty, value, body, non_dep) => Expr::let_named(
            rename_name(name, avoid, ctx),
            rename((**ty).clone(), avoid, ctx),
            rename((**value).clone(), avoid, ctx),
            rename((**body).clone(), avoid, ctx),
            *non_dep,
        ),
        ExprKind::MData(metadata, inner) => {
            let metadata = if matches!(inner.kind(), ExprKind::Lam(_, _, _) | ExprKind::Pi(_, _, _))
            {
                rename_metadata(metadata, avoid, ctx)
            } else {
                metadata.clone()
            };
            Expr::mdata(metadata, rename((**inner).clone(), avoid, ctx))
        }
        ExprKind::Proj(struct_name, idx, inner) => Expr::proj(
            struct_name.clone(),
            *idx,
            rename((**inner).clone(), avoid, ctx),
        ),
        _ => expr,
    }
}

fn check(
    expr: &Expr,
    ctx: &HygieneContext,
    tagged_scope: Option<ScopeId>,
    violations: &mut Vec<HygieneViolation>,
) {
    match expr.kind() {
        ExprKind::Const(name, _) => check_ref(
            name,
            ctx,
            tagged_scope.unwrap_or_else(ScopeId::root),
            violations,
        ),
        ExprKind::FVar(id) => check_ref(
            &canonical_fvar_name(*id),
            ctx,
            tagged_scope.unwrap_or_else(ScopeId::root),
            violations,
        ),
        ExprKind::App(func, arg) => {
            check(func, ctx, tagged_scope, violations);
            check(arg, ctx, tagged_scope, violations);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            check(ty, ctx, tagged_scope, violations);
            check(body, ctx, tagged_scope, violations);
        }
        ExprKind::Let(name, ty, value, body, _) => {
            check_binder(name, ctx, violations);
            check(ty, ctx, tagged_scope, violations);
            check(value, ctx, tagged_scope, violations);
            check(body, ctx, tagged_scope, violations);
        }
        ExprKind::MData(metadata, inner) => {
            if matches!(inner.kind(), ExprKind::Lam(_, _, _) | ExprKind::Pi(_, _, _)) {
                if let Some(name) = binder_name_from_metadata(metadata) {
                    check_binder(&name, ctx, violations);
                }
            }
            check(
                inner,
                ctx,
                scope_from_metadata(metadata).or(tagged_scope),
                violations,
            );
        }
        ExprKind::Proj(_, _, inner) => check(inner, ctx, tagged_scope, violations),
        _ => {}
    }
}
