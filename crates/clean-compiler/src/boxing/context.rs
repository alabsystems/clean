// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boxing pass context — tracks variable types, aux decls, and config.

use crate::compiler_env::CompilerEnv;
use crate::ir::{FnId, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use clean_kernel::Name;
use std::cell::RefCell;
use std::collections::HashMap;

use super::config::BoxingConfig;

pub struct BoxingContext<'a> {
    fn_name: Name,
    result_type: IRType,
    var_types: HashMap<VarId, IRType>,
    var_values: HashMap<VarId, IRExpr>,
    jp_params: HashMap<JoinPointId, Vec<IRType>>,
    decls: &'a [IRDecl],
    /// Index from declaration name to position in `decls` for O(1) lookup.
    /// Used when no `CompilerEnv` is provided (legacy path).
    decl_index: HashMap<Name, usize>,
    /// Unified compiler environment. When present, `get_decl` delegates here
    /// instead of using the local `decl_index`. Part of #1970.
    env: Option<&'a CompilerEnv>,
    aux_decls: Vec<IRDecl>,
    next_var: u32,
    next_aux: u32,
    /// Configuration for boxing behavior.
    pub(crate) config: BoxingConfig,
    /// Diagnostic warnings for silent defaults (#1930).
    pub(crate) warnings: RefCell<Vec<String>>,
}

impl<'a> BoxingContext<'a> {
    pub fn new(decl: &IRDecl, decls: &'a [IRDecl], config: &BoxingConfig) -> Self {
        let mut var_types = HashMap::new();
        for (var_id, ty) in &decl.params {
            var_types.insert(*var_id, ty.clone());
        }
        // SOUNDNESS: seed the fresh-VarId counter from the max VarId across BOTH
        // params and the decl body. `to_ir` numbers VarIds continuously (params
        // first, then body locals), so body locals can exceed the largest param
        // id. Scanning params alone under-seeds `next_var`, causing mk_fresh_var
        // to hand back a VarId already defined in the body — producing a
        // duplicate VDecl that the IR checker's V2 rule rightly rejects as
        // DuplicateDefinition. Taking the max over the body keeps every fresh
        // VarId genuinely unused. (#boxing-duplicate-varid)
        let max_var = decl
            .params
            .iter()
            .map(|(v, _)| v.0)
            .max()
            .unwrap_or(0)
            .max(crate::inline_pass::max_var_id(&decl.body));
        // Build O(1) lookup index from declaration names to positions
        let decl_index: HashMap<Name, usize> = decls
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.clone(), i))
            .collect();
        Self {
            fn_name: decl.name.clone(),
            result_type: decl.return_type.clone(),
            var_types,
            var_values: HashMap::new(),
            jp_params: HashMap::new(),
            decls,
            decl_index,
            env: None,
            aux_decls: Vec::new(),
            next_var: max_var + 1,
            next_aux: 0,
            config: config.clone(),
            warnings: RefCell::new(Vec::new()),
        }
    }

    /// Create a boxing context backed by a unified `CompilerEnv`.
    ///
    /// Delegates declaration lookup to the shared environment instead of
    /// building a per-context `decl_index`. Part of #1970.
    pub fn new_with_env(
        decl: &IRDecl,
        decls: &'a [IRDecl],
        env: &'a CompilerEnv,
        config: &BoxingConfig,
    ) -> Self {
        let mut var_types = HashMap::new();
        for (var_id, ty) in &decl.params {
            var_types.insert(*var_id, ty.clone());
        }
        // SOUNDNESS: see `new` — seed `next_var` from the max VarId across both
        // params and body so mk_fresh_var never collides with an existing body
        // local. (#boxing-duplicate-varid)
        let max_var = decl
            .params
            .iter()
            .map(|(v, _)| v.0)
            .max()
            .unwrap_or(0)
            .max(crate::inline_pass::max_var_id(&decl.body));
        Self {
            fn_name: decl.name.clone(),
            result_type: decl.return_type.clone(),
            var_types,
            var_values: HashMap::new(),
            jp_params: HashMap::new(),
            decls,
            decl_index: HashMap::new(), // unused when env is present
            env: Some(env),
            aux_decls: Vec::new(),
            next_var: max_var + 1,
            next_aux: 0,
            config: config.clone(),
            warnings: RefCell::new(Vec::new()),
        }
    }

    /// Create context with default config (all optimizations enabled).
    pub fn new_default(decl: &IRDecl, decls: &'a [IRDecl]) -> Self {
        Self::new(decl, decls, &BoxingConfig::new())
    }
    pub fn mk_fresh_var(&mut self) -> VarId {
        let id = VarId(self.next_var);
        self.next_var += 1;
        id
    }
    pub(crate) fn next_aux_id(&mut self) -> u32 {
        let id = self.next_aux;
        self.next_aux += 1;
        id
    }
    pub fn get_var_type(&self, var: VarId) -> IRType {
        self.var_types.get(&var).cloned().unwrap_or_else(|| {
            self.warnings.borrow_mut().push(format!(
                "unknown VarId {:?} in boxing, defaulting to Object",
                var
            ));
            IRType::Object
        })
    }
    pub fn set_var_type(&mut self, var: VarId, ty: IRType) {
        self.var_types.insert(var, ty);
    }
    pub fn get_var_value(&self, var: VarId) -> Option<&IRExpr> {
        self.var_values.get(&var)
    }
    pub fn set_var_value(&mut self, var: VarId, value: IRExpr) {
        self.var_values.insert(var, value);
    }
    pub fn result_type(&self) -> &IRType {
        &self.result_type
    }
    pub fn get_jp_params(&self, jp: JoinPointId) -> Vec<IRType> {
        self.jp_params.get(&jp).cloned().unwrap_or_default()
    }
    pub fn set_jp_params(&mut self, jp: JoinPointId, params: Vec<IRType>) {
        self.jp_params.insert(jp, params);
    }
    /// Look up a declaration by function ID. O(1) via HashMap index (#1109).
    ///
    /// Delegates to `CompilerEnv` when available (Part of #1970), otherwise
    /// falls back to the local `decl_index`.
    pub fn get_decl(&self, fn_id: &FnId) -> Option<&IRDecl> {
        if let Some(env) = self.env {
            env.get_decl(&fn_id.0, self.decls)
        } else {
            self.decl_index.get(&fn_id.0).map(|&i| &self.decls[i])
        }
    }
    pub fn add_aux_decl(&mut self, decl: IRDecl) {
        self.aux_decls.push(decl);
    }
    pub fn take_aux_decls(&mut self) -> Vec<IRDecl> {
        std::mem::take(&mut self.aux_decls)
    }
    pub fn mk_aux_name(&mut self) -> Name {
        let id = self.next_aux_id();
        self.fn_name.clone().str(format!("_boxed_const_{}", id))
    }

    /// Check if function needs boxed version for partial application.
    pub(crate) fn requires_boxed_version_for_pap(&self, fn_id: &FnId) -> bool {
        self.get_decl(fn_id)
            .map(super::boxed_version::requires_boxed_version)
            .unwrap_or(false)
    }

    /// Compute expected scrutinee type for case analysis based on constructors.
    /// Returns USize only when there is no default branch AND all alternatives
    /// are scalar. A default branch may need the full object (e.g., to access
    /// fields or pass to another function), so its presence forces Object.
    pub(crate) fn expected_case_scrutinee_type(
        alts: &[crate::ir::IRAlt],
        has_default: bool,
    ) -> IRType {
        if !has_default
            && alts
                .iter()
                .all(|a| a.ctor.num_objects == 0 && a.ctor.num_scalars <= 1)
        {
            IRType::USize // Tag value is enough
        } else {
            IRType::Object
        }
    }

    /// Check if a variable holds an expensive constant that should be boxed once.
    /// Returns Some(aux_call_expr) if an aux decl was created, None otherwise.
    pub(crate) fn expensive_constant_boxing(
        var: VarId,
        var_type: &IRType,
        ctx: &mut BoxingContext<'_>,
    ) -> Option<IRExpr> {
        use crate::ir::{FnId, IRArg, IRBody};

        // Skip cheap types - small integers fit in tagged pointers
        match var_type {
            IRType::UInt8 | IRType::UInt16 | IRType::Bool => return None,
            _ if !var_type.is_scalar() => return None,
            _ => {}
        }

        let value = ctx.get_var_value(var)?.clone();
        let is_expensive = match &value {
            IRExpr::Lit(_) => true,
            IRExpr::Apply { args, .. } if args.is_empty() => true,
            _ => false,
        };
        if !is_expensive {
            return None;
        }

        // Create aux decl that boxes once at init time
        let aux_name = ctx.mk_aux_name();
        let aux_body = IRBody::VDecl {
            var: VarId(0),
            ty: var_type.clone(),
            value,
            rest: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty: var_type.clone(),
                    arg: IRArg::Var(VarId(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            }),
        };
        let aux_decl = IRDecl {
            name: aux_name.clone(),
            params: vec![],
            return_type: IRType::Object,
            body: aux_body,
        };
        ctx.add_aux_decl(aux_decl);
        Some(IRExpr::Apply {
            fn_id: FnId(aux_name),
            args: vec![],
        })
    }
}
