// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Ext2CheckCategory {
    OperandType,
    RcPath,
    ControlFlow,
    JoinPoint,
    CtorArity,
    ClosureArity,
    ScopedType,
    Erasure,
    Exhaustiveness,
}
impl Ext2CheckCategory {
    const ALL: [Self; 9] = [
        Self::OperandType,
        Self::RcPath,
        Self::ControlFlow,
        Self::JoinPoint,
        Self::CtorArity,
        Self::ClosureArity,
        Self::ScopedType,
        Self::Erasure,
        Self::Exhaustiveness,
    ];
}

#[derive(Debug, Clone, Default)]
pub(crate) struct CategoryStats {
    pub(crate) checks: u64,
    pub(crate) errors: u64,
}
pub(crate) type Ext2Stats = HashMap<Ext2CheckCategory, CategoryStats>;

#[derive(Debug, Clone, Default)]
pub(crate) struct Ext2CheckerResult {
    pub(crate) diagnostics: Vec<Ext2Error>,
    pub(crate) stats: Ext2Stats,
}

impl Ext2CheckerResult {
    pub(crate) fn has_errors(&self) -> bool {
        !self.diagnostics.is_empty()
    }
    pub(crate) fn error_count(&self) -> usize {
        self.diagnostics.len()
    }
    pub(crate) fn errors_in(&self, cat: Ext2CheckCategory) -> usize {
        self.diagnostics
            .iter()
            .filter(|e| e.category() == cat)
            .count()
    }
    pub(crate) fn total_checks(&self) -> u64 {
        self.stats.values().map(|s| s.checks).sum()
    }
}

#[derive(Debug, Clone, Error)]
#[error("[{cat:?}] {func}: {msg}")]
pub(crate) struct Ext2Error {
    pub(crate) cat: Ext2CheckCategory,
    pub(crate) func: String,
    pub(crate) msg: String,
}

impl Ext2Error {
    fn category(&self) -> Ext2CheckCategory {
        self.cat
    }
}

#[derive(Clone)]
struct JoinPointInfo {
    types: Vec<IRType>,
}
type Vars = HashMap<VarId, IRType>;
type Jps = HashMap<JoinPointId, JoinPointInfo>;
type RcMap = HashMap<VarId, i64>;

struct Ext2Checker {
    diagnostics: Vec<Ext2Error>,
    stats: Ext2Stats,
}

pub(crate) fn check_ir_ext2(decls: &[IRDecl]) -> Ext2CheckerResult {
    let mut checker = Ext2Checker::new();
    checker.run(decls)
}

impl Ext2Checker {
    fn new() -> Self {
        let stats = Ext2CheckCategory::ALL
            .into_iter()
            .map(|c| (c, CategoryStats::default()))
            .collect();
        Self {
            diagnostics: Vec::new(),
            stats,
        }
    }

    fn run(&mut self, decls: &[IRDecl]) -> Ext2CheckerResult {
        for decl in decls {
            self.check_decl(decl);
        }
        Ext2CheckerResult {
            diagnostics: std::mem::take(&mut self.diagnostics),
            stats: std::mem::take(&mut self.stats),
        }
    }

    fn record(&mut self, cat: Ext2CheckCategory) {
        self.stats.entry(cat).or_default().checks += 1;
    }

    fn emit(
        &mut self,
        cat: Ext2CheckCategory,
        function: &Name,
        site: impl Into<String>,
        message: impl Into<String>,
    ) {
        let err = Ext2Error {
            cat,
            func: format!("{function:?}"),
            msg: format!("{}: {}", site.into(), message.into()),
        };
        self.stats.entry(cat).or_default().errors += 1;
        self.diagnostics.push(err);
    }

    fn check_decl(&mut self, decl: &IRDecl) {
        let mut vars = Vars::new();
        for (var, ty) in &decl.params {
            self.insert_var(&decl.name, &mut vars, *var, ty.clone(), "param");
        }
        self.check_body(&decl.name, &decl.body, &vars, &Jps::new());
        self.record(Ext2CheckCategory::ControlFlow);
        if !self.terminates(&decl.body) {
            self.emit(
                Ext2CheckCategory::ControlFlow,
                &decl.name,
                "entry",
                "function body may fail to terminate on some paths",
            );
        }
        self.check_rc_paths(&decl.name, &decl.body, &RcMap::new(), "entry");
    }

    fn check_body(&mut self, function: &Name, body: &IRBody, vars: &Vars, jps: &Jps) {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                self.check_expr(function, value, vars);
                if let Some(found) = self.infer_expr_type(vars, value) {
                    self.record(Ext2CheckCategory::ScopedType);
                    if !runtime_compatible(ty, &found) {
                        self.emit(
                            Ext2CheckCategory::ScopedType,
                            function,
                            format!("vdecl x{}", var.0),
                            format!(
                                "declared type {ty:?} does not match inferred value type {found:?}"
                            ),
                        );
                    }
                }
                let mut next = vars.clone();
                self.insert_var(
                    function,
                    &mut next,
                    *var,
                    ty.clone(),
                    format!("vdecl x{}", var.0),
                );
                self.check_body(function, rest, &next, jps);
            }
            IRBody::JDecl {
                jp,
                params,
                body,
                rest,
            } => {
                let mut body_vars = vars.clone();
                for (var, ty) in params {
                    self.insert_var(
                        function,
                        &mut body_vars,
                        *var,
                        ty.clone(),
                        format!("jp{} param x{}", jp.0, var.0),
                    );
                }
                self.check_body(function, body, &body_vars, jps);
                self.record(Ext2CheckCategory::JoinPoint);
                let mut next_jps = jps.clone();
                if next_jps.contains_key(jp) {
                    self.emit(
                        Ext2CheckCategory::JoinPoint,
                        function,
                        format!("jp{}", jp.0),
                        "join point redeclared in the same scope",
                    );
                }
                next_jps.insert(
                    *jp,
                    JoinPointInfo {
                        types: params.iter().map(|(_, ty)| ty.clone()).collect(),
                    },
                );
                self.check_body(function, rest, vars, &next_jps);
            }
            IRBody::Inc { var, rest, .. } => {
                self.check_rc_operand(function, vars, *var, format!("inc x{}", var.0));
                self.check_body(function, rest, vars, jps);
            }
            IRBody::Dec { var, rest } => {
                self.check_rc_operand(function, vars, *var, format!("dec x{}", var.0));
                self.check_body(function, rest, vars, jps);
            }
            IRBody::Set {
                var, value, rest, ..
            } => {
                self.check_object_target(function, vars, *var, format!("set x{}", var.0));
                let val_ty =
                    self.touch_var(function, vars, *value, format!("set value x{}", value.0));
                self.record(Ext2CheckCategory::Erasure);
                if matches!(val_ty.as_ref(), Some(IRType::Erased)) {
                    self.emit(
                        Ext2CheckCategory::Erasure,
                        function,
                        format!("set value x{}", value.0),
                        "Erased type cannot appear as Set value",
                    );
                }
                self.check_body(function, rest, vars, jps);
            }
            IRBody::SetTag { var, rest, .. } => {
                self.touch_var(function, vars, *var, format!("setTag x{}", var.0));
                self.check_body(function, rest, vars, jps);
            }
            IRBody::USet {
                var, value, rest, ..
            } => {
                self.check_object_target(function, vars, *var, format!("uset x{}", var.0));
                let val_ty =
                    self.touch_var(function, vars, *value, format!("uset value x{}", value.0));
                if let Some(ref found) = val_ty {
                    self.record(Ext2CheckCategory::ScopedType);
                    if *found != IRType::USize {
                        self.emit(
                            Ext2CheckCategory::ScopedType,
                            function,
                            format!("uset value x{}", value.0),
                            format!("expected USize, found {found:?}"),
                        );
                    }
                }
                self.record(Ext2CheckCategory::Erasure);
                if matches!(val_ty.as_ref(), Some(IRType::Erased)) {
                    self.emit(
                        Ext2CheckCategory::Erasure,
                        function,
                        format!("uset value x{}", value.0),
                        "Erased type cannot appear as USet value",
                    );
                }
                self.check_body(function, rest, vars, jps);
            }
            IRBody::SSet {
                var,
                value,
                ty,
                rest,
                ..
            } => {
                self.check_object_target(function, vars, *var, format!("sset x{}", var.0));
                self.record(Ext2CheckCategory::OperandType);
                if !ty.is_scalar() {
                    self.emit(
                        Ext2CheckCategory::OperandType,
                        function,
                        format!("sset x{}", var.0),
                        format!("SSet field type must be scalar, found {ty:?}"),
                    );
                }
                let val_ty =
                    self.touch_var(function, vars, *value, format!("sset value x{}", value.0));
                if let Some(ref found) = val_ty {
                    self.record(Ext2CheckCategory::ScopedType);
                    if !runtime_compatible(ty, found) {
                        self.emit(
                            Ext2CheckCategory::ScopedType,
                            function,
                            format!("sset value x{}", value.0),
                            format!(
                                "declared field type {ty:?} does not match value type {found:?}"
                            ),
                        );
                    }
                }
                self.record(Ext2CheckCategory::Erasure);
                if matches!(val_ty.as_ref(), Some(IRType::Erased)) {
                    self.emit(
                        Ext2CheckCategory::Erasure,
                        function,
                        format!("sset value x{}", value.0),
                        "Erased type cannot appear as SSet value",
                    );
                }
                self.check_body(function, rest, vars, jps);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                let scr_ty = self.touch_var(
                    function,
                    vars,
                    *scrutinee,
                    format!("case scrutinee x{}", scrutinee.0),
                );
                self.record(Ext2CheckCategory::Erasure);
                if matches!(scr_ty.as_ref(), Some(IRType::Erased)) {
                    self.emit(
                        Ext2CheckCategory::Erasure,
                        function,
                        format!("case scrutinee x{}", scrutinee.0),
                        "Erased type cannot appear as Case scrutinee",
                    );
                }
                self.check_exhaustiveness(function, alts, default);
                for alt in alts {
                    self.check_body(function, &alt.body, vars, jps);
                }
                if let Some(default) = default.as_deref() {
                    self.check_body(function, default, vars, jps);
                }
            }
            IRBody::Jmp { jp, args } => self.check_jump(function, vars, jps, *jp, args),
            IRBody::Ret(arg) => {
                self.touch_arg(function, vars, arg, "ret");
            }
            IRBody::Unreachable => {}
        }
    }

    fn check_expr(&mut self, function: &Name, expr: &IRExpr, vars: &Vars) {
        match expr {
            IRExpr::Ctor { info, args } => {
                self.check_ctor_arity(function, info, args, "ctor");
                self.touch_args(function, vars, args, "ctor arg");
            }
            IRExpr::Proj { arg, .. } | IRExpr::Tag(arg) | IRExpr::Unbox { arg, .. } => {
                self.expect_arg_object(function, vars, arg, "object arg")
            }
            IRExpr::Box { ty, arg } => {
                self.record(Ext2CheckCategory::Erasure);
                if matches!(arg, IRArg::Erased) {
                    self.emit(
                        Ext2CheckCategory::Erasure,
                        function,
                        "box",
                        "IRArg::Erased cannot appear in Box",
                    );
                }
                if let Some(found) = self.touch_arg(function, vars, arg, "box") {
                    self.record(Ext2CheckCategory::ScopedType);
                    if !runtime_compatible(ty, &found) {
                        self.emit(
                            Ext2CheckCategory::ScopedType,
                            function,
                            "box",
                            format!("boxed type {ty:?} does not match argument type {found:?}"),
                        );
                    }
                }
            }
            IRExpr::Lit(_) | IRExpr::String(_) => {}
            IRExpr::Apply { args, .. } => self.touch_args(function, vars, args, "apply arg"),
            IRExpr::PartialApply { fn_id, arity, args } => {
                self.check_partial_apply(function, fn_id, *arity, args);
                self.touch_args(function, vars, args, "partial_apply arg");
            }
            IRExpr::ClosureApply { closure, args } => {
                self.record(Ext2CheckCategory::ClosureArity);
                if args.is_empty() {
                    self.emit(
                        Ext2CheckCategory::ClosureArity,
                        function,
                        "closure_apply",
                        "ClosureApply requires at least one argument",
                    );
                }
                self.expect_arg_object(function, vars, closure, "closure_apply");
                self.touch_args(function, vars, args, "closure_apply arg");
            }
            IRExpr::UProj { var, .. }
            | IRExpr::SProj { var, .. }
            | IRExpr::IsShared(var)
            | IRExpr::Reset(var) => {
                self.expect_var_object(function, vars, *var, format!("object x{}", var.0))
            }
            IRExpr::Reuse { var, ctor, args } => {
                self.check_ctor_arity(function, ctor, args, "reuse");
                self.expect_var_object(function, vars, *var, format!("reuse x{}", var.0));
                self.touch_args(function, vars, args, "reuse arg");
            }
        }
    }

    fn check_jump(
        &mut self,
        function: &Name,
        vars: &Vars,
        jps: &Jps,
        jp: JoinPointId,
        args: &[IRArg],
    ) {
        self.record(Ext2CheckCategory::JoinPoint);
        let Some(info) = jps.get(&jp) else {
            self.emit(
                Ext2CheckCategory::JoinPoint,
                function,
                format!("jmp jp{}", jp.0),
                "jump target is out of scope or undeclared",
            );
            return;
        };
        if args.len() != info.types.len() {
            self.emit(
                Ext2CheckCategory::JoinPoint,
                function,
                format!("jmp jp{}", jp.0),
                format!("expected {} args, found {}", info.types.len(), args.len()),
            );
        }
        for (arg, expected) in args.iter().zip(&info.types) {
            if let Some(found) = self.touch_arg(function, vars, arg, format!("jmp jp{} arg", jp.0))
            {
                self.record(Ext2CheckCategory::ScopedType);
                if !runtime_compatible(expected, &found) {
                    self.emit(
                        Ext2CheckCategory::ScopedType,
                        function,
                        format!("jmp jp{}", jp.0),
                        format!("expected {expected:?}, found {found:?}"),
                    );
                }
            }
        }
    }

    fn check_ctor_arity(&mut self, function: &Name, info: &CtorInfo, args: &[IRArg], site: &str) {
        self.record(Ext2CheckCategory::CtorArity);
        if args.len() != info.field_types.len() {
            self.emit(
                Ext2CheckCategory::CtorArity,
                function,
                site,
                format!(
                    "constructor {:?} expects {} args, found {}",
                    info.name,
                    info.field_types.len(),
                    args.len()
                ),
            );
        }
    }

    fn check_partial_apply(&mut self, function: &Name, fn_id: &FnId, arity: u16, args: &[IRArg]) {
        self.record(Ext2CheckCategory::ClosureArity);
        if args.len() >= usize::from(arity) {
            self.emit(
                Ext2CheckCategory::ClosureArity,
                function,
                format!("partial_apply {:?}", fn_id.0),
                format!(
                    "expected fewer than {arity} captured args, found {}",
                    args.len()
                ),
            );
        }
    }

    fn insert_var(
        &mut self,
        function: &Name,
        vars: &mut Vars,
        var: VarId,
        ty: IRType,
        site: impl Into<String>,
    ) {
        self.record(Ext2CheckCategory::ScopedType);
        let site = site.into();
        if let Some(old) = vars.get(&var) {
            if !runtime_compatible(old, &ty) {
                self.emit(
                    Ext2CheckCategory::ScopedType,
                    function,
                    site,
                    format!("x{} changes type from {old:?} to {ty:?}", var.0),
                );
            }
        }
        vars.insert(var, ty);
    }

    fn touch_var(
        &mut self,
        function: &Name,
        vars: &Vars,
        var: VarId,
        site: impl Into<String>,
    ) -> Option<IRType> {
        self.record(Ext2CheckCategory::ScopedType);
        let site = site.into();
        match vars.get(&var) {
            Some(ty) => Some(ty.clone()),
            None => {
                self.emit(
                    Ext2CheckCategory::ScopedType,
                    function,
                    site,
                    format!("x{} is used without an in-scope type", var.0),
                );
                None
            }
        }
    }

    fn touch_arg(
        &mut self,
        function: &Name,
        vars: &Vars,
        arg: &IRArg,
        site: impl Into<String>,
    ) -> Option<IRType> {
        match arg {
            IRArg::Var(var) => self.touch_var(function, vars, *var, site),
            IRArg::Erased => None,
        }
    }

    fn touch_args(&mut self, function: &Name, vars: &Vars, args: &[IRArg], site: &str) {
        for arg in args {
            self.touch_arg(function, vars, arg, site);
        }
    }

    fn check_rc_operand(
        &mut self,
        function: &Name,
        vars: &Vars,
        var: VarId,
        site: impl Into<String>,
    ) {
        self.record(Ext2CheckCategory::OperandType);
        let site = site.into();
        if let Some(ty) = self.touch_var(function, vars, var, site.clone()) {
            if !ty.is_rc_type() && ty != IRType::Erased {
                self.emit(
                    Ext2CheckCategory::OperandType,
                    function,
                    site,
                    format!("Inc/Dec require an object/RC or erased type, found {ty:?}"),
                );
            }
        }
    }

    fn check_object_target(
        &mut self,
        function: &Name,
        vars: &Vars,
        var: VarId,
        site: impl Into<String>,
    ) {
        self.record(Ext2CheckCategory::OperandType);
        let site = site.into();
        if let Some(ty) = self.touch_var(function, vars, var, site.clone()) {
            if !ty.is_object() {
                self.emit(
                    Ext2CheckCategory::OperandType,
                    function,
                    site,
                    format!("mutable update target must be an object type, found {ty:?}"),
                );
            }
        }
    }

    fn expect_var_object(
        &mut self,
        function: &Name,
        vars: &Vars,
        var: VarId,
        site: impl Into<String>,
    ) {
        self.record(Ext2CheckCategory::ScopedType);
        let site = site.into();
        if let Some(ty) = self.touch_var(function, vars, var, site.clone()) {
            if !ty.is_object() {
                self.emit(
                    Ext2CheckCategory::ScopedType,
                    function,
                    site,
                    format!("expected object type, found {ty:?}"),
                );
            }
        }
    }

    fn expect_arg_object(
        &mut self,
        function: &Name,
        vars: &Vars,
        arg: &IRArg,
        site: impl Into<String>,
    ) {
        self.record(Ext2CheckCategory::ScopedType);
        let site = site.into();
        if let Some(ty) = self.touch_arg(function, vars, arg, site.clone()) {
            if !ty.is_object() {
                self.emit(
                    Ext2CheckCategory::ScopedType,
                    function,
                    site,
                    format!("expected object argument, found {ty:?}"),
                );
            }
        }
    }

    fn infer_expr_type(&self, vars: &Vars, expr: &IRExpr) -> Option<IRType> {
        match expr {
            IRExpr::Ctor { .. }
            | IRExpr::String(_)
            | IRExpr::PartialApply { .. }
            | IRExpr::Box { .. }
            | IRExpr::Reuse { .. } => Some(IRType::Object),
            IRExpr::Proj { ty, .. } | IRExpr::SProj { ty, .. } | IRExpr::Unbox { ty, .. } => {
                Some(ty.clone())
            }
            IRExpr::Tag(_) | IRExpr::UProj { .. } => Some(IRType::USize),
            IRExpr::Lit(lit) => Some(literal_type(lit)),
            IRExpr::IsShared(_) => Some(IRType::UInt8),
            IRExpr::Reset(var) => vars.get(var).cloned(),
            IRExpr::Apply { .. } | IRExpr::ClosureApply { .. } => None,
        }
    }

    fn check_exhaustiveness(
        &mut self,
        function: &Name,
        alts: &[IRAlt],
        default: &Option<Box<IRBody>>,
    ) {
        self.record(Ext2CheckCategory::Exhaustiveness);
        if !default.is_some() && !case_complete(alts) {
            self.emit(
                Ext2CheckCategory::Exhaustiveness,
                function,
                "case",
                "potentially non-exhaustive case: missing default or missing constructor tags",
            );
        }
    }

    fn terminates(&self, body: &IRBody) -> bool {
        match body {
            IRBody::VDecl { rest, .. }
            | IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => self.terminates(rest),
            IRBody::JDecl { body, rest, .. } => self.terminates(body) && self.terminates(rest),
            IRBody::Case { alts, default, .. } => {
                let default_ok = match default.as_deref() {
                    Some(body) => self.terminates(body),
                    None => true,
                };
                (default.is_some() || case_complete(alts))
                    && default_ok
                    && alts.iter().all(|alt| self.terminates(&alt.body))
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => true,
        }
    }

    fn check_rc_paths(&mut self, function: &Name, body: &IRBody, rc: &RcMap, path: &str) {
        match body {
            IRBody::Inc { var, n, rest } => {
                self.record(Ext2CheckCategory::RcPath);
                let mut next = rc.clone();
                *next.entry(*var).or_insert(0) += i64::from(*n);
                self.check_rc_paths(function, rest, &next, path);
            }
            IRBody::Dec { var, rest } => {
                self.record(Ext2CheckCategory::RcPath);
                let mut next = rc.clone();
                *next.entry(*var).or_insert(0) -= 1;
                self.check_rc_paths(function, rest, &next, path);
            }
            IRBody::VDecl { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => self.check_rc_paths(function, rest, rc, path),
            IRBody::JDecl { jp, body, rest, .. } => {
                self.check_rc_paths(function, body, rc, &format!("{path}/jp{}", jp.0));
                self.check_rc_paths(function, rest, rc, &format!("{path}/after_jp{}", jp.0));
            }
            IRBody::Case { alts, default, .. } => {
                for alt in alts {
                    self.check_rc_paths(
                        function,
                        &alt.body,
                        rc,
                        &format!("{path}/tag{}", alt.ctor.tag),
                    );
                }
                if let Some(default) = default.as_deref() {
                    self.check_rc_paths(function, default, rc, &format!("{path}/default"));
                }
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {
                self.record(Ext2CheckCategory::RcPath);
                for (var, bal) in rc.iter().filter(|(_, bal)| **bal < -1) {
                    self.emit(
                        Ext2CheckCategory::RcPath,
                        function,
                        path,
                        format!("path ends with RC balance {} for x{}", bal, var.0),
                    );
                }
            }
        }
    }
}

fn runtime_compatible(expected: &IRType, found: &IRType) -> bool {
    expected == found || (expected.is_object() && found.is_object())
}

fn case_complete(alts: &[IRAlt]) -> bool {
    let seen: HashSet<u32> = alts.iter().map(|alt| alt.ctor.tag).collect();
    match alts.iter().map(|alt| alt.ctor.tag).max() {
        Some(max_tag) => (seen.len() as u32) == max_tag.saturating_add(1),
        None => false,
    }
}

fn literal_type(lit: &IRLiteral) -> IRType {
    match lit {
        IRLiteral::Bool(_) => IRType::Bool,
        IRLiteral::UInt8(_) => IRType::UInt8,
        IRLiteral::UInt16(_) => IRType::UInt16,
        IRLiteral::UInt32(_) => IRType::UInt32,
        IRLiteral::UInt64(_) => IRType::UInt64,
        IRLiteral::USize(_) => IRType::USize,
        IRLiteral::NatBig(_) => IRType::Object,
        IRLiteral::Float32(_) => IRType::Float32,
        IRLiteral::Float64(_) => IRType::Float64,
    }
}
