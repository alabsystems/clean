// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded structural retention accounting. This inspects existing syntax;
//! it neither parses nor classifies primitive semantics. Unknown syntax is
//! unobserved. Limits are checked before retaining/cloning any payload.

use super::{ObservationGap, ObservationLimit, ObservationLimits};
use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, LetValue, Param};
use clean_kernel::name::NameInner;
use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, Name};
use std::collections::HashSet;
use std::mem::size_of;

pub(super) struct Meter {
    pub bytes: usize,
    pub work: usize,
    bytes_left: usize,
    work_left: usize,
    depth: usize,
}
impl Meter {
    pub fn new(limits: ObservationLimits, bytes: usize, work: usize) -> Self {
        Self {
            bytes: 0,
            work: 0,
            bytes_left: limits.byte_limit().saturating_sub(bytes),
            work_left: limits.work_limit().saturating_sub(work),
            depth: limits.depth_limit(),
        }
    }
    pub(super) fn add(&mut self, bytes: usize) -> Result<(), ObservationGap> {
        if self.work == self.work_left {
            return Err(ObservationGap::Truncated(ObservationLimit::Work));
        }
        self.work += 1;
        if bytes > self.bytes_left.saturating_sub(self.bytes) {
            return Err(ObservationGap::Truncated(ObservationLimit::Bytes));
        }
        self.bytes += bytes;
        Ok(())
    }
    pub(super) fn check_depth(&self, depth: usize) -> Result<(), ObservationGap> {
        if depth > self.depth {
            Err(ObservationGap::Truncated(ObservationLimit::Depth))
        } else {
            Ok(())
        }
    }
    fn name(&mut self, name: &Name) -> Result<(), ObservationGap> {
        let mut current = name;
        let mut depth = 0;
        loop {
            self.check_depth(depth)?;
            self.add(size_of::<Name>() + size_of::<NameInner>())?;
            match current.inner() {
                NameInner::Anon => return Ok(()),
                NameInner::Str(parent, part) => {
                    self.add(part.len())?;
                    current = parent;
                }
                NameInner::Num(parent, _) => current = parent,
            }
            depth += 1;
        }
    }
    fn level(&mut self, root: &Level) -> Result<(), ObservationGap> {
        let mut pending = vec![(root, 0)];
        while let Some((level, depth)) = pending.pop() {
            self.check_depth(depth)?;
            self.add(size_of::<Level>() + 2 * size_of::<usize>())?;
            match level {
                Level::Zero => {}
                Level::Param(name) => self.name(name)?,
                Level::Succ(a) => pending.push((a, depth + 1)),
                Level::Max(a, b) | Level::IMax(a, b) => {
                    pending.push((a, depth + 1));
                    pending.push((b, depth + 1));
                }
            }
        }
        Ok(())
    }
    fn literal(&mut self, literal: &Literal) -> Result<(), ObservationGap> {
        self.add(size_of::<Literal>())?;
        match literal {
            Literal::Nat(BigNat::Small(_)) => Ok(()),
            Literal::Nat(BigNat::Big(limbs)) => {
                self.add(limbs.len().saturating_mul(size_of::<u64>()))
            }
            Literal::String(s) => self.add(s.len()),
        }
    }
    fn expr(&mut self, root: &Expr) -> Result<(), ObservationGap> {
        let mut pending = vec![(root, 0)];
        let mut seen = HashSet::new();
        while let Some((expr, depth)) = pending.pop() {
            self.check_depth(depth)?;
            self.add(size_of::<Expr>() + 2 * size_of::<usize>())?;
            // Address identity only avoids repeated traversal; it grants no
            // semantic equality and does not invoke adversarial deep Expr::eq.
            if !seen.insert(std::ptr::from_ref(expr) as usize) {
                continue;
            }
            match expr.kind() {
                ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::SProp => {}
                ExprKind::Sort(level) => self.level(level)?,
                ExprKind::Const(name, levels) => {
                    self.name(name)?;
                    for level in levels {
                        self.level(level)?;
                    }
                }
                ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
                    pending.push((a, depth + 1));
                    pending.push((b, depth + 1));
                }
                ExprKind::Let(name, ty, value, body, _) => {
                    self.name(name)?;
                    pending.push((ty, depth + 1));
                    pending.push((value, depth + 1));
                    pending.push((body, depth + 1));
                }
                ExprKind::Proj(name, _, value) => {
                    self.name(name)?;
                    pending.push((value, depth + 1));
                }
                ExprKind::Lit(literal) => self.literal(literal)?,
                _ => {
                    return Err(ObservationGap::Unobserved {
                        owner: "source expression retention",
                        reason: "expression payload lacks bounded observation traversal",
                    })
                }
            }
        }
        Ok(())
    }
    fn args(&mut self, args: &[Arg]) -> Result<(), ObservationGap> {
        for arg in args {
            self.add(size_of::<Arg>())?;
            if let Arg::Type(ty) = arg {
                self.expr(ty)?;
            }
        }
        Ok(())
    }
    fn params(&mut self, params: &[Param]) -> Result<(), ObservationGap> {
        for param in params {
            self.add(size_of::<Param>())?;
            self.name(&param.name)?;
            self.expr(&param.ty)?;
        }
        Ok(())
    }
    pub fn value(&mut self, value: &LetValue) -> Result<(), ObservationGap> {
        self.add(size_of::<LetValue>())?;
        match value {
            LetValue::Lit(literal) => self.literal(literal)?,
            LetValue::Erased => {}
            LetValue::Proj { type_name, .. } => self.name(type_name)?,
            LetValue::FVar { args, .. } => self.args(args)?,
            LetValue::Const { name, levels, args }
            | LetValue::Ctor { name, levels, args }
            | LetValue::Reuse {
                ctor_name: name,
                levels,
                args,
                ..
            } => {
                self.name(name)?;
                for level in levels {
                    self.level(level)?;
                }
                self.args(args)?;
            }
        }
        Ok(())
    }
    pub fn code(&mut self, root: &Code) -> Result<(), ObservationGap> {
        let mut pending = vec![(root, 0)];
        while let Some((code, depth)) = pending.pop() {
            self.check_depth(depth)?;
            self.add(size_of::<Code>())?;
            match code {
                Code::Let(decl, rest) => {
                    self.name(&decl.name)?;
                    self.expr(&decl.ty)?;
                    self.value(&decl.value)?;
                    pending.push((rest, depth + 1));
                }
                Code::Fun(decl, rest) | Code::JoinPoint(decl, rest) => {
                    self.name(&decl.name)?;
                    self.params(&decl.params)?;
                    self.expr(&decl.ty)?;
                    pending.push((&decl.body, depth + 1));
                    pending.push((rest, depth + 1));
                }
                Code::Cases(cases) => {
                    self.name(&cases.type_name)?;
                    self.expr(&cases.result_type)?;
                    // Charge each alternative before growing the work stack.
                    for alt in &cases.alts {
                        self.add(size_of::<Alt>())?;
                        match alt {
                            Alt::Ctor {
                                ctor_name,
                                params,
                                body,
                            } => {
                                self.name(ctor_name)?;
                                self.params(params)?;
                                pending.push((body, depth + 1));
                            }
                            Alt::Default(body) => pending.push((body, depth + 1)),
                        }
                    }
                }
                Code::Jmp { args, .. } => self.args(args)?,
                Code::Unreachable(ty) => self.expr(ty)?,
                Code::Return(_) => {}
            }
        }
        Ok(())
    }
    pub fn declarations(&mut self, decls: &[Decl]) -> Result<(), ObservationGap> {
        for decl in decls {
            self.add(size_of::<Decl>())?;
            self.name(&decl.name)?;
            for name in &decl.level_params {
                self.name(name)?;
            }
            self.expr(&decl.ty)?;
            self.params(&decl.params)?;
            match &decl.body {
                DeclValue::Code(code) => self.code(code)?,
                DeclValue::Extern(_) => {
                    return Err(ObservationGap::Unobserved {
                        owner: "LCNF extern retention",
                        reason: "extern payload retention is not observed",
                    })
                }
            }
        }
        Ok(())
    }
}

impl Meter {
    pub fn ir_type(&mut self, root: &crate::ir::IRType) -> Result<(), ObservationGap> {
        use crate::ir::IRType;
        let mut pending = vec![(root, 0)];
        while let Some((ty, depth)) = pending.pop() {
            self.check_depth(depth)?;
            self.add(size_of::<IRType>())?;
            if let IRType::Struct(types) | IRType::Union(types) = ty {
                for ty in types {
                    self.add(size_of::<&IRType>())?;
                    pending.push((ty, depth + 1));
                }
            }
        }
        Ok(())
    }
    fn ctor(&mut self, ctor: &crate::ir::CtorInfo) -> Result<(), ObservationGap> {
        self.add(size_of::<crate::ir::CtorInfo>())?;
        self.name(&ctor.name)?;
        for ty in &ctor.field_types {
            self.ir_type(ty)?;
        }
        Ok(())
    }
    pub fn ir_expr(&mut self, expr: &crate::ir::IRExpr) -> Result<(), ObservationGap> {
        use crate::ir::{IRArg, IRExpr};
        self.add(size_of::<IRExpr>())?;
        match expr {
            IRExpr::Ctor { info, args }
            | IRExpr::Reuse {
                ctor: info, args, ..
            } => {
                self.ctor(info)?;
                for _ in args {
                    self.add(size_of::<IRArg>())?;
                }
            }
            IRExpr::Apply { fn_id, args } | IRExpr::PartialApply { fn_id, args, .. } => {
                self.name(&fn_id.0)?;
                for _ in args {
                    self.add(size_of::<IRArg>())?;
                }
            }
            IRExpr::ClosureApply { args, .. } => {
                for _ in args {
                    self.add(size_of::<IRArg>())?;
                }
            }
            IRExpr::Box { ty, .. }
            | IRExpr::Unbox { ty, .. }
            | IRExpr::Proj { ty, .. }
            | IRExpr::SProj { ty, .. } => self.ir_type(ty)?,
            IRExpr::String(s) => self.add(s.len())?,
            IRExpr::Lit(_)
            | IRExpr::Tag(_)
            | IRExpr::UProj { .. }
            | IRExpr::IsShared(_)
            | IRExpr::Reset(_) => {}
        }
        Ok(())
    }
    pub fn ir_declarations(&mut self, decls: &[crate::ir::IRDecl]) -> Result<(), ObservationGap> {
        use crate::ir::{IRArg, IRBody, IRDecl, IRType, VarId};
        for decl in decls {
            self.add(size_of::<IRDecl>())?;
            self.name(&decl.name)?;
            self.ir_type(&decl.return_type)?;
            for (_, ty) in &decl.params {
                // Reserve the entire vector element, including tuple padding,
                // before inspecting any nested type payload.
                self.add(size_of::<(VarId, IRType)>())?;
                self.ir_type(ty)?;
            }
            let mut pending = vec![(&decl.body, 0)];
            while let Some((body, depth)) = pending.pop() {
                self.check_depth(depth)?;
                self.add(size_of::<IRBody>())?;
                match body {
                    IRBody::VDecl {
                        ty, value, rest, ..
                    } => {
                        self.ir_type(ty)?;
                        self.ir_expr(value)?;
                        pending.push((rest, depth + 1));
                    }
                    IRBody::JDecl {
                        params, body, rest, ..
                    } => {
                        for (_, ty) in params {
                            self.add(size_of::<(VarId, IRType)>())?;
                            self.ir_type(ty)?;
                        }
                        pending.push((body, depth + 1));
                        pending.push((rest, depth + 1));
                    }
                    IRBody::Inc { rest, .. }
                    | IRBody::Dec { rest, .. }
                    | IRBody::Set { rest, .. }
                    | IRBody::SetTag { rest, .. }
                    | IRBody::USet { rest, .. } => pending.push((rest, depth + 1)),
                    IRBody::SSet { ty, rest, .. } => {
                        self.ir_type(ty)?;
                        pending.push((rest, depth + 1));
                    }
                    IRBody::Case { alts, default, .. } => {
                        for alt in alts {
                            self.ctor(&alt.ctor)?;
                            pending.push((&alt.body, depth + 1));
                        }
                        if let Some(body) = default {
                            pending.push((body, depth + 1));
                        }
                    }
                    IRBody::Jmp { args, .. } => {
                        for _ in args {
                            self.add(size_of::<IRArg>())?;
                        }
                    }
                    IRBody::Ret(_) | IRBody::Unreachable => {}
                }
            }
        }
        Ok(())
    }
}
