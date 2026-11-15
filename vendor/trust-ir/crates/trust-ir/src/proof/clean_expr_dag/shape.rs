// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact shallow wire records. Child positions are patched after DFS completion.

use super::{Input, Limits, Pending, Result, require};
use clean_kernel::Level;
use clean_kernel::expr::{
    BigNat, BinderData, BinderInfo, ExprKind, Literal, MDataValue, Multiplicity, ZFCSetExpr,
};
use clean_kernel::name::NameInner;

struct Writer<'a> {
    bytes: Vec<u8>,
    children: Vec<(usize, Input<'a>)>,
    limit: usize,
}

impl<'a> Writer<'a> {
    fn raw(&mut self, data: &[u8]) -> Result<()> {
        require(
            data.len() <= self.limit.saturating_sub(self.bytes.len()),
            "record byte limit exceeded",
        )?;
        self.bytes.extend_from_slice(data);
        Ok(())
    }
    fn byte(&mut self, value: u8) -> Result<()> {
        self.raw(&[value])
    }
    fn u32(&mut self, value: u32) -> Result<()> {
        self.raw(&value.to_le_bytes())
    }
    fn u64(&mut self, value: u64) -> Result<()> {
        self.raw(&value.to_le_bytes())
    }
    fn count(&mut self, value: usize) -> Result<()> {
        self.u32(u32::try_from(value).map_err(|_| "Clean Expr DAG v2: field length overflow")?)
    }
    fn string(&mut self, value: &str) -> Result<()> {
        self.count(value.len())?;
        self.raw(value.as_bytes())
    }
    fn reference(&mut self, value: Input<'a>) -> Result<()> {
        let offset = self.bytes.len();
        self.u32(0)?;
        self.children.push((offset, value));
        Ok(())
    }
    fn expr(&mut self, value: &'a clean_kernel::Expr) -> Result<()> {
        self.reference(Input::Expr(value))
    }
    fn level(&mut self, value: &'a Level) -> Result<()> {
        self.reference(Input::Level(value))
    }
    fn name(&mut self, value: &'a clean_kernel::Name) -> Result<()> {
        self.reference(Input::Name(value))
    }
    fn binder(&mut self, data: BinderData) -> Result<()> {
        self.byte(match data.info {
            BinderInfo::Default => 0,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
        })?;
        self.byte(match data.mult {
            Multiplicity::Zero => 0,
            Multiplicity::One => 1,
            Multiplicity::Many => 2,
        })
    }
}

pub(super) fn pending(input: Input<'_>, limits: Limits) -> Result<Pending<'_>> {
    let mut w = Writer {
        bytes: Vec::new(),
        children: Vec::new(),
        limit: limits.bytes,
    };
    w.byte(input.kind())?;
    match input {
        Input::Name(name) => match name.inner() {
            NameInner::Anon => w.byte(0)?,
            NameInner::Str(parent, text) => {
                w.byte(1)?;
                w.name(parent)?;
                w.string(text)?;
            }
            NameInner::Num(parent, number) => {
                w.byte(2)?;
                w.name(parent)?;
                w.u64(*number)?;
            }
        },
        Input::Level(level) => match level {
            Level::Zero => w.byte(0)?,
            Level::Succ(child) => {
                w.byte(1)?;
                w.level(child)?;
            }
            Level::Max(a, b) => {
                w.byte(2)?;
                w.level(a)?;
                w.level(b)?;
            }
            Level::IMax(a, b) => {
                w.byte(3)?;
                w.level(a)?;
                w.level(b)?;
            }
            Level::Param(name) => {
                w.byte(4)?;
                w.name(name)?;
            }
        },
        Input::Expr(expr) => match expr.kind() {
            ExprKind::BVar(n) => {
                require(*n < 1_048_575, "BVar exceeds kernel constructor bound")?;
                w.byte(0)?;
                w.u32(*n)?;
            }
            ExprKind::FVar(id) => {
                w.byte(1)?;
                w.u64(id.as_u64())?;
            }
            ExprKind::Sort(level) => {
                w.byte(2)?;
                w.level(level)?;
            }
            ExprKind::Const(name, levels) => {
                w.byte(3)?;
                w.name(name)?;
                w.count(levels.len())?;
                for level in levels {
                    w.level(level)?;
                }
            }
            ExprKind::App(a, b) => {
                w.byte(4)?;
                w.expr(a)?;
                w.expr(b)?;
            }
            ExprKind::Lam(info, ty, body) => {
                w.byte(5)?;
                w.binder(*info)?;
                w.expr(ty)?;
                w.expr(body)?;
            }
            ExprKind::Pi(info, ty, body) => {
                w.byte(6)?;
                w.binder(*info)?;
                w.expr(ty)?;
                w.expr(body)?;
            }
            ExprKind::Let(name, ty, value, body, non_dep) => {
                w.byte(7)?;
                w.name(name)?;
                w.expr(ty)?;
                w.expr(value)?;
                w.expr(body)?;
                w.byte(u8::from(*non_dep))?;
            }
            ExprKind::Lit(Literal::Nat(n)) => {
                w.byte(8)?;
                match n {
                    BigNat::Small(n) => {
                        w.byte(0)?;
                        w.u64(*n)?;
                    }
                    BigNat::Big(limbs) => {
                        w.byte(1)?;
                        w.count(limbs.len())?;
                        for limb in limbs {
                            w.u64(*limb)?;
                        }
                    }
                }
            }
            ExprKind::Lit(Literal::String(text)) => {
                w.byte(9)?;
                w.string(text)?;
            }
            ExprKind::Proj(name, field, value) => {
                w.byte(10)?;
                w.name(name)?;
                w.u32(*field)?;
                w.expr(value)?;
            }
            ExprKind::MData(metadata, value) => {
                w.byte(11)?;
                w.count(metadata.len())?;
                for (key, item) in metadata {
                    w.name(key)?;
                    match item {
                        MDataValue::Bool(v) => {
                            w.byte(0)?;
                            w.byte(u8::from(*v))?;
                        }
                        MDataValue::Nat(v) => {
                            w.byte(1)?;
                            w.u64(*v)?;
                        }
                        MDataValue::String(v) => {
                            w.byte(2)?;
                            w.string(v)?;
                        }
                        MDataValue::Name(v) => {
                            w.byte(3)?;
                            w.name(v)?;
                        }
                    }
                }
                w.expr(value)?;
            }
            ExprKind::SProp => w.byte(12)?,
            ExprKind::Squash(value) => {
                w.byte(13)?;
                w.expr(value)?;
            }
            ExprKind::CubicalInterval => w.byte(14)?,
            ExprKind::CubicalI0 => w.byte(15)?,
            ExprKind::CubicalI1 => w.byte(16)?,
            ExprKind::CubicalPath { ty, left, right } => {
                w.byte(17)?;
                w.expr(ty)?;
                w.expr(left)?;
                w.expr(right)?;
            }
            ExprKind::CubicalPathLam { body } => {
                w.byte(18)?;
                w.expr(body)?;
            }
            ExprKind::CubicalPathApp { path, arg } => {
                w.byte(19)?;
                w.expr(path)?;
                w.expr(arg)?;
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                w.byte(20)?;
                w.expr(ty)?;
                w.expr(phi)?;
                w.expr(u)?;
                w.expr(base)?;
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                w.byte(21)?;
                w.expr(ty)?;
                w.expr(phi)?;
                w.expr(base)?;
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                w.byte(22)?;
                w.expr(ty)?;
                w.expr(r)?;
                w.expr(s)?;
                w.expr(base)?;
            }
            ExprKind::ZFCSet(set) => {
                w.byte(23)?;
                match set {
                    ZFCSetExpr::Empty => w.byte(0)?,
                    ZFCSetExpr::Singleton(a) => {
                        w.byte(1)?;
                        w.expr(a)?;
                    }
                    ZFCSetExpr::Pair(a, b) => {
                        w.byte(2)?;
                        w.expr(a)?;
                        w.expr(b)?;
                    }
                    ZFCSetExpr::Union(a) => {
                        w.byte(3)?;
                        w.expr(a)?;
                    }
                    ZFCSetExpr::PowerSet(a) => {
                        w.byte(4)?;
                        w.expr(a)?;
                    }
                    ZFCSetExpr::Separation { set, pred } => {
                        w.byte(5)?;
                        w.expr(set)?;
                        w.expr(pred)?;
                    }
                    ZFCSetExpr::Replacement { set, func } => {
                        w.byte(6)?;
                        w.expr(set)?;
                        w.expr(func)?;
                    }
                    ZFCSetExpr::Infinity => w.byte(7)?,
                    ZFCSetExpr::Choice(a) => {
                        w.byte(8)?;
                        w.expr(a)?;
                    }
                }
            }
            ExprKind::ZFCMem { element, set } => {
                w.byte(24)?;
                w.expr(element)?;
                w.expr(set)?;
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                w.byte(25)?;
                w.expr(domain)?;
                w.expr(pred)?;
            }
        },
    }
    Ok(Pending {
        input,
        bytes: w.bytes,
        children: w.children,
        next: 0,
        depth: 1,
    })
}
