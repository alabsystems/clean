// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Length-checked iterative reader and exact kernel-node reconstruction.

use super::{Decoded, Limits, Output, Result, require};
use clean_kernel::expr::{
    BigNat, BinderData, BinderInfo, ExprKind, FVarId, Literal, MDataValue, Multiplicity, ZFCSetExpr,
};
use clean_kernel::{Expr, Level, Name};
use std::sync::Arc;

pub(super) struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
}
impl<'a> Reader<'a> {
    pub(super) fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }
    pub(super) fn remaining(&self) -> usize {
        self.bytes.len() - self.position
    }
    pub(super) fn take(&mut self, size: usize) -> Result<&'a [u8]> {
        require(size <= self.remaining(), "truncated record/field")?;
        let start = self.position;
        self.position += size;
        Ok(&self.bytes[start..self.position])
    }
    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    pub(super) fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four bytes"),
        ))
    }
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight bytes"),
        ))
    }
    fn boolean(&mut self) -> Result<bool> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err("Clean Expr DAG v2: invalid boolean".into()),
        }
    }
    fn count(&mut self, minimum_bytes: usize) -> Result<usize> {
        let count = self.u32()? as usize;
        require(
            count <= self.remaining() / minimum_bytes,
            "field count exceeds remaining bytes",
        )?;
        Ok(count)
    }
    fn string(&mut self) -> Result<&'a str> {
        let count = self.count(1)?;
        std::str::from_utf8(self.take(count)?)
            .map_err(|_| "Clean Expr DAG v2: invalid UTF-8".into())
    }
    fn binder(&mut self) -> Result<BinderData> {
        let info = match self.byte()? {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            3 => BinderInfo::InstImplicit,
            _ => return Err("Clean Expr DAG v2: invalid binder info".into()),
        };
        let mult = match self.byte()? {
            0 => Multiplicity::Zero,
            1 => Multiplicity::One,
            2 => Multiplicity::Many,
            _ => return Err("Clean Expr DAG v2: invalid binder multiplicity".into()),
        };
        Ok(BinderData { info, mult })
    }
}

struct Fields<'a, 'n> {
    reader: Reader<'a>,
    nodes: &'n [Decoded],
    depth: usize,
    level_work: usize,
    limits: Limits,
    edges: &'n mut Vec<u32>,
}
impl Fields<'_, '_> {
    fn reference(&mut self) -> Result<&Decoded> {
        let id = self.reader.u32()? as usize;
        let node = self
            .nodes
            .get(id)
            .ok_or("Clean Expr DAG v2: forward/self/out-of-range reference")?;
        self.edges.push(id as u32);
        self.depth = self.depth.max(node.depth + 1);
        require(
            self.depth <= self.limits.depth,
            "graph depth limit exceeded",
        )?;
        Ok(node)
    }
    fn name(&mut self) -> Result<Name> {
        match &self.reference()?.value {
            Output::Name(name) => Ok(name.clone()),
            _ => Err("Clean Expr DAG v2: reference is not a Name".into()),
        }
    }
    fn level(&mut self) -> Result<Arc<Level>> {
        let node = self.reference()?;
        let Output::Level(level) = &node.value else {
            return Err("Clean Expr DAG v2: reference is not a Level".into());
        };
        let work = node.level_work;
        let level = level.clone();
        self.level_work = self
            .level_work
            .saturating_add(work)
            .min(self.limits.constructor_work.saturating_add(1));
        Ok(level)
    }
    fn expr(&mut self) -> Result<Arc<Expr>> {
        match &self.reference()?.value {
            Output::Expr(expr) => Ok(expr.clone()),
            _ => Err("Clean Expr DAG v2: reference is not an Expr".into()),
        }
    }
}

pub(super) fn node(
    bytes: &[u8],
    nodes: &[Decoded],
    limits: Limits,
    work: &mut usize,
    edges: &mut Vec<u32>,
) -> Result<Decoded> {
    require(limits.depth > 0, "graph depth limit exceeded")?;
    let start = edges.len();
    let mut r = Fields {
        reader: Reader::new(bytes),
        nodes,
        depth: 1,
        level_work: 0,
        limits,
        edges,
    };
    let kind = r.reader.byte()?;
    let tag = r.reader.byte()?;
    let value = match kind {
        0 => Output::Name(match tag {
            0 => Name::anon(),
            1 => {
                let parent = r.name()?;
                parent.str(r.reader.string()?)
            }
            2 => {
                let parent = r.name()?;
                parent.num(r.reader.u64()?)
            }
            _ => return Err("Clean Expr DAG v2: invalid Name tag".into()),
        }),
        1 => Output::Level(Arc::new(match tag {
            0 => Level::Zero,
            1 => Level::Succ(r.level()?.into()),
            2 => Level::Max(r.level()?.into(), r.level()?.into()),
            3 => Level::IMax(r.level()?.into(), r.level()?.into()),
            4 => Level::Param(r.name()?),
            _ => return Err("Clean Expr DAG v2: invalid Level tag".into()),
        })),
        2 => {
            let expression = match tag {
                0 => {
                    let n = r.reader.u32()?;
                    require(n < 1_048_575, "BVar exceeds kernel constructor bound")?;
                    ExprKind::BVar(n)
                }
                1 => ExprKind::FVar(FVarId::new(r.reader.u64()?)),
                2 => ExprKind::Sort(r.level()?.as_ref().clone()),
                3 => {
                    let name = r.name()?;
                    let count = r.reader.count(4)?;
                    require(
                        count <= limits.constructor_work.saturating_sub(*work) / 3,
                        "expanded Level constructor work limit exceeded",
                    )?;
                    let mut levels = Vec::with_capacity(count);
                    for _ in 0..count {
                        levels.push(r.level()?.as_ref().clone());
                    }
                    ExprKind::Const(name, levels.into())
                }
                4 => ExprKind::App(r.expr()?, r.expr()?),
                5 => ExprKind::Lam(r.reader.binder()?, r.expr()?, r.expr()?),
                6 => ExprKind::Pi(r.reader.binder()?, r.expr()?, r.expr()?),
                7 => ExprKind::Let(
                    r.name()?,
                    r.expr()?,
                    r.expr()?,
                    r.expr()?,
                    r.reader.boolean()?,
                ),
                8 => ExprKind::Lit(Literal::Nat(match r.reader.byte()? {
                    0 => BigNat::Small(r.reader.u64()?),
                    1 => {
                        let count = r.reader.count(8)?;
                        let mut limbs = Vec::with_capacity(count);
                        for _ in 0..count {
                            limbs.push(r.reader.u64()?);
                        }
                        BigNat::Big(limbs)
                    }
                    _ => return Err("Clean Expr DAG v2: invalid BigNat tag".into()),
                })),
                9 => ExprKind::Lit(Literal::String(Arc::from(r.reader.string()?))),
                10 => ExprKind::Proj(r.name()?, r.reader.u32()?, r.expr()?),
                11 => {
                    let count = r.reader.count(6)?;
                    let mut metadata = Vec::with_capacity(count);
                    for _ in 0..count {
                        let name = r.name()?;
                        let value = match r.reader.byte()? {
                            0 => MDataValue::Bool(r.reader.boolean()?),
                            1 => MDataValue::Nat(r.reader.u64()?),
                            2 => MDataValue::String(Arc::from(r.reader.string()?)),
                            3 => MDataValue::Name(r.name()?),
                            _ => return Err("Clean Expr DAG v2: invalid metadata tag".into()),
                        };
                        metadata.push((name, value));
                    }
                    ExprKind::MData(metadata, r.expr()?)
                }
                12 => ExprKind::SProp,
                13 => ExprKind::Squash(r.expr()?),
                14 => ExprKind::CubicalInterval,
                15 => ExprKind::CubicalI0,
                16 => ExprKind::CubicalI1,
                17 => ExprKind::CubicalPath {
                    ty: r.expr()?,
                    left: r.expr()?,
                    right: r.expr()?,
                },
                18 => ExprKind::CubicalPathLam { body: r.expr()? },
                19 => ExprKind::CubicalPathApp {
                    path: r.expr()?,
                    arg: r.expr()?,
                },
                20 => ExprKind::CubicalHComp {
                    ty: r.expr()?,
                    phi: r.expr()?,
                    u: r.expr()?,
                    base: r.expr()?,
                },
                21 => ExprKind::CubicalTransp {
                    ty: r.expr()?,
                    phi: r.expr()?,
                    base: r.expr()?,
                },
                22 => ExprKind::CubicalCoe {
                    ty: r.expr()?,
                    r: r.expr()?,
                    s: r.expr()?,
                    base: r.expr()?,
                },
                23 => ExprKind::ZFCSet(match r.reader.byte()? {
                    0 => ZFCSetExpr::Empty,
                    1 => ZFCSetExpr::Singleton(r.expr()?),
                    2 => ZFCSetExpr::Pair(r.expr()?, r.expr()?),
                    3 => ZFCSetExpr::Union(r.expr()?),
                    4 => ZFCSetExpr::PowerSet(r.expr()?),
                    5 => ZFCSetExpr::Separation {
                        set: r.expr()?,
                        pred: r.expr()?,
                    },
                    6 => ZFCSetExpr::Replacement {
                        set: r.expr()?,
                        func: r.expr()?,
                    },
                    7 => ZFCSetExpr::Infinity,
                    8 => ZFCSetExpr::Choice(r.expr()?),
                    _ => return Err("Clean Expr DAG v2: invalid ZFC tag".into()),
                }),
                24 => ExprKind::ZFCMem {
                    element: r.expr()?,
                    set: r.expr()?,
                },
                25 => ExprKind::ZFCComprehension {
                    domain: r.expr()?,
                    pred: r.expr()?,
                },
                _ => return Err("Clean Expr DAG v2: invalid Expr tag".into()),
            };
            // Sort/Const alone carry levels. Clean currently walks each level
            // for metadata hashing, parameter flags and metavariable flags;
            // bound all three passes
            // before calling its constructor, including across many constants.
            let charge = r.level_work.saturating_mul(3);
            *work = work.saturating_add(charge);
            require(
                *work <= limits.constructor_work,
                "expanded Level constructor work limit exceeded",
            )?;
            Output::Expr(Arc::new(Expr::from_kind(expression)))
        }
        _ => return Err("Clean Expr DAG v2: invalid node type".into()),
    };
    require(r.reader.remaining() == 0, "trailing node bytes")?;
    let level_work = if kind == 1 {
        r.level_work
            .saturating_add(1)
            .min(limits.constructor_work.saturating_add(1))
    } else {
        0
    };
    Ok(Decoded {
        value,
        depth: r.depth,
        level_work,
        references: start..r.edges.len(),
    })
}
