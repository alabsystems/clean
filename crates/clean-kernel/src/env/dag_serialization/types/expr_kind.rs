// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::ExprKind as SExprKind;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WExprKind {
    BVar(u32),
    FVar(WFVarId),
    Sort(WLevel),
    Const(WName, Vec<WLevel>),
    App(Ref, Ref),
    Lam(WBinderData, Ref, Ref),
    Pi(WBinderData, Ref, Ref),
    Let(WName, Ref, Ref, Ref, bool),
    Lit(WLiteral),
    Proj(WName, u32, Ref),
    MData(Vec<(WName, WMDataValue)>, Ref),
    SProp,
    Squash(Ref),
    CubicalInterval,
    CubicalI0,
    CubicalI1,
    CubicalPath {
        ty: Ref,
        left: Ref,
        right: Ref,
    },
    CubicalPathLam {
        body: Ref,
    },
    CubicalPathApp {
        path: Ref,
        arg: Ref,
    },
    CubicalHComp {
        ty: Ref,
        phi: Ref,
        u: Ref,
        base: Ref,
    },
    CubicalTransp {
        ty: Ref,
        phi: Ref,
        base: Ref,
    },
    CubicalCoe {
        ty: Ref,
        r: Ref,
        s: Ref,
        base: Ref,
    },
    ZFCSet(WZFCSetExpr),
    ZFCMem {
        element: Ref,
        set: Ref,
    },
    ZFCComprehension {
        domain: Ref,
        pred: Ref,
    },
}
impl Wire for WExprKind {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::BVar(<u32 as Wire>::read(r)?)),
            1 => Ok(Self::FVar(<WFVarId as Wire>::read(r)?)),
            2 => Ok(Self::Sort(<WLevel as Wire>::read(r)?)),
            3 => Ok(Self::Const(
                <WName as Wire>::read(r)?,
                <Vec<WLevel> as Wire>::read(r)?,
            )),
            4 => Ok(Self::App(<Ref as Wire>::read(r)?, <Ref as Wire>::read(r)?)),
            5 => Ok(Self::Lam(
                <WBinderData as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
            )),
            6 => Ok(Self::Pi(
                <WBinderData as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
            )),
            7 => Ok(Self::Let(
                <WName as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
                <bool as Wire>::read(r)?,
            )),
            8 => Ok(Self::Lit(<WLiteral as Wire>::read(r)?)),
            9 => Ok(Self::Proj(
                <WName as Wire>::read(r)?,
                <u32 as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
            )),
            10 => Ok(Self::MData(
                <Vec<(WName, WMDataValue)> as Wire>::read(r)?,
                <Ref as Wire>::read(r)?,
            )),
            11 => Ok(Self::SProp),
            12 => Ok(Self::Squash(<Ref as Wire>::read(r)?)),
            13 => Ok(Self::CubicalInterval),
            14 => Ok(Self::CubicalI0),
            15 => Ok(Self::CubicalI1),
            16 => Ok(Self::CubicalPath {
                ty: <Ref as Wire>::read(r)?,
                left: <Ref as Wire>::read(r)?,
                right: <Ref as Wire>::read(r)?,
            }),
            17 => Ok(Self::CubicalPathLam {
                body: <Ref as Wire>::read(r)?,
            }),
            18 => Ok(Self::CubicalPathApp {
                path: <Ref as Wire>::read(r)?,
                arg: <Ref as Wire>::read(r)?,
            }),
            19 => Ok(Self::CubicalHComp {
                ty: <Ref as Wire>::read(r)?,
                phi: <Ref as Wire>::read(r)?,
                u: <Ref as Wire>::read(r)?,
                base: <Ref as Wire>::read(r)?,
            }),
            20 => Ok(Self::CubicalTransp {
                ty: <Ref as Wire>::read(r)?,
                phi: <Ref as Wire>::read(r)?,
                base: <Ref as Wire>::read(r)?,
            }),
            21 => Ok(Self::CubicalCoe {
                ty: <Ref as Wire>::read(r)?,
                r: <Ref as Wire>::read(r)?,
                s: <Ref as Wire>::read(r)?,
                base: <Ref as Wire>::read(r)?,
            }),
            22 => Ok(Self::ZFCSet(<WZFCSetExpr as Wire>::read(r)?)),
            23 => Ok(Self::ZFCMem {
                element: <Ref as Wire>::read(r)?,
                set: <Ref as Wire>::read(r)?,
            }),
            24 => Ok(Self::ZFCComprehension {
                domain: <Ref as Wire>::read(r)?,
                pred: <Ref as Wire>::read(r)?,
            }),
            _ => Err(error("unknown WExprKind tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::BVar(__wire_field_0) => {
                w.u32(0)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::FVar(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Sort(__wire_field_0) => {
                w.u32(2)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Const(__wire_field_0, __wire_field_1) => {
                w.u32(3)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::App(__wire_field_0, __wire_field_1) => {
                w.u32(4)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::Lam(__wire_field_0, __wire_field_1, __wire_field_2) => {
                w.u32(5)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                Ok(())
            }
            Self::Pi(__wire_field_0, __wire_field_1, __wire_field_2) => {
                w.u32(6)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                Ok(())
            }
            Self::Let(
                __wire_field_0,
                __wire_field_1,
                __wire_field_2,
                __wire_field_3,
                __wire_field_4,
            ) => {
                w.u32(7)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                __wire_field_3.write(w)?;
                __wire_field_4.write(w)?;
                Ok(())
            }
            Self::Lit(__wire_field_0) => {
                w.u32(8)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Proj(__wire_field_0, __wire_field_1, __wire_field_2) => {
                w.u32(9)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                Ok(())
            }
            Self::MData(__wire_field_0, __wire_field_1) => {
                w.u32(10)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::SProp => {
                w.u32(11)?;
                Ok(())
            }
            Self::Squash(__wire_field_0) => {
                w.u32(12)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::CubicalInterval => {
                w.u32(13)?;
                Ok(())
            }
            Self::CubicalI0 => {
                w.u32(14)?;
                Ok(())
            }
            Self::CubicalI1 => {
                w.u32(15)?;
                Ok(())
            }
            Self::CubicalPath {
                ty: __wire_field_0,
                left: __wire_field_1,
                right: __wire_field_2,
            } => {
                w.u32(16)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                Ok(())
            }
            Self::CubicalPathLam {
                body: __wire_field_0,
            } => {
                w.u32(17)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::CubicalPathApp {
                path: __wire_field_0,
                arg: __wire_field_1,
            } => {
                w.u32(18)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::CubicalHComp {
                ty: __wire_field_0,
                phi: __wire_field_1,
                u: __wire_field_2,
                base: __wire_field_3,
            } => {
                w.u32(19)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                __wire_field_3.write(w)?;
                Ok(())
            }
            Self::CubicalTransp {
                ty: __wire_field_0,
                phi: __wire_field_1,
                base: __wire_field_2,
            } => {
                w.u32(20)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                Ok(())
            }
            Self::CubicalCoe {
                ty: __wire_field_0,
                r: __wire_field_1,
                s: __wire_field_2,
                base: __wire_field_3,
            } => {
                w.u32(21)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                __wire_field_2.write(w)?;
                __wire_field_3.write(w)?;
                Ok(())
            }
            Self::ZFCSet(__wire_field_0) => {
                w.u32(22)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::ZFCMem {
                element: __wire_field_0,
                set: __wire_field_1,
            } => {
                w.u32(23)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::ZFCComprehension {
                domain: __wire_field_0,
                pred: __wire_field_1,
            } => {
                w.u32(24)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SExprKind {
    type Wire = WExprKind;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SExprKind::BVar(__wire_field_0) => Ok(WExprKind::BVar(__wire_field_0.to_wire(p)?)),
            SExprKind::FVar(__wire_field_0) => Ok(WExprKind::FVar(__wire_field_0.to_wire(p)?)),
            SExprKind::Sort(__wire_field_0) => Ok(WExprKind::Sort(__wire_field_0.to_wire(p)?)),
            SExprKind::Const(__wire_field_0, __wire_field_1) => Ok(WExprKind::Const(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
            )),
            SExprKind::App(__wire_field_0, __wire_field_1) => Ok(WExprKind::App(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
            )),
            SExprKind::Lam(__wire_field_0, __wire_field_1, __wire_field_2) => Ok(WExprKind::Lam(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
                __wire_field_2.to_wire(p)?,
            )),
            SExprKind::Pi(__wire_field_0, __wire_field_1, __wire_field_2) => Ok(WExprKind::Pi(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
                __wire_field_2.to_wire(p)?,
            )),
            SExprKind::Let(
                __wire_field_0,
                __wire_field_1,
                __wire_field_2,
                __wire_field_3,
                __wire_field_4,
            ) => Ok(WExprKind::Let(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
                __wire_field_2.to_wire(p)?,
                __wire_field_3.to_wire(p)?,
                __wire_field_4.to_wire(p)?,
            )),
            SExprKind::Lit(__wire_field_0) => Ok(WExprKind::Lit(__wire_field_0.to_wire(p)?)),
            SExprKind::Proj(__wire_field_0, __wire_field_1, __wire_field_2) => Ok(WExprKind::Proj(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
                __wire_field_2.to_wire(p)?,
            )),
            SExprKind::MData(__wire_field_0, __wire_field_1) => Ok(WExprKind::MData(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
            )),
            SExprKind::SProp => Ok(WExprKind::SProp),
            SExprKind::Squash(__wire_field_0) => Ok(WExprKind::Squash(__wire_field_0.to_wire(p)?)),
            SExprKind::CubicalInterval => Ok(WExprKind::CubicalInterval),
            SExprKind::CubicalI0 => Ok(WExprKind::CubicalI0),
            SExprKind::CubicalI1 => Ok(WExprKind::CubicalI1),
            SExprKind::CubicalPath {
                ty: __wire_field_0,
                left: __wire_field_1,
                right: __wire_field_2,
            } => Ok(WExprKind::CubicalPath {
                ty: __wire_field_0.to_wire(p)?,
                left: __wire_field_1.to_wire(p)?,
                right: __wire_field_2.to_wire(p)?,
            }),
            SExprKind::CubicalPathLam {
                body: __wire_field_0,
            } => Ok(WExprKind::CubicalPathLam {
                body: __wire_field_0.to_wire(p)?,
            }),
            SExprKind::CubicalPathApp {
                path: __wire_field_0,
                arg: __wire_field_1,
            } => Ok(WExprKind::CubicalPathApp {
                path: __wire_field_0.to_wire(p)?,
                arg: __wire_field_1.to_wire(p)?,
            }),
            SExprKind::CubicalHComp {
                ty: __wire_field_0,
                phi: __wire_field_1,
                u: __wire_field_2,
                base: __wire_field_3,
            } => Ok(WExprKind::CubicalHComp {
                ty: __wire_field_0.to_wire(p)?,
                phi: __wire_field_1.to_wire(p)?,
                u: __wire_field_2.to_wire(p)?,
                base: __wire_field_3.to_wire(p)?,
            }),
            SExprKind::CubicalTransp {
                ty: __wire_field_0,
                phi: __wire_field_1,
                base: __wire_field_2,
            } => Ok(WExprKind::CubicalTransp {
                ty: __wire_field_0.to_wire(p)?,
                phi: __wire_field_1.to_wire(p)?,
                base: __wire_field_2.to_wire(p)?,
            }),
            SExprKind::CubicalCoe {
                ty: __wire_field_0,
                r: __wire_field_1,
                s: __wire_field_2,
                base: __wire_field_3,
            } => Ok(WExprKind::CubicalCoe {
                ty: __wire_field_0.to_wire(p)?,
                r: __wire_field_1.to_wire(p)?,
                s: __wire_field_2.to_wire(p)?,
                base: __wire_field_3.to_wire(p)?,
            }),
            SExprKind::ZFCSet(__wire_field_0) => Ok(WExprKind::ZFCSet(__wire_field_0.to_wire(p)?)),
            SExprKind::ZFCMem {
                element: __wire_field_0,
                set: __wire_field_1,
            } => Ok(WExprKind::ZFCMem {
                element: __wire_field_0.to_wire(p)?,
                set: __wire_field_1.to_wire(p)?,
            }),
            SExprKind::ZFCComprehension {
                domain: __wire_field_0,
                pred: __wire_field_1,
            } => Ok(WExprKind::ZFCComprehension {
                domain: __wire_field_0.to_wire(p)?,
                pred: __wire_field_1.to_wire(p)?,
            }),
        }
    }
}
impl FromWire<WExprKind> for SExprKind {
    fn from_wire(wire: WExprKind, r: &mut Restoration) -> Result<Self> {
        match wire {
            WExprKind::BVar(__wire_field_0) => {
                Ok(Self::BVar(FromWire::from_wire(__wire_field_0, r)?))
            }
            WExprKind::FVar(__wire_field_0) => {
                Ok(Self::FVar(FromWire::from_wire(__wire_field_0, r)?))
            }
            WExprKind::Sort(__wire_field_0) => {
                Ok(Self::Sort(FromWire::from_wire(__wire_field_0, r)?))
            }
            WExprKind::Const(__wire_field_0, __wire_field_1) => Ok(Self::Const(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
            )),
            WExprKind::App(__wire_field_0, __wire_field_1) => Ok(Self::App(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
            )),
            WExprKind::Lam(__wire_field_0, __wire_field_1, __wire_field_2) => Ok(Self::Lam(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
                FromWire::from_wire(__wire_field_2, r)?,
            )),
            WExprKind::Pi(__wire_field_0, __wire_field_1, __wire_field_2) => Ok(Self::Pi(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
                FromWire::from_wire(__wire_field_2, r)?,
            )),
            WExprKind::Let(
                __wire_field_0,
                __wire_field_1,
                __wire_field_2,
                __wire_field_3,
                __wire_field_4,
            ) => Ok(Self::Let(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
                FromWire::from_wire(__wire_field_2, r)?,
                FromWire::from_wire(__wire_field_3, r)?,
                FromWire::from_wire(__wire_field_4, r)?,
            )),
            WExprKind::Lit(__wire_field_0) => {
                Ok(Self::Lit(FromWire::from_wire(__wire_field_0, r)?))
            }
            WExprKind::Proj(__wire_field_0, __wire_field_1, __wire_field_2) => Ok(Self::Proj(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
                FromWire::from_wire(__wire_field_2, r)?,
            )),
            WExprKind::MData(__wire_field_0, __wire_field_1) => Ok(Self::MData(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
            )),
            WExprKind::SProp => Ok(Self::SProp),
            WExprKind::Squash(__wire_field_0) => {
                Ok(Self::Squash(FromWire::from_wire(__wire_field_0, r)?))
            }
            WExprKind::CubicalInterval => Ok(Self::CubicalInterval),
            WExprKind::CubicalI0 => Ok(Self::CubicalI0),
            WExprKind::CubicalI1 => Ok(Self::CubicalI1),
            WExprKind::CubicalPath {
                ty: __wire_field_0,
                left: __wire_field_1,
                right: __wire_field_2,
            } => Ok(Self::CubicalPath {
                ty: FromWire::from_wire(__wire_field_0, r)?,
                left: FromWire::from_wire(__wire_field_1, r)?,
                right: FromWire::from_wire(__wire_field_2, r)?,
            }),
            WExprKind::CubicalPathLam {
                body: __wire_field_0,
            } => Ok(Self::CubicalPathLam {
                body: FromWire::from_wire(__wire_field_0, r)?,
            }),
            WExprKind::CubicalPathApp {
                path: __wire_field_0,
                arg: __wire_field_1,
            } => Ok(Self::CubicalPathApp {
                path: FromWire::from_wire(__wire_field_0, r)?,
                arg: FromWire::from_wire(__wire_field_1, r)?,
            }),
            WExprKind::CubicalHComp {
                ty: __wire_field_0,
                phi: __wire_field_1,
                u: __wire_field_2,
                base: __wire_field_3,
            } => Ok(Self::CubicalHComp {
                ty: FromWire::from_wire(__wire_field_0, r)?,
                phi: FromWire::from_wire(__wire_field_1, r)?,
                u: FromWire::from_wire(__wire_field_2, r)?,
                base: FromWire::from_wire(__wire_field_3, r)?,
            }),
            WExprKind::CubicalTransp {
                ty: __wire_field_0,
                phi: __wire_field_1,
                base: __wire_field_2,
            } => Ok(Self::CubicalTransp {
                ty: FromWire::from_wire(__wire_field_0, r)?,
                phi: FromWire::from_wire(__wire_field_1, r)?,
                base: FromWire::from_wire(__wire_field_2, r)?,
            }),
            WExprKind::CubicalCoe {
                ty: __wire_field_0,
                r: __wire_field_1,
                s: __wire_field_2,
                base: __wire_field_3,
            } => Ok(Self::CubicalCoe {
                ty: FromWire::from_wire(__wire_field_0, r)?,
                r: FromWire::from_wire(__wire_field_1, r)?,
                s: FromWire::from_wire(__wire_field_2, r)?,
                base: FromWire::from_wire(__wire_field_3, r)?,
            }),
            WExprKind::ZFCSet(__wire_field_0) => {
                Ok(Self::ZFCSet(FromWire::from_wire(__wire_field_0, r)?))
            }
            WExprKind::ZFCMem {
                element: __wire_field_0,
                set: __wire_field_1,
            } => Ok(Self::ZFCMem {
                element: FromWire::from_wire(__wire_field_0, r)?,
                set: FromWire::from_wire(__wire_field_1, r)?,
            }),
            WExprKind::ZFCComprehension {
                domain: __wire_field_0,
                pred: __wire_field_1,
            } => Ok(Self::ZFCComprehension {
                domain: FromWire::from_wire(__wire_field_0, r)?,
                pred: FromWire::from_wire(__wire_field_1, r)?,
            }),
        }
    }
}
