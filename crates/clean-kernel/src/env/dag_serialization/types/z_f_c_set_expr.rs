// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::ZFCSetExpr as SZFCSetExpr;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WZFCSetExpr {
    Empty,
    Singleton(Ref),
    Pair(Ref, Ref),
    Union(Ref),
    PowerSet(Ref),
    Separation { set: Ref, pred: Ref },
    Replacement { set: Ref, func: Ref },
    Infinity,
    Choice(Ref),
}
impl Wire for WZFCSetExpr {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Empty),
            1 => Ok(Self::Singleton(<Ref as Wire>::read(r)?)),
            2 => Ok(Self::Pair(<Ref as Wire>::read(r)?, <Ref as Wire>::read(r)?)),
            3 => Ok(Self::Union(<Ref as Wire>::read(r)?)),
            4 => Ok(Self::PowerSet(<Ref as Wire>::read(r)?)),
            5 => Ok(Self::Separation {
                set: <Ref as Wire>::read(r)?,
                pred: <Ref as Wire>::read(r)?,
            }),
            6 => Ok(Self::Replacement {
                set: <Ref as Wire>::read(r)?,
                func: <Ref as Wire>::read(r)?,
            }),
            7 => Ok(Self::Infinity),
            8 => Ok(Self::Choice(<Ref as Wire>::read(r)?)),
            _ => Err(error("unknown WZFCSetExpr tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Empty => {
                w.u32(0)?;
                Ok(())
            }
            Self::Singleton(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Pair(__wire_field_0, __wire_field_1) => {
                w.u32(2)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::Union(__wire_field_0) => {
                w.u32(3)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::PowerSet(__wire_field_0) => {
                w.u32(4)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Separation {
                set: __wire_field_0,
                pred: __wire_field_1,
            } => {
                w.u32(5)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::Replacement {
                set: __wire_field_0,
                func: __wire_field_1,
            } => {
                w.u32(6)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::Infinity => {
                w.u32(7)?;
                Ok(())
            }
            Self::Choice(__wire_field_0) => {
                w.u32(8)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SZFCSetExpr {
    type Wire = WZFCSetExpr;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SZFCSetExpr::Empty => Ok(WZFCSetExpr::Empty),
            SZFCSetExpr::Singleton(__wire_field_0) => {
                Ok(WZFCSetExpr::Singleton(__wire_field_0.to_wire(p)?))
            }
            SZFCSetExpr::Pair(__wire_field_0, __wire_field_1) => Ok(WZFCSetExpr::Pair(
                __wire_field_0.to_wire(p)?,
                __wire_field_1.to_wire(p)?,
            )),
            SZFCSetExpr::Union(__wire_field_0) => {
                Ok(WZFCSetExpr::Union(__wire_field_0.to_wire(p)?))
            }
            SZFCSetExpr::PowerSet(__wire_field_0) => {
                Ok(WZFCSetExpr::PowerSet(__wire_field_0.to_wire(p)?))
            }
            SZFCSetExpr::Separation {
                set: __wire_field_0,
                pred: __wire_field_1,
            } => Ok(WZFCSetExpr::Separation {
                set: __wire_field_0.to_wire(p)?,
                pred: __wire_field_1.to_wire(p)?,
            }),
            SZFCSetExpr::Replacement {
                set: __wire_field_0,
                func: __wire_field_1,
            } => Ok(WZFCSetExpr::Replacement {
                set: __wire_field_0.to_wire(p)?,
                func: __wire_field_1.to_wire(p)?,
            }),
            SZFCSetExpr::Infinity => Ok(WZFCSetExpr::Infinity),
            SZFCSetExpr::Choice(__wire_field_0) => {
                Ok(WZFCSetExpr::Choice(__wire_field_0.to_wire(p)?))
            }
        }
    }
}
impl FromWire<WZFCSetExpr> for SZFCSetExpr {
    fn from_wire(wire: WZFCSetExpr, r: &mut Restoration) -> Result<Self> {
        match wire {
            WZFCSetExpr::Empty => Ok(Self::Empty),
            WZFCSetExpr::Singleton(__wire_field_0) => {
                Ok(Self::Singleton(FromWire::from_wire(__wire_field_0, r)?))
            }
            WZFCSetExpr::Pair(__wire_field_0, __wire_field_1) => Ok(Self::Pair(
                FromWire::from_wire(__wire_field_0, r)?,
                FromWire::from_wire(__wire_field_1, r)?,
            )),
            WZFCSetExpr::Union(__wire_field_0) => {
                Ok(Self::Union(FromWire::from_wire(__wire_field_0, r)?))
            }
            WZFCSetExpr::PowerSet(__wire_field_0) => {
                Ok(Self::PowerSet(FromWire::from_wire(__wire_field_0, r)?))
            }
            WZFCSetExpr::Separation {
                set: __wire_field_0,
                pred: __wire_field_1,
            } => Ok(Self::Separation {
                set: FromWire::from_wire(__wire_field_0, r)?,
                pred: FromWire::from_wire(__wire_field_1, r)?,
            }),
            WZFCSetExpr::Replacement {
                set: __wire_field_0,
                func: __wire_field_1,
            } => Ok(Self::Replacement {
                set: FromWire::from_wire(__wire_field_0, r)?,
                func: FromWire::from_wire(__wire_field_1, r)?,
            }),
            WZFCSetExpr::Infinity => Ok(Self::Infinity),
            WZFCSetExpr::Choice(__wire_field_0) => {
                Ok(Self::Choice(FromWire::from_wire(__wire_field_0, r)?))
            }
        }
    }
}
