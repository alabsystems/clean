// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::GrindAttrKind as SGrindAttrKind;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WGrindAttrKind {
    Infer,
    EqLhs,
    Forward,
    Backward,
    Cases,
    Ext,
    Intro,
    Unmodeled(String),
}
impl Wire for WGrindAttrKind {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Infer),
            1 => Ok(Self::EqLhs),
            2 => Ok(Self::Forward),
            3 => Ok(Self::Backward),
            4 => Ok(Self::Cases),
            5 => Ok(Self::Ext),
            6 => Ok(Self::Intro),
            7 => Ok(Self::Unmodeled(<String as Wire>::read(r)?)),
            _ => Err(error("unknown WGrindAttrKind tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Infer => {
                w.u32(0)?;
                Ok(())
            }
            Self::EqLhs => {
                w.u32(1)?;
                Ok(())
            }
            Self::Forward => {
                w.u32(2)?;
                Ok(())
            }
            Self::Backward => {
                w.u32(3)?;
                Ok(())
            }
            Self::Cases => {
                w.u32(4)?;
                Ok(())
            }
            Self::Ext => {
                w.u32(5)?;
                Ok(())
            }
            Self::Intro => {
                w.u32(6)?;
                Ok(())
            }
            Self::Unmodeled(__wire_field_0) => {
                w.u32(7)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SGrindAttrKind {
    type Wire = WGrindAttrKind;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SGrindAttrKind::Infer => Ok(WGrindAttrKind::Infer),
            SGrindAttrKind::EqLhs => Ok(WGrindAttrKind::EqLhs),
            SGrindAttrKind::Forward => Ok(WGrindAttrKind::Forward),
            SGrindAttrKind::Backward => Ok(WGrindAttrKind::Backward),
            SGrindAttrKind::Cases => Ok(WGrindAttrKind::Cases),
            SGrindAttrKind::Ext => Ok(WGrindAttrKind::Ext),
            SGrindAttrKind::Intro => Ok(WGrindAttrKind::Intro),
            SGrindAttrKind::Unmodeled(__wire_field_0) => {
                Ok(WGrindAttrKind::Unmodeled(__wire_field_0.to_wire(p)?))
            }
        }
    }
}
impl FromWire<WGrindAttrKind> for SGrindAttrKind {
    fn from_wire(wire: WGrindAttrKind, r: &mut Restoration) -> Result<Self> {
        match wire {
            WGrindAttrKind::Infer => Ok(Self::Infer),
            WGrindAttrKind::EqLhs => Ok(Self::EqLhs),
            WGrindAttrKind::Forward => Ok(Self::Forward),
            WGrindAttrKind::Backward => Ok(Self::Backward),
            WGrindAttrKind::Cases => Ok(Self::Cases),
            WGrindAttrKind::Ext => Ok(Self::Ext),
            WGrindAttrKind::Intro => Ok(Self::Intro),
            WGrindAttrKind::Unmodeled(__wire_field_0) => {
                Ok(Self::Unmodeled(FromWire::from_wire(__wire_field_0, r)?))
            }
        }
    }
}
