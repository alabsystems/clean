// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::ConstantKind as SConstantKind;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WConstantKind {
    Definition,
    Theorem,
    Opaque,
    Axiom,
}
impl Wire for WConstantKind {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Definition),
            1 => Ok(Self::Theorem),
            2 => Ok(Self::Opaque),
            3 => Ok(Self::Axiom),
            _ => Err(error("unknown WConstantKind tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Definition => {
                w.u32(0)?;
                Ok(())
            }
            Self::Theorem => {
                w.u32(1)?;
                Ok(())
            }
            Self::Opaque => {
                w.u32(2)?;
                Ok(())
            }
            Self::Axiom => {
                w.u32(3)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SConstantKind {
    type Wire = WConstantKind;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SConstantKind::Definition => Ok(WConstantKind::Definition),
            SConstantKind::Theorem => Ok(WConstantKind::Theorem),
            SConstantKind::Opaque => Ok(WConstantKind::Opaque),
            SConstantKind::Axiom => Ok(WConstantKind::Axiom),
        }
    }
}
impl FromWire<WConstantKind> for SConstantKind {
    fn from_wire(wire: WConstantKind, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WConstantKind::Definition => Ok(Self::Definition),
            WConstantKind::Theorem => Ok(Self::Theorem),
            WConstantKind::Opaque => Ok(Self::Opaque),
            WConstantKind::Axiom => Ok(Self::Axiom),
        }
    }
}
