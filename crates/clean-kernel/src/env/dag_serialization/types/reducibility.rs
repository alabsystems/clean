// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::Reducibility as SReducibility;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WReducibility {
    Reducible,
    Regular(u32),
    Irreducible,
    Opaque,
}
impl Wire for WReducibility {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Reducible),
            1 => Ok(Self::Regular(<u32 as Wire>::read(r)?)),
            2 => Ok(Self::Irreducible),
            3 => Ok(Self::Opaque),
            _ => Err(error("unknown WReducibility tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Reducible => {
                w.u32(0)?;
                Ok(())
            }
            Self::Regular(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Irreducible => {
                w.u32(2)?;
                Ok(())
            }
            Self::Opaque => {
                w.u32(3)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SReducibility {
    type Wire = WReducibility;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SReducibility::Reducible => Ok(WReducibility::Reducible),
            SReducibility::Regular(__wire_field_0) => {
                Ok(WReducibility::Regular(__wire_field_0.to_wire(p)?))
            }
            SReducibility::Irreducible => Ok(WReducibility::Irreducible),
            SReducibility::Opaque => Ok(WReducibility::Opaque),
        }
    }
}
impl FromWire<WReducibility> for SReducibility {
    fn from_wire(wire: WReducibility, r: &mut Restoration) -> Result<Self> {
        match wire {
            WReducibility::Reducible => Ok(Self::Reducible),
            WReducibility::Regular(__wire_field_0) => {
                Ok(Self::Regular(FromWire::from_wire(__wire_field_0, r)?))
            }
            WReducibility::Irreducible => Ok(Self::Irreducible),
            WReducibility::Opaque => Ok(Self::Opaque),
        }
    }
}
