// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::Literal as SLiteral;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WLiteral {
    Nat(WBigNat),
    String(String),
}
impl Wire for WLiteral {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Nat(<WBigNat as Wire>::read(r)?)),
            1 => Ok(Self::String(<String as Wire>::read(r)?)),
            _ => Err(error("unknown WLiteral tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Nat(__wire_field_0) => {
                w.u32(0)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::String(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SLiteral {
    type Wire = WLiteral;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SLiteral::Nat(__wire_field_0) => Ok(WLiteral::Nat(__wire_field_0.to_wire(p)?)),
            SLiteral::String(__wire_field_0) => Ok(WLiteral::String(__wire_field_0.to_wire(p)?)),
        }
    }
}
impl FromWire<WLiteral> for SLiteral {
    fn from_wire(wire: WLiteral, r: &mut Restoration) -> Result<Self> {
        match wire {
            WLiteral::Nat(__wire_field_0) => Ok(Self::Nat(FromWire::from_wire(__wire_field_0, r)?)),
            WLiteral::String(__wire_field_0) => {
                Ok(Self::String(FromWire::from_wire(__wire_field_0, r)?))
            }
        }
    }
}
