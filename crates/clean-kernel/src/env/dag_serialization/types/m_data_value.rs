// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::MDataValue as SMDataValue;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WMDataValue {
    Bool(bool),
    Nat(u64),
    String(String),
    Name(WName),
}
impl Wire for WMDataValue {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Bool(<bool as Wire>::read(r)?)),
            1 => Ok(Self::Nat(<u64 as Wire>::read(r)?)),
            2 => Ok(Self::String(<String as Wire>::read(r)?)),
            3 => Ok(Self::Name(<WName as Wire>::read(r)?)),
            _ => Err(error("unknown WMDataValue tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Bool(__wire_field_0) => {
                w.u32(0)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Nat(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::String(__wire_field_0) => {
                w.u32(2)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Name(__wire_field_0) => {
                w.u32(3)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SMDataValue {
    type Wire = WMDataValue;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SMDataValue::Bool(__wire_field_0) => Ok(WMDataValue::Bool(__wire_field_0.to_wire(p)?)),
            SMDataValue::Nat(__wire_field_0) => Ok(WMDataValue::Nat(__wire_field_0.to_wire(p)?)),
            SMDataValue::String(__wire_field_0) => {
                Ok(WMDataValue::String(__wire_field_0.to_wire(p)?))
            }
            SMDataValue::Name(__wire_field_0) => Ok(WMDataValue::Name(__wire_field_0.to_wire(p)?)),
        }
    }
}
impl FromWire<WMDataValue> for SMDataValue {
    fn from_wire(wire: WMDataValue, r: &mut Restoration) -> Result<Self> {
        match wire {
            WMDataValue::Bool(__wire_field_0) => {
                Ok(Self::Bool(FromWire::from_wire(__wire_field_0, r)?))
            }
            WMDataValue::Nat(__wire_field_0) => {
                Ok(Self::Nat(FromWire::from_wire(__wire_field_0, r)?))
            }
            WMDataValue::String(__wire_field_0) => {
                Ok(Self::String(FromWire::from_wire(__wire_field_0, r)?))
            }
            WMDataValue::Name(__wire_field_0) => {
                Ok(Self::Name(FromWire::from_wire(__wire_field_0, r)?))
            }
        }
    }
}
