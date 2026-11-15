// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::EnvExtensionEntryData as SEnvExtensionEntryData;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WEnvExtensionEntryData {
    Scalar(u64),
    Object(Vec<u8>),
}
impl Wire for WEnvExtensionEntryData {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Scalar(<u64 as Wire>::read(r)?)),
            1 => Ok(Self::Object(<Vec<u8> as Wire>::read(r)?)),
            _ => Err(error("unknown WEnvExtensionEntryData tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Scalar(__wire_field_0) => {
                w.u32(0)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Object(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SEnvExtensionEntryData {
    type Wire = WEnvExtensionEntryData;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SEnvExtensionEntryData::Scalar(__wire_field_0) => {
                Ok(WEnvExtensionEntryData::Scalar(__wire_field_0.to_wire(p)?))
            }
            SEnvExtensionEntryData::Object(__wire_field_0) => {
                Ok(WEnvExtensionEntryData::Object(__wire_field_0.to_wire(p)?))
            }
        }
    }
}
impl FromWire<WEnvExtensionEntryData> for SEnvExtensionEntryData {
    fn from_wire(wire: WEnvExtensionEntryData, r: &mut Restoration) -> Result<Self> {
        match wire {
            WEnvExtensionEntryData::Scalar(__wire_field_0) => {
                Ok(Self::Scalar(FromWire::from_wire(__wire_field_0, r)?))
            }
            WEnvExtensionEntryData::Object(__wire_field_0) => {
                Ok(Self::Object(FromWire::from_wire(__wire_field_0, r)?))
            }
        }
    }
}
