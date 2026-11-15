// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::origin::OriginTrust as SOriginTrust;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WOriginTrust {
    KernelChecked,
    OleanUnpinned,
    CleanPayloadUnpinned,
}
impl Wire for WOriginTrust {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::KernelChecked),
            1 => Ok(Self::OleanUnpinned),
            2 => Ok(Self::CleanPayloadUnpinned),
            _ => Err(error("unknown WOriginTrust tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::KernelChecked => {
                w.u32(0)?;
                Ok(())
            }
            Self::OleanUnpinned => {
                w.u32(1)?;
                Ok(())
            }
            Self::CleanPayloadUnpinned => {
                w.u32(2)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SOriginTrust {
    type Wire = WOriginTrust;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SOriginTrust::KernelChecked => Ok(WOriginTrust::KernelChecked),
            SOriginTrust::OleanUnpinned => Ok(WOriginTrust::OleanUnpinned),
            SOriginTrust::CleanPayloadUnpinned => Ok(WOriginTrust::CleanPayloadUnpinned),
        }
    }
}
impl FromWire<WOriginTrust> for SOriginTrust {
    fn from_wire(wire: WOriginTrust, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WOriginTrust::KernelChecked => Ok(Self::KernelChecked),
            WOriginTrust::OleanUnpinned => Ok(Self::OleanUnpinned),
            WOriginTrust::CleanPayloadUnpinned => Ok(Self::CleanPayloadUnpinned),
        }
    }
}
