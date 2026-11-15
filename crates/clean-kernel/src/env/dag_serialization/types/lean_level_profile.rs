// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::level::LeanLevelProfile as SLeanLevelProfile;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WLeanLevelProfile {
    Lean48,
    Lean430,
}
impl Wire for WLeanLevelProfile {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Lean48),
            1 => Ok(Self::Lean430),
            _ => Err(error("unknown WLeanLevelProfile tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Lean48 => {
                w.u32(0)?;
                Ok(())
            }
            Self::Lean430 => {
                w.u32(1)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SLeanLevelProfile {
    type Wire = WLeanLevelProfile;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SLeanLevelProfile::Lean48 => Ok(WLeanLevelProfile::Lean48),
            SLeanLevelProfile::Lean430 => Ok(WLeanLevelProfile::Lean430),
        }
    }
}
impl FromWire<WLeanLevelProfile> for SLeanLevelProfile {
    fn from_wire(wire: WLeanLevelProfile, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WLeanLevelProfile::Lean48 => Ok(Self::Lean48),
            WLeanLevelProfile::Lean430 => Ok(Self::Lean430),
        }
    }
}
