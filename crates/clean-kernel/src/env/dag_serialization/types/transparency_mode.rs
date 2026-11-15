// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::TransparencyMode as STransparencyMode;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WTransparencyMode {
    Reducible,
    Instances,
    Default,
    All,
}
impl Wire for WTransparencyMode {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Reducible),
            1 => Ok(Self::Instances),
            2 => Ok(Self::Default),
            3 => Ok(Self::All),
            _ => Err(error("unknown WTransparencyMode tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Reducible => {
                w.u32(0)?;
                Ok(())
            }
            Self::Instances => {
                w.u32(1)?;
                Ok(())
            }
            Self::Default => {
                w.u32(2)?;
                Ok(())
            }
            Self::All => {
                w.u32(3)?;
                Ok(())
            }
        }
    }
}
impl ToWire for STransparencyMode {
    type Wire = WTransparencyMode;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            STransparencyMode::Reducible => Ok(WTransparencyMode::Reducible),
            STransparencyMode::Instances => Ok(WTransparencyMode::Instances),
            STransparencyMode::Default => Ok(WTransparencyMode::Default),
            STransparencyMode::All => Ok(WTransparencyMode::All),
        }
    }
}
impl FromWire<WTransparencyMode> for STransparencyMode {
    fn from_wire(wire: WTransparencyMode, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WTransparencyMode::Reducible => Ok(Self::Reducible),
            WTransparencyMode::Instances => Ok(Self::Instances),
            WTransparencyMode::Default => Ok(Self::Default),
            WTransparencyMode::All => Ok(Self::All),
        }
    }
}
