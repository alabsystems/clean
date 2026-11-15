// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::mode::CleanMode as SCleanMode;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WCleanMode {
    Constructive,
    Impredicative,
    Cubical,
    Directed,
    Classical,
    SetTheoretic,
}
impl Wire for WCleanMode {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Constructive),
            1 => Ok(Self::Impredicative),
            2 => Ok(Self::Cubical),
            3 => Ok(Self::Directed),
            4 => Ok(Self::Classical),
            5 => Ok(Self::SetTheoretic),
            _ => Err(error("unknown WCleanMode tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Constructive => {
                w.u32(0)?;
                Ok(())
            }
            Self::Impredicative => {
                w.u32(1)?;
                Ok(())
            }
            Self::Cubical => {
                w.u32(2)?;
                Ok(())
            }
            Self::Directed => {
                w.u32(3)?;
                Ok(())
            }
            Self::Classical => {
                w.u32(4)?;
                Ok(())
            }
            Self::SetTheoretic => {
                w.u32(5)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SCleanMode {
    type Wire = WCleanMode;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SCleanMode::Constructive => Ok(WCleanMode::Constructive),
            SCleanMode::Impredicative => Ok(WCleanMode::Impredicative),
            SCleanMode::Cubical => Ok(WCleanMode::Cubical),
            SCleanMode::Directed => Ok(WCleanMode::Directed),
            SCleanMode::Classical => Ok(WCleanMode::Classical),
            SCleanMode::SetTheoretic => Ok(WCleanMode::SetTheoretic),
        }
    }
}
impl FromWire<WCleanMode> for SCleanMode {
    fn from_wire(wire: WCleanMode, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WCleanMode::Constructive => Ok(Self::Constructive),
            WCleanMode::Impredicative => Ok(Self::Impredicative),
            WCleanMode::Cubical => Ok(Self::Cubical),
            WCleanMode::Directed => Ok(Self::Directed),
            WCleanMode::Classical => Ok(Self::Classical),
            WCleanMode::SetTheoretic => Ok(Self::SetTheoretic),
        }
    }
}
