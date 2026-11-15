// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::aesop::AesopIndexMode as SAesopIndexMode;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WAesopIndexMode {
    Target,
    Hyps,
    Unindexed,
}
impl Wire for WAesopIndexMode {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Target),
            1 => Ok(Self::Hyps),
            2 => Ok(Self::Unindexed),
            _ => Err(error("unknown WAesopIndexMode tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Target => {
                w.u32(0)?;
                Ok(())
            }
            Self::Hyps => {
                w.u32(1)?;
                Ok(())
            }
            Self::Unindexed => {
                w.u32(2)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SAesopIndexMode {
    type Wire = WAesopIndexMode;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SAesopIndexMode::Target => Ok(WAesopIndexMode::Target),
            SAesopIndexMode::Hyps => Ok(WAesopIndexMode::Hyps),
            SAesopIndexMode::Unindexed => Ok(WAesopIndexMode::Unindexed),
        }
    }
}
impl FromWire<WAesopIndexMode> for SAesopIndexMode {
    fn from_wire(wire: WAesopIndexMode, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WAesopIndexMode::Target => Ok(Self::Target),
            WAesopIndexMode::Hyps => Ok(Self::Hyps),
            WAesopIndexMode::Unindexed => Ok(Self::Unindexed),
        }
    }
}
