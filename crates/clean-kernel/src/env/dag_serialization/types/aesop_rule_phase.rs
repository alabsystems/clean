// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::aesop::AesopRulePhase as SAesopRulePhase;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WAesopRulePhase {
    Safe,
    Unsafe,
    Norm,
}
impl Wire for WAesopRulePhase {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Safe),
            1 => Ok(Self::Unsafe),
            2 => Ok(Self::Norm),
            _ => Err(error("unknown WAesopRulePhase tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Safe => {
                w.u32(0)?;
                Ok(())
            }
            Self::Unsafe => {
                w.u32(1)?;
                Ok(())
            }
            Self::Norm => {
                w.u32(2)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SAesopRulePhase {
    type Wire = WAesopRulePhase;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SAesopRulePhase::Safe => Ok(WAesopRulePhase::Safe),
            SAesopRulePhase::Unsafe => Ok(WAesopRulePhase::Unsafe),
            SAesopRulePhase::Norm => Ok(WAesopRulePhase::Norm),
        }
    }
}
impl FromWire<WAesopRulePhase> for SAesopRulePhase {
    fn from_wire(wire: WAesopRulePhase, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WAesopRulePhase::Safe => Ok(Self::Safe),
            WAesopRulePhase::Unsafe => Ok(Self::Unsafe),
            WAesopRulePhase::Norm => Ok(Self::Norm),
        }
    }
}
