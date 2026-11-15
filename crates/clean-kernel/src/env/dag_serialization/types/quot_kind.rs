// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::quot::QuotKind as SQuotKind;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WQuotKind {
    Type,
    Mk,
    Lift,
    Ind,
    Sound,
}
impl Wire for WQuotKind {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Type),
            1 => Ok(Self::Mk),
            2 => Ok(Self::Lift),
            3 => Ok(Self::Ind),
            4 => Ok(Self::Sound),
            _ => Err(error("unknown WQuotKind tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Type => {
                w.u32(0)?;
                Ok(())
            }
            Self::Mk => {
                w.u32(1)?;
                Ok(())
            }
            Self::Lift => {
                w.u32(2)?;
                Ok(())
            }
            Self::Ind => {
                w.u32(3)?;
                Ok(())
            }
            Self::Sound => {
                w.u32(4)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SQuotKind {
    type Wire = WQuotKind;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SQuotKind::Type => Ok(WQuotKind::Type),
            SQuotKind::Mk => Ok(WQuotKind::Mk),
            SQuotKind::Lift => Ok(WQuotKind::Lift),
            SQuotKind::Ind => Ok(WQuotKind::Ind),
            SQuotKind::Sound => Ok(WQuotKind::Sound),
        }
    }
}
impl FromWire<WQuotKind> for SQuotKind {
    fn from_wire(wire: WQuotKind, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WQuotKind::Type => Ok(Self::Type),
            WQuotKind::Mk => Ok(Self::Mk),
            WQuotKind::Lift => Ok(Self::Lift),
            WQuotKind::Ind => Ok(Self::Ind),
            WQuotKind::Sound => Ok(Self::Sound),
        }
    }
}
