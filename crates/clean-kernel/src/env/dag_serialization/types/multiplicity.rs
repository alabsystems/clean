// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::Multiplicity as SMultiplicity;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WMultiplicity {
    Zero,
    One,
    Many,
}
impl Wire for WMultiplicity {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Zero),
            1 => Ok(Self::One),
            2 => Ok(Self::Many),
            _ => Err(error("unknown WMultiplicity tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Zero => {
                w.u32(0)?;
                Ok(())
            }
            Self::One => {
                w.u32(1)?;
                Ok(())
            }
            Self::Many => {
                w.u32(2)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SMultiplicity {
    type Wire = WMultiplicity;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SMultiplicity::Zero => Ok(WMultiplicity::Zero),
            SMultiplicity::One => Ok(WMultiplicity::One),
            SMultiplicity::Many => Ok(WMultiplicity::Many),
        }
    }
}
impl FromWire<WMultiplicity> for SMultiplicity {
    fn from_wire(wire: WMultiplicity, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WMultiplicity::Zero => Ok(Self::Zero),
            WMultiplicity::One => Ok(Self::One),
            WMultiplicity::Many => Ok(Self::Many),
        }
    }
}
