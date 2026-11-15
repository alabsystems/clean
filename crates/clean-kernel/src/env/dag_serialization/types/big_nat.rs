// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::BigNat as SBigNat;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WBigNat {
    Small(u64),
    Big(Vec<u64>),
}
impl Wire for WBigNat {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Small(<u64 as Wire>::read(r)?)),
            1 => Ok(Self::Big(<Vec<u64> as Wire>::read(r)?)),
            _ => Err(error("unknown WBigNat tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Small(__wire_field_0) => {
                w.u32(0)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Big(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SBigNat {
    type Wire = WBigNat;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SBigNat::Small(__wire_field_0) => Ok(WBigNat::Small(__wire_field_0.to_wire(p)?)),
            SBigNat::Big(__wire_field_0) => Ok(WBigNat::Big(__wire_field_0.to_wire(p)?)),
        }
    }
}
impl FromWire<WBigNat> for SBigNat {
    fn from_wire(wire: WBigNat, r: &mut Restoration) -> Result<Self> {
        match wire {
            WBigNat::Small(__wire_field_0) => {
                Ok(Self::Small(FromWire::from_wire(__wire_field_0, r)?))
            }
            WBigNat::Big(__wire_field_0) => Ok(Self::Big(FromWire::from_wire(__wire_field_0, r)?)),
        }
    }
}
