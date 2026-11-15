// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::SimpPriority as SSimpPriority;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WSimpPriority {
    Default,
    Custom(u32),
}
impl Wire for WSimpPriority {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Default),
            1 => Ok(Self::Custom(<u32 as Wire>::read(r)?)),
            _ => Err(error("unknown WSimpPriority tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Default => {
                w.u32(0)?;
                Ok(())
            }
            Self::Custom(__wire_field_0) => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SSimpPriority {
    type Wire = WSimpPriority;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SSimpPriority::Default => Ok(WSimpPriority::Default),
            SSimpPriority::Custom(__wire_field_0) => {
                Ok(WSimpPriority::Custom(__wire_field_0.to_wire(p)?))
            }
        }
    }
}
impl FromWire<WSimpPriority> for SSimpPriority {
    fn from_wire(wire: WSimpPriority, r: &mut Restoration) -> Result<Self> {
        match wire {
            WSimpPriority::Default => Ok(Self::Default),
            WSimpPriority::Custom(__wire_field_0) => {
                Ok(Self::Custom(FromWire::from_wire(__wire_field_0, r)?))
            }
        }
    }
}
