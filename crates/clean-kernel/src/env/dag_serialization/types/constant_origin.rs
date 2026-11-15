// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::origin::ConstantOrigin as SConstantOrigin;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WConstantOrigin {
    Kernel {
        trust: WOriginTrust,
    },
    Olean {
        module: Option<String>,
        trust: WOriginTrust,
    },
    CleanPayload {
        module: Option<String>,
        trust: WOriginTrust,
    },
}
impl Wire for WConstantOrigin {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Kernel {
                trust: <WOriginTrust as Wire>::read(r)?,
            }),
            1 => Ok(Self::Olean {
                module: <Option<String> as Wire>::read(r)?,
                trust: <WOriginTrust as Wire>::read(r)?,
            }),
            2 => Ok(Self::CleanPayload {
                module: <Option<String> as Wire>::read(r)?,
                trust: <WOriginTrust as Wire>::read(r)?,
            }),
            _ => Err(error("unknown WConstantOrigin tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Kernel {
                trust: __wire_field_0,
            } => {
                w.u32(0)?;
                __wire_field_0.write(w)?;
                Ok(())
            }
            Self::Olean {
                module: __wire_field_0,
                trust: __wire_field_1,
            } => {
                w.u32(1)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
            Self::CleanPayload {
                module: __wire_field_0,
                trust: __wire_field_1,
            } => {
                w.u32(2)?;
                __wire_field_0.write(w)?;
                __wire_field_1.write(w)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SConstantOrigin {
    type Wire = WConstantOrigin;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SConstantOrigin::Kernel {
                trust: __wire_field_0,
            } => Ok(WConstantOrigin::Kernel {
                trust: __wire_field_0.to_wire(p)?,
            }),
            SConstantOrigin::Olean {
                module: __wire_field_0,
                trust: __wire_field_1,
            } => Ok(WConstantOrigin::Olean {
                module: __wire_field_0.to_wire(p)?,
                trust: __wire_field_1.to_wire(p)?,
            }),
            SConstantOrigin::CleanPayload {
                module: __wire_field_0,
                trust: __wire_field_1,
            } => Ok(WConstantOrigin::CleanPayload {
                module: __wire_field_0.to_wire(p)?,
                trust: __wire_field_1.to_wire(p)?,
            }),
        }
    }
}
impl FromWire<WConstantOrigin> for SConstantOrigin {
    fn from_wire(wire: WConstantOrigin, r: &mut Restoration) -> Result<Self> {
        match wire {
            WConstantOrigin::Kernel {
                trust: __wire_field_0,
            } => Ok(Self::Kernel {
                trust: FromWire::from_wire(__wire_field_0, r)?,
            }),
            WConstantOrigin::Olean {
                module: __wire_field_0,
                trust: __wire_field_1,
            } => Ok(Self::Olean {
                module: FromWire::from_wire(__wire_field_0, r)?,
                trust: FromWire::from_wire(__wire_field_1, r)?,
            }),
            WConstantOrigin::CleanPayload {
                module: __wire_field_0,
                trust: __wire_field_1,
            } => Ok(Self::CleanPayload {
                module: FromWire::from_wire(__wire_field_0, r)?,
                trust: FromWire::from_wire(__wire_field_1, r)?,
            }),
        }
    }
}
