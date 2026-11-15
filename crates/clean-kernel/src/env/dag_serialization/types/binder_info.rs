// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::BinderInfo as SBinderInfo;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WBinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}
impl Wire for WBinderInfo {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Default),
            1 => Ok(Self::Implicit),
            2 => Ok(Self::StrictImplicit),
            3 => Ok(Self::InstImplicit),
            _ => Err(error("unknown WBinderInfo tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Default => {
                w.u32(0)?;
                Ok(())
            }
            Self::Implicit => {
                w.u32(1)?;
                Ok(())
            }
            Self::StrictImplicit => {
                w.u32(2)?;
                Ok(())
            }
            Self::InstImplicit => {
                w.u32(3)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SBinderInfo {
    type Wire = WBinderInfo;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SBinderInfo::Default => Ok(WBinderInfo::Default),
            SBinderInfo::Implicit => Ok(WBinderInfo::Implicit),
            SBinderInfo::StrictImplicit => Ok(WBinderInfo::StrictImplicit),
            SBinderInfo::InstImplicit => Ok(WBinderInfo::InstImplicit),
        }
    }
}
impl FromWire<WBinderInfo> for SBinderInfo {
    fn from_wire(wire: WBinderInfo, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WBinderInfo::Default => Ok(Self::Default),
            WBinderInfo::Implicit => Ok(Self::Implicit),
            WBinderInfo::StrictImplicit => Ok(Self::StrictImplicit),
            WBinderInfo::InstImplicit => Ok(Self::InstImplicit),
        }
    }
}
