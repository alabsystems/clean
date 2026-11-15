// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::inductive::RecursorArgOrder as SRecursorArgOrder;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WRecursorArgOrder {
    MajorAfterMinors,
    MajorAfterMotive,
}
impl Wire for WRecursorArgOrder {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::MajorAfterMinors),
            1 => Ok(Self::MajorAfterMotive),
            _ => Err(error("unknown WRecursorArgOrder tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::MajorAfterMinors => {
                w.u32(0)?;
                Ok(())
            }
            Self::MajorAfterMotive => {
                w.u32(1)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SRecursorArgOrder {
    type Wire = WRecursorArgOrder;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SRecursorArgOrder::MajorAfterMinors => Ok(WRecursorArgOrder::MajorAfterMinors),
            SRecursorArgOrder::MajorAfterMotive => Ok(WRecursorArgOrder::MajorAfterMotive),
        }
    }
}
impl FromWire<WRecursorArgOrder> for SRecursorArgOrder {
    fn from_wire(wire: WRecursorArgOrder, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WRecursorArgOrder::MajorAfterMinors => Ok(Self::MajorAfterMinors),
            WRecursorArgOrder::MajorAfterMotive => Ok(Self::MajorAfterMotive),
        }
    }
}
