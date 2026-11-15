// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::SimpLemmaInfo as SSimpLemmaInfo;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WSimpLemmaInfo {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) priority: WSimpPriority,
}
impl Wire for WSimpLemmaInfo {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            priority: <WSimpPriority as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.priority.write(w)?;
        Ok(())
    }
}
impl ToWire for SSimpLemmaInfo {
    type Wire = WSimpLemmaInfo;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SSimpLemmaInfo {
            name: __wire_field_0,
            priority: __wire_field_1,
        } = self;
        Ok(WSimpLemmaInfo {
            name: __wire_field_0.to_wire(p)?,
            priority: __wire_field_1.to_wire(p)?,
        })
    }
}
impl FromWire<WSimpLemmaInfo> for SSimpLemmaInfo {
    fn from_wire(wire: WSimpLemmaInfo, r: &mut Restoration) -> Result<Self> {
        let WSimpLemmaInfo {
            name: __wire_field_0,
            priority: __wire_field_1,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            priority: FromWire::from_wire(__wire_field_1, r)?,
        })
    }
}
