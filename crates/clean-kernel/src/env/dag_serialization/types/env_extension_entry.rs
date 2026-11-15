// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::EnvExtensionEntry as SEnvExtensionEntry;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WEnvExtensionEntry {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) data: WEnvExtensionEntryData,
}
impl Wire for WEnvExtensionEntry {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            data: <WEnvExtensionEntryData as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.data.write(w)?;
        Ok(())
    }
}
impl ToWire for SEnvExtensionEntry {
    type Wire = WEnvExtensionEntry;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SEnvExtensionEntry {
            name: __wire_field_0,
            data: __wire_field_1,
        } = self;
        Ok(WEnvExtensionEntry {
            name: __wire_field_0.to_wire(p)?,
            data: __wire_field_1.to_wire(p)?,
        })
    }
}
impl FromWire<WEnvExtensionEntry> for SEnvExtensionEntry {
    fn from_wire(wire: WEnvExtensionEntry, r: &mut Restoration) -> Result<Self> {
        let WEnvExtensionEntry {
            name: __wire_field_0,
            data: __wire_field_1,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            data: FromWire::from_wire(__wire_field_1, r)?,
        })
    }
}
