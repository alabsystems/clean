// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::PersistentEnvExtensionState as SPersistentEnvExtensionState;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WPersistentEnvExtensionState {
    pub(in crate::env::dag_serialization) imported_entries: Vec<Vec<WEnvExtensionEntry>>,
    pub(in crate::env::dag_serialization) state: Vec<u8>,
}
impl Wire for WPersistentEnvExtensionState {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            imported_entries: <Vec<Vec<WEnvExtensionEntry>> as Wire>::read(r)?,
            state: <Vec<u8> as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.imported_entries.write(w)?;
        self.state.write(w)?;
        Ok(())
    }
}
impl ToWire for SPersistentEnvExtensionState {
    type Wire = WPersistentEnvExtensionState;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SPersistentEnvExtensionState {
            imported_entries: __wire_field_0,
            state: __wire_field_1,
        } = self;
        Ok(WPersistentEnvExtensionState {
            imported_entries: __wire_field_0.to_wire(p)?,
            state: __wire_field_1.to_wire(p)?,
        })
    }
}
impl FromWire<WPersistentEnvExtensionState> for SPersistentEnvExtensionState {
    fn from_wire(wire: WPersistentEnvExtensionState, r: &mut Restoration) -> Result<Self> {
        let WPersistentEnvExtensionState {
            imported_entries: __wire_field_0,
            state: __wire_field_1,
        } = wire;
        Ok(Self {
            imported_entries: FromWire::from_wire(__wire_field_0, r)?,
            state: FromWire::from_wire(__wire_field_1, r)?,
        })
    }
}
