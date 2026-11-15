// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::expr::BinderData as SBinderData;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WBinderData {
    pub(in crate::env::dag_serialization) info: WBinderInfo,
    pub(in crate::env::dag_serialization) mult: WMultiplicity,
}
impl Wire for WBinderData {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            info: <WBinderInfo as Wire>::read(r)?,
            mult: <WMultiplicity as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.info.write(w)?;
        self.mult.write(w)?;
        Ok(())
    }
}
impl ToWire for SBinderData {
    type Wire = WBinderData;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SBinderData {
            info: __wire_field_0,
            mult: __wire_field_1,
        } = self;
        Ok(WBinderData {
            info: __wire_field_0.to_wire(p)?,
            mult: __wire_field_1.to_wire(p)?,
        })
    }
}
impl FromWire<WBinderData> for SBinderData {
    fn from_wire(wire: WBinderData, r: &mut Restoration) -> Result<Self> {
        let WBinderData {
            info: __wire_field_0,
            mult: __wire_field_1,
        } = wire;
        Ok(Self {
            info: FromWire::from_wire(__wire_field_0, r)?,
            mult: FromWire::from_wire(__wire_field_1, r)?,
        })
    }
}
