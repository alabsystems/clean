// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::quot::QuotVal as SQuotVal;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WQuotVal {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) level_params: Vec<WName>,
    pub(in crate::env::dag_serialization) type_: Ref,
    pub(in crate::env::dag_serialization) kind: WQuotKind,
}
impl Wire for WQuotVal {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            level_params: <Vec<WName> as Wire>::read(r)?,
            type_: <Ref as Wire>::read(r)?,
            kind: <WQuotKind as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.level_params.write(w)?;
        self.type_.write(w)?;
        self.kind.write(w)?;
        Ok(())
    }
}
impl ToWire for SQuotVal {
    type Wire = WQuotVal;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SQuotVal {
            name: __wire_field_0,
            level_params: __wire_field_1,
            type_: __wire_field_2,
            kind: __wire_field_3,
        } = self;
        Ok(WQuotVal {
            name: __wire_field_0.to_wire(p)?,
            level_params: __wire_field_1.to_wire(p)?,
            type_: __wire_field_2.to_wire(p)?,
            kind: __wire_field_3.to_wire(p)?,
        })
    }
}
impl FromWire<WQuotVal> for SQuotVal {
    fn from_wire(wire: WQuotVal, r: &mut Restoration) -> Result<Self> {
        let WQuotVal {
            name: __wire_field_0,
            level_params: __wire_field_1,
            type_: __wire_field_2,
            kind: __wire_field_3,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            level_params: FromWire::from_wire(__wire_field_1, r)?,
            type_: FromWire::from_wire(__wire_field_2, r)?,
            kind: FromWire::from_wire(__wire_field_3, r)?,
        })
    }
}
