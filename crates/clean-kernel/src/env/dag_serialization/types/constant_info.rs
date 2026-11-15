// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::ConstantInfo as SConstantInfo;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WConstantInfo {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) level_params: Vec<WName>,
    pub(in crate::env::dag_serialization) type_: Ref,
    pub(in crate::env::dag_serialization) value: Option<Ref>,
    pub(in crate::env::dag_serialization) is_reducible: bool,
    pub(in crate::env::dag_serialization) reducibility: WReducibility,
    pub(in crate::env::dag_serialization) kind: WConstantKind,
}
impl Wire for WConstantInfo {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            level_params: <Vec<WName> as Wire>::read(r)?,
            type_: <Ref as Wire>::read(r)?,
            value: <Option<Ref> as Wire>::read(r)?,
            is_reducible: <bool as Wire>::read(r)?,
            reducibility: <WReducibility as Wire>::read(r)?,
            kind: <WConstantKind as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.level_params.write(w)?;
        self.type_.write(w)?;
        self.value.write(w)?;
        self.is_reducible.write(w)?;
        self.reducibility.write(w)?;
        self.kind.write(w)?;
        Ok(())
    }
}
impl ToWire for SConstantInfo {
    type Wire = WConstantInfo;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SConstantInfo {
            name: __wire_field_0,
            level_params: __wire_field_1,
            type_: __wire_field_2,
            value: __wire_field_3,
            is_reducible: __wire_field_4,
            reducibility: __wire_field_5,
            kind: __wire_field_6,
        } = self;
        Ok(WConstantInfo {
            name: __wire_field_0.to_wire(p)?,
            level_params: __wire_field_1.to_wire(p)?,
            type_: __wire_field_2.to_wire(p)?,
            value: __wire_field_3.to_wire(p)?,
            is_reducible: __wire_field_4.to_wire(p)?,
            reducibility: __wire_field_5.to_wire(p)?,
            kind: __wire_field_6.to_wire(p)?,
        })
    }
}
impl FromWire<WConstantInfo> for SConstantInfo {
    fn from_wire(wire: WConstantInfo, r: &mut Restoration) -> Result<Self> {
        let WConstantInfo {
            name: __wire_field_0,
            level_params: __wire_field_1,
            type_: __wire_field_2,
            value: __wire_field_3,
            is_reducible: __wire_field_4,
            reducibility: __wire_field_5,
            kind: __wire_field_6,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            level_params: FromWire::from_wire(__wire_field_1, r)?,
            type_: FromWire::from_wire(__wire_field_2, r)?,
            value: FromWire::from_wire(__wire_field_3, r)?,
            is_reducible: FromWire::from_wire(__wire_field_4, r)?,
            reducibility: FromWire::from_wire(__wire_field_5, r)?,
            kind: FromWire::from_wire(__wire_field_6, r)?,
        })
    }
}
