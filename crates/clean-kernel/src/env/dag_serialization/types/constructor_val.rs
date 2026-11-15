// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::inductive::ConstructorVal as SConstructorVal;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WConstructorVal {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) inductive_name: WName,
    pub(in crate::env::dag_serialization) level_params: Vec<WName>,
    pub(in crate::env::dag_serialization) type_: Ref,
    pub(in crate::env::dag_serialization) num_params: u32,
    pub(in crate::env::dag_serialization) num_fields: u32,
    pub(in crate::env::dag_serialization) constructor_idx: u32,
}
impl Wire for WConstructorVal {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            inductive_name: <WName as Wire>::read(r)?,
            level_params: <Vec<WName> as Wire>::read(r)?,
            type_: <Ref as Wire>::read(r)?,
            num_params: <u32 as Wire>::read(r)?,
            num_fields: <u32 as Wire>::read(r)?,
            constructor_idx: <u32 as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.inductive_name.write(w)?;
        self.level_params.write(w)?;
        self.type_.write(w)?;
        self.num_params.write(w)?;
        self.num_fields.write(w)?;
        self.constructor_idx.write(w)?;
        Ok(())
    }
}
impl ToWire for SConstructorVal {
    type Wire = WConstructorVal;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SConstructorVal {
            name: __wire_field_0,
            inductive_name: __wire_field_1,
            level_params: __wire_field_2,
            type_: __wire_field_3,
            num_params: __wire_field_4,
            num_fields: __wire_field_5,
            constructor_idx: __wire_field_6,
        } = self;
        Ok(WConstructorVal {
            name: __wire_field_0.to_wire(p)?,
            inductive_name: __wire_field_1.to_wire(p)?,
            level_params: __wire_field_2.to_wire(p)?,
            type_: __wire_field_3.to_wire(p)?,
            num_params: __wire_field_4.to_wire(p)?,
            num_fields: __wire_field_5.to_wire(p)?,
            constructor_idx: __wire_field_6.to_wire(p)?,
        })
    }
}
impl FromWire<WConstructorVal> for SConstructorVal {
    fn from_wire(wire: WConstructorVal, r: &mut Restoration) -> Result<Self> {
        let WConstructorVal {
            name: __wire_field_0,
            inductive_name: __wire_field_1,
            level_params: __wire_field_2,
            type_: __wire_field_3,
            num_params: __wire_field_4,
            num_fields: __wire_field_5,
            constructor_idx: __wire_field_6,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            inductive_name: FromWire::from_wire(__wire_field_1, r)?,
            level_params: FromWire::from_wire(__wire_field_2, r)?,
            type_: FromWire::from_wire(__wire_field_3, r)?,
            num_params: FromWire::from_wire(__wire_field_4, r)?,
            num_fields: FromWire::from_wire(__wire_field_5, r)?,
            constructor_idx: FromWire::from_wire(__wire_field_6, r)?,
        })
    }
}
