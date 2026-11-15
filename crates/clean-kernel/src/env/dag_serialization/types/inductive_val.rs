// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::inductive::InductiveVal as SInductiveVal;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WInductiveVal {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) level_params: Vec<WName>,
    pub(in crate::env::dag_serialization) type_: Ref,
    pub(in crate::env::dag_serialization) num_params: u32,
    pub(in crate::env::dag_serialization) num_indices: u32,
    pub(in crate::env::dag_serialization) all_names: Vec<WName>,
    pub(in crate::env::dag_serialization) constructor_names: Vec<WName>,
    pub(in crate::env::dag_serialization) is_recursive: bool,
    pub(in crate::env::dag_serialization) is_reflexive: bool,
    pub(in crate::env::dag_serialization) is_large_elim: bool,
    pub(in crate::env::dag_serialization) is_nested: bool,
}
impl Wire for WInductiveVal {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            level_params: <Vec<WName> as Wire>::read(r)?,
            type_: <Ref as Wire>::read(r)?,
            num_params: <u32 as Wire>::read(r)?,
            num_indices: <u32 as Wire>::read(r)?,
            all_names: <Vec<WName> as Wire>::read(r)?,
            constructor_names: <Vec<WName> as Wire>::read(r)?,
            is_recursive: <bool as Wire>::read(r)?,
            is_reflexive: <bool as Wire>::read(r)?,
            is_large_elim: <bool as Wire>::read(r)?,
            is_nested: <bool as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.level_params.write(w)?;
        self.type_.write(w)?;
        self.num_params.write(w)?;
        self.num_indices.write(w)?;
        self.all_names.write(w)?;
        self.constructor_names.write(w)?;
        self.is_recursive.write(w)?;
        self.is_reflexive.write(w)?;
        self.is_large_elim.write(w)?;
        self.is_nested.write(w)?;
        Ok(())
    }
}
impl ToWire for SInductiveVal {
    type Wire = WInductiveVal;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SInductiveVal {
            name: __wire_field_0,
            level_params: __wire_field_1,
            type_: __wire_field_2,
            num_params: __wire_field_3,
            num_indices: __wire_field_4,
            all_names: __wire_field_5,
            constructor_names: __wire_field_6,
            is_recursive: __wire_field_7,
            is_reflexive: __wire_field_8,
            is_large_elim: __wire_field_9,
            is_nested: __wire_field_10,
        } = self;
        Ok(WInductiveVal {
            name: __wire_field_0.to_wire(p)?,
            level_params: __wire_field_1.to_wire(p)?,
            type_: __wire_field_2.to_wire(p)?,
            num_params: __wire_field_3.to_wire(p)?,
            num_indices: __wire_field_4.to_wire(p)?,
            all_names: __wire_field_5.to_wire(p)?,
            constructor_names: __wire_field_6.to_wire(p)?,
            is_recursive: __wire_field_7.to_wire(p)?,
            is_reflexive: __wire_field_8.to_wire(p)?,
            is_large_elim: __wire_field_9.to_wire(p)?,
            is_nested: __wire_field_10.to_wire(p)?,
        })
    }
}
impl FromWire<WInductiveVal> for SInductiveVal {
    fn from_wire(wire: WInductiveVal, r: &mut Restoration) -> Result<Self> {
        let WInductiveVal {
            name: __wire_field_0,
            level_params: __wire_field_1,
            type_: __wire_field_2,
            num_params: __wire_field_3,
            num_indices: __wire_field_4,
            all_names: __wire_field_5,
            constructor_names: __wire_field_6,
            is_recursive: __wire_field_7,
            is_reflexive: __wire_field_8,
            is_large_elim: __wire_field_9,
            is_nested: __wire_field_10,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            level_params: FromWire::from_wire(__wire_field_1, r)?,
            type_: FromWire::from_wire(__wire_field_2, r)?,
            num_params: FromWire::from_wire(__wire_field_3, r)?,
            num_indices: FromWire::from_wire(__wire_field_4, r)?,
            all_names: FromWire::from_wire(__wire_field_5, r)?,
            constructor_names: FromWire::from_wire(__wire_field_6, r)?,
            is_recursive: FromWire::from_wire(__wire_field_7, r)?,
            is_reflexive: FromWire::from_wire(__wire_field_8, r)?,
            is_large_elim: FromWire::from_wire(__wire_field_9, r)?,
            is_nested: FromWire::from_wire(__wire_field_10, r)?,
        })
    }
}
