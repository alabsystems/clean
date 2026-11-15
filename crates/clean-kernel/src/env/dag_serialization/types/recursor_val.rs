// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::inductive::RecursorVal as SRecursorVal;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WRecursorVal {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) arg_order: WRecursorArgOrder,
    pub(in crate::env::dag_serialization) level_params: Vec<WName>,
    pub(in crate::env::dag_serialization) type_: Ref,
    pub(in crate::env::dag_serialization) inductive_name: WName,
    pub(in crate::env::dag_serialization) num_params: u32,
    pub(in crate::env::dag_serialization) num_indices: u32,
    pub(in crate::env::dag_serialization) num_motives: u32,
    pub(in crate::env::dag_serialization) num_minors: u32,
    pub(in crate::env::dag_serialization) rules: Vec<WRecursorRule>,
    pub(in crate::env::dag_serialization) is_k: bool,
}
impl Wire for WRecursorVal {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            arg_order: <WRecursorArgOrder as Wire>::read(r)?,
            level_params: <Vec<WName> as Wire>::read(r)?,
            type_: <Ref as Wire>::read(r)?,
            inductive_name: <WName as Wire>::read(r)?,
            num_params: <u32 as Wire>::read(r)?,
            num_indices: <u32 as Wire>::read(r)?,
            num_motives: <u32 as Wire>::read(r)?,
            num_minors: <u32 as Wire>::read(r)?,
            rules: <Vec<WRecursorRule> as Wire>::read(r)?,
            is_k: <bool as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.arg_order.write(w)?;
        self.level_params.write(w)?;
        self.type_.write(w)?;
        self.inductive_name.write(w)?;
        self.num_params.write(w)?;
        self.num_indices.write(w)?;
        self.num_motives.write(w)?;
        self.num_minors.write(w)?;
        self.rules.write(w)?;
        self.is_k.write(w)?;
        Ok(())
    }
}
impl ToWire for SRecursorVal {
    type Wire = WRecursorVal;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SRecursorVal {
            name: __wire_field_0,
            arg_order: __wire_field_1,
            level_params: __wire_field_2,
            type_: __wire_field_3,
            inductive_name: __wire_field_4,
            num_params: __wire_field_5,
            num_indices: __wire_field_6,
            num_motives: __wire_field_7,
            num_minors: __wire_field_8,
            rules: __wire_field_9,
            is_k: __wire_field_10,
        } = self;
        Ok(WRecursorVal {
            name: __wire_field_0.to_wire(p)?,
            arg_order: __wire_field_1.to_wire(p)?,
            level_params: __wire_field_2.to_wire(p)?,
            type_: __wire_field_3.to_wire(p)?,
            inductive_name: __wire_field_4.to_wire(p)?,
            num_params: __wire_field_5.to_wire(p)?,
            num_indices: __wire_field_6.to_wire(p)?,
            num_motives: __wire_field_7.to_wire(p)?,
            num_minors: __wire_field_8.to_wire(p)?,
            rules: __wire_field_9.to_wire(p)?,
            is_k: __wire_field_10.to_wire(p)?,
        })
    }
}
impl FromWire<WRecursorVal> for SRecursorVal {
    fn from_wire(wire: WRecursorVal, r: &mut Restoration) -> Result<Self> {
        let WRecursorVal {
            name: __wire_field_0,
            arg_order: __wire_field_1,
            level_params: __wire_field_2,
            type_: __wire_field_3,
            inductive_name: __wire_field_4,
            num_params: __wire_field_5,
            num_indices: __wire_field_6,
            num_motives: __wire_field_7,
            num_minors: __wire_field_8,
            rules: __wire_field_9,
            is_k: __wire_field_10,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            arg_order: FromWire::from_wire(__wire_field_1, r)?,
            level_params: FromWire::from_wire(__wire_field_2, r)?,
            type_: FromWire::from_wire(__wire_field_3, r)?,
            inductive_name: FromWire::from_wire(__wire_field_4, r)?,
            num_params: FromWire::from_wire(__wire_field_5, r)?,
            num_indices: FromWire::from_wire(__wire_field_6, r)?,
            num_motives: FromWire::from_wire(__wire_field_7, r)?,
            num_minors: FromWire::from_wire(__wire_field_8, r)?,
            rules: FromWire::from_wire(__wire_field_9, r)?,
            is_k: FromWire::from_wire(__wire_field_10, r)?,
        })
    }
}
