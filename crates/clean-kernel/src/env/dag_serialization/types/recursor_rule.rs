// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::inductive::RecursorRule as SRecursorRule;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WRecursorRule {
    pub(in crate::env::dag_serialization) constructor_name: WName,
    pub(in crate::env::dag_serialization) num_fields: u32,
    pub(in crate::env::dag_serialization) recursive_fields: Vec<bool>,
    pub(in crate::env::dag_serialization) rhs: Ref,
}
impl Wire for WRecursorRule {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            constructor_name: <WName as Wire>::read(r)?,
            num_fields: <u32 as Wire>::read(r)?,
            recursive_fields: <Vec<bool> as Wire>::read(r)?,
            rhs: <Ref as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.constructor_name.write(w)?;
        self.num_fields.write(w)?;
        self.recursive_fields.write(w)?;
        self.rhs.write(w)?;
        Ok(())
    }
}
impl ToWire for SRecursorRule {
    type Wire = WRecursorRule;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SRecursorRule {
            constructor_name: __wire_field_0,
            num_fields: __wire_field_1,
            recursive_fields: __wire_field_2,
            rhs: __wire_field_3,
        } = self;
        Ok(WRecursorRule {
            constructor_name: __wire_field_0.to_wire(p)?,
            num_fields: __wire_field_1.to_wire(p)?,
            recursive_fields: __wire_field_2.to_wire(p)?,
            rhs: __wire_field_3.to_wire(p)?,
        })
    }
}
impl FromWire<WRecursorRule> for SRecursorRule {
    fn from_wire(wire: WRecursorRule, r: &mut Restoration) -> Result<Self> {
        let WRecursorRule {
            constructor_name: __wire_field_0,
            num_fields: __wire_field_1,
            recursive_fields: __wire_field_2,
            rhs: __wire_field_3,
        } = wire;
        Ok(Self {
            constructor_name: FromWire::from_wire(__wire_field_0, r)?,
            num_fields: FromWire::from_wire(__wire_field_1, r)?,
            recursive_fields: FromWire::from_wire(__wire_field_2, r)?,
            rhs: FromWire::from_wire(__wire_field_3, r)?,
        })
    }
}
