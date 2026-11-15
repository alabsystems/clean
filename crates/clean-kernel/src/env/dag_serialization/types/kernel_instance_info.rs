// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::KernelInstanceInfo as SKernelInstanceInfo;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WKernelInstanceInfo {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) class_name: WName,
    pub(in crate::env::dag_serialization) priority: u32,
    pub(in crate::env::dag_serialization) type_: Option<Ref>,
    pub(in crate::env::dag_serialization) value: Option<Ref>,
}
impl Wire for WKernelInstanceInfo {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            class_name: <WName as Wire>::read(r)?,
            priority: <u32 as Wire>::read(r)?,
            type_: <Option<Ref> as Wire>::read(r)?,
            value: <Option<Ref> as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.class_name.write(w)?;
        self.priority.write(w)?;
        self.type_.write(w)?;
        self.value.write(w)?;
        Ok(())
    }
}
impl ToWire for SKernelInstanceInfo {
    type Wire = WKernelInstanceInfo;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SKernelInstanceInfo {
            name: __wire_field_0,
            class_name: __wire_field_1,
            priority: __wire_field_2,
            type_: __wire_field_3,
            value: __wire_field_4,
        } = self;
        Ok(WKernelInstanceInfo {
            name: __wire_field_0.to_wire(p)?,
            class_name: __wire_field_1.to_wire(p)?,
            priority: __wire_field_2.to_wire(p)?,
            type_: __wire_field_3.to_wire(p)?,
            value: __wire_field_4.to_wire(p)?,
        })
    }
}
impl FromWire<WKernelInstanceInfo> for SKernelInstanceInfo {
    fn from_wire(wire: WKernelInstanceInfo, r: &mut Restoration) -> Result<Self> {
        let WKernelInstanceInfo {
            name: __wire_field_0,
            class_name: __wire_field_1,
            priority: __wire_field_2,
            type_: __wire_field_3,
            value: __wire_field_4,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            class_name: FromWire::from_wire(__wire_field_1, r)?,
            priority: FromWire::from_wire(__wire_field_2, r)?,
            type_: FromWire::from_wire(__wire_field_3, r)?,
            value: FromWire::from_wire(__wire_field_4, r)?,
        })
    }
}
