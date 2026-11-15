// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::types::KernelClassInfo as SKernelClassInfo;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WKernelClassInfo {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) num_params: usize,
    pub(in crate::env::dag_serialization) out_params: Vec<usize>,
    pub(in crate::env::dag_serialization) semi_out_params: Vec<usize>,
}
impl Wire for WKernelClassInfo {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            num_params: <usize as Wire>::read(r)?,
            out_params: <Vec<usize> as Wire>::read(r)?,
            semi_out_params: <Vec<usize> as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.num_params.write(w)?;
        self.out_params.write(w)?;
        self.semi_out_params.write(w)?;
        Ok(())
    }
}
impl ToWire for SKernelClassInfo {
    type Wire = WKernelClassInfo;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SKernelClassInfo {
            name: __wire_field_0,
            num_params: __wire_field_1,
            out_params: __wire_field_2,
            semi_out_params: __wire_field_3,
        } = self;
        Ok(WKernelClassInfo {
            name: __wire_field_0.to_wire(p)?,
            num_params: __wire_field_1.to_wire(p)?,
            out_params: __wire_field_2.to_wire(p)?,
            semi_out_params: __wire_field_3.to_wire(p)?,
        })
    }
}
impl FromWire<WKernelClassInfo> for SKernelClassInfo {
    fn from_wire(wire: WKernelClassInfo, r: &mut Restoration) -> Result<Self> {
        let WKernelClassInfo {
            name: __wire_field_0,
            num_params: __wire_field_1,
            out_params: __wire_field_2,
            semi_out_params: __wire_field_3,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            num_params: FromWire::from_wire(__wire_field_1, r)?,
            out_params: FromWire::from_wire(__wire_field_2, r)?,
            semi_out_params: FromWire::from_wire(__wire_field_3, r)?,
        })
    }
}
