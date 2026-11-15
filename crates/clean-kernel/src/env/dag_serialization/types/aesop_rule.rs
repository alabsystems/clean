// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::aesop::AesopRule as SAesopRule;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WAesopRule {
    pub(in crate::env::dag_serialization) name: WName,
    pub(in crate::env::dag_serialization) phase: WAesopRulePhase,
    pub(in crate::env::dag_serialization) builder: WAesopRuleBuilder,
    pub(in crate::env::dag_serialization) builder_args: Vec<WName>,
    pub(in crate::env::dag_serialization) priority: u32,
    pub(in crate::env::dag_serialization) index_mode: WAesopIndexMode,
    pub(in crate::env::dag_serialization) transparency: WTransparencyMode,
}
impl Wire for WAesopRule {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            name: <WName as Wire>::read(r)?,
            phase: <WAesopRulePhase as Wire>::read(r)?,
            builder: <WAesopRuleBuilder as Wire>::read(r)?,
            builder_args: <Vec<WName> as Wire>::read(r)?,
            priority: <u32 as Wire>::read(r)?,
            index_mode: <WAesopIndexMode as Wire>::read(r)?,
            transparency: <WTransparencyMode as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.name.write(w)?;
        self.phase.write(w)?;
        self.builder.write(w)?;
        self.builder_args.write(w)?;
        self.priority.write(w)?;
        self.index_mode.write(w)?;
        self.transparency.write(w)?;
        Ok(())
    }
}
impl ToWire for SAesopRule {
    type Wire = WAesopRule;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SAesopRule {
            name: __wire_field_0,
            phase: __wire_field_1,
            builder: __wire_field_2,
            builder_args: __wire_field_3,
            priority: __wire_field_4,
            index_mode: __wire_field_5,
            transparency: __wire_field_6,
        } = self;
        Ok(WAesopRule {
            name: __wire_field_0.to_wire(p)?,
            phase: __wire_field_1.to_wire(p)?,
            builder: __wire_field_2.to_wire(p)?,
            builder_args: __wire_field_3.to_wire(p)?,
            priority: __wire_field_4.to_wire(p)?,
            index_mode: __wire_field_5.to_wire(p)?,
            transparency: __wire_field_6.to_wire(p)?,
        })
    }
}
impl FromWire<WAesopRule> for SAesopRule {
    fn from_wire(wire: WAesopRule, r: &mut Restoration) -> Result<Self> {
        let WAesopRule {
            name: __wire_field_0,
            phase: __wire_field_1,
            builder: __wire_field_2,
            builder_args: __wire_field_3,
            priority: __wire_field_4,
            index_mode: __wire_field_5,
            transparency: __wire_field_6,
        } = wire;
        Ok(Self {
            name: FromWire::from_wire(__wire_field_0, r)?,
            phase: FromWire::from_wire(__wire_field_1, r)?,
            builder: FromWire::from_wire(__wire_field_2, r)?,
            builder_args: FromWire::from_wire(__wire_field_3, r)?,
            priority: FromWire::from_wire(__wire_field_4, r)?,
            index_mode: FromWire::from_wire(__wire_field_5, r)?,
            transparency: FromWire::from_wire(__wire_field_6, r)?,
        })
    }
}
