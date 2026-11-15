// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::aesop::AesopRuleSet as SAesopRuleSet;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) struct WAesopRuleSet {
    pub(in crate::env::dag_serialization) safe_rules: Vec<WAesopRule>,
    pub(in crate::env::dag_serialization) unsafe_rules: Vec<WAesopRule>,
    pub(in crate::env::dag_serialization) norm_rules: Vec<WAesopRule>,
    pub(in crate::env::dag_serialization) priority_overrides: Map<WName, u32>,
}
impl Wire for WAesopRuleSet {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self {
            safe_rules: <Vec<WAesopRule> as Wire>::read(r)?,
            unsafe_rules: <Vec<WAesopRule> as Wire>::read(r)?,
            norm_rules: <Vec<WAesopRule> as Wire>::read(r)?,
            priority_overrides: <Map<WName, u32> as Wire>::read(r)?,
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        self.safe_rules.write(w)?;
        self.unsafe_rules.write(w)?;
        self.norm_rules.write(w)?;
        self.priority_overrides.write(w)?;
        Ok(())
    }
}
impl ToWire for SAesopRuleSet {
    type Wire = WAesopRuleSet;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        let SAesopRuleSet {
            safe_rules: __wire_field_0,
            unsafe_rules: __wire_field_1,
            norm_rules: __wire_field_2,
            priority_overrides: __wire_field_3,
        } = self;
        Ok(WAesopRuleSet {
            safe_rules: __wire_field_0.to_wire(p)?,
            unsafe_rules: __wire_field_1.to_wire(p)?,
            norm_rules: __wire_field_2.to_wire(p)?,
            priority_overrides: __wire_field_3.to_wire(p)?,
        })
    }
}
impl FromWire<WAesopRuleSet> for SAesopRuleSet {
    fn from_wire(wire: WAesopRuleSet, r: &mut Restoration) -> Result<Self> {
        let WAesopRuleSet {
            safe_rules: __wire_field_0,
            unsafe_rules: __wire_field_1,
            norm_rules: __wire_field_2,
            priority_overrides: __wire_field_3,
        } = wire;
        Ok(Self {
            safe_rules: FromWire::from_wire(__wire_field_0, r)?,
            unsafe_rules: FromWire::from_wire(__wire_field_1, r)?,
            norm_rules: FromWire::from_wire(__wire_field_2, r)?,
            priority_overrides: FromWire::from_wire(__wire_field_3, r)?,
        })
    }
}
