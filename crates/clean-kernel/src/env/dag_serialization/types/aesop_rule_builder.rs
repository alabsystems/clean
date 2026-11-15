// Copyright 2026 Andrew Yates | Apache-2.0
// Generated from the frozen schema_v2.json; do not infer live serde.
use super::*;
use crate::env::aesop::AesopRuleBuilder as SAesopRuleBuilder;
#[derive(Debug, PartialEq, Eq)]
pub(in crate::env::dag_serialization) enum WAesopRuleBuilder {
    Apply,
    Cases,
    Constructors,
    Destruct,
    Forward,
    Simp,
    Tactic,
    Unfold,
}
impl Wire for WAesopRuleBuilder {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        match r.u32()? {
            0 => Ok(Self::Apply),
            1 => Ok(Self::Cases),
            2 => Ok(Self::Constructors),
            3 => Ok(Self::Destruct),
            4 => Ok(Self::Forward),
            5 => Ok(Self::Simp),
            6 => Ok(Self::Tactic),
            7 => Ok(Self::Unfold),
            _ => Err(error("unknown WAesopRuleBuilder tag")),
        }
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Apply => {
                w.u32(0)?;
                Ok(())
            }
            Self::Cases => {
                w.u32(1)?;
                Ok(())
            }
            Self::Constructors => {
                w.u32(2)?;
                Ok(())
            }
            Self::Destruct => {
                w.u32(3)?;
                Ok(())
            }
            Self::Forward => {
                w.u32(4)?;
                Ok(())
            }
            Self::Simp => {
                w.u32(5)?;
                Ok(())
            }
            Self::Tactic => {
                w.u32(6)?;
                Ok(())
            }
            Self::Unfold => {
                w.u32(7)?;
                Ok(())
            }
        }
    }
}
impl ToWire for SAesopRuleBuilder {
    type Wire = WAesopRuleBuilder;
    fn to_wire(&self, _p: &mut Projection) -> Result<Self::Wire> {
        match self {
            SAesopRuleBuilder::Apply => Ok(WAesopRuleBuilder::Apply),
            SAesopRuleBuilder::Cases => Ok(WAesopRuleBuilder::Cases),
            SAesopRuleBuilder::Constructors => Ok(WAesopRuleBuilder::Constructors),
            SAesopRuleBuilder::Destruct => Ok(WAesopRuleBuilder::Destruct),
            SAesopRuleBuilder::Forward => Ok(WAesopRuleBuilder::Forward),
            SAesopRuleBuilder::Simp => Ok(WAesopRuleBuilder::Simp),
            SAesopRuleBuilder::Tactic => Ok(WAesopRuleBuilder::Tactic),
            SAesopRuleBuilder::Unfold => Ok(WAesopRuleBuilder::Unfold),
        }
    }
}
impl FromWire<WAesopRuleBuilder> for SAesopRuleBuilder {
    fn from_wire(wire: WAesopRuleBuilder, _r: &mut Restoration) -> Result<Self> {
        match wire {
            WAesopRuleBuilder::Apply => Ok(Self::Apply),
            WAesopRuleBuilder::Cases => Ok(Self::Cases),
            WAesopRuleBuilder::Constructors => Ok(Self::Constructors),
            WAesopRuleBuilder::Destruct => Ok(Self::Destruct),
            WAesopRuleBuilder::Forward => Ok(Self::Forward),
            WAesopRuleBuilder::Simp => Ok(Self::Simp),
            WAesopRuleBuilder::Tactic => Ok(Self::Tactic),
            WAesopRuleBuilder::Unfold => Ok(Self::Unfold),
        }
    }
}
