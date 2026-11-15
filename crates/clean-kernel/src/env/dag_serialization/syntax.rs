// Copyright 2026 Andrew Yates | Apache-2.0
//! Frozen recursive atoms; no dotted-name, level or literal normalization.
use super::containers::{FromWire, ToWire};
use super::error;
use super::graph::{Projection, Restoration};
use super::primitive::{Decoder, Encoder, Result, Wire};
use crate::expr::{FVarId, LevelVec};
use crate::level::{level_arc, LevelArc};
use crate::name::NameInner;
use crate::{Level, Name};

#[derive(Debug, PartialEq, Eq)]
pub(super) enum WName {
    Anon,
    Str(Box<WName>, String),
    Num(Box<WName>, u64),
}
impl Wire for WName {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.atom(|r| match r.u32()? {
            0 => Ok(Self::Anon),
            1 => Ok(Self::Str(Box::read(r)?, String::read(r)?)),
            2 => Ok(Self::Num(Box::read(r)?, u64::read(r)?)),
            _ => Err(error("unknown Name tag")),
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Anon => w.u32(0),
            Self::Str(parent, value) => {
                w.u32(1)?;
                parent.write(w)?;
                value.write(w)
            }
            Self::Num(parent, value) => {
                w.u32(2)?;
                parent.write(w)?;
                value.write(w)
            }
        }
    }
}
impl ToWire for Name {
    type Wire = WName;
    fn to_wire(&self, p: &mut Projection) -> Result<WName> {
        p.atom(|p| match self.dag_wire_inner() {
            NameInner::Anon => Ok(WName::Anon),
            NameInner::Str(parent, value) => {
                p.allocate(1, size_of::<WName>())?;
                p.allocate(value.len(), 1)?;
                let parent: &Name = parent;
                Ok(WName::Str(Box::new(parent.to_wire(p)?), value.to_string()))
            }
            NameInner::Num(parent, value) => {
                p.allocate(1, size_of::<WName>())?;
                let parent: &Name = parent;
                Ok(WName::Num(Box::new(parent.to_wire(p)?), *value))
            }
        })
    }
}
impl FromWire<WName> for Name {
    fn from_wire(wire: WName, r: &mut Restoration) -> Result<Self> {
        r.atom(|r| match wire {
            WName::Anon => Ok(Self::anon()),
            WName::Str(parent, value) => {
                r.allocate(value.len(), 1)?;
                r.allocate(1, size_of::<Name>().saturating_add(64))?;
                Ok(Self::from_wire(*parent, r)?.str(value))
            }
            WName::Num(parent, value) => {
                r.allocate(1, size_of::<Name>().saturating_add(32))?;
                Ok(Self::from_wire(*parent, r)?.num(value))
            }
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum WLevel {
    Zero,
    Succ(Box<WLevel>),
    Max(Box<WLevel>, Box<WLevel>),
    IMax(Box<WLevel>, Box<WLevel>),
    Param(WName),
}
impl Wire for WLevel {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        r.atom(|r| match r.u32()? {
            0 => Ok(Self::Zero),
            1 => Ok(Self::Succ(Box::read(r)?)),
            2 => Ok(Self::Max(Box::read(r)?, Box::read(r)?)),
            3 => Ok(Self::IMax(Box::read(r)?, Box::read(r)?)),
            4 => Ok(Self::Param(WName::read(r)?)),
            _ => Err(error("unknown Level tag")),
        })
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        match self {
            Self::Zero => w.u32(0),
            Self::Succ(v) => {
                w.u32(1)?;
                v.write(w)
            }
            Self::Max(a, b) => {
                w.u32(2)?;
                a.write(w)?;
                b.write(w)
            }
            Self::IMax(a, b) => {
                w.u32(3)?;
                a.write(w)?;
                b.write(w)
            }
            Self::Param(v) => {
                w.u32(4)?;
                v.write(w)
            }
        }
    }
}
impl ToWire for LevelArc {
    type Wire = Box<WLevel>;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        p.allocate(1, size_of::<WLevel>())?;
        Ok(Box::new((**self).to_wire(p)?))
    }
}
impl ToWire for Level {
    type Wire = WLevel;
    fn to_wire(&self, p: &mut Projection) -> Result<WLevel> {
        p.atom(|p| match self {
            Self::Zero => Ok(WLevel::Zero),
            Self::Succ(v) => Ok(WLevel::Succ(v.to_wire(p)?)),
            Self::Max(a, b) => Ok(WLevel::Max(a.to_wire(p)?, b.to_wire(p)?)),
            Self::IMax(a, b) => Ok(WLevel::IMax(a.to_wire(p)?, b.to_wire(p)?)),
            Self::Param(v) => Ok(WLevel::Param(v.to_wire(p)?)),
        })
    }
}
impl FromWire<Box<WLevel>> for LevelArc {
    fn from_wire(wire: Box<WLevel>, r: &mut Restoration) -> Result<Self> {
        r.allocate(1, size_of::<Level>().saturating_add(32))?;
        Ok(level_arc(Level::from_wire(*wire, r)?))
    }
}
impl FromWire<WLevel> for Level {
    fn from_wire(wire: WLevel, r: &mut Restoration) -> Result<Self> {
        r.atom(|r| match wire {
            WLevel::Zero => Ok(Self::Zero),
            WLevel::Succ(v) => Ok(Self::Succ(FromWire::from_wire(v, r)?)),
            WLevel::Max(a, b) => Ok(Self::Max(
                FromWire::from_wire(a, r)?,
                FromWire::from_wire(b, r)?,
            )),
            WLevel::IMax(a, b) => Ok(Self::IMax(
                FromWire::from_wire(a, r)?,
                FromWire::from_wire(b, r)?,
            )),
            WLevel::Param(v) => Ok(Self::Param(Name::from_wire(v, r)?)),
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct WFVarId(u64);
impl Wire for WFVarId {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self(r.u64()?))
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.u64(self.0)
    }
}
impl ToWire for FVarId {
    type Wire = WFVarId;
    fn to_wire(&self, _: &mut Projection) -> Result<WFVarId> {
        let Self(value) = self;
        Ok(WFVarId(*value))
    }
}
impl FromWire<WFVarId> for FVarId {
    fn from_wire(wire: WFVarId, _: &mut Restoration) -> Result<Self> {
        Ok(Self(wire.0))
    }
}
impl ToWire for LevelVec {
    type Wire = Vec<WLevel>;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        p.allocate(self.len(), size_of::<WLevel>())?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(self.len())
            .map_err(|_| error("level vector allocation refused"))?;
        for level in self {
            result.push(level.to_wire(p)?);
        }
        Ok(result)
    }
}
impl FromWire<Vec<WLevel>> for LevelVec {
    fn from_wire(wire: Vec<WLevel>, r: &mut Restoration) -> Result<Self> {
        r.allocate(wire.len(), size_of::<Level>())?;
        let mut result = Self::new();
        result
            .try_reserve(wire.len())
            .map_err(|_| error("level vector allocation refused"))?;
        for level in wire {
            result.push(Level::from_wire(level, r)?);
        }
        Ok(result)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Unit;
impl Wire for Unit {
    fn read(_: &mut Decoder<'_>) -> Result<Self> {
        Ok(Self)
    }
    fn write(&self, _: &mut Encoder) -> Result<()> {
        Ok(())
    }
}
impl ToWire for super::super::persistent_ext::EnvExtensionStates {
    type Wire = Unit;
    fn to_wire(&self, _: &mut Projection) -> Result<Unit> {
        self.dag_wire_unit();
        Ok(Unit)
    }
}
impl FromWire<Unit> for super::super::persistent_ext::EnvExtensionStates {
    fn from_wire(_: Unit, _: &mut Restoration) -> Result<Self> {
        Ok(Self::new())
    }
}
