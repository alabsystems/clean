// Copyright 2026 Andrew Yates | Apache-2.0
//! Full explicit epoch DTOs. The fixed list is not live serde reflection.
use super::containers::*;
use super::graph::{Projection, Ref, Restoration};
use super::primitive::*;
use super::syntax::*;
use super::types::*;
use crate::env::Environment;

macro_rules! environment_schema {
    (before { $($pre:ident: $pt:ty => $pb:ident,)* }
     after { $($post:ident: $at:ty => $ab:ident,)* }
     transient { $($skip:ident => $sb:ident),* }) => {
        #[derive(Debug,PartialEq,Eq)]
        pub(super) struct WireEnvironment {
            $($pre:$pt,)*
            lean_level_profile:WLeanLevelProfile,
            $($post:$at,)*
        }
        #[derive(Debug,PartialEq,Eq)]
        pub(super) struct Legacy3faEnvironment { $($pre:$pt,)* $($post:$at,)* }
        #[derive(Debug,PartialEq,Eq)]
        pub(super) struct LegacyC4Environment {
            $($pre:$pt,)*
            lean_level_profile:WLeanLevelProfile,
            $($post:$at,)*
        }
        impl Wire for WireEnvironment {
            fn read(r:&mut Decoder<'_>)->Result<Self> {
                Ok(Self { $($pre:<$pt as Wire>::read(r)?,)*
                    lean_level_profile:WLeanLevelProfile::read(r)?,
                    $($post:<$at as Wire>::read(r)?,)* })
            }
            fn write(&self,w:&mut Encoder)->Result<()> {
                $(self.$pre.write(w)?;)*
                self.lean_level_profile.write(w)?;
                $(self.$post.write(w)?;)*
                Ok(())
            }
        }
        impl Wire for Legacy3faEnvironment {
            fn read(r:&mut Decoder<'_>)->Result<Self> {
                Ok(Self { $($pre:<$pt as Wire>::read(r)?,)* $($post:<$at as Wire>::read(r)?,)* })
            }
            fn write(&self,w:&mut Encoder)->Result<()> {
                $(self.$pre.write(w)?;)* $(self.$post.write(w)?;)* Ok(())
            }
        }
        impl Wire for LegacyC4Environment {
            fn read(r:&mut Decoder<'_>)->Result<Self> {
                Ok(Self { $($pre:<$pt as Wire>::read(r)?,)*
                    lean_level_profile:WLeanLevelProfile::read(r)?,
                    $($post:<$at as Wire>::read(r)?,)* })
            }
            fn write(&self,w:&mut Encoder)->Result<()> {
                $(self.$pre.write(w)?;)* self.lean_level_profile.write(w)?;
                $(self.$post.write(w)?;)* Ok(())
            }
        }
        impl Legacy3faEnvironment {
            pub(super) fn into_current(self)->WireEnvironment {
                let Self { $($pre:$pb,)* $($post:$ab,)* }=self;
                // Original 3fa's universe constructor algorithm is the
                // currently named Lean430 algebra, not the Lean48 choice.
                WireEnvironment { $($pre:$pb,)* lean_level_profile:WLeanLevelProfile::Lean430, $($post:$ab,)* }
            }
        }
        impl LegacyC4Environment {
            pub(super) fn into_current(self)->WireEnvironment {
                let Self { $($pre:$pb,)* lean_level_profile:__wire_env_profile, $($post:$ab,)* }=self;
                WireEnvironment { $($pre:$pb,)* lean_level_profile:__wire_env_profile, $($post:$ab,)* }
            }
        }
        impl ToWire for Environment {
            type Wire=WireEnvironment;
            fn to_wire(&self,p:&mut Projection)->Result<Self::Wire> {
                // All source fields, including deliberate transients, occur
                // in this pattern without `..`: a new field must be decided.
                let Self { $($pre:$pb,)* lean_level_profile:__wire_env_profile, $($post:$ab,)* $($skip:$sb,)* }=self;
                let _=($($sb,)*);
                Ok(WireEnvironment {
                    $($pre:$pb.to_wire(p)?,)*
                    lean_level_profile:__wire_env_profile.to_wire(p)?,
                    $($post:$ab.to_wire(p)?,)*
                })
            }
        }
        impl FromWire<WireEnvironment> for Environment {
            fn from_wire(wire:WireEnvironment,r:&mut Restoration)->Result<Self> {
                let WireEnvironment { $($pre:$pb,)* lean_level_profile:__wire_env_profile, $($post:$ab,)* }=wire;
                let mut environment=Self {
                    $($pre:FromWire::from_wire($pb,r)?,)*
                    lean_level_profile:FromWire::from_wire(__wire_env_profile,r)?,
                    $($post:FromWire::from_wire($ab,r)?,)*
                    $($skip:Default::default(),)*
                };
                // Transients restart at their defaults; the matcher index is
                // derived from persisted fields, so it is re-derived from them.
                environment.rebuild_matcher_index();
                Ok(environment)
            }
        }
    };
}

include!("environment_fields.rs");

#[cfg(test)]
impl Legacy3faEnvironment {
    pub(super) fn declaration_counts(&self) -> [usize; 5] {
        [
            self.constants.0.len(),
            self.inductives.0.len(),
            self.constructors.0.len(),
            self.recursors.0.len(),
            self.quotients.0.len(),
        ]
    }
}

#[cfg(test)]
#[path = "tests_boolean.rs"]
mod tests_boolean;
