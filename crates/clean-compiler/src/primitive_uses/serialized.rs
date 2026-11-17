// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Finite preflight for the maintained TrustIR module's derived serde visitor.
//! No bytes, parser, lowering or permission classification are produced here.
use super::{measure::Meter, ObservationGap};
use serde::ser::{self, Serialize};

#[derive(Debug, thiserror::Error)]
#[error("observation preflight incomplete")]
pub(super) struct Error(pub ObservationGap);
impl ser::Error for Error {
    fn custom<T: std::fmt::Display>(_: T) -> Self {
        Self(ObservationGap::Unobserved {
            owner: "module retention",
            reason: "serde visitor refused",
        })
    }
}
pub(super) struct Visitor<'a> {
    meter: &'a mut Meter,
    depth: usize,
}
impl Meter {
    pub(super) fn serialized<T: Serialize>(&mut self, value: &T) -> Result<(), ObservationGap> {
        self.add(size_of::<T>().saturating_mul(2))?;
        value
            .serialize(Visitor {
                meter: self,
                depth: 0,
            })
            .map_err(|error| error.0)
    }
}
impl Visitor<'_> {
    fn node(&mut self, bytes: usize) -> Result<(), Error> {
        self.meter.check_depth(self.depth).map_err(Error)?;
        self.meter.add(bytes).map_err(Error)
    }
    fn child<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        // Reserve traversal and structural storage BEFORE invoking a child.
        self.node(size_of_val(value).saturating_mul(2).saturating_add(32))?;
        value.serialize(Visitor {
            meter: self.meter,
            depth: self.depth + 1,
        })
    }
}
macro_rules! primitive { ($($method:ident($ty:ty)),*) => {$ (
    fn $method(mut self, _: $ty) -> Result<(), Error> { self.node(32) }
)*}; }
impl<'a> ser::Serializer for Visitor<'a> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;
    primitive!(
        serialize_bool(bool),
        serialize_i8(i8),
        serialize_i16(i16),
        serialize_i32(i32),
        serialize_i64(i64),
        serialize_i128(i128),
        serialize_u8(u8),
        serialize_u16(u16),
        serialize_u32(u32),
        serialize_u64(u64),
        serialize_u128(u128),
        serialize_f32(f32),
        serialize_f64(f64),
        serialize_char(char)
    );
    fn serialize_str(mut self, value: &str) -> Result<(), Error> {
        self.node(value.len().saturating_mul(2).saturating_add(32))
    }
    fn serialize_bytes(mut self, value: &[u8]) -> Result<(), Error> {
        self.node(value.len().saturating_mul(2).saturating_add(32))
    }
    fn serialize_none(mut self) -> Result<(), Error> {
        self.node(32)
    }
    fn serialize_some<T: ?Sized + Serialize>(mut self, value: &T) -> Result<(), Error> {
        self.child(value)
    }
    fn serialize_unit(mut self) -> Result<(), Error> {
        self.node(32)
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<(), Error> {
        self.serialize_unit()
    }
    fn serialize_unit_variant(self, _: &'static str, _: u32, _: &'static str) -> Result<(), Error> {
        self.serialize_unit()
    }
    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        mut self,
        _: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.child(value)
    }
    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        mut self,
        _: &'static str,
        _: u32,
        _: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.child(value)
    }
    fn serialize_seq(mut self, _: Option<usize>) -> Result<Self, Error> {
        self.node(64)?;
        Ok(self)
    }
    fn serialize_tuple(self, _: usize) -> Result<Self, Error> {
        self.serialize_seq(None)
    }
    fn serialize_tuple_struct(self, _: &'static str, _: usize) -> Result<Self, Error> {
        self.serialize_seq(None)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        self.serialize_seq(None)
    }
    fn serialize_map(self, _: Option<usize>) -> Result<Self, Error> {
        self.serialize_seq(None)
    }
    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self, Error> {
        self.serialize_seq(None)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        self.serialize_seq(None)
    }
    fn collect_str<T: ?Sized + std::fmt::Display>(self, _: &T) -> Result<(), Error> {
        Err(Error(ObservationGap::Unobserved {
            owner: "module retention",
            reason: "unbounded Display serializer is not visited",
        }))
    }
}
macro_rules! compound { ($trait:ident,$method:ident $(,$arg:ident : $ty:ty)*) => {
    impl ser::$trait for Visitor<'_> {
        type Ok = (); type Error = Error;
        fn $method<T: ?Sized + Serialize>(&mut self, $($arg:$ty,)* value: &T) -> Result<(), Error> { $(let _ = $arg;)* self.child(value) }
        fn end(self) -> Result<(), Error> { Ok(()) }
    }
}; }
compound!(SerializeSeq, serialize_element);
compound!(SerializeTuple, serialize_element);
compound!(SerializeTupleStruct, serialize_field);
compound!(SerializeTupleVariant, serialize_field);
compound!(SerializeStruct, serialize_field, key: &'static str);
compound!(SerializeStructVariant, serialize_field, key: &'static str);
impl ser::SerializeMap for Visitor<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.child(value)
    }
    fn serialize_value<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.child(value)
    }
    fn end(self) -> Result<(), Error> {
        Ok(())
    }
}
