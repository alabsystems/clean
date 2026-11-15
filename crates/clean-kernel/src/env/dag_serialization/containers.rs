// Copyright 2026 Andrew Yates | Apache-2.0
//! Frozen container shapes and exhaustive live-type conversion contracts.
use super::graph::{Projection, Restoration};
use super::primitive::{Decoder, Encoder, Encoding, Result, Wire};
use super::{error, syntax::WName};
use std::collections::BTreeSet;
use std::hash::Hash;
use std::sync::Arc;

pub(super) trait ToWire {
    type Wire: Wire;
    fn to_wire(&self, projection: &mut Projection) -> Result<Self::Wire>;
}
pub(super) trait FromWire<W>: Sized {
    fn from_wire(wire: W, restoration: &mut Restoration) -> Result<Self>;
}

/// Only these fixed key types may be projected before value/Expr discovery.
pub(super) trait Key: Wire {}
impl Key for WName {}
impl Key for String {}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Map<K, V>(pub(super) Vec<(K, V)>);
#[derive(Debug, PartialEq, Eq)]
pub(super) struct Set<K>(pub(super) Vec<K>);

fn key_bytes<K: Wire>(key: &K, available: usize) -> Result<Vec<u8>> {
    let mut encoder = Encoder::bounded(Encoding::V2, available);
    key.write(&mut encoder)?;
    Ok(encoder.finish())
}
fn unique_key<K: Key>(
    r: &mut Decoder<'_>,
    key: &K,
    seen: &mut BTreeSet<Vec<u8>>,
) -> Result<Vec<u8>> {
    let available = r.budget.remaining().saturating_sub(64) / 2;
    let bytes = key_bytes(key, available)?;
    r.budget.allocate(
        bytes
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(64))
            .ok_or_else(|| error("key size overflow"))?,
        1,
    )?;
    if !seen.insert(bytes.clone()) {
        return Err(error("duplicate map/set key"));
    }
    Ok(bytes)
}
impl<K: Key, V: Wire> Wire for Map<K, V> {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        let len = r.len()?;
        r.budget.can_allocate(len, size_of::<(K, V)>().max(1))?;
        let mut values = Vec::new();
        let mut accounted = 0;
        let mut seen = BTreeSet::new();
        let mut previous: Option<Vec<u8>> = None;
        for _ in 0..len {
            let key = K::read(r)?;
            let value = V::read(r)?;
            let bytes = unique_key(r, &key, &mut seen)?;
            if r.encoding == Encoding::V2 && previous.as_ref().is_some_and(|p| p >= &bytes) {
                return Err(error("noncanonical map key order"));
            }
            previous = Some(bytes);
            r.push(&mut values, &mut accounted, (key, value), len)?;
        }
        Ok(Self(values))
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.len(self.0.len())?;
        // Projection canonicalizes before discovering expression IDs. Legacy
        // DTOs retain original entry order for exact grammar roundtrips.
        for (key, value) in &self.0 {
            key.write(w)?;
            value.write(w)?;
        }
        Ok(())
    }
}
impl<K: Key> Wire for Set<K> {
    fn read(r: &mut Decoder<'_>) -> Result<Self> {
        let len = r.len()?;
        r.budget.can_allocate(len, size_of::<K>().max(1))?;
        let mut values = Vec::new();
        let mut accounted = 0;
        let mut seen = BTreeSet::new();
        let mut previous: Option<Vec<u8>> = None;
        for _ in 0..len {
            let key = K::read(r)?;
            let bytes = unique_key(r, &key, &mut seen)?;
            if r.encoding == Encoding::V2 && previous.as_ref().is_some_and(|p| p >= &bytes) {
                return Err(error("noncanonical set key order"));
            }
            previous = Some(bytes);
            r.push(&mut values, &mut accounted, key, len)?;
        }
        Ok(Self(values))
    }
    fn write(&self, w: &mut Encoder) -> Result<()> {
        w.len(self.0.len())?;
        for key in &self.0 {
            key.write(w)?;
        }
        Ok(())
    }
}

macro_rules! scalar {
    ($($ty:ty),* $(,)?) => { $(
        impl ToWire for $ty {
            type Wire = Self;
            fn to_wire(&self, _: &mut Projection) -> Result<Self> { Ok(*self) }
        }
        impl FromWire<$ty> for $ty {
            fn from_wire(wire: $ty, _: &mut Restoration) -> Result<Self> { Ok(wire) }
        }
    )* };
}
scalar!(bool, u8, u32, u64, usize);
impl ToWire for String {
    type Wire = Self;
    fn to_wire(&self, p: &mut Projection) -> Result<Self> {
        p.allocate(self.len(), 1)?;
        Ok(self.clone())
    }
}
impl FromWire<String> for String {
    fn from_wire(wire: String, _: &mut Restoration) -> Result<Self> {
        Ok(wire)
    }
}
impl ToWire for Arc<str> {
    type Wire = String;
    fn to_wire(&self, p: &mut Projection) -> Result<String> {
        p.allocate(self.len(), 1)?;
        Ok(self.to_string())
    }
}
impl FromWire<String> for Arc<str> {
    fn from_wire(wire: String, r: &mut Restoration) -> Result<Self> {
        r.allocate(
            wire.len()
                .checked_add(32)
                .ok_or_else(|| error("string size overflow"))?,
            1,
        )?;
        Ok(wire.into())
    }
}
impl<T: ToWire> ToWire for Option<T> {
    type Wire = Option<T::Wire>;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        self.as_ref().map(|v| v.to_wire(p)).transpose()
    }
}
impl<T: FromWire<W>, W> FromWire<Option<W>> for Option<T> {
    fn from_wire(wire: Option<W>, r: &mut Restoration) -> Result<Self> {
        wire.map(|v| T::from_wire(v, r)).transpose()
    }
}
impl<T: ToWire> ToWire for Vec<T> {
    type Wire = Vec<T::Wire>;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        p.allocate(self.len(), size_of::<T::Wire>().max(1))?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(self.len())
            .map_err(|_| error("projection allocation refused"))?;
        for value in self {
            values.push(value.to_wire(p)?);
        }
        Ok(values)
    }
}
impl<T: FromWire<W>, W> FromWire<Vec<W>> for Vec<T> {
    fn from_wire(wire: Vec<W>, r: &mut Restoration) -> Result<Self> {
        r.allocate(wire.len(), size_of::<T>().max(1))?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(wire.len())
            .map_err(|_| error("restoration allocation refused"))?;
        for value in wire {
            values.push(T::from_wire(value, r)?);
        }
        Ok(values)
    }
}
impl<A: ToWire, B: ToWire> ToWire for (A, B) {
    type Wire = (A::Wire, B::Wire);
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        Ok((self.0.to_wire(p)?, self.1.to_wire(p)?))
    }
}
impl<A: FromWire<X>, B: FromWire<Y>, X, Y> FromWire<(X, Y)> for (A, B) {
    fn from_wire(wire: (X, Y), r: &mut Restoration) -> Result<Self> {
        Ok((A::from_wire(wire.0, r)?, B::from_wire(wire.1, r)?))
    }
}
impl<K, V> ToWire for hashbrown::HashMap<K, V>
where
    K: ToWire + Eq + Hash,
    K::Wire: Key,
    V: ToWire,
{
    type Wire = Map<K::Wire, V::Wire>;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        // Keys cannot contain Expr references. Sort BEFORE projecting values:
        // sorting the final map after graph discovery would be insufficient.
        p.allocate(self.len(), size_of::<(K::Wire, Vec<u8>, &V)>())?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(self.len())
            .map_err(|_| error("map projection allocation refused"))?;
        for (key, value) in self {
            let key = key.to_wire(p)?;
            let bytes = key_bytes(&key, p.remaining())?;
            p.allocate(bytes.len(), 1)?;
            pending.push((key, bytes, value));
        }
        pending.sort_unstable_by(|a, b| a.1.cmp(&b.1));
        p.allocate(self.len(), size_of::<(K::Wire, V::Wire)>())?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(self.len())
            .map_err(|_| error("map projection allocation refused"))?;
        for (key, _, value) in pending {
            values.push((key, value.to_wire(p)?));
        }
        Ok(Map(values))
    }
}
impl<K, V, WK, WV> FromWire<Map<WK, WV>> for hashbrown::HashMap<K, V>
where
    K: FromWire<WK> + Eq + Hash,
    V: FromWire<WV>,
{
    fn from_wire(wire: Map<WK, WV>, r: &mut Restoration) -> Result<Self> {
        r.allocate(
            wire.0.len(),
            size_of::<(K, V)>()
                .checked_add(32)
                .ok_or_else(|| error("map size overflow"))?,
        )?;
        let mut values = Self::new();
        values
            .try_reserve(wire.0.len())
            .map_err(|_| error("map restoration allocation refused"))?;
        for (key, value) in wire.0 {
            let key = K::from_wire(key, r)?;
            let value = V::from_wire(value, r)?;
            if values.insert(key, value).is_some() {
                return Err(error("duplicate restored map key"));
            }
        }
        Ok(values)
    }
}
impl<K> ToWire for hashbrown::HashSet<K>
where
    K: ToWire + Eq + Hash,
    K::Wire: Key,
{
    type Wire = Set<K::Wire>;
    fn to_wire(&self, p: &mut Projection) -> Result<Self::Wire> {
        p.allocate(self.len(), size_of::<(K::Wire, Vec<u8>)>())?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(self.len())
            .map_err(|_| error("set projection allocation refused"))?;
        for value in self {
            let v = value.to_wire(p)?;
            let key = key_bytes(&v, p.remaining())?;
            p.allocate(key.len(), 1)?;
            pending.push((v, key));
        }
        pending.sort_unstable_by(|a, b| a.1.cmp(&b.1));
        p.allocate(self.len(), size_of::<K::Wire>().max(1))?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(self.len())
            .map_err(|_| error("set projection allocation refused"))?;
        for (value, _) in pending {
            values.push(value);
        }
        Ok(Set(values))
    }
}
impl<K, WK> FromWire<Set<WK>> for hashbrown::HashSet<K>
where
    K: FromWire<WK> + Eq + Hash,
{
    fn from_wire(wire: Set<WK>, r: &mut Restoration) -> Result<Self> {
        r.allocate(
            wire.0.len(),
            size_of::<K>()
                .checked_add(32)
                .ok_or_else(|| error("set size overflow"))?,
        )?;
        let mut values = Self::new();
        values
            .try_reserve(wire.0.len())
            .map_err(|_| error("set restoration allocation refused"))?;
        for value in wire.0 {
            if !values.insert(K::from_wire(value, r)?) {
                return Err(error("duplicate restored set key"));
            }
        }
        Ok(values)
    }
}
