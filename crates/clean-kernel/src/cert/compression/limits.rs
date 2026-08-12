// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared fail-closed resource limits for certificate archive ingress.

use std::{cell::Cell, fmt, io::Read, marker::PhantomData, rc::Rc};

use serde::de::{
    DeserializeOwned, DeserializeSeed, Deserializer, EnumAccess, MapAccess, SeqAccess,
    VariantAccess, Visitor,
};

use crate::serde_budget::{with_decode_resource_limits, DecodeResourceLimits};

/// Maximum compressed payload accepted by an in-memory archive decoder.
pub(crate) const MAX_COMPRESSED_ARCHIVE_BYTES: usize = 256 * 1024 * 1024;

/// Maximum decompressed payload accepted by an in-memory archive decoder.
pub(crate) const MAX_UNCOMPRESSED_ARCHIVE_BYTES: usize = 512 * 1024 * 1024;

/// Maximum dictionary payload accepted by dictionary-backed zstd operations.
pub(crate) const MAX_DICTIONARY_BYTES: usize = 16 * 1024 * 1024;

/// Maximum number of entries in any one compressed representation table.
///
/// Container entries and recursive certificate nodes have independent decode
/// budgets.  This limit therefore means what it says: a single table may
/// contain up to four million rows, while all variable containers in one
/// carrier share the aggregate container-element budget below.
pub(crate) const MAX_COMPRESSED_TABLE_ENTRIES: usize = 4_000_000;

/// Maximum expanded certificate/definitional-equality nodes reconstructed
/// from a compressed certificate DAG.
pub(crate) const MAX_DECOMPRESSED_CERT_NODES: usize = 1_000_000;

/// Maximum estimated owned bytes reconstructed from a compressed certificate
/// DAG, including payload bytes multiplied by sharing expansion.
pub(crate) const MAX_DECOMPRESSED_CERT_BYTES: usize = 256 * 1024 * 1024;

/// Wire-proportional GROWTH factor for the plain-bincode certificate
/// decode: a large carrier may claim up to `wire x 1024` owned bytes even
/// where that exceeds the flat `MAX_DECOMPRESSED_CERT_BYTES` budget
/// (backstopped by the archive-wide `MAX_DECODE_NODES`). Rationale: the
/// flat budgets bound what a SMALL forged carrier can make the decoder
/// allocate; a carrier that actually transmits megabytes may
/// proportionally claim more, which is the standard resource-bounding
/// posture and what real deep-term bundles (the indexed M-type
/// graduation bundle: >1M nodes from a 660 KiB carrier, ~400x) need.
/// Small carriers see EXACTLY the old flat budgets — the decompression
/// bomb defenses are unchanged.
pub(crate) const CERT_WIRE_EXPANSION: usize = 1024;

/// Maximum serialized size of one certificate in a streaming archive.
pub(crate) const MAX_STREAM_CERT_BYTES: usize = 256 * 1024 * 1024;

/// Maximum certificate count accepted in one streaming archive.
pub(crate) const MAX_STREAM_CERTIFICATES: u64 = 1_000_000;

/// Maximum aggregate uncompressed bytes accepted from one streaming archive.
pub(crate) const MAX_STREAM_UNCOMPRESSED_BYTES: u64 = 16 * 1024 * 1024 * 1024;

/// Maximum aggregate number of recursive kernel nodes decoded in one value.
pub(crate) const MAX_DECODE_NODES: usize = 8_000_000;

/// Maximum recursive kernel-value depth decoded in one value.
pub(crate) const MAX_DECODE_DEPTH: usize = 100_000;

/// Maximum aggregate number of non-byte variable-container entries decoded in
/// one archive value.
///
/// Byte sequences are bounded by the carrier and bincode byte limits instead;
/// charging every `u8` as a structural row would silently reduce the advertised
/// 256/512 MiB archive limits to only a few MiB.
const MAX_DECODE_CONTAINER_ELEMENTS: usize = 8_000_000;

/// Default recursive decode budget for an archive-contained kernel value.
pub(crate) const ARCHIVE_DECODE_LIMITS: DecodeResourceLimits = DecodeResourceLimits {
    max_nodes: MAX_DECODE_NODES,
    max_depth: MAX_DECODE_DEPTH,
};

/// Upper bound on how many in-memory bytes one wire byte may claim during
/// decode.  bincode's limit config meters capacity claims (in-memory element
/// sizes), which legitimately exceed wire bytes for structured data: a
/// varint-packed `u64` claims 8 bytes for 1-3 wire bytes, and boxed recursive
/// enum nodes claim tens.  64x envelopes every shape observed in real bundles
/// (~14x) with margin, while still capping what a small forged carrier can
/// make the decoder pre-allocate (a 100-byte header authorizes at most 6.4 KiB).
const DECODE_CLAIM_AMPLIFICATION: usize = 64;

/// Conservative upper bound charged for each certificate/kernel structural
/// node decoded from bincode.  This covers the largest recursive enums, Box or
/// Arc bookkeeping, and allocator slack; carrier bytes are charged separately.
const CERTIFICATE_DECODE_NODE_BYTES: usize = 256;

/// Decode one bincode value under recursive kernel node/depth accounting.
///
/// Exact consumption is part of the archive contract: trailing bytes are
/// rejected instead of silently accepting an ambiguous carrier.
pub(crate) fn decode_bincode_limited<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, String> {
    decode_bincode_with_limits(bytes, ARCHIVE_DECODE_LIMITS)
}

/// Decode a certificate carrier while bounding materialization itself.
///
/// Compressed-certificate expansion checks run after bincode decoding, so they
/// cannot protect against recursive `ModeSpecific(ProofCert)` or `DefEqStep`
/// trees allocating during Deserialize.  Charge the carrier bytes plus a
/// conservative per-node allocation bound against the same expanded-byte
/// ceiling, and cap structural nodes at the expanded-node ceiling.
pub(crate) fn decode_certificate_bincode_limited<T: DeserializeOwned>(
    bytes: &[u8],
) -> Result<T, String> {
    // Wire-proportional GROWTH: small carriers keep the flat budgets (the
    // decompression-bomb defenses are unchanged); a carrier that actually
    // transmits more may claim proportionally more, backstopped by the
    // archive-wide node ceiling. Real deep-term bundles (the indexed
    // M-type graduation bundle: >1M nodes from a 660 KiB carrier, ~400x
    // claim/wire) need this headroom.
    let owned = MAX_DECOMPRESSED_CERT_BYTES.max(bytes.len().saturating_mul(CERT_WIRE_EXPANSION));
    let nodes = MAX_DECOMPRESSED_CERT_NODES
        .max(owned / CERTIFICATE_DECODE_NODE_BYTES)
        .min(MAX_DECODE_NODES);
    decode_certificate_bincode_with_limits(bytes, nodes, owned)
}

fn decode_certificate_bincode_with_limits<T: DeserializeOwned>(
    bytes: &[u8],
    max_nodes: usize,
    max_owned_bytes: usize,
) -> Result<T, String> {
    let remaining = max_owned_bytes.checked_sub(bytes.len()).ok_or_else(|| {
        format!(
            "certificate carrier size {} exceeds owned-byte budget {max_owned_bytes}",
            bytes.len()
        )
    })?;
    let byte_limited_nodes = remaining / CERTIFICATE_DECODE_NODE_BYTES;
    let node_limit = max_nodes.min(byte_limited_nodes);
    if node_limit == 0 {
        return Err(format!(
            "certificate carrier leaves no structural-node budget within {max_owned_bytes} bytes"
        ));
    }
    decode_bincode_with_limits(
        bytes,
        DecodeResourceLimits {
            max_nodes: node_limit,
            max_depth: MAX_DECODE_DEPTH.min(node_limit),
        },
    )
}

pub(crate) fn decode_bincode_with_limits<T: DeserializeOwned>(
    bytes: &[u8],
    limits: DecodeResourceLimits,
) -> Result<T, String> {
    if bytes.len() > MAX_UNCOMPRESSED_ARCHIVE_BYTES {
        return Err(format!(
            "archive value size {} exceeds maximum {}",
            bytes.len(),
            MAX_UNCOMPRESSED_ARCHIVE_BYTES
        ));
    }

    // bincode's native Decode implementations account for container
    // allocations, but its serde sequence/map bridge exposes the declared
    // length as a size_hint without claiming it.  In particular, a tiny
    // length-only payload could otherwise make Vec reserve attacker-chosen
    // capacity before the decoder discovers EOF.  Suppress those hints and
    // meter elements as they are actually requested by serde visitors.
    let container_budget =
        MAX_DECODE_CONTAINER_ELEMENTS.min(bytes.len().saturating_mul(8).max(4_096));
    let seed = LimitedSeed::<T>::new(DecodeBudgets::new(container_budget, limits.max_nodes));

    // Owned strings and byte buffers are allocated inside bincode before a
    // serde visitor sees them.  Select a compile-time bincode limit by size
    // class so a tiny carrier can never authorize a large allocation.
    //
    // The class must be chosen against the carrier's ALLOCATION CLAIMS, not
    // its wire length: bincode's limit meters in-memory capacity claims
    // (`size_of::<T>() * len` per container), and structured graphs claim a
    // large multiple of their wire bytes (small varint-encoded fields expand
    // to full-width in-memory fields; boxed enum nodes claim tens of bytes
    // per few wire bytes).  Classing on the raw wire length made ~1.1 MiB
    // archives whose claims run ~14x the wire size die at the 16 MiB class
    // with `LimitExceeded` — a legitimate `export-cert` bundle failed its own
    // `cert verify` roundtrip.  `DECODE_CLAIM_AMPLIFICATION` bounds that
    // in-memory expansion; the per-node and per-container budgets in
    // `LimitedSeed` remain the fine-grained structural meter.
    let claim_budget = bytes
        .len()
        .saturating_mul(DECODE_CLAIM_AMPLIFICATION)
        .max(4 * 1024);
    let decoded = with_decode_resource_limits(limits, || {
        if claim_budget <= 4 * 1024 {
            decode_seed_with_limit::<T, { 4 * 1024 }>(bytes, seed)
        } else if claim_budget <= 64 * 1024 {
            decode_seed_with_limit::<T, { 64 * 1024 }>(bytes, seed)
        } else if claim_budget <= 1024 * 1024 {
            decode_seed_with_limit::<T, { 1024 * 1024 }>(bytes, seed)
        } else if claim_budget <= 16 * 1024 * 1024 {
            decode_seed_with_limit::<T, { 16 * 1024 * 1024 }>(bytes, seed)
        } else if claim_budget <= 256 * 1024 * 1024 {
            decode_seed_with_limit::<T, { 256 * 1024 * 1024 }>(bytes, seed)
        } else {
            decode_seed_with_limit::<T, { MAX_UNCOMPRESSED_ARCHIVE_BYTES }>(bytes, seed)
        }
    })
    .map_err(|error| error.to_string())?;
    if decoded.1 != bytes.len() {
        return Err(format!(
            "archive value has {} trailing bytes",
            bytes.len() - decoded.1
        ));
    }
    Ok(decoded.0)
}

fn decode_seed_with_limit<T: DeserializeOwned, const N: usize>(
    bytes: &[u8],
    seed: LimitedSeed<T>,
) -> Result<(T, usize), bincode::error::DecodeError> {
    bincode::serde::seed_decode_from_slice(
        seed,
        bytes,
        bincode::config::standard().with_limit::<N>(),
    )
}

#[derive(Clone)]
struct DecodeBudgets {
    container_elements: Rc<Cell<usize>>,
    recursive_nodes: Rc<Cell<usize>>,
}

impl DecodeBudgets {
    fn new(container_elements: usize, recursive_nodes: usize) -> Self {
        Self {
            container_elements: Rc::new(Cell::new(container_elements)),
            recursive_nodes: Rc::new(Cell::new(recursive_nodes)),
        }
    }

    fn charge_container<E: serde::de::Error>(&self) -> Result<(), E> {
        let remaining = self.container_elements.get();
        if remaining == 0 {
            return Err(E::custom("archive container element limit exceeded"));
        }
        self.container_elements.set(remaining - 1);
        Ok(())
    }

    fn charge_recursive_node<E: serde::de::Error>(&self) -> Result<(), E> {
        let remaining = self.recursive_nodes.get();
        if remaining == 0 {
            return Err(E::custom(
                "certificate recursive structural node limit exceeded",
            ));
        }
        self.recursive_nodes.set(remaining - 1);
        Ok(())
    }
}

struct LimitedSeed<T> {
    budgets: DecodeBudgets,
    marker: PhantomData<fn() -> T>,
}

impl<T> LimitedSeed<T> {
    fn new(budgets: DecodeBudgets) -> Self {
        Self {
            budgets,
            marker: PhantomData,
        }
    }
}

impl<T> Clone for LimitedSeed<T> {
    fn clone(&self) -> Self {
        Self::new(self.budgets.clone())
    }
}

impl<'de, T: serde::Deserialize<'de>> DeserializeSeed<'de> for LimitedSeed<T> {
    type Value = T;

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<T, D::Error> {
        T::deserialize(LimitedDeserializer {
            inner: deserializer,
            budgets: self.budgets,
            pending_sequence_element: false,
        })
    }
}

struct LimitedDeserializer<D> {
    inner: D,
    budgets: DecodeBudgets,
    pending_sequence_element: bool,
}

impl<D> LimitedDeserializer<D> {
    fn charge_pending_sequence_element<E: serde::de::Error>(&mut self) -> Result<(), E> {
        if std::mem::take(&mut self.pending_sequence_element) {
            self.budgets.charge_container()?;
        }
        Ok(())
    }

    fn accept_pending_byte(&mut self) {
        // A `Vec<u8>` is a byte payload rather than a structural container.
        // Its allocation and decoded length remain bounded by the carrier's
        // bincode limit and the archive's explicit byte ceilings.
        self.pending_sequence_element = false;
    }
}

macro_rules! forward_scalar {
    ($($method:ident),+ $(,)?) => {
        $(
            fn $method<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
            where
                V: Visitor<'de>,
            {
                self.charge_pending_sequence_element()?;
                self.inner.$method(visitor)
            }
        )+
    };
}

impl<'de, D: Deserializer<'de>> Deserializer<'de> for LimitedDeserializer<D> {
    type Error = D::Error;

    forward_scalar!(
        deserialize_any,
        deserialize_bool,
        deserialize_i8,
        deserialize_i16,
        deserialize_i32,
        deserialize_i64,
        deserialize_i128,
        deserialize_u16,
        deserialize_u32,
        deserialize_u64,
        deserialize_u128,
        deserialize_f32,
        deserialize_f64,
        deserialize_char,
        deserialize_str,
        deserialize_string,
        deserialize_bytes,
        deserialize_byte_buf,
        deserialize_unit,
        deserialize_identifier,
        deserialize_ignored_any,
    );

    fn deserialize_u8<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.accept_pending_byte();
        self.inner.deserialize_u8(visitor)
    }

    fn deserialize_option<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_option(LimitedVisitor::fixed(visitor, self.budgets))
    }

    fn deserialize_unit_struct<V>(
        mut self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner.deserialize_unit_struct(name, visitor)
    }

    fn deserialize_newtype_struct<V>(
        mut self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_newtype_struct(name, LimitedVisitor::fixed(visitor, self.budgets))
    }

    fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_seq(LimitedVisitor::variable(visitor, self.budgets))
    }

    fn deserialize_tuple<V>(mut self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_tuple(len, LimitedVisitor::fixed(visitor, self.budgets))
    }

    fn deserialize_tuple_struct<V>(
        mut self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_tuple_struct(name, len, LimitedVisitor::fixed(visitor, self.budgets))
    }

    fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_map(LimitedVisitor::variable(visitor, self.budgets))
    }

    fn deserialize_struct<V>(
        mut self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        self.inner
            .deserialize_struct(name, fields, LimitedVisitor::fixed(visitor, self.budgets))
    }

    fn deserialize_enum<V>(
        mut self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.charge_pending_sequence_element()?;
        // Only genuinely recursive certificate enums consume this budget.
        // Flat compressed-table enums are independently bounded as container
        // rows, and ordinary byte sequences are independently byte-bounded.
        // The `*Wire` names are used by the stack-safe custom serde layer.
        if matches!(
            name,
            "ProofCert" | "ProofCertWire" | "DefEqStep" | "DefEqStepWire"
        ) {
            self.budgets.charge_recursive_node()?;
        }
        self.inner
            .deserialize_enum(name, variants, LimitedVisitor::fixed(visitor, self.budgets))
    }
}

struct LimitedVisitor<V> {
    inner: V,
    budgets: DecodeBudgets,
    charge_elements: bool,
}

impl<V> LimitedVisitor<V> {
    fn fixed(inner: V, budgets: DecodeBudgets) -> Self {
        Self {
            inner,
            budgets,
            charge_elements: false,
        }
    }

    fn variable(inner: V, budgets: DecodeBudgets) -> Self {
        Self {
            inner,
            budgets,
            charge_elements: true,
        }
    }
}

macro_rules! forward_visit_copy {
    ($(($method:ident, $ty:ty)),+ $(,)?) => {
        $(
            fn $method<E: serde::de::Error>(self, value: $ty) -> Result<Self::Value, E> {
                self.inner.$method(value)
            }
        )+
    };
}

impl<'de, V: Visitor<'de>> Visitor<'de> for LimitedVisitor<V> {
    type Value = V::Value;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.expecting(formatter)
    }

    forward_visit_copy!(
        (visit_bool, bool),
        (visit_i8, i8),
        (visit_i16, i16),
        (visit_i32, i32),
        (visit_i64, i64),
        (visit_i128, i128),
        (visit_u8, u8),
        (visit_u16, u16),
        (visit_u32, u32),
        (visit_u64, u64),
        (visit_u128, u128),
        (visit_f32, f32),
        (visit_f64, f64),
        (visit_char, char),
    );

    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Self::Value, E> {
        self.inner.visit_str(value)
    }

    fn visit_borrowed_str<E: serde::de::Error>(self, value: &'de str) -> Result<Self::Value, E> {
        self.inner.visit_borrowed_str(value)
    }

    fn visit_string<E: serde::de::Error>(self, value: String) -> Result<Self::Value, E> {
        self.inner.visit_string(value)
    }

    fn visit_bytes<E: serde::de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        self.inner.visit_bytes(value)
    }

    fn visit_borrowed_bytes<E: serde::de::Error>(self, value: &'de [u8]) -> Result<Self::Value, E> {
        self.inner.visit_borrowed_bytes(value)
    }

    fn visit_byte_buf<E: serde::de::Error>(self, value: Vec<u8>) -> Result<Self::Value, E> {
        self.inner.visit_byte_buf(value)
    }

    fn visit_none<E: serde::de::Error>(self) -> Result<Self::Value, E> {
        self.inner.visit_none()
    }

    fn visit_some<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        self.inner.visit_some(LimitedDeserializer {
            inner: deserializer,
            budgets: self.budgets,
            pending_sequence_element: false,
        })
    }

    fn visit_unit<E: serde::de::Error>(self) -> Result<Self::Value, E> {
        self.inner.visit_unit()
    }

    fn visit_newtype_struct<D: Deserializer<'de>>(
        self,
        deserializer: D,
    ) -> Result<Self::Value, D::Error> {
        self.inner.visit_newtype_struct(LimitedDeserializer {
            inner: deserializer,
            budgets: self.budgets,
            pending_sequence_element: false,
        })
    }

    fn visit_seq<A: SeqAccess<'de>>(self, access: A) -> Result<Self::Value, A::Error> {
        self.inner.visit_seq(LimitedSeqAccess {
            inner: access,
            budgets: self.budgets,
            charge_elements: self.charge_elements,
        })
    }

    fn visit_map<A: MapAccess<'de>>(self, access: A) -> Result<Self::Value, A::Error> {
        self.inner.visit_map(LimitedMapAccess {
            inner: access,
            budgets: self.budgets,
            charge_entries: self.charge_elements,
        })
    }

    fn visit_enum<A: EnumAccess<'de>>(self, access: A) -> Result<Self::Value, A::Error> {
        self.inner.visit_enum(LimitedEnumAccess {
            inner: access,
            budgets: self.budgets,
        })
    }
}

struct LimitedSeqAccess<A> {
    inner: A,
    budgets: DecodeBudgets,
    charge_elements: bool,
}

impl<'de, A: SeqAccess<'de>> SeqAccess<'de> for LimitedSeqAccess<A> {
    type Error = A::Error;

    fn next_element_seed<T: DeserializeSeed<'de>>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, Self::Error> {
        self.inner.next_element_seed(WrappedSeed {
            inner: seed,
            budgets: self.budgets.clone(),
            pending_sequence_element: self.charge_elements,
        })
    }

    // Never propagate an attacker-controlled declared length into Vec or map
    // reserve.  Capacity grows only as successfully decoded elements arrive.
    fn size_hint(&self) -> Option<usize> {
        None
    }
}

struct LimitedMapAccess<A> {
    inner: A,
    budgets: DecodeBudgets,
    charge_entries: bool,
}

impl<'de, A: MapAccess<'de>> MapAccess<'de> for LimitedMapAccess<A> {
    type Error = A::Error;

    fn next_key_seed<K: DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Self::Error> {
        if self.charge_entries {
            self.budgets.charge_container()?;
        }
        self.inner.next_key_seed(WrappedSeed {
            inner: seed,
            budgets: self.budgets.clone(),
            pending_sequence_element: false,
        })
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Self::Error> {
        self.inner.next_value_seed(WrappedSeed {
            inner: seed,
            budgets: self.budgets.clone(),
            pending_sequence_element: false,
        })
    }

    fn size_hint(&self) -> Option<usize> {
        None
    }
}

struct WrappedSeed<S> {
    inner: S,
    budgets: DecodeBudgets,
    pending_sequence_element: bool,
}

impl<'de, S: DeserializeSeed<'de>> DeserializeSeed<'de> for WrappedSeed<S> {
    type Value = S::Value;

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        self.inner.deserialize(LimitedDeserializer {
            inner: deserializer,
            budgets: self.budgets,
            pending_sequence_element: self.pending_sequence_element,
        })
    }
}

struct LimitedEnumAccess<A> {
    inner: A,
    budgets: DecodeBudgets,
}

impl<'de, A: EnumAccess<'de>> EnumAccess<'de> for LimitedEnumAccess<A> {
    type Error = A::Error;
    type Variant = LimitedVariantAccess<A::Variant>;

    fn variant_seed<V: DeserializeSeed<'de>>(
        self,
        seed: V,
    ) -> Result<(V::Value, Self::Variant), Self::Error> {
        let (value, variant) = self.inner.variant_seed(WrappedSeed {
            inner: seed,
            budgets: self.budgets.clone(),
            pending_sequence_element: false,
        })?;
        Ok((
            value,
            LimitedVariantAccess {
                inner: variant,
                budgets: self.budgets,
            },
        ))
    }
}

struct LimitedVariantAccess<A> {
    inner: A,
    budgets: DecodeBudgets,
}

impl<'de, A: VariantAccess<'de>> VariantAccess<'de> for LimitedVariantAccess<A> {
    type Error = A::Error;

    fn unit_variant(self) -> Result<(), Self::Error> {
        self.inner.unit_variant()
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(
        self,
        seed: T,
    ) -> Result<T::Value, Self::Error> {
        self.inner.newtype_variant_seed(WrappedSeed {
            inner: seed,
            budgets: self.budgets,
            pending_sequence_element: false,
        })
    }

    fn tuple_variant<V: Visitor<'de>>(
        self,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.inner
            .tuple_variant(len, LimitedVisitor::fixed(visitor, self.budgets))
    }

    fn struct_variant<V: Visitor<'de>>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.inner
            .struct_variant(fields, LimitedVisitor::fixed(visitor, self.budgets))
    }
}

/// Read exactly a declared decompressed payload, bounded before allocation.
pub(crate) fn read_declared_bounded(
    reader: impl Read,
    declared_size: usize,
    max_size: usize,
    label: &str,
) -> Result<Vec<u8>, String> {
    if declared_size > max_size {
        return Err(format!(
            "{label} declared size {declared_size} exceeds maximum {max_size}"
        ));
    }

    let limit = declared_size
        .checked_add(1)
        .ok_or_else(|| format!("{label} declared size overflow"))?;
    // The declaration is attacker-controlled.  Do not reserve it up front:
    // a one-byte compressed stream claiming the maximum archive size must not
    // force a hundreds-of-megabytes allocation before EOF is observed.
    let mut output = Vec::new();
    reader
        .take(limit as u64)
        .read_to_end(&mut output)
        .map_err(|error| error.to_string())?;

    if output.len() != declared_size {
        return Err(format!(
            "{label} declared size {declared_size} does not match decoded size {}",
            output.len()
        ));
    }
    Ok(output)
}

/// Read an undeclared payload up to a fixed maximum.
pub(crate) fn read_unknown_bounded(
    reader: impl Read,
    max_size: usize,
    label: &str,
) -> Result<Vec<u8>, String> {
    let limit = max_size
        .checked_add(1)
        .ok_or_else(|| format!("{label} size limit overflow"))?;
    let mut output = Vec::new();
    reader
        .take(limit as u64)
        .read_to_end(&mut output)
        .map_err(|error| error.to_string())?;
    if output.len() > max_size {
        return Err(format!("{label} decoded size exceeds maximum {max_size}"));
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cert::{DefEqStep, ProofCert};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    enum FlatRow {
        Value,
    }

    struct CapturesSequenceHint(bool);

    impl<'de> Deserialize<'de> for CapturesSequenceHint {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            struct HintVisitor;

            impl<'de> Visitor<'de> for HintVisitor {
                type Value = CapturesSequenceHint;

                fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                    formatter.write_str("a sequence")
                }

                fn visit_seq<A: SeqAccess<'de>>(
                    self,
                    sequence: A,
                ) -> Result<Self::Value, A::Error> {
                    Ok(CapturesSequenceHint(sequence.size_hint().is_none()))
                }
            }

            deserializer.deserialize_seq(HintVisitor)
        }
    }

    fn huge_length_prefix() -> Vec<u8> {
        bincode::serde::encode_to_vec(u64::MAX, bincode::config::standard()).unwrap()
    }

    #[test]
    fn untrusted_sequence_length_is_never_a_reservation_hint() {
        let decoded =
            decode_bincode_limited::<CapturesSequenceHint>(&huge_length_prefix()).unwrap();
        assert!(decoded.0);
    }

    #[test]
    fn tiny_huge_lengths_fail_without_large_vec_or_string_allocation() {
        let prefix = huge_length_prefix();

        assert!(decode_bincode_limited::<Vec<u8>>(&prefix).is_err());
        assert!(decode_bincode_limited::<String>(&prefix).is_err());

        let error = decode_bincode_limited::<Vec<()>>(&prefix).unwrap_err();
        assert!(
            error.contains("container element limit"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn byte_payloads_and_flat_rows_do_not_consume_recursive_node_budget() {
        // Exceed the old accidental ~1 MiB certificate-byte ceiling while
        // allowing only one genuinely recursive node.
        let raw = vec![0xA5_u8; 1_100_000];
        let raw_bytes = bincode::serde::encode_to_vec(&raw, bincode::config::standard()).unwrap();
        let decoded =
            decode_certificate_bincode_with_limits::<Vec<u8>>(&raw_bytes, 1, 2 * 1024 * 1024)
                .expect("raw bytes are carrier-bounded, not recursive-node-bounded");
        assert_eq!(decoded, raw);

        let rows = (0..64).map(|_| FlatRow::Value).collect::<Vec<_>>();
        let row_bytes = bincode::serde::encode_to_vec(&rows, bincode::config::standard()).unwrap();
        let decoded =
            decode_certificate_bincode_with_limits::<Vec<FlatRow>>(&row_bytes, 1, 1024 * 1024)
                .expect("flat table enums are container-bounded, not recursive-node-bounded");
        assert_eq!(decoded, rows);
        assert_eq!(MAX_COMPRESSED_TABLE_ENTRIES, 4_000_000);
    }

    #[test]
    fn huge_declaration_with_tiny_source_is_read_incrementally() {
        let error = read_declared_bounded(
            std::io::Cursor::new([0_u8]),
            MAX_UNCOMPRESSED_ARCHIVE_BYTES,
            MAX_UNCOMPRESSED_ARCHIVE_BYTES,
            "test archive",
        )
        .unwrap_err();
        assert!(error.contains("does not match decoded size 1"));
    }

    #[test]
    fn certificate_decode_rejects_recursive_nodes_during_materialization() {
        let mut cert = ProofCert::SProp;
        let mut step = DefEqStep::Refl;
        for _ in 0..64 {
            cert = ProofCert::Squash {
                inner_cert: Box::new(cert),
            };
            step = DefEqStep::Symm(Box::new(step));
        }

        let cert_bytes = bincode::serde::encode_to_vec(&cert, bincode::config::standard()).unwrap();
        let step_bytes = bincode::serde::encode_to_vec(&step, bincode::config::standard()).unwrap();
        let cert_error =
            decode_certificate_bincode_with_limits::<ProofCert>(&cert_bytes, 32, 1024 * 1024)
                .unwrap_err();
        let step_error =
            decode_certificate_bincode_with_limits::<DefEqStep>(&step_bytes, 32, 1024 * 1024)
                .unwrap_err();
        assert!(
            cert_error.contains("recursive structural node limit")
                || cert_error.contains("structural node count"),
            "unexpected certificate error: {cert_error}"
        );
        assert!(
            step_error.contains("recursive structural node limit")
                || step_error.contains("structural node count"),
            "unexpected definitional-equality error: {step_error}"
        );
    }

    /// Regression for the export-cert -> cert verify roundtrip failure
    /// (2026-08-04): the size class fed bincode's limit with the WIRE length,
    /// but bincode meters in-memory allocation claims, which run a large
    /// multiple of wire bytes for structured data. A ~2.4 MiB carrier of
    /// varint-packed tuples claims ~8x its wire size in `Vec<u64>` capacity
    /// alone — under wire-length classing it landed in the 16 MiB class and
    /// died with LimitExceeded; under claim classing it decodes fine.
    #[test]
    fn test_decode_structured_carrier_claims_exceed_wire_class_roundtrips() {
        // 800k rows of three small u64s: wire ~3 bytes/row (varint), claims
        // 24 bytes/row in-memory — the amplification shape real cert bundles
        // exhibit (boxed enum graphs), in a cheap synthetic carrier.
        let rows: Vec<(u64, u64, u64)> = (0..800_000u64).map(|i| (i % 7, i % 5, i % 3)).collect();
        let bytes = bincode::serde::encode_to_vec(&rows, bincode::config::standard()).unwrap();
        assert!(
            bytes.len() > 1024 * 1024 && bytes.len() < 16 * 1024 * 1024,
            "fixture must land above the 1 MiB wire class (got {})",
            bytes.len()
        );
        let decoded: Vec<(u64, u64, u64)> = decode_bincode_with_limits(
            &bytes,
            DecodeResourceLimits {
                max_nodes: MAX_DECODE_NODES,
                max_depth: MAX_DECODE_DEPTH,
            },
        )
        .expect("legitimate structured carrier must decode under claim-classed limits");
        assert_eq!(decoded.len(), rows.len());
    }

    /// The claim-amplification factor must still forbid tiny forged carriers
    /// from authorizing large allocations: a length-prefix-only payload keeps
    /// being rejected, exactly as before the classing fix.
    #[test]
    fn test_decode_tiny_forged_carrier_still_rejected_after_claim_classing() {
        let prefix = huge_length_prefix();
        assert!(decode_bincode_limited::<Vec<u8>>(&prefix).is_err());
        assert!(decode_bincode_limited::<String>(&prefix).is_err());
    }
}
