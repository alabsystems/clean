// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A parsed projection's index is the Nat the `.olean` stores, or a refusal.
//!
//! Lean's kernel takes a projection index only when it is a small Nat that
//! fits in `unsigned` (`to_proj_idx`, `src/kernel/type_checker.cpp`, v4.33.1;
//! v4.30.0-rc2's `infer_proj` refuses `!proj_idx(e).is_small()`). A small Nat
//! is a boxed scalar. Until decision R147 this reader kept the low limb of a
//! heap Nat and read a null or unreadable index as 0, so `.proj S (2^64) c`
//! parsed as `.proj S 0 c`, a different and possibly well-typed term.
use super::*;
use crate::import::{convert_expr, read_and_convert_expr, ExprInternCache};

const BASE: u64 = 0x10000;

struct Raw(Vec<u8>);
impl Raw {
    /// A v2 GMP-layout header, as `bvar_tests` builds it.
    fn new() -> Self {
        let mut bytes = vec![0; 152];
        bytes[..5].copy_from_slice(b"olean");
        bytes[5] = 2;
        bytes[6] = 1;
        bytes[7..17].copy_from_slice(b"4.30.0-rc2");
        bytes[40..80].fill(b'a');
        bytes[80..88].copy_from_slice(&BASE.to_le_bytes());
        bytes[88..96].copy_from_slice(&(BASE + 96).to_le_bytes());
        bytes[100..102].copy_from_slice(&56u16.to_le_bytes());
        bytes[102] = 5;
        for index in 0..5 {
            bytes[104 + index * 8..112 + index * 8].copy_from_slice(&1u64.to_le_bytes());
        }
        Self(bytes)
    }
    fn ptr(offset: usize) -> u64 {
        BASE + offset as u64
    }
    /// `.bvar 0`, the projected term.
    fn bvar0(&mut self) -> usize {
        let offset = self.0.len();
        self.0
            .extend_from_slice(&[0, 0, 0, 0, 24, 0, 1, expr_tags::BVAR]);
        self.0.extend_from_slice(&1u64.to_le_bytes());
        self.0.extend_from_slice(&[0; 8]);
        offset
    }
    /// `.proj <anonymous> idx (.bvar 0)` with the index field `idx_field`.
    fn proj(&mut self, idx_field: u64) -> usize {
        let inner = self.bvar0();
        let offset = self.0.len();
        self.0
            .extend_from_slice(&[0, 0, 0, 0, 40, 0, 3, expr_tags::PROJ]);
        self.0.extend_from_slice(&1u64.to_le_bytes());
        self.0.extend_from_slice(&idx_field.to_le_bytes());
        self.0.extend_from_slice(&Self::ptr(inner).to_le_bytes());
        self.0.extend_from_slice(&[0; 8]);
        offset
    }
    fn mpz(&mut self, limbs: &[u64]) -> u64 {
        let ptr = Self::ptr(self.0.len());
        self.0.extend_from_slice(&[0; 4]);
        self.0
            .extend_from_slice(&((24 + limbs.len() * 8) as u16).to_le_bytes());
        self.0.extend_from_slice(&[0, tags::MPZ]);
        self.0
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.0
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.0.extend_from_slice(&(ptr + 24).to_le_bytes());
        for limb in limbs {
            self.0.extend_from_slice(&limb.to_le_bytes());
        }
        ptr
    }
    fn read(&self, offset: usize) -> OleanResult<ParsedExpr> {
        CompactedRegion::new(&self.0, BASE).read_expr_at(offset)
    }
    /// Both decoders, parse-then-convert and direct, refuse the projection.
    fn assert_refused(&self, offset: usize, what: &str) {
        let parsed = self.read(offset);
        let converted = parsed.as_ref().map(|expr| {
            convert_expr("proj-index", expr, &mut ExprInternCache::default()).map(|(e, _)| e)
        });
        assert!(
            !matches!(converted, Ok(Ok(_))),
            "{what}: the two-phase decoder must refuse, parsed {parsed:?}"
        );
        let region = CompactedRegion::new(&self.0, BASE);
        assert!(
            read_and_convert_expr(
                &region,
                Self::ptr(offset),
                "proj-index",
                &mut ExprInternCache::default()
            )
            .is_err(),
            "{what}: the direct decoder must refuse"
        );
    }
}

#[test]
fn small_projection_index_is_exact() {
    for index in [0u64, 2, u64::from(u32::MAX)] {
        let mut raw = Raw::new();
        let offset = raw.proj((index << 1) | 1);
        let parsed = raw.read(offset).expect("a scalar index parses");
        assert_eq!(
            parsed,
            ParsedExpr::Proj(String::new(), index, Box::new(ParsedExpr::BVar(0)))
        );
        // Both decoders accept this object, so a refusal below is the index's.
        // (They spell the anonymous structure name differently, which no real
        // projection carries, so only the index is compared.)
        let (two_phase, _) = convert_expr("proj-index", &parsed, &mut ExprInternCache::default())
            .expect("the two-phase decoder converts a small index");
        let region = CompactedRegion::new(&raw.0, BASE);
        let (direct, _) = read_and_convert_expr(
            &region,
            Raw::ptr(offset),
            "proj-index",
            &mut ExprInternCache::default(),
        )
        .expect("the direct decoder converts a small index");
        for (decoder, expr) in [("two-phase", &two_phase), ("direct", &direct)] {
            assert!(
                matches!(expr.kind(), clean_kernel::ExprKind::Proj(_, i, _) if u64::from(*i) == index),
                "{decoder}: index {index} must convert exactly, got {expr:?}"
            );
        }
    }
}

#[test]
fn over_u64_projection_index_never_truncates_to_zero() {
    let mut raw = Raw::new();
    let heap = raw.mpz(&[0, 1]);
    let offset = raw.proj(heap);
    raw.assert_refused(offset, "2^64");
    assert!(raw.read(offset).is_err(), "2^64 has no u64 reading");
}

#[test]
fn null_projection_index_refuses_instead_of_inventing_zero() {
    let mut raw = Raw::new();
    let offset = raw.proj(0);
    raw.assert_refused(offset, "null");
    assert!(raw.read(offset).is_err(), "a null index is not 0");
}

#[test]
fn noncanonical_heap_projection_index_refuses() {
    // Lean boxes every Nat below 2^63, so a heap Nat holding 5 is not one Lean
    // writes, and its kernel's `is_small()` refuses it.
    let mut raw = Raw::new();
    let heap = raw.mpz(&[5]);
    let offset = raw.proj(heap);
    raw.assert_refused(offset, "heap 5");
    assert!(raw.read(offset).is_err(), "a heap 5 is not read as 5");
}

#[test]
fn heap_projection_index_beyond_the_kernel_carrier_refuses() {
    // A canonical heap Nat (>= 2^63) parses exactly, and conversion refuses it
    // because it exceeds `unsigned`.
    for index in [1u64 << 63, u64::MAX] {
        let mut raw = Raw::new();
        let heap = raw.mpz(&[index]);
        let offset = raw.proj(heap);
        assert_eq!(
            raw.read(offset).expect("a canonical heap Nat parses"),
            ParsedExpr::Proj(String::new(), index, Box::new(ParsedExpr::BVar(0)))
        );
        raw.assert_refused(offset, "u64 heap Nat");
    }
}
