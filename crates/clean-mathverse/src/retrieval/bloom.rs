// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bloom filter — the fast negative-lookup pre-filter under
//! [`super::RetrievalIndex`].
//!
//! A retrieval query that can prove "this name is definitely NOT in the index"
//! without touching the name table or the discrimination tree is the cheapest
//! query there is, and that is all this file is for. Sizing (`optimal_bits`)
//! and hash count (`optimal_hashes`) are derived from the requested capacity
//! and false-positive rate, and the hash is a seeded FNV-1a; the three are only
//! ever correct TOGETHER, so they live in one file with the filter itself.

/// Simple Bloom filter for fast negative lookups.
pub struct BloomFilter {
    bits: Vec<u64>,
    num_bits: usize,
    num_hashes: u32,
}

impl BloomFilter {
    /// Create a new Bloom filter with the given capacity and false-positive rate.
    #[must_use]
    pub fn new(expected_items: usize, fp_rate: f64) -> Self {
        let num_bits = optimal_bits(expected_items, fp_rate);
        let num_hashes = optimal_hashes(num_bits, expected_items);
        let words = num_bits.div_ceil(64);
        Self {
            bits: vec![0; words],
            num_bits,
            num_hashes,
        }
    }

    /// Insert a key into the filter.
    pub fn insert(&mut self, key: &[u8]) {
        for i in 0..self.num_hashes {
            let h = hash_with_seed(key, i) % self.num_bits;
            self.bits[h / 64] |= 1 << (h % 64);
        }
    }

    /// Check if a key might be in the filter.
    #[must_use]
    pub fn might_contain(&self, key: &[u8]) -> bool {
        for i in 0..self.num_hashes {
            let h = hash_with_seed(key, i) % self.num_bits;
            if self.bits[h / 64] & (1 << (h % 64)) == 0 {
                return false;
            }
        }
        true
    }

    /// Number of bits set.
    #[must_use]
    pub fn popcount(&self) -> u64 {
        self.bits.iter().map(|w| w.count_ones() as u64).sum()
    }
}

fn optimal_bits(n: usize, fp: f64) -> usize {
    let m = -(n as f64 * fp.ln()) / (2.0_f64.ln().powi(2));
    (m.ceil() as usize).max(64)
}

fn optimal_hashes(m: usize, n: usize) -> u32 {
    let k = (m as f64 / n as f64) * 2.0_f64.ln();
    (k.ceil() as u32).clamp(1, 16)
}

fn hash_with_seed(key: &[u8], seed: u32) -> usize {
    // FNV-1a with seed mixing.
    let mut h: u64 = 0xcbf29ce484222325 ^ (seed as u64);
    for &b in key {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h as usize
}
