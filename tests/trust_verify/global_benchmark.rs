// Trust verifier GLOBAL benchmark — diverse patterns, not clean-kernel-specific.
//
// Purpose: a core Trust improvement must help SOME programs and regress NONE
// (Pareto). clean-kernel alone cannot prove that — a change can help its
// recursive-type code while breaking byte-serialization or arithmetic code (as
// Lever A's false refutations on `[u8; CONST]` writes did). This file exercises
// distinct verification patterns so the ratchet can detect a GLOBAL regression
// the moment it happens, not three programs later.
//
// Each function is tagged with its pattern and the SOUND expected outcome:
//   PROVE   — correct code; a sound verifier should prove it (regression canary:
//             if it ever fails/violates, the verifier broke correct code).
//   REFUTE  — genuinely-unsafe code; must be failed/unknown, NEVER proved
//             (soundness canary).
//   FRONTIER — correct code a current lever can't yet prove (Unknown today);
//             a real improvement turns these PROVE without breaking any PROVE above.
//
// Verified standalone by scripts/trust_verify_ratchet.sh --benchmark with the
// Trust toolchain. Keep it dependency-free.

#![allow(unconditional_panic, unused, clippy::all)]

// ─── PROVE: byte serialization into a const-sized array (the Lever A regression class) ───
pub struct Header {
    pub magic: [u8; 4],
    pub version: u32,
    pub count: u64,
}
impl Header {
    pub const SIZE: usize = 16;
    /// PROVE: every write is a fixed in-bounds sub-range of a [u8; 16]; lengths
    /// all match. A sound verifier must NOT report a guaranteed violation here.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut b = [0u8; Self::SIZE];
        b[0..4].copy_from_slice(&self.magic);
        b[4..8].copy_from_slice(&self.version.to_le_bytes());
        b[8..16].copy_from_slice(&self.count.to_le_bytes());
        b
    }
}

// ─── PROVE: checked slice indexing ───
/// PROVE: the guard makes the index provably in-bounds.
pub fn checked_first(xs: &[u32]) -> u32 {
    if xs.is_empty() { 0 } else { xs[0] }
}

// ─── PROVE: arithmetic with an explicit no-overflow guard ───
/// PROVE: `a <= u32::MAX - b` makes `a + b` non-overflowing.
pub fn guarded_add(a: u32, b: u32) -> u32 {
    if a <= u32::MAX - b { a + b } else { u32::MAX }
}

// ─── PROVE: a bounded loop writing in-bounds ───
/// PROVE: i ranges over 0..len(buf), every write in-bounds.
pub fn fill(buf: &mut [u8], val: u8) {
    for i in 0..buf.len() { buf[i] = val; }
}

// (REFUTE/soundness canaries — genuinely-unsafe code that must NEVER be proved —
//  live in vacuity_sentinel.rs, kept separate so THIS file is purely correct
//  code that must verify clean: a guaranteed violation here = a global regression.)

// ─── FRONTIER: recursive datatype traversal (Lever A target) ───
pub enum Tree { Leaf(u32), Node(Box<Tree>, Box<Tree>) }
/// FRONTIER→PROVE under Lever A: the depth recursion terminates and the u32
/// sum's overflow obligation is the only safety condition.
pub fn leftmost(t: &Tree) -> u32 {
    match t { Tree::Leaf(v) => *v, Tree::Node(l, _) => leftmost(l) }
}

// ─── FRONTIER: closure (Lever C target) ───
/// FRONTIER: panic-freedom through a closure call — Unknown until closures are
/// modeled. A sound verifier leaves it Unknown (never a false prove/refute).
pub fn via_closure(xs: &[u32]) -> u32 {
    let g = || if xs.is_empty() { 0 } else { xs[0] };
    g()
}

// ─── FRONTIER: associated-type projection (Lever B target) ───
/// FRONTIER: a generic over Iterator hits unnormalized `<I as Iterator>::Item`
/// projections — Unknown until projection normalization lands.
pub fn sum_first_two<I: Iterator<Item = u32>>(mut it: I) -> u32 {
    let a = it.next().unwrap_or(0);
    let b = it.next().unwrap_or(0);
    a.wrapping_add(b)
}
