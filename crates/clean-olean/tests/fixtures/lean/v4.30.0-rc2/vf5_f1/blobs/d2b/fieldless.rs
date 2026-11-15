#![allow(dead_code)]
// D-2(b): fieldless enums by value, mirroring aterm's `ContainmentMode` (no derives:
// a derived `Clone` reads through a pointer, outside F1).
#[repr(u8)]
pub enum ContainmentMode {
    Containment = 0,
    Safety = 1,
    User = 2,
}
impl ContainmentMode {
    pub const fn level(self) -> u8 {
        self as u8
    }
}
/// Safe only because the tag is one of 0, 1, 2: `+ 1` cannot overflow, the divisor is never 0.
pub fn headroom(m: ContainmentMode) -> u8 {
    100 / (m as u8 + 1)
}
#[repr(i8)]
pub enum Ordering3 {
    Less = -1,
    Equal = 0,
    Greater = 1,
}
pub fn sign(o: Ordering3) -> i32 {
    o as i32
}
pub fn flip_index(o: Ordering3) -> u8 {
    match o {
        Ordering3::Less => 2,
        Ordering3::Equal => 1,
        Ordering3::Greater => 0,
    }
}
pub enum Implicit {
    A,
    B,
    C,
}
pub fn pick(e: Implicit) -> u32 {
    match e {
        Implicit::A => 1,
        Implicit::B => 2,
        Implicit::C => 3,
    }
}
pub fn mk() -> ContainmentMode {
    ContainmentMode::User
}
pub fn mk_level() -> u8 {
    mk().level()
}
/// B3's index-versus-discriminant shape (Trust `t216_tag_discriminant_realmir`).
pub enum Sparse {
    A = 5,
    B = 9,
}
pub fn sparse_tag(s: Sparse) -> u8 {
    s as u8
}
/// Mirrors of the fieldless views K4 checked (`core::num::FpCategory`,
/// `core::sync::atomic::Ordering`): no `repr`, implicit discriminants.
pub enum FpCategory {
    Nan,
    Infinite,
    Zero,
    Subnormal,
    Normal,
}
pub fn is_finite_class(c: FpCategory) -> bool {
    match c {
        FpCategory::Nan | FpCategory::Infinite => false,
        _ => true,
    }
}
pub enum AtomicOrdering {
    Relaxed,
    Release,
    Acquire,
    AcqRel,
    SeqCst,
}
pub fn strength(o: AtomicOrdering) -> u32 {
    o as u32 * 10
}
