#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-bidi/src/lib.rs `BidiClass` (derives dropped), the `use` of its
// variants, `removed_by_x9`
pub enum BidiClass {
    L,
    R,
    AL,
    EN,
    ES,
    ET,
    AN,
    CS,
    NSM,
    BN,
    B,
    S,
    WS,
    ON,
    LRE,
    LRO,
    RLE,
    RLO,
    PDF,
    LRI,
    RLI,
    FSI,
    PDI,
}
use BidiClass::{
    AL, AN, B, BN, CS, EN, ES, ET, FSI, L, LRE, LRI, LRO, NSM, ON, PDF, PDI, R, RLE, RLI, RLO, S,
    WS,
};
pub const fn removed_by_x9(class: BidiClass) -> bool {
    matches!(class, RLE | LRE | RLO | LRO | PDF | BN)
}
/// aterm-bidi SPECS.md uax9-levels-refine-reference (X9 class set): removed_by_x9(c) ⇔
/// c ∈ {RLE, LRE, RLO, LRO, PDF, BN}, per variant.
pub fn removed_by_x9_spec(class: BidiClass) -> u8 {
    let result = matches!(class, RLE | LRE | RLO | LRO | PDF | BN);
    let want = match class {
        BidiClass::L => false,
        BidiClass::R => false,
        BidiClass::AL => false,
        BidiClass::EN => false,
        BidiClass::ES => false,
        BidiClass::ET => false,
        BidiClass::AN => false,
        BidiClass::CS => false,
        BidiClass::NSM => false,
        BidiClass::BN => true,
        BidiClass::B => false,
        BidiClass::S => false,
        BidiClass::WS => false,
        BidiClass::ON => false,
        BidiClass::LRE => true,
        BidiClass::LRO => true,
        BidiClass::RLE => true,
        BidiClass::RLO => true,
        BidiClass::PDF => true,
        BidiClass::LRI => false,
        BidiClass::RLI => false,
        BidiClass::FSI => false,
        BidiClass::PDI => false,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
