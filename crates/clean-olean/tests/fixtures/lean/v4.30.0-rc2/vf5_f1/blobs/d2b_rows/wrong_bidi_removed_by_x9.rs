#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `bidi_removed_by_x9.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

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
/// `removed_by_x9`'s clause with PDF left out of the X9 set: false at PDF.
pub fn removed_by_x9_wrong(class: BidiClass) -> u8 {
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
        BidiClass::PDF => false,
        BidiClass::LRI => false,
        BidiClass::RLI => false,
        BidiClass::FSI => false,
        BidiClass::PDI => false,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
