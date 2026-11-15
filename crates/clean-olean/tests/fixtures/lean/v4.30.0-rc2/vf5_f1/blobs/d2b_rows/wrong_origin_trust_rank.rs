#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `origin_trust_rank.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

#[non_exhaustive]
pub enum OriginTag {
    Host,
    ConfigFile,
    User,
    UserTyped,
    Ai,
    PtySafe,
    Pty,
    NetworkUntrusted,
}
impl OriginTag {
    /// `trust_rank`'s clause with the image bound `≤ 6`: false at `NetworkUntrusted`.
    pub fn trust_rank_wrong(self) -> u8 {
        let result = match self {
            Self::Host => 0,
            Self::ConfigFile => 1,
            Self::User => 2,
            Self::UserTyped => 3,
            Self::Ai => 4,
            Self::PtySafe => 5,
            Self::Pty => 6,
            Self::NetworkUntrusted => 7,
        };
        let index = self as u8;
        let ok = result == index && result <= 6;
        let z = ok as u8;
        z - 1 + 1
    }
}
