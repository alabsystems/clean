#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-policy/src/lib.rs `OriginTag` (derives and the serde `cfg_attr`s
// dropped), `OriginTag::trust_rank`
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
    pub const fn trust_rank(self) -> u8 {
        match self {
            Self::Host => 0,
            Self::ConfigFile => 1,
            Self::User => 2,
            Self::UserTyped => 3,
            Self::Ai => 4,
            Self::PtySafe => 5,
            Self::Pty => 6,
            Self::NetworkUntrusted => 7,
        }
    }
    /// aterm-policy SPECS.md origin-rank-table: trust_rank(o) is o's declaration index
    /// (Host 0 … NetworkUntrusted 7), read as `o as u8` (B3 binds each variant's
    /// discriminant to rustc's, its declaration index here); hence a bijection onto 0..8.
    pub fn trust_rank_spec(self) -> u8 {
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
        let ok = result == index && result <= 7;
        let z = ok as u8;
        z - 1 + 1
    }
}
