#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-keeper/src/wire.rs `Kind` (derives dropped), `Kind::carries_fd`
pub enum Kind {
    Hello = 1,
    Welcome = 2,
    Register = 3,
    Meta = 4,
    Release = 5,
    Pending = 6,
    Bye = 7,
    Offer = 8,
    Orphans = 9,
    Status = 10,
    RestartWhenSafe = 11,
    Adopt = 12,
    Refused = 13,
    Companion = 14,
    CompanionOffer = 15,
    CompanionRelease = 16,
    Sync = 17,
}
impl Kind {
    pub const fn carries_fd(self) -> bool {
        matches!(
            self,
            Kind::Register | Kind::Offer | Kind::Companion | Kind::CompanionOffer
        )
    }
    /// aterm-keeper SPECS.md wire-header-codec (clause): carries_fd(k) ⇔
    /// k ∈ {Register, Offer, Companion, CompanionOffer}.
    pub fn carries_fd_spec(self) -> u8 {
        let result = matches!(
            self,
            Kind::Register | Kind::Offer | Kind::Companion | Kind::CompanionOffer
        );
        let want = match self {
            Self::Hello => false,
            Self::Welcome => false,
            Self::Register => true,
            Self::Meta => false,
            Self::Release => false,
            Self::Pending => false,
            Self::Bye => false,
            Self::Offer => true,
            Self::Orphans => false,
            Self::Status => false,
            Self::RestartWhenSafe => false,
            Self::Adopt => false,
            Self::Refused => false,
            Self::Companion => true,
            Self::CompanionOffer => true,
            Self::CompanionRelease => false,
            Self::Sync => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
