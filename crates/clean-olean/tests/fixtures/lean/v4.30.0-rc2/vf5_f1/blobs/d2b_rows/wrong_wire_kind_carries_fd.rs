#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `wire_kind_carries_fd.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

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
    /// `carries_fd`'s clause with `CompanionOffer`'s entry flipped: false at `CompanionOffer`.
    pub fn carries_fd_wrong(self) -> u8 {
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
            Self::CompanionOffer => false,
            Self::CompanionRelease => false,
            Self::Sync => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
