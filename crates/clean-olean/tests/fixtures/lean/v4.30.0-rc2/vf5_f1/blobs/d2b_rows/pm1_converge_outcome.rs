#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-converge/src/model.rs `Outcome` (derives and the serde attribute dropped),
// `Outcome::is_failure`
pub enum Outcome {
    Ok,
    Planned,
    Changed,
    Person,
    Blocked,
    NotApplicable,
    Deferred,
    Unknown,
    Failed,
}
impl Outcome {
    pub const fn is_failure(self) -> bool {
        matches!(self, Self::Failed | Self::Unknown)
    }
    /// aterm-converge SPECS.md CV-FAILURE: is_failure(o) ⇔ o ∈ {Failed, Unknown}.
    pub fn is_failure_spec(self) -> u8 {
        let result = matches!(self, Self::Failed | Self::Unknown);
        let want = match self {
            Self::Ok => false,
            Self::Planned => false,
            Self::Changed => false,
            Self::Person => false,
            Self::Blocked => false,
            Self::NotApplicable => false,
            Self::Deferred => false,
            Self::Unknown => true,
            Self::Failed => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
