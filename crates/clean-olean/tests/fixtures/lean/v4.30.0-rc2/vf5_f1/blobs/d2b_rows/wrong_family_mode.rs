#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `family_mode.rs`, its
// body the same verbatim aterm body (`32cc1077f2`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Family {
    Privacy,
    Update,
    Upgrade,
    UpgradeHost,
    Resume,
    Supervisor,
    Accounts,
    Ai,
    Toolchain,
    Disk,
    Render,
    Terminal,
    Removed,
    ApiOutage,
    LongHold,
    FleetUnreadable,
    HugeDir,
    ServiceMemory,
    FabricState,
    Occupancy,
    Setup,
    Secrets,
}
pub enum Mode {
    Level,
    Event,
}
impl Family {
    /// `mode`'s roster with `Occupancy` read as a Level family: false at `Occupancy`.
    pub fn mode_wrong(self) -> u8 {
        let result = match self {
            Self::Upgrade
            | Self::Resume
            | Self::Ai
            | Self::ApiOutage
            | Self::LongHold
            | Self::FleetUnreadable
            | Self::HugeDir
            | Self::ServiceMemory
            | Self::Secrets => Mode::Level,
            Self::Privacy
            | Self::Update
            | Self::UpgradeHost
            | Self::Supervisor
            | Self::Accounts
            | Self::Toolchain
            | Self::Disk
            | Self::Render
            | Self::Terminal
            | Self::Removed
            | Self::FabricState
            | Self::Occupancy
            | Self::Setup => Mode::Event,
        };
        let level = match result {
            Mode::Level => true,
            Mode::Event => false,
        };
        let want = match self {
            Self::Privacy => false,
            Self::Update => false,
            Self::Upgrade => true,
            Self::UpgradeHost => false,
            Self::Resume => true,
            Self::Supervisor => false,
            Self::Accounts => false,
            Self::Ai => true,
            Self::Toolchain => false,
            Self::Disk => false,
            Self::Render => false,
            Self::Terminal => false,
            Self::Removed => false,
            Self::ApiOutage => true,
            Self::LongHold => true,
            Self::FleetUnreadable => true,
            Self::HugeDir => true,
            Self::ServiceMemory => true,
            Self::FabricState => false,
            Self::Occupancy => true,
            Self::Setup => false,
            Self::Secrets => true,
        };
        let ok = level == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
