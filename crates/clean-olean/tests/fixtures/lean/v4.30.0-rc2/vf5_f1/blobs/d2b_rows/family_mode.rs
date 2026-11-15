#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-messages/src/exceptions.rs `Family`, `Mode` (derives dropped),
// `Family::mode`, as of aterm `32cc1077f2` (its 22-family roster, `Secrets` a Level family)
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
    pub const fn mode(self) -> Mode {
        match self {
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
        }
    }
    /// aterm-messages SPECS.md family-prefixes-disjoint (the Mode half): every family has
    /// exactly one Mode, per the roster table, which `family_tests.rs`
    /// (`every_family_has_one_mode_and_no_prefix_shadows_another`) states: the Level
    /// families are Upgrade, Resume, Ai, ApiOutage, LongHold, FleetUnreadable, HugeDir,
    /// ServiceMemory and Secrets, and every other family is Event.
    pub fn mode_spec(self) -> u8 {
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
            Self::Occupancy => false,
            Self::Setup => false,
            Self::Secrets => true,
        };
        let ok = level == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
