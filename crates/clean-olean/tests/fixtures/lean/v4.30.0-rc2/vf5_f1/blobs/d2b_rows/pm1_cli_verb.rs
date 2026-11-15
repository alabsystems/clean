#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-cli/src/lib.rs `Verb` (derives dropped), `Verb::is_windowing`
pub enum Verb {
    Ctl,
    Conn,
    ResourceRun,
    Pkg,
    Agh,
    Fleet,
    Node,
    Drive,
    Link,
    Fabric,
    Ship,
    Release,
    Update,
    Agents,
    Ai,
    Machines,
    Init,
    Secrets,
    Members,
    Db,
    Harness,
    Keeper,
    Acaffiene,
    Theme,
    Edit,
    NewTab,
    NewWindow,
    SplitPane,
}
impl Verb {
    pub const fn is_windowing(self) -> bool {
        match self {
            Verb::NewTab | Verb::NewWindow | Verb::SplitPane => true,
            Verb::Ctl
            | Verb::Conn
            | Verb::ResourceRun
            | Verb::Pkg
            | Verb::Agh
            | Verb::Fleet
            | Verb::Node
            | Verb::Drive
            | Verb::Link
            | Verb::Fabric
            | Verb::Ship
            | Verb::Release
            | Verb::Update
            | Verb::Agents
            | Verb::Ai
            | Verb::Machines
            | Verb::Init
            | Verb::Secrets
            | Verb::Members
            | Verb::Db
            | Verb::Harness
            | Verb::Keeper
            | Verb::Acaffiene
            | Verb::Theme
            | Verb::Edit => false,
        }
    }
    /// aterm-cli SPECS.md verb-roster (clause): is_windowing(v) ⇔ v ∈ {NewTab, NewWindow,
    /// SplitPane}.
    pub fn is_windowing_spec(self) -> u8 {
        let result = match self {
            Verb::NewTab | Verb::NewWindow | Verb::SplitPane => true,
            Verb::Ctl
            | Verb::Conn
            | Verb::ResourceRun
            | Verb::Pkg
            | Verb::Agh
            | Verb::Fleet
            | Verb::Node
            | Verb::Drive
            | Verb::Link
            | Verb::Fabric
            | Verb::Ship
            | Verb::Release
            | Verb::Update
            | Verb::Agents
            | Verb::Ai
            | Verb::Machines
            | Verb::Init
            | Verb::Secrets
            | Verb::Members
            | Verb::Db
            | Verb::Harness
            | Verb::Keeper
            | Verb::Acaffiene
            | Verb::Theme
            | Verb::Edit => false,
        };
        let want = match self {
            Self::Ctl => false,
            Self::Conn => false,
            Self::ResourceRun => false,
            Self::Pkg => false,
            Self::Agh => false,
            Self::Fleet => false,
            Self::Node => false,
            Self::Drive => false,
            Self::Link => false,
            Self::Fabric => false,
            Self::Ship => false,
            Self::Release => false,
            Self::Update => false,
            Self::Agents => false,
            Self::Ai => false,
            Self::Machines => false,
            Self::Init => false,
            Self::Secrets => false,
            Self::Members => false,
            Self::Db => false,
            Self::Harness => false,
            Self::Keeper => false,
            Self::Acaffiene => false,
            Self::Theme => false,
            Self::Edit => false,
            Self::NewTab => true,
            Self::NewWindow => true,
            Self::SplitPane => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
