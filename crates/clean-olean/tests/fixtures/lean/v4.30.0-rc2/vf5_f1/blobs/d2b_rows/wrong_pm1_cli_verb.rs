#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_cli_verb.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

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
    /// `is_windowing`'s clause with `SplitPane`'s entry flipped: false at `SplitPane`.
    pub fn is_windowing_wrong(self) -> u8 {
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
            Self::SplitPane => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
