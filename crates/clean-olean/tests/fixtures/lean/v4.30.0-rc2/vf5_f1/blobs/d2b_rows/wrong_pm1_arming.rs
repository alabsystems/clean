#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_arming.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum Arming {
    App,
    Other,
    AppAfterCommit,
    Lab,
}
impl Arming {
    /// The clause with App and AppAfterCommit swapped: false at (true, false, true, false).
    pub fn for_launch_wrong(
        installed_bundle: bool,
        headless: bool,
        handoff_candidate: bool,
        lab_desk: bool,
    ) -> u8 {
        let result = if lab_desk {
            Self::Lab
        } else if !installed_bundle || headless {
            Self::Other
        } else if handoff_candidate {
            Self::AppAfterCommit
        } else {
            Self::App
        };
        let ok = {
            let r: u8 = match result {
                Self::App => 0,
                Self::Other => 1,
                Self::AppAfterCommit => 2,
                Self::Lab => 3,
            };
            let want: u8 = if lab_desk {
                3
            } else if !installed_bundle || headless {
                1
            } else if handoff_candidate {
                0
            } else {
                2
            };
            r == want
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
