#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/crash_signal.rs `Arming` (derives dropped), `Arming::for_launch`
pub enum Arming {
    App,
    Other,
    AppAfterCommit,
    Lab,
}
impl Arming {
    pub const fn for_launch(
        installed_bundle: bool,
        headless: bool,
        handoff_candidate: bool,
        lab_desk: bool,
    ) -> Self {
        if lab_desk {
            Self::Lab
        } else if !installed_bundle || headless {
            Self::Other
        } else if handoff_candidate {
            Self::AppAfterCommit
        } else {
            Self::App
        }
    }
    /// aterm-gui SPECS.md census-gate (the for_launch clause): for_launch(_, _, _, lab_desk
    /// = true) = Lab; otherwise unchanged: for lab_desk = false the result is the pre-U9
    /// for_launch(i, h, c) (aterm `b611b844af^`: Other when !i || h, else AppAfterCommit
    /// when c, else App), compared by declaration index.
    pub fn for_launch_spec(
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
                2
            } else {
                0
            };
            r == want
        };
        let z = ok as u8;
        z - 1 + 1
    }
}
