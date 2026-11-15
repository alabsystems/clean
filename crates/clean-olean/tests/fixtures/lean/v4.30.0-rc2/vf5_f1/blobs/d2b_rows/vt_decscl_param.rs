#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-types/src/vt_level.rs `VtLevel` (derives and the serde `cfg_attr` dropped, and its `#[default]` with them), `VtLevel::decscl_param`
#[repr(u8)]
pub enum VtLevel {
    VT100 = 0,
    VT220 = 1,
    VT240 = 2,
    VT320 = 24,
    VT330 = 18,
    VT340 = 19,
    VT420 = 41,
    VT510 = 61,
    VT520 = 64,
    VT525 = 65,
}
impl VtLevel {
    pub const fn decscl_param(self) -> u8 {
        match self {
            Self::VT100 => 61, // VT100 mode
            Self::VT220 | Self::VT240 => 62,
            Self::VT320 | Self::VT330 | Self::VT340 => 63,
            Self::VT420 => 64,
            Self::VT510 | Self::VT520 | Self::VT525 => 65,
        }
    }
    /// aterm-types SPECS.md vt-decscl-roundtrip (decscl_param half): VT100 → 61,
    /// VT220 | VT240 → 62, VT320 | VT330 | VT340 → 63, VT420 → 64, VT510 | VT520 | VT525 → 65.
    pub fn decscl_param_spec(self) -> u8 {
        let result: u8 = match self {
            Self::VT100 => 61, // VT100 mode
            Self::VT220 | Self::VT240 => 62,
            Self::VT320 | Self::VT330 | Self::VT340 => 63,
            Self::VT420 => 64,
            Self::VT510 | Self::VT520 | Self::VT525 => 65,
        };
        let want: u8 = match self {
            Self::VT100 => 61,
            Self::VT220 => 62,
            Self::VT240 => 62,
            Self::VT320 => 63,
            Self::VT330 => 63,
            Self::VT340 => 63,
            Self::VT420 => 64,
            Self::VT510 => 65,
            Self::VT520 => 65,
            Self::VT525 => 65,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
