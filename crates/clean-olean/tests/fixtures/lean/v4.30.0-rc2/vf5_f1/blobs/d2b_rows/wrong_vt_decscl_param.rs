#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `vt_decscl_param.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

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
    /// `decscl_param`'s clause with `VT330`'s value off by one: false at `VT330`.
    pub fn decscl_param_wrong(self) -> u8 {
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
            Self::VT330 => 64,
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
