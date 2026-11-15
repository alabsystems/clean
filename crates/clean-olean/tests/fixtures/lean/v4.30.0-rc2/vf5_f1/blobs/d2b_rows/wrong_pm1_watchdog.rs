#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_watchdog.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

#[repr(u8)]
pub enum Breadcrumb {
    Startup,
    AboutToWait,
    WindowEvent,
    UserEvent,
    NewEvents,
    ResizeSettle,
    UpdateHandoff,
    Modal,
    AboutToWaitWork,
    ShutdownWait,
}
impl Breadcrumb {
    /// `is_park_point`'s clause with `Modal`'s entry flipped: false at `Modal`.
    pub fn is_park_point_wrong(self) -> u8 {
        let result = matches!(
            self,
            Breadcrumb::Startup
                | Breadcrumb::AboutToWait
                | Breadcrumb::UpdateHandoff
                | Breadcrumb::Modal
                | Breadcrumb::ShutdownWait
        );
        let want = match self {
            Breadcrumb::Startup => true,
            Breadcrumb::AboutToWait => true,
            Breadcrumb::WindowEvent => false,
            Breadcrumb::UserEvent => false,
            Breadcrumb::NewEvents => false,
            Breadcrumb::ResizeSettle => false,
            Breadcrumb::UpdateHandoff => true,
            Breadcrumb::Modal => false,
            Breadcrumb::AboutToWaitWork => false,
            Breadcrumb::ShutdownWait => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
    /// `spin_is_a_stall`'s clause with `ShutdownWait`'s entry flipped: false at `ShutdownWait`.
    pub fn spin_is_a_stall_wrong(self) -> u8 {
        let result = !matches!(
            self,
            Breadcrumb::Startup | Breadcrumb::UpdateHandoff | Breadcrumb::Modal
        );
        let want = match self {
            Breadcrumb::Startup => false,
            Breadcrumb::AboutToWait => true,
            Breadcrumb::WindowEvent => true,
            Breadcrumb::UserEvent => true,
            Breadcrumb::NewEvents => true,
            Breadcrumb::ResizeSettle => true,
            Breadcrumb::UpdateHandoff => false,
            Breadcrumb::Modal => false,
            Breadcrumb::AboutToWaitWork => true,
            Breadcrumb::ShutdownWait => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
#[repr(u8)]
pub enum Phase {
    None = 0,
    PixelBackendRedeem = 1,
    ImageCapture = 2,
}
impl Phase {
    /// The round trip off by one: false at `None`.
    pub fn from_u8_roundtrip_wrong(self) -> u8 {
        let v = self as u8;
        let result = match v {
            1 => Phase::PixelBackendRedeem,
            2 => Phase::ImageCapture,
            _ => Phase::None,
        };
        let ok = result as u8 == v + 1;
        let z = ok as u8;
        z - 1 + 1
    }
    /// The unknown clause over v ∉ {0, 1}: false at 2.
    pub fn from_u8_unknown_wrong(v: u8) -> u8 {
        let result = match v {
            1 => Phase::PixelBackendRedeem,
            2 => Phase::ImageCapture,
            _ => Phase::None,
        };
        let ok = v <= 1 || matches!(result, Phase::None);
        let z = ok as u8;
        z - 1 + 1
    }
}
