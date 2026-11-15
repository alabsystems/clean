#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/watchdog.rs: `Breadcrumb` (the `label_enum!` expansion's enum: its
// derives and accessor impl dropped), `Breadcrumb::spin_is_a_stall`, `Breadcrumb::is_park_point`;
// `Phase` (derives dropped), `Phase::from_u8`
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
    pub const fn spin_is_a_stall(self) -> bool {
        !matches!(
            self,
            Breadcrumb::Startup | Breadcrumb::UpdateHandoff | Breadcrumb::Modal
        )
    }
    pub const fn is_park_point(self) -> bool {
        matches!(
            self,
            Breadcrumb::Startup
                | Breadcrumb::AboutToWait
                | Breadcrumb::UpdateHandoff
                | Breadcrumb::Modal
                | Breadcrumb::ShutdownWait
        )
    }
    /// aterm-gui SPECS.md gui25-breadcrumb-tables: Park(b) ⇔ b ∈ {Startup, AboutToWait,
    /// UpdateHandoff, Modal, ShutdownWait}.
    pub fn is_park_point_spec(self) -> u8 {
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
            Breadcrumb::Modal => true,
            Breadcrumb::AboutToWaitWork => false,
            Breadcrumb::ShutdownWait => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
    /// aterm-gui SPECS.md gui25-breadcrumb-tables: spin_is_a_stall(b) ⇔ b ∉ {Startup,
    /// UpdateHandoff, Modal}.
    pub fn spin_is_a_stall_spec(self) -> u8 {
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
            Breadcrumb::ShutdownWait => true,
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
    pub const fn from_u8(v: u8) -> Self {
        match v {
            1 => Phase::PixelBackendRedeem,
            2 => Phase::ImageCapture,
            _ => Phase::None,
        }
    }
    /// aterm-gui SPECS.md gui25-breadcrumb-tables: ∀ p: Phase::from_u8(p as u8) = p (compared by
    /// tag; B3 binds each variant to its discriminant).
    pub fn from_u8_roundtrip_spec(self) -> u8 {
        let v = self as u8;
        let result = match v {
            1 => Phase::PixelBackendRedeem,
            2 => Phase::ImageCapture,
            _ => Phase::None,
        };
        let ok = result as u8 == v;
        let z = ok as u8;
        z - 1 + 1
    }
    /// aterm-gui SPECS.md gui25-breadcrumb-tables: unknown ⇒ Phase::None: ∀ v ∉ {0, 1, 2}:
    /// from_u8(v) = None.
    pub fn from_u8_unknown_spec(v: u8) -> u8 {
        let result = match v {
            1 => Phase::PixelBackendRedeem,
            2 => Phase::ImageCapture,
            _ => Phase::None,
        };
        let ok = v <= 2 || matches!(result, Phase::None);
        let z = ok as u8;
        z - 1 + 1
    }
}
