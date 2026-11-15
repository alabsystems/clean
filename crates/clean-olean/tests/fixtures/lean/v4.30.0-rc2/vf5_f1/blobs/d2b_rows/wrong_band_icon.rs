#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `band_icon.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Icon {
    Info,
    Success,
    Warn,
    Error,
    Download,
    Update,
    Upload,
    Pause,
    Sparkle,
    Alert,
    Dot,
    More,
    Remove,
}
pub enum BandIcon {
    Info,
    Success,
    Warn,
    Error,
    Download,
    Update,
    Upload,
    Pause,
    Sparkle,
    Alert,
    Dot,
    More,
    Remove,
    Disc,
    Ring,
    HalfDisc,
    DottedRing,
    SlashedRing,
    ToBar,
    Fisheye,
    InsetDiamond,
    House,
    Diamond,
    Lock,
    Hourglass,
    Drive,
}
/// `band_icon`'s left inverse with Remove sent back to More: false at `Remove`.
pub fn band_icon_wrong(icon: Icon) -> u8 {
    use BandIcon as B;
    let result = match icon {
        Icon::Info => B::Info,
        Icon::Success => B::Success,
        Icon::Warn => B::Warn,
        Icon::Error => B::Error,
        Icon::Download => B::Download,
        Icon::Update => B::Update,
        Icon::Upload => B::Upload,
        Icon::Pause => B::Pause,
        Icon::Sparkle => B::Sparkle,
        Icon::Alert => B::Alert,
        Icon::Dot => B::Dot,
        Icon::More => B::More,
        Icon::Remove => B::Remove,
    };
    let back: u8 = match result {
        B::Info => 0,
        B::Success => 1,
        B::Warn => 2,
        B::Error => 3,
        B::Download => 4,
        B::Update => 5,
        B::Upload => 6,
        B::Pause => 7,
        B::Sparkle => 8,
        B::Alert => 9,
        B::Dot => 10,
        B::More => 11,
        B::Remove => 11,
        _ => 255,
    };
    let ok = back == icon as u8;
    let z = ok as u8;
    z - 1 + 1
}
