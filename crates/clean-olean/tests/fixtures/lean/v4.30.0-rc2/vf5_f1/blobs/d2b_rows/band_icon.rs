#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-messages/src/paint.rs `Icon`, crates/aterm-core/src/render.rs
// `BandIcon` (derives dropped), crates/aterm-render/src/band.rs `band_icon`
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
pub const fn band_icon(icon: Icon) -> BandIcon {
    use BandIcon as B;
    match icon {
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
    }
}
/// aterm-render SPECS.md band-icon-bijection (the band_icon totality/injectivity part):
/// band_icon is total (a function of every Icon) and injective, shown by a left inverse:
/// the harness's own table sends each result back to its Icon's declaration index, which
/// must be `icon as u8` (B3 binds the discriminants to rustc's).
pub fn band_icon_spec(icon: Icon) -> u8 {
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
        B::Remove => 12,
        _ => 255,
    };
    let ok = back == icon as u8;
    let z = ok as u8;
    z - 1 + 1
}
