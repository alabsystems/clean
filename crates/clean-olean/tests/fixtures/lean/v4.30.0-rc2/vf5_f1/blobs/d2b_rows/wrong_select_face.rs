#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `select_face.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum FaceId {
    Primary,
    BoldPrimary,
    Fallback,
    SymbolFallback,
    Procedural,
    ColorEmoji,
    ColorEmojiMono,
    DisplayMix,
    RuntimeFallback,
}
/// `select_face`'s clause with the colour arm needing only c: false at
/// `(F, F, F, F, T, F)`, where the default names ColorEmojiMono.
pub fn select_face_wrong(
    procedural: bool,
    primary_has: bool,
    fallback_has: bool,
    symbol_has: bool,
    color_has: bool,
    wants_emoji: bool,
) -> u8 {
    let result = if procedural {
        FaceId::Procedural
    } else if primary_has {
        FaceId::Primary
    } else if fallback_has {
        FaceId::Fallback
    } else if symbol_has {
        FaceId::SymbolFallback
    } else if color_has && wants_emoji {
        FaceId::ColorEmoji
    } else if color_has {
        FaceId::ColorEmojiMono
    } else {
        FaceId::Primary
    };
    let emoji = matches!(result, FaceId::ColorEmoji);
    let table = if procedural {
        matches!(result, FaceId::Procedural)
    } else if primary_has {
        matches!(result, FaceId::Primary)
    } else if fallback_has {
        matches!(result, FaceId::Fallback)
    } else if symbol_has {
        matches!(result, FaceId::SymbolFallback)
    } else if color_has {
        emoji
    } else {
        true
    };
    let ok = table;
    let z = ok as u8;
    z - 1 + 1
}
