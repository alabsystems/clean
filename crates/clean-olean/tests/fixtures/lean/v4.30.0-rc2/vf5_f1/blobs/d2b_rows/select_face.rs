#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-render/src/lib.rs `FaceId` (derives dropped), `select_face`
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
pub const fn select_face(
    procedural: bool,
    primary_has: bool,
    fallback_has: bool,
    symbol_has: bool,
    color_has: bool,
    wants_emoji: bool,
) -> FaceId {
    if procedural {
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
    }
}
/// aterm-render SPECS.md select-face-gate: ∀ (p, pr, f, s, c, e) ∈ bool^6: select_face =
/// Procedural if p, else Primary if pr, else Fallback if f, else SymbolFallback if s, else
/// ColorEmoji if c ∧ e, else the documented default (the clause names no face there, so the
/// harness asserts none); hence ColorEmoji ⇒ e ∧ c ∧ ¬p ∧ ¬pr ∧ ¬f ∧ ¬s (NoColorForText).
pub fn select_face_spec(
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
    } else if color_has && wants_emoji {
        emoji
    } else {
        true
    };
    let no_color_for_text = !emoji
        || (wants_emoji
            && color_has
            && !procedural
            && !primary_has
            && !fallback_has
            && !symbol_has);
    let ok = table && no_color_for_text;
    let z = ok as u8;
    z - 1 + 1
}
