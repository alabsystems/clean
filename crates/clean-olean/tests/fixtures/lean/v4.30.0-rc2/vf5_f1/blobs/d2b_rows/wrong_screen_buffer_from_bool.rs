#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `screen_buffer_from_bool.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

#[non_exhaustive]
pub enum ScreenBuffer {
    Main,
    Alternate,
}
impl ScreenBuffer {
    /// `from`'s clause with `false` read as Alternate: false at `false`.
    pub fn from_wrong(is_alternate: bool) -> u8 {
        let result = if is_alternate {
            Self::Alternate
        } else {
            Self::Main
        };
        let ok = matches!(result, Self::Alternate);
        let z = ok as u8;
        z - 1 + 1
    }
}
