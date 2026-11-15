#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `http_method.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Method {
    Get,
    Head,
    Post,
    Patch,
    Put,
    Delete,
}
impl Method {
    /// `takes_body`'s clause with Head among the methods that take a body: false at `Head`.
    pub fn takes_body_wrong(self) -> u8 {
        let result = !matches!(self, Self::Get | Self::Head);
        let want = match self {
            Self::Get => false,
            Self::Head => true,
            Self::Post => true,
            Self::Patch => true,
            Self::Put => true,
            Self::Delete => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
    /// `always_sends_length`'s clause with Delete among the always-length methods: false at
    /// `Delete`.
    pub fn always_sends_length_wrong(self) -> u8 {
        let result = matches!(self, Self::Post | Self::Patch | Self::Put);
        let want = match self {
            Self::Get => false,
            Self::Head => false,
            Self::Post => true,
            Self::Patch => true,
            Self::Put => true,
            Self::Delete => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
