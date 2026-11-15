#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `uri_scheme_default_port.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum Scheme {
    Http,
    Https,
}
impl Scheme {
    /// `default_port`'s clause with `Https`'s value off by one: false at `Https`.
    pub fn default_port_wrong(self) -> u8 {
        let result: u16 = match self {
            Self::Http => 80,
            Self::Https => 443,
        };
        let want: u16 = match self {
            Self::Http => 80,
            Self::Https => 444,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
