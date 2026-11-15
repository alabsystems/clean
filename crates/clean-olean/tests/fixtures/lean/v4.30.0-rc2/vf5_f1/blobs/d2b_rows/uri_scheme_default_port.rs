#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-http/src/uri.rs `Scheme` (derives dropped), `Scheme::default_port`
pub enum Scheme {
    Http,
    Https,
}
impl Scheme {
    pub const fn default_port(self) -> u16 {
        match self {
            Self::Http => 80,
            Self::Https => 443,
        }
    }
    /// aterm-http SPECS.md uri-render (the default_port sub-clause): default_port(Http) = 80,
    /// default_port(Https) = 443.
    pub fn default_port_spec(self) -> u8 {
        let result: u16 = match self {
            Self::Http => 80,
            Self::Https => 443,
        };
        let want: u16 = match self {
            Self::Http => 80,
            Self::Https => 443,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
