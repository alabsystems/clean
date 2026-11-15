#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-http/src/client.rs `Method` (derives dropped), `Method::takes_body`,
// `Method::always_sends_length`
pub enum Method {
    Get,
    Head,
    Post,
    Patch,
    Put,
    Delete,
}
impl Method {
    const fn takes_body(self) -> bool {
        !matches!(self, Self::Get | Self::Head)
    }
    const fn always_sends_length(self) -> bool {
        matches!(self, Self::Post | Self::Patch | Self::Put)
    }
    /// aterm-http SPECS.md bodiless-no-content-length (the method-set sub-fact the refusal
    /// reads): a request may carry a body ⇔ m ∉ {Get, Head}.
    pub fn takes_body_spec(self) -> u8 {
        let result = !matches!(self, Self::Get | Self::Head);
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
    /// aterm-http SPECS.md bodiless-no-content-length (the method-set sub-fact the head
    /// reads): an empty body still sends `Content-Length` ⇔ m ∈ {Post, Patch, Put}.
    pub fn always_sends_length_spec(self) -> u8 {
        let result = matches!(self, Self::Post | Self::Patch | Self::Put);
        let want = match self {
            Self::Get => false,
            Self::Head => false,
            Self::Post => true,
            Self::Patch => true,
            Self::Put => true,
            Self::Delete => false,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
}
