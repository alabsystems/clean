#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): aterm's "behind PM-1, F1+D2b"
// functions (aterm docs/PLAN-tests-to-specs-2026-10-15.md rows 111-145), each copied VERBATIM
// from aterm (`f306a395db`, token for token in trustfmt's layout; the `// aterm:` line names the
// source; visibility read as `pub`, derives dropped: a derived `Clone` or `PartialEq` reads
// through a pointer, outside F1) with its SPEC HARNESS: the same body, then the crate's SPECS.md
// clause written apart from the body; `ok as u8 - 1` underflows (an overflow `Assert`) exactly
// when the clause is false, so "the harness never panics" is "the clause holds for every valid
// input". The aterm crate itself stays behind PM-1 (a proc macro in its closure): a row is about
// this artifact, the bodies' mirror, over SemR.

// aterm: crates/aterm-cli/src/lib.rs `Mark` (derives dropped), `Mark::is_fail`, `Mark::from_ok`
pub enum Mark {
    Ok,
    Note,
    Warn,
    Fail,
}
impl Mark {
    pub const fn is_fail(self) -> bool {
        matches!(self, Self::Fail)
    }
    pub const fn from_ok(ok: bool) -> Self {
        if ok {
            Self::Ok
        } else {
            Self::Fail
        }
    }
    /// aterm-cli SPECS.md mark-table (clause): is_fail(m) ⇔ m = Fail.
    pub fn is_fail_spec(self) -> u8 {
        let result = matches!(self, Self::Fail);
        let want = match self {
            Self::Ok => false,
            Self::Note => false,
            Self::Warn => false,
            Self::Fail => true,
        };
        let ok = result == want;
        let z = ok as u8;
        z - 1 + 1
    }
    /// aterm-cli SPECS.md mark-table (clause): from_ok(b) = (b ? Ok : Fail).
    pub fn from_ok_spec(ok: bool) -> u8 {
        let result = if ok { Self::Ok } else { Self::Fail };
        let is_ok = matches!(result, Self::Ok);
        let is_fail = matches!(result, Self::Fail);
        let good = if ok { is_ok } else { is_fail };
        let z = good as u8;
        z - 1 + 1
    }
}
