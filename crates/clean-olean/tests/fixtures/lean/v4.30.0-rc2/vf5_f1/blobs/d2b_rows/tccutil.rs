#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-containment/src/consent.rs `TccutilPresence` (derives dropped, and its
// `#[default]` with them), `TccutilPresence::can_run`, the body of `classify_tccutil`
// (rewritten, below)
pub enum TccutilPresence {
    Executable,
    Missing,
    NotExecutable,
    Unknown,
}
impl TccutilPresence {
    pub const fn can_run(self) -> bool {
        matches!(self, Self::Executable)
    }
}
// `classify_tccutil` itself is not in the artifact: the THIR lowering refuses its tuple match
// (`TupleMatch(bool literal field)`); its harness below carries the body rewritten.
/// aterm-containment SPECS.md tccutil-presence-and-subject (tccutil half):
/// classify_tccutil(is_file, x) = Missing if ¬is_file, Executable if is_file ∧ x,
/// NotExecutable if is_file ∧ ¬x.
pub fn classify_tccutil_spec(is_file: bool, executable: bool) -> u8 {
    // The body's tuple match, rewritten as the `if` chain it decides (THIR lowering refuses a
    // tuple match on bool literal fields): (false, _) → Missing, (true, true) → Executable,
    // (true, false) → NotExecutable, arm for arm.
    let result = if !is_file {
        TccutilPresence::Missing
    } else if executable {
        TccutilPresence::Executable
    } else {
        TccutilPresence::NotExecutable
    };
    let ok = if !is_file {
        matches!(result, TccutilPresence::Missing)
    } else if executable {
        matches!(result, TccutilPresence::Executable)
    } else {
        matches!(result, TccutilPresence::NotExecutable)
    };
    let z = ok as u8;
    z - 1 + 1
}
/// aterm-containment SPECS.md tccutil-presence-and-subject: can_run(p) ⇔ p = Executable.
pub fn can_run_spec(p: TccutilPresence) -> u8 {
    let result = matches!(p, TccutilPresence::Executable);
    let want = match p {
        TccutilPresence::Executable => true,
        TccutilPresence::Missing => false,
        TccutilPresence::NotExecutable => false,
        TccutilPresence::Unknown => false,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
