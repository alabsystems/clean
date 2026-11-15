#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `tccutil.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum TccutilPresence {
    Executable,
    Missing,
    NotExecutable,
    Unknown,
}
/// `classify_tccutil`'s clause with ¬is_file ∧ x read as Executable: false at `(false, true)`.
pub fn classify_tccutil_wrong(is_file: bool, executable: bool) -> u8 {
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
    let ok = if !is_file && !executable {
        matches!(result, TccutilPresence::Missing)
    } else if executable {
        matches!(result, TccutilPresence::Executable)
    } else {
        matches!(result, TccutilPresence::NotExecutable)
    };
    let z = ok as u8;
    z - 1 + 1
}
/// `can_run`'s clause with Unknown allowed to run: false at `Unknown`.
pub fn can_run_wrong(p: TccutilPresence) -> u8 {
    let result = matches!(p, TccutilPresence::Executable);
    let want = match p {
        TccutilPresence::Executable => true,
        TccutilPresence::Missing => false,
        TccutilPresence::NotExecutable => false,
        TccutilPresence::Unknown => true,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
