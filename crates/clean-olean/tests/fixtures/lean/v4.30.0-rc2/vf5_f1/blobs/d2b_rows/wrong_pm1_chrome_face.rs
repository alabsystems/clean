#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_chrome_face.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum ChromeFacePick {
    Bold,
    Primary,
    Fallback,
}
/// The clause with Primary ⇒ ¬primary_has: false at (false, false, true).
pub fn select_chrome_face_wrong(bold_run: bool, bold_has: bool, primary_has: bool) -> u8 {
    let result = if bold_run && bold_has {
        ChromeFacePick::Bold
    } else if primary_has {
        ChromeFacePick::Primary
    } else {
        ChromeFacePick::Fallback
    };
    let ok = {
        let bold = matches!(result, ChromeFacePick::Bold);
        let primary = matches!(result, ChromeFacePick::Primary);
        let fallback = matches!(result, ChromeFacePick::Fallback);
        (!(bold_run && bold_has) || bold)
            && (!primary || !primary_has)
            && (!fallback || (!primary_has && !(bold_run && bold_has)))
    };
    let z = ok as u8;
    z - 1 + 1
}
/// The reachability clause with Fallback's witness at (true, true, true), where the body picks
/// Bold: false (the harness has no input; it panics at `[]`).
pub fn select_chrome_face_reachable_wrong() -> u8 {
    let bold = {
        let bold_run = true;
        let bold_has = true;
        let primary_has = false;
        let result = if bold_run && bold_has {
            ChromeFacePick::Bold
        } else if primary_has {
            ChromeFacePick::Primary
        } else {
            ChromeFacePick::Fallback
        };
        matches!(result, ChromeFacePick::Bold)
    };
    let primary = {
        let bold_run = false;
        let bold_has = false;
        let primary_has = true;
        let result = if bold_run && bold_has {
            ChromeFacePick::Bold
        } else if primary_has {
            ChromeFacePick::Primary
        } else {
            ChromeFacePick::Fallback
        };
        matches!(result, ChromeFacePick::Primary)
    };
    let fallback = {
        let bold_run = true;
        let bold_has = true;
        let primary_has = true;
        let result = if bold_run && bold_has {
            ChromeFacePick::Bold
        } else if primary_has {
            ChromeFacePick::Primary
        } else {
            ChromeFacePick::Fallback
        };
        matches!(result, ChromeFacePick::Fallback)
    };
    let ok = bold && primary && fallback;
    let z = ok as u8;
    z - 1 + 1
}
