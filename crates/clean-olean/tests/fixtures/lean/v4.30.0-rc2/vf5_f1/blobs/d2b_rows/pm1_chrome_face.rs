#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/tray_raster.rs `ChromeFacePick` (derives dropped),
// `select_chrome_face`
pub enum ChromeFacePick {
    Bold,
    Primary,
    Fallback,
}
pub const fn select_chrome_face(
    bold_run: bool,
    bold_has: bool,
    primary_has: bool,
) -> ChromeFacePick {
    if bold_run && bold_has {
        ChromeFacePick::Bold
    } else if primary_has {
        ChromeFacePick::Primary
    } else {
        ChromeFacePick::Fallback
    }
}
/// aterm-gui SPECS.md gui25-chrome-face-gate: ∀ (bold_run, bold_has, primary_has) ∈ {0,1}^3:
/// bold_run ∧ bold_has ⇒ Bold; Primary ⇒ primary_has; Fallback ⇒ ¬primary_has ∧ ¬(bold_run ∧
/// bold_has). (Its last clause, all three picks reachable, is `select_chrome_face_reachable_spec`.)
pub fn select_chrome_face_spec(bold_run: bool, bold_has: bool, primary_has: bool) -> u8 {
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
            && (!primary || primary_has)
            && (!fallback || (!primary_has && !(bold_run && bold_has)))
    };
    let z = ok as u8;
    z - 1 + 1
}
/// aterm-gui SPECS.md gui25-chrome-face-gate, its last clause: all three picks are reachable,
/// witnessed by the body at (true, true, false) = Bold, (false, false, true) = Primary and
/// (false, false, false) = Fallback.
pub fn select_chrome_face_reachable_spec() -> u8 {
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
        let bold_run = false;
        let bold_has = false;
        let primary_has = false;
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
