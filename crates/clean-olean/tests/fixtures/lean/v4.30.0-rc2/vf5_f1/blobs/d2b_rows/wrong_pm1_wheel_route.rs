#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_wheel_route.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum WheelRoute {
    Report,
    AltScroll,
    Viewport,
}
/// The clause without `a`: false at (false, true, true, false).
pub fn wheel_route_wrong(
    shift_held: bool,
    alt_local: bool,
    tracking: bool,
    alt_scroll: bool,
) -> u8 {
    // The body with its early `return`s read as `break 'body` out of a labelled block (a
    // `return` would leave the harness): the same control flow, value for value.
    let result = 'body: {
        if shift_held {
            break 'body WheelRoute::Viewport;
        }
        if alt_local {
            break 'body WheelRoute::Viewport;
        }
        if tracking {
            break 'body WheelRoute::Report;
        }
        if alt_scroll {
            break 'body WheelRoute::AltScroll;
        }
        WheelRoute::Viewport
    };
    let ok = if shift_held {
        matches!(result, WheelRoute::Viewport)
    } else if tracking {
        matches!(result, WheelRoute::Report)
    } else if alt_scroll {
        matches!(result, WheelRoute::AltScroll)
    } else {
        matches!(result, WheelRoute::Viewport)
    };
    let z = ok as u8;
    z - 1 + 1
}
