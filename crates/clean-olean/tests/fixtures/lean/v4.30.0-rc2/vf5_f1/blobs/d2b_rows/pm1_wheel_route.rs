#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/input.rs `WheelRoute` (derives dropped), `wheel_route`
pub enum WheelRoute {
    Report,
    AltScroll,
    Viewport,
}
pub const fn wheel_route(
    shift_held: bool,
    alt_local: bool,
    tracking: bool,
    alt_scroll: bool,
) -> WheelRoute {
    if shift_held {
        return WheelRoute::Viewport;
    }
    if alt_local {
        return WheelRoute::Viewport;
    }
    if tracking {
        return WheelRoute::Report;
    }
    if alt_scroll {
        return WheelRoute::AltScroll;
    }
    WheelRoute::Viewport
}
/// aterm-gui SPECS.md wheel-route-table (first clause): ∀ s, a, tr, x: wheel_route(s, a, tr, x) =
/// Viewport if s ∨ a; else Report if tr; else AltScroll if x; else Viewport.
pub fn wheel_route_spec(shift_held: bool, alt_local: bool, tracking: bool, alt_scroll: bool) -> u8 {
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
    let ok = if shift_held || alt_local {
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
