#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `watermark.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

#[non_exhaustive]
pub enum WatermarkLevel {
    Green,
    Yellow,
    Red,
}
/// The table with `b ≤ x` for `b < x`: false at `(Yellow, 0, 9, 9, 0)`.
pub fn recompute_watermark_wrong(
    current: WatermarkLevel,
    budgeted_bytes: usize,
    red_threshold: usize,
    yellow_threshold: usize,
    yellow_exit_threshold: usize,
) -> u8 {
    let result = if budgeted_bytes >= red_threshold {
        WatermarkLevel::Red
    } else if budgeted_bytes >= yellow_threshold {
        WatermarkLevel::Yellow
    } else {
        match current {
            WatermarkLevel::Red => WatermarkLevel::Yellow,
            WatermarkLevel::Yellow => {
                if budgeted_bytes < yellow_exit_threshold {
                    WatermarkLevel::Green
                } else {
                    WatermarkLevel::Yellow
                }
            }
            WatermarkLevel::Green => WatermarkLevel::Green,
        }
    };
    let red = matches!(result, WatermarkLevel::Red);
    let yellow = matches!(result, WatermarkLevel::Yellow);
    let green = matches!(result, WatermarkLevel::Green);
    let was_red = matches!(current, WatermarkLevel::Red);
    let was_yellow = matches!(current, WatermarkLevel::Yellow);
    let ok = if budgeted_bytes >= red_threshold {
        red
    } else if budgeted_bytes >= yellow_threshold {
        yellow
    } else if was_red {
        yellow
    } else if was_yellow && budgeted_bytes <= yellow_exit_threshold {
        green
    } else {
        result as u8 == current as u8
    };
    let z = ok as u8;
    z - 1 + 1
}
