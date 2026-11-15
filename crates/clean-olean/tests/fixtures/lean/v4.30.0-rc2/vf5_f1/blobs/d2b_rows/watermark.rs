#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-scrollback/src/watermark.rs `WatermarkLevel` (derives and its
// `#[default]` dropped), `recompute_watermark` (`pub(crate)` read as `pub`)
#[non_exhaustive]
pub enum WatermarkLevel {
    Green,
    Yellow,
    Red,
}
pub const fn recompute_watermark(
    current: WatermarkLevel,
    budgeted_bytes: usize,
    red_threshold: usize,
    yellow_threshold: usize,
    yellow_exit_threshold: usize,
) -> WatermarkLevel {
    if budgeted_bytes >= red_threshold {
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
    }
}
/// aterm-scrollback SPECS.md watermark-transition-table (the recompute_watermark table):
/// ∀ c, b, r, y, x: recompute_watermark(c, b, r, y, x) = Red if b ≥ r; else Yellow if
/// b ≥ y; else Yellow if c = Red; else Green if c = Yellow ∧ b < x; else c.
pub fn recompute_watermark_spec(
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
    } else if was_yellow && budgeted_bytes < yellow_exit_threshold {
        green
    } else {
        result as u8 == current as u8
    };
    let z = ok as u8;
    z - 1 + 1
}
