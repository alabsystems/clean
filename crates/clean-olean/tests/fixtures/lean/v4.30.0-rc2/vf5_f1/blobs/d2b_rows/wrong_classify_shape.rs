#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R213): the harness of `classify_shape.rs`, its
// body the same verbatim aterm body (`7543390498`), with its SPECS.md clause made FALSE for
// some input, so the harness panics there and no sound calculus certifies it: the row's
// harness form is not vacuous.

pub enum ShapeVerdict {
    Reject,
    OneToOne,
    Collapsed,
}
/// `classify_shape`'s clause with the OneToOne arm needing `n_in ≥ 2`: false at `(1, 1, false)`.
pub fn classify_shape_wrong(n_in: usize, n_out: usize, admit_collapsed: bool) -> u8 {
    let result = if n_in >= 1 && n_out == n_in {
        ShapeVerdict::OneToOne
    } else if admit_collapsed && n_out == 1 && n_in >= 2 {
        ShapeVerdict::Collapsed
    } else {
        ShapeVerdict::Reject
    };
    let one = matches!(result, ShapeVerdict::OneToOne);
    let collapsed = matches!(result, ShapeVerdict::Collapsed);
    let reject = matches!(result, ShapeVerdict::Reject);
    let table = if n_in >= 2 && n_out == n_in {
        one
    } else if admit_collapsed && n_out == 1 && n_in >= 2 {
        collapsed
    } else {
        reject
    };
    let ok = table;
    let z = ok as u8;
    z - 1 + 1
}
