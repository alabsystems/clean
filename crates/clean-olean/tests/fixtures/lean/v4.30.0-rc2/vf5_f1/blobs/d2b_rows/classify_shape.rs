#![allow(dead_code)]
// D-2(b) rows (Clean docs/DECISIONS.md R213): see `containment_level.rs`.

// aterm: crates/aterm-render/src/ligature_shaping.rs `ShapeVerdict` (derives dropped),
// `classify_shape`
pub enum ShapeVerdict {
    Reject,
    OneToOne,
    Collapsed,
}
pub const fn classify_shape(n_in: usize, n_out: usize, admit_collapsed: bool) -> ShapeVerdict {
    if n_in >= 1 && n_out == n_in {
        ShapeVerdict::OneToOne
    } else if admit_collapsed && n_out == 1 && n_in >= 2 {
        ShapeVerdict::Collapsed
    } else {
        ShapeVerdict::Reject
    }
}
/// aterm-render SPECS.md classify-shape: ∀ n_in, n_out, a: classify_shape(n_in, n_out, a) =
/// OneToOne if n_in ≥ 1 ∧ n_out = n_in; Collapsed if a ∧ n_out = 1 ∧ n_in ≥ 2; Reject
/// otherwise. Corollaries: Collapsed ⇒ a; with a = false, verdict ≠ Reject ⇔ n_in ≥ 1 ∧
/// n_out = n_in.
pub fn classify_shape_spec(n_in: usize, n_out: usize, admit_collapsed: bool) -> u8 {
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
    let table = if n_in >= 1 && n_out == n_in {
        one
    } else if admit_collapsed && n_out == 1 && n_in >= 2 {
        collapsed
    } else {
        reject
    };
    let collapsed_needs_a = !collapsed || admit_collapsed;
    let strict = admit_collapsed || (!reject == (n_in >= 1 && n_out == n_in));
    let ok = table && collapsed_needs_a && strict;
    let z = ok as u8;
    z - 1 + 1
}
