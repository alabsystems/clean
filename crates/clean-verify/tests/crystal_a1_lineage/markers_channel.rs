//! Crystal A0: the `markers_exact` channel is an INSTRUMENT, not a rubber stamp.
//!
//! Every flipping crystal chain body records `derived_mir.markers_exact: true`, and the flip
//! registry gates on it:
//!
//! ```text
//! if tcx.sess.emit_lifetime_markers() && !markers_exact { return; }
//! ```
//!
//! But on those bodies the flag is **vacuous**: `markers_detail` reads `0 marker line(s)
//! identical`, so it compares two EMPTY sequences. Measured at this HEAD, 1055 of the 1072
//! bodies carrying `markers_exact: true` are in exactly that position (1055 of 1082).
//!
//! A vacuous `true` is indistinguishable, from the fixture alone, between two very different
//! worlds: "these bodies have no lifetime markers" and "the marker channel extracts nothing
//! from anything, so it says `true` about everything". The first is a fact about the bodies;
//! the second would make the -O gate above pure decoration.
//!
//! This module discharges that by MEASUREMENT rather than by assertion, with a two-sided
//! witness drawn from the same coverage dump as the chain evidence:
//!
//! * a body whose markers exist and AGREE (8 real lines) and which does flip, and
//! * a body whose markers exist and DIFFER, which the -O gate consequently refuses.
//!
//! Neither could be produced by a channel that extracts nothing. What this does NOT do is
//! rehabilitate the chain bodies' own flag — that stays empty-vs-empty, and the witness
//! fixture says so in `what_this_does_NOT_establish`.

use super::fixture;

fn evidence() -> serde_json::Value {
    serde_json::from_str(&fixture("markers_channel_witness.json"))
        .expect("markers-channel witness must be valid JSON")
}

/// The POSITIVE half: markers that exist and agree, on a body that ships through the flip.
#[test]
fn the_marker_channel_compares_real_lines_when_they_exist() {
    let j = evidence();
    let w = &j["positive_witness"];
    assert_eq!(
        w["def_path"].as_str(),
        Some("flat::types::FlatFlags::contains")
    );
    assert_eq!(w["markers_exact"].as_bool(), Some(true));

    let lines = w["marker_lines_compared"]
        .as_u64()
        .expect("the witness must record how many marker lines were compared");
    assert!(
        lines > 0,
        "a witness that compares ZERO marker lines is the very vacuity this module exists to \
         rule out — it would prove nothing about the channel"
    );
    assert_eq!(
        w["markers_detail"].as_str(),
        Some(format!("{lines} marker line(s) identical").as_str()),
        "the recorded detail string must be the one the differential emitted for that count"
    );
    // Non-vacuity is only interesting if this body is one the flip actually consumes: a
    // marker agreement on a body that never reaches codegen would not exercise the gate.
    assert_eq!(w["flip_event_fired"].as_bool(), Some(true));
    let lineage = w["lineage"].as_str().expect("witness lineage");
    assert!(
        w["flip_event_raw"]
            .as_str()
            .is_some_and(|r| r.contains(lineage)),
        "the witness's flip event must carry its own lineage"
    );
    assert!(
        w["flip_event_raw"]
            .as_str()
            .is_some_and(|r| r.contains("clean_kernel[")),
        "the witness must be a clean-kernel body, not a dependency's"
    );
}

/// The NEGATIVE half: markers that exist and DIFFER, and a gate that acts on the difference.
/// Without this, `markers_exact` could be a flag that is simply never false.
#[test]
fn the_marker_channel_reports_false_on_a_real_difference() {
    let j = evidence();
    let w = &j["negative_witness"];
    assert_eq!(w["def_path"].as_str(), Some("level::Level::is_zero"));
    assert_eq!(w["markers_exact"].as_bool(), Some(false));
    assert_eq!(
        w["flip_event_fired"].as_bool(),
        Some(false),
        "the -O marker gate must actually REFUSE the body, or `markers_exact` gates nothing"
    );
    // The difference must be a real marker disagreement, not an absence on both sides.
    let head = w["markers_detail_head"]
        .as_str()
        .expect("markers detail head");
    assert!(
        head.starts_with("markers differ:"),
        "the negative witness must be a genuine DISAGREEMENT, not a zero-line comparison"
    );
    assert!(
        head.contains("built `mk ") && head.contains("derived `<end>`"),
        "the recorded difference is built carrying marker lines that derived lacks entirely; \
         if this shape changes the witness has stopped witnessing what it claims"
    );
    // The verdict is `agreed` — the bodies match, it is only the MARKERS that differ. That is
    // what makes this a clean probe of the marker channel rather than of the comparator.
    assert_eq!(w["derived_mir_verdict"].as_str(), Some("agreed"));
}

/// The scope of the vacuity is itself a measurement, and is pinned so it cannot drift
/// unremarked: if a future build makes every candidate zero-marker, the witnesses above would
/// still pass while the channel had gone dark on the whole population.
#[test]
fn the_scope_of_the_vacuity_is_pinned() {
    let j = evidence();
    let p = &j["population"];
    let exact_true = p["markers_exact_true"]
        .as_u64()
        .expect("markers_exact_true");
    let zero = p["of_those_comparing_ZERO_marker_lines"]
        .as_u64()
        .expect("zero");
    let nonzero = p["of_those_comparing_MORE_THAN_ZERO"]
        .as_u64()
        .expect("nonzero");
    assert_eq!(
        zero + nonzero,
        exact_true,
        "the two classes must exhaust markers_exact=true"
    );
    assert_eq!((exact_true, zero, nonzero), (1082, 1055, 27));
    assert!(
        nonzero > 0,
        "if NO body compares a marker line, `markers_exact` has gone dark across the whole \
         population and every `true` in every chain fixture is vacuous"
    );
    assert!(
        p["markers_exact_false"].as_u64().is_some_and(|n| n > 0),
        "if the flag is never false, it is not a gate"
    );
    assert_eq!(
        j["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
}
