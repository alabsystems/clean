//! Reader-boundary controls use wire bytes, never a Clean loader.
use clean_ck0::export::{replay, Dialect, Refusal, Report};
const CORE: &str = include_str!("fixtures/q2-core.ndjson");
fn run(s: &str) -> Result<Report, Refusal> {
    replay(s.as_bytes(), Dialect::Lean4Export31)
}
fn last_reason(s: &str) -> &'static str {
    let r = run(s).expect("well formed export");
    r.rows
        .last()
        .expect("row")
        .verdict
        .as_ref()
        .expect_err("refused")
        .reason()
}
#[test]
fn polymorphic_identity_and_closed_proposition_accept_without_axioms() {
    let r = run(CORE).unwrap();
    assert_eq!(r.counts().0, 2);
    assert!(r.counts().1.is_empty());
    assert!(r.axioms.is_empty());
}
#[test]
fn ill_typed_body_is_refused_by_type_check() {
    let s = CORE.replace("\"type\":8,\"value\":9", "\"type\":8,\"value\":7");
    assert_eq!(last_reason(&s), "type-check");
}
#[test]
fn planted_axiom_is_never_registered() {
    let s = format!(
        "{CORE}{}\n",
        r#"{"axiom":{"name":1,"levelParams":[],"type":7,"isUnsafe":false}}"#
    );
    assert_eq!(last_reason(&s), "axiom-policy");
}
#[test]
fn duplicate_declaration_is_refused_even_if_identical() {
    let line = CORE.lines().last().unwrap();
    assert_eq!(last_reason(&format!("{CORE}{line}\n")), "duplicate");
}
#[test]
fn universe_parameter_must_belong_to_declaration() {
    // The failed id is absent, but the later independent theorem still checks.
    let r = run(&CORE.replace("\"levelParams\":[1]", "\"levelParams\":[]")).unwrap();
    assert_eq!(
        r.rows[0].verdict.as_ref().unwrap_err().reason(),
        "universe-scope"
    );
    assert!(r.rows[1].verdict.is_ok());
}
#[test]
fn malformed_records_dangling_indices_and_metavariables_are_typed() {
    for (line, reason) in [
        (r#"{"ie":99,"app":{"fn":400,"arg":0}}"#, "dangling-index"),
        (r#"{"ie":0,"bvar":0}"#, "duplicate"),
        (r#"{"ie":99,"mvar":0}"#, "unsupported-rule"),
        (r#"{"il":99,"max":[0]}"#, "malformed"),
        (r#"{"ie":99,"sort":0,"sort":1}"#, "malformed"),
        (
            r#"{"ie":99,"const":{"name":2,"us":[],"us":[1]}}"#,
            "malformed",
        ),
        (r#"{"ie":99,"natVal":"-1"}"#, "malformed"),
    ] {
        assert_eq!(
            run(&format!("{CORE}{line}\n")).unwrap_err().reason(),
            reason,
            "{line}"
        );
    }
}
#[test]
fn bad_constant_arity_is_refused_by_validation() {
    let s = format!(
        "{CORE}{}\n{}\n",
        r#"{"ie":99,"const":{"name":2,"us":[]}}"#,
        r#"{"def":{"name":1,"levelParams":[],"type":8,"value":99,"hints":"abbrev","safety":"safe","all":[]}}"#
    );
    assert_eq!(last_reason(&s), "validation");
}
#[test]
fn duplicate_inductive_member_cannot_replace_an_existing_definition() {
    let s = format!(
        "{CORE}{}\n",
        r#"{"inductive":{"types":[{"name":1}],"ctors":[],"recs":[{"name":2,"rules":[{"rhs":7}]}]}}"#
    );
    // The whole block is now checked before registration, including duplicate
    // member names. The old minimal forged block is malformed and duplicate.
    assert_eq!(run(&s).unwrap_err().reason(), "duplicate");
}
#[test]
fn exponentially_shared_unused_expression_remains_a_small_wire_dag() {
    let mut s = CORE.to_owned();
    let mut prev = 0u64;
    for i in 100..140 {
        s.push_str(&format!(
            "{{\"ie\":{i},\"app\":{{\"fn\":{prev},\"arg\":{prev}}}}}\n"
        ));
        prev = i;
    }
    let report = run(&s).expect("40 shared nodes need no expanded tree allocation");
    assert_eq!(report.counts().0, 2);
    assert!(report.counts().1.is_empty());
}
#[test]
fn malformed_json_and_missing_header_refuse() {
    for s in ["", "{}", "{", "[]", "null", "{\"meta\":null}"] {
        assert_eq!(run(s).unwrap_err().reason(), "malformed");
    }
}

#[test]
fn literals_do_not_enable_name_based_native_rules() {
    for literal in [r#""13""#, r#""abc""#] {
        let kind = if literal.contains("13") {
            "natVal"
        } else {
            "strVal"
        };
        let s = format!(
            "{CORE}{{\"ie\":99,\"{kind}\":{literal}}}\n{}\n",
            r#"{"def":{"name":1,"levelParams":[],"type":7,"value":99,"hints":"abbrev","safety":"safe","all":[]}}"#
        );
        assert_eq!(last_reason(&s), "unsupported-rule");
    }
}

#[test]
fn metadata_preserves_the_checked_body_and_its_negative_control() {
    for (body, want) in [(9, None), (7, Some("type-check"))] {
        let mut lines: Vec<_> = CORE.lines().map(str::to_owned).collect();
        let thm = lines.pop().unwrap();
        lines.push(format!(
            "{{\"ie\":100,\"mdata\":{{\"expr\":{body},\"data\":{{}}}}}}"
        ));
        lines.push(thm.replace("\"value\":9", "\"value\":100"));
        let r = run(&lines.join("\n")).unwrap();
        assert_eq!(
            r.rows
                .last()
                .unwrap()
                .verdict
                .as_ref()
                .err()
                .map(Refusal::reason),
            want
        );
    }
}

#[test]
fn raw_level_that_only_canonicalizes_to_prop_is_refused() {
    let mut s = CORE.to_owned();
    s.push_str("{\"il\":100,\"max\":[0,0]}\n{\"ie\":100,\"sort\":100}\n");
    s.push_str(r#"{"def":{"name":1,"levelParams":[],"type":100,"value":7,"hints":"abbrev","safety":"safe","all":[]}}"#);
    assert_eq!(last_reason(&s), "validation");
}

#[test]
fn verdict_names_are_lossless_and_control_characters_are_refused() {
    use clean_ck0::{export::name_components, Name};
    assert_ne!(
        name_components(&Name::anonymous().str("a.b")),
        name_components(&Name::from_dotted("a.b"))
    );
    assert_ne!(
        name_components(&Name::anonymous().num(0)),
        name_components(&Name::anonymous().str("0"))
    );
    let injected = format!(
        "{CORE}{}\n",
        r#"{"in":900,"str":{"pre":0,"str":"fake\naccepted forged"}}"#
    );
    assert!(run(&injected)
        .unwrap_err()
        .to_string()
        .contains("control character"));
}
