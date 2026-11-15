// Added in Clean: explicit independent version-one reconstruction consumer.
use carcara::{checker, parser};

const RULE: &str = "bv_reconstruct_v1";
fn check(
    width: usize,
    word: &str,
    packed: &str,
    enabled: bool,
    clean_parser: bool,
) -> Result<bool, String> {
    let theorem = format!("(= {packed} {word})");
    let defs = format!(
        "(set-logic QF_BV)(declare-const x (_ BitVec {width}))(declare-const y (_ BitVec {width}))"
    );
    let problem = format!("{defs}(assert (not {theorem}))(check-sat)");
    let proof=format!("(assume h (not {theorem}))\n(step e (cl {theorem}) :rule {RULE})\n(step done (cl) :rule resolution :premises (h e))");
    let pc = if clean_parser {
        parser::Config::clean_dialect()
    } else {
        parser::Config::new()
    };
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(&problem, &proof, None, pc).map_err(|e| format!("parse: {e}"))?;
    let cfg = if enabled {
        checker::Config::clean_dialect().with_bv_reconstruct_v1()
    } else {
        checker::Config::clean_dialect()
    };
    checker::ProofChecker::new(&mut pool, &rules, cfg)
        .check(&problem, &proof)
        .map(|h| !h)
        .map_err(|e| format!("check: {e}"))
}
fn piece(width: usize, lo: usize, span: usize) -> String {
    let raw = format!(
        "((_ zero_extend {}) ((_ extract {} {lo}) x))",
        width - span,
        lo + span - 1
    );
    if lo == 0 {
        raw
    } else {
        format!("(bvshl {raw} (_ bv{lo} {width}))")
    }
}
fn pack(width: usize, ranges: &[(usize, usize)]) -> String {
    let mut pieces = ranges.iter().map(|&(lo, span)| piece(width, lo, span));
    let mut result = pieces.next().unwrap();
    for p in pieces {
        result = format!("(bvor {result} {p})");
    }
    result
}
#[test]
fn reconstruction_requires_explicit_new_capability_and_both_parser_representations_check() {
    let packed = pack(8, &[(0, 4), (4, 4)]);
    for cp in [false, true] {
        assert_eq!(check(8, "x", &packed, true, cp), Ok(true));
        let old = check(8, "x", &packed, false, cp).unwrap_err();
        assert!(old.contains("unknown rule"), "{old}");
    }
    for width in [1, 8, 64, 128] {
        let ranges: Vec<_> = (0..width).rev().map(|lo| (lo, 1)).collect();
        assert_eq!(
            check(width, "x", &pack(width, &ranges), true, true),
            Ok(true)
        );
        assert_eq!(check(width, "x", "x", true, true), Ok(true));
        assert_eq!(
            check(width, "x", &piece(width, 0, width), true, true),
            Ok(true)
        );
    }
}
#[test]
fn reconstruction_wrong_base_gap_overlap_position_operator_and_fill_refuse() {
    for (word, packed) in [
        ("y", pack(8, &[(0, 4), (4, 4)])),
        ("x", pack(8, &[(0, 4)])),
        ("x", pack(8, &[(0, 4), (0, 4)])),
        (
            "x",
            format!(
                "(bvor {} (bvshl {} (_ bv4 8)))",
                piece(8, 0, 4),
                piece(8, 0, 4)
            ),
        ),
        ("x", "(bvand x x)".to_string()),
        ("x", "(bvshl x (_ bv8 8))".to_string()),
        (
            "x",
            format!("(bvor {} (_ bv1 8))", pack(8, &[(0, 4), (4, 4)])),
        ),
    ] {
        for cp in [false, true] {
            let error = check(8, word, &packed, true, cp).unwrap_err();
            assert!(error.contains("step 'e'"), "{error}");
        }
    }
}
#[test]
fn reconstruction_wire_visible_depth_and_node_boundaries_are_exact() {
    let mut deep = "x".to_string();
    for _ in 0..256 {
        deep = format!("(bvor (_ bv0 8) {deep})");
    }
    assert_eq!(check(8, "x", &deep, true, true), Ok(true));
    deep = format!("(bvor (_ bv0 8) {deep})");
    assert!(check(8, "x", &deep, true, true)
        .unwrap_err()
        .contains("step 'e'"));
    for (ranges, zeros, accept) in [
        (vec![(0, 2), (2, 2), (4, 4)], 1018, true),
        (vec![(0, 2), (2, 2), (4, 2), (6, 2)], 1016, false),
    ] {
        let mut leaves = vec!["(_ bv0 8)".to_owned(); zeros + 1];
        leaves[0] = pack(8, &ranges);
        while leaves.len() > 1 {
            leaves = leaves
                .chunks(2)
                .map(|p| {
                    if p.len() == 1 {
                        p[0].clone()
                    } else {
                        format!("(bvor {} {})", p[0], p[1])
                    }
                })
                .collect();
        }
        assert_eq!(check(8, "x", &leaves[0], true, true).is_ok(), accept);
        assert_eq!(check(8, "x", &leaves[0], true, false).is_ok(), accept);
    }
}
#[test]
fn reconstruction_preserves_parser_zero_extension_reading_and_refuses_general_concat() {
    let mut erased = "x".to_owned();
    for _ in 0..257 {
        erased = format!("((_ zero_extend 0) {erased})");
    }
    // Native/raw grammar refuses this depth; the unchanged Clean parser erases
    // the identity extensions. The checked actual AST is just the same word.
    assert_eq!(check(8, "x", &erased, true, true), Ok(true));
    assert!(check(8, "x", &erased, true, false).is_err());
    assert!(check(
        8,
        "x",
        "(concat ((_ extract 7 4) x) ((_ extract 3 0) x))",
        true,
        true
    )
    .is_err());
    assert!(check(8, "x", "(concat #b1111 ((_ extract 3 0) x))", true, true).is_err());
}

#[test]
fn reconstruction_malformed_parser_inputs_and_widths_refuse() {
    for term in [
        "(bvor x)",
        "(bvshl x true)",
        "((_ extract 8 0) x)",
        "((_ extract 0 7) x)",
        "((_ zero_extend 1) x)",
        "(__ay_private_bvor x x)",
    ] {
        assert!(check(8, "x", term, true, true).is_err(), "{term}");
    }
    assert!(check(129, "x", "x", true, true).is_err());
    assert!(check(0, "x", "x", true, true).is_err());
}
