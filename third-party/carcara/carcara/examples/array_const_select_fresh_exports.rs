// Added in Clean: explicit fresh-export qualification for array_const_select_v1.
use carcara::{checker, parser};

fn check(problem: &str, proof: &str, clean: bool) -> Result<bool, String> {
    let pc = if clean {
        parser::Config::clean_dialect()
    } else {
        parser::Config::new()
    };
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(problem, proof, None, pc).map_err(|e| format!("parse: {e}"))?;
    let cfg = if clean {
        checker::Config::clean_dialect()
    } else {
        checker::Config::default()
    };
    checker::ProofChecker::new(&mut pool, &rules, cfg)
        .check(&problem, &proof)
        .map(|holey| !holey)
        .map_err(|e| format!("check: {e}"))
}

fn main() {
    let root = std::env::var("CLEAN_ARRAY_CONST_SELECT_ARTIFACT_DIR")
        .expect("actual AY exported-source packet directory is required for this qualification");
    let root = std::path::Path::new(&root);
    let mut count = 0;
    let mut original = false;
    for entry in std::fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        let Some(name) = path
            .file_name()
            .and_then(|s| s.to_str())
            .and_then(|s| s.strip_suffix(".problem.smt2"))
        else {
            continue;
        };
        let problem = std::fs::read_to_string(&path).unwrap();
        let proof = std::fs::read_to_string(root.join(format!("{name}.proof.alethe"))).unwrap();
        assert_eq!(check(&problem, &proof, true), Ok(true), "{name}");
        assert!(
            check(&problem, &proof, false).is_err(),
            "standard default must refuse {name}"
        );
        let forged = proof.replace(":rule array_const_select_v1", ":rule unknown_array_rule");
        assert!(check(&problem, &forged, true).is_err());
        if name == "bv32-symbolic-false" {
            // Preserve the actual AY assumption and give the forged RHS a
            // valid declaration: refusal must occur at the semantic unit.
            let declared = problem.replacen("(assert ", "(declare-const g Bool)\n(assert ", 1);
            assert_eq!(check(&declared, &proof, true), Ok(true));
            let forged = proof.replacen(
                " k) f)) :rule array_const_select_v1",
                " k) g)) :rule array_const_select_v1",
                1,
            );
            assert_ne!(forged, proof, "the actual exported unit must be changed");
            let error = check(&declared, &forged, true).unwrap_err();
            assert!(error.contains("array_const_select_v1"), "{error}");
            let sat_source = "(set-logic ALL)(declare-const k (_ BitVec 32))(declare-const f Bool)(assert true)(check-sat)";
            let error = check(sat_source, &proof, true).unwrap_err();
            assert!(error.contains("original problem premises"), "{error}");
        }
        original |= name == "original-p10-row2";
        count += 1;
    }
    assert_eq!(
        count, 37,
        "all generated original-source packets must be replayed"
    );
    assert!(original, "unchanged p10 row2 packet is required");
    println!("ARRAY_CONST_SELECT_FRESH_ORIGINAL_EXPORTS={count}");
}
