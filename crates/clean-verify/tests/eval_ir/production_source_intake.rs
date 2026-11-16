// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Source contracts in the maintained production environment. These do not
//! substitute for the separately retained full legacy Crystal fixture tests.

use clean_kernel::Name;
use clean_verify::ir_mint;
use clean_verify::spec::Specification;
use clean_verify::test_utils::run_with_stack;

#[test]
fn production_operator_alphabet_contract() {
    run_with_stack(|| {
        let spec = Specification::new_eval_ir_prelude_spec()
            .expect("the production EvalIR vocabulary must register through ordinary admission");
        super::trust_ir_parity::assert_operator_contract(spec);
    });
}

#[test]
fn production_ty_description_contract() {
    run_with_stack(|| {
        let spec = Specification::new_eval_ir_prelude_spec()
            .expect("the production EvalIR vocabulary must register through ordinary admission");
        super::trust_ir_parity::assert_ty_contract(spec);
    });
}

#[test]
fn production_canonical_literals_round_trip_and_refuse_foreign_inputs() {
    run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_prelude_spec()
            .expect("the production EvalIR vocabulary must register");
        // The minter's declared atom pool contains a few chain-owned names
        // absent from the production vocabulary. Supply their actual checked
        // numeral definitions, never axioms or uninterpreted placeholders.
        for numeral in 0..=130 {
            let name = format!("ir_d{numeral}");
            if spec.env().get_const(&Name::from_string(&name)).is_none() {
                spec.add_recursive_def(
                    &format!("def {name} : Nat := {numeral}"),
                    "Canonical source-intake numeral, checked through ordinary registration.",
                )
                .expect("a missing numeral must elaborate to its actual Nat value");
            }
        }
        let mut decoded = Vec::new();
        for (prefix, core, tags, definitions, record) in [
            (
                "ir_h2",
                ir_mint::IR_H2_CORE,
                ir_mint::IR_H2_TAGS,
                ir_mint::IR_H2_DEFS,
                ir_mint::IR_H2_RECORD,
            ),
            (
                "ir_br",
                ir_mint::IR_BR_CORE,
                ir_mint::IR_BR_TAGS,
                ir_mint::IR_BR_DEFS,
                ir_mint::IR_BR_RECORD,
            ),
        ] {
            assert!(record.contains(&ir_mint::digest(core)));
            let core = ir_mint::parse(core).expect("committed core");
            let tags = ir_mint::tags::parse(tags).expect("committed tag authority");
            let minted = ir_mint::mint(&core, prefix, &tags).expect("canonical source renderer");
            assert_eq!(minted.text(), definitions);
            assert!(record.contains(&ir_mint::digest(definitions)));
            for line in definitions.lines().filter(|line| !line.trim().is_empty()) {
                spec.add_recursive_def(line, "Canonical typed module literal source intake.")
                    .expect("every literal must pass ordinary elaborator/kernel admission");
            }
            let actual = ir_mint::decode(spec.env(), &format!("{prefix}_module"), &tags)
                .expect("independent reader of the actual registered kernel term");
            let actual = ir_mint::print(&actual).expect("decoded canonical core");
            assert_eq!(actual, ir_mint::print(&core).expect("expected core"));
            decoded.push(actual);
        }
        assert_ne!(
            decoded[0], decoded[1],
            "two different bodies cannot decode as one"
        );
        assert!(ir_mint::decode(spec.env(), "ir_h2_module", &ir_mint::Tags::default()).is_err());
        let tags = ir_mint::tags::parse(ir_mint::IR_H2_TAGS).expect("H2 tags");
        assert!(ir_mint::decode(spec.env(), "ir_h2_func", &tags).is_err());
        assert!(ir_mint::decode(spec.env(), "absent_foreign_module", &tags).is_err());
    });
}
