// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Join the selected rule families to their existing model contract replays.

use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

const BINDINGS: &str = include_str!("../../../../data/cic_l_model_rule_bindings.json");
const CPP_ROOT: &str = "tests/fixtures/lean_kernel/v4.30.0-rc2";
const CPP_FILE: &str = "src/kernel/type_checker.cpp";
const CPP: &[u8] = include_bytes!(
    "../../../../tests/fixtures/lean_kernel/v4.30.0-rc2/src/kernel/type_checker.cpp"
);
const CONTRACTS: &str = "CICL.Model.Contracts.";
pub(super) const NAMED_LOCAL_FAMILY: &str = "infer-local-variable";

struct Family {
    id: &'static str,
    component: &'static str,
    mutation: &'static str,
    anchors: &'static [(&'static str, [usize; 2])],
}

const FAMILIES: &[Family] = &[
    Family {
        id: "infer-sort",
        component: "sort",
        mutation: "CICL.Model.Contracts.sortBoundOffByOne",
        anchors: &[("type_checker::infer_type_core", [289, 292])],
    },
    Family {
        id: "infer-constant",
        component: "constant",
        mutation: "CICL.Model.Contracts.constantWithoutLevelSubstitution",
        anchors: &[
            ("type_checker::infer_constant", [92, 99]),
            ("type_checker::infer_constant", [113, 114]),
            ("type_checker::infer_type_core", [293, 293]),
        ],
    },
    Family {
        id: "infer-let",
        component: "letE",
        mutation: "CICL.Model.Contracts.letWithoutInstantiation",
        anchors: &[
            ("type_checker::infer_let", [198, 219]),
            ("type_checker::infer_type_core", [297, 297]),
        ],
    },
    Family {
        id: "infer-lambda",
        component: "lam",
        mutation: "CICL.Model.Contracts.lambdaWithoutBodyTyping",
        anchors: &[
            ("type_checker::infer_lambda", [116, 132]),
            ("type_checker::infer_type_core", [294, 294]),
        ],
    },
    Family {
        id: "infer-app",
        component: "app",
        mutation: "CICL.Model.Contracts.appWithoutArgumentMembership",
        anchors: &[
            ("type_checker::infer_app", [163, 167]),
            ("type_checker::infer_app", [174, 196]),
            ("type_checker::infer_type_core", [296, 296]),
        ],
    },
    Family {
        id: "infer-pi",
        component: "pi",
        mutation: "CICL.Model.Contracts.piWithoutPointwiseFamily",
        anchors: &[
            ("type_checker::infer_pi", [134, 156]),
            ("type_checker::infer_type_core", [295, 295]),
        ],
    },
    Family {
        id: NAMED_LOCAL_FAMILY,
        component: "bvar",
        mutation: "CICL.Model.Contracts.inferFVarWithoutLookup",
        anchors: &[
            ("type_checker::infer_fvar", [84, 90]),
            ("type_checker::infer_type_core", [285, 285]),
        ],
    },
    Family {
        id: "infer-mdata",
        component: "mdata",
        mutation: "CICL.Model.Contracts.mdataWithoutInnerMembership",
        anchors: &[("type_checker::infer_type_core", [283, 283])],
    },
];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Binding {
    pub(super) family: String,
    pub(super) constructor: String,
    pub(super) constructor_module: String,
    pub(super) lemma: String,
    pub(super) lemma_module: String,
    pub(super) contract: String,
    pub(super) contract_module: String,
    pub(super) mutation: String,
    pub(super) mutation_module: String,
    upstream_commit: String,
    anchors: Vec<Anchor>,
}

#[derive(Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Anchor {
    file: String,
    function: String,
    lines: [usize; 2],
    sha256: String,
}

pub(super) fn read(
    inventory: &Value,
    replays: &[[String; 2]],
    mutations: &[[String; 2]],
) -> Result<Vec<Binding>, String> {
    let bindings = decode_bindings(BINDINGS)?;
    for binding in &bindings {
        validate(binding, inventory, replays, mutations, CPP)?;
    }
    Ok(bindings)
}

fn decode_bindings(input: &str) -> Result<Vec<Binding>, String> {
    let mut bindings: Vec<Binding> =
        serde_json::from_str(input).map_err(|error| format!("rule family bindings: {error}"))?;
    bindings.sort_by_key(|binding| {
        FAMILIES
            .iter()
            .position(|family| family.id == binding.family)
    });
    if bindings
        .iter()
        .map(|binding| binding.family.as_str())
        .eq(FAMILIES.iter().map(|family| family.id))
    {
        return Ok(bindings);
    }
    Err(
        "bindings need exactly one record for each registered family in the model binding roster"
            .to_owned(),
    )
}

fn validate(
    binding: &Binding,
    inventory: &Value,
    replays: &[[String; 2]],
    mutations: &[[String; 2]],
    source: &[u8],
) -> Result<(), String> {
    let family = &binding.family;
    let expected = FAMILIES
        .iter()
        .find(|candidate| candidate.id == family)
        .ok_or_else(|| format!("unrecognized rule family binding {family}"))?;
    let component = expected.component;
    let constructor = format!("CICL.CoreJudgmentIn.{component}");
    if binding.constructor != constructor {
        return Err(format!("{family} binding must select {constructor}"));
    }
    let named_local = expected.id == NAMED_LOCAL_FAMILY;
    let core_lemma = format!("CICL.Model.CoreRules.{component}");
    let (lemma, lemma_module, contract_module) = if named_local {
        (
            "CICL.Model.LocalContextSemantics.inferFVar_sound",
            "CICLModel.LocalContextSemantics",
            "CICLModel.Contracts",
        )
    } else {
        (
            core_lemma.as_str(),
            "CICLModel.RuleMeaning",
            "CICLModel.CoreContracts",
        )
    };
    if binding.constructor_module != "CICL.CoreTyping"
        || binding.lemma_module != lemma_module
        || binding.contract_module != contract_module
        || binding.mutation_module != contract_module
    {
        return Err(format!(
            "{family} binding names an unexpected declaration owner"
        ));
    }
    let rows = inventory["rows"].as_array().ok_or("rule inventory rows")?;
    let mut matches = rows.iter().filter(|row| row["id"] == family.as_str());
    let Some(row) = matches.next() else {
        return Err(format!("rule inventory has no {family} row"));
    };
    if matches.next().is_some() || row["kind"] != "rule" || row["status"] != "specified" {
        return Err(format!("rule inventory needs one specified {family} rule"));
    }
    let constructor_file = "CICL/CoreTyping.lean";
    let citations = row["cic_l"].as_array().map_or(&[][..], Vec::as_slice);
    let mut constructors = citations.iter().filter(|citation| {
        citation["item"] == binding.constructor.as_str()
            && citation["kind"] == "constructor"
            && citation["file"] == constructor_file
    });
    let citation = constructors
        .next()
        .filter(|_| constructors.next().is_none() && inventory["spec"]["root"] == "theories/cic_l")
        .ok_or_else(|| {
            format!(
                "{family} must cite {} exactly once in {constructor_file}",
                binding.constructor
            )
        })?;
    let control = format!("CICL.NegativeControls.{component}_control");
    if citation["control"]["theorem"] != control.as_str()
        || citation["control"]["file"] != "CICL/NegativeControls.lean"
    {
        return Err(format!(
            "{family} requires the exact {component} deleted-premise control"
        ));
    }
    let required_citations: &[(&str, &str, &str)] = match expected.id {
        "infer-constant" => &[("CICL.levelSubstitution", "def", "CICL/Declaration.lean")],
        NAMED_LOCAL_FAMILY => &[
            ("CICL.lookupType", "def", constructor_file),
            (
                "CICL.LocalContextRules.inferFVar",
                "def",
                "CICL/LocalContextRules.lean",
            ),
            (
                "CICL.LocalContextRules.inferFVar_iff_lookupType",
                "theorem",
                "CICL/LocalContextRules.lean",
            ),
        ],
        _ => &[],
    };
    for &(item, kind, file) in required_citations {
        if citations
            .iter()
            .filter(|citation| {
                citation["item"] == item && citation["kind"] == kind && citation["file"] == file
            })
            .count()
            != 1
        {
            return Err(format!("{family} must cite {item} exactly once in {file}"));
        }
    }
    if binding.lemma != lemma {
        return Err(if named_local {
            format!("{family} requires the {lemma} lemma")
        } else {
            format!("{family} requires the core {component} lemma")
        });
    }
    if named_local && binding.contract != "CICL.Model.Contracts.inferFVarSound" {
        return Err(format!(
            "{family} requires the independent inferFVarSound contract"
        ));
    }
    if !unique_replay(replays, &binding.lemma, &binding.contract) {
        return Err(format!("{family} has no unique positive contract replay"));
    }
    if binding.mutation != expected.mutation
        || !unique_replay(mutations, &binding.lemma, &binding.mutation)
    {
        return Err(format!(
            "{family} has no unique {} mutation replay",
            expected.mutation
        ));
    }
    validate_anchors(binding, expected, inventory, row, source)
}

fn unique_replay(catalog: &[[String; 2]], proof: &str, proposition: &str) -> bool {
    let Some(key) = proposition.strip_prefix(CONTRACTS) else {
        return false;
    };
    let mut rows = catalog.iter().filter(|[_, candidate]| candidate == key);
    rows.next().is_some_and(|[candidate, _]| candidate == proof) && rows.next().is_none()
}

fn validate_anchors(
    binding: &Binding,
    expected: &Family,
    inventory: &Value,
    row: &Value,
    source: &[u8],
) -> Result<(), String> {
    let family = &binding.family;
    let upstream = &inventory["upstream"];
    if upstream["repository"] != "https://github.com/leanprover/lean4"
        || upstream["tag"] != "v4.30.0-rc2"
        || upstream["root"] != CPP_ROOT
        || upstream["commit"] != binding.upstream_commit.as_str()
    {
        return Err(format!(
            "{family} upstream does not match the pinned C++ source"
        ));
    }
    let anchors: Vec<Anchor> = serde_json::from_value(row["anchors"].clone())
        .map_err(|error| format!("{family} C++ anchors: {error}"))?;
    if anchors != binding.anchors {
        return Err(format!("{family} row does not match the bound C++ anchors"));
    }
    if anchors.len() != expected.anchors.len()
        || anchors
            .iter()
            .zip(expected.anchors)
            .any(|(anchor, &(function, lines))| {
                anchor.file != CPP_FILE || anchor.function != function || anchor.lines != lines
            })
    {
        return Err(format!(
            "{family} binding must cover the exact pinned C++ function spans"
        ));
    }
    let pin = &upstream["files"][CPP_FILE];
    let source_digest = digest_hex(Sha256::digest(source).as_ref());
    if pin["sha256"] != source_digest.as_str() || pin["bytes"].as_u64() != Some(source.len() as u64)
    {
        return Err(format!(
            "{family} pinned C++ file bytes disagree with the inventory"
        ));
    }

    for anchor in anchors {
        let [start, end] = anchor.lines;
        let mut lines = source
            .split_inclusive(|&byte| byte == b'\n')
            .skip(start - 1);
        let mut digest = Sha256::new();
        for _ in start..=end {
            let line = lines
                .next()
                .ok_or_else(|| format!("{family} C++ anchor extends past the source"))?;
            digest.update(line);
        }
        if digest_hex(digest.finalize().as_ref()) != anchor.sha256 {
            return Err(format!(
                "{family} C++ anchor SHA-256 mismatch at lines {start}-{end}"
            ));
        }
    }
    Ok(())
}

fn digest_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::{
        decode_bindings, digest_hex, read, unique_replay, validate, Digest, Sha256, Value,
        BINDINGS, CPP, CPP_FILE, NAMED_LOCAL_FAMILY,
    };

    fn inputs() -> (Value, Vec<[String; 2]>, Vec<[String; 2]>) {
        let inventory: Value =
            serde_json::from_str(include_str!("../../../../data/cic_l_rule_inventory.json"))
                .expect("rule inventory");
        let replays: Vec<[String; 2]> = serde_json::from_str(include_str!(
            "../../../../theories/cic_l_model/contract_replays.json"
        ))
        .expect("positive model replay catalog");
        let mutations: Vec<[String; 2]> = serde_json::from_str(include_str!(
            "../../../../theories/cic_l_model/mutant_replays.json"
        ))
        .expect("negative model replay catalog");
        (inventory, replays, mutations)
    }

    #[test]
    fn model_rule_binding_refuses_wrong_associations() {
        let (inventory, replays, mutations) = inputs();
        let mut bindings = read(&inventory, &replays, &mutations).expect("bound model replays");
        let binding = bindings.remove(0);

        // An existing but different proof/contract pair is not a sort binding.
        let mut wrong_pair = decode_bindings(BINDINGS).unwrap().remove(0);
        wrong_pair.lemma = "CICL.Model.CoreRules.sortCong".to_owned();
        wrong_pair.contract = "CICL.Model.Contracts.ruleSortCong".to_owned();
        assert!(unique_replay(
            &replays,
            &wrong_pair.lemma,
            &wrong_pair.contract
        ));
        assert_eq!(
            validate(&wrong_pair, &inventory, &replays, &mutations, CPP).unwrap_err(),
            "infer-sort requires the core sort lemma"
        );

        let selected = inventory["rows"]
            .as_array()
            .unwrap()
            .iter()
            .position(|row| row["id"] == binding.family.as_str())
            .unwrap();
        let mut uncontrolled = inventory.clone();
        uncontrolled["rows"][selected]["cic_l"][0]["control"] = Value::Null;
        assert_eq!(
            validate(&binding, &uncontrolled, &replays, &mutations, CPP).unwrap_err(),
            "infer-sort requires the exact sort deleted-premise control"
        );

        let mut moved = inventory.clone();
        let rows = moved["rows"].as_array_mut().unwrap();
        let citation = rows[selected]["cic_l"].take();
        rows.push(serde_json::json!({"id": "another-family", "cic_l": citation}));
        assert_eq!(
            validate(&binding, &moved, &replays, &mutations, CPP).unwrap_err(),
            "infer-sort must cite CICL.CoreJudgmentIn.sort exactly once in CICL/CoreTyping.lean"
        );
        moved["rows"].as_array_mut().unwrap().remove(selected);
        assert_eq!(
            validate(&binding, &moved, &replays, &mutations, CPP).unwrap_err(),
            "rule inventory has no infer-sort row"
        );

        // A coherently repinned Const arm cannot replace the Sort anchor.
        let mut shifted = inventory.clone();
        let mut other_arm = decode_bindings(BINDINGS).unwrap().remove(0);
        let const_line = CPP.split_inclusive(|&byte| byte == b'\n').nth(292).unwrap();
        let other_anchor = &mut other_arm.anchors[0];
        other_anchor.lines = [293, 293];
        other_anchor.sha256 = digest_hex(Sha256::digest(const_line).as_ref());
        let anchor = &mut shifted["rows"][selected]["anchors"][0];
        anchor["lines"] = serde_json::json!(other_anchor.lines);
        anchor["sha256"] = Value::String(other_anchor.sha256.clone());
        assert_eq!(
            validate(&other_arm, &shifted, &replays, &mutations, CPP).unwrap_err(),
            "infer-sort binding must cover the exact pinned C++ function spans"
        );

        // Even a valid new whole-file pin cannot substitute the anchored bytes.
        let mut source = CPP.to_vec();
        let first_anchor_byte = CPP
            .split_inclusive(|&byte| byte == b'\n')
            .take(binding.anchors[0].lines[0] - 1)
            .map(<[u8]>::len)
            .sum::<usize>();
        source[first_anchor_byte] ^= 1;
        let mut repinned = inventory;
        repinned["upstream"]["files"][CPP_FILE]["sha256"] =
            Value::String(digest_hex(Sha256::digest(&source).as_ref()));
        assert_eq!(
            validate(&binding, &repinned, &replays, &mutations, &source).unwrap_err(),
            "infer-sort C++ anchor SHA-256 mismatch at lines 289-292"
        );
    }

    #[test]
    fn model_rule_bindings_require_every_named_family() {
        let mut rows: Vec<Value> = serde_json::from_str(BINDINGS).unwrap();
        rows.reverse();
        let ordered = decode_bindings(&serde_json::to_string(&rows).unwrap()).unwrap();
        assert_eq!(
            ordered
                .iter()
                .map(|binding| binding.family.as_str())
                .collect::<Vec<_>>(),
            [
                "infer-sort",
                "infer-constant",
                "infer-let",
                "infer-lambda",
                "infer-app",
                "infer-pi",
                NAMED_LOCAL_FAMILY,
                "infer-mdata",
            ]
        );

        let required = rows.remove(0);
        assert!(decode_bindings(&serde_json::to_string(&rows).unwrap()).is_err());
        rows.push(rows[0].clone());
        assert!(decode_bindings(&serde_json::to_string(&rows).unwrap()).is_err());
        let last = rows.last_mut().unwrap();
        *last = required;
        last["family"] = Value::String("unknown-rule".to_owned());
        assert!(decode_bindings(&serde_json::to_string(&rows).unwrap()).is_err());
    }

    #[test]
    fn named_local_binding_requires_the_named_proof_and_lookup_bridge() {
        let (mut inventory, replays, mutations) = inputs();
        let mut binding = read(&inventory, &replays, &mutations)
            .expect("bound model replays")
            .into_iter()
            .find(|binding| binding.family == NAMED_LOCAL_FAMILY)
            .expect("named local lookup binding");
        let actual = std::mem::replace(&mut binding.lemma, "CICL.Model.CoreRules.bvar".to_owned());
        assert_eq!(
            validate(&binding, &inventory, &replays, &mutations, CPP).unwrap_err(),
            "infer-local-variable requires the CICL.Model.LocalContextSemantics.inferFVar_sound lemma"
        );
        binding.lemma = actual;
        let row = inventory["rows"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|row| row["id"] == NAMED_LOCAL_FAMILY)
            .unwrap();
        let bridge = row["cic_l"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|citation| citation["item"] == "CICL.LocalContextRules.inferFVar_iff_lookupType")
            .unwrap();
        bridge["item"] =
            Value::String("CICL.LocalContextRules.inferFVar_eq_open_lookupType".to_owned());
        assert_eq!(
            validate(&binding, &inventory, &replays, &mutations, CPP).unwrap_err(),
            "infer-local-variable must cite CICL.LocalContextRules.inferFVar_iff_lookupType exactly once in CICL/LocalContextRules.lean"
        );
    }

    #[test]
    fn constant_rule_binding_requires_its_substitution_citation_and_three_spans() {
        let (inventory, replays, mutations) = inputs();
        let mut binding = read(&inventory, &replays, &mutations)
            .expect("bound model replays")
            .into_iter()
            .find(|binding| binding.family == "infer-constant")
            .expect("infer-constant binding");
        let selected = inventory["rows"]
            .as_array()
            .unwrap()
            .iter()
            .position(|row| row["id"] == binding.family.as_str())
            .unwrap();
        let mut no_substitution = inventory.clone();
        no_substitution["rows"][selected]["cic_l"]
            .as_array_mut()
            .unwrap()
            .retain(|citation| citation["item"] != "CICL.levelSubstitution");
        assert_eq!(
            validate(&binding, &no_substitution, &replays, &mutations, CPP).unwrap_err(),
            "infer-constant must cite CICL.levelSubstitution exactly once in CICL/Declaration.lean"
        );

        let mut too_short = inventory;
        too_short["rows"][selected]["anchors"]
            .as_array_mut()
            .unwrap()
            .remove(1);
        binding.anchors.remove(1);
        assert_eq!(
            validate(&binding, &too_short, &replays, &mutations, CPP).unwrap_err(),
            "infer-constant binding must cover the exact pinned C++ function spans"
        );
    }
}
