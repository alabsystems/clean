// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **ROUTING — the thing a value differential on these bodies cannot see.**
//!
//! GAP 2 names one question by name: does Clean's `switch` encoding *route*
//! like trust-ir's? Until 2026-08-20 the answer rested on the
//! `from_source_system` chain, described in three places as the differential's
//! sharpest because "a contiguous table can be got right by a mechanism that
//! merely indexes, while a hole cannot".
//!
//! Measured from the committed fixture, that is backwards. The hole is real and
//! worth keeping — it puts a live input on the DEFAULT edge — but the body is
//! many-to-one: six of its twelve target blocks emit the same
//! `const enum.13 { 4 }`. So **2,880 permutations of its targets leave every
//! returned value unchanged**, and the specific off-by-one the hole was supposed
//! to expose (a positional encoder routing case 11 to `bb12` and tag 10 to
//! `bb11`) is observably wrong on **0 of 12** inputs. Cost cannot separate them
//! either: both blocks are `const` + `br`.
//!
//! What actually pins routing is structural, and is here: the registered Clean
//! case table is compared against the emitted switch tag-for-tag and
//! target-for-target, default included. That comparison refuses the swap the
//! value differential accepts, and
//! [`crystal_a3_the_value_differential_is_blind_to_the_swap`] measures the
//! blindness rather than asserting it.

use std::collections::BTreeMap;

use super::chains::{chains, Chain};
use super::fixture;

/// A switch, as a routing table: explicit cases plus the default target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Routing {
    /// Discriminant -> target block id, explicit cases only.
    pub cases: BTreeMap<u32, u32>,
    /// The default target block id.
    pub default: u32,
}

/// Read the routing out of an emitted body: `switch %N [ 0: bb1 … default: bbK ]`.
fn emitted_routing(text: &str) -> Routing {
    let line = text
        .lines()
        .map(|l| l.split("; #").next().unwrap_or(l).trim())
        .find(|l| l.starts_with("switch "))
        .expect("the emitted body must contain a switch");
    let open = line.find('[').expect("the switch lists its cases");
    let close = line.rfind(']').expect("the case list is closed");
    let mut cases = BTreeMap::new();
    let mut default = None;
    let toks: Vec<&str> = line[open + 1..close].split_whitespace().collect();
    let mut i = 0;
    while i + 1 < toks.len() {
        let key = toks[i].trim_end_matches(':');
        let target = toks[i + 1]
            .strip_prefix("bb")
            .and_then(|n| n.parse::<u32>().ok())
            .unwrap_or_else(|| panic!("switch target is not a block: `{}`", toks[i + 1]));
        if key == "default" {
            default = Some(target);
        } else {
            let tag = key
                .parse::<u32>()
                .unwrap_or_else(|e| panic!("switch case key is not a number ({e}): `{key}`"));
            assert!(
                cases.insert(tag, target).is_none(),
                "the emitted switch lists tag {tag} twice"
            );
        }
        i += 2;
    }
    Routing {
        cases,
        default: default.expect("the emitted switch must have a default edge"),
    }
}

/// Read the routing out of a registered Clean block definition.
///
/// Shape: `IRInst.switch <scrut> <default> <args> (ir_sc <tag> <target> …) <exh>`,
/// with every numeral an `ir_dN` atom.
fn clean_routing(def: &str) -> Routing {
    let at = def
        .find("IRInst.switch ")
        .expect("the Clean entry block must contain a switch");
    let rest = &def[at + "IRInst.switch ".len()..];
    let mut head = rest.split_whitespace();
    let _scrut = head.next().expect("switch has a scrutinee");
    let default = atom(head.next().expect("switch has a default target"));

    let mut cases = BTreeMap::new();
    for chunk in rest.split("ir_sc ").skip(1) {
        let mut it = chunk.split_whitespace();
        let tag = atom(it.next().expect("a case has a discriminant"));
        let target = atom(it.next().expect("a case has a target"));
        assert!(
            cases.insert(tag, target).is_none(),
            "the Clean case table lists tag {tag} twice"
        );
    }
    Routing { cases, default }
}

/// `ir_dN` -> `N`, with the trailing `)` a nested spine leaves behind.
fn atom(tok: &str) -> u32 {
    tok.trim_end_matches(')')
        .strip_prefix("ir_d")
        .and_then(|n| n.parse::<u32>().ok())
        .unwrap_or_else(|| panic!("not an ir_dN numeral: `{tok}`"))
}

/// The chain's entry-block definition — the one carrying the switch.
fn switch_def(chain: &Chain) -> &'static str {
    chain
        .clean_defs
        .iter()
        .copied()
        .find(|d| d.contains("IRInst.switch "))
        .unwrap_or_else(|| panic!("chain `{}` registers no switch", chain.name))
}

/// **Routing is pinned tag-for-tag, target-for-target, default included.**
///
/// This is the check that refuses a wrong ROUTE. The value differential cannot:
/// see [`crystal_a3_the_value_differential_is_blind_to_the_swap`].
#[test]
fn crystal_a3_routing_pairwise_matches_the_emitted_switch() {
    for chain in chains() {
        let emitted = emitted_routing(&fixture(chain.fixture));
        let clean = clean_routing(switch_def(&chain));
        assert_eq!(
            clean, emitted,
            "chain `{}`: the registered Clean case table and the emitted switch do not route \
             alike. This is the comparison that catches a value-preserving permutation of \
             targets, which no returned value and no step count on these bodies can.",
            chain.name
        );
        eprintln!(
            "routing pinned: {:<20} {} explicit cases + default -> bb{}",
            chain.name,
            clean.cases.len(),
            clean.default
        );
    }
}

/// **Mutation — the routing comparator must refuse the swap.**
///
/// The mutation is the exact positional off-by-one `from_source_system`'s hole
/// was meant to expose: case 11 routed to the default block and tag 10 routed to
/// `bb11`. Applied to the Clean side, the pairwise comparison goes RED.
#[test]
fn crystal_a3_mutation_a_value_preserving_route_swap_is_refused() {
    let chain = chains()
        .into_iter()
        .find(|c| c.name == "from_source_system")
        .expect("the from_source_system chain is registered");
    let emitted = emitted_routing(&fixture(chain.fixture));
    let def = switch_def(&chain);

    // `(ir_sc ir_d11 ir_d11 ir_sc0)` -> `(ir_sc ir_d10 ir_d11 ir_sc0)`, and the
    // default `ir_d12` stays: a positional encoder that believed the eleventh
    // listed case was discriminant 10.
    let mutated = def.replace("ir_sc ir_d11 ir_d11 ir_sc0", "ir_sc ir_d10 ir_d11 ir_sc0");
    assert_ne!(mutated, def, "the mutation must actually change the table");
    let mutated_routing = clean_routing(&mutated);

    assert_ne!(
        mutated_routing, emitted,
        "THE ROUTING PIN IS VACUOUS: a case table that routes discriminant 10 to bb11 and \
         leaves 11 on the default edge compared equal to the emitted switch"
    );
    assert_eq!(
        mutated_routing.cases.get(&10),
        Some(&11),
        "the mutation routes tag 10 explicitly"
    );
    assert_eq!(
        emitted.cases.get(&10),
        None,
        "the emitted switch has no case 10 — that is the hole"
    );
    eprintln!("mutation (route swap) correctly REFUSED by the pairwise routing pin");
}

/// **The blindness is MEASURED, not conceded in prose.**
///
/// Under the true routing and under the swap, the value returned on each of the
/// twelve inputs is computed from the emitted body and compared. They are equal
/// everywhere, and the two blocks cost the same number of instructions — so the
/// differential's two observables, value and step count, are both blind to it.
#[test]
fn crystal_a3_the_value_differential_is_blind_to_the_swap() {
    let text = fixture("from_source_system.trust-ir.txt");
    let routing = emitted_routing(&text);
    let blocks = block_bodies(&text);

    let value_of = |block: u32| -> String {
        blocks
            .get(&block)
            .and_then(|b| b.iter().find_map(|l| l.split(" = const ").nth(1)))
            .unwrap_or_else(|| panic!("bb{block} materializes no constant"))
            .trim()
            .to_owned()
    };

    let mut invisible = 0;
    for tag in 0..12u32 {
        let truth = *routing.cases.get(&tag).unwrap_or(&routing.default);
        // The swap: 11 leaves bb11 for the default block, 10 takes bb11.
        let swapped = match tag {
            10 => 11,
            11 => routing.default,
            other => *routing.cases.get(&other).unwrap_or(&routing.default),
        };
        if truth != swapped {
            assert_eq!(
                value_of(truth),
                value_of(swapped),
                "tag {tag}: the swap IS observable after all — then say so and re-rank the \
                 chain, do not leave the description as it was"
            );
            invisible += 1;
        }
    }
    assert_eq!(
        invisible, 2,
        "the swap must actually move two inputs (10 and 11) to different blocks"
    );

    let n11 = blocks.get(&11).map(Vec::len).unwrap_or_default();
    let n12 = blocks.get(&12).map(Vec::len).unwrap_or_default();
    assert_eq!(
        n11, n12,
        "bb11 and bb12 must cost the same, or the STEP COUNT would separate them and the \
         differential would not be blind after all"
    );
    eprintln!(
        "measured blindness: the 10<->11 route swap moves 2 of 12 inputs to a different block, \
         changes 0 returned values, and changes 0 steps ({n11} instructions either way)"
    );
}

/// **Per-chain discriminating power, computed from the committed fixtures.**
///
/// The number reported is the count of permutations of a switch's target blocks
/// that leave the observed value function unchanged: `1` means every wrong
/// routing is visible to the differential, anything larger is the size of its
/// blind spot. Declared on each [`Chain`] and recomputed here, so neither the
/// number nor the prose that quotes it can drift from the body.
#[test]
fn crystal_a3_discriminating_power_is_measured() {
    eprintln!("\n--- what a VALUE differential can discriminate, per chain ---");
    let mut fully_discriminating = Vec::new();
    for chain in chains() {
        let text = fixture(chain.fixture);
        let routing = emitted_routing(&text);
        let blocks = block_bodies(&text);

        let targets: Vec<u32> = chain
            .domain
            .iter()
            .map(|t| *routing.cases.get(t).unwrap_or(&routing.default))
            .collect();
        let mut by_value: BTreeMap<String, u64> = BTreeMap::new();
        for b in targets
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
        {
            let v = blocks
                .get(&b)
                .and_then(|body| body.iter().find_map(|l| l.split(" = const ").nth(1)))
                .unwrap_or_else(|| panic!("bb{b} materializes no constant"))
                .trim()
                .to_owned();
            *by_value.entry(v).or_insert(0) += 1;
        }
        let permutations: u64 = by_value
            .values()
            .map(|n| (1..=*n).product::<u64>())
            .product();
        assert_eq!(
            permutations, chain.value_preserving_target_permutations,
            "chain `{}` declares {} value-preserving target permutations but the committed \
             fixture has {permutations}. The declared number is quoted in the module docs and \
             in data/crystal_gap2_semdiff_2026-08-20.json; correct both.",
            chain.name, chain.value_preserving_target_permutations
        );
        eprintln!(
            "  {:<20} {:>2} inputs | {:>2} distinct values | {:>4} value-preserving target \
             permutations | E3 {}",
            chain.name,
            chain.domain.len(),
            by_value.len(),
            permutations,
            if chain.shipped.is_some() {
                "present"
            } else {
                "ABSENT"
            }
        );
        if permutations == 1 {
            fully_discriminating.push((chain.name, chain.shipped.is_some()));
        }
    }
    assert_eq!(
        fully_discriminating,
        vec![("level_kind_ord", false)],
        "the honest summary of this table is that exactly one chain is fully discriminating and \
         it is the one with no E3. If that changes, rewrite the summary rather than the test."
    );
    eprintln!(
        "  => the only fully discriminating chain is the one with no shipped leg; the widest \
         chain (from_source_system) is the DULLEST, not the sharpest."
    );
}

/// Block id -> its instruction lines, comments and headers stripped.
fn block_bodies(text: &str) -> BTreeMap<u32, Vec<String>> {
    let mut out: BTreeMap<u32, Vec<String>> = BTreeMap::new();
    let mut cur: Option<u32> = None;
    for raw in text.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim().to_owned();
        if line.is_empty() || line.starts_with(';') || line == "}" {
            continue;
        }
        if let Some(id) = line.strip_prefix("bb").and_then(|r| {
            r.split(|c: char| !c.is_ascii_digit())
                .next()
                .and_then(|n| n.parse::<u32>().ok())
        }) {
            if line.ends_with(':') || line.contains("):") {
                cur = Some(id);
                out.entry(id).or_default();
                continue;
            }
        }
        if let Some(id) = cur {
            out.entry(id).or_default().push(line);
        }
    }
    out
}
