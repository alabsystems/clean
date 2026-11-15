// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural axiom closures: the declared axioms each declaration reaches
//! through the declarations it mentions, compared as `Name`s.
//!
//! Lean's `CollectAxioms` walks the same edges and counts `axiomInfo`
//! constants only (a `quot` record is no axiom). Names are compared by
//! structure, never by a flattened string: nanoda's `permitted_axioms`
//! compared `«Quot.sound»` (one component) equal to `Quot.sound`
//! (ammkrn/nanoda_lib#37).

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use clean_kernel::name::Name;

/// Every declaration's closure. A declaration on a reference cycle (which the
/// replay refuses anyway) gets the closure of everything it reaches.
pub(crate) fn axiom_closures(
    refs: &BTreeMap<Name, BTreeSet<Name>>,
    axioms: &BTreeSet<Name>,
) -> BTreeMap<Name, BTreeSet<Name>> {
    // Kahn's order over the declarations: a declaration is finished once
    // every declaration it mentions is.
    let mut waiting: BTreeMap<&Name, usize> = BTreeMap::new();
    let mut users: BTreeMap<&Name, Vec<&Name>> = BTreeMap::new();
    for (name, mentioned) in refs {
        let deps = mentioned
            .iter()
            .filter(|d| *d != name && refs.contains_key(*d))
            .inspect(|d| users.entry(*d).or_default().push(name))
            .count();
        waiting.insert(name, deps);
    }
    let mut ready: VecDeque<&Name> = waiting
        .iter()
        .filter(|(_, &n)| n == 0)
        .map(|(name, _)| *name)
        .collect();
    let mut done: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
    while let Some(name) = ready.pop_front() {
        let mut closure: BTreeSet<Name> = BTreeSet::new();
        if axioms.contains(name) {
            closure.insert(name.clone());
        }
        for dep in refs.get(name).into_iter().flatten() {
            if let Some(found) = done.get(dep) {
                closure.extend(found.iter().cloned());
            } else if axioms.contains(dep) {
                closure.insert(dep.clone());
            }
        }
        done.insert(name.clone(), closure);
        for user in users.get(name).into_iter().flatten() {
            if let Some(count) = waiting.get_mut(user) {
                *count -= 1;
                if *count == 0 {
                    ready.push_back(*user);
                }
            }
        }
    }
    // What is left sits on or behind a cycle: walk it directly.
    for name in refs.keys() {
        if done.contains_key(name) {
            continue;
        }
        let mut closure = BTreeSet::new();
        let mut seen: BTreeSet<&Name> = BTreeSet::new();
        let mut stack: Vec<&Name> = vec![name];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            if axioms.contains(n) {
                closure.insert(n.clone());
            }
            if let Some(found) = done.get(n) {
                closure.extend(found.iter().cloned());
                continue;
            }
            stack.extend(refs.get(n).into_iter().flatten());
        }
        done.insert(name.clone(), closure);
    }
    done
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    #[test]
    fn test_axiom_closure_follows_references_and_cycles() {
        let refs: BTreeMap<Name, BTreeSet<Name>> = [
            ("ax", vec![]),
            ("def1", vec!["ax"]),
            ("thm", vec!["def1"]),
            ("cycA", vec!["cycB", "ax"]),
            ("cycB", vec!["cycA"]),
            ("free", vec![]),
        ]
        .into_iter()
        .map(|(k, v)| (n(k), v.into_iter().map(n).collect()))
        .collect();
        let axioms: BTreeSet<Name> = [n("ax")].into_iter().collect();
        let closures = axiom_closures(&refs, &axioms);
        assert_eq!(closures[&n("thm")], axioms);
        assert_eq!(closures[&n("cycB")], axioms);
        assert!(closures[&n("free")].is_empty());
    }

    #[test]
    fn test_axiom_closure_compares_names_by_structure() {
        // `«Quot.sound»` (one component) is not `Quot.sound`.
        let one_component = Name::anon().str("Quot.sound");
        let refs: BTreeMap<Name, BTreeSet<Name>> =
            [(n("user"), [one_component.clone()].into_iter().collect())]
                .into_iter()
                .chain([(one_component.clone(), BTreeSet::new())])
                .collect();
        let axioms: BTreeSet<Name> = [one_component.clone()].into_iter().collect();
        let closures = axiom_closures(&refs, &axioms);
        assert!(closures[&n("user")].contains(&one_component));
        assert!(!closures[&n("user")].contains(&n("Quot.sound")));
    }
}
