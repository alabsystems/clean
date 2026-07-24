// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for symmetry group formalization.

use super::symmetry::*;

// ---------------------------------------------------------------------------
// GroupElement tests
// ---------------------------------------------------------------------------

#[test]
fn test_group_element_identity() {
    let id = GroupElement::identity(4);
    assert_eq!(id.dim(), 4);
    assert_eq!(id.mapping, vec![0, 1, 2, 3]);
}

#[test]
fn test_group_element_compose_identity() {
    let id = GroupElement::identity(3);
    let sigma = GroupElement::new(vec![1, 2, 0]); // cyclic shift
    let result = id.compose(&sigma);
    assert_eq!(result.mapping, sigma.mapping);
    let result2 = sigma.compose(&id);
    assert_eq!(result2.mapping, sigma.mapping);
}

#[test]
fn test_group_element_inverse() {
    let sigma = GroupElement::new(vec![1, 2, 0]); // (0->1, 1->2, 2->0)
    let inv = sigma.inverse();
    let composed = sigma.compose(&inv);
    let id = GroupElement::identity(3);
    assert_eq!(composed.mapping, id.mapping, "sigma * sigma^-1 = identity");
}

#[test]
fn test_group_element_compose_associative() {
    let a = GroupElement::new(vec![1, 2, 0]);
    let b = GroupElement::new(vec![0, 2, 1]); // swap 1 and 2
    let c = GroupElement::new(vec![2, 0, 1]);

    let ab_c = a.compose(&b).compose(&c);
    let a_bc = a.compose(&b.compose(&c));
    assert_eq!(ab_c.mapping, a_bc.mapping, "composition is associative");
}

#[test]
fn test_group_element_act_on_vec() {
    let sigma = GroupElement::new(vec![1, 2, 0]); // 0->1, 1->2, 2->0
    let x = vec![10.0, 20.0, 30.0];
    let result = sigma.act_on_vec(&x);
    // sigma sends position 0 to 1, position 1 to 2, position 2 to 0
    // So result[1] = x[0] = 10, result[2] = x[1] = 20, result[0] = x[2] = 30
    assert_eq!(result, vec![30.0, 10.0, 20.0]);
}

#[test]
fn test_group_element_permutation_matrix() {
    let sigma = GroupElement::new(vec![1, 0]); // swap
    let rho = sigma.to_permutation_matrix();
    // rho[sigma(j)][j] = 1: rho[1][0] = 1, rho[0][1] = 1
    assert_eq!(rho, vec![vec![0.0, 1.0], vec![1.0, 0.0]]);
}

#[test]
fn test_permutation_matrix_acts_correctly() {
    let sigma = GroupElement::new(vec![2, 0, 1]); // 0->2, 1->0, 2->1
    let rho = sigma.to_permutation_matrix();
    let x = vec![10.0, 20.0, 30.0];

    // Manual matrix-vector multiply rho * x
    let mut result = [0.0; 3];
    for i in 0..3 {
        for j in 0..3 {
            result[i] += rho[i][j] * x[j];
        }
    }

    // Compare with act_on_vec
    let act_result = sigma.act_on_vec(&x);
    for i in 0..3 {
        assert!(
            (result[i] - act_result[i]).abs() < 1e-12,
            "permutation matrix and act_on_vec must agree at index {i}"
        );
    }
}

// ---------------------------------------------------------------------------
// TranslationGroup tests
// ---------------------------------------------------------------------------

#[test]
fn test_translation_group_basic() {
    let g = TranslationGroup::new(4);
    assert_eq!(g.dim(), 4);
    assert_eq!(g.order(), 4);
}

#[test]
fn test_translation_group_generator() {
    let g = TranslationGroup::new(4);
    let gens = g.generators();
    assert_eq!(gens.len(), 1);
    assert_eq!(gens[0].mapping, vec![1, 2, 3, 0]);
}

#[test]
fn test_translation_group_orbit_single() {
    let g = TranslationGroup::new(4);
    let orb = g.orbit(0);
    assert_eq!(orb.size(), 4);
    assert_eq!(orb.indices, vec![0, 1, 2, 3]);
}

#[test]
fn test_translation_group_all_one_orbit() {
    let g = TranslationGroup::new(6);
    let orbits = g.all_orbits();
    assert_eq!(orbits.len(), 1, "Z_6 on R^6 has one orbit");
    assert_eq!(orbits[0].size(), 6);
}

#[test]
fn test_translation_group_quotient_dim() {
    let g = TranslationGroup::new(8);
    assert_eq!(g.quotient_dim(), 1, "Z_8 has one orbit, quotient dim = 1");
}

#[test]
fn test_translation_group_with_step() {
    let g = TranslationGroup::with_step(6, 2);
    // gcd(6, 2) = 2, so orbit size = 6/2 = 3, order = 3
    assert_eq!(g.order(), 3);
    let orb0 = g.orbit(0);
    assert_eq!(orb0.indices, vec![0, 2, 4]);
    let orb1 = g.orbit(1);
    assert_eq!(orb1.indices, vec![1, 3, 5]);
    assert_eq!(g.quotient_dim(), 2);
}

#[test]
fn test_translation_group_stabilizer() {
    let g = TranslationGroup::new(4);
    // All orbits have size 4, so stabilizer has size 4/4 = 1 (trivial)
    assert_eq!(g.stabilizer_size(0), 1);
    assert_eq!(g.stabilizer_size(2), 1);
}

#[test]
fn test_translation_group_with_step_stabilizer() {
    let g = TranslationGroup::with_step(6, 2);
    // Orbits have size 3, order = 3, so stabilizer size = 3/3 = 1
    assert_eq!(g.stabilizer_size(0), 1);
}

// ---------------------------------------------------------------------------
// PermutationGroup tests
// ---------------------------------------------------------------------------

#[test]
fn test_permutation_group_trivial() {
    // Trivial group (identity only) on R^3
    let g = PermutationGroup::new(3, vec![]);
    assert_eq!(g.dim(), 3);
    assert_eq!(g.order(), 1);
    assert_eq!(
        g.quotient_dim(),
        3,
        "trivial group: each index is its own orbit"
    );
}

#[test]
fn test_permutation_group_z2_swap() {
    // Z_2 generated by swap(0, 1) on R^3
    let swap = GroupElement::new(vec![1, 0, 2]);
    let g = PermutationGroup::new(3, vec![swap]);
    assert_eq!(g.order(), 2);

    let orb0 = g.orbit(0);
    assert_eq!(orb0.indices, vec![0, 1]);
    let orb2 = g.orbit(2);
    assert_eq!(orb2.indices, vec![2]);

    assert_eq!(g.quotient_dim(), 2);
}

#[test]
fn test_permutation_group_s3() {
    // S_3 on R^3, generated by (0 1 2) and (0 1)
    let cycle = GroupElement::new(vec![1, 2, 0]);
    let swap = GroupElement::new(vec![1, 0, 2]);
    let g = PermutationGroup::new(3, vec![cycle, swap]);
    assert_eq!(g.order(), 6, "S_3 has order 6");

    let orb = g.orbit(0);
    assert_eq!(orb.size(), 3, "S_3 acts transitively on {{0,1,2}}");
    assert_eq!(g.quotient_dim(), 1);
}

#[test]
fn test_permutation_group_orbit_stabilizer_theorem() {
    // Verify |G| = |Orb(x)| * |Stab(x)| for S_3
    let cycle = GroupElement::new(vec![1, 2, 0]);
    let swap = GroupElement::new(vec![1, 0, 2]);
    let g = PermutationGroup::new(3, vec![cycle, swap]);

    for i in 0..3 {
        let orbit_size = g.orbit(i).size();
        let stab_size = g.stabilizer_size(i);
        assert_eq!(
            g.order(),
            orbit_size * stab_size,
            "orbit-stabilizer theorem: |G| = |Orb({i})| * |Stab({i})|"
        );
    }
}

#[test]
fn test_orbit_representative() {
    let g = TranslationGroup::new(4);
    let orb = g.orbit(2);
    assert_eq!(
        orb.representative(),
        0,
        "representative is the smallest index"
    );
}

// ---------------------------------------------------------------------------
// Group element enumerate_elements
// ---------------------------------------------------------------------------

#[test]
fn test_enumerate_z3_elements() {
    let cycle = GroupElement::new(vec![1, 2, 0]);
    let g = PermutationGroup::new(3, vec![cycle]);
    let elements = g.enumerate_elements();
    assert_eq!(elements.len(), 3, "Z_3 has 3 elements");

    // Should contain identity, (0 1 2), (0 2 1)
    let mappings: Vec<Vec<usize>> = elements.iter().map(|e| e.mapping.clone()).collect();
    assert!(mappings.contains(&vec![0, 1, 2]), "must contain identity");
    assert!(mappings.contains(&vec![1, 2, 0]), "must contain (0 1 2)");
    assert!(mappings.contains(&vec![2, 0, 1]), "must contain (0 2 1)");
}
