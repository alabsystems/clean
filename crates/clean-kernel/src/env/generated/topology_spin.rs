// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::simple_axioms::build_simple_type_u_payload;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.Spin";
pub(crate) const DECL_COUNT: usize = 72;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    // Clifford Algebras
    "Topology.Spin.QuadraticForm",
    "Topology.Spin.polarization",
    "Topology.Spin.CliffordAlgebra",
    "Topology.Spin.clifford_relation",
    "Topology.Spin.CliffordEven",
    "Topology.Spin.CliffordOdd",
    "Topology.Spin.clifford_grading",
    "Topology.Spin.clifford_embedding",
    // Spin and Pin Groups
    "Topology.Spin.SpinGroup",
    "Topology.Spin.spin_double_cover",
    "Topology.Spin.spin_kernel",
    "Topology.Spin.spin_lie_algebra",
    "Topology.Spin.PinPlus",
    "Topology.Spin.PinMinus",
    "Topology.Spin.pin_relation",
    "Topology.Spin.spin_low_dim",
    // Spin Structures
    "Topology.Spin.FrameBundle",
    "Topology.Spin.SpinStructure",
    "Topology.Spin.spin_lift",
    "Topology.Spin.spin_obstruction",
    "Topology.Spin.SpinManifold",
    "Topology.Spin.spin_uniqueness",
    "Topology.Spin.spin_bordism",
    // Spinor Bundles and Representations
    "Topology.Spin.SpinRepresentation",
    "Topology.Spin.SpinorBundle",
    "Topology.Spin.ComplexSpinors",
    "Topology.Spin.RealSpinors",
    "Topology.Spin.SpinorField",
    "Topology.Spin.clifford_action",
    "Topology.Spin.ChiralityOperator",
    "Topology.Spin.WeylSpinors",
    "Topology.Spin.chiral_decomposition",
    // Dirac Operators
    "Topology.Spin.SpinConnection",
    "Topology.Spin.spin_connection_lift",
    "Topology.Spin.DiracOperator",
    "Topology.Spin.dirac_self_adjoint",
    "Topology.Spin.dirac_square",
    "Topology.Spin.WeitzenbockFormula",
    "Topology.Spin.DiracSpectrum",
    "Topology.Spin.dirac_discrete_spectrum",
    // Index Theory
    "Topology.Spin.DiracIndex",
    "Topology.Spin.AtiyahSingerSpin",
    "Topology.Spin.AHatGenus",
    "Topology.Spin.ahat_characteristic",
    "Topology.Spin.ahat_multiplicative",
    "Topology.Spin.RokhlinTheorem",
    "Topology.Spin.alpha_invariant",
    // Spin^c Structures
    "Topology.Spin.SpinCGroup",
    "Topology.Spin.spinc_exact",
    "Topology.Spin.SpinCStructure",
    "Topology.Spin.spinc_obstruction",
    "Topology.Spin.spinc_always_4d",
    "Topology.Spin.SpinCManifold",
    "Topology.Spin.spinc_line_bundle",
    "Topology.Spin.SpinCDirac",
    "Topology.Spin.spinc_index",
    // Physics Applications
    "Topology.Spin.FermionField",
    "Topology.Spin.DiracEquation",
    "Topology.Spin.dirac_covariant",
    "Topology.Spin.ChiralAnomaly",
    "Topology.Spin.anomaly_index",
    "Topology.Spin.MajoranaSpinor",
    "Topology.Spin.majorana_condition",
    // Advanced Topics
    "Topology.Spin.SpinorNorm",
    "Topology.Spin.ChargeConjugation",
    "Topology.Spin.RealityCondition",
    "Topology.Spin.PeriodicityBott",
    "Topology.Spin.SpinFoam",
    "Topology.Spin.TwistedSpinors",
    "Topology.Spin.KillingSpinor",
    "Topology.Spin.ParallelSpinor",
    "Topology.Spin.parallel_holonomy",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = build_simple_type_u_payload(&DECL_NAMES);
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    p
}
