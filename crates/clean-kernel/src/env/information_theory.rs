// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Information theory structures for Environment
//!
//! This module contains axioms for classical information theory:
//! - Shannon entropy and mutual information
//! - Divergence measures and inequalities
//! - Channel capacity and coding theorems
//! - Source coding, rate-distortion, and multiuser information theory

#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::Expr;
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Initialize InformationTheory module
    ///
    /// Information theory quantifies uncertainty, compression limits, and
    /// communication reliability. Core applications include:
    /// - Machine learning (generalization bounds, representation learning)
    /// - Data compression and coding
    /// - Communication systems and network reliability
    /// - Statistical inference and hypothesis testing
    ///
    /// This module provides axioms for:
    /// - Entropy, mutual information, and divergence measures
    /// - Source and channel coding theorems
    /// - Rate-distortion theory
    /// - Multiuser channels and capacity regions
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.information_theory_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `rat`, `measure_theory`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_information_theory(&mut self) -> Result<(), EnvError> {
        if self.information_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_measure_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Information theory constants
        for name in &[
            // ================================================================
            // Entropy and Mutual Information
            // ================================================================
            "InformationTheory.Entropy",                      // H(X)
            "InformationTheory.JointEntropy",                 // H(X,Y)
            "InformationTheory.ConditionalEntropy",           // H(X|Y)
            "InformationTheory.EntropyNonneg",                // H(X) ≥ 0
            "InformationTheory.ChainRuleEntropy",             // H(X,Y) = H(Y) + H(X|Y)
            "InformationTheory.MutualInformation",            // I(X;Y)
            "InformationTheory.ConditionalMutualInformation", // I(X;Y|Z)
            "InformationTheory.MutualInformationSymm",        // I(X;Y) = I(Y;X)
            "InformationTheory.ChainRuleMutualInfo",          // chain rule for I
            "InformationTheory.NonnegMutualInformation",      // I(X;Y) ≥ 0
            "InformationTheory.DataProcessing",               // data processing inequality
            "InformationTheory.EntropySubadditivity",         // H(X,Y) ≤ H(X)+H(Y)
            "InformationTheory.StrongSubadditivity",          // SSA: H(X,Y,Z)+H(Y) ≤ H(X,Y)+H(Y,Z)
            "InformationTheory.AEP",                          // asymptotic equipartition property
            "InformationTheory.TypicalSet",                   // typical sequences
            "InformationTheory.TypicalSetCardinality",        // |T_ε^{(n)}| ≈ 2^{nH(X)}
            "InformationTheory.TypicalSetProbability",        // P(Xⁿ ∈ T_ε^{(n)}) → 1
            // ================================================================
            // Divergence Measures
            // ================================================================
            "InformationTheory.KLDivergence",           // D(P‖Q)
            "InformationTheory.KLNonnegativity",        // D(P‖Q) ≥ 0
            "InformationTheory.GibbsInequality",        // KL ≥ 0 equality iff P=Q
            "InformationTheory.CrossEntropy",           // H(P,Q)
            "InformationTheory.JensenShannon",          // JS divergence
            "InformationTheory.TotalVariation",         // TV distance
            "InformationTheory.PinskerInequality",      // TV ≤ sqrt(KL/2)
            "InformationTheory.HellingerDistance",      // Hellinger distance
            "InformationTheory.FDiv",                   // f-divergence general form
            "InformationTheory.RenyiEntropy",           // Rényi entropy H_α
            "InformationTheory.RenyiDivergence",        // Rényi divergence D_α
            "InformationTheory.AlphaDivergence",        // α-divergence family
            "InformationTheory.DeBruijnIdentity",       // connects entropy and Fisher info
            "InformationTheory.FisherInformation",      // Fisher information
            "InformationTheory.EntropyPower",           // entropy power N(X)
            "InformationTheory.EntropyPowerInequality", // N(X+Y) ≥ N(X)+N(Y)
            // ================================================================
            // Channel Coding
            // ================================================================
            "InformationTheory.DiscreteMemorylessChannel", // DMC definition
            "InformationTheory.ChannelTransition",         // channel law P_{Y|X}
            "InformationTheory.ChannelCapacity",           // C = max_p I(X;Y)
            "InformationTheory.ChannelCodingTheorem",      // reliable comm if R < C
            "InformationTheory.SpherePackingBound",        // converse bound
            "InformationTheory.ErrorExponent",             // reliability function E(R)
            "InformationTheory.FanoInequality",            // lower bound error via entropy
            "InformationTheory.DataProcessingChannel",     // DPI for channels
            "InformationTheory.ChannelMutualInfo",         // I(X;Y) over channel
            "InformationTheory.TypicalSetDecoder",         // joint typicality decoding
            "InformationTheory.RandomCoding",              // random coding achievability
            "InformationTheory.HammingCodeBounds",         // Hamming/Singleton bounds
            "InformationTheory.GilbertVarshamov",          // GV bound for codes
            // ================================================================
            // Source Coding and Compression
            // ================================================================
            "InformationTheory.PrefixFreeCode", // prefix-free code definition
            "InformationTheory.KraftInequality", // Σ 2^{-l_i} ≤ 1
            "InformationTheory.KraftMcMillan",  // necessary/sufficient for prefix-free
            "InformationTheory.SourceCodingTheorem", // expected length ≥ H(X)
            "InformationTheory.AsymptoticEquipartition", // source coding via AEP
            "InformationTheory.UniversalCoding", // universal code families
            "InformationTheory.LempelZiv",      // LZ universal coding
            "InformationTheory.ArithmeticCoding", // arithmetic coding existence
            // ================================================================
            // Rate-Distortion Theory
            // ================================================================
            "InformationTheory.DistortionMeasure", // d(x,y) distortion
            "InformationTheory.RateDistortionFunction", // R(D)
            "InformationTheory.RateDistortionTheorem", // achievability/converse
            "InformationTheory.BlahutArimoto",     // algorithm for R(D)
            "InformationTheory.GaussianRateDistortion", // closed form for Gaussian
            "InformationTheory.WaterFilling",      // water-filling solution
            // ================================================================
            // Multiuser Information Theory
            // ================================================================
            "InformationTheory.MultipleAccessChannel", // MAC definition
            "InformationTheory.MACCapacityRegion",     // MAC capacity region
            "InformationTheory.BroadcastChannel",      // BC definition
            "InformationTheory.BroadcastCapacity",     // known BC regions
            "InformationTheory.InterferenceChannel",   // interference channel
            "InformationTheory.HanKobayashiRegion",    // HK achievable region
            "InformationTheory.SlepianWolf",           // distributed source coding
            "InformationTheory.WynerZiv",              // lossy coding with side info
            "InformationTheory.GelfandPinsker",        // coding with state info
            "InformationTheory.CutSetBound",           // network converse bound
            // ================================================================
            // Information-Theoretic Learning
            // ================================================================
            "InformationTheory.InformationBottleneck", // IB objective
            "InformationTheory.InfoNCE",               // InfoNCE lower bound
            "InformationTheory.MinimumDescriptionLength", // MDL principle
            "InformationTheory.PACBayesMutualInfo",    // PAC-Bayes via MI
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.information_theory_init = true;
        Ok(())
    }

    /// Check if InformationTheory has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_information_theory` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_information_theory(&self) -> bool {
        self.information_theory_init
    }
}
