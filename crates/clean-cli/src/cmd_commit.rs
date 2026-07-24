// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial commitment command handlers.

use clean_fold::commit::cli::CommitCommands;
use clean_fold::commit::{IpaScheme, KzgScheme, ProofCommitmentScheme};
use clean_kernel::cert::ProofCert;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::PathBuf;
use std::time::Instant;

/// Handle commit subcommands
pub(crate) fn handle_commit_command(command: CommitCommands) -> anyhow::Result<()> {
    match command {
        CommitCommands::Kzg {
            cert,
            output,
            max_degree,
            verbose,
        } => commit_kzg(&cert, &output, max_degree, verbose),
        CommitCommands::Ipa {
            cert,
            output,
            max_degree,
            verbose,
        } => commit_ipa(&cert, &output, max_degree, verbose),
        CommitCommands::Verify {
            commitment,
            cert,
            verbose,
        } => commit_verify(&commitment, &cert, verbose),
    }
}

/// Serializable commitment for file storage
#[derive(Serialize, Deserialize)]
pub(crate) struct SerializableCommitment {
    scheme: String,
    /// Commitment as hex-encoded bytes
    commitment: String,
    /// Degree of committed polynomial
    degree: usize,
    /// Hash of original certificate
    cert_hash: String,
    /// Max degree parameter used
    max_degree: u32,
}

/// Create a KZG commitment to a certificate
pub(crate) fn commit_kzg(
    cert_path: &PathBuf,
    output_path: &PathBuf,
    max_degree: u32,
    verbose: bool,
) -> anyhow::Result<()> {
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;

    let start = Instant::now();

    // Load certificate
    let cert_content = std::fs::read_to_string(cert_path)?;
    let cert: ProofCert = serde_json::from_str(&cert_content)
        .map_err(|e| anyhow::anyhow!("Failed to parse certificate: {e}"))?;

    if verbose {
        println!("Loaded certificate from {}", cert_path.display());
    }

    // Setup KZG scheme
    let degree = 1usize << max_degree;
    if verbose {
        println!("Setting up KZG with max degree 2^{max_degree} = {degree}...");
    }

    let setup_start = Instant::now();
    // Use deterministic RNG for reproducible trusted setup (for testing)
    let mut rng = StdRng::seed_from_u64(42);
    let kzg = KzgScheme::setup(degree, &mut rng)?;
    if verbose {
        println!(
            "  Setup completed in {:.3}s",
            setup_start.elapsed().as_secs_f64()
        );
    }

    // Create commitment
    let commit_start = Instant::now();
    let commitment = kzg.commit(&cert)?;
    if verbose {
        println!(
            "  Commitment computed in {:.3}s",
            commit_start.elapsed().as_secs_f64()
        );
    }

    // Compute certificate hash
    let mut hasher = DefaultHasher::new();
    cert_content.hash(&mut hasher);
    let cert_hash = format!("{:016x}", hasher.finish());

    // Serialize commitment
    let serializable = SerializableCommitment {
        scheme: "KZG".to_string(),
        commitment: format!("{commitment:?}"),
        degree,
        cert_hash,
        max_degree,
    };

    let json = serde_json::to_string_pretty(&serializable)?;
    std::fs::write(output_path, &json)?;

    let elapsed = start.elapsed();
    println!("Created KZG commitment in {:.3}s", elapsed.as_secs_f64());
    println!("  Output: {}", output_path.display());
    println!("  Polynomial degree: {degree}");

    Ok(())
}

/// Create an IPA commitment to a certificate
pub(crate) fn commit_ipa(
    cert_path: &PathBuf,
    output_path: &PathBuf,
    max_degree: u32,
    verbose: bool,
) -> anyhow::Result<()> {
    let start = Instant::now();

    // Load certificate
    let cert_content = std::fs::read_to_string(cert_path)?;
    let cert: ProofCert = serde_json::from_str(&cert_content)
        .map_err(|e| anyhow::anyhow!("Failed to parse certificate: {e}"))?;

    if verbose {
        println!("Loaded certificate from {}", cert_path.display());
    }

    // Setup IPA scheme
    let degree = 1usize << max_degree;
    if verbose {
        println!("Setting up IPA with max degree 2^{max_degree} = {degree}...");
    }

    let setup_start = Instant::now();
    let ipa = IpaScheme::setup(degree)?;
    if verbose {
        println!(
            "  Setup completed in {:.3}s",
            setup_start.elapsed().as_secs_f64()
        );
    }

    // Create commitment
    let commit_start = Instant::now();
    let commitment = ipa.commit(&cert)?;
    if verbose {
        println!(
            "  Commitment computed in {:.3}s",
            commit_start.elapsed().as_secs_f64()
        );
    }

    // Compute certificate hash
    let mut hasher = DefaultHasher::new();
    cert_content.hash(&mut hasher);
    let cert_hash = format!("{:016x}", hasher.finish());

    // Serialize commitment
    let serializable = SerializableCommitment {
        scheme: "IPA".to_string(),
        commitment: format!("{commitment:?}"),
        degree,
        cert_hash,
        max_degree,
    };

    let json = serde_json::to_string_pretty(&serializable)?;
    std::fs::write(output_path, &json)?;

    let elapsed = start.elapsed();
    println!("Created IPA commitment in {:.3}s", elapsed.as_secs_f64());
    println!("  Output: {}", output_path.display());
    println!("  Polynomial degree: {degree}");
    println!("  Note: IPA has no trusted setup (transparent)");

    Ok(())
}

/// Verify a polynomial commitment
pub(crate) fn commit_verify(
    commitment_path: &PathBuf,
    cert_path: &PathBuf,
    verbose: bool,
) -> anyhow::Result<()> {
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;

    let start = Instant::now();

    // Load commitment
    let commitment_content = std::fs::read_to_string(commitment_path)?;
    let saved: SerializableCommitment = serde_json::from_str(&commitment_content)
        .map_err(|e| anyhow::anyhow!("Failed to parse commitment: {e}"))?;

    // Load certificate
    let cert_content = std::fs::read_to_string(cert_path)?;
    let cert: ProofCert = serde_json::from_str(&cert_content)
        .map_err(|e| anyhow::anyhow!("Failed to parse certificate: {e}"))?;

    if verbose {
        println!(
            "Loaded commitment ({}) from {}",
            saved.scheme,
            commitment_path.display()
        );
        println!("Loaded certificate from {}", cert_path.display());
    }

    // Compute certificate hash and compare
    let mut hasher = DefaultHasher::new();
    cert_content.hash(&mut hasher);
    let computed_hash = format!("{:016x}", hasher.finish());

    let hash_matches = computed_hash == saved.cert_hash;

    // Re-compute commitment and compare
    let recomputed = match saved.scheme.as_str() {
        "KZG" => {
            // Use same deterministic RNG as during creation
            let mut rng = StdRng::seed_from_u64(42);
            let kzg = KzgScheme::setup(saved.degree, &mut rng)?;
            format!("{:?}", kzg.commit(&cert)?)
        }
        "IPA" => {
            let ipa = IpaScheme::setup(saved.degree)?;
            format!("{:?}", ipa.commit(&cert)?)
        }
        _ => anyhow::bail!("Unknown commitment scheme: {}", saved.scheme),
    };

    let commitment_matches = recomputed == saved.commitment;

    let elapsed = start.elapsed();

    if hash_matches && commitment_matches {
        println!("Commitment verification: PASSED");
        println!("  Scheme: {}", saved.scheme);
        println!("  Certificate hash: matches");
        println!("  Commitment: matches");
        println!("  Verified in {:.3}s", elapsed.as_secs_f64());
    } else {
        println!("Commitment verification: FAILED");
        if !hash_matches {
            println!("  Certificate hash: MISMATCH");
            println!("    Expected: {}", saved.cert_hash);
            println!("    Got: {computed_hash}");
        }
        if !commitment_matches {
            println!("  Commitment: MISMATCH");
        }
        std::process::exit(1);
    }

    Ok(())
}
