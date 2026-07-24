// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse release` — package, verify, download, and inspect mathverse library releases.

use std::path::PathBuf;

use crate::release::{
    download_release, package_release_with_stamp, print_manifest_summary, verify_release,
    ReleaseConfig, ReleaseManifest, DEFAULT_CLEAN_RELEASE_REPO,
};

use super::default_library_dir;

pub fn cmd_release(args: &[String]) {
    if args.is_empty() {
        print_release_usage();
        std::process::exit(1);
    }

    match args[0].as_str() {
        "build" => cmd_release_build(&args[1..]),
        "package" => cmd_release_package(&args[1..]),
        "verify" => cmd_release_verify(&args[1..]),
        "download" => cmd_release_download(&args[1..]),
        "info" => cmd_release_info(&args[1..]),
        "help" | "--help" | "-h" => print_release_usage(),
        other => {
            eprintln!("Unknown release subcommand: {other}");
            print_release_usage();
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// build
// ---------------------------------------------------------------------------

fn cmd_release_build(args: &[String]) {
    let mut output_dir: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--output" => {
                i += 1;
                output_dir = args.get(i).map(PathBuf::from);
            }
            other => {
                eprintln!("Unknown build option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let out = output_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-shards"));
    println!("Building mathverse shards...");
    println!("  Output: {}", out.display());
    println!();
    println!("This requires a Lean 4 toolchain and upstream library clones.");
    println!("For full build, use the shell pipeline:");
    println!("  ./scripts/download_all_libraries.sh");
    println!("  ./scripts/release_mathverse_shards.sh <lean4-lib-path>");
    println!();
    println!("For individual shard builds, use:");
    println!(
        "  cargo run --locked -p clean-mathverse --bin mathverse_shard -- build <olean-dir> {}",
        out.display()
    );
}

// ---------------------------------------------------------------------------
// package
// ---------------------------------------------------------------------------

fn cmd_release_package(args: &[String]) {
    let parsed = PackageArgs::parse(args).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });

    let version = parsed.version.unwrap_or_else(|| {
        eprintln!("Error: --version <VERSION> is required for packaging.");
        eprintln!("Example: mathverse release package --version 1.1.0");
        std::process::exit(1);
    });
    let shards = parsed.shard_dir;
    let out = parsed.output_dir;
    let kernel_verified_manifest = parsed.kernel_verified_manifest;

    println!("Packaging mathverse library v{version}...");
    println!("  Shard dir: {}", shards.display());
    println!("  Output:    {}", out.display());
    if let Some(m) = &kernel_verified_manifest {
        println!("  Stamping KernelVerified from manifest: {}", m.display());
    }

    match package_release_with_stamp(&shards, &version, &out, kernel_verified_manifest.as_deref()) {
        Ok(archive) => {
            println!("  Archive created: {}", archive.display());
            println!();
            println!("To publish, upload to GitHub Releases:");
            println!(
                "  gh release create mathverse-v{version} {} --title 'Mathverse Library v{version}'",
                archive.display()
            );
        }
        Err(e) => {
            eprintln!("Packaging failed: {e}");
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// verify
// ---------------------------------------------------------------------------

fn cmd_release_verify(args: &[String]) {
    let dir = if args.is_empty() || args[0].starts_with('-') {
        default_library_dir()
    } else {
        PathBuf::from(&args[0])
    };

    println!("Verifying mathverse library at {}...", dir.display());
    match verify_release(&dir) {
        Ok(result) => {
            println!("  Checked: {}", result.checked);
            println!("  Passed:  {}", result.passed);
            if !result.missing.is_empty() {
                println!("  Missing: {}", result.missing.len());
                for path in &result.missing {
                    println!("    - {path}");
                }
            }
            if !result.failures.is_empty() {
                println!("  Failed:  {}", result.failures.len());
                for f in &result.failures {
                    println!(
                        "    - {} (expected {}, got {})",
                        f.path,
                        &f.expected[..16],
                        &f.actual[..16]
                    );
                }
            }
            if result.is_ok() {
                println!("\nAll shards verified successfully.");
            } else {
                eprintln!("\nVerification FAILED.");
                std::process::exit(1);
            }
        }
        Err(e) => {
            eprintln!("Verification failed: {e}");
            eprintln!();
            eprintln!("Ensure mathverse-manifest.json exists in the library directory.");
            eprintln!("Run `mathverse download` to fetch the library first.");
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// download
// ---------------------------------------------------------------------------

fn cmd_release_download(args: &[String]) {
    let mut version: Option<String> = None;
    let mut output_dir: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--version" => {
                i += 1;
                version = args.get(i).cloned();
            }
            "--output" => {
                i += 1;
                output_dir = args.get(i).map(PathBuf::from);
            }
            other => {
                eprintln!("Unknown download option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let out = output_dir.unwrap_or_else(default_library_dir);
    let config = ReleaseConfig {
        repo: DEFAULT_CLEAN_RELEASE_REPO.to_string(),
        version,
        output_dir: out,
    };

    println!("Downloading mathverse library release...");
    match download_release(&config) {
        Ok(path) => {
            println!("Library downloaded to {}", path.display());
        }
        Err(e) => {
            eprintln!("Download failed: {e}");
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// info
// ---------------------------------------------------------------------------

fn cmd_release_info(args: &[String]) {
    let dir = if !args.is_empty() && !args[0].starts_with('-') {
        PathBuf::from(&args[0])
    } else {
        default_library_dir()
    };

    let manifest_path = dir.join("mathverse-manifest.json");
    match ReleaseManifest::from_file(&manifest_path) {
        Ok(manifest) => {
            if let Err(e) = print_manifest_summary(&manifest, std::io::stdout()) {
                eprintln!("Failed to print summary: {e}");
                std::process::exit(1);
            }
        }
        Err(e) => {
            eprintln!(
                "Could not read manifest at {}: {e}",
                manifest_path.display()
            );
            eprintln!();
            eprintln!("No mathverse library found. Run `mathverse download` to fetch it,");
            eprintln!("or set MATHVERSE_LIBRARY_PATH to your library directory.");
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// usage
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Parsed argument structs (testable)
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct PackageArgs {
    pub(crate) version: Option<String>,
    pub(crate) shard_dir: PathBuf,
    pub(crate) output_dir: PathBuf,
    /// Optional path to a `kernel-verified.json` manifest. When set, the shards
    /// are destructively stamped with `KernelVerified` before hashing (WS5).
    pub(crate) kernel_verified_manifest: Option<PathBuf>,
}

impl PackageArgs {
    pub(crate) fn parse(args: &[String]) -> Result<Self, String> {
        let mut version: Option<String> = None;
        let mut shard_dir: Option<PathBuf> = None;
        let mut output_dir: Option<PathBuf> = None;
        let mut kernel_verified_manifest: Option<PathBuf> = None;
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--version" => {
                    i += 1;
                    version = args.get(i).cloned();
                }
                "--shards" => {
                    i += 1;
                    shard_dir = args.get(i).map(PathBuf::from);
                }
                "--output" => {
                    i += 1;
                    output_dir = args.get(i).map(PathBuf::from);
                }
                "--kernel-verified-manifest" => {
                    i += 1;
                    kernel_verified_manifest = args.get(i).map(PathBuf::from);
                }
                other => return Err(format!("Unknown package option: {other}")),
            }
            i += 1;
        }
        Ok(Self {
            version,
            shard_dir: shard_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-shards")),
            output_dir: output_dir.unwrap_or_else(|| PathBuf::from("dist")),
            kernel_verified_manifest,
        })
    }
}

fn print_release_usage() {
    eprintln!("mathverse release — manage mathverse library releases");
    eprintln!();
    eprintln!("Subcommands:");
    eprintln!("  build              Build all shards from sources");
    eprintln!("  package            Package shards into tar.zst with manifest");
    eprintln!("  verify [DIR]       Verify shard integrity (blake3 checksums)");
    eprintln!("  download           Download release from GitHub");
    eprintln!("  info               Show current release version and stats");
    eprintln!();
    eprintln!("build options:");
    eprintln!("  --output <DIR>     Output directory (default: data/mathverse-shards)");
    eprintln!();
    eprintln!("package options:");
    eprintln!("  --version <V>      Release version (required, e.g. 1.1.0)");
    eprintln!("  --shards <DIR>     Shard directory (default: data/mathverse-shards)");
    eprintln!("  --output <DIR>     Output directory for archive (default: dist)");
    eprintln!(
        "  --kernel-verified-manifest <FILE>  Stamp KernelVerified into shard bytes \
         from this kernel-verified.json before hashing"
    );
    eprintln!();
    eprintln!("download options:");
    eprintln!("  --version <V>      Specify release version (default: latest)");
    eprintln!("  --output <DIR>     Output directory");
    eprintln!();
    eprintln!("info options:");
    eprintln!("  [DIR]              Library directory to inspect");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(strs: &[&str]) -> Vec<String> {
        strs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn test_package_args_defaults() {
        let parsed = PackageArgs::parse(&args(&[])).expect("should parse empty args");
        assert_eq!(parsed.version, None);
        assert_eq!(parsed.shard_dir, PathBuf::from("data/mathverse-shards"));
        assert_eq!(parsed.output_dir, PathBuf::from("dist"));
        assert_eq!(parsed.kernel_verified_manifest, None);
    }

    #[test]
    fn test_package_args_all_flags() {
        let parsed = PackageArgs::parse(&args(&[
            "--version",
            "1.1.0",
            "--shards",
            "/data/shards",
            "--output",
            "/dist",
            "--kernel-verified-manifest",
            "/data/shards/kernel-verified.json",
        ]))
        .expect("should parse all flags");
        assert_eq!(parsed.version, Some("1.1.0".to_string()));
        assert_eq!(parsed.shard_dir, PathBuf::from("/data/shards"));
        assert_eq!(parsed.output_dir, PathBuf::from("/dist"));
        assert_eq!(
            parsed.kernel_verified_manifest,
            Some(PathBuf::from("/data/shards/kernel-verified.json"))
        );
    }

    #[test]
    fn test_package_args_unknown_flag() {
        let result = PackageArgs::parse(&args(&["--invalid"]));
        assert!(result.is_err());
    }
}
