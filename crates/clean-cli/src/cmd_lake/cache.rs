// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cache management and .olean pack/unpack/upload.

use crate::cmd_core::resolve_project_dir;
use std::path::PathBuf;

/// Get cached .olean files
pub(super) fn lake_cache_get(verbose: bool, dir: Option<PathBuf>) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;

    // Check for cache executable (like Mathlib's cache tool)
    let cache_exe = config.exes.iter().find(|e| e.name == "cache");

    if let Some(exe) = cache_exe {
        println!("Found cache executable: {}", exe.name);
        println!("To download cache, run:");
        println!("  clean lake exe cache get");
        return Ok(());
    }

    // Check standard cache locations
    let cache_dir = cwd.join(".lake").join("cache");
    let cloud_dir = cwd.join(".lake").join("cloud");

    if verbose {
        println!("Checking cache locations...");
        println!("  Local cache: {}", cache_dir.display());
        println!("  Cloud cache: {}", cloud_dir.display());
    }

    if !cache_dir.exists() && !cloud_dir.exists() {
        println!("No cache configured for this project.");
        println!();
        println!("To use caching:");
        println!("  1. For Mathlib projects: run 'lake exe cache get'");
        println!("  2. For custom projects: define a 'cache' executable in lakefile.lean");
        return Ok(());
    }

    if cache_dir.exists() {
        let entries = std::fs::read_dir(&cache_dir)?;
        let count = entries.count();
        println!("Local cache: {} entries in {}", count, cache_dir.display());
    }

    if cloud_dir.exists() {
        let entries = std::fs::read_dir(&cloud_dir)?;
        let count = entries.count();
        println!("Cloud cache: {} entries in {}", count, cloud_dir.display());
    }

    Ok(())
}

/// Upload .olean files to cache
pub(super) fn lake_cache_put(verbose: bool, dir: Option<PathBuf>) -> anyhow::Result<()> {
    use clean_lake::Workspace;

    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;
    let ws = Workspace::from_config(&cwd, config);

    let build_lib = ws.lib_dir();

    if !build_lib.exists() {
        anyhow::bail!("No build output found. Run 'clean lake build' first.");
    }

    // Count .olean files
    let olean_files: Vec<_> = walkdir::WalkDir::new(&build_lib)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "olean"))
        .collect();

    if verbose {
        println!(
            "Found {} .olean files in {}",
            olean_files.len(),
            build_lib.display()
        );
    }

    if olean_files.is_empty() {
        println!("No .olean files to cache. Run 'clean lake build' first.");
        return Ok(());
    }

    // Create local cache directory
    let cache_dir = cwd.join(".lake").join("cache");
    std::fs::create_dir_all(&cache_dir)?;

    // Copy files to cache (simple local caching)
    let mut cached = 0;
    for entry in &olean_files {
        let rel_path = entry.path().strip_prefix(&build_lib)?;
        let cache_path = cache_dir.join(rel_path);

        if let Some(parent) = cache_path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        std::fs::copy(entry.path(), &cache_path)?;
        cached += 1;

        if verbose {
            println!("  Cached: {}", rel_path.display());
        }
    }

    println!("Cached {} .olean files to {}", cached, cache_dir.display());
    println!();
    println!("Note: Cloud cache upload requires authentication configuration.");
    println!("For Mathlib, use 'lake exe cache put' with proper setup.");

    Ok(())
}

/// Add files to the local cache
pub(super) fn lake_cache_add(
    files: &[String],
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir.clone())?;
    let cache_dir = cwd.join(".lake").join("cache");
    std::fs::create_dir_all(&cache_dir)?;

    if files.is_empty() {
        // Add all .olean files from build directory
        return lake_cache_put(verbose, dir);
    }

    let mut added = 0;
    for file in files {
        let path = PathBuf::from(file);
        if !path.exists() {
            eprintln!("Warning: {file} does not exist, skipping");
            continue;
        }

        let dest = cache_dir.join(path.file_name().unwrap_or_default());
        std::fs::copy(&path, &dest)?;
        added += 1;

        if verbose {
            println!("  Added: {} -> {}", file, dest.display());
        }
    }

    println!("Added {added} file(s) to cache");

    Ok(())
}

/// Recursively collect .olean files from a directory.
fn collect_oleans(
    dir: &std::path::Path,
    base: &std::path::Path,
    files: &mut Vec<(PathBuf, PathBuf)>,
) -> std::io::Result<()> {
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir)? {
            let path = entry?.path();
            if path.is_dir() {
                collect_oleans(&path, base, files)?;
            } else if path.extension().is_some_and(|e| e == "olean") {
                let rel = path.strip_prefix(base).unwrap_or(&path).to_path_buf();
                files.push((path, rel));
            }
        }
    }
    Ok(())
}

/// Recursively scan for .olean files, returning relative paths as strings.
fn scan_oleans(
    dir: &std::path::Path,
    base: &std::path::Path,
    files: &mut Vec<String>,
) -> std::io::Result<()> {
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir)? {
            let path = entry?.path();
            if path.is_dir() {
                scan_oleans(&path, base, files)?;
            } else if path.extension().is_some_and(|e| e == "olean") {
                let rel = path.strip_prefix(base).unwrap_or(&path);
                files.push(rel.display().to_string());
            }
        }
    }
    Ok(())
}

/// Recursively collect .olean and .ilean artifact files.
fn collect_artifacts(dir: &std::path::Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir)? {
            let path = entry?.path();
            if path.is_dir() {
                collect_artifacts(&path, files)?;
            } else if path
                .extension()
                .is_some_and(|e| e == "olean" || e == "ilean")
            {
                files.push(path);
            }
        }
    }
    Ok(())
}

/// Pack .olean files into an archive
///
/// Uses a simple JSON manifest + directory copy format.
/// For tar.gz support, use the system `tar` command.
pub(super) fn lake_pack(
    output: Option<PathBuf>,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let build_dir = cwd.join(".lake").join("build");

    if !build_dir.exists() {
        anyhow::bail!("Build directory does not exist. Run 'lake build' first.");
    }

    let output_path = output.unwrap_or_else(|| cwd.join("build-cache"));

    if verbose {
        println!("Packing build artifacts to {}...", output_path.display());
    }

    // Collect .olean files
    let mut files = Vec::new();
    collect_oleans(&build_dir, &cwd, &mut files)?;

    if files.is_empty() {
        println!("No .olean files found to pack.");
        return Ok(());
    }

    // Create output directory
    std::fs::create_dir_all(&output_path)?;

    // Copy files preserving directory structure
    for (src, rel) in &files {
        let dest = output_path.join(rel);
        if let Some(parent) = dest.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::copy(src, &dest)?;
        if verbose {
            println!("  Packed: {}", rel.display());
        }
    }

    // Write manifest
    let manifest_path = output_path.join("manifest.json");
    let manifest: Vec<_> = files
        .iter()
        .map(|(_, rel)| rel.display().to_string())
        .collect();
    let manifest_json = serde_json::to_string_pretty(&manifest)?;
    std::fs::write(&manifest_path, manifest_json)?;

    println!(
        "Packed {} .olean file(s) to {}",
        files.len(),
        output_path.display()
    );
    println!(
        "Tip: Use 'tar -czf build-cache.tar.gz {}' for a compressed archive.",
        output_path.display()
    );

    Ok(())
}

/// Unpack .olean files from a pack directory
pub(super) fn lake_unpack(
    archive: &std::path::Path,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;

    if !archive.exists() {
        anyhow::bail!("Archive directory does not exist: {}", archive.display());
    }

    if verbose {
        println!("Unpacking {} to {}...", archive.display(), cwd.display());
    }

    // Read manifest if available
    let manifest_path = archive.join("manifest.json");
    let files: Vec<String> = if manifest_path.exists() {
        let content = std::fs::read_to_string(&manifest_path)?;
        serde_json::from_str(&content)?
    } else {
        // Fall back to scanning for .olean files
        let mut found = Vec::new();
        scan_oleans(archive, archive, &mut found)?;
        found
    };

    if files.is_empty() {
        println!("No .olean files found in archive.");
        return Ok(());
    }

    let mut count = 0;
    for rel_path in &files {
        let src = archive.join(rel_path);
        let dest = cwd.join(rel_path);

        if !src.exists() {
            if verbose {
                eprintln!("  Warning: {} not found in archive", rel_path);
            }
            continue;
        }

        if let Some(parent) = dest.parent() {
            std::fs::create_dir_all(parent)?;
        }

        std::fs::copy(&src, &dest)?;
        count += 1;

        if verbose {
            println!("  Extracted: {}", rel_path);
        }
    }

    println!("Unpacked {} file(s)", count);

    Ok(())
}

/// Upload build artifacts to Reservoir
pub(super) fn lake_upload(
    verbose: bool,
    dry_run: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    let cwd = resolve_project_dir(dir)?;
    let config = super::load_project_config(&cwd)?;
    let build_dir = cwd.join(".lake").join("build");

    if !build_dir.exists() {
        anyhow::bail!("Build directory does not exist. Run 'lake build' first.");
    }

    if verbose {
        println!("Preparing upload for package: {}", config.package.name);
    }

    // Collect files to upload
    let mut files = Vec::new();
    collect_artifacts(&build_dir, &mut files)?;

    if files.is_empty() {
        println!("No artifacts found to upload.");
        return Ok(());
    }

    if dry_run {
        println!("Would upload {} file(s):", files.len());
        for file in &files {
            let rel_path = file.strip_prefix(&cwd).unwrap_or(file);
            println!("  {}", rel_path.display());
        }
        println!("\nRun without --dry-run to upload.");
        return Ok(());
    }

    // TODO(#421): Implement actual Reservoir upload
    // Blockers: Reservoir API is not publicly documented. See issue for details.
    // Need: API endpoint, authentication format for ~/.lake/credentials.json
    anyhow::bail!(
        "Reservoir upload not yet implemented.\n\
         Configure reservoir credentials in ~/.lake/credentials.json"
    )
}
