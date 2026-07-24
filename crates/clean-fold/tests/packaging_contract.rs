// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::{Path, PathBuf};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crate directory should have a workspace root")
        .to_path_buf()
}

fn section_after<'a>(config: &'a str, header: &str) -> &'a str {
    config
        .split(header)
        .nth(1)
        .and_then(|rest| rest.split("\n[").next())
        .expect("config should contain the requested section")
}

#[test]
fn clean_package_declares_canonical_binary_contract() {
    let workspace = workspace_root();
    let workspace_manifest = fs::read_to_string(workspace.join("Cargo.toml"))
        .expect("workspace manifest should be readable");
    let clean_manifest = fs::read_to_string(workspace.join("crates/clean/Cargo.toml"))
        .expect("clean manifest should be readable");
    let clean_cli_manifest = fs::read_to_string(workspace.join("crates/clean-cli/Cargo.toml"))
        .expect("clean-cli manifest should be readable");

    assert!(
        clean_manifest.contains("[[bin]]\nname = \"clean\"\npath = \"src/bin/clean.rs\""),
        "clean package should own the canonical clean binary target via a local wrapper"
    );
    assert!(
        clean_manifest.contains("clean-cli.workspace = true"),
        "clean package should depend on the shared clean-cli library entrypoint"
    );
    assert!(
        workspace_manifest.contains("clean-cli = { path = \"crates/clean-cli\" }"),
        "workspace dependencies should expose clean-cli for the clean wrapper"
    );
    assert!(
        clean_cli_manifest.contains("[[bin]]\nname = \"clean-cli\""),
        "clean-cli package should expose the renamed non-canonical binary target"
    );
}

#[test]
fn linux_x86_64_cross_target_avoids_host_native_cpu_flag() {
    let config = fs::read_to_string(workspace_root().join(".cargo/config.toml"))
        .expect("workspace cargo config should be readable");
    let build_section = section_after(&config, "[build]");
    let linux_x86_64_section = section_after(
        &config,
        "[target.'cfg(all(target_arch = \"x86_64\", target_os = \"linux\"))']",
    );

    assert!(
        build_section.contains("target-cpu=native"),
        "build section should keep the local host-tuned default"
    );
    assert!(
        linux_x86_64_section.contains("target-cpu=x86-64"),
        "linux/x86_64 target should pin a portable CPU baseline"
    );
    assert!(
        !linux_x86_64_section.contains("target-cpu=native"),
        "linux/x86_64 target must not inherit the host-only native CPU flag"
    );
}
