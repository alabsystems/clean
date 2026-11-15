// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Host C invocations share SDK discovery, including non-Apple Clang on macOS.

use std::process::Command;

pub(crate) fn command(compiler: &str) -> anyhow::Result<Command> {
    let mut command = Command::new(compiler);
    configure_sdk(&mut command)?;
    Ok(command)
}

#[cfg(not(target_os = "macos"))]
fn configure_sdk(_command: &mut Command) -> anyhow::Result<()> {
    Ok(())
}

#[cfg(target_os = "macos")]
fn configure_sdk(command: &mut Command) -> anyhow::Result<()> {
    use anyhow::{bail, Context};
    use std::path::Path;

    // Preserve an explicitly selected SDK, including an invalid one: silently
    // choosing a different SDK would change the caller's compilation inputs.
    if std::env::var_os("SDKROOT").is_some() {
        return Ok(());
    }
    // Apple's cc trampoline does this itself; a bundled upstream Clang does
    // not. Use the platform selector rather than guessing an installed path.
    let output = Command::new("/usr/bin/xcrun")
        .args(["--sdk", "macosx", "--show-sdk-path"])
        .output()
        .context("could not discover the macOS C SDK; set SDKROOT explicitly")?;
    if !output.status.success() {
        bail!(
            "could not discover the macOS C SDK; set SDKROOT explicitly: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    let root = std::str::from_utf8(&output.stdout)
        .context("macOS SDK selector returned a non-UTF-8 path")?
        .trim();
    if !Path::new(root).is_absolute() || !Path::new(root).is_dir() {
        bail!("macOS SDK selector returned an invalid SDK directory: {root:?}");
    }
    command.env("SDKROOT", root);
    Ok(())
}
