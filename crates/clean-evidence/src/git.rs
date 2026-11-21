// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;
use std::process::Command;

/// Read Git inputs from the named checkout, with its own index and objects.
pub(crate) fn read(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let mut command = Command::new("git");
    for (name, _) in std::env::vars_os() {
        if name
            .as_encoded_bytes()
            .get(..4)
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b"GIT_"))
        {
            command.env_remove(name);
        }
    }
    command
        .current_dir(root)
        .args(["--no-replace-objects", "--literal-pathspecs"])
        .args(args)
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_ALLOW_PROTOCOL", "")
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("GIT_OPTIONAL_LOCKS", "0");
    let error = |message: &str| format!("git {} at {}: {message}", args.join(" "), root.display());
    let output = command.output().map_err(|err| error(&err.to_string()))?;
    if !output.status.success() {
        return Err(error(String::from_utf8_lossy(&output.stderr).trim()));
    }
    Ok(output.stdout)
}
