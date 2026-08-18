// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake serve` — the Lake-compatible editor entry point.
//!
//! The Lean 4 VS Code extension (and other Lean-aware editors) launch the
//! language server by spawning `lake serve --` in the project root and
//! speaking LSP over the child's stdio. This handler mirrors that contract:
//! it loads the workspace configuration fail-closed (lakefile + optional
//! `lean-toolchain`), enters the project root, and runs the Clean LSP stdio
//! server ([`clean_lsp::run_server`]) until the client closes the stream.
//!
//! The launch is split behind a seam ([`serve_with_launcher`]) so unit tests
//! can prove the wiring — workspace resolution feeding the exec point —
//! without binding the test process to stdin/stdout.
//!
//! Nothing is printed on the success path: stdout is the LSP JSON-RPC
//! channel, and stderr chatter during startup can confuse editor clients
//! that buffer both streams (see the `clean_lsp::cli` module docs; the
//! top-level dispatcher also skips tracing-subscriber init for this verb).

use std::future::Future;
use std::path::PathBuf;

use anyhow::Context as _;
use clean_lake::{LakeError, Workspace};

/// Workspace facts resolved before the stdio server launches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ServeContext {
    /// Project root — the directory containing the lakefile (canonicalized
    /// by [`Workspace::load`]).
    pub(super) root: PathBuf,
    /// Package name declared in the lakefile.
    pub(super) package: String,
    /// `lean-toolchain` identifier, when the project pins one.
    pub(super) toolchain: Option<String>,
}

/// Resolve the project root and load the workspace configuration.
///
/// Fail-closed: a missing lakefile yields the shared friendly hint, and a
/// malformed lakefile or `lean-toolchain` propagates its parse error — the
/// server is never launched against an unloadable project.
fn prepare_serve(dir: Option<PathBuf>) -> anyhow::Result<ServeContext> {
    let root = crate::cmd_core::resolve_project_dir(dir)?;
    let ws = match Workspace::load(&root) {
        Ok(ws) => ws,
        Err(LakeError::LakefileNotFound(_)) => anyhow::bail!("{}", super::NO_LAKEFILE_HINT),
        Err(other) => {
            return Err(anyhow::Error::new(other)
                .context(format!("failed to load lakefile in {}", root.display())))
        }
    };
    Ok(ServeContext {
        root: ws.root().to_path_buf(),
        package: ws.config().package.name.clone(),
        toolchain: ws.toolchain().map(str::to_owned),
    })
}

/// Resolve the workspace, then hand the [`ServeContext`] to `launch`.
///
/// This is the testable exec seam: production passes the real stdio-server
/// launcher (see [`lake_serve`]); unit tests pass a recorder to prove the
/// wiring reaches the exec point with the resolved project root, without
/// binding to stdin/stdout.
async fn serve_with_launcher<F, Fut>(dir: Option<PathBuf>, launch: F) -> anyhow::Result<()>
where
    F: FnOnce(ServeContext) -> Fut,
    Fut: Future<Output = anyhow::Result<()>>,
{
    let ctx = prepare_serve(dir)?;
    launch(ctx).await
}

/// Handle `clean lake serve`: load the workspace config, enter the project
/// root, and serve LSP over stdio until the client closes the stream.
///
/// `_forwarded` holds arguments the editor appends after `--` (the VS Code
/// Lean extension launches `lake serve -- <args>`); they are accepted for
/// Lake CLI compatibility and intentionally unused — the transport is
/// always stdio.
pub(crate) async fn lake_serve(dir: Option<PathBuf>, _forwarded: &[String]) -> anyhow::Result<()> {
    serve_with_launcher(dir, |ctx| async move {
        // Silent by default: no tracing subscriber is installed for this verb
        // (see lib.rs::run), so this records the resolved workspace facts
        // only for embedders that wire a subscriber in-process.
        tracing::debug!(
            package = %ctx.package,
            toolchain = ctx.toolchain.as_deref().unwrap_or("<none>"),
            root = %ctx.root.display(),
            "lake serve: workspace resolved; starting stdio LSP server"
        );
        // Real `lake serve` runs in the project root, and relative paths in
        // the LSP backend resolve against the process cwd — mirror that.
        std::env::set_current_dir(&ctx.root)
            .with_context(|| format!("failed to enter project root {}", ctx.root.display()))?;
        clean_lsp::run_server().await;
        Ok(())
    })
    .await
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::sync::atomic::{AtomicBool, Ordering};
    use tempfile::TempDir;

    fn write_project(tmp: &TempDir) {
        fs::write(
            tmp.path().join("lakefile.lean"),
            "package servepkg\nlean_lib ServePkg\n",
        )
        .unwrap();
        // An exact-version identifier resolves without scanning installed
        // toolchains, keeping the assertion machine-independent.
        fs::write(
            tmp.path().join("lean-toolchain"),
            "leanprover/lean4:v4.13.0\n",
        )
        .unwrap();
    }

    #[test]
    fn test_prepare_serve_resolves_workspace_root_package_and_toolchain() {
        let tmp = TempDir::new().unwrap();
        write_project(&tmp);

        let ctx = prepare_serve(Some(tmp.path().to_path_buf()))
            .expect("prepare_serve should load the workspace");
        let canonical = tmp.path().canonicalize().expect("canonicalize temp root");
        assert_eq!(ctx.root, canonical);
        assert_eq!(ctx.package, "servepkg");
        assert_eq!(ctx.toolchain.as_deref(), Some("leanprover/lean4:v4.13.0"));
    }

    #[test]
    fn test_prepare_serve_missing_lakefile_fails_closed() {
        let tmp = TempDir::new().unwrap();
        let err = prepare_serve(Some(tmp.path().to_path_buf()))
            .expect_err("prepare_serve without a lakefile must fail");
        assert!(
            err.to_string()
                .contains("No lakefile.toml or lakefile.lean"),
            "expected the friendly no-lakefile hint, got: {err}"
        );
    }

    #[tokio::test]
    async fn test_serve_with_launcher_reaches_exec_seam_with_resolved_root() {
        let tmp = TempDir::new().unwrap();
        write_project(&tmp);

        let launched = AtomicBool::new(false);
        let canonical = tmp.path().canonicalize().expect("canonicalize temp root");
        serve_with_launcher(Some(tmp.path().to_path_buf()), |ctx| {
            launched.store(true, Ordering::SeqCst);
            assert_eq!(ctx.root, canonical, "launcher must see the project root");
            assert_eq!(ctx.package, "servepkg");
            std::future::ready(Ok(()))
        })
        .await
        .expect("serve wiring should reach the launcher");
        assert!(
            launched.load(Ordering::SeqCst),
            "the stdio-server exec seam must be invoked"
        );
    }

    #[tokio::test]
    async fn test_serve_with_launcher_missing_lakefile_never_launches() {
        let tmp = TempDir::new().unwrap();
        let launched = AtomicBool::new(false);
        let err = serve_with_launcher(Some(tmp.path().to_path_buf()), |_ctx| {
            launched.store(true, Ordering::SeqCst);
            std::future::ready(Ok(()))
        })
        .await
        .expect_err("serve without a lakefile must fail before exec");
        assert!(err.to_string().contains("No lakefile"));
        assert!(
            !launched.load(Ordering::SeqCst),
            "fail-closed: the server must not launch without a loadable workspace"
        );
    }
}
