// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The host owns its build identity; the reusable elaborator owns admission.

use super::OracleCompilerError;
use std::sync::OnceLock;

/// Stable policy, independent of which Trust source revision built the host.
const HOST_TOOLCHAIN_BOUND: bool = match option_env!("CFG_TRUST_ORACLE_HOST") {
    None => false,
    Some(value) => !(value.len() == 1 && value.as_bytes()[0] == b'0'),
};
static HOST: HostIdentity = HostIdentity::new();

// An older bootstrap has no runtime-binding handshake. Retain its existing
// admission check. Participating builds exclude this macro before expansion,
// so their elaborator fingerprint does not depend on the changing build ID.
#[cfg(not(clean_runtime_oracle_host))]
fn legacy_build_commit() -> Option<&'static str> {
    option_env!("CFG_VER_HASH")
}

#[cfg(clean_runtime_oracle_host)]
fn legacy_build_commit() -> Option<&'static str> {
    None
}

struct HostIdentity {
    commit: OnceLock<Option<String>>,
}

impl HostIdentity {
    const fn new() -> Self {
        Self {
            commit: OnceLock::new(),
        }
    }

    fn bind(&self, commit: Option<&str>, required: bool) -> Result<(), OracleCompilerError> {
        let fail = |detail: &str| OracleCompilerError::HostIdentity {
            detail: detail.to_owned(),
        };
        let desired = match commit {
            Some(commit)
                if commit.len() == 40 && commit.bytes().all(|byte| byte.is_ascii_hexdigit()) =>
            {
                Some(commit.to_owned())
            }
            Some(_) => return Err(fail("the host supplied an invalid Trust build identity")),
            None if required => {
                return Err(fail("a Trust host must supply its loaded build identity"))
            }
            None => None,
        };
        let established = self.commit.get_or_init(|| desired.clone());
        if established != &desired {
            return Err(fail(
                "the loaded host identity cannot be replaced or downgraded",
            ));
        }
        Ok(())
    }

    fn expected(&self, required: bool) -> Result<Option<String>, OracleCompilerError> {
        // First use also freezes a standalone host. Otherwise an oracle
        // admitted while unbound could survive a later, incompatible binding
        // in the process-wide resolved-oracle cache.
        if !required {
            self.commit.get_or_init(|| None);
        }
        match self.commit.get() {
            Some(None) if required => Err(OracleCompilerError::HostIdentity {
                detail: "a standalone binding cannot satisfy a Trust host".to_owned(),
            }),
            Some(commit) => Ok(commit.clone()),
            None if required => Err(OracleCompilerError::HostIdentity {
                detail: "the Trust host has not bound its loaded build identity".to_owned(),
            }),
            None => Ok(None),
        }
    }
}

/// Bind the identity compiled into the running host before calling Clean.
/// Repeated calls with the same identity are harmless; conflicting identities
/// and attempts to downgrade a bound host fail. Trust-built libraries refuse
/// oracle admission until their host binds its identity. Standalone libraries
/// retain unbound admission when no Trust identity is supplied.
///
/// The identity must come from the host's loaded code (for example its own
/// `option_env!("CFG_VER_HASH")`), never from runtime environment variables,
/// a candidate compiler, or a file that may have replaced the running image.
pub fn bind_host_toolchain(commit: Option<&str>) -> Result<(), OracleCompilerError> {
    if let Some(expected) = legacy_build_commit() {
        if commit != Some(expected) {
            return Err(OracleCompilerError::HostIdentity {
                detail: "the loaded host differs from this legacy toolchain build".to_owned(),
            });
        }
    }
    HOST.bind(commit, HOST_TOOLCHAIN_BOUND)
}

pub(super) fn host_toolchain_commit() -> Result<Option<String>, OracleCompilerError> {
    if let Some(commit) = legacy_build_commit() {
        return Ok(Some(commit.to_owned()));
    }
    HOST.expected(HOST_TOOLCHAIN_BOUND)
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIRST: &str = "0123456789012345678901234567890123456789";
    const SECOND: &str = "1123456789012345678901234567890123456789";

    #[test]
    fn bound_host_requires_an_identity_and_cannot_change_it() {
        let host = HostIdentity::new();
        assert!(host.expected(true).is_err());
        assert!(host.bind(None, true).is_err());
        assert!(host.bind(Some("unknown"), true).is_err());
        assert!(host.expected(true).is_err());
        host.bind(Some(FIRST), true).expect("first host binding");
        host.bind(Some(FIRST), true).expect("idempotent binding");
        assert_eq!(
            host.expected(true).expect("bound host").as_deref(),
            Some(FIRST)
        );
        assert!(host.bind(Some(SECOND), true).is_err());
        assert!(host.bind(None, false).is_err());
        assert_eq!(
            host.expected(true).expect("binding retained").as_deref(),
            Some(FIRST)
        );
    }

    #[test]
    fn standalone_binding_cannot_be_reinterpreted_as_a_different_host() {
        let host = HostIdentity::new();
        assert_eq!(host.expected(false).expect("standalone library"), None);
        assert!(host.bind(Some(FIRST), false).is_err());
        host.bind(None, false).expect("standalone host");
        assert!(host.expected(true).is_err());
        assert_eq!(host.expected(false).expect("binding retained"), None);
    }

    #[test]
    fn concurrent_hosts_cannot_replace_the_first_identity() {
        let host = HostIdentity::new();
        let barrier = std::sync::Barrier::new(8);
        let results = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|index| {
                    let host = &host;
                    let barrier = &barrier;
                    scope.spawn(move || {
                        barrier.wait();
                        let commit = if index % 2 == 0 { FIRST } else { SECOND };
                        (commit, host.bind(Some(commit), true))
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("binding thread"))
                .collect::<Vec<_>>()
        });
        let winner = host.expected(true).expect("bound host").expect("identity");
        assert_eq!(
            results.iter().filter(|(_, result)| result.is_ok()).count(),
            4
        );
        for (commit, result) in results {
            assert_eq!(result.is_ok(), commit == winner);
        }
    }

    #[test]
    fn production_binding_checks_the_actual_oracle_in_a_fresh_process() {
        const CHILD: &str = "CLEAN_ORACLE_BINDING_TEST_CHILD";
        // Two-way: the child re-run (CHILD set below) binds and admits the
        // test's own compiler in a fresh process; the parent asserts it passed.
        if std::env::var_os(CHILD).is_some() {
            use super::super::{admit, admit_expecting};
            let cargo = std::env::var_os("CARGO").unwrap_or_else(|| env!("CARGO").into());
            let candidate = std::path::PathBuf::from(cargo)
                .canonicalize()
                .expect("Targo executable")
                .with_file_name(format!("trustc{}", std::env::consts::EXE_SUFFIX));
            let compiler = admit_expecting(&candidate, None).expect("test's native Trust compiler");
            // A legacy bootstrap reports its own compiled-in identity, and a
            // compiler from any other build is refused outright.
            let legacy_mismatch = match legacy_build_commit() {
                Some(expected) => {
                    assert_eq!(
                        host_toolchain_commit().expect("legacy identity").as_deref(),
                        Some(expected)
                    );
                    expected != compiler.commit()
                }
                None => false,
            };
            if legacy_mismatch {
                assert!(matches!(
                    admit(&candidate),
                    Err(OracleCompilerError::CommitMismatch { .. })
                ));
                assert!(bind_host_toolchain(Some(compiler.commit())).is_err());
            } else {
                if HOST_TOOLCHAIN_BOUND {
                    assert!(matches!(
                        admit(&candidate),
                        Err(OracleCompilerError::HostIdentity { .. })
                    ));
                    assert!(bind_host_toolchain(None).is_err());
                }
                bind_host_toolchain(Some(compiler.commit())).expect("bind loaded test host");
                admit(&candidate).expect("same-build oracle admitted");
                let other = if compiler.commit() == FIRST {
                    SECOND
                } else {
                    FIRST
                };
                assert!(bind_host_toolchain(Some(other)).is_err());
                assert!(bind_host_toolchain(None).is_err());
                admit(&candidate).expect("conflicting bind did not replace the host");
            }
        } else {
            let result =
                std::process::Command::new(std::env::current_exe().expect("test executable"))
                    .args(["--exact", "oracle_compiler::host_identity::tests::production_binding_checks_the_actual_oracle_in_a_fresh_process", "--nocapture"])
                    .env(CHILD, "1")
                    .output()
                    .expect("run isolated native binding test");
            assert!(
                result.status.success(),
                "{}\n{}",
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            );
            // An --exact filter that matched nothing would pass vacuously.
            assert!(
                String::from_utf8_lossy(&result.stdout).contains("1 passed"),
                "the isolated binding test did not run: {}",
                String::from_utf8_lossy(&result.stdout)
            );
        }
    }
}
