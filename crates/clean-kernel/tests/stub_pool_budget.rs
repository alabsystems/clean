// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Compile the actual private pool source, without exporting a kernel test door.
#[path = "../src/env/stub_upgrade_pool.rs"]
mod worker_pool;

use std::ffi::OsStr;
use std::process::Command;

#[test]
fn hardware_default_and_explicit_caps() {
    let count = |available, cargo: Option<&str>, rayon: Option<&str>| {
        worker_pool::worker_count(available, cargo.map(OsStr::new), rayon.map(OsStr::new))
    };
    assert_eq!(count(32, None, None), 32);
    assert_eq!(count(0, None, None), 1);
    assert_eq!(count(1, Some("8"), None), 1);
    assert_eq!(count(32, Some("6"), None), 6);
    assert_eq!(count(32, None, Some("2")), 2);
    assert_eq!(count(32, Some("6"), Some("2")), 2);
    assert_eq!(count(32, Some("2"), Some("6")), 2);
    assert_eq!(count(4, Some("16"), Some("8")), 4);
    assert_eq!(count(32, Some("0006"), None), 6);
}

#[test]
fn malformed_admission_is_serial_and_rayon_auto_stays_capped() {
    for value in [
        "",
        "0",
        "-1",
        "+2",
        " 2",
        "2 ",
        "2x",
        "1e3",
        "999999999999999999999999",
    ] {
        assert_eq!(
            worker_pool::worker_count(32, Some(OsStr::new(value)), None),
            1,
            "Cargo {value:?}"
        );
    }
    for value in [
        "",
        "0",
        "-1",
        " 2",
        "2 ",
        "2x",
        "1e3",
        "999999999999999999999999",
    ] {
        assert_eq!(
            worker_pool::worker_count(32, None, Some(OsStr::new(value))),
            32
        );
        assert_eq!(
            worker_pool::worker_count(32, Some(OsStr::new("6")), Some(OsStr::new(value))),
            6
        );
    }
    assert_eq!(
        worker_pool::worker_count(32, None, Some(OsStr::new("+2"))),
        2
    );
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        assert_eq!(
            worker_pool::worker_count(32, Some(OsStr::from_bytes(b"\xff")), None),
            1
        );
        assert_eq!(
            worker_pool::worker_count(32, Some(OsStr::new("6")), Some(OsStr::from_bytes(b"\xff"))),
            6
        );
    }
}

/// Two-way: the child re-run (`POOL_CHILD_ENV` set below) measures the private
/// pool in a fresh process; the parent spawns one child per environment row and
/// asserts each passes. Both branches assert, so neither path is a skip.
const POOL_CHILD_ENV: &str = "CLEAN_STUB_POOL_EXPECTED";

#[test]
fn actual_pool_in_fresh_processes() {
    if let Ok(expected) = std::env::var(POOL_CHILD_ENV) {
        let expected: usize = expected.parse().unwrap();
        let actual = worker_pool::pool().map_or(1, |pool| {
            let actual = pool.current_num_threads();
            assert_eq!(pool.install(rayon::current_num_threads), actual);
            actual
        });
        assert_eq!(actual, expected);
        eprintln!("actual private stub pool workers={actual}");
    } else {
        let hardware = std::thread::available_parallelism().map_or(1, usize::from);
        for (cargo, rayon, expected) in [
            (None, None, hardware),
            (Some("2"), None, hardware.min(2)),
            (Some("6"), Some("2"), hardware.min(2)),
            (Some("2"), Some("6"), hardware.min(2)),
            (Some("1"), None, 1),
            (Some("bad"), Some("6"), 1),
            (Some("6"), Some("0"), hardware.min(6)),
            (Some("6"), Some("bad"), hardware.min(6)),
            (None, Some("0"), hardware),
        ] {
            let mut child = Command::new(std::env::current_exe().unwrap());
            child
                .args([
                    "--exact",
                    "actual_pool_in_fresh_processes",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env_remove("CARGO_BUILD_JOBS")
                .env_remove("RAYON_NUM_THREADS")
                .env(POOL_CHILD_ENV, expected.to_string());
            if let Some(cap) = cargo {
                child.env("CARGO_BUILD_JOBS", cap);
            }
            if let Some(cap) = rayon {
                child.env("RAYON_NUM_THREADS", cap);
            }
            let result = child.output().unwrap();
            let stderr = String::from_utf8_lossy(&result.stderr);
            eprintln!("Cargo={cargo:?}, Rayon={rayon:?}, expected={expected}: {stderr}");
            assert!(
                result.status.success(),
                "Cargo={cargo:?}, Rayon={rayon:?}: {}{stderr}",
                String::from_utf8_lossy(&result.stdout),
            );
            // A filter that matched nothing would pass vacuously: require the
            // child to have actually measured the pool.
            assert!(
                stderr.contains("actual private stub pool workers="),
                "Cargo={cargo:?}, Rayon={rayon:?}: child did not run the measurement"
            );
        }
    }
}

#[test]
fn normal_kernel_upgrade_still_checks_valid_and_tampered_values() {
    use clean_kernel::env::{ConstantInfo, Declaration, EnvError, Environment, TrustedEnvExt};
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;
    let mut env = Environment::new();
    let mut records = Vec::new();
    for i in 0..5 {
        let name = Name::from_string(&format!("PoolBudget.{i}"));
        env.add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();
        let value = if i == 4 {
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0))
        } else {
            Expr::prop()
        };
        records.push(ConstantInfo::new(
            name,
            vec![],
            Expr::type_(),
            Some(value),
            false,
        ));
    }
    let (accepted, refused) = env.upgrade_axiom_stubs_checked(records.into_iter());
    assert_eq!(accepted, 4);
    assert_eq!(refused.len(), 1);
    assert!(matches!(refused[0].1, EnvError::TypeCheckFailed { .. }));
    assert!(env
        .get_const(&Name::from_string("PoolBudget.4"))
        .unwrap()
        .value
        .is_none());
}
