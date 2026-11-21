// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A caller's process-wide panic policy also applies during dependency probes.
//! The hook scenario runs in its own test process, never alongside other tests.

use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Duration;

const TEST_NAME: &str =
    "compile::panic_hook_tests::dependency_selection_preserves_caller_hook_during_overlap";
const CHILD: &str = "CLEAN_NATIVE_PANIC_HOOK_TEST_CHILD";
const REFUSAL: &str = "panic hook regression reached dependency route";
const WAIT: Duration = Duration::from_secs(60);

struct PolicyPanic;

fn caught_policy_panic() {
    assert!(std::panic::catch_unwind(|| std::panic::panic_any(PolicyPanic)).is_err());
}

fn held_selection(
    entered: mpsc::Sender<()>,
    release: mpsc::Receiver<()>,
) -> thread::JoinHandle<String> {
    thread::spawn(move || {
        let dir = tempfile::tempdir().expect("fixture directory");
        let source = dir.path().join("Hook.lean");
        std::fs::write(
            &source,
            "def panicHookDep : Nat := 7\ndef panicHookRoot : Nat := panicHookDep\n",
        )
        .expect("dependency fixture");
        let env = elaborate_file_to_env(&source).expect("elaborate dependency fixture");
        let dep = Name::from_string("panicHookDep");
        let route = |name: &Name| {
            if name != &dep {
                return DepRoute::Compile;
            }
            entered.send(()).expect("announce actual dependency route");
            release
                .recv_timeout(WAIT)
                .expect("release dependency route");
            DepRoute::Refuse(REFUSAL.to_owned())
        };
        match select_in_environment(
            env,
            &HashSet::new(),
            &Name::from_string("panicHookRoot"),
            0,
            &|_| false,
            &route,
            CodeMeaning::KernelValue,
        ) {
            Ok(_) => panic!("dependency route must refuse selection"),
            Err(error) => format!("{error:#}"),
        }
    })
}

fn isolated_hook_scenario() {
    let observed = Arc::new(AtomicUsize::new(0));
    let hook_observed = Arc::clone(&observed);
    let caller_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if info.payload().is::<PolicyPanic>() {
            hook_observed.fetch_add(1, Ordering::SeqCst);
        } else {
            caller_hook(info);
        }
    }));

    caught_policy_panic();
    assert_eq!(observed.swap(0, Ordering::SeqCst), 1, "caller hook premise");

    let (entered_a, ready_a) = mpsc::channel();
    let (release_a, held_a) = mpsc::channel();
    let first = held_selection(entered_a, held_a);
    ready_a.recv_timeout(WAIT).expect("first selection entered");

    let (entered_b, ready_b) = mpsc::channel();
    let (release_b, held_b) = mpsc::channel();
    let second = held_selection(entered_b, held_b);
    ready_b
        .recv_timeout(WAIT)
        .expect("second selection entered");

    caught_policy_panic();
    let overlapping = observed.load(Ordering::SeqCst);
    release_a.send(()).expect("release first selection");
    let first_refusal = first.join().expect("first selection thread");

    caught_policy_panic();
    let one_remaining = observed.load(Ordering::SeqCst);
    release_b.send(()).expect("release second selection");
    let second_refusal = second.join().expect("second selection thread");

    caught_policy_panic();
    let completed = observed.load(Ordering::SeqCst);
    // Keep the observations visible even if the broken implementation restored
    // a silent hook and consequently hides the later assertion's panic report.
    println!("\npanic_hook_counts={overlapping},{one_remaining},{completed}");
    assert_eq!(first_refusal, REFUSAL);
    assert_eq!(second_refusal, REFUSAL);
    assert_eq!((overlapping, one_remaining, completed), (1, 2, 3));
}

#[test]
fn dependency_selection_preserves_caller_hook_during_overlap() {
    if std::env::var_os(CHILD).is_some() {
        assert!(
            std::env::args()
                .skip(1)
                .eq(["--exact", TEST_NAME, "--nocapture"]),
            "install the caller hook only in the exact isolated test process"
        );
        isolated_hook_scenario();
        return;
    }

    // Only this isolated caller installs a hook. The parent test process keeps
    // its hook, environment and parallel tests unchanged. This starts no Rust
    // compiler or native code generator, just the current test executable.
    let result = std::process::Command::new(std::env::current_exe().expect("test executable"))
        .args(["--exact", TEST_NAME, "--nocapture"])
        .env(CHILD, "1")
        .output()
        .expect("run isolated hook scenario");
    let stdout = String::from_utf8_lossy(&result.stdout);
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(result.status.success(), "{stdout}\n{stderr}");
    let receipt = stdout
        .lines()
        .find(|line| line.starts_with("panic_hook_counts="))
        .expect("actual child hook observations");
    assert_eq!(receipt, "panic_hook_counts=1,2,3", "{stdout}");
    println!("\n{receipt}");
    assert!(stdout.contains("1 passed; 0 failed"), "{stdout}");
}
