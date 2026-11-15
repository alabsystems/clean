// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A stand-in for an environment that takes long to free.
//!
//! [`gated_source`] is a constant source that serves nothing and whose drop
//! waits for the test to release it (up to the hang detector), then reports
//! the thread it ran on and whether the test released it. Installed as the
//! only reference in an environment, it makes freeing that environment last
//! exactly as long as the test wants, so a test can tell where a free ran and
//! whether the runtime served anything while it ran: a free on the test's own
//! runtime thread can never be released by the test, which waits on that
//! thread.

use clean_kernel::env::{ConstantInfo, ConstantSource};
use clean_kernel::Name;
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;
use std::time::{Duration, Instant};

/// A wait for something that must happen: a one-minute hang detector.
const HANG: Duration = Duration::from_secs(60);

#[derive(Debug)]
struct Gated {
    go: Mutex<mpsc::Receiver<()>>,
    freeing: mpsc::Sender<()>,
    freed: mpsc::Sender<(ThreadId, bool)>,
}

impl ConstantSource for Gated {
    fn get(&self, _name: &Name) -> Option<&ConstantInfo> {
        None
    }

    fn contains(&self, _name: &Name) -> bool {
        false
    }
}

impl Drop for Gated {
    fn drop(&mut self) {
        let _ = self.freeing.send(());
        let released = self
            .go
            .lock()
            .map(|go| go.recv_timeout(HANG).is_ok())
            .unwrap_or(false);
        let _ = self.freed.send((std::thread::current().id(), released));
    }
}

/// The test's side of a gated source.
pub(crate) struct FreeGate {
    go: mpsc::Sender<()>,
    freeing: mpsc::Receiver<()>,
    freed: mpsc::Receiver<(ThreadId, bool)>,
}

/// Where a gated free ran, and whether the test released it.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Freed {
    pub(crate) on: ThreadId,
    pub(crate) released: bool,
}

/// A gated constant source and its gate. Install the source as the only
/// reference to it (`Environment::set_constant_source`): it is freed with the
/// last environment that holds it.
pub(crate) fn gated_source() -> (Arc<dyn ConstantSource>, FreeGate) {
    let (go, go_rx) = mpsc::channel();
    let (freeing_tx, freeing) = mpsc::channel();
    let (freed_tx, freed) = mpsc::channel();
    let source = Arc::new(Gated {
        go: Mutex::new(go_rx),
        freeing: freeing_tx,
        freed: freed_tx,
    });
    (source, FreeGate { go, freeing, freed })
}

/// Wait on a free's signal without blocking the runtime.
async fn signalled<T>(what: &str, signal: &mpsc::Receiver<T>) -> T {
    let give_up = Instant::now() + HANG;
    loop {
        if let Ok(value) = signal.try_recv() {
            return value;
        }
        assert!(Instant::now() < give_up, "{what} never happened");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

impl FreeGate {
    /// Wait until the free has started (it then waits for [`Self::release`]).
    pub(crate) async fn freeing(&self) {
        signalled("the free", &self.freeing).await;
    }

    /// Let the free finish, and report where it ran.
    pub(crate) async fn release(self) -> Freed {
        let _ = self.go.send(());
        let (on, released) = signalled("the end of the free", &self.freed).await;
        Freed { on, released }
    }
}
