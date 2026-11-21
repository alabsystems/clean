// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn limited(part: usize, total: usize) -> CaptureBudget {
    CaptureBudget::new(Some(ModuleCaptureLimits::new(part, total, 8, 8)))
}

fn invalid_data(result: Result<Vec<u8>, ImportError>) {
    assert!(
        matches!(result, Err(ImportError::FileUnreadable { source, .. })
        if source.kind() == io::ErrorKind::InvalidData)
    );
}

#[test]
fn regular_bytes_absence_and_present_empty_remain_distinct() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Part.olean");
    assert!(optional(&path, &mut limited(8, 8)).unwrap().is_none());
    std::fs::write(&path, []).unwrap();
    assert_eq!(optional(&path, &mut limited(0, 0)).unwrap(), Some(vec![]));
    std::fs::write(&path, b"abcdefgh").unwrap();
    assert_eq!(required(&path, &mut limited(8, 8)).unwrap(), b"abcdefgh");
    for (mut budget, why) in [(limited(7, 8), "per-part"), (limited(8, 7), "graph")] {
        assert!(
            matches!(required(&path, &mut budget), Err(ImportError::ResourceLimit { reason, .. })
            if reason.contains("Part.olean") && reason.contains(why))
        );
    }
    // A caller's stricter policy is not installed on ordinary imports.
    assert_eq!(
        required(&path, &mut CaptureBudget::default()).unwrap(),
        b"abcdefgh"
    );
}

#[test]
fn sparse_oversize_refuses_before_reading_or_spending_the_budget() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Sparse.olean");
    File::create(&path)
        .unwrap()
        .set_len(16 * 1024 * 1024)
        .unwrap();
    let mut budget = limited(8, 8);
    assert!(matches!(
        required(&path, &mut budget),
        Err(ImportError::ResourceLimit { .. })
    ));
    assert_eq!(budget.bytes, 0);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 16 * 1024 * 1024);
}

#[test]
fn the_whole_graph_budget_counts_each_present_part() {
    let dir = tempfile::tempdir().unwrap();
    let base = dir.path().join("Root.olean");
    let server = base.with_extension("olean.server");
    let private = base.with_extension("olean.private");
    let ir = base.with_extension("ir");
    for path in [&base, &server, &private, &ir] {
        std::fs::write(path, b"12").unwrap();
    }
    let mut budget = limited(2, 7);
    for path in [&base, &server, &private] {
        assert_eq!(required(path, &mut budget).unwrap(), b"12");
    }
    assert_eq!(budget.bytes, 6);
    assert!(matches!(optional(&ir, &mut budget),
        Err(ImportError::ResourceLimit { reason, .. })
        if reason.contains("Root.ir") && reason.contains("6 used, 7 limit")));
    assert_eq!(budget.bytes, 6);
    std::fs::remove_file(&ir).unwrap();
    assert!(optional(&ir, &mut budget).unwrap().is_none());
}

#[test]
fn growing_and_shrinking_after_open_are_unreadable_not_truncated_inputs() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Changing.olean");
    for replacement in [b"short".as_slice(), b"a longer replacement".as_slice()] {
        std::fs::write(&path, b"original").unwrap();
        let mut budget = limited(64, 64);
        let opened = OpenedPart::from_file(open(&path).unwrap(), &path).unwrap();
        std::fs::write(&path, replacement).unwrap();
        invalid_data(opened.read(&mut budget));
        assert_eq!(budget.bytes, 0);
    }
}

#[cfg(unix)]
#[test]
fn restoring_mtime_does_not_hide_an_in_place_rewrite() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Rewrite.olean");
    std::fs::write(&path, b"original").unwrap();
    let mut budget = limited(8, 8);
    let opened = OpenedPart::from_file(open(&path).unwrap(), &path).unwrap();
    let modified = std::fs::metadata(&path).unwrap().modified().unwrap();
    std::fs::write(&path, b"replaced").unwrap();
    File::options()
        .write(true)
        .open(&path)
        .unwrap()
        .set_times(std::fs::FileTimes::new().set_modified(modified))
        .unwrap();
    invalid_data(opened.read(&mut budget));
    assert_eq!(budget.bytes, 0);
}

#[cfg(unix)]
#[test]
fn regular_symlink_aliases_bind_the_open_descriptor() {
    use std::os::unix::fs::symlink;
    let dir = tempfile::tempdir().unwrap();
    let first = dir.path().join("First.olean");
    let second = dir.path().join("Second.olean");
    let alias = dir.path().join("Alias.olean");
    std::fs::write(&first, b"original").unwrap();
    std::fs::write(&second, b"replaced").unwrap();
    symlink(&first, &alias).unwrap();
    let mut budget = limited(8, 8);
    let opened = OpenedPart::from_file(open(&alias).unwrap(), &alias).unwrap();
    std::fs::remove_file(&alias).unwrap();
    symlink(&second, &alias).unwrap();
    assert_eq!(opened.read(&mut budget).unwrap(), b"original");
    assert_eq!(required(&alias, &mut limited(8, 8)).unwrap(), b"replaced");
}

#[cfg(unix)]
#[test]
fn a_dangling_optional_symlink_is_present_but_unreadable() {
    use std::os::unix::fs::symlink;
    let dir = tempfile::tempdir().unwrap();
    let alias = dir.path().join("Missing.olean.private");
    symlink(dir.path().join("Absent"), &alias).unwrap();
    assert!(matches!(optional(&alias, &mut CaptureBudget::default()),
        Err(ImportError::FileUnreadable { source, .. })
        if source.kind() == io::ErrorKind::NotFound));
    assert!(std::fs::symlink_metadata(&alias)
        .unwrap()
        .file_type()
        .is_symlink());
}

#[cfg(unix)]
#[test]
fn fifo_and_fifo_symlink_refuse_without_waiting_for_a_writer() {
    use std::os::unix::fs::{symlink, FileTypeExt};
    use std::sync::mpsc;
    use std::time::Duration;
    let dir = tempfile::tempdir().unwrap();
    let fifo = dir.path().join("Pipe.olean");
    assert!(std::process::Command::new("mkfifo")
        .arg(&fifo)
        .status()
        .unwrap()
        .success());
    assert!(std::fs::symlink_metadata(&fifo)
        .unwrap()
        .file_type()
        .is_fifo());
    let alias = dir.path().join("Alias.olean.private");
    symlink(&fifo, &alias).unwrap();
    for (path, is_optional) in [(fifo, false), (alias, true)] {
        let (send, receive) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let result = if is_optional {
                optional(&path, &mut limited(8, 8)).map(|_| ())
            } else {
                required(&path, &mut limited(8, 8)).map(|_| ())
            };
            let _ = send.send(result);
        });
        let result = receive
            .recv_timeout(Duration::from_secs(2))
            .expect("module capture blocked on a FIFO with no writer");
        worker.join().unwrap();
        assert!(
            matches!(result, Err(ImportError::FileUnreadable { source, .. })
            if source.kind() == io::ErrorKind::InvalidInput)
        );
    }
}
