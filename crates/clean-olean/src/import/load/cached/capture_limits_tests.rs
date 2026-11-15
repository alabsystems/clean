// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::captured_guard_tests::{bytes, write};
use super::*;
use crate::import::typed_imports::typed_import_count;

#[test]
fn explicit_limits_preserve_the_ordinary_checked_population_and_order() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Root", "Root.a", &[("Child", false)]);
    write(dir.path(), "Child", "Child.a", &[]);
    let roots = ["Root".into()];
    let paths = [dir.path().to_path_buf()];
    let mut ordinary = Environment::default();
    let mut old_parts = Vec::new();
    let old = load_modules_with_deps_checked(
        &mut ordinary,
        &roots,
        &paths,
        &mut |_, _, _| Ok(()),
        &mut |name, _, part| {
            old_parts.push((
                name.clone(),
                part.base.to_vec(),
                part.ir.map(<[u8]>::to_vec),
            ));
            Ok(())
        },
    )
    .unwrap();
    let total: usize = old_parts.iter().map(|(_, part, _)| part.len()).sum();
    let largest = old_parts
        .iter()
        .map(|(_, part, _)| part.len())
        .max()
        .unwrap();
    let mut limited = Environment::default();
    let mut new_parts = Vec::new();
    let new = load_modules_with_deps_checked_with_limits(
        &mut limited,
        &roots,
        &paths,
        ModuleCaptureLimits::new(largest, total, 2, 1),
        &mut |_, _, _| Ok(()),
        &mut |name, _, part| {
            new_parts.push((
                name.clone(),
                part.base.to_vec(),
                part.ir.map(<[u8]>::to_vec),
            ));
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(old_parts, new_parts);
    assert_eq!(old.len(), new.len());
    for name in ["Root.a", "Child.a"] {
        assert!(ordinary.get_const(&Name::from_string(name)).is_some());
        assert!(limited.get_const(&Name::from_string(name)).is_some());
    }
}

#[test]
fn total_bytes_are_shared_by_roots_and_dependencies_before_registration() {
    let dir = tempfile::tempdir().unwrap();
    let root = bytes("Root.a", &[("Child", false)]);
    let child = bytes("Child.a", &[]);
    std::fs::write(dir.path().join("Root.olean"), &root).unwrap();
    std::fs::write(dir.path().join("Child.olean"), &child).unwrap();
    let mut env = Environment::default();
    let mut captured = Vec::new();
    let result = load_modules_with_deps_checked_with_limits(
        &mut env,
        &["Root".into()],
        &[dir.path().into()],
        ModuleCaptureLimits::new(
            root.len().max(child.len()),
            root.len() + child.len() - 1,
            2,
            1,
        ),
        &mut |_, _, _| Ok(()),
        &mut |name, _, _| {
            captured.push(name.clone());
            Ok(())
        },
    );
    assert!(
        matches!(result, Err(ImportError::FileUnreadable { path, source })
        if path.ends_with("Child.olean") && source.kind() == std::io::ErrorKind::InvalidData)
    );
    assert_eq!(captured, [Name::from_string("Root")]);
    assert_eq!(env.constants().count(), 0);
}

#[test]
fn module_and_import_limits_stop_graph_growth_without_registering_a_prefix() {
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Root", "Root.a", &[("Child", false)]);
    write(dir.path(), "Child", "Child.a", &[]);
    for (modules, imports) in [(1, 8), (8, 0)] {
        let mut env = Environment::default();
        let mut paths = Vec::new();
        let result = load_modules_with_deps_checked_with_limits(
            &mut env,
            &["Root".into()],
            &[dir.path().into()],
            ModuleCaptureLimits::new(1024 * 1024, 2 * 1024 * 1024, modules, imports),
            &mut |name, _, _| {
                paths.push(name.clone());
                Ok(())
            },
            &mut |_, _, _| Ok(()),
        );
        assert!(matches!(result, Err(ImportError::ResourceLimit { .. })));
        assert_eq!(paths, [Name::from_string("Root")]);
        assert_eq!(env.constants().count(), 0);
    }
}

#[test]
fn import_rows_are_charged_before_their_allocation_or_decoding() {
    let dir = tempfile::tempdir().unwrap();
    let mut root = bytes("Root.a", &[("Child", false)]);
    let header = crate::parse_header(&root).unwrap();
    let region = crate::region::CompactedRegion::new(&root, header.base_addr);
    let at = region.ptr_to_offset(region.root_ptr().unwrap()).unwrap();
    let array = region
        .ptr_to_offset(region.read_u64_at(at + 8).unwrap())
        .unwrap();
    let first = region.array_elem_offset(array, 0, "test import").unwrap();
    // The envelope has one row, but the row is deliberately malformed. A
    // zero budget must refuse the envelope before trying to decode that row.
    root[first..first + 8].copy_from_slice(&0u64.to_le_bytes());
    assert_eq!(typed_import_count(&root).unwrap(), 1);
    assert!(parse_typed_imports(&root).is_err());
    std::fs::write(dir.path().join("Root.olean"), &root).unwrap();
    for allowed in [0, 1] {
        let mut env = Environment::default();
        let result = load_modules_with_deps_checked_with_limits(
            &mut env,
            &["Root".into()],
            &[dir.path().into()],
            ModuleCaptureLimits::new(root.len(), root.len(), 1, allowed),
            &mut |_, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        );
        if allowed == 0 {
            assert!(matches!(result, Err(ImportError::ResourceLimit { .. })));
        } else {
            assert!(matches!(result, Err(ImportError::FileParse { .. })));
        }
        assert_eq!(env.constants().count(), 0);
    }
}

#[test]
fn companion_rows_cannot_bypass_the_explicit_budget() {
    let hash = "0000000000000000000000000000000000000000";
    let empty = crate::payload::CleanPayload::default();
    for private_case in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let root = bytes("Root.a", &[]);
        let server =
            crate::OleanExporter::export_with_payload_after(&root, &[], &[], &[], hash, &empty)
                .unwrap();
        let predecessor = if private_case { &server } else { &root };
        let mut companion = crate::OleanExporter::export_with_payload_after(
            predecessor,
            &[("Child", false)],
            &[],
            &[],
            hash,
            &empty,
        )
        .unwrap();
        let header = crate::parse_header(&companion).unwrap();
        let region = crate::region::CompactedRegion::new(&companion, header.base_addr);
        let at = region.ptr_to_offset(region.root_ptr().unwrap()).unwrap();
        let array = region
            .ptr_to_offset(region.read_u64_at(at + 8).unwrap())
            .unwrap();
        let first = region
            .array_elem_offset(array, 0, "test companion import")
            .unwrap();
        companion[first..first + 8].copy_from_slice(&0u64.to_le_bytes());
        let path = dir.path().join("Root.olean");
        std::fs::write(&path, &root).unwrap();
        let extension = if private_case {
            std::fs::write(path.with_extension("olean.server"), &server).unwrap();
            "olean.private"
        } else {
            "olean.server"
        };
        std::fs::write(path.with_extension(extension), &companion).unwrap();
        let expected = std::fs::canonicalize(&path)
            .unwrap()
            .with_extension(extension);
        for allowed in [0, 1] {
            let mut env = Environment::default();
            let result = load_modules_with_deps_checked_with_limits(
                &mut env,
                &["Root".into()],
                &[dir.path().into()],
                ModuleCaptureLimits::new(1024 * 1024, 1024 * 1024, 1, allowed),
                &mut |_, _, _| Ok(()),
                &mut |_, _, _| Ok(()),
            );
            if allowed == 0 {
                assert!(matches!(result, Err(ImportError::ResourceLimit { .. })));
            } else {
                assert!(
                    matches!(result, Err(ImportError::FileParse { path: failed, .. })
                    if failed == expected)
                );
            }
            assert_eq!(env.constants().count(), 0);
        }
    }
}

#[test]
fn companion_roots_borrowed_from_prior_parts_are_counted_and_supported() {
    let dir = tempfile::tempdir().unwrap();
    let root = bytes("Root.a", &[("Child", false)]);
    let header = crate::parse_header(&root).unwrap();
    let root_pointer = crate::region::CompactedRegion::new(&root, header.base_addr)
        .root_ptr()
        .unwrap();
    let empty = crate::payload::CleanPayload::default();
    let hash = "0000000000000000000000000000000000000000";
    let mut server =
        crate::OleanExporter::export_with_payload_after(&root, &[], &[], &[], hash, &empty)
            .unwrap();
    // Empty real companions may borrow a prior captured ModuleData root.
    // All three parts therefore decode the base's one import row.
    let header_size = crate::header::HEADER_SIZE;
    server[header_size..header_size + 8].copy_from_slice(&root_pointer.to_le_bytes());
    let mut private =
        crate::OleanExporter::export_with_payload_after(&server, &[], &[], &[], hash, &empty)
            .unwrap();
    private[header_size..header_size + 8].copy_from_slice(&root_pointer.to_le_bytes());
    let path = dir.path().join("Root.olean");
    std::fs::write(&path, &root).unwrap();
    std::fs::write(path.with_extension("olean.server"), &server).unwrap();
    std::fs::write(path.with_extension("olean.private"), &private).unwrap();
    write(dir.path(), "Child", "Child.a", &[]);
    for allowed in [2, 3] {
        let mut env = Environment::default();
        let result = load_modules_with_deps_checked_with_limits(
            &mut env,
            &["Root".into()],
            &[dir.path().into()],
            ModuleCaptureLimits::new(1024 * 1024, 1024 * 1024, 2, allowed),
            &mut |_, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        );
        if allowed == 2 {
            assert!(matches!(result, Err(ImportError::ResourceLimit { .. })));
            assert_eq!(env.constants().count(), 0);
        } else {
            result.unwrap();
            assert!(env.get_const(&Name::from_string("Root.a")).is_some());
            assert!(env.get_const(&Name::from_string("Child.a")).is_some());
        }
    }
}

#[cfg(unix)]
#[test]
fn ordinary_loaders_follow_regular_aliases_and_keep_lexical_companions() {
    use std::os::unix::fs::symlink;
    let dir = tempfile::tempdir().unwrap();
    let selected = dir.path().join("selected");
    let stored = dir.path().join("stored");
    std::fs::create_dir(&selected).unwrap();
    std::fs::create_dir(&stored).unwrap();
    let base = bytes("Root.a", &[]);
    let empty = crate::payload::CleanPayload::default();
    let hash = "0000000000000000000000000000000000000000";
    let server =
        crate::OleanExporter::export_with_payload_after(&base, &[], &[], &[], hash, &empty)
            .unwrap();
    let private =
        crate::OleanExporter::export_with_payload_after(&server, &[], &[], &[], hash, &empty)
            .unwrap();
    let original = stored.join("Actual.olean");
    std::fs::write(&original, &base).unwrap();
    // These must never replace the lexical Root companions merely because
    // the base was canonicalized for cache identity.
    for extension in ["olean.server", "olean.private", "ir"] {
        std::fs::write(
            original.with_extension(extension),
            b"wrong canonical companion",
        )
        .unwrap();
    }
    let root = selected.join("Root.olean");
    symlink(&original, &root).unwrap();
    let canonical = std::fs::canonicalize(&original).unwrap();
    let ir = b"captured lexical IR";
    for (extension, contents) in [
        ("olean.server", server.as_slice()),
        ("olean.private", private.as_slice()),
        ("ir", ir.as_slice()),
    ] {
        let target = stored.join(format!("lexical-{extension}"));
        std::fs::write(&target, contents).unwrap();
        symlink(&target, root.with_extension(extension)).unwrap();
    }
    let mut checked = Environment::default();
    let mut captures = 0;
    load_modules_with_deps_checked(
        &mut checked,
        &["Root".into()],
        std::slice::from_ref(&selected),
        &mut |_, path, _| {
            assert_eq!(path, root);
            Ok(())
        },
        &mut |_, path, captured| {
            assert_eq!(path, root);
            assert_eq!(captured.canonical_path, canonical);
            assert_eq!(captured.base, base);
            assert_eq!(captured.server, Some(server.as_slice()));
            assert_eq!(captured.private, Some(private.as_slice()));
            assert_eq!(captured.ir, Some(ir.as_slice()));
            captures += 1;
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(captures, 1);
    assert!(checked.get_const(&Name::from_string("Root.a")).is_some());
    let mut ordinary = Environment::default();
    load_module_with_deps_cached(
        &mut ordinary,
        "Root",
        std::slice::from_ref(&selected),
        &ModuleCache::new(),
    )
    .unwrap();
    assert!(ordinary.get_const(&Name::from_string("Root.a")).is_some());
    // A dangling optional link remains present and unreadable on the real
    // loader route, even though all regular aliases above were supported.
    let server_path = root.with_extension("olean.server");
    std::fs::remove_file(&server_path).unwrap();
    symlink(stored.join("missing"), &server_path).unwrap();
    let mut refused = Environment::default();
    let result =
        load_module_with_deps_cached(&mut refused, "Root", &[selected], &ModuleCache::new());
    assert!(
        matches!(result, Err(ImportError::FileUnreadable { path, source })
        if path == server_path && source.kind() == std::io::ErrorKind::NotFound)
    );
    assert_eq!(refused.constants().count(), 0);
}

#[test]
fn a_file_grown_after_the_path_guard_is_bounded_by_the_actual_descriptor() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Root.olean");
    let original = bytes("Root.a", &[]);
    std::fs::write(&path, &original).unwrap();
    let mut env = Environment::default();
    let mut checked = 0;
    let result = load_modules_with_deps_checked_with_limits(
        &mut env,
        &["Root".into()],
        &[dir.path().into()],
        ModuleCaptureLimits::new(original.len(), original.len(), 1, 0),
        &mut |_, resolved, _| {
            assert_eq!(
                std::fs::metadata(resolved).unwrap().len(),
                original.len() as u64
            );
            std::fs::OpenOptions::new()
                .write(true)
                .open(resolved)
                .unwrap()
                .set_len(original.len() as u64 + 1)
                .unwrap();
            Ok(())
        },
        &mut |_, _, _| {
            checked += 1;
            Ok(())
        },
    );
    assert!(
        matches!(result, Err(ImportError::FileUnreadable { path: failed, source })
        if failed == path && source.kind() == std::io::ErrorKind::InvalidData)
    );
    assert_eq!(checked, 0);
    assert_eq!(env.constants().count(), 0);
}

#[test]
fn optional_ir_spends_the_same_budget_and_preserves_absence_and_empty() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Root.olean");
    let root = bytes("Root.a", &[]);
    std::fs::write(&path, &root).unwrap();
    let ir = path.with_extension("ir");
    std::fs::write(&ir, b"not an absent input").unwrap();
    let limits = ModuleCaptureLimits::new(root.len(), root.len(), 1, 0);
    let mut env = Environment::default();
    let mut checked = 0;
    let result = load_modules_with_deps_checked_with_limits(
        &mut env,
        &["Root".into()],
        &[dir.path().into()],
        limits,
        &mut |_, _, _| Ok(()),
        &mut |_, _, _| {
            checked += 1;
            Ok(())
        },
    );
    assert!(
        matches!(result, Err(ImportError::FileUnreadable { path: failed, .. }) if failed == ir)
    );
    assert_eq!(checked, 0);
    assert_eq!(env.constants().count(), 0);
    for present in [false, true] {
        if present {
            std::fs::write(&ir, []).unwrap();
        } else {
            std::fs::remove_file(&ir).unwrap();
        }
        let mut env = Environment::default();
        let mut observed = None;
        load_modules_with_deps_checked_with_limits(
            &mut env,
            &["Root".into()],
            &[dir.path().into()],
            limits,
            &mut |_, _, _| Ok(()),
            &mut |_, _, captured| {
                observed = Some(captured.ir.map(<[u8]>::to_vec));
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(observed, Some(if present { Some(vec![]) } else { None }));
        assert!(env.get_const(&Name::from_string("Root.a")).is_some());
    }
}

#[test]
fn a_real_checked_cache_hit_cannot_bypass_a_stricter_capture_budget() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Root.olean");
    let root = bytes("Root.a", &[]);
    std::fs::write(&path, &root).unwrap();
    let cache = ModuleCache::new();
    let roots = [Name::from_string("Root")];
    let paths = [dir.path().to_path_buf()];
    let mut original = Environment::default();
    load_captured_graph(
        &mut original,
        &roots,
        &paths,
        &cache,
        false,
        Some(&mut |_, _, _| Ok(())),
        Some(&mut |_, _, _| Ok(())),
        true,
        None,
    )
    .unwrap();
    let captured = CapturedModule::read(&path)
        .unwrap()
        .capture_ir(&path)
        .unwrap();
    assert!(
        cache.get_direct(&captured).is_some(),
        "must exercise an actual populated cache"
    );
    let mut fresh = Environment::default();
    let mut checked = 0;
    let result = load_captured_graph(
        &mut fresh,
        &roots,
        &paths,
        &cache,
        false,
        Some(&mut |_, _, _| Ok(())),
        Some(&mut |_, _, _| {
            checked += 1;
            Ok(())
        }),
        true,
        Some(ModuleCaptureLimits::new(root.len() - 1, root.len(), 1, 0)),
    );
    assert!(matches!(result, Err(ImportError::FileUnreadable { .. })));
    assert_eq!(checked, 0);
    assert_eq!(fresh.constants().count(), 0);
}

#[cfg(unix)]
#[test]
fn replacing_a_guarded_regular_path_with_a_fifo_cannot_block_the_loader() {
    use std::os::unix::fs::{symlink, FileTypeExt};
    use std::sync::mpsc;
    use std::time::Duration;
    let dir = tempfile::tempdir().unwrap();
    write(dir.path(), "Root", "Root.a", &[]);
    let fifo = dir.path().join("Pipe");
    assert!(std::process::Command::new("mkfifo")
        .arg(&fifo)
        .status()
        .unwrap()
        .success());
    assert!(std::fs::symlink_metadata(&fifo)
        .unwrap()
        .file_type()
        .is_fifo());
    let search = dir.path().to_path_buf();
    let (send, receive) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let mut env = Environment::default();
        let mut checked = 0;
        let result = load_modules_with_deps_checked_with_limits(
            &mut env,
            &["Root".into()],
            &[search],
            ModuleCaptureLimits::new(1024 * 1024, 1024 * 1024, 1, 0),
            &mut |_, path, _| {
                assert!(std::fs::metadata(path).unwrap().is_file());
                std::fs::remove_file(path).unwrap();
                symlink(&fifo, path).unwrap();
                Ok(())
            },
            &mut |_, _, _| {
                checked += 1;
                Ok(())
            },
        );
        let _ = send.send((result, checked, env.constants().count()));
    });
    let (result, checked, constants) = receive
        .recv_timeout(Duration::from_secs(2))
        .expect("checked import blocked on a FIFO substituted after the path guard");
    worker.join().unwrap();
    assert!(
        matches!(result, Err(ImportError::FileUnreadable { source, .. })
        if source.kind() == std::io::ErrorKind::InvalidInput)
    );
    assert_eq!(checked, 0);
    assert_eq!(constants, 0);
}
