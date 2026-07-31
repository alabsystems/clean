// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Streaming certificate I/O tests

use crate::cert::*;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;

fn explicit_v1_stream_fixture(certs: &[ProofCert]) -> Vec<u8> {
    use std::io::Write as _;

    let mut payload = Vec::new();
    for cert in certs {
        let bytes =
            bincode::serde::encode_to_vec(cert, bincode::config::standard()).expect("cert bytes");
        payload
            .write_all(&(bytes.len() as u32).to_le_bytes())
            .unwrap();
        payload.write_all(&bytes).unwrap();
    }
    let header = StreamingArchiveHeader {
        magic: StreamingArchiveHeader::MAGIC,
        version: 1,
        algorithm: 1,
        compression_level: 3,
        uncompressed_size: payload.len() as u64,
        cert_count: certs.len() as u64,
    };
    let header_bytes =
        bincode::serde::encode_to_vec(&header, bincode::config::standard()).expect("header bytes");
    let compressed = zstd::encode_all(payload.as_slice(), 3).expect("zstd fixture");
    let mut fixture = Vec::new();
    fixture
        .write_all(&(header_bytes.len() as u32).to_le_bytes())
        .unwrap();
    fixture.write_all(&header_bytes).unwrap();
    fixture.write_all(&compressed).unwrap();
    fixture
}

#[test]
fn test_streaming_header_new_zstd() {
    let header = StreamingArchiveHeader::new_zstd(3);
    assert_eq!(header.magic, StreamingArchiveHeader::MAGIC);
    assert_eq!(header.version, StreamingArchiveHeader::VERSION);
    assert_eq!(header.algorithm, 1); // Zstd
    assert_eq!(header.compression_level, 3);
    header.validate().expect("zstd header should validate");
}

#[test]
fn test_streaming_header_new_lz4() {
    let header = StreamingArchiveHeader::new_lz4();
    assert_eq!(header.magic, StreamingArchiveHeader::MAGIC);
    assert_eq!(header.version, StreamingArchiveHeader::VERSION);
    assert_eq!(header.algorithm, 0); // LZ4
    header.validate().expect("lz4 header should validate");
}

#[test]
fn test_streaming_header_invalid_magic() {
    let header = StreamingArchiveHeader {
        magic: *b"XXXX",
        version: 1,
        algorithm: 1,
        compression_level: 3,
        uncompressed_size: 0,
        cert_count: 0,
    };
    let err = header.validate().unwrap_err();
    assert!(
        matches!(err, StreamingError::InvalidFormat(_)),
        "expected InvalidFormat for bad magic, got: {err:?}"
    );
}

#[test]
fn test_streaming_header_invalid_version() {
    let header = StreamingArchiveHeader {
        magic: StreamingArchiveHeader::MAGIC,
        version: 255, // Too high
        algorithm: 1,
        compression_level: 3,
        uncompressed_size: 0,
        cert_count: 0,
    };
    let err = header.validate().unwrap_err();
    assert!(
        matches!(err, StreamingError::InvalidFormat(_)),
        "expected InvalidFormat for bad version, got: {err:?}"
    );
}

#[test]
fn test_explicit_streaming_v1_fixture_remains_compatible() {
    let certs = vec![ProofCert::Sort {
        level: Level::zero(),
    }];
    let fixture = explicit_v1_stream_fixture(&certs);
    let mut reader =
        StreamingCertReader::new(std::io::Cursor::new(fixture)).expect("read v1 header");
    assert_eq!(reader.read_all().expect("read v1 fixture"), certs);
}

#[test]
fn test_streaming_rejects_legacy_version_zero() {
    use std::io::Write as _;

    let mut header = StreamingArchiveHeader::new_zstd(3);
    header.version = 0;
    let header_bytes = bincode::serde::encode_to_vec(&header, bincode::config::standard()).unwrap();
    let mut fixture = Vec::new();
    fixture
        .write_all(&(header_bytes.len() as u32).to_le_bytes())
        .unwrap();
    fixture.write_all(&header_bytes).unwrap();
    assert!(matches!(
        StreamingCertReader::new(std::io::Cursor::new(fixture)),
        Err(StreamingError::InvalidFormat(message))
            if message.contains("Unsupported version")
    ));
}

#[test]
fn test_streaming_header_algorithm() {
    let lz4 = StreamingArchiveHeader::new_lz4();
    assert_eq!(lz4.algorithm(), CompressionAlgorithm::Lz4);

    let zstd_default = StreamingArchiveHeader::new_zstd(3);
    assert_eq!(zstd_default.algorithm(), CompressionAlgorithm::ZstdDefault);

    let zstd_high = StreamingArchiveHeader::new_zstd(19);
    assert_eq!(zstd_high.algorithm(), CompressionAlgorithm::ZstdHigh);

    let zstd_max = StreamingArchiveHeader::new_zstd(22);
    assert_eq!(zstd_max.algorithm(), CompressionAlgorithm::ZstdMax);
}

#[test]
fn test_streaming_write_read_single_cert() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let mut buffer = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer, 3).expect("create writer failed");
        writer.write_cert(&cert).expect("write cert failed");
        assert_eq!(writer.cert_count(), 1);
        writer.finish().expect("finish failed");
    }

    let cursor = std::io::Cursor::new(buffer);
    let mut reader = StreamingCertReader::new(cursor).expect("create reader failed");

    let read_cert = reader.read_cert().expect("read cert failed");
    assert_eq!(read_cert, Some(cert));

    let next = reader.read_cert().expect("read next failed");
    assert_eq!(next, None);

    assert_eq!(reader.certs_read(), 1);
}

#[test]
fn test_streaming_write_read_multiple_certs() {
    let certs = vec![
        ProofCert::Sort {
            level: Level::zero(),
        },
        ProofCert::Sort {
            level: Level::succ(Level::zero()),
        },
        ProofCert::Pi {
            binder_info: BinderInfo::Default,
            arg_type_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
            arg_level: Level::succ(Level::zero()),
            body_type_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
            body_level: Level::succ(Level::zero()),
        },
    ];

    let mut buffer = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer, 3).expect("create writer failed");
        writer.write_certs(&certs).expect("write certs failed");
        assert_eq!(writer.cert_count(), 3);
        writer.finish().expect("finish failed");
    }

    let cursor = std::io::Cursor::new(buffer);
    let mut reader = StreamingCertReader::new(cursor).expect("create reader failed");

    let read_certs = reader.read_all().expect("read all failed");
    assert_eq!(read_certs.len(), 3);
    assert_eq!(read_certs, certs);
}

#[test]
fn test_partial_stream_consumer_can_drain_and_validate_terminal_boundary() {
    let certs = vec![
        ProofCert::Sort {
            level: Level::zero(),
        },
        ProofCert::Sort {
            level: Level::succ(Level::zero()),
        },
    ];
    let fixture = explicit_v1_stream_fixture(&certs);
    let mut reader =
        StreamingCertReader::new(std::io::Cursor::new(fixture)).expect("stream reader");
    assert_eq!(reader.read_cert().unwrap(), Some(certs[0].clone()));
    reader.finish().expect("drain and validate");
    assert_eq!(reader.certs_read(), 2);
}

#[test]
fn test_streaming_rejects_trailing_bytes_and_concatenated_frames() {
    let certs = vec![ProofCert::Sort {
        level: Level::zero(),
    }];
    let base = explicit_v1_stream_fixture(&certs);
    for suffix in [
        vec![0x42],
        zstd::encode_all(&b"second frame"[..], 3).expect("second frame"),
    ] {
        let mut bad = base.clone();
        bad.extend(suffix);
        let mut reader =
            StreamingCertReader::new(std::io::Cursor::new(bad)).expect("stream header");
        assert!(matches!(
            reader.read_all(),
            Err(StreamingError::InvalidFormat(message))
                if message.contains("trailing bytes")
        ));
    }
}

#[test]
fn test_streaming_file_roundtrip() {
    let certs = vec![
        ProofCert::Sort {
            level: Level::zero(),
        },
        ProofCert::Sort {
            level: Level::succ(Level::zero()),
        },
    ];

    // Use tempfile crate for unique temp file name (fixes race condition with parallel tests)
    let temp_file = tempfile::NamedTempFile::new().expect("create temp file failed");
    let temp_path = temp_file.path();

    let write_stats = stream_certs_to_file(temp_path, &certs, 3).expect("write to file failed");
    assert_eq!(write_stats.cert_count, 2);
    assert!(write_stats.compressed_bytes > 0);

    let (read_certs, read_stats) =
        stream_certs_from_file(temp_path).expect("read from file failed");
    assert_eq!(read_certs, certs);
    assert_eq!(read_stats.cert_count, 2);
    assert_eq!(read_stats.algorithm, CompressionAlgorithm::ZstdDefault);

    // temp_file is automatically cleaned up when it goes out of scope
}

#[test]
fn test_streaming_progress_callback() {
    use std::sync::{Arc, Mutex};

    let certs: Vec<ProofCert> = (0..10)
        .map(|i| ProofCert::Sort {
            level: if i == 0 {
                Level::zero()
            } else {
                Level::succ(Level::zero())
            },
        })
        .collect();

    // Track bytes processed (not cert count - callback reports bytes per doc)
    let bytes_processed = Arc::new(Mutex::new(0u64));
    let last_total = Arc::new(Mutex::new(None::<u64>));
    let call_count = Arc::new(Mutex::new(0u32));
    let prev_bytes = Arc::new(Mutex::new(0u64));
    let monotonic = Arc::new(Mutex::new(true));

    let mut buffer = Vec::new();
    {
        let bp = Arc::clone(&bytes_processed);
        let lt = Arc::clone(&last_total);
        let cc = Arc::clone(&call_count);
        let pb = Arc::clone(&prev_bytes);
        let mono = Arc::clone(&monotonic);
        let callback: StreamingProgressCallback = Box::new(move |current, total| {
            // Verify progress is monotonically increasing
            let mut prev = pb.lock().unwrap();
            if current < *prev {
                *mono.lock().unwrap() = false;
            }
            *prev = current;

            *bp.lock().unwrap() = current;
            *lt.lock().unwrap() = total;
            *cc.lock().unwrap() += 1;
        });
        let mut writer = StreamingCertWriter::new_zstd(&mut buffer, 3)
            .expect("create writer")
            .with_progress(callback);
        writer.write_certs(&certs).expect("write certs");
        writer.finish().expect("finish");
    }

    // Progress callback reports bytes_processed (not cert count) per documentation
    // The callback may be called multiple times per cert (buffer flushes, compression chunks)
    // so we verify callback was called and progress increased, not exact call count
    let final_bytes = *bytes_processed.lock().unwrap();
    let calls = *call_count.lock().unwrap();
    assert!(
        calls > 0,
        "Progress callback should be called at least once"
    );
    assert!(final_bytes > 0, "Bytes processed should be > 0");
    assert!(
        *monotonic.lock().unwrap(),
        "Progress should increase monotonically"
    );
    // Total is None for streaming writes (total size not known ahead of time)
    assert_eq!(
        *last_total.lock().unwrap(),
        None,
        "Total should be None for streaming writes"
    );
}

#[test]
fn test_streaming_stats_display() {
    let stats = StreamingStats {
        cert_count: 100,
        uncompressed_bytes: 10000,
        compressed_bytes: 2500,
        algorithm: CompressionAlgorithm::ZstdDefault,
    };

    let display = format!("{stats}");
    assert!(display.contains("certs: 100"));
    assert!(display.contains("uncompressed: 10000"));
    assert!(display.contains("compressed: 2500"));
    assert!(display.contains("ratio: 4.00x"));
    assert!(display.contains("Zstd"));
}

#[test]
fn test_streaming_stats_ratio() {
    let stats = StreamingStats {
        cert_count: 1,
        uncompressed_bytes: 1000,
        compressed_bytes: 250,
        algorithm: CompressionAlgorithm::Lz4,
    };
    assert!((stats.ratio() - 4.0).abs() < 0.001);

    let zero_stats = StreamingStats {
        cert_count: 0,
        uncompressed_bytes: 0,
        compressed_bytes: 0,
        algorithm: CompressionAlgorithm::Lz4,
    };
    assert_eq!(zero_stats.ratio(), 0.0);
}

#[test]
fn test_streaming_error_display() {
    let io_err = StreamingError::Io(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "file not found",
    ));
    assert!(format!("{io_err}").contains("I/O error"));

    let ser_err = StreamingError::Serialize("bad format".to_string());
    assert!(format!("{ser_err}").contains("Serialization error"));

    let decomp_err = StreamingError::Decompress("corrupt data".to_string());
    assert!(format!("{decomp_err}").contains("Decompression error"));

    let fmt_err = StreamingError::InvalidFormat("wrong header".to_string());
    assert!(format!("{fmt_err}").contains("Invalid format"));
}

#[test]
fn test_streaming_invalid_reader() {
    // Try to read from invalid data
    let bad_data = vec![0u8; 10];
    let cursor = std::io::Cursor::new(bad_data);
    let result = StreamingCertReader::new(cursor);
    match result {
        Err(StreamingError::InvalidFormat(_)) => {} // expected
        Err(other) => panic!("expected InvalidFormat for bad data, got: {other:?}"),
        Ok(_) => panic!("expected error for invalid data, got Ok"),
    }
}

#[test]
fn test_streaming_truncated_cert_errors() {
    // Write valid certs to a buffer
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let certs = vec![cert.clone(), cert.clone(), cert];

    let mut buffer = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer, 3).expect("create writer failed");
        writer.write_certs(&certs).expect("write certs failed");
        writer.finish().expect("finish failed");
    }

    // Truncate the buffer mid-stream (after header, but truncated cert data)
    // This should cause an IO error (not EOF at cert boundary).
    //
    // The cut is `len - 1`, not the historical fixed `len - 50`: commit
    // 886baf53 migrated bincode 1.3 (fixint) -> 2.0 (varint, `standard()`
    // config), which shrank this 3-cert stream below 50 bytes, so the fixed
    // subtraction underflowed (panic under the workspace's release
    // `overflow-checks = true`).
    //
    // Why exactly the LAST byte: probing zstd 0.13's `stream::Decoder` over
    // every truncation point of this frame shows it does NOT error at the
    // zstd layer for a mid-frame cut — it silently yields the decompressed
    // prefix and a clean EOF. The reader therefore only returns `Err` when
    // the surviving decompressed prefix ends MID-CERT (the payload
    // `read_exact` hits `UnexpectedEof` -> `StreamingError::Io`); a cut whose
    // decompressed prefix ends exactly on a cert boundary yields `Ok` with
    // fewer certs. This tiny stream is stored in a raw zstd block (frame
    // bytes map 1:1 onto the 18 decompressed bytes), so dropping the final
    // byte always leaves a partial third cert — the deterministic mid-cert
    // truncation this test wants.
    assert!(
        buffer.len() > 1,
        "test invariant: stream must be non-trivial (len = {})",
        buffer.len()
    );
    let truncated = &buffer[..buffer.len() - 1];
    let cursor = std::io::Cursor::new(truncated.to_vec());

    let reader_result = StreamingCertReader::new(cursor);
    match reader_result {
        Ok(mut reader) => {
            // Should get an error when reading certs (not Ok(None))
            let all_result = reader.read_all();
            assert!(
                all_result.is_err(),
                "Truncated stream should produce an error, not Ok"
            );
        }
        Err(e) => {
            // Reader creation detected truncation — verify it's an IO error
            let msg = format!("{e}");
            assert!(!msg.is_empty(), "Truncation error should have a message");
        }
    }
}

/// A reader that fails with a non-EOF error after reading some bytes
struct FailingReader {
    inner: std::io::Cursor<Vec<u8>>,
    bytes_until_fail: usize,
    bytes_read: usize,
}

impl std::io::Read for FailingReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if self.bytes_read >= self.bytes_until_fail {
            return Err(std::io::Error::new(
                std::io::ErrorKind::ConnectionReset,
                "simulated connection reset",
            ));
        }
        let remaining = self.bytes_until_fail - self.bytes_read;
        let max_read = remaining.min(buf.len());
        let result = self.inner.read(&mut buf[..max_read])?;
        self.bytes_read += result;
        Ok(result)
    }
}

#[test]
fn test_streaming_non_eof_error_propagates() {
    // Write a valid stream to a buffer
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let certs = vec![cert.clone(), cert.clone(), cert.clone(), cert];

    let mut buffer = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer, 3).expect("create writer failed");
        writer.write_certs(&certs).expect("write certs failed");
        writer.finish().expect("finish failed");
    }

    // Create a reader that fails after reading the header but mid-cert
    // Header is typically ~24 bytes, fail a bit after
    let failing_reader = FailingReader {
        inner: std::io::Cursor::new(buffer.clone()),
        bytes_until_fail: 30,
        bytes_read: 0,
    };

    let reader_result = StreamingCertReader::new(failing_reader);
    match reader_result {
        Ok(mut reader) => {
            // The reader was created; now read_cert should fail with an error
            let read_result = reader.read_cert();
            assert!(
                read_result.is_err(),
                "Non-EOF IO error must propagate as Err, got {read_result:?}"
            );
        }
        Err(e) => {
            // Reader creation hit the simulated error — verify it's ConnectionReset
            let msg = format!("{e}");
            assert!(
                msg.contains("connection reset") || msg.contains("ConnectionReset"),
                "Error should be the simulated ConnectionReset, got: {msg}"
            );
        }
    }
}

#[test]
fn test_streaming_empty_stream() {
    let certs: Vec<ProofCert> = vec![];

    let mut buffer = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer, 3).expect("create writer failed");
        writer.write_certs(&certs).expect("write certs failed");
        assert_eq!(writer.cert_count(), 0);
        writer.finish().expect("finish failed");
    }

    let cursor = std::io::Cursor::new(buffer);
    let mut reader = StreamingCertReader::new(cursor).expect("create reader failed");

    let read_certs = reader.read_all().expect("read all failed");
    assert!(read_certs.is_empty());
    assert_eq!(reader.certs_read(), 0);
}

#[test]
fn test_streaming_complex_certs() {
    // Build complex nested certificates
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let complex_cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Lam {
            binder_info: BinderInfo::Default,
            arg_type_cert: Box::new(ProofCert::Sort {
                level: Level::zero(),
            }),
            body_cert: Box::new(ProofCert::BVar {
                idx: 0,
                expected_type: Box::new(type0.clone()),
            }),
            result_type: Box::new(Expr::pi(BinderInfo::Default, type0.clone(), type0.clone())),
        }),
        fn_type: Box::new(Expr::pi(BinderInfo::Default, type0.clone(), type0.clone())),
        arg_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(type1.clone()),
    };

    let certs = vec![complex_cert.clone(), complex_cert.clone()];

    let mut buffer = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer, 3).expect("create writer failed");
        writer.write_certs(&certs).expect("write certs failed");
        writer.finish().expect("finish failed");
    }

    let cursor = std::io::Cursor::new(buffer);
    let mut reader = StreamingCertReader::new(cursor).expect("create reader failed");

    let read_certs = reader.read_all().expect("read all failed");
    assert_eq!(read_certs.len(), 2);
    assert_eq!(read_certs[0], complex_cert);
    assert_eq!(read_certs[1], complex_cert);
}

#[test]
fn test_streaming_compression_levels() {
    let certs: Vec<ProofCert> = (0..50)
        .map(|_| ProofCert::Sort {
            level: Level::zero(),
        })
        .collect();

    // Test default level (3)
    let mut buffer_default = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer_default, 3).expect("create writer");
        writer.write_certs(&certs).expect("write certs");
        writer.finish().expect("finish");
    }

    // Test high level (19)
    let mut buffer_high = Vec::new();
    {
        let mut writer =
            StreamingCertWriter::new_zstd(&mut buffer_high, 19).expect("create writer");
        writer.write_certs(&certs).expect("write certs");
        writer.finish().expect("finish");
    }

    // Both levels should produce valid compressed data
    // Note: For small data, higher levels don't always produce smaller output
    // due to zstd internal heuristics and streaming overhead
    assert!(!buffer_default.is_empty());
    assert!(!buffer_high.is_empty());

    // Both should decompress to the same certs
    let cursor_default = std::io::Cursor::new(buffer_default);
    let mut reader_default =
        StreamingCertReader::new(cursor_default).expect("create reader default");
    let read_default = reader_default.read_all().expect("read all default");

    let cursor_high = std::io::Cursor::new(buffer_high);
    let mut reader_high = StreamingCertReader::new(cursor_high).expect("create reader high");
    let read_high = reader_high.read_all().expect("read all high");

    assert_eq!(read_default, read_high);
    assert_eq!(read_default, certs);
}

// ========================================================================
// Bounds Check Tests (memory safety guards)
// ========================================================================

#[test]
fn test_streaming_rejects_oversized_header() {
    // Craft a raw byte stream whose header-length field exceeds MAX_HEADER_BYTES (1 MB).
    // The reader should reject this before allocating.
    let oversized_len: u32 = 2 * 1024 * 1024; // 2 MB
    let mut data = Vec::new();
    data.extend_from_slice(&oversized_len.to_le_bytes());
    // Pad with garbage (won't be read if the guard fires first)
    data.extend_from_slice(&[0xAA; 64]);

    let cursor = std::io::Cursor::new(data);
    let result = StreamingCertReader::new(cursor);
    match result {
        Err(StreamingError::InvalidFormat(msg)) => {
            assert!(
                msg.contains("header size") && msg.contains("exceeds maximum"),
                "expected oversized header message, got: {msg}"
            );
        }
        Err(other) => panic!("expected InvalidFormat for oversized header, got: {other:?}"),
        Ok(_) => panic!("expected InvalidFormat for oversized header, got Ok"),
    }
}

#[test]
fn test_streaming_rejects_oversized_cert_entry() {
    // Craft a valid archive whose compressed stream contains a cert-length
    // field that exceeds MAX_CERT_BYTES (256 MB). The reader should reject
    // this before attempting the allocation.
    use std::io::Write;

    let header = StreamingArchiveHeader::new_zstd(3);
    let header_bytes = bincode::serde::encode_to_vec(&header, bincode::config::standard())
        .expect("serialize header");
    let header_len = header_bytes.len() as u32;

    // Build the raw (uncompressed) cert stream: a single u32 length prefix
    // claiming 300 MB, which exceeds the 256 MB guard.
    let bogus_cert_len: u32 = 300 * 1024 * 1024;
    let raw_payload = bogus_cert_len.to_le_bytes();

    // Compress the bogus payload with zstd
    let compressed_payload =
        zstd::encode_all(raw_payload.as_slice(), 3).expect("zstd compress bogus payload");

    // Assemble the full archive: [header_len][header_bytes][zstd_stream]
    let mut buffer = Vec::new();
    buffer.write_all(&header_len.to_le_bytes()).unwrap();
    buffer.write_all(&header_bytes).unwrap();
    buffer.write_all(&compressed_payload).unwrap();

    let cursor = std::io::Cursor::new(buffer);
    let mut reader = StreamingCertReader::new(cursor).expect("create reader from crafted stream");

    // read_cert should hit the MAX_CERT_BYTES guard
    let result = reader.read_cert();
    match result {
        Err(StreamingError::Decompress(msg)) => {
            assert!(
                msg.contains("certificate size") && msg.contains("exceeds maximum"),
                "expected oversized cert message, got: {msg}"
            );
        }
        Err(other) => panic!("expected Decompress for oversized cert entry, got: {other:?}"),
        Ok(v) => panic!("expected Decompress for oversized cert entry, got Ok({v:?})"),
    }
}

#[test]
fn test_streaming_reader_rejects_lz4_algorithm() {
    // The streaming reader only supports Zstd. An LZ4 header should be rejected
    // with InvalidFormat even though LZ4 is a valid CompressionAlgorithm.
    use std::io::Write;

    let header = StreamingArchiveHeader::new_lz4();
    // Sanity: header itself validates fine
    header.validate().expect("LZ4 header validates");

    let header_bytes = bincode::serde::encode_to_vec(&header, bincode::config::standard())
        .expect("serialize LZ4 header");
    let header_len = header_bytes.len() as u32;

    let mut buffer = Vec::new();
    buffer.write_all(&header_len.to_le_bytes()).unwrap();
    buffer.write_all(&header_bytes).unwrap();
    // No compressed payload needed — rejection happens before reading certs

    let cursor = std::io::Cursor::new(buffer);
    let result = StreamingCertReader::new(cursor);
    match result {
        Err(StreamingError::InvalidFormat(msg)) => {
            assert!(
                msg.contains("Streaming only supports Zstd"),
                "expected Zstd-only message, got: {msg}"
            );
        }
        Err(other) => panic!("expected InvalidFormat for LZ4 reader, got: {other:?}"),
        Ok(_) => panic!("expected InvalidFormat for LZ4 reader, got Ok"),
    }
}

#[test]
fn test_streaming_header_rejects_unknown_algorithm() {
    // algorithm > 1 should fail validation
    let header = StreamingArchiveHeader {
        magic: StreamingArchiveHeader::MAGIC,
        version: StreamingArchiveHeader::VERSION,
        algorithm: 2, // Neither LZ4 (0) nor Zstd (1)
        compression_level: 0,
        uncompressed_size: 0,
        cert_count: 0,
    };
    let err = header.validate().unwrap_err();
    match err {
        StreamingError::InvalidFormat(msg) => {
            assert!(
                msg.contains("Unknown algorithm"),
                "expected 'Unknown algorithm' message, got: {msg}"
            );
        }
        other => panic!("expected InvalidFormat for algorithm=2, got: {other:?}"),
    }
}

#[test]
fn test_streaming_size_overflow_error_display() {
    // Verify the SizeOverflow variant formats correctly via thiserror
    let err = StreamingError::SizeOverflow {
        size: 5_000_000_000,
        max: u32::MAX,
    };
    let msg = format!("{err}");
    assert!(
        msg.contains("5000000000") && msg.contains("exceeds maximum"),
        "SizeOverflow display should include size and max, got: {msg}"
    );
}

// ========================================================================
// Dictionary Compression Tests
// ========================================================================
