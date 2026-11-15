// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The TCP transport's request lines, read with a bound on what one line can
//! make the server hold (plan item `devsurface-server-trust-boundary`).
//!
//! `AsyncBufReadExt::read_line` holds a line of any length: it reads until the
//! newline arrives, so a peer that never sends one made the server buffer
//! everything it sent, and the line limit was compared only after that.
//! [`read_line_within`] holds at most one byte past its limit, and
//! [`discard_rest_of_line`] skips the rest of an overlong line through the
//! reader's own buffer, holding none of it.

use tokio::io::{AsyncBufRead, AsyncBufReadExt, AsyncReadExt};

/// What reading one line found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LineRead {
    /// The peer closed the connection before sending another byte.
    Closed,
    /// A line is in the buffer: through its newline, or what the peer sent
    /// before it closed the connection.
    Line,
    /// The line is longer than the limit: one byte past the limit is in the
    /// buffer. `ended`: the buffer holds the line's newline (the line is
    /// exactly that long); otherwise the rest of the line is still to come.
    TooLong {
        /// Whether the buffer ends with the line's newline.
        ended: bool,
    },
}

/// Read one line, its newline included, into `line` (cleared first), holding
/// no more than `limit + 1` bytes of it.
pub(crate) async fn read_line_within<R>(
    reader: &mut R,
    line: &mut Vec<u8>,
    limit: usize,
) -> std::io::Result<LineRead>
where
    R: AsyncBufRead + Unpin,
{
    line.clear();
    let most = u64::try_from(limit).unwrap_or(u64::MAX).saturating_add(1);
    let read = (&mut *reader).take(most).read_until(b'\n', line).await?;
    Ok(if read == 0 {
        LineRead::Closed
    } else if line.len() <= limit {
        LineRead::Line
    } else {
        LineRead::TooLong {
            ended: line.ends_with(b"\n"),
        }
    })
}

/// Skip the rest of a line whose first bytes were read already, through its
/// newline or to the end of the stream, holding none of it: how many bytes it
/// skipped.
pub(crate) async fn discard_rest_of_line<R>(reader: &mut R) -> std::io::Result<usize>
where
    R: AsyncBufRead + Unpin,
{
    let mut skipped = 0usize;
    loop {
        let (used, ended) = {
            let available = reader.fill_buf().await?;
            if available.is_empty() {
                return Ok(skipped);
            }
            match available.iter().position(|&b| b == b'\n') {
                Some(at) => (at + 1, true),
                None => (available.len(), false),
            }
        };
        reader.consume(used);
        skipped = skipped.saturating_add(used);
        if ended {
            return Ok(skipped);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::io::BufReader;

    #[tokio::test]
    async fn test_read_line_within_holds_one_byte_past_the_limit_of_an_endless_line() {
        // A peer that never sends a newline: `read_line` would never return.
        let mut reader = BufReader::new(tokio::io::repeat(b'x'));
        let mut line = Vec::new();
        let read = read_line_within(&mut reader, &mut line, 16)
            .await
            .expect("read");
        assert_eq!(read, LineRead::TooLong { ended: false });
        assert_eq!(line, vec![b'x'; 17]);
    }

    #[tokio::test]
    async fn test_read_line_within_reads_lines_up_to_the_limit() {
        let input: &[u8] = b"abc\n0123456789abcde\n0123456789abcdef\ntail";
        let mut reader = BufReader::new(input);
        let mut line = Vec::new();
        let mut seen = Vec::new();
        loop {
            let read = read_line_within(&mut reader, &mut line, 16)
                .await
                .expect("read");
            seen.push((read, String::from_utf8_lossy(&line).into_owned()));
            if read == LineRead::Closed {
                break;
            }
        }
        assert_eq!(
            seen,
            vec![
                (LineRead::Line, "abc\n".to_string()),
                // Sixteen bytes with the newline: at the limit.
                (LineRead::Line, "0123456789abcde\n".to_string()),
                // Seventeen with it: past the limit, and the newline read.
                (
                    LineRead::TooLong { ended: true },
                    "0123456789abcdef\n".to_string()
                ),
                // The end of the stream ends a line too.
                (LineRead::Line, "tail".to_string()),
                (LineRead::Closed, String::new()),
            ]
        );
    }

    #[tokio::test]
    async fn test_discard_rest_of_line_skips_through_the_newline_only() {
        let input = [vec![b'x'; 20_000], b"\nnext\n".to_vec()].concat();
        let mut reader = BufReader::with_capacity(64, input.as_slice());
        let mut line = Vec::new();
        let read = read_line_within(&mut reader, &mut line, 100)
            .await
            .expect("read");
        assert_eq!(read, LineRead::TooLong { ended: false });
        assert_eq!(
            discard_rest_of_line(&mut reader).await.expect("skip"),
            20_000 + 1 - 101
        );
        let read = read_line_within(&mut reader, &mut line, 100)
            .await
            .expect("read");
        assert_eq!((read, line.as_slice()), (LineRead::Line, &b"next\n"[..]));
        // At the end of the stream there is nothing left to skip.
        assert_eq!(discard_rest_of_line(&mut reader).await.expect("skip"), 0);
    }
}
