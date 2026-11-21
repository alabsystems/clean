// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The module-header scan used by Lean's `--deps-json` and Lake. This scan
//! follows `Lean.Elab.ParseImportsFast`. Its prefix matching and diagnostics
//! differ from the command parser used by `--deps` and source elaboration.

use super::dialect::LeanDialect;
use serde::Serialize;
use serde_json::ser::{CharEscape, CompactFormatter, Formatter};
use std::io::{self, Read, Write};

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Import {
    import_all: bool,
    is_exported: bool,
    is_meta: bool,
    module: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Header {
    imports: Vec<Import>,
    is_module: bool,
}

#[derive(Serialize)]
struct FileResult {
    errors: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<Header>,
}

#[derive(Serialize)]
struct Report {
    imports: Vec<FileResult>,
}

struct ReportFormatter;

impl Formatter for ReportFormatter {
    fn write_char_escape<W: Write + ?Sized>(
        &mut self,
        writer: &mut W,
        escape: CharEscape,
    ) -> io::Result<()> {
        let escape = match escape {
            CharEscape::Backspace => CharEscape::AsciiControl(b'\x08'),
            CharEscape::FormFeed => CharEscape::AsciiControl(b'\x0c'),
            CharEscape::Tab => CharEscape::AsciiControl(b'\t'),
            other => other,
        };
        CompactFormatter.write_char_escape(writer, escape)
    }
}

pub(super) fn print(dialect: LeanDialect, stdin: bool, files: Vec<String>) -> i32 {
    let files = if stdin {
        let mut bytes = Vec::new();
        if let Err(error) = io::stdin().read_to_end(&mut bytes) {
            eprintln!("clean: `lean --stdin`: {error}");
            return 1;
        }
        String::from_utf8_lossy(&bytes)
            .lines()
            .map(str::to_owned)
            .collect()
    } else {
        files
    };
    let imports = files
        .iter()
        .map(|file| match read_header(dialect, file) {
            Ok(header) => FileResult {
                errors: Vec::new(),
                result: Some(header),
            },
            Err(error) => FileResult {
                errors: vec![error],
                result: None,
            },
        })
        .collect();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();
    let mut serializer = serde_json::Serializer::with_formatter(&mut stdout, ReportFormatter);
    if let Err(error) = (Report { imports }).serialize(&mut serializer) {
        eprintln!("clean: `lean --deps-json`: {error}");
        return 1;
    }
    if let Err(error) = writeln!(stdout) {
        eprintln!("clean: `lean --deps-json`: {error}");
        return 1;
    }
    0
}

fn read_header(dialect: LeanDialect, file: &str) -> Result<Header, String> {
    let bytes = std::fs::read(file).map_err(|error| match error.kind() {
        io::ErrorKind::NotFound => super::missing_file(dialect, file, &error),
        io::ErrorKind::IsADirectory => {
            let code = error.raw_os_error().unwrap_or(21);
            let detail = if dialect == LeanDialect::V4_36_0 {
                "illegal operation on a directory"
            } else {
                "is a directory"
            };
            format!("inappropriate type (error code: {code}, {detail})")
        }
        _ => format!("{error}\n  file: {file}"),
    })?;
    let source = std::str::from_utf8(&bytes)
        .map_err(|_| format!("Tried to read file '{file}' containing non UTF-8 data."))?;
    scan_header(source).map_err(|error| {
        let prefix = &source[..error.offset];
        let line_prefix = prefix.rsplit_once('\n').map_or(prefix, |(_, line)| line);
        let line = 1 + prefix.bytes().filter(|byte| *byte == b'\n').count();
        let column = line_prefix.chars().count();
        format!("{file}:{line}:{column}: {}", error.message)
    })
}

struct ScanError {
    offset: usize,
    message: &'static str,
}

struct Cursor<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn rest(&self) -> &'a str {
        &self.source[self.offset..]
    }

    fn error(&self, message: &'static str) -> ScanError {
        ScanError {
            offset: self.offset,
            message,
        }
    }

    fn eat(&mut self, prefix: &str) -> bool {
        if !self.rest().starts_with(prefix) {
            return false;
        }
        self.offset += prefix.len();
        true
    }

    fn space(&mut self) -> Result<(), ScanError> {
        loop {
            self.offset +=
                self.rest().len() - self.rest().trim_start_matches([' ', '\r', '\n']).len();
            if self.rest().starts_with('\t') {
                return Err(
                    self.error("tabs are not allowed; please configure your editor to expand them")
                );
            }
            if self.eat("--") {
                self.offset += self.rest().find('\n').unwrap_or(self.rest().len());
            } else if self.rest().starts_with("/--") || self.rest().starts_with("/-!") {
                return Ok(());
            } else if self.eat("/-") {
                self.block_comment()?;
            } else {
                return Ok(());
            }
        }
    }

    fn block_comment(&mut self) -> Result<(), ScanError> {
        let mut depth = 1;
        loop {
            let Some(candidate) = self.rest().find(['/', '-']) else {
                self.offset = self.source.len();
                return Err(self.error("unterminated comment"));
            };
            self.offset += candidate;
            if self.eat("-/") {
                depth -= 1;
                if depth == 0 {
                    return Ok(());
                }
            } else if self.eat("/-") {
                depth += 1;
            } else {
                self.offset += 1;
            }
        }
    }

    fn keyword(&mut self, spelling: &str) -> Result<bool, ScanError> {
        let found = self.eat(spelling);
        if found {
            self.space()?;
        }
        Ok(found)
    }

    fn import(&mut self, is_module: bool) -> Result<Option<Import>, ScanError> {
        let start = self.offset;
        let prefix = (|| {
            let public = self.keyword("public")?;
            let meta = self.keyword("meta")?;
            Ok::<_, ScanError>(self.keyword("import")?.then_some((public, meta)))
        })();
        // The import prefix is atomic. Failed prefix probes end the scan.
        let Ok(Some((public, meta))) = prefix else {
            return Ok(None);
        };
        let all = self.keyword("all")?;
        let module = self.module_name()?;
        self.space()?;
        if !is_module && (public || meta || all) {
            return Err(ScanError {
                offset: start,
                message: "cannot use 'public', 'meta', or 'all' without 'module'",
            });
        }
        Ok(Some(Import {
            import_all: all,
            is_exported: public || !is_module,
            is_meta: meta,
            module,
        }))
    }

    fn module_name(&mut self) -> Result<String, ScanError> {
        let mut parts = Vec::new();
        loop {
            let part = if self.eat("«") {
                let Some(end) = self.rest().find('»') else {
                    self.offset = self.source.len();
                    return Err(self.error("unterminated identifier escape"));
                };
                let part = &self.rest()[..end];
                self.offset += end + '»'.len_utf8();
                part
            } else {
                let mut chars = self.rest().chars();
                let Some(first) = chars.next() else {
                    return Err(self.error("unexpected end of input"));
                };
                if !ident_start(first) {
                    return Err(self.error("expected identifier"));
                }
                let len = first.len_utf8()
                    + chars
                        .take_while(|c| ident_continue(*c))
                        .map(char::len_utf8)
                        .sum::<usize>();
                let part = &self.rest()[..len];
                self.offset += len;
                part
            };
            parts.push(part);
            if !self
                .rest()
                .strip_prefix('.')
                .and_then(|next| next.chars().next())
                .is_some_and(|next| next == '«' || ident_start(next))
            {
                break;
            }
            self.offset += 1;
        }
        let first = parts[0];
        let last = parts[parts.len() - 1];
        if first.starts_with(['#', '?'])
            || last == "_hyg"
            || last == "_inaccessible"
            || last.contains('✝')
        {
            return Ok(parts.join("."));
        }
        Ok(parts
            .iter()
            .map(|part| {
                let mut chars = part.chars();
                if chars.next().is_some_and(ident_start) && chars.all(ident_continue) {
                    (*part).to_owned()
                } else {
                    format!("«{part}»")
                }
            })
            .collect::<Vec<_>>()
            .join("."))
    }
}

fn scan_header(source: &str) -> Result<Header, ScanError> {
    let mut cursor = Cursor { source, offset: 0 };
    cursor.space()?;
    let is_module = cursor.keyword("module")?;
    let mut imports = Vec::new();
    if !cursor.keyword("prelude")? {
        imports.extend([false, true].map(|is_meta| Import {
            import_all: false,
            is_exported: true,
            is_meta,
            module: "Init".to_owned(),
        }));
    }
    while let Some(import) = cursor.import(is_module)? {
        imports.push(import);
    }
    Ok(Header { imports, is_module })
}

fn ident_start(c: char) -> bool {
    c.is_ascii_alphabetic()
        || c == '_'
        || matches!(c,
            '\u{3b1}'..='\u{3c9}' | '\u{391}'..='\u{3a9}' | '\u{3ca}'..='\u{3fb}' |
            '\u{1f00}'..='\u{1ffe}' | '\u{2100}'..='\u{214f}' | '\u{1d49c}'..='\u{1d59f}' |
            '\u{c0}'..='\u{ff}' | '\u{100}'..='\u{17f}'
        ) && !matches!(c, 'λ' | 'Π' | 'Σ' | '×' | '÷')
}

fn ident_continue(c: char) -> bool {
    ident_start(c)
        || c.is_ascii_digit()
        || matches!(c, '\'' | '!' | '?' |
            '\u{2080}'..='\u{2089}' | '\u{2090}'..='\u{209c}' | '\u{1d62}'..='\u{1d6a}' | '\u{2c7c}'
        )
}
