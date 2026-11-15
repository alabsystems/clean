// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The original bounded ABI grammar, with flat ownership and inner admission.

use super::arena::{Arena, Node};
use super::*;
use core::mem::size_of;

pub(super) fn parse<O: ExecutionObserver>(
    input: &str,
    out: &mut Writer<'_, '_, O>,
) -> R<(Arena, usize)> {
    out.admit(1, size_of::<Parser<'_>>())?;
    if input.len() > MAX_ABI_TEXT_BYTES {
        return Err(ObservedValueError::UnsupportedValue);
    }
    let mut parser = Parser {
        input,
        offset: 0,
        nodes: 0,
        arena: Arena::new(),
    };
    let result = parser.node(0, out).and_then(|root| {
        out.poll()?;
        if parser.offset != input.len() {
            return Err(ObservedValueError::UnsupportedValue);
        }
        Ok(root)
    });
    match result {
        Ok(root) => Ok((parser.arena, root)),
        Err(error) => {
            parser.arena.retire(out);
            Err(error)
        }
    }
}

struct Parser<'a> {
    input: &'a str,
    offset: usize,
    nodes: usize,
    arena: Arena,
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.input.as_bytes().get(self.offset).copied()
    }

    fn expect<O: ExecutionObserver>(&mut self, byte: u8, out: &mut Writer<'_, '_, O>) -> R {
        out.poll()?;
        if self.peek() != Some(byte) {
            return Err(ObservedValueError::UnsupportedValue);
        }
        self.offset += 1;
        Ok(())
    }

    fn word<O: ExecutionObserver>(&mut self, out: &mut Writer<'_, '_, O>) -> R<String> {
        let start = self.offset;
        loop {
            out.poll()?;
            if self
                .peek()
                .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_')
            {
                self.offset += 1;
            } else {
                break;
            }
        }
        if start == self.offset {
            return Err(ObservedValueError::UnsupportedValue);
        }
        out.copy(&self.input[start..self.offset])
    }

    fn quoted<O: ExecutionObserver>(&mut self, out: &mut Writer<'_, '_, O>) -> R<String> {
        self.expect(b'"', out)?;
        let mut value = String::new();
        let result = (|| loop {
            out.admit(4, 0)?;
            let Some(character) = self.input[self.offset..].chars().next() else {
                return Err(ObservedValueError::UnsupportedValue);
            };
            self.offset += character.len_utf8();
            match character {
                '"' => return Ok(()),
                '\\' => {
                    let escaped = self.escape(out)?;
                    out.character_to(&mut value, escaped)?;
                }
                c if c.is_control() => return Err(ObservedValueError::UnsupportedValue),
                c => out.character_to(&mut value, c)?,
            }
        })();
        if let Err(error) = result {
            out.retire(value);
            return Err(error);
        }
        Ok(value)
    }

    fn escape<O: ExecutionObserver>(&mut self, out: &mut Writer<'_, '_, O>) -> R<char> {
        out.poll()?;
        let Some(escape) = self.peek() else {
            return Err(ObservedValueError::UnsupportedValue);
        };
        self.offset += 1;
        match escape {
            b'"' => Ok('"'),
            b'\\' => Ok('\\'),
            b'n' => Ok('\n'),
            b'r' => Ok('\r'),
            b't' => Ok('\t'),
            b'u' => self.unicode(out),
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }

    fn unicode<O: ExecutionObserver>(&mut self, out: &mut Writer<'_, '_, O>) -> R<char> {
        self.expect(b'{', out)?;
        let start = self.offset;
        loop {
            out.poll()?;
            if self.peek().is_some_and(|b| b.is_ascii_hexdigit()) {
                self.offset += 1;
            } else {
                break;
            }
        }
        if self.offset - start > 6 || self.offset == start {
            return Err(ObservedValueError::UnsupportedValue);
        }
        let mut value = 0u32;
        for byte in self.input.as_bytes()[start..self.offset].iter().copied() {
            out.poll()?;
            let digit = match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => return Err(ObservedValueError::UnsupportedValue),
            };
            value = value * 16 + u32::from(digit);
        }
        self.expect(b'}', out)?;
        char::from_u32(value).ok_or(ObservedValueError::UnsupportedValue)
    }

    fn node<O: ExecutionObserver>(
        &mut self,
        depth: usize,
        out: &mut Writer<'_, '_, O>,
    ) -> R<usize> {
        out.poll()?;
        self.nodes = self
            .nodes
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if depth > MAX_DEPTH || self.nodes > MAX_NODES {
            return Err(ObservedValueError::UnsupportedValue);
        }
        match self.peek() {
            Some(b'"') => {
                let value = self.quoted(out)?;
                self.arena.push(Node::Text(value), out)
            }
            Some(b'[') => self.list(depth, out),
            Some(b'{') => self.record(depth, out),
            _ => {
                let value = self.word(out)?;
                self.arena.push(Node::Atom(value), out)
            }
        }
    }

    fn list<O: ExecutionObserver>(
        &mut self,
        depth: usize,
        out: &mut Writer<'_, '_, O>,
    ) -> R<usize> {
        let mut values = Vec::new();
        let result = (|| {
            self.expect(b'[', out)?;
            if self.peek() != Some(b']') {
                loop {
                    out.poll()?;
                    let value = self.node(depth + 1, out)?;
                    out.reserve(&mut values, 1)?;
                    out.admit(1, size_of::<usize>())?;
                    values.push(value);
                    if self.peek() != Some(b',') {
                        break;
                    }
                    self.expect(b',', out)?;
                }
            }
            self.expect(b']', out)
        })();
        if let Err(error) = result {
            out.retire(values);
            return Err(error);
        }
        self.arena.push(Node::List(values), out)
    }

    fn record<O: ExecutionObserver>(
        &mut self,
        depth: usize,
        out: &mut Writer<'_, '_, O>,
    ) -> R<usize> {
        let mut fields = Vec::new();
        let mut key = String::new();
        let result = (|| {
            self.expect(b'{', out)?;
            if self.peek() != Some(b'}') {
                loop {
                    out.poll()?;
                    key = self.word(out)?;
                    self.expect(b'=', out)?;
                    let value = self.node(depth + 1, out)?;
                    out.reserve(&mut fields, 1)?;
                    out.admit(1, size_of::<(String, usize)>())?;
                    fields.push((core::mem::take(&mut key), value));
                    if self.peek() != Some(b',') {
                        break;
                    }
                    self.expect(b',', out)?;
                }
            }
            self.expect(b'}', out)
        })();
        if let Err(error) = result {
            out.retire(key);
            Node::Record(fields).retire(out);
            return Err(error);
        }
        self.arena.push(Node::Record(fields), out)
    }
}
