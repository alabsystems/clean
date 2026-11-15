// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
const ALIASES: [(&str, &str, &str); 4] = [
    ("trustvc", "trust-vc", "trust_vc"),
    ("trustmc", "trust-mc", "trust_mc"),
    ("trustwp", "trust-wp", "trust_wp"),
    ("trustir", "trust-ir", "trust-ir"),
];
impl State {
    pub(super) fn run<O: ExecutionObserver>(&mut self, name: &str, w: &mut Work<'_, '_, O>) -> R {
        self.normalize(name, w)?;
        let mut at = 0;
        while let Some((compact, separated, family)) = w.at(&ALIASES, at)? {
            w.admit(3, size_of::<(&str, &str, &str)>())?;
            if w.equal(&self.normalized, compact)? || w.equal(&self.normalized, separated)? {
                w.text(family, &mut self.canonical)?;
                return Ok(());
            }
            if self.prefixed(compact, family, w)? || self.prefixed(separated, family, w)? {
                return Ok(());
            }
            w.next(&mut at)?;
        }
        w.admit(1, 2 * size_of::<String>())?;
        self.canonical = take(&mut self.normalized);
        Ok(())
    }
    fn normalize<O: ExecutionObserver>(&mut self, name: &str, w: &mut Work<'_, '_, O>) -> R {
        let mut at = 0;
        let mut separator = false;
        // trim() can be elided exactly: every Unicode whitespace encodes only
        // non-ASCII-alphanumeric bytes. Leading such bytes are ignored and a
        // trailing pending separator is never emitted. No UTF8 interpretation
        // or Unicode case folding is part of the ordinary byte algorithm.
        while let Some(byte) = w.at(name.as_bytes(), at)? {
            w.admit(8, size_of::<u8>() + size_of::<bool>())?;
            let byte = *byte;
            if byte.is_ascii_alphanumeric() {
                if separator && !self.normalized.is_empty() {
                    w.byte(b'-', &mut self.normalized)?;
                }
                w.byte(byte.to_ascii_lowercase(), &mut self.normalized)?;
                w.admit(1, size_of::<bool>())?;
                separator = false;
            } else if !self.normalized.is_empty() {
                w.admit(1, size_of::<bool>())?;
                separator = true;
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn prefixed<O: ExecutionObserver>(
        &mut self,
        prefix: &'static str,
        family: &'static str,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        // Both strings come only from the fixed ASCII table above. Original
        // format!("{prefix}-") is replaced by two bounded checked slices.
        w.admit(2 * prefix.len() + 4, size_of::<Option<&str>>())?;
        let Some(tail) = self.normalized.strip_prefix(prefix) else {
            return Ok(false);
        };
        let Some(suffix) = tail.strip_prefix('-') else {
            return Ok(false);
        };
        w.text(family, &mut self.canonical)?;
        w.text("-", &mut self.canonical)?;
        w.text(suffix, &mut self.canonical)?;
        Ok(true)
    }
}
