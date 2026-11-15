// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
pub(super) struct Row<'a> {
    pub(super) glue: FuncId,
    pub(super) ty: &'a Ty,
}
#[derive(Clone, Copy)]
pub(super) enum TypeTask<'a> {
    Value(&'a Ty),
    Tail(&'a [Ty]),
}
pub(super) struct State<'a> {
    pub(super) target: Option<&'a Function>,
    pub(super) rows: Vec<Row<'a>>,
    pub(super) roots: Vec<&'a Ty>,
    pub(super) frames: Vec<TypeTask<'a>>,
    pub(super) current: Option<TypeTask<'a>>,
    pub(super) plan: Plan,
    pub(super) reason: String,
    pub(super) first_text: String,
    pub(super) second_text: String,
    pub(super) digest: Option<ProofDigest>,
}
impl<'a> State<'a> {
    pub(super) fn new() -> Self {
        Self {
            target: None,
            rows: Vec::new(),
            roots: Vec::new(),
            frames: Vec::new(),
            current: None,
            plan: Plan::default(),
            reason: String::new(),
            first_text: String::new(),
            second_text: String::new(),
            digest: None,
        }
    }
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        function: FuncId,
        out: &mut Output<'_, '_, O>,
    ) -> R {
        for f in &module.functions {
            out.admit(2, size_of::<Option<&Function>>())?;
            if f.id != function {
                continue;
            }
            if self.target.is_some() {
                return self.missing(function, out);
            }
            self.target = Some(f);
        }
        let Some(f) = self.target else {
            return self.missing(function, out);
        };
        for block in &f.blocks {
            out.poll()?;
            for node in &block.body {
                out.admit(1, size_of::<Option<&'static str>>())?;
                if let Some(construct) = node.inst.binary_wire_gap() {
                    append(&mut self.reason, "function #", out)?;
                    decimal(&mut self.reason, function.index() as usize, out)?;
                    append(&mut self.reason, " carries ", out)?;
                    append(&mut self.reason, construct, out)?;
                    return append(
                        &mut self.reason,
                        ", which has no binary carrier yet, so the body has no identity to state",
                        out,
                    );
                }
            }
        }
        if !self.drop_rows(module, f, out)? {
            return Ok(());
        }
        if self.spells_error(f, out)? {
            append(&mut self.reason, "function #", out)?;
            decimal(&mut self.reason, function.index() as usize, out)?;
            return append(
                &mut self.reason,
                " spells the producer-internal Ty::Error, which has no binary spelling, so the body has no identity to state",
                out,
            );
        }
        if let Some(scopes) = &f.scopes {
            for (index, scope) in scopes.iter().enumerate() {
                out.admit(2, size_of::<Option<&crate::ScopeData>>())?;
                if let Ok(index) = u32::try_from(index)
                    && scope.inlined_at.is_some()
                {
                    append(&mut self.reason, "function #", out)?;
                    decimal(&mut self.reason, function.index() as usize, out)?;
                    append(&mut self.reason, " lexical scope #", out)?;
                    decimal(&mut self.reason, index as usize, out)?;
                    return append(
                        &mut self.reason,
                        " carries an inlining chain link, which has no binary carrier yet, so the body has no identity to state",
                        out,
                    );
                }
            }
        }
        self.plan.build(f, out)?;
        out.admit(1, 2 * size_of::<Builder>())?;
        let mut builder = Builder::new(false);
        let collected = wire::collect(f, &self.plan, &self.rows, &mut builder, out);
        if let Err(error) = collected {
            builder.retire(out);
            return Err(error);
        }
        let pool = builder.seal();
        let encoded = (|| {
            wire::write(f, &self.plan, &self.rows, &pool, out)?;
            let length = out.count()?;
            out.start_hash(EXECUTABLE_CONTENT_DIGEST_V1_DOMAIN, length)?;
            wire::write(f, &self.plan, &self.rows, &pool, out)?;
            out.finish_hash()
        })();
        pool.retire(out);
        let executable = encoded?;
        out.admit(34, 2 * 33)?;
        let mut bytes = [0u8; 33];
        bytes[0] = match executable.algorithm {
            crate::proof::ProofDigestAlgorithm::Sha256 => 0,
            crate::proof::ProofDigestAlgorithm::TrustIrStableV1 => 1,
        };
        bytes[1..].copy_from_slice(&executable.bytes);
        self.digest = Some(out.body_domain(&bytes)?);
        Ok(())
    }
    fn missing<O: ExecutionObserver>(
        &mut self,
        function: FuncId,
        out: &mut Output<'_, '_, O>,
    ) -> R {
        append(&mut self.reason, "body digest target function #", out)?;
        decimal(&mut self.reason, function.index() as usize, out)?;
        append(&mut self.reason, " is missing or duplicated", out)
    }
    pub(super) fn retire_scratch<O: ExecutionObserver>(&mut self, out: &mut Output<'_, '_, O>) {
        self.plan.retire(out);
        out.body_retire(self.current.take());
        while !self.rows.is_empty() {
            out.body_retire(self.rows.pop());
        }
        while !self.roots.is_empty() {
            out.body_retire(self.roots.pop());
        }
        while !self.frames.is_empty() {
            out.body_retire(self.frames.pop());
        }
        out.body_retire(core::mem::take(&mut self.rows));
        out.body_retire(core::mem::take(&mut self.roots));
        out.body_retire(core::mem::take(&mut self.frames));
        out.body_retire_text(core::mem::take(&mut self.first_text));
        out.body_retire_text(core::mem::take(&mut self.second_text));
        out.body_retire(self.target.take());
        out.body_retirement(size_of::<Self>() + 1, size_of::<Self>());
    }
    pub(super) fn retire_output<O: ExecutionObserver>(&mut self, out: &mut Output<'_, '_, O>) {
        out.body_retire_text(core::mem::take(&mut self.reason));
        out.body_retire(self.digest.take());
    }
}
pub(super) fn append<O: ExecutionObserver>(
    text: &mut String,
    part: &str,
    out: &mut Output<'_, '_, O>,
) -> R {
    let mut at = 0usize;
    while at < part.len() {
        // UTF8 backoff is at most three continuation bytes. Each copy below
        // is actual bounded work after its own admission, never an opaque
        // full push_str following a mere observation prewalk.
        out.admit(5, 2 * size_of::<usize>())?;
        let mut end = at
            .checked_add((part.len() - at).min(1024))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        while !part.is_char_boundary(end) {
            end -= 1;
        }
        let chunk = part.get(at..end).ok_or(ObservedValueError::InvalidRange)?;
        let needed = text
            .len()
            .checked_add(chunk.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > text.capacity() {
            let images = needed
                .checked_add(text.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            out.admit(
                images
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                images,
            )?;
            text.try_reserve_exact(chunk.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        let bytes = chunk
            .len()
            .checked_mul(2)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        out.admit(
            bytes
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            bytes,
        )?;
        text.push_str(chunk);
        at = end;
    }
    Ok(())
}
pub(super) fn decimal<O: ExecutionObserver>(
    text: &mut String,
    mut value: usize,
    out: &mut Output<'_, '_, O>,
) -> R {
    const WIDTH: usize = usize::BITS as usize;
    out.admit(WIDTH * 4, WIDTH * 2)?;
    let mut bytes = [0u8; WIDTH];
    let mut at = WIDTH;
    loop {
        at -= 1;
        bytes[at] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    let digits =
        core::str::from_utf8(&bytes[at..]).map_err(|_| ObservedValueError::InvalidRange)?;
    append(text, digits, out)
}
