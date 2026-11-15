// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn validate<O: ExecutionObserver>(
        &mut self,
        a: &SignatureAbi,
        signature: &FuncTy,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(1, size_of::<String>())?;
        self.wire = a.canonical_text_for_wire_observed(w.session, w.site)?;
        w.flat(take(&mut self.wire));
        w.admit(32, 0)?;
        if a.target.triple.is_empty()
            || a.target.data_layout.is_empty()
            || a.target.cpu.is_empty()
            || a.target.target_spec.is_empty()
            || a.frontend.name.is_empty()
            || a.frontend.revision.is_empty()
            || a.convention.is_empty()
            || a.source_abi.is_empty()
        {
            return self.fail("signature ABI identity is incomplete", w);
        }
        let mut i = 0;
        // Preserve the original whole any(empty) before any adjacent ordering.
        while let Some(f) = w.at(&a.target.features, i)? {
            w.admit(1, 0)?;
            if f.is_empty() {
                return self.fail("target features are not sorted, unique, nonempty names", w);
            }
            w.next(&mut i)?;
        }
        i = 1;
        while let Some(right) = w.at(&a.target.features, i)? {
            let left = w
                .at(&a.target.features, i - 1)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if w.lex(left, right)? != Ordering::Less {
                return self.fail("target features are not sorted, unique, nonempty names", w);
            }
            w.next(&mut i)?;
        }
        w.admit(16, 0)?;
        if !matches!(a.target.pointer_bytes, 2 | 4 | 8 | 16) {
            return self.fail("signature ABI pointer width is invalid", w);
        }
        if a.variadic != signature.is_vararg || a.fixed_count as usize > a.arguments.len() {
            return self.fail("signature ABI variadic/fixed argument census disagrees", w);
        }
        for (rows, count) in [
            (&mut self.parameters, signature.params.len()),
            (&mut self.results, signature.returns.len()),
        ] {
            let mut i = 0;
            while i < count {
                w.reserve(rows)?;
                w.admit(1, size_of::<Vec<(u64, u64)>>())?;
                rows.push(Vec::new());
                w.next(&mut i)?;
            }
        }
        i = 0;
        while let Some(arg) = w.at(&a.arguments, i)? {
            if !self.argument(arg, Kind::Parameter, w)? {
                self.prefix(Some(i), w)?;
                return Ok(false);
            }
            let mut b = 0;
            while let Some(binding) = w.at(&arg.bindings, b)? {
                w.admit(12, 0)?;
                let AbiBindingPlace::Parameter(index) = binding.place else {
                    return self.fail("source argument has a result or hidden-result binding", w);
                };
                if matches!(
                    arg.mode,
                    AbiPassMode::Indirect {
                        metadata_attributes: None,
                        on_stack: false,
                        ..
                    }
                ) && (!matches!(w.at(&signature.params, index as usize)?, Some(Ty::Ptr))
                    || binding.carrier_offset != 0
                    || binding.carrier_bytes != u64::from(a.target.pointer_bytes))
                {
                    return self.fail(
                        "indirect argument does not name one prelowered Ptr carrier",
                        w,
                    );
                }
                if !self.claim(Kind::Parameter, index, binding, w)? {
                    return Ok(false);
                }
                w.next(&mut b)?;
            }
            self.retire_ranges(w);
            w.admit(1, 0)?;
            w.next(&mut i)?;
        }
        if !self.argument(&a.result, Kind::Result, w)? {
            self.prefix(None, w)?;
            return Ok(false);
        }
        i = 0;
        while let Some(binding) = w.at(&a.result.bindings, i)? {
            w.admit(16, 0)?;
            match binding.place {
                AbiBindingPlace::Result(index) => {
                    if !self.claim(Kind::Result, index, binding, w)? {
                        return Ok(false);
                    }
                }
                AbiBindingPlace::HiddenResult(index) => {
                    if !matches!(
                        a.result.mode,
                        AbiPassMode::Indirect {
                            on_stack: false,
                            ..
                        }
                    ) || !signature.returns.is_empty()
                        || a.result.bindings.len() != 1
                    {
                        return self.fail(
                            "hidden result requires one indirect result and no result values",
                            w,
                        );
                    }
                    let Some(ty) = w.at(&signature.params, index as usize)? else {
                        return self.fail("hidden result parameter is out of range", w);
                    };
                    if !matches!(ty, Ty::Ptr) {
                        return self.fail(
                            "hidden result parameter is not the prelowered Ptr carrier",
                            w,
                        );
                    }
                    if binding.carrier_offset != 0
                        || binding.carrier_bytes != u64::from(a.target.pointer_bytes)
                    {
                        return self.fail("hidden result carrier is not one complete pointer", w);
                    }
                    if !self.claim(Kind::HiddenResultParameter, index, binding, w)? {
                        return Ok(false);
                    }
                }
                AbiBindingPlace::Parameter(_) => {
                    return self.fail("source result has an ordinary parameter binding", w);
                }
            }
            w.next(&mut i)?;
        }
        for kind in [Kind::Parameter, Kind::Result] {
            let mut i = 0;
            loop {
                let empty = {
                    let rows = match kind {
                        Kind::Result => &self.results,
                        _ => &self.parameters,
                    };
                    let Some(row) = w.at(rows, i)? else { break };
                    w.admit(1, 0)?;
                    row.is_empty()
                };
                if empty {
                    return self.fail("signature ABI omits a lowered parameter or result", w);
                }
                w.next(&mut i)?;
            }
        }
        self.retire_ranges(w);
        w.admit(1, 0)?;
        if !self.carrier_bounds(
            Kind::Parameter,
            &signature.params,
            a.target.pointer_bytes,
            w,
        )? {
            return Ok(false);
        }
        self.carrier_bounds(Kind::Result, &signature.returns, a.target.pointer_bytes, w)
    }
    pub(super) fn target<O: ExecutionObserver>(
        &mut self,
        a: &SignatureAbi,
        target: Option<&TargetInfo>,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(12, 0)?;
        let Some(t) = target else {
            return self.fail("typed signature ABI requires module target information", w);
        };
        if w.lex(&a.target.triple, &t.triple)? != Ordering::Equal
            || u32::from(a.target.pointer_bytes) != t.pointer_size
            || a.target.little_endian != (t.endianness == crate::Endianness::Little)
        {
            return self.fail(
                "typed signature ABI target disagrees with the module target",
                w,
            );
        }
        if let Some(abi) = &t.abi
            && w.lex(abi, &a.target.abi)? != Ordering::Equal
        {
            return self.fail(
                "typed signature ABI target disagrees with the module target",
                w,
            );
        }
        Ok(true)
    }
}
