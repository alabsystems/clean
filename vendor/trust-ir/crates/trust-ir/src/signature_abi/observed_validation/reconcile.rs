// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn reconcile<O: ExecutionObserver>(
        &mut self,
        a: &SignatureAbi,
        function: &Function,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(4, 0)?;
        if function.calling_conv != a.lowered_convention {
            return self.fail("function convention disagrees with typed signature ABI", w);
        }
        let mut i = 0;
        while let Some(attrs) = w.at(&function.attrs.params, i)? {
            w.admit(32, 0)?;
            if attrs.is_empty() {
                w.next(&mut i)?;
                continue;
            }
            let mut found = false;
            let mut j = 0;
            loop {
                w.admit(1, size_of::<Option<&AbiArgument>>())?;
                let arg = if let Some(arg) = w.at(&a.arguments, j)? {
                    arg
                } else if j == a.arguments.len() {
                    &a.result
                } else {
                    break;
                };
                let mut b = 0;
                while let Some(binding) = w.at(&arg.bindings, b)? {
                    w.admit(8, 0)?;
                    if matches!(binding.place,AbiBindingPlace::Parameter(index)|AbiBindingPlace::HiddenResult(index) if index as usize==i)
                    {
                        if !self.reconcile_attrs(attrs, arg, binding, w)? {
                            return Ok(false);
                        }
                        found = true;
                    }
                    w.next(&mut b)?;
                }
                w.next(&mut j)?;
            }
            w.admit(1, 0)?;
            if !found {
                w.text("function attribute ", &mut self.reason)?;
                w.unsigned(i as u128, &mut self.reason)?;
                w.text(" has no typed ABI binding", &mut self.reason)?;
                return Ok(false);
            }
            w.next(&mut i)?;
        }
        w.admit(32, 0)?;
        if !function.attrs.ret.is_empty() {
            let [binding] = a.result.bindings.as_slice() else {
                return self.fail(
                    "return attributes require exactly one typed result binding",
                    w,
                );
            };
            if !matches!(binding.place, AbiBindingPlace::Result(_)) {
                return self.fail("return attributes disagree with a hidden result", w);
            }
            if !self.reconcile_attrs(&function.attrs.ret, &a.result, binding, w)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn reconcile_attrs<O: ExecutionObserver>(
        &mut self,
        legacy: &crate::ParamAttrs,
        arg: &AbiArgument,
        binding: &AbiBinding,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(128, 0)?;
        let indirect = matches!(arg.mode, AbiPassMode::Indirect { .. });
        let hidden = matches!(binding.place, AbiBindingPlace::HiddenResult(_));
        if legacy.sret && !hidden || legacy.byval && (!indirect || hidden) {
            return self.fail(
                "function byval/sret attribute disagrees with typed ABI role",
                w,
            );
        }
        let attrs = match &arg.mode {
            AbiPassMode::Direct(s) => &s.attributes,
            AbiPassMode::Pair(a, _)
                if binding.source_offset == a.source_offset
                    && binding.source_bytes == a.source_bytes =>
            {
                &a.attributes
            }
            AbiPassMode::Pair(_, b)
                if binding.source_offset == b.source_offset
                    && binding.source_bytes == b.source_bytes =>
            {
                &b.attributes
            }
            AbiPassMode::Cast { attributes, .. } | AbiPassMode::Indirect { attributes, .. } => {
                attributes
            }
            _ => {
                return self.fail(
                    "function attributes do not identify one typed ABI carrier",
                    w,
                );
            }
        };
        let extension = match legacy.ext {
            crate::ArgExt::None => None,
            crate::ArgExt::SignExt => Some(AbiExtension::Sign),
            crate::ArgExt::ZeroExt => Some(AbiExtension::Zero),
        };
        if extension.is_some_and(|ext| ext != attrs.extension)
            || legacy.nonnull && !attrs.nonnull
            || legacy.noalias && !attrs.no_alias
            || legacy.readonly && !attrs.readonly
            || legacy
                .align
                .is_some_and(|align| Some(align) != attrs.pointee_align)
            || legacy
                .dereferenceable
                .is_some_and(|bytes| bytes != attrs.pointee_size)
        {
            return self.fail(
                "function attributes disagree with typed ABI carrier attributes",
                w,
            );
        }
        if let Some(pass) = &legacy.pass {
            let compatible = match pass {
                crate::PassMode::Ignore => matches!(arg.mode, AbiPassMode::Ignore),
                crate::PassMode::Direct => {
                    matches!(arg.mode, AbiPassMode::Direct(_) | AbiPassMode::Pair(..))
                }
                crate::PassMode::Pair => {
                    matches!(arg.mode, AbiPassMode::Pair(..)) && arg.bindings.len() == 1
                }
                crate::PassMode::Indirect { on_stack } => {
                    matches!(arg.mode,AbiPassMode::Indirect{on_stack:actual,..} if actual==*on_stack)
                }
                crate::PassMode::Cast { .. } => false,
            };
            if !compatible {
                return self.fail(
                    "function pass mode disagrees with or cannot refine the typed ABI mode",
                    w,
                );
            }
        }
        Ok(true)
    }
}
