// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn label<O: ExecutionObserver>(
        &mut self,
        value: &Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(32, 4 * size_of::<usize>())?;
        match value {
            Constant::Closure { func, captures } => {
                work.text("closure<func.", &mut self.label)?;
                work.unsigned(u128::from(func.index()), &mut self.label)?;
                work.text(">[", &mut self.label)?;
                work.unsigned(captures.len() as u128, &mut self.label)?;
                work.text("]", &mut self.label)
            }
            Constant::FnDef(func) => {
                work.text("fndef<func.", &mut self.label)?;
                work.unsigned(u128::from(func.index()), &mut self.label)?;
                work.text(">", &mut self.label)
            }
            Constant::SymbolAddr { symbol, addend } => {
                work.text("symaddr<", &mut self.label)?;
                work.text(symbol, &mut self.label)?;
                work.text(" + ", &mut self.label)?;
                work.signed(i128::from(*addend), &mut self.label)?;
                work.text(">", &mut self.label)
            }
            _ => {
                // Actual shape() is closed outer-tag/length-only; it neither
                // scans child payload nor allocates. Preserve its full labels.
                let shape = value.shape();
                let (prefix, len) = match shape {
                    ConstantShape::Int => return work.text("int", &mut self.label),
                    ConstantShape::Float => return work.text("float", &mut self.label),
                    ConstantShape::Bool => return work.text("bool", &mut self.label),
                    ConstantShape::PhantomData => return work.text("phantomdata", &mut self.label),
                    ConstantShape::Uninit => return work.text("uninit", &mut self.label),
                    ConstantShape::Bytes { len } => ("bytes", len as u128),
                    ConstantShape::Aggregate { len } => ("aggregate", len as u128),
                    ConstantShape::Array { len } => ("array", len as u128),
                    ConstantShape::Splat { len } => ("splat", u128::from(len)),
                    ConstantShape::Vector { len } => ("vector", len as u128),
                    ConstantShape::Sequence { len } => ("sequence", len as u128),
                    ConstantShape::Set { len } => ("set", len as u128),
                    ConstantShape::Record { fields } => ("record", fields as u128),
                    ConstantShape::TensorBlob { rank } => ("tensor_blob", rank as u128),
                    ConstantShape::Closure { .. }
                    | ConstantShape::FnDef
                    | ConstantShape::SymbolAddr => return Err(ObservedValueError::InvalidRange),
                };
                work.text(prefix, &mut self.label)?;
                work.text("[", &mut self.label)?;
                work.unsigned(len, &mut self.label)?;
                work.text("]", &mut self.label)
            }
        }
    }
}
