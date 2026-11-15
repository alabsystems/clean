// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn shape<O: ExecutionObserver>(
    value: TyShape,
    work: &mut Work<'_, '_, O>,
    output: &mut String,
) -> R {
    work.admit(1, size_of::<TyShape>())?;
    let text = match value {
        TyShape::Storage => "storage",
        TyShape::Int { signed, bits } => {
            work.text(if signed { "i" } else { "u" }, output)?;
            return work.number(u64::from(bits), output);
        }
        TyShape::PointerInt { signed } => {
            if signed {
                "isize"
            } else {
                "usize"
            }
        }
        TyShape::Error => "error",
        TyShape::Float { bits } => {
            work.text("f", output)?;
            return work.number(u64::from(bits), output);
        }
        TyShape::Bool => "bool",
        TyShape::ThinPointer => "thin_pointer",
        TyShape::FatPointer => "fat_pointer",
        TyShape::Unit => "unit",
        TyShape::Never => "never",
        TyShape::Struct => "struct",
        TyShape::Array => "array",
        TyShape::Vector => "vector",
        TyShape::Tuple => "tuple",
        TyShape::Enum => "enum",
        TyShape::Function => "function",
        TyShape::Ref => "ref",
        TyShape::RefMut => "ref_mut",
        TyShape::PtrConst => "ptr_const",
        TyShape::PtrMut => "ptr_mut",
        TyShape::Rc => "rc",
        TyShape::Set => "set",
        TyShape::Sequence => "sequence",
        TyShape::Record => "record",
        TyShape::Closure => "closure",
        TyShape::Refine => "refine",
        TyShape::Dialect => "dialect",
        TyShape::Handle => "handle",
        TyShape::Tensor => "tensor",
    };
    work.text(text, output)
}

pub(super) fn metadata<O: ExecutionObserver>(
    value: Option<PointerMetadataShape>,
    work: &mut Work<'_, '_, O>,
    output: &mut String,
) -> R {
    work.admit(1, size_of::<Option<PointerMetadataShape>>())?;
    let Some(value) = value else {
        return work.text("None", output);
    };
    work.text("Some(", output)?;
    work.admit(1, size_of::<PointerMetadataShape>())?;
    match value {
        PointerMetadataShape::SliceLen { elem } => {
            // The ordinary typed_id! macro spells Debug as TyId(N).
            work.text("SliceLen { elem: TyId(", output)?;
            work.number(u64::from(elem.0), output)?;
            work.text(") }", output)?;
        }
        PointerMetadataShape::StrLen => work.text("StrLen", output)?,
        PointerMetadataShape::VTable { trait_id } => {
            work.text("VTable { trait_id: ", output)?;
            work.number(u64::from(trait_id), output)?;
            work.text(" }", output)?;
        }
        PointerMetadataShape::ContainerLen => work.text("ContainerLen", output)?,
        PointerMetadataShape::ContainerVtable => work.text("ContainerVtable", output)?,
    }
    work.text(")", output)
}
